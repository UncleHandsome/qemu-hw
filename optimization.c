/*
 *  (C) 2010 by Computer System Laboratory, IIS, Academia Sinica, Taiwan.
 *      See COPYRIGHT in top-level directory.
 */

#include <stdlib.h>
#include "exec-all.h"
#include "tcg-op.h"
#include "helper.h"
#define GEN_HELPER 1
#include "helper.h"
#include "optimization.h"

extern uint8_t *optimization_ret_addr;

static TranslationBlock *tb_find_slow(CPUState* env,
                                      target_ulong pc,
                                      target_ulong cs_base,
                                      uint64_t flags)
{
    TranslationBlock *tb, **ptb1;
    unsigned int h;
    tb_page_addr_t phys_pc, phys_page1, phys_page2;
    target_ulong virt_page2;

    tb_invalidated_flag = 0;

    phys_pc = get_page_addr_code(env, pc);
    phys_page1 = phys_pc & TARGET_PAGE_MASK;
    phys_page2 = -1;
    h = tb_phys_hash_func(phys_pc);
    ptb1 = &tb_phys_hash[h];
    for(;;) {
        tb = *ptb1;
        if (!tb)
            return tb;
        if (tb->pc == pc &&
            tb->page_addr[0] == phys_page1 &&
            tb->cs_base == cs_base &&
            tb->flags == flags) {
            /* check next page if needed */
            if (tb->page_addr[1] != -1) {
                virt_page2 = (pc & TARGET_PAGE_MASK) +
                    TARGET_PAGE_SIZE;
                phys_page2 = get_page_addr_code(env, virt_page2);
                if (tb->page_addr[1] == phys_page2)
                    break;
            } else {
                break;
            }
        }
        ptb1 = &tb->phys_hash_next;
    }

    env->tb_jmp_cache[tb_jmp_cache_hash_func(pc)] = tb;
    return tb;
}

static inline TranslationBlock *tb_find(CPUState* env, target_ulong pc)
{
    TranslationBlock *tb;
    target_ulong cs_base;
    int flags;

    cs_base = env->segs[R_CS].base;
    flags = env->hflags |
        (env->eflags & (IOPL_MASK | TF_MASK | RF_MASK | VM_MASK));

    tb = env->tb_jmp_cache[tb_jmp_cache_hash_func(pc)];
    if (unlikely(!tb || tb->pc != pc || tb->cs_base != cs_base ||
                 tb->flags != flags)) {
        tb = tb_find_slow(env, pc, cs_base, flags);
    }
    return tb;
}

/*
 * Shadow Stack
 */
const int sz = sizeof(target_ulong);
const int SIZE = 50;
target_ulong *eip_list, *eip_end, *curr_eip;
unsigned long *slot_list, *slot_end, *curr_slot;

static inline void shack_init(CPUState *env)
{
    eip_list = (target_ulong *)malloc(SIZE * sizeof(shadow_pair));
    curr_eip = eip_end = eip_list + SIZE;
    slot_list = (unsigned long*)curr_eip;
    curr_slot = slot_end = slot_list + SIZE;
    env->shack = (uint64_t *)malloc(SHACK_SIZE * sizeof(uint64_t));
    env->shack_end = env->shack_top = env->shack;
}

/*
 * shack_set_shadow()
 *  Insert a guest eip to host eip pair if it is not yet created.
 */
 void shack_set_shadow(CPUState *env, target_ulong guest_eip, unsigned long *host_eip)
{
    target_ulong *p = curr_eip;
    while (++p < eip_end) {
        if (*p == guest_eip) {
            int id = p - curr_eip;
            curr_slot[id] = (uintptr_t)host_eip;
            ++curr_slot;
            ++curr_eip;
            if (id > 1) {
                memmove(curr_slot + 1, curr_slot, id * sizeof(target_ulong));
                memmove(curr_eip + 1, curr_eip, id * sizeof(unsigned long));
            }
            return;
        }
    }
}

/*
 * helper_shack_flush()
 *  Reset shadow stack.
 */
void helper_shack_flush(CPUState *env)
{
}

/*
 * push_shack()
 *  Push next guest eip into shadow stack.
 */
void push_shack(CPUState *env, TCGv_ptr cpu_env, target_ulong next_eip)
{
    TCGv_ptr temp_shack_top = tcg_temp_new_ptr();
    tcg_gen_ld_ptr(temp_shack_top, cpu_env, offsetof(CPUState, shack_top));
    tcg_gen_add_ptr(temp_shack_top, temp_shack_top, tcg_const_i64(sz));

    TranslationBlock* tb = tb_find(env, next_eip);
    if (tb)
        tcg_gen_st_tl(tcg_const_tl((int32_t)tb->tc_ptr), temp_shack_top, 0);
    else {
        tcg_gen_st_tl(tcg_const_tl(5566), temp_shack_top, 0);
        *--curr_eip = next_eip;
        *--curr_slot = gen_opparam_ptr - 4;
    }

    tcg_gen_add_ptr(temp_shack_top, temp_shack_top, tcg_const_i64(sz));
    tcg_gen_st_tl(tcg_const_tl(next_eip), temp_shack_top, 0);

}

/*
 * pop_shack()
 *  Pop next host eip from shadow stack.
 */
void pop_shack(TCGv_ptr cpu_env, TCGv next_eip)
{
    TCGv_ptr temp_shack_top = tcg_temp_local_new_ptr();
    TCGv guest_eip = tcg_temp_new();
    tcg_gen_ld_ptr(temp_shack_top, cpu_env, offsetof(CPUState, shack_top));
    tcg_gen_ld_tl(guest_eip, temp_shack_top, 0);
    int l = gen_new_label();
    tcg_gen_brcond_tl(TCG_COND_NE, next_eip, guest_eip, l);

    TCGv host_eip = tcg_temp_new();
    tcg_gen_add_ptr(temp_shack_top, temp_shack_top, tcg_const_i64(sz));
    tcg_gen_ld_tl(host_eip, temp_shack_top, 0);
    tcg_gen_add_ptr(temp_shack_top, temp_shack_top, tcg_const_i64(sz));

    *gen_opc_ptr++ = INDEX_op_jmp;
    *gen_opparam_ptr++ = GET_TCGV(host_eip);


    gen_set_label(l);
}

/*
 * Indirect Branch Target Cache
 */
__thread int update_ibtc;

/*
 * helper_lookup_ibtc()
 *  Look up IBTC. Return next host eip if cache hit or
 *  back-to-dispatcher stub address if cache miss.
 */
void *helper_lookup_ibtc(target_ulong guest_eip)
{
    return optimization_ret_addr;
}

/*
 * update_ibtc_entry()
 *  Populate eip and tb pair in IBTC entry.
 */
void update_ibtc_entry(TranslationBlock *tb)
{
}

/*
 * ibtc_init()
 *  Create and initialize indirect branch target cache.
 */
static inline void ibtc_init(CPUState *env)
{
}

/*
 * init_optimizations()
 *  Initialize optimization subsystem.
 */
int init_optimizations(CPUState *env)
{
    shack_init(env);
    ibtc_init(env);

    return 0;
}

/*
 * vim: ts=8 sts=4 sw=4 expandtab
 */
