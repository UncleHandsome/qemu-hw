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

shadowht ht;

static inline void shack_init(CPUState *env)
{
    ht.ht = malloc(sizeof(shadow_pair*) * TB_JMP_CACHE_SIZE);
    memset(ht.ht, 0, sizeof(shadow_pair*) * TB_JMP_CACHE_SIZE);
    ht.addr_slot = malloc(sizeof(unsigned long) * TB_JMP_CACHE_SIZE * 5);
    env->shack = (uint64_t *)malloc(SHACK_SIZE * sizeof(uint64_t));
    env->shack_top = env->shack;
    env->shack_end = env->shack + SHACK_SIZE;
}

/*
 * shack_set_shadow()
 *  Insert a guest eip to host eip pair if it is not yet created.
 */
 void shack_set_shadow(CPUState *env, target_ulong guest_eip, unsigned long *host_eip)
{
    int idx = tb_jmp_cache_hash_func(guest_eip);
    shadow_pair *p = ht.ht[idx], *prev = NULL;
    while (p) {
        if (p->guest_eip == guest_eip) {
            // if (prev)
            //     prev->next = p->next;
            // else
            //     ht.ht[idx] = p->next;
            *p->shadow_slot = (uintptr_t)host_eip;
            // free(p);
            return;
        }
        prev = p;
        p = p->next;
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
    TCGv_ptr temp_shack_top = tcg_temp_local_new_ptr();
    TCGv_ptr temp_shack_end = tcg_temp_local_new_ptr();
    int not_full = gen_new_label();
    // temp_shack_top = cpu_env->shack_top
    tcg_gen_ld_ptr(temp_shack_top, cpu_env, offsetof(CPUState, shack_top));
    // temp_shack_end = cpu_env->shack_end
    tcg_gen_ld_ptr(temp_shack_end, cpu_env, offsetof(CPUState, shack_end));
    // if (temp_shack_top != temp_shack_end) goto not_full
    tcg_gen_brcond_tl(TCG_COND_NE, temp_shack_top, temp_shack_end, not_full);

    // temp_shack_top = env->shack
    tcg_gen_mov_tl(temp_shack_top, tcg_const_tl((int32_t)env->shack));

    gen_set_label(not_full);

    unsigned long *slot = ht.addr_slot++;
    // temp_shack_top[1] = slot
    tcg_gen_st_tl(tcg_const_tl((int32_t)slot), temp_shack_top, sizeof(target_ulong));

    TranslationBlock* tb = tb_find(env, next_eip);
    if (tb)
        *slot = tb->tc_ptr;
    else {
        *slot = 5566;
        int index = tb_jmp_cache_hash_func(next_eip);
        shadow_pair *new = malloc(sizeof(shadow_pair));
        new->guest_eip = next_eip;
        new->shadow_slot = slot;
        new->next = ht.ht[index];
        ht.ht[index] = new;
    }

    // temp_shack_top[2] = next_eip
    tcg_gen_st_tl(tcg_const_tl(next_eip), temp_shack_top, 2 * sizeof(target_ulong));
    // temp_shack_top + 8
    tcg_gen_addi_ptr(temp_shack_top, temp_shack_top, 2 * sizeof(target_ulong));
    // env->shack_top = temp_shack_top
    tcg_gen_st_ptr(temp_shack_top, cpu_env, offsetof(CPUState, shack_top));

}

/*
 * pop_shack()
 *  Pop next host eip from shadow stack.
 */
void pop_shack(TCGv_ptr cpu_env, TCGv next_eip)
{
    TCGv_ptr temp_shack_top = tcg_temp_local_new_ptr();
    TCGv guest_eip = tcg_temp_new();
    int l = gen_new_label();

    // temp = cpu_env->shack_top
    tcg_gen_ld_ptr(temp_shack_top, cpu_env, offsetof(CPUState, shack_top));
    // guest_eip = *temp;
    tcg_gen_ld_tl(guest_eip, temp_shack_top, 0);
    // if (guest_eip != next_eip) goto l;
    tcg_gen_brcond_tl(TCG_COND_NE, next_eip, guest_eip, l);

    TCGv_ptr host_eip_ptr = tcg_temp_new_ptr();
    TCGv host_eip = tcg_temp_local_new();
    // host_eip_ptr = temp[-1];
    tcg_gen_ld_tl(host_eip_ptr, temp_shack_top, -4);
    // host_eip = *host_eip_ptr
    tcg_gen_ld_tl(host_eip, host_eip_ptr, 0);
    // if (host_eip == 5566) goto l;
    tcg_gen_brcond_tl(TCG_COND_EQ, host_eip, tcg_const_tl(5566), l);
    // temp = temp - 2;
    tcg_gen_subi_tl(temp_shack_top, temp_shack_top, 2*sizeof(target_ulong));
    // cpu_env->shack_top = temp
    tcg_gen_st_ptr(temp_shack_top, cpu_env, offsetof(CPUState, shack_top));

    *gen_opc_ptr++ = INDEX_op_jmp;
    *gen_opparam_ptr++ = GET_TCGV(host_eip);


    gen_set_label(l);

    tcg_temp_free_ptr(temp_shack_top);
    tcg_temp_free(guest_eip);
    tcg_temp_free(host_eip);
    tcg_temp_free(host_eip_ptr);
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

#define IBTC_KEY(eip) ((uint16_t)(eip & IBTC_CACHE_MASK))
static struct ibtc_table *itable;
static target_ulong last_guest_eip;
void *helper_lookup_ibtc(target_ulong guest_eip)
{
    struct jmp_pair *jp = &itable->htable[IBTC_KEY(guest_eip)];
    if (jp != NULL) {
        return jp->tb->tc_ptr;
    }

    last_guest_eip = guest_eip;
    return optimization_ret_addr;
}

/*
 * update_ibtc_entry()
 *  Populate eip and tb pair in IBTC entry.
 */
void update_ibtc_entry(TranslationBlock *tb)
{
    struct jmp_pair *jp = &itable->htable[IBTC_KEY(last_guest_eip)];
    jp->guest_eip = last_guest_eip;
    jp->tb = tb;
    last_guest_eip = NULL;
}

/*
 * ibtc_init()
 *  Create and initialize indirect branch target cache.
 */

static inline void ibtc_init(CPUState *env)
{
    itable = malloc(sizeof(struct ibtc_table));
    memset(itable, 0, sizeof(struct ibtc_table));
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
