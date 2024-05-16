from notation_lib import generate_notation

mask_opts = [
    {
        'mask_not': '⟨ A , E , E\' ⟩ ',
        'mask_fmt': '⟨ A ,  E ,  E\' ⟩  ',
        'mask_top': 'A',
        'mask_val': 'A E E\'',
        'mask_levels': 'A, E, E\' at level 9, '
    }
]

binder_pre_opts = [
    {
        'binders_pre_not': 'x1 .. xn , ',
        'binders_pre_fmt': 'x1 .. xn ,  ',
        'binders_pre_tele': '(TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))',
        'binders_pre_levels': 'x1 closed binder, xn closed binder, ',
        'binders_pre_lmask': '(λ x1, .. (λ xn, ',
        'binders_pre_rmask': ') .. )',
    },
    {
        'binders_pre_not': '',
        'binders_pre_fmt': '',
        'binders_pre_tele': 'TeleO',
        'binders_pre_levels': '',
        'binders_pre_lmask': '',
        'binders_pre_rmask': '',
    },
]

private_pre_opts = [
    {
        'private_pre_not': 'P1 ¦ ',
        'private_pre_fmt': 'P1  ¦  ',
        'private_pre_val': 'P1%I',
        'private_pre_levels': 'P1, ',
    },
    {
        'private_pre_not': '',
        'private_pre_fmt': '',
        'private_pre_val': 'True%I',
        'private_pre_levels': '',
    }
]

binder_post_opts = [
    {
        'binders_post_not': 'y1 .. yn , ',
        'binders_post_fmt': 'y1 .. yn ,  ',
        'binders_post_tele': '(TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))',
        'binders_post_levels': 'y1 closed binder, yn closed binder, ',
        'binders_post_lmask': '(λ y1, .. (λ yn, ',
        'binders_post_rmask': ') .. )',
    },
    {
        'binders_post_not': '',
        'binders_post_fmt': '',
        'binders_post_tele': 'TeleO',
        'binders_post_levels': '',
        'binders_post_lmask': '',
        'binders_post_rmask': '',
    },
]

key_hyp_opts = [
    {
        'key_hyp_not': '[ pre ] ',
        'key_hyp_fmt': '[ pre ]  ',
        'key_hyp_arg': 'pre',
        'key_hyp_levels': 'pre, ',
    },
    {
        'key_hyp_not': '',
        'key_hyp_fmt': '',
        'key_hyp_arg': 'empty_hyp_first',
        'key_hyp_levels': '',
    },
]

private_post_opts = [
    {
        'private_post_not': 'Q1 ¦ ',
        'private_post_fmt': "Q1  ¦ '/  '  ",
        'private_post_val': 'Q1%I',
        'private_post_levels': 'Q1, ',
    },
    {
        'private_post_not': '',
        'private_post_fmt': '',
        'private_post_val': 'True%I',
        'private_post_levels': '',
    }
]

header = '''From iris.bi Require Export bi telescopes.
From iris.proofmode Require Import tactics notation reduction.
From iris.program_logic Require Import weakestpre lifting.
From diaframe Require Import util_classes tele_utils solve_defs.
From diaframe.symb_exec Require Import defs weakestpre weakestpre_logatom.
Import bi.

From gpfsl.diaframe Require Import vprop_weakestpre vprop_weakestpre_logatom.

'''

if __name__ == '__main__':
    print(header)

    generate_notation('''Notation "'SPEC' {key_hyp_not}{mask_not}{binders_pre_not}<< {private_pre_not}P2 > > e << {binders_post_not}'RET' e' ; {private_post_not}Q2 > >" :=
  (AtomicReductionStep'
    wp_red_cond
    {key_hyp_arg}%I
    {mask_val}
    {binders_pre_tele}
    {binders_post_tele}
    {private_pre_val}
    {binders_pre_lmask}P2%I{binders_pre_rmask}
    {binders_pre_lmask}{binders_post_lmask}{private_post_val}{binders_post_rmask}{binders_pre_rmask}
    {binders_pre_lmask}{binders_post_lmask}Q2%I{binders_post_rmask}{binders_pre_rmask}
    e%E
    {binders_pre_lmask}{binders_post_lmask}e'{binders_post_rmask}{binders_pre_rmask}
    [tele_arg3 ({mask_top} : coPset)] )
  (at level 20, {mask_levels}{binders_pre_levels}{binders_post_levels}e, {key_hyp_levels}e' at level 200, {private_pre_levels}P2, {private_post_levels}Q2 at level 55, format
  "'[hv' SPEC  {key_hyp_fmt}{mask_fmt}{binders_pre_fmt}'/ ' <<  {private_pre_fmt}P2  > > '/  '  e  '/ ' << '[hv'  {binders_post_fmt}'RET'  e' ; '/  '  {private_post_fmt}Q2  ']' > > ']'"
).
''', [
        mask_opts,
        binder_pre_opts,
        private_pre_opts,
        binder_post_opts,
        key_hyp_opts,
        private_post_opts,
    ])


    # generate_notation('''Notation "'SPEC2' {key_hyp1}{mask_not1}{binders_pre1}{{{{ Ps }} }} e{stuckness1} {{{{ {laters_not1}'RET' [ e' ] ; Qs }} }}" :=
    #   (ReductionStep'
    #     wp_red_cond
    #     {key_hyp_arg}%I
    #     e
    #     {laters_arg}
    #     {mask_open}
    #     {mask_close}
    #     {binders_tele}
    #     _
    #     {binders_pre_lmask}Ps%I{binders_pre_rmask}
    #     e'
    #     Qs%I
    #     [tele_arg {mask_arg} ; {stuckness_arg}] )
    #   (at level 20, {laters_levels}{mask_levels}{binders_levels}{stuckness_levels}e, Ps, {key_hyp_levels}e', Qs at level 200, format
    #   "'[hv' SPEC2  {key_hyp2}{mask_not2}{binders_pre2}'/ ' {{{{  Ps  }} }} '/  '  e{stuckness2}  '/ ' {{{{  {laters_not2}'RET'  [ e' ] ; '/  '  Qs  }} }} ']'", only printing
    # ).
    # ''', [
    #     mask_opts,
    #     [binder_pre_opts[0]],
    #     stuckness_opts,
    #     key_hyp_opts,
    #     later_opts,
    # ])
