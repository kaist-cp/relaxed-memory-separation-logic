from notation_lib import generate_notation

mask_opts = [
    {
        'mask_not1': '⟨ E1 , E2 ⟩ ',
        'mask_not2': '⟨ E1 , E2 ⟩  ',
        'mask_open': '(fupd E1 E2)',
        'mask_close': '(fupd E2 E1)',
        'mask_levels': 'E1, E2 at level 9, ',
        'mask_arg': 'E1',
    },
    {
        'mask_not1': '⟨ E1 ⟩ ',
        'mask_not2': '⟨ E1 ⟩  ',
        'mask_open': '(fupd E1 E1)',
        'mask_close': '(fupd E1 E1)',
        'mask_levels': 'E1 at level 9, ',
        'mask_arg': 'E1',
    },
    {
        'mask_not1': '',
        'mask_not2': '',
        'mask_open': '(fupd ⊤ ⊤)',
        'mask_close': '(fupd ⊤ ⊤)',
        'mask_levels': '',
        'mask_arg': '(⊤ : coPset)',
    },
]

binder_pre_opts = [
    {
        'binders_pre1': 'x1 .. xn , ',
        'binders_pre2': 'x1 .. xn ,  ',
        'binders_tele': '(TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))',
        'binders_levels': 'x1 closed binder, xn closed binder, ',
        'binders_pre_lmask': '(λ x1, .. (λ xn, ',
        'binders_pre_rmask': ') .. )',
    },
    {
        'binders_pre1': '',
        'binders_pre2': '',
        'binders_tele': 'TeleO',
        'binders_levels': '',
        'binders_pre_lmask': '',
        'binders_pre_rmask': '',
    },
]

key_hyp_opts = [
    {
        'key_hyp1': '[ pre ] ',
        'key_hyp2': '[ pre ]  ',
        'key_hyp_arg': 'pre',
        'key_hyp_levels': 'pre, ',
    },
    {
        'key_hyp1': '',
        'key_hyp2': '',
        'key_hyp_arg': 'empty_hyp_first',
        'key_hyp_levels': '',
    },
]

later_opts = [
    {
        'laters_not1': '[ ▷^ n ] ',
        'laters_not2': '[ ▷^ n ]  ',
        'laters_arg': 'n',
        'laters_levels': 'n at level 9, ',
    },
    {
        'laters_not1': '',
        'laters_not2': '',
        'laters_arg': '1',
        'laters_levels': '',
    },
]

binder_post_opts = [
    {
        'binders_post1': 'y1 .. yn , ',
        'binders_post_tele': '(TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))',
        'binders_post2': 'y1 .. yn ,  ',
        'binders_post_lmask': '(λ y1, .. (λ yn, ',
        'binders_post_rmask': ') .. )',
        'binders_post_levels': 'y1 closed binder, yn closed binder, '
    },
    {
        'binders_post1': '',
        'binders_post_tele': 'TeleO',
        'binders_post2': '',
        'binders_post_lmask': '',
        'binders_post_rmask': '',
        'binders_post_levels': ''
    }
]

header = '''From iris.bi Require Export bi telescopes.
From iris.proofmode Require Import tactics notation reduction.
From iris.program_logic Require Import weakestpre lifting.
From diaframe Require Import util_classes tele_utils solve_defs.
From diaframe.symb_exec Require Import defs.

From gpfsl.diaframe Require Import vprop_weakestpre.

Import bi.

'''

if __name__ == '__main__':
    print(header)

    generate_notation('''Notation "'SPEC' {key_hyp1}{mask_not1}{binders_pre1}{{{{ Ps }} }} e {{{{ {laters_not1}{binders_post1}'RET' e' ; Qs }} }}" :=
  (ReductionStep'
    wp_red_cond
    {key_hyp_arg}%I
    {laters_arg}
    {mask_open}
    {mask_close}
    {binders_tele}
    {binders_post_tele}
    {binders_pre_lmask}Ps%I{binders_pre_rmask}
    {binders_pre_lmask}{binders_post_lmask}Qs%I{binders_post_rmask}{binders_pre_rmask}
    e%E
    {binders_pre_lmask}{binders_post_lmask}e'{binders_post_rmask}{binders_pre_rmask}
    [tele_arg3 {mask_arg}] )
  (at level 20, {laters_levels}{mask_levels}{binders_levels}{binders_post_levels}e, Ps, {key_hyp_levels}e', Qs at level 200, format
  "'[hv' SPEC  {key_hyp2}{mask_not2}{binders_pre2}'/ ' {{{{  Ps  }} }} '/  '  e  '/ ' {{{{ '[hv'  {laters_not2}{binders_post2}'RET'  e' ; '/  '  Qs  ']' }} }} ']'"
).
''', [
        mask_opts,
        binder_pre_opts,
        key_hyp_opts,
        later_opts,
        binder_post_opts,
    ])


    generate_notation('''Notation "'SPEC2' {key_hyp1}{mask_not1}{binders_pre1}{{{{ Ps }} }} e {{{{ {laters_not1}'RET' [ e' ] ; Qs }} }}" :=
  (ReductionStep'
    wp_red_cond
    {key_hyp_arg}%I
    {laters_arg}
    {mask_open}
    {mask_close}
    {binders_tele}
    _
    {binders_pre_lmask}Ps%I{binders_pre_rmask}
    Qs%I
    e
    e'
    [tele_arg3 {mask_arg}] )
  (at level 20, {laters_levels}{mask_levels}{binders_levels}e, Ps, {key_hyp_levels}e', Qs at level 200, format
  "'[hv' SPEC2  {key_hyp2}{mask_not2}{binders_pre2}'/ ' {{{{  Ps  }} }} '/  '  e  '/ ' {{{{  {laters_not2}'RET'  [ e' ] ; '/  '  Qs  }} }} ']'", only printing
).
''', [
        mask_opts,
        [binder_pre_opts[0]],
        key_hyp_opts,
        later_opts,
    ])
