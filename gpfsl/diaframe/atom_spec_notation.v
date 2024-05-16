From iris.bi Require Export bi telescopes.
From iris.proofmode Require Import tactics notation reduction.
From iris.program_logic Require Import weakestpre lifting.
From diaframe Require Import util_classes tele_utils solve_defs.
From diaframe.symb_exec Require Import defs weakestpre weakestpre_logatom.
Import bi.

From gpfsl.diaframe Require Import vprop_weakestpre vprop_weakestpre_logatom.


Notation "'SPEC' [ pre ] ⟨ A , E , E' ⟩ x1 .. xn , << P1 ¦ P2 > > e << y1 .. yn , 'RET' e' ; Q1 ¦ Q2 > >" :=
  (AtomicReductionStep'
    wp_red_cond
    pre%I
    A E E'
    (TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
    (TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
    P1%I
    (λ x1, .. (λ xn, P2%I) .. )
    (λ x1, .. (λ xn, (λ y1, .. (λ yn, Q1%I) .. )) .. )
    (λ x1, .. (λ xn, (λ y1, .. (λ yn, Q2%I) .. )) .. )
    e%E
    (λ x1, .. (λ xn, (λ y1, .. (λ yn, e') .. )) .. )
    [tele_arg3 (A : coPset)] )
  (at level 20, A, E, E' at level 9, x1 closed binder, xn closed binder, y1 closed binder, yn closed binder, e, pre, e' at level 200, P1, P2, Q1, Q2 at level 55, format
  "'[hv' SPEC  [ pre ]  ⟨ A ,  E ,  E' ⟩  x1 .. xn ,  '/ ' <<  P1  ¦  P2  > > '/  '  e  '/ ' << '[hv'  y1 .. yn ,  'RET'  e' ; '/  '  Q1  ¦ '/  '  Q2  ']' > > ']'"
).

Notation "'SPEC' [ pre ] ⟨ A , E , E' ⟩ x1 .. xn , << P1 ¦ P2 > > e << y1 .. yn , 'RET' e' ; Q2 > >" :=
  (AtomicReductionStep'
    wp_red_cond
    pre%I
    A E E'
    (TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
    (TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
    P1%I
    (λ x1, .. (λ xn, P2%I) .. )
    (λ x1, .. (λ xn, (λ y1, .. (λ yn, True%I) .. )) .. )
    (λ x1, .. (λ xn, (λ y1, .. (λ yn, Q2%I) .. )) .. )
    e%E
    (λ x1, .. (λ xn, (λ y1, .. (λ yn, e') .. )) .. )
    [tele_arg3 (A : coPset)] )
  (at level 20, A, E, E' at level 9, x1 closed binder, xn closed binder, y1 closed binder, yn closed binder, e, pre, e' at level 200, P1, P2, Q2 at level 55, format
  "'[hv' SPEC  [ pre ]  ⟨ A ,  E ,  E' ⟩  x1 .. xn ,  '/ ' <<  P1  ¦  P2  > > '/  '  e  '/ ' << '[hv'  y1 .. yn ,  'RET'  e' ; '/  '  Q2  ']' > > ']'"
).

Notation "'SPEC' ⟨ A , E , E' ⟩ x1 .. xn , << P1 ¦ P2 > > e << y1 .. yn , 'RET' e' ; Q1 ¦ Q2 > >" :=
  (AtomicReductionStep'
    wp_red_cond
    empty_hyp_first%I
    A E E'
    (TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
    (TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
    P1%I
    (λ x1, .. (λ xn, P2%I) .. )
    (λ x1, .. (λ xn, (λ y1, .. (λ yn, Q1%I) .. )) .. )
    (λ x1, .. (λ xn, (λ y1, .. (λ yn, Q2%I) .. )) .. )
    e%E
    (λ x1, .. (λ xn, (λ y1, .. (λ yn, e') .. )) .. )
    [tele_arg3 (A : coPset)] )
  (at level 20, A, E, E' at level 9, x1 closed binder, xn closed binder, y1 closed binder, yn closed binder, e, e' at level 200, P1, P2, Q1, Q2 at level 55, format
  "'[hv' SPEC  ⟨ A ,  E ,  E' ⟩  x1 .. xn ,  '/ ' <<  P1  ¦  P2  > > '/  '  e  '/ ' << '[hv'  y1 .. yn ,  'RET'  e' ; '/  '  Q1  ¦ '/  '  Q2  ']' > > ']'"
).

Notation "'SPEC' ⟨ A , E , E' ⟩ x1 .. xn , << P1 ¦ P2 > > e << y1 .. yn , 'RET' e' ; Q2 > >" :=
  (AtomicReductionStep'
    wp_red_cond
    empty_hyp_first%I
    A E E'
    (TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
    (TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
    P1%I
    (λ x1, .. (λ xn, P2%I) .. )
    (λ x1, .. (λ xn, (λ y1, .. (λ yn, True%I) .. )) .. )
    (λ x1, .. (λ xn, (λ y1, .. (λ yn, Q2%I) .. )) .. )
    e%E
    (λ x1, .. (λ xn, (λ y1, .. (λ yn, e') .. )) .. )
    [tele_arg3 (A : coPset)] )
  (at level 20, A, E, E' at level 9, x1 closed binder, xn closed binder, y1 closed binder, yn closed binder, e, e' at level 200, P1, P2, Q2 at level 55, format
  "'[hv' SPEC  ⟨ A ,  E ,  E' ⟩  x1 .. xn ,  '/ ' <<  P1  ¦  P2  > > '/  '  e  '/ ' << '[hv'  y1 .. yn ,  'RET'  e' ; '/  '  Q2  ']' > > ']'"
).

Notation "'SPEC' [ pre ] ⟨ A , E , E' ⟩ x1 .. xn , << P1 ¦ P2 > > e << 'RET' e' ; Q1 ¦ Q2 > >" :=
  (AtomicReductionStep'
    wp_red_cond
    pre%I
    A E E'
    (TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
    TeleO
    P1%I
    (λ x1, .. (λ xn, P2%I) .. )
    (λ x1, .. (λ xn, Q1%I) .. )
    (λ x1, .. (λ xn, Q2%I) .. )
    e%E
    (λ x1, .. (λ xn, e') .. )
    [tele_arg3 (A : coPset)] )
  (at level 20, A, E, E' at level 9, x1 closed binder, xn closed binder, e, pre, e' at level 200, P1, P2, Q1, Q2 at level 55, format
  "'[hv' SPEC  [ pre ]  ⟨ A ,  E ,  E' ⟩  x1 .. xn ,  '/ ' <<  P1  ¦  P2  > > '/  '  e  '/ ' << '[hv'  'RET'  e' ; '/  '  Q1  ¦ '/  '  Q2  ']' > > ']'"
).

Notation "'SPEC' [ pre ] ⟨ A , E , E' ⟩ x1 .. xn , << P1 ¦ P2 > > e << 'RET' e' ; Q2 > >" :=
  (AtomicReductionStep'
    wp_red_cond
    pre%I
    A E E'
    (TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
    TeleO
    P1%I
    (λ x1, .. (λ xn, P2%I) .. )
    (λ x1, .. (λ xn, True%I) .. )
    (λ x1, .. (λ xn, Q2%I) .. )
    e%E
    (λ x1, .. (λ xn, e') .. )
    [tele_arg3 (A : coPset)] )
  (at level 20, A, E, E' at level 9, x1 closed binder, xn closed binder, e, pre, e' at level 200, P1, P2, Q2 at level 55, format
  "'[hv' SPEC  [ pre ]  ⟨ A ,  E ,  E' ⟩  x1 .. xn ,  '/ ' <<  P1  ¦  P2  > > '/  '  e  '/ ' << '[hv'  'RET'  e' ; '/  '  Q2  ']' > > ']'"
).

Notation "'SPEC' ⟨ A , E , E' ⟩ x1 .. xn , << P1 ¦ P2 > > e << 'RET' e' ; Q1 ¦ Q2 > >" :=
  (AtomicReductionStep'
    wp_red_cond
    empty_hyp_first%I
    A E E'
    (TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
    TeleO
    P1%I
    (λ x1, .. (λ xn, P2%I) .. )
    (λ x1, .. (λ xn, Q1%I) .. )
    (λ x1, .. (λ xn, Q2%I) .. )
    e%E
    (λ x1, .. (λ xn, e') .. )
    [tele_arg3 (A : coPset)] )
  (at level 20, A, E, E' at level 9, x1 closed binder, xn closed binder, e, e' at level 200, P1, P2, Q1, Q2 at level 55, format
  "'[hv' SPEC  ⟨ A ,  E ,  E' ⟩  x1 .. xn ,  '/ ' <<  P1  ¦  P2  > > '/  '  e  '/ ' << '[hv'  'RET'  e' ; '/  '  Q1  ¦ '/  '  Q2  ']' > > ']'"
).

Notation "'SPEC' ⟨ A , E , E' ⟩ x1 .. xn , << P1 ¦ P2 > > e << 'RET' e' ; Q2 > >" :=
  (AtomicReductionStep'
    wp_red_cond
    empty_hyp_first%I
    A E E'
    (TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
    TeleO
    P1%I
    (λ x1, .. (λ xn, P2%I) .. )
    (λ x1, .. (λ xn, True%I) .. )
    (λ x1, .. (λ xn, Q2%I) .. )
    e%E
    (λ x1, .. (λ xn, e') .. )
    [tele_arg3 (A : coPset)] )
  (at level 20, A, E, E' at level 9, x1 closed binder, xn closed binder, e, e' at level 200, P1, P2, Q2 at level 55, format
  "'[hv' SPEC  ⟨ A ,  E ,  E' ⟩  x1 .. xn ,  '/ ' <<  P1  ¦  P2  > > '/  '  e  '/ ' << '[hv'  'RET'  e' ; '/  '  Q2  ']' > > ']'"
).

Notation "'SPEC' [ pre ] ⟨ A , E , E' ⟩ x1 .. xn , << P2 > > e << y1 .. yn , 'RET' e' ; Q1 ¦ Q2 > >" :=
  (AtomicReductionStep'
    wp_red_cond
    pre%I
    A E E'
    (TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
    (TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
    True%I
    (λ x1, .. (λ xn, P2%I) .. )
    (λ x1, .. (λ xn, (λ y1, .. (λ yn, Q1%I) .. )) .. )
    (λ x1, .. (λ xn, (λ y1, .. (λ yn, Q2%I) .. )) .. )
    e%E
    (λ x1, .. (λ xn, (λ y1, .. (λ yn, e') .. )) .. )
    [tele_arg3 (A : coPset)] )
  (at level 20, A, E, E' at level 9, x1 closed binder, xn closed binder, y1 closed binder, yn closed binder, e, pre, e' at level 200, P2, Q1, Q2 at level 55, format
  "'[hv' SPEC  [ pre ]  ⟨ A ,  E ,  E' ⟩  x1 .. xn ,  '/ ' <<  P2  > > '/  '  e  '/ ' << '[hv'  y1 .. yn ,  'RET'  e' ; '/  '  Q1  ¦ '/  '  Q2  ']' > > ']'"
).

Notation "'SPEC' [ pre ] ⟨ A , E , E' ⟩ x1 .. xn , << P2 > > e << y1 .. yn , 'RET' e' ; Q2 > >" :=
  (AtomicReductionStep'
    wp_red_cond
    pre%I
    A E E'
    (TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
    (TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
    True%I
    (λ x1, .. (λ xn, P2%I) .. )
    (λ x1, .. (λ xn, (λ y1, .. (λ yn, True%I) .. )) .. )
    (λ x1, .. (λ xn, (λ y1, .. (λ yn, Q2%I) .. )) .. )
    e%E
    (λ x1, .. (λ xn, (λ y1, .. (λ yn, e') .. )) .. )
    [tele_arg3 (A : coPset)] )
  (at level 20, A, E, E' at level 9, x1 closed binder, xn closed binder, y1 closed binder, yn closed binder, e, pre, e' at level 200, P2, Q2 at level 55, format
  "'[hv' SPEC  [ pre ]  ⟨ A ,  E ,  E' ⟩  x1 .. xn ,  '/ ' <<  P2  > > '/  '  e  '/ ' << '[hv'  y1 .. yn ,  'RET'  e' ; '/  '  Q2  ']' > > ']'"
).

Notation "'SPEC' ⟨ A , E , E' ⟩ x1 .. xn , << P2 > > e << y1 .. yn , 'RET' e' ; Q1 ¦ Q2 > >" :=
  (AtomicReductionStep'
    wp_red_cond
    empty_hyp_first%I
    A E E'
    (TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
    (TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
    True%I
    (λ x1, .. (λ xn, P2%I) .. )
    (λ x1, .. (λ xn, (λ y1, .. (λ yn, Q1%I) .. )) .. )
    (λ x1, .. (λ xn, (λ y1, .. (λ yn, Q2%I) .. )) .. )
    e%E
    (λ x1, .. (λ xn, (λ y1, .. (λ yn, e') .. )) .. )
    [tele_arg3 (A : coPset)] )
  (at level 20, A, E, E' at level 9, x1 closed binder, xn closed binder, y1 closed binder, yn closed binder, e, e' at level 200, P2, Q1, Q2 at level 55, format
  "'[hv' SPEC  ⟨ A ,  E ,  E' ⟩  x1 .. xn ,  '/ ' <<  P2  > > '/  '  e  '/ ' << '[hv'  y1 .. yn ,  'RET'  e' ; '/  '  Q1  ¦ '/  '  Q2  ']' > > ']'"
).

Notation "'SPEC' ⟨ A , E , E' ⟩ x1 .. xn , << P2 > > e << y1 .. yn , 'RET' e' ; Q2 > >" :=
  (AtomicReductionStep'
    wp_red_cond
    empty_hyp_first%I
    A E E'
    (TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
    (TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
    True%I
    (λ x1, .. (λ xn, P2%I) .. )
    (λ x1, .. (λ xn, (λ y1, .. (λ yn, True%I) .. )) .. )
    (λ x1, .. (λ xn, (λ y1, .. (λ yn, Q2%I) .. )) .. )
    e%E
    (λ x1, .. (λ xn, (λ y1, .. (λ yn, e') .. )) .. )
    [tele_arg3 (A : coPset)] )
  (at level 20, A, E, E' at level 9, x1 closed binder, xn closed binder, y1 closed binder, yn closed binder, e, e' at level 200, P2, Q2 at level 55, format
  "'[hv' SPEC  ⟨ A ,  E ,  E' ⟩  x1 .. xn ,  '/ ' <<  P2  > > '/  '  e  '/ ' << '[hv'  y1 .. yn ,  'RET'  e' ; '/  '  Q2  ']' > > ']'"
).

Notation "'SPEC' [ pre ] ⟨ A , E , E' ⟩ x1 .. xn , << P2 > > e << 'RET' e' ; Q1 ¦ Q2 > >" :=
  (AtomicReductionStep'
    wp_red_cond
    pre%I
    A E E'
    (TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
    TeleO
    True%I
    (λ x1, .. (λ xn, P2%I) .. )
    (λ x1, .. (λ xn, Q1%I) .. )
    (λ x1, .. (λ xn, Q2%I) .. )
    e%E
    (λ x1, .. (λ xn, e') .. )
    [tele_arg3 (A : coPset)] )
  (at level 20, A, E, E' at level 9, x1 closed binder, xn closed binder, e, pre, e' at level 200, P2, Q1, Q2 at level 55, format
  "'[hv' SPEC  [ pre ]  ⟨ A ,  E ,  E' ⟩  x1 .. xn ,  '/ ' <<  P2  > > '/  '  e  '/ ' << '[hv'  'RET'  e' ; '/  '  Q1  ¦ '/  '  Q2  ']' > > ']'"
).

Notation "'SPEC' [ pre ] ⟨ A , E , E' ⟩ x1 .. xn , << P2 > > e << 'RET' e' ; Q2 > >" :=
  (AtomicReductionStep'
    wp_red_cond
    pre%I
    A E E'
    (TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
    TeleO
    True%I
    (λ x1, .. (λ xn, P2%I) .. )
    (λ x1, .. (λ xn, True%I) .. )
    (λ x1, .. (λ xn, Q2%I) .. )
    e%E
    (λ x1, .. (λ xn, e') .. )
    [tele_arg3 (A : coPset)] )
  (at level 20, A, E, E' at level 9, x1 closed binder, xn closed binder, e, pre, e' at level 200, P2, Q2 at level 55, format
  "'[hv' SPEC  [ pre ]  ⟨ A ,  E ,  E' ⟩  x1 .. xn ,  '/ ' <<  P2  > > '/  '  e  '/ ' << '[hv'  'RET'  e' ; '/  '  Q2  ']' > > ']'"
).

Notation "'SPEC' ⟨ A , E , E' ⟩ x1 .. xn , << P2 > > e << 'RET' e' ; Q1 ¦ Q2 > >" :=
  (AtomicReductionStep'
    wp_red_cond
    empty_hyp_first%I
    A E E'
    (TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
    TeleO
    True%I
    (λ x1, .. (λ xn, P2%I) .. )
    (λ x1, .. (λ xn, Q1%I) .. )
    (λ x1, .. (λ xn, Q2%I) .. )
    e%E
    (λ x1, .. (λ xn, e') .. )
    [tele_arg3 (A : coPset)] )
  (at level 20, A, E, E' at level 9, x1 closed binder, xn closed binder, e, e' at level 200, P2, Q1, Q2 at level 55, format
  "'[hv' SPEC  ⟨ A ,  E ,  E' ⟩  x1 .. xn ,  '/ ' <<  P2  > > '/  '  e  '/ ' << '[hv'  'RET'  e' ; '/  '  Q1  ¦ '/  '  Q2  ']' > > ']'"
).

Notation "'SPEC' ⟨ A , E , E' ⟩ x1 .. xn , << P2 > > e << 'RET' e' ; Q2 > >" :=
  (AtomicReductionStep'
    wp_red_cond
    empty_hyp_first%I
    A E E'
    (TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
    TeleO
    True%I
    (λ x1, .. (λ xn, P2%I) .. )
    (λ x1, .. (λ xn, True%I) .. )
    (λ x1, .. (λ xn, Q2%I) .. )
    e%E
    (λ x1, .. (λ xn, e') .. )
    [tele_arg3 (A : coPset)] )
  (at level 20, A, E, E' at level 9, x1 closed binder, xn closed binder, e, e' at level 200, P2, Q2 at level 55, format
  "'[hv' SPEC  ⟨ A ,  E ,  E' ⟩  x1 .. xn ,  '/ ' <<  P2  > > '/  '  e  '/ ' << '[hv'  'RET'  e' ; '/  '  Q2  ']' > > ']'"
).

Notation "'SPEC' [ pre ] ⟨ A , E , E' ⟩ << P1 ¦ P2 > > e << y1 .. yn , 'RET' e' ; Q1 ¦ Q2 > >" :=
  (AtomicReductionStep'
    wp_red_cond
    pre%I
    A E E'
    TeleO
    (TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
    P1%I
    P2%I
    (λ y1, .. (λ yn, Q1%I) .. )
    (λ y1, .. (λ yn, Q2%I) .. )
    e%E
    (λ y1, .. (λ yn, e') .. )
    [tele_arg3 (A : coPset)] )
  (at level 20, A, E, E' at level 9, y1 closed binder, yn closed binder, e, pre, e' at level 200, P1, P2, Q1, Q2 at level 55, format
  "'[hv' SPEC  [ pre ]  ⟨ A ,  E ,  E' ⟩  '/ ' <<  P1  ¦  P2  > > '/  '  e  '/ ' << '[hv'  y1 .. yn ,  'RET'  e' ; '/  '  Q1  ¦ '/  '  Q2  ']' > > ']'"
).

Notation "'SPEC' [ pre ] ⟨ A , E , E' ⟩ << P1 ¦ P2 > > e << y1 .. yn , 'RET' e' ; Q2 > >" :=
  (AtomicReductionStep'
    wp_red_cond
    pre%I
    A E E'
    TeleO
    (TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
    P1%I
    P2%I
    (λ y1, .. (λ yn, True%I) .. )
    (λ y1, .. (λ yn, Q2%I) .. )
    e%E
    (λ y1, .. (λ yn, e') .. )
    [tele_arg3 (A : coPset)] )
  (at level 20, A, E, E' at level 9, y1 closed binder, yn closed binder, e, pre, e' at level 200, P1, P2, Q2 at level 55, format
  "'[hv' SPEC  [ pre ]  ⟨ A ,  E ,  E' ⟩  '/ ' <<  P1  ¦  P2  > > '/  '  e  '/ ' << '[hv'  y1 .. yn ,  'RET'  e' ; '/  '  Q2  ']' > > ']'"
).

Notation "'SPEC' ⟨ A , E , E' ⟩ << P1 ¦ P2 > > e << y1 .. yn , 'RET' e' ; Q1 ¦ Q2 > >" :=
  (AtomicReductionStep'
    wp_red_cond
    empty_hyp_first%I
    A E E'
    TeleO
    (TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
    P1%I
    P2%I
    (λ y1, .. (λ yn, Q1%I) .. )
    (λ y1, .. (λ yn, Q2%I) .. )
    e%E
    (λ y1, .. (λ yn, e') .. )
    [tele_arg3 (A : coPset)] )
  (at level 20, A, E, E' at level 9, y1 closed binder, yn closed binder, e, e' at level 200, P1, P2, Q1, Q2 at level 55, format
  "'[hv' SPEC  ⟨ A ,  E ,  E' ⟩  '/ ' <<  P1  ¦  P2  > > '/  '  e  '/ ' << '[hv'  y1 .. yn ,  'RET'  e' ; '/  '  Q1  ¦ '/  '  Q2  ']' > > ']'"
).

Notation "'SPEC' ⟨ A , E , E' ⟩ << P1 ¦ P2 > > e << y1 .. yn , 'RET' e' ; Q2 > >" :=
  (AtomicReductionStep'
    wp_red_cond
    empty_hyp_first%I
    A E E'
    TeleO
    (TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
    P1%I
    P2%I
    (λ y1, .. (λ yn, True%I) .. )
    (λ y1, .. (λ yn, Q2%I) .. )
    e%E
    (λ y1, .. (λ yn, e') .. )
    [tele_arg3 (A : coPset)] )
  (at level 20, A, E, E' at level 9, y1 closed binder, yn closed binder, e, e' at level 200, P1, P2, Q2 at level 55, format
  "'[hv' SPEC  ⟨ A ,  E ,  E' ⟩  '/ ' <<  P1  ¦  P2  > > '/  '  e  '/ ' << '[hv'  y1 .. yn ,  'RET'  e' ; '/  '  Q2  ']' > > ']'"
).

Notation "'SPEC' [ pre ] ⟨ A , E , E' ⟩ << P1 ¦ P2 > > e << 'RET' e' ; Q1 ¦ Q2 > >" :=
  (AtomicReductionStep'
    wp_red_cond
    pre%I
    A E E'
    TeleO
    TeleO
    P1%I
    P2%I
    Q1%I
    Q2%I
    e%E
    e'
    [tele_arg3 (A : coPset)] )
  (at level 20, A, E, E' at level 9, e, pre, e' at level 200, P1, P2, Q1, Q2 at level 55, format
  "'[hv' SPEC  [ pre ]  ⟨ A ,  E ,  E' ⟩  '/ ' <<  P1  ¦  P2  > > '/  '  e  '/ ' << '[hv'  'RET'  e' ; '/  '  Q1  ¦ '/  '  Q2  ']' > > ']'"
).

Notation "'SPEC' [ pre ] ⟨ A , E , E' ⟩ << P1 ¦ P2 > > e << 'RET' e' ; Q2 > >" :=
  (AtomicReductionStep'
    wp_red_cond
    pre%I
    A E E'
    TeleO
    TeleO
    P1%I
    P2%I
    True%I
    Q2%I
    e%E
    e'
    [tele_arg3 (A : coPset)] )
  (at level 20, A, E, E' at level 9, e, pre, e' at level 200, P1, P2, Q2 at level 55, format
  "'[hv' SPEC  [ pre ]  ⟨ A ,  E ,  E' ⟩  '/ ' <<  P1  ¦  P2  > > '/  '  e  '/ ' << '[hv'  'RET'  e' ; '/  '  Q2  ']' > > ']'"
).

Notation "'SPEC' ⟨ A , E , E' ⟩ << P1 ¦ P2 > > e << 'RET' e' ; Q1 ¦ Q2 > >" :=
  (AtomicReductionStep'
    wp_red_cond
    empty_hyp_first%I
    A E E'
    TeleO
    TeleO
    P1%I
    P2%I
    Q1%I
    Q2%I
    e%E
    e'
    [tele_arg3 (A : coPset)] )
  (at level 20, A, E, E' at level 9, e, e' at level 200, P1, P2, Q1, Q2 at level 55, format
  "'[hv' SPEC  ⟨ A ,  E ,  E' ⟩  '/ ' <<  P1  ¦  P2  > > '/  '  e  '/ ' << '[hv'  'RET'  e' ; '/  '  Q1  ¦ '/  '  Q2  ']' > > ']'"
).

Notation "'SPEC' ⟨ A , E , E' ⟩ << P1 ¦ P2 > > e << 'RET' e' ; Q2 > >" :=
  (AtomicReductionStep'
    wp_red_cond
    empty_hyp_first%I
    A E E'
    TeleO
    TeleO
    P1%I
    P2%I
    True%I
    Q2%I
    e%E
    e'
    [tele_arg3 (A : coPset)] )
  (at level 20, A, E, E' at level 9, e, e' at level 200, P1, P2, Q2 at level 55, format
  "'[hv' SPEC  ⟨ A ,  E ,  E' ⟩  '/ ' <<  P1  ¦  P2  > > '/  '  e  '/ ' << '[hv'  'RET'  e' ; '/  '  Q2  ']' > > ']'"
).

Notation "'SPEC' [ pre ] ⟨ A , E , E' ⟩ << P2 > > e << y1 .. yn , 'RET' e' ; Q1 ¦ Q2 > >" :=
  (AtomicReductionStep'
    wp_red_cond
    pre%I
    A E E'
    TeleO
    (TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
    True%I
    P2%I
    (λ y1, .. (λ yn, Q1%I) .. )
    (λ y1, .. (λ yn, Q2%I) .. )
    e%E
    (λ y1, .. (λ yn, e') .. )
    [tele_arg3 (A : coPset)] )
  (at level 20, A, E, E' at level 9, y1 closed binder, yn closed binder, e, pre, e' at level 200, P2, Q1, Q2 at level 55, format
  "'[hv' SPEC  [ pre ]  ⟨ A ,  E ,  E' ⟩  '/ ' <<  P2  > > '/  '  e  '/ ' << '[hv'  y1 .. yn ,  'RET'  e' ; '/  '  Q1  ¦ '/  '  Q2  ']' > > ']'"
).

Notation "'SPEC' [ pre ] ⟨ A , E , E' ⟩ << P2 > > e << y1 .. yn , 'RET' e' ; Q2 > >" :=
  (AtomicReductionStep'
    wp_red_cond
    pre%I
    A E E'
    TeleO
    (TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
    True%I
    P2%I
    (λ y1, .. (λ yn, True%I) .. )
    (λ y1, .. (λ yn, Q2%I) .. )
    e%E
    (λ y1, .. (λ yn, e') .. )
    [tele_arg3 (A : coPset)] )
  (at level 20, A, E, E' at level 9, y1 closed binder, yn closed binder, e, pre, e' at level 200, P2, Q2 at level 55, format
  "'[hv' SPEC  [ pre ]  ⟨ A ,  E ,  E' ⟩  '/ ' <<  P2  > > '/  '  e  '/ ' << '[hv'  y1 .. yn ,  'RET'  e' ; '/  '  Q2  ']' > > ']'"
).

Notation "'SPEC' ⟨ A , E , E' ⟩ << P2 > > e << y1 .. yn , 'RET' e' ; Q1 ¦ Q2 > >" :=
  (AtomicReductionStep'
    wp_red_cond
    empty_hyp_first%I
    A E E'
    TeleO
    (TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
    True%I
    P2%I
    (λ y1, .. (λ yn, Q1%I) .. )
    (λ y1, .. (λ yn, Q2%I) .. )
    e%E
    (λ y1, .. (λ yn, e') .. )
    [tele_arg3 (A : coPset)] )
  (at level 20, A, E, E' at level 9, y1 closed binder, yn closed binder, e, e' at level 200, P2, Q1, Q2 at level 55, format
  "'[hv' SPEC  ⟨ A ,  E ,  E' ⟩  '/ ' <<  P2  > > '/  '  e  '/ ' << '[hv'  y1 .. yn ,  'RET'  e' ; '/  '  Q1  ¦ '/  '  Q2  ']' > > ']'"
).

Notation "'SPEC' ⟨ A , E , E' ⟩ << P2 > > e << y1 .. yn , 'RET' e' ; Q2 > >" :=
  (AtomicReductionStep'
    wp_red_cond
    empty_hyp_first%I
    A E E'
    TeleO
    (TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
    True%I
    P2%I
    (λ y1, .. (λ yn, True%I) .. )
    (λ y1, .. (λ yn, Q2%I) .. )
    e%E
    (λ y1, .. (λ yn, e') .. )
    [tele_arg3 (A : coPset)] )
  (at level 20, A, E, E' at level 9, y1 closed binder, yn closed binder, e, e' at level 200, P2, Q2 at level 55, format
  "'[hv' SPEC  ⟨ A ,  E ,  E' ⟩  '/ ' <<  P2  > > '/  '  e  '/ ' << '[hv'  y1 .. yn ,  'RET'  e' ; '/  '  Q2  ']' > > ']'"
).

Notation "'SPEC' [ pre ] ⟨ A , E , E' ⟩ << P2 > > e << 'RET' e' ; Q1 ¦ Q2 > >" :=
  (AtomicReductionStep'
    wp_red_cond
    pre%I
    A E E'
    TeleO
    TeleO
    True%I
    P2%I
    Q1%I
    Q2%I
    e%E
    e'
    [tele_arg3 (A : coPset)] )
  (at level 20, A, E, E' at level 9, e, pre, e' at level 200, P2, Q1, Q2 at level 55, format
  "'[hv' SPEC  [ pre ]  ⟨ A ,  E ,  E' ⟩  '/ ' <<  P2  > > '/  '  e  '/ ' << '[hv'  'RET'  e' ; '/  '  Q1  ¦ '/  '  Q2  ']' > > ']'"
).

Notation "'SPEC' [ pre ] ⟨ A , E , E' ⟩ << P2 > > e << 'RET' e' ; Q2 > >" :=
  (AtomicReductionStep'
    wp_red_cond
    pre%I
    A E E'
    TeleO
    TeleO
    True%I
    P2%I
    True%I
    Q2%I
    e%E
    e'
    [tele_arg3 (A : coPset)] )
  (at level 20, A, E, E' at level 9, e, pre, e' at level 200, P2, Q2 at level 55, format
  "'[hv' SPEC  [ pre ]  ⟨ A ,  E ,  E' ⟩  '/ ' <<  P2  > > '/  '  e  '/ ' << '[hv'  'RET'  e' ; '/  '  Q2  ']' > > ']'"
).

Notation "'SPEC' ⟨ A , E , E' ⟩ << P2 > > e << 'RET' e' ; Q1 ¦ Q2 > >" :=
  (AtomicReductionStep'
    wp_red_cond
    empty_hyp_first%I
    A E E'
    TeleO
    TeleO
    True%I
    P2%I
    Q1%I
    Q2%I
    e%E
    e'
    [tele_arg3 (A : coPset)] )
  (at level 20, A, E, E' at level 9, e, e' at level 200, P2, Q1, Q2 at level 55, format
  "'[hv' SPEC  ⟨ A ,  E ,  E' ⟩  '/ ' <<  P2  > > '/  '  e  '/ ' << '[hv'  'RET'  e' ; '/  '  Q1  ¦ '/  '  Q2  ']' > > ']'"
).

Notation "'SPEC' ⟨ A , E , E' ⟩ << P2 > > e << 'RET' e' ; Q2 > >" :=
  (AtomicReductionStep'
    wp_red_cond
    empty_hyp_first%I
    A E E'
    TeleO
    TeleO
    True%I
    P2%I
    True%I
    Q2%I
    e%E
    e'
    [tele_arg3 (A : coPset)] )
  (at level 20, A, E, E' at level 9, e, e' at level 200, P2, Q2 at level 55, format
  "'[hv' SPEC  ⟨ A ,  E ,  E' ⟩  '/ ' <<  P2  > > '/  '  e  '/ ' << '[hv'  'RET'  e' ; '/  '  Q2  ']' > > ']'"
).

