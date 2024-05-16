From iris.program_logic Require Import weakestpre.
From iris.proofmode Require Import proofmode.

From gpfsl.lang Require Export notation.
From gpfsl.logic Require Export lifting proofmode.

Require Import iris.prelude.options.

Definition for_loop i (cond incr body : expr) :=
  ((rec: "loop" ["i"] :=
      if: cond ["i"] then body ["i"] ;; "loop" [incr ["i"]] else #☠) [i])%E.

Notation "'for:' ( i := v ; cond ; incr ) body" :=
  (for_loop v (λ: [i]%binder, cond%E) (λ: [i]%binder, incr%E) (λ: [i]%binder, body%E))
  (at level 102) : expr_scope.

(* For now, force the induction variable to be a number. *)
Lemma wp_for `{!noprolG Σ} tid E (v : Z) (f : Z → Z) (c : Z → bool)
  cond incr body `{Closed [] cond, Closed [] incr, Closed [] body}
  Φ (SUB: ↑histN ⊆ E) :
  □ (∀i, {{{ ⌜c i = true⌝ ∗ Φ i }}} body [ #i] @ tid; E {{{ v, RET v; Φ (f i) }}}) -∗
  □ (∀i, {{{ True }}} incr [ #i] @ tid; E {{{ v, RET v; ⌜v = #(f i)⌝ }}}) -∗
  □ (∀i, {{{ True }}} cond [ #i] @ tid; E {{{ v, RET v; ⌜v = #(c i)⌝ }}}) -∗
  {{{ Φ v }}}
    for_loop #v cond incr body @ tid; E
  {{{ RET #☠; ∃v, ⌜c v = false⌝ ∗ Φ v }}}.
Proof.
  iIntros "#Hbody #Hincr #Hcond !>" (?) "Hv Hpost". rewrite /for_loop.
  iLöb as "I" forall (v).
  wp_rec. wp_bind (cond _). iApply "Hcond"; [done|].
  iNext; iIntros (?) "%"; subst.
  destruct (c v) eqn: Hc.
  - wp_if. wp_bind (body _).
    iApply ("Hbody" with "[$Hv]"); first done.
    iNext; iIntros (?) "Hf".
    wp_seq.
    wp_bind (incr _).
    iApply "Hincr"; first done.
    iNext; iIntros (?) "%"; subst.
    iApply ("I" with "Hf Hpost").
  - wp_if. iApply "Hpost"; iExists v; auto.
Qed.

Lemma wp_for_simple `{!noprolG Σ} tid E (v : Z) (i : string) N body Φ
  `{Closed [] body} (SUB: ↑histN ⊆ E) :
  □ (∀i, {{{ ⌜i < N⌝ ∗ Φ i }}} body [ #i] @ tid; E {{{ v, RET v; Φ (i + 1) }}}) -∗
  {{{ Φ v }}}
    for_loop #v (λ: [i], i < #N) (λ: [i], i + #1) body @ tid; E
  {{{ RET #☠; ∃v, ⌜v >= N⌝ ∗ Φ v }}}.
Proof.
  iIntros "#Hbody !>" (?) "Hpre Hpost".
  iApply (wp_for _ _ _ (fun i => i + 1) (fun i => i <? N) with "[#] [#] [#] Hpre").
  - done.
  - iIntros "!>" (??) "!> [H1 HP] H". iDestruct "H1" as %?%Z.ltb_lt.
    iApply ("Hbody" with "[$HP] H"); auto.
  - iIntros "!>" (??) "!> _ H".
    wp_let. rewrite bool_decide_true; [|done].
    wp_op. iApply "H"; auto.
  - iIntros "!>" (j?) "!> _ H".
    wp_let. rewrite bool_decide_true; [|done].
    pose proof (Zlt_cases j N).
    wp_op; destruct (j <? N); iApply "H"; auto; iPureIntro.
    + by rewrite bool_decide_true.
    + rewrite bool_decide_false; [done|lia].
  - iNext; iIntros "H"; iDestruct "H" as (?) "[H2 ?]".
    iDestruct "H2" as %?%Z.ltb_nlt.
    iApply "Hpost". eauto.
Qed.

Global Instance for_closed l i cond incr body
  {Hi : Closed l i} {Hc : Closed l cond} {Hn : Closed l incr} {Hb : Closed l body}
  : Closed l (for_loop i cond incr body).
Proof.
  rewrite /for_loop /Closed /= !andb_true_r.
  assert (l ⊆ "loop" :: "i" :: l) as Hl.
  { repeat intro. do 2 constructor; done. }
  pose proof (is_closed_weaken _ _ _ Hc Hl).
  pose proof (is_closed_weaken _ _ _ Hn Hl).
  pose proof (is_closed_weaken _ _ _ Hb Hl).
  set_solver.
Qed.

Lemma subst_for s e i cond incr body (Hs : s ≠ "loop" ∧ s ≠ "i") :
  subst s e (for_loop i cond incr body) =
  for_loop (subst s e i) (subst s e cond) (subst s e incr) (subst s e body).
Proof.
  unfold for_loop, subst; fold subst. destruct Hs.
  rewrite bool_decide_true; last by set_solver. simpl.
  rewrite (_: subst s e "i" = "i"); last first.
  { rewrite /subst. by rewrite bool_decide_false. }
  rewrite (_: subst s e (body ["i"];; "loop" [incr ["i"]])
              = ((subst s e body) ["i"];; "loop" [(subst s e incr) ["i"]])%E); [done|].
  rewrite {1}/subst /= -/subst.
  rewrite bool_decide_false; [|done].
  by rewrite bool_decide_false.
Qed.

Opaque for_loop.
