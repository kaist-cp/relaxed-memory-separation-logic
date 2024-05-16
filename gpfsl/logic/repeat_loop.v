From iris.proofmode Require Import proofmode.

From gpfsl.lang Require Export notation.
From gpfsl.logic Require Export lifting proofmode.

Require Import iris.prelude.options.

(* Repeat-until loop: repeat doing [e] until it returns true *)
Notation "'repeat:' e" :=
  ((rec: "f" []%binder :=
    let: "v" := e%E in if: "v" = #false then "f" [] else "v") [])%E
  (at level 102, e at level 200) : expr_scope.

(* TODO : improve these specs *)
Lemma wp_repeat_2 `{!noprolG Σ} tid E e `{Closed [] e} Φ (SUB: ↑histN ⊆ E) :
  WP e @ tid; E {{ v, ∃ (z: lit), ⌜v = #z ∧ z ≠ ☠%V⌝ ∧
                      if bool_decide (z = 0)
                      then ▷ |={E}=> ▷ (WP (repeat: e) @ tid; E {{ Φ }})
                      else ▷ |={E}=> ▷ Φ #z }} -∗
  WP (repeat: e) @ tid; E {{ Φ }}.
Proof.
  iIntros "H". wp_rec. wp_bind e. iApply wp_mono; [|iExact "H"].
  iIntros (v) "H". iDestruct "H" as (z) "([%%] & R)". subst v.
  wp_lam. destruct z as [|l|z]; [done|..].
  - wp_op. iMod "R"; by wp_if.
  - case (decide (z = 0)) => [->|?].
    + wp_op. iMod "R"; by wp_if.
    + rewrite bool_decide_false; [|intros ?; simplify_eq]. wp_op.
      rewrite bool_decide_false; [|done].
      iMod "R"; by wp_if.
Qed.

Lemma wp_repeat `{!noprolG Σ} tid E e `{Closed [] e} Φ (SUB: ↑histN ⊆ E) :
  WP e @ tid; E {{ v, ∃ (z: lit), ⌜v = #z ∧ z ≠ ☠%V⌝ ∧
                      if bool_decide (z = 0)
                      then |={E}=> ▷ (WP (repeat: e) @ tid; E {{ Φ }})
                      else |={E}=> ▷ Φ #z }} -∗
  WP (repeat: e) @ tid; E {{ Φ }}.
Proof.
  iIntros "H". iApply wp_repeat_2; [done|].
  iApply wp_mono; [|iExact "H"].
  iIntros (v) "H". iDestruct "H" as (z) "(H & R)". iExists z. iFrame "H".
  case (bool_decide _); by iFrame.
Qed.
