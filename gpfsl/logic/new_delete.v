From gpfsl.base_logic Require Import na meta_data.
From gpfsl.logic Require Import proofmode.

Require Import iris.prelude.options.

From gpfsl.diaframe Require Import base_specs spec_notation.
From diaframe Require Import proofmode_base lib.except_zero.

Definition new : val :=
  λ: ["n"],
    if: "n" ≤ #0 then #((42%positive, 1337):loc)
    else Alloc "n".

Definition delete : val :=
  λ: ["n"; "loc"],
    if: "n" ≤ #0 then #☠
    else Free "n" "loc".

Section specs.
Context `{!noprolG Σ}.

Lemma wp_new E tid (n : Z):
  ↑histN ⊆ E → (0 ≤ n)%Z →
  {{{ True }}} new [ #n ] @ tid; E
  {{{ l, RET LitV $ LitLoc l;
      (⎡†l…(Z.to_nat n)⎤ ∨ ⌜n = 0⌝) ∗
      l ↦∗ repeat #☠ (Z.to_nat n) ∗
      [∗ list] i ∈ seq 0 (Z.to_nat n), meta_token (l >> i) ⊤ }}}.
Proof.
  iSteps. case_bool_decide; iSteps.
  replace n with 0%Z by lia.
  rewrite own_loc_na_vec_nil. iSteps.
Qed.

Global Instance wp_new_spec n E :
  SolveSepSideCondition (↑histN ⊆ E) →
  SPEC ⟨E⟩ {{ ⌜0 ≤ n⌝%Z }}
    new [ #n ]
  {{ (l : loc), RET #l;
      (⎡†l…(Z.to_nat n)⎤ ∨ ⌜n = 0⌝) ∗
      l ↦∗ repeat #☠ (Z.to_nat n) ∗
      [∗ list] i ∈ seq 0 (Z.to_nat n), meta_token (l >> i) ⊤
  }}.
Proof.
  move => HE. do 2 iStep. iApply wp_new; [exact HE | done | iSteps..].
  rewrite own_loc_na_vec_nil. iSteps.
Qed.

Lemma wp_delete E tid (n:Z) l vl :
  ↑histN ⊆ E → n = length vl →
  {{{ l ↦∗ vl ∗ (⎡†l…(length vl)⎤ ∨ ⌜n = 0⌝) }}}
    delete [ #n; #l] @ tid; E
  {{{ RET #☠; True }}}.
Proof.
  iIntros (?? Φ) "[H↦ [H†|%]] HΦ";
  wp_lam; wp_op; case_bool_decide; try lia;
  wp_if; try wp_free; by iApply "HΦ".
Qed.

Global Instance wp_delete_spec (n:Z) l E:
  SolveSepSideCondition (↑histN ⊆ E) →
  SPEC ⟨E⟩ {{ (⎡†l…(Z.to_nat n)⎤ ∨ ⌜n = 0⌝) ∗ ▷ own_loc_vec l 1 (Z.to_nat n) }}
    delete [ #n; #l]
  {{ RET #☠; True }}.
Proof.
  move => HE. iSteps; case_bool_decide; try lia; iSteps.
Qed.

End specs.
