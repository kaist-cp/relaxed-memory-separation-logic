From diaframe Require Import proofmode_base.
From gpfsl.logic Require Import proofmode atomics invariants.
From gpfsl.examples.algebra Require Import mono_list.


Require Import iris.prelude.options.


Section hints.

Context `{!mono_listG A Σ}.

#[local] Notation iProp := (iProp Σ).
#[local] Notation vProp := (vProp Σ).

(* Todo: remove. *)
(* #[global] Instance mergable_consume_mono_list_auth_idx_lookup γ q l i a :
  MergableConsume (PROP := vProp) (⎡ mono_list_auth_own γ q l ⎤) true (λ p Pin Pout,
    (TCAnd (TCEq Pin (⎡ mono_list_idx_own γ i a ⎤)) $
      TCEq Pout (⌜l !! i = Some a⌝ ∗ ⎡ mono_list_auth_own γ q l ⎤ ∗ ⎡ mono_list_idx_own γ i a ⎤))
  )%I.
Proof.
  intros p Pin Pout [-> ->]. rewrite bi.intuitionistically_if_elim.
  iIntros "[A B]". iDestruct (mono_list_auth_idx_lookup with "A B") as "%". auto.
Qed. *)

#[global] Instance mergable_consume_mono_list_auth_idx_lookup_rev γ q l i a :
  MergablePersist (PROP := vProp) (⎡ mono_list_idx_own γ i a ⎤) (λ p Pin Pout,
    (TCAnd (TCEq Pin (⎡ mono_list_auth_own γ q l ⎤)) $
      TCEq Pout (⌜l !! i = Some a⌝))
  )%I.
Proof.
  intros p Pin Pout [-> ->]. rewrite bi.intuitionistically_if_elim.
  iIntros "[A B]". iDestruct (mono_list_auth_idx_lookup with "B A") as "%". auto.
Qed.

#[global] Instance mergable_consume_mono_list_auth_lb_valid γ q l1 l2 :
  MergableConsume (PROP := vProp) (⎡ mono_list_auth_own γ q l1 ⎤) true (λ p Pin Pout,
      (TCAnd (TCEq Pin (⎡ mono_list_lb_own γ l2 ⎤)) $
        TCIf (TCEq l1 l2)
          (TCEq Pout ( ⎡ mono_list_auth_own γ q l1 ⎤))
          (TCEq Pout (⌜l2 `prefix_of` l1⌝ ∗ ⎡ mono_list_auth_own γ q l1 ⎤))
      )
  )%I.
Proof.
  intros p Pin Pout [-> [-> ->| ->]]; rewrite bi.intuitionistically_if_elim; iIntros "[A B]";
  iDestruct (mono_list_auth_lb_valid with "A B") as "[% %]"; auto.
Qed.

#[global] Instance mergable_consume_mono_list_lb_own_rev γ q l1 l2 :
  MergableConsume (PROP := vProp) (⎡ mono_list_lb_own γ l2 ⎤) false (λ p Pin Pout,
      (TCAnd (TCEq Pin (⎡ mono_list_auth_own γ q l1 ⎤)) $
       TCIf (TCEq l1 l2) False $
        TCEq Pout (⎡ mono_list_lb_own γ l2 ⎤ ∗ ⎡ mono_list_auth_own γ q l1 ⎤))
  )%I.
Proof.
  intros p Pin Pout [-> [?| ->]]; [done|]. rewrite bi.intuitionistically_if_elim. iIntros "[$ $]".
Qed.

#[global] Instance mergable_persist_mono_list_lb_own_get γ q l :
  MergablePersist (PROP := vProp) (⎡ mono_list_auth_own γ q l ⎤) (λ p Pin Pout,
      (TCAnd (TCEq Pin (ε₀)) $
        TCEq Pout (⎡ mono_list_lb_own γ l ⎤))
  )%I.
Proof.
  intros p Pin Pout [-> ->]. rewrite bi.intuitionistically_if_elim.
  iIntros "[A _]". iDestruct (mono_list_lb_own_get with "A") as "#?". auto.
Qed.


Section test.
Context `{!noprolG Σ}.
#[local] Lemma test_mono_list_auth_intro γ q l l2 lo v :
  ⎡ mono_list_auth_own γ q l ⎤ -∗ ⎡ mono_list_lb_own γ l2 ⎤ -∗ lo ↦ v.
Proof.
  iStepDebug. solveStep. solveStep.
  iStepDebug. solveStep. solveStep. solveStep. solveStep. solveStep.
  solveStep. solveStep. solveStep. solveStep.
Abort.

End test.

#[global] Instance biabd_mono_list_lb_own_le p γ l l':
  HINT □⟨ p ⟩ @embed _ vProp _ (mono_list_lb_own γ l) ✱ [-; ⌜ l' `prefix_of` l ⌝ ]
  ⊫ [id]
  ; ⎡ mono_list_lb_own γ l' ⎤✱ [ emp ] | 100.
Proof using All.
  iStep as (?) "A". rewrite bi.intuitionistically_if_elim. iSplitL; last done. by iApply (mono_list_lb_own_le).
Qed.


#[global] Instance biabd_mono_list_idx_own_get γ i a :
HINT ε₁ ✱ [l; ⎡ mono_list_lb_own γ l ⎤ ∗ ⌜ l !! i = Some a ⌝ ]
⊫ [id]
; @embed _ vProp _ (mono_list_idx_own γ i a) ✱ [ emp ].
Proof.
iStep. iIntros "(_ & A & %)". iDestruct (mono_list_idx_own_get with "A") as "$". done.
Qed.

#[global] Instance mergable_consume_mono_list_idx_agree γ i a1 a2 :
  MergableConsume (PROP := vProp) (⎡ mono_list_idx_own γ i a1 ⎤) false (λ p Pin Pout,
      (TCAnd (TCEq Pin (⎡ mono_list_idx_own γ i a2 ⎤)) $
        TCEq Pout (⌜a1 = a2⌝))
  )%I.
Proof.
  intros p Pin Pout [-> ->]. rewrite bi.intuitionistically_if_elim.
  iIntros "[A B]". by iDestruct (mono_list_idx_agree with "A B") as "%".
Qed.

End hints.
