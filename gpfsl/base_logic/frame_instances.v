From iris.bi Require Export monpred big_op.
From iris.proofmode Require Import proofmode monpred modality_instances.
From iris.base_logic.lib Require Import fancy_updates.

From gpfsl.base_logic Require Export vprop.

Require Import iris.prelude.options.

Section instances.
Context `{Σ : gFunctors}.
#[local] Notation vProp := (vProp Σ).
Implicit Types (P Q R : vProp) (V : view).

Example test_before P Q V :
  ⊔{V} P ∗ ⊔{V} Q ⊢ ⊔{V} (P ∗ Q).
Proof. Fail iIntros "[$ $]". Abort.
Example test_before P Q V1 V2 (SUB: V1 ⊑ V2) :
  ⊔{V1} P ∗ ⊔{V1} Q ⊢ ⊔{V2} (P ∗ Q).
Proof. Fail iIntros "[$ $]". Abort.

#[global] Instance frame_view_join_view_mono p R P Q V1 V2 :
  IsBiIndexRel V1 V2 →
  Frame p R P Q → Frame p (⊔{V1} R) (⊔{V2} P) (⊔{V2} Q).
Proof.
  rewrite /Frame /IsBiIndexRel -view_join_intuitionistically_if => -> H.
  rewrite -view_join_sep.
  by apply view_join_wand_2, view_join_at, bi.entails_wand.
Qed.

#[global] Instance frame_view_join_view_mono_emp p P V1 V2 :
  IsBiIndexRel V1 V2 → Frame p (⊔{V1} P) (⊔{V2} P) emp | 0.
Proof.
  rewrite /Frame /IsBiIndexRel=> ->. by rewrite right_id bi.intuitionistically_if_elim.
Qed.

Example test_after P Q V :
  ⊔{V} P ∗ ⊔{V} Q ⊢ ⊔{V} (P ∗ Q).
Proof. iIntros "[$ $]". Abort.
Example test_after P Q V1 V2 (SUB: V1 ⊑ V2) :
  ⊔{V1} P ∗ ⊔{V1} Q ⊢ ⊔{V2} (P ∗ Q).
Proof. iIntros "[$ $]". Abort.

Example test_before R V : R ⊢ ⊔{V} R.
Proof. Fail iIntros "$". Abort.
#[global] Instance frame_current_view_join p R P Q V :
  Frame p R P Q → Frame p R (⊔{V} P) (⊔{V} Q).
Proof.
  rewrite /Frame => H.
  rewrite (view_join_intro_current R V) -view_join_intuitionistically_if -view_join_sep.
  by apply view_join_wand_2, view_join_at, bi.entails_wand.
Qed.
Example test_after R V : R ⊢ ⊔{V} R.
Proof. iIntros "$". Abort.
Example test_after P Q V : P ∗ ⊔{V} Q ⊢ ⊔{V} (P ∗ Q).
Proof. iIntros "[$ $]". Abort.

#[global] Instance frame_current_view_join_emp p P V :
  Frame p P (⊔{V} P) emp | 0.
Proof.
  by rewrite /Frame right_id bi.intuitionistically_if_elim -view_join_intro_current.
Qed.

Example test_before P Q V :
  @{V} P ∗ ⊔{V} Q ⊢ ⊔{V} (P ∗ Q).
Proof. Fail iIntros "[$ $]". Abort.
Example test_before P Q V1 V2 (SUB: V1 ⊑ V2) :
  @{V1} P ∗ ⊔{V1} Q ⊢ ⊔{V2} (P ∗ Q).
Proof. Fail iIntros "[$ $]". Abort.
#[global] Instance frame_view_at_view_join p R P Q V1 V2 :
  IsBiIndexRel V1 V2 →
  Frame p R P Q → Frame p (@{V1} R) (⊔{V2} P) (⊔{V2} Q).
Proof.
  rewrite /Frame /IsBiIndexRel -view_at_intuitionistically_if => ->.
  rewrite view_at_to_view_join -view_join_sep => ?.
  by apply view_join_wand_2, view_join_at, bi.entails_wand.
Qed.
Example test_after P Q V :
  @{V} P ∗ ⊔{V} Q ⊢ ⊔{V} (P ∗ Q).
Proof. iIntros "[$ $]". Abort.
Example test_after P Q V1 V2 (SUB: V1 ⊑ V2) :
  @{V1} P ∗ ⊔{V1} Q ⊢ ⊔{V2} (P ∗ Q).
Proof. iIntros "[$ $]". Abort.

#[global] Instance frame_view_at_view_join_emp p P V1 V2 :
  IsBiIndexRel V1 V2 → Frame p (@{V1} P) (⊔{V2} P) emp | 0.
Proof.
  by rewrite /Frame /IsBiIndexRel right_id bi.intuitionistically_if_elim
              view_at_to_view_join => ->.
Qed.

#[global] Instance frame_view_join_from_embed p (R : iProp Σ) V :
  Frame p (⊔{V} ⎡ R ⎤) ⎡ R ⎤ emp | 0.
Proof.
  by rewrite /Frame view_join_embed right_id bi.intuitionistically_if_elim.
Qed.

(* view_at *)
#[global] Instance frame_view_at_from_embed p (R : iProp Σ) V :
  Frame p (@{V} ⎡ R ⎤) ⎡ R ⎤ emp | 0.
Proof.
  by rewrite /Frame view_at_embed right_id bi.intuitionistically_if_elim.
Qed.

#[global] Instance frame_view_at_view_mono p R P Q V1 V2 :
  IsBiIndexRel V1 V2 →
  Frame p R P Q → Frame p (@{V1} R) (@{V2} P) (@{V2} Q).
Proof.
  rewrite /Frame /IsBiIndexRel -view_at_intuitionistically_if => -> H.
  rewrite -view_at_sep.
  by apply view_at_wand_2, view_at_at, bi.entails_wand.
Qed.

#[global] Instance frame_view_at_view_mono_emp p P V1 V2 :
  IsBiIndexRel V1 V2 → Frame p (@{V1} P) (@{V2} P) emp | 0.
Proof.
  by rewrite /Frame /IsBiIndexRel right_id bi.intuitionistically_if_elim => ->.
Qed.

#[global] Instance frame_objective_view_at p R P Q V `{!Objective R} :
  Frame p R P Q → Frame p R (@{V} P) (@{V} Q).
Proof.
  rewrite /Frame -{2}(view_at_objective_iff R V).
  apply frame_view_at_view_mono. by rewrite /IsBiIndexRel.
Qed.

(* TODO: generalize. This needs only a lattice on the biIndex. *)
#[global] Instance frame_subjectively_view_from_embed p R P Q V :
  Frame p R P Q → Frame p (⎡ R V ⎤) (<subj> P) (<subj> Q).
Proof.
  rewrite /Frame. intros <-. rewrite view_subjectively_sep. apply bi.sep_mono_l.
  rewrite monPred_subjectively_unfold embed_exist
          -embed_intuitionistically_if -monPred_at_intuitionistically_if.
  by eauto.
Qed.

End instances.
