From iris.proofmode Require Import proofmode.

From gpfsl.base_logic Require Import vprop history.

Section preds.
Context `{!noprolG Σ}.
#[local] Notation iProp := (iProp Σ).
#[local] Notation vProp := (vProp Σ).

Program Definition seen_time l t : vProp :=
  MonPred (λ V0, ⌜seen_local l t V0⌝)%I _.
Next Obligation.
  intros ?????. iIntros "!%". by eapply seen_local_mono.
Qed.
Program Definition seen_view l t V : vProp :=
  MonPred (λ V0, ⌜seen_local l t V0 ∧ V ⊑ V0⌝)%I _.
Next Obligation.
  intros ?????. iIntros (?) "!%". move => [??]. split; [|solve_lat].
  eapply seen_local_mono; eauto.
Qed.

Program Definition AllocLocal l C : vProp :=
  MonPred (λ V0, ⌜alloc_local l C V0⌝)%I _.
Next Obligation. intros ?????. iIntros "!%". by apply alloc_local_mono. Qed.
Program Definition NaLocal l rs Va : vProp :=
  MonPred (λ V0, ⌜na_local l rs Va ∧ Va ⊑ V0⌝)%I _.
Next Obligation.
  intros ?????. iIntros (?) "!%". move => [??]. split; [|solve_lat].
  by eapply na_local_mono; eauto.
Qed.
Program Definition AtRLocal l rs : vProp :=
  MonPred (λ V0, ⌜atr_local l rs V0⌝)%I _.
Next Obligation. intros ?????. iIntros "!%". by apply atr_local_mono. Qed.
Program Definition AtWLocal l ws : vProp :=
  MonPred (λ V0, ⌜atw_local l ws V0⌝)%I _.
Next Obligation. intros ?????. iIntros "!%". by apply atw_local_mono. Qed.

(* Local predicates *)
#[global] Instance seen_time_persistent l t :
  Persistent (seen_time l t) := monPred_persistent _ _.
#[global] Instance seen_time_timeless l t :
  Timeless (seen_time l t) := monPred_timeless _ _.

#[global] Instance seen_view_persistent l t V :
  Persistent (seen_view l t V) := monPred_persistent _ _.
#[global] Instance seen_view_timeless l t V :
  Timeless (seen_view l t V) := monPred_timeless _ _.

#[global] Instance AllocLocal_persistent l C :
  Persistent (AllocLocal l C) := monPred_persistent _ _.
#[global] Instance AllocLocal_timeless l C :
  Timeless (AllocLocal l C) := monPred_timeless _ _.

#[global] Instance NaLocal_persistent l rs Va :
  Persistent (NaLocal l rs Va) := monPred_persistent _ _.
#[global] Instance NaLocal_timeless l rs Va :
  Timeless (NaLocal l rs Va) := monPred_timeless _ _.

#[global] Instance AtRLocal_persistent l rs :
  Persistent (AtRLocal l rs) := monPred_persistent _ _.
#[global] Instance AtRLocal_timeless l rs :
  Timeless (AtRLocal l rs) := monPred_timeless _ _.

#[global] Instance AtWLocal_persistent l ws :
  Persistent (AtWLocal l ws) := monPred_persistent _ _.
#[global] Instance AtWLocal_timeless l ws :
  Timeless (AtWLocal l ws) := monPred_timeless _ _.

Lemma AtRLocal_view_at Vb l rs :
  @{Vb} AtRLocal l rs ⊢@{vPropI Σ} ⌜atr_local l rs Vb⌝.
Proof. rewrite view_at_eq. by iDestruct 1 as "%". Qed.

#[global] Instance into_pure_AtRLocal Vb l rs :
  @IntoPure (vPropI Σ) (@{Vb} AtRLocal l rs) (atr_local l rs Vb).
Proof. rewrite /IntoPure. apply AtRLocal_view_at. Qed.

Lemma AtWLocal_view_at Vb l ws :
  @{Vb} AtWLocal l ws ⊢@{vPropI Σ} ⌜atw_local l ws Vb⌝.
Proof. rewrite view_at_eq. by iDestruct 1 as "%". Qed.

#[global] Instance into_pure_AtWLocal Vb l ws :
  @IntoPure (vPropI Σ) (@{Vb} AtWLocal l ws) (atw_local l ws Vb).
Proof. rewrite /IntoPure. apply AtWLocal_view_at. Qed.

Lemma AllocLocal_view_at Vb l C :
  @{Vb} AllocLocal l C ⊢@{vPropI Σ} ⌜alloc_local l C Vb⌝.
Proof. rewrite view_at_eq. by iDestruct 1 as "%". Qed.

#[global] Instance into_pure_AllocLocal Vb l C :
  @IntoPure (vPropI Σ) (@{Vb} AllocLocal l C) (alloc_local l C Vb).
Proof. rewrite /IntoPure. apply AllocLocal_view_at. Qed.

Lemma NaLocal_view_at Vb l rs Va :
  @{Vb} NaLocal l rs Va ⊢@{vPropI Σ} ⌜na_local l rs Va ∧ Va ⊑ Vb⌝.
Proof. rewrite view_at_eq. by iDestruct 1 as "%". Qed.

#[global] Instance into_pure_NaLocal Vb l rs Va :
  @IntoPure (vPropI Σ) (@{Vb} NaLocal l rs Va) (na_local l rs Va ∧ Va ⊑ Vb).
Proof. rewrite /IntoPure. apply NaLocal_view_at. Qed.

Lemma seen_view_seen_time l t V :
  seen_view l t V ⊣⊢ seen_time l t ∗ ⊒V.
Proof.
  constructor => ?. rewrite monPred_at_sep /= monPred_at_in.
  apply : anti_symm; eauto.
Qed.

Lemma seen_time_AllocLocal_singleton l t m :
  m.(mval) ≠ DVal →
  seen_time l t ⊢ AllocLocal l {[t := m]}.
Proof.
  intros. constructor => V. iPureIntro. intros ?. exists t, m.
  by rewrite lookup_insert.
Qed.

Lemma seen_time_AllocLocal_singleton_inv l t m :
  AllocLocal l {[t := m]} ⊢ seen_time l t.
Proof.
  intros. constructor => V. iPureIntro.
  intros (t' & m' & []%lookup_singleton_Some & ? & ?). by subst.
Qed.

Lemma AtRLocal_join l rsa1 rsa2 :
  AtRLocal l rsa1 ∗ AtRLocal l rsa2 ⊣⊢ AtRLocal l (rsa1 ∪ rsa2).
Proof.
  constructor => V. rewrite monPred_at_sep /=. iPureIntro. split.
  - intros []. by apply atr_local_join.
  - intros ?. split; eapply atr_local_mono; eauto; simpl; solve_lat.
Qed.

Lemma AtWLocal_join l wsa1 wsa2 :
  AtWLocal l wsa1 ∗ AtWLocal l wsa2 ⊣⊢ AtWLocal l (wsa1 ∪ wsa2).
Proof.
  constructor => V. rewrite monPred_at_sep /=. iPureIntro. split.
  - intros []. by apply atw_local_join.
  - intros ?. split; eapply atw_local_mono; eauto; simpl; solve_lat.
Qed.

Lemma NaLocal_join_read l rs1 rs2 Va :
  NaLocal l rs1 Va ∗ NaLocal l rs2 Va ⊣⊢ NaLocal l (rs1 ∪ rs2) Va.
Proof.
  constructor => V. rewrite monPred_at_sep /=. iPureIntro. split.
  - intros [[] []]. split; [|done]. by apply na_local_join.
  - intros []. split; (split; last done); eapply na_local_mono; eauto; simpl; solve_lat.
Qed.

Lemma NaLocal_join l rs1 rs2 Va1 Va2 :
  NaLocal l rs1 Va1 ∗ NaLocal l rs2 Va2 ⊢ NaLocal l (rs1 ∪ rs2) (Va1 ⊔ Va2).
Proof.
  constructor => V. rewrite monPred_at_sep /=. iPureIntro.
  intros [[] []]. split; [|solve_lat]. by apply na_local_join'.
Qed.

Lemma NaLocal_seen l rs V :
  NaLocal l rs V ⊢ ⊒V.
Proof. constructor => V'. iPureIntro. by intros []. Qed.
End preds.
