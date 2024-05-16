From iris.algebra Require Import auth.
From iris.algebra Require Import proofmode_classes.
From iris.base_logic Require Import lib.own.
From iris.proofmode Require Import proofmode.

From gpfsl.algebra Require Import lattice_cmra.

Require Import iris.prelude.options.

Definition lat_authR (LAT : latticeT) `{!@LatBottom LAT bot} := authR (latUR LAT).

Definition lat_auth `{!@LatBottom LAT bot} q a : lat_authR LAT :=
  ●{q} to_latT a ⋅ ◯ to_latT a.
Definition lat_lb   `{!@LatBottom LAT bot} a   : lat_authR LAT :=
  ◯ to_latT a.

(** FIXME: Refactor these notations using custom entries once Coq bug #13654
has been fixed. *)
Notation "●L{ dq } l" :=
  (lat_auth dq l) (at level 20, format "●L{ dq }  l").
Notation "●L{# q } l" :=
  (lat_auth (DfracOwn q) l) (at level 20, format "●L{# q }  l").
Notation "●□ML l" := (lat_auth DfracDiscarded l) (at level 20).
Notation "●L l" := (lat_auth (DfracOwn 1) l) (at level 20).
Notation "◯L l" := (lat_lb l) (at level 20).


Section props.
Context {LAT : latticeT} `{!@LatBottom LAT bot}.
(* TODO dfrac vs frac *)

(** Setoid properties *)
Global Instance lat_auth_proper dq : Proper ((≡) ==> (≡)) (@lat_auth LAT _ _ dq).
Proof. solve_proper. Qed.
Global Instance lat_lb_proper : Proper ((≡) ==> (≡)) (@lat_lb LAT _ _).
Proof. solve_proper. Qed.

Global Instance lat_lb_inj : Inj (≡) (≡) (@lat_lb LAT _ _).
Proof. rewrite /lat_lb. by intros ?? ?%(inj _)%(inj _). Qed.

(** * Operations *)
Global Instance lat_lb_core_id a : CoreId (◯L a).
Proof. rewrite /lat_lb. apply _. Qed.

Lemma lat_auth_dfrac_op dq1 dq2 a :
  ●L{dq1 ⋅ dq2} a ≡ ●L{dq1} a ⋅ ●L{dq2} a.
Proof.
  rewrite /lat_auth auth_auth_dfrac_op.
  rewrite (comm _ (●{dq2} _)) -!assoc (assoc _ (◯ _)).
  by rewrite -core_id_dup (comm _ (◯ _)).
Qed.
Lemma lat_auth_frac_op q1 q2 a :
  ●L{#(q1 + q2)} a ≡ ●L{#q1} a ⋅ ●L{#q2} a.
Proof. by rewrite -lat_auth_dfrac_op dfrac_op_own. Qed.

Lemma lat_lb_op_l a b : a ⊑ b → ◯L a ⋅ ◯L b ≡ ◯L b.
Proof. intros ?. by rewrite /lat_lb -auth_frag_op lat_op_join' lat_le_join_r. Qed.
Lemma lat_lb_op_r a b : a ⊑ b → ◯L b ⋅ ◯L a ≡ ◯L b.
Proof. intros ?. by rewrite /lat_lb -auth_frag_op lat_op_join' lat_le_join_l. Qed.
Lemma lat_auth_lb_op dq a : ●L{dq} a ≡ ●L{dq} a ⋅ ◯L a.
Proof. by rewrite /lat_auth /lat_lb -!assoc -auth_frag_op -core_id_dup. Qed.

Global Instance lat_lb_is_op a : IsOp' (◯L a) (◯L a) (◯L a).
Proof. by rewrite /IsOp' /IsOp -core_id_dup. Qed.

(** * Validity *)

Lemma lat_auth_dfrac_valid dq a : ✓ (●L{dq} a) ↔ ✓ dq.
Proof. rewrite /lat_auth auth_both_dfrac_valid. naive_solver. Qed.
Lemma lat_auth_valid a : ✓ (●L a).
Proof. by apply lat_auth_dfrac_valid. Qed.

Lemma lat_auth_both_valid q a b :
  ✓ (●L{q} a ⋅ ◯L b) ↔ ✓ q ∧ b ⊑ a.
Proof.
  rewrite -assoc -auth_frag_op auth_both_dfrac_valid_discrete latT_included !of_to_latT.
  f_equiv. split.
  - intros []. solve_lat.
  - intros. split; [solve_lat|done].
Qed.

Lemma lat_auth_auth_valid q1 q2 a b :
  ✓ (●L{q1} a ⋅ ●L{q2} b) ↔ ✓ (q1 ⋅ q2) ∧ a ≡ b.
Proof.
  rewrite /lat_auth (comm _ (●{q2} _)) -!assoc (assoc _ (◯ _)).
  rewrite -auth_frag_op (comm _ (◯ _)) assoc. split.
  - move=> /cmra_valid_op_l /auth_auth_dfrac_op_valid. naive_solver.
  - intros [? ->].
    rewrite -core_id_dup -auth_auth_dfrac_op auth_both_dfrac_valid_discrete.
    naive_solver.
Qed.

(** * Inclusion *)
Lemma lat_auth_included dq l : ◯L l ≼ ●L{dq} l.
Proof. apply cmra_included_r. Qed.

Lemma lat_lb_mono a b :
  a ⊑ b → ◯L a ≼ ◯L b.
Proof. intros. by apply auth_frag_mono, latT_included. Qed.

(** * Update *)
Lemma lat_auth_update a b :
  a ⊑ b → ●L a ~~> ●L b.
Proof. intros. by apply auth_update, latT_local_unit_update. Qed.

Lemma lat_auth_update_join a b :
  ●L a ~~> ●L (a ⊔ b).
Proof. apply lat_auth_update. solve_lat. Qed.

End props.

Section master.
Context {LAT : latticeT} `{!@LatBottom LAT bot} `{!inG Σ (lat_authR LAT)}.

Lemma own_master_max γ q a b :
  own γ (●L{q} a) -∗ own γ (◯L b) -∗ ⌜b ⊑ a⌝.
Proof.
  iIntros "H1 H2". by iCombine "H1 H2" gives %[]%lat_auth_both_valid.
Qed.

Lemma own_master_eq γ p q a b :
  own γ (●L{p} a) -∗ own γ (●L{q} b) -∗ ⌜a ≡ b⌝.
Proof.
  iIntros "H1 H2". by iCombine "H1 H2" gives %[]%lat_auth_auth_valid.
Qed.

Lemma own_master_update γ a b (Ext : a ⊑ b) :
  own γ (●L a) ==∗ own γ (●L b).
Proof. by apply own_update, lat_auth_update. Qed.

Lemma own_master_update_join γ a b :
  own γ (●L a) ==∗ own γ (●L (a ⊔ b)).
Proof. apply own_update, lat_auth_update_join. Qed.

Lemma own_snapshot_downclosed γ a b (Le : a ⊑ b) :
  own γ (◯L b) ⊢ own γ (◯L a).
Proof. by apply own_mono, lat_lb_mono. Qed.
End master.
