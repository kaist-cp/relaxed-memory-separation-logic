From stdpp Require Import gmap.
From iris.algebra Require Import coPset.

Require Import iris.prelude.options.

(** Tokens with infinite number to be used in various examples **)

Definition Pos_upto_set (up: nat) : gset positive :=
  list_to_set (Pos.of_nat <$> (seq 1 up)).

Definition coPset_from_ex (i: nat): coPset
  := ⊤ ∖  gset_to_coPset (Pos_upto_set i).

Lemma coPset_from_ex_gt i p:
  p ∈ coPset_from_ex i ↔ (i < Pos.to_nat p)%nat.
Proof.
  rewrite elem_of_difference elem_of_gset_to_coPset.
  rewrite elem_of_list_to_set elem_of_list_fmap. split.
  - move => [_ /= NIn].
    apply: not_ge => ?. apply: NIn.
    exists (Pos.to_nat p). rewrite Pos2Nat.id elem_of_list_In in_seq. lia.
  - move => Lt. split; [done|].
    move => [n [Eqn /elem_of_list_In /in_seq [Ge1 Lt2]]].
    subst. rewrite Nat2Pos.id_max in Lt. lia.
Qed.

Lemma coPset_from_insert i:
  coPset_from_ex i = {[Pos.of_succ_nat i]} ∪ coPset_from_ex (S i).
Proof.
  apply leibniz_equiv.
  move => p. rewrite elem_of_union elem_of_singleton !coPset_from_ex_gt. lia.
Qed.

Lemma coPset_from_disjoint i:
  {[Pos.of_succ_nat i]} ## coPset_from_ex (S i).
Proof.
  rewrite disjoint_singleton_l coPset_from_ex_gt SuccNat2Pos.id_succ. lia.
Qed.

Lemma gset_to_coPset_union X Y :
  gset_to_coPset (X ∪ Y) = gset_to_coPset X ∪ gset_to_coPset Y.
Proof.
  apply leibniz_equiv.
  move => ?. by rewrite elem_of_union !elem_of_gset_to_coPset elem_of_union.
Qed.

Lemma gset_to_coPset_difference X Y:
  gset_to_coPset (X ∖ Y) = gset_to_coPset X ∖ gset_to_coPset Y.
Proof.
  apply leibniz_equiv => ?.
  by rewrite elem_of_difference !elem_of_gset_to_coPset elem_of_difference.
Qed.

Lemma gset_to_coPset_difference_union (X Y Z: gset positive)
  (Disj: Y ## Z) (Sub: Y ⊆ X):
  gset_to_coPset (X ∖ Z) = gset_to_coPset (X ∖ (Y ∪ Z)) ∪ gset_to_coPset Y.
Proof.
  apply leibniz_equiv => x.
  rewrite elem_of_union !elem_of_gset_to_coPset
          !elem_of_difference elem_of_union.
  split.
  - move => [InX NIn]. case (decide (x ∈ Y)) => [?|NInY].
    + by right.
    + left. split; first auto. by move => [|].
  - set_solver.
Qed.

Lemma gset_to_coPset_difference_disjoint (X Y Z: gset positive):
  gset_to_coPset (X ∖ (Y ∪ Z)) ## gset_to_coPset Y.
Proof.
  rewrite elem_of_disjoint => ?.
  rewrite !elem_of_gset_to_coPset elem_of_difference elem_of_union.
  set_solver.
Qed.

Lemma gset_to_coPset_top_difference (X Y: gset positive) (Disj: X ## Y):
  ⊤ ∖  gset_to_coPset X = (⊤ ∖  gset_to_coPset (Y ∪ X)) ∪ gset_to_coPset Y.
Proof.
  apply leibniz_equiv. move => x.
  rewrite elem_of_union !elem_of_difference
          !elem_of_gset_to_coPset elem_of_union.
  split.
  - move => [_ NIn]. case (decide (x ∈ Y)) => [|?]; [by right|left]. set_solver.
  - set_solver.
Qed.

Lemma gset_to_coPset_top_disjoint (X Y: gset positive):
  (⊤ ∖  gset_to_coPset (Y ∪ X)) ## gset_to_coPset Y.
Proof.
  rewrite elem_of_disjoint.
  move => x. rewrite elem_of_difference gset_to_coPset_union. set_solver.
Qed.

Lemma gset_to_coPset_empty :
  gset_to_coPset ∅ = ∅.
Proof. by apply leibniz_equiv. Qed.

Lemma coPset_difference_top_empty:
  ⊤ ∖ ∅ = (⊤ : coPset).
Proof. by apply leibniz_equiv. Qed.
