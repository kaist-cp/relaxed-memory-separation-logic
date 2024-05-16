From iris.bi Require Import bi.
Import bi.

From iris.proofmode Require Import tactics.

Require Import iris.prelude.options.

Section map.
  Context {PROP: bi} `{Countable K} {A : Type}.
  Implicit Types l : list A.
  Implicit Types Φ Ψ : nat → A → PROP.

  Lemma big_sepM_map_seq_big_sepL Φ Ψ L start :
    (∀ k x, L !! k = Some x → Φ (k + start) x ⊢ Ψ k x) →
    ([∗ map] k ↦ x ∈ (map_seq start L), Φ k x) ⊢ [∗ list] k ↦ x ∈ L, Ψ k x.
  Proof.
    revert Φ Ψ start.
    induction L as [|y L IH]; intros Φ Ψ start HM.
    - by rewrite /= big_sepM_empty.
    - rewrite big_sepL_cons map_seq_cons big_sepM_insert; last first.
      { apply lookup_map_seq_None. by left; lia. }
      iIntros "[HΦ HM]". iSplitL "HΦ".
      + iApply HM; [done|]. by rewrite Nat.add_0_l.
      + iApply (IH with "HM"). intros k x Eqk. simpl. apply (HM (S k)) in Eqk.
        by rewrite -Nat.add_succ_comm.
  Qed.

  Lemma big_sepM_map_seq_0_big_sepL Φ Ψ L :
    (∀ k x, L !! k = Some x → Φ k x ⊢ Ψ k x) →
    ([∗ map] k ↦ x ∈ (map_seq 0 L), Φ k x) ⊢ [∗ list] k ↦ x ∈ L, Ψ k x.
  Proof.
    intros HM. apply big_sepM_map_seq_big_sepL. by setoid_rewrite Nat.add_0_r.
  Qed.
End map.

Section big_op_map.
  Context {PROP : bi} `{Countable K} {A : Type}.
  Implicit Types m : gmap K A.
  Implicit Types Φ Ψ : K → A → PROP.

  Lemma big_sepM_lookup_acc_impl_2 {Φ m} i x :
    m !! i = Some x →
    ([∗ map] k↦y ∈ m, Φ k y) -∗
    (* We obtain [Φ] for [x] *)
    Φ i x ∗
    (* We reobtain the bigop for a predicate [Ψ] selected by the user *)
    ∀ Ψ,
      □ (∀ k y, ⌜ m !! k = Some y ⌝ → ⌜ k ≠ i ⌝ → Φ k y -∗ Ψ k y) -∗
      ∀ x', Ψ i x' -∗
      [∗ map] k↦y ∈ <[i := x']> m, Ψ k y.
  Proof.
    intros. rewrite big_sepM_delete //. apply sep_mono_r, forall_intro=> Ψ.
    apply wand_intro_r, forall_intro=> x'.
    apply bi.wand_intro_l.
    rewrite (big_sepM_delete Ψ (<[i:=x']>m) i x'); last by rewrite lookup_insert.
    apply sep_mono_r. rewrite delete_insert_delete.
    eapply wand_apply; [apply big_sepM_impl|apply sep_mono_r].
    f_equiv; f_equiv=> k; f_equiv=> y.
    rewrite impl_curry -pure_and lookup_delete_Some.
    do 2 f_equiv. intros ?; naive_solver.
  Qed.
End big_op_map.
