From iris.algebra Require Import agree gmap local_updates.

Require Import iris.prelude.options.

(** [to_agree] of a [gmap] *)
(* TODO: MOVE *)
Section to_agree.
Context `{Countable K} {A: Type}.

Implicit Type (m : gmap K A) (k : K) (a : A).

Definition agreeMR := (gmapUR K (agreeR (leibnizO A))).

Definition to_agreeM m : agreeMR := (@to_agree (leibnizO A)) <$> m.

(** * Validity *)
Lemma to_agreeM_valid m : ✓ (to_agreeM m).
Proof. intros i. rewrite lookup_fmap. by case lookup => [?|] //. Qed.

Lemma to_agreeM_lookup_agree m1 m2 k a1 a2 :
  ✓ (to_agreeM m1 ⋅ to_agreeM m2) →
  m1 !! k = Some a1 → m2 !! k = Some a2 → a1 = a2.
Proof.
  move => /(_ k). rewrite lookup_op 2!lookup_fmap => EqL Eq1 Eq2.
  move : EqL. rewrite Eq1 Eq2 /= -Some_op Some_valid.
  apply : to_agree_op_inv_L.
Qed.

Lemma to_agreeM_singleton_agree k a1 a2 :
  ✓ (to_agreeM {[k := a1]} ⋅ to_agreeM {[k := a2]}) → a1 = a2.
Proof.
  intros ?%(to_agreeM_lookup_agree _ _ k a1 a2); [done|by apply lookup_insert..].
Qed.

Lemma to_agreeM_dom_eq m1 m2 :
  ✓ (to_agreeM m1 ⋅ to_agreeM m2) →
  dom m1 ≡ dom m2 → m1 = m2.
Proof.
  intros AG EqD. apply map_eq => i.
  move : EqD => /(_ i). rewrite 2!elem_of_dom => EqD.
  destruct (m1 !! i) as [a1|] eqn:Eq1, (m2 !! i) as [a2|] eqn:Eq2; [..|done].
  - f_equal. apply (to_agreeM_lookup_agree _ _ _ _ _ AG Eq1 Eq2).
  - exfalso. destruct EqD as [[] _]; [by eexists|done].
  - exfalso. destruct EqD as [_ []]; [by eexists|done].
Qed.

Lemma to_agreeM_valid_union m1 m2 :
  ✓ (to_agreeM m1 ⋅ to_agreeM m2) → m1 ∪ m2 = m2 ∪ m1.
Proof.
  intros VAL. apply map_eq => i. rewrite 2!lookup_union.
  destruct (m1 !! i) as [a1|] eqn:Eq1, (m2 !! i) as [a2|] eqn:Eq2; [|done..];
    rewrite !union_Some_l.
  f_equal. apply (to_agreeM_lookup_agree _ _ i _ _ VAL Eq1 Eq2).
Qed.

(** * Equiv *)
Lemma to_agreeM_agree m m' : to_agreeM m ≡ to_agreeM m' → m = m'.
Proof.
  intros Eqv. apply map_eq => i. move : (Eqv i). rewrite 2!lookup_fmap.
  destruct (m !! i) eqn:Eq1; destruct (m' !! i) eqn:Eq2; rewrite /=Eq1 Eq2;
    [|inversion 1..|done].
  inversion 1 as [?? Eq3|]. simplify_eq. f_equal. by move : Eq3 => /to_agree_inj.
Qed.

(** * Inclusion *)
Lemma to_agreeM_included m1 m2 :
  to_agreeM m2 ≼ to_agreeM m1 ↔ m2 ⊆ m1.
Proof.
  split.
  - move => INCL i. move : INCL. rewrite lookup_included => /(_ i).
    rewrite /to_agreeM 2!lookup_fmap.
    destruct (m2 !! i) as [a2|] eqn:Eq1, (m1 !! i) as [a1|] eqn:Eq2;
      rewrite Eq1 Eq2; try done.
    + move => /Some_included_total /(to_agree_included (A:=leibnizO A))
              /leibniz_equiv_iff -> //.
    + move => /option_included_total. naive_solver.
  - move => INCL. apply lookup_included => i. rewrite 2!lookup_fmap.
    specialize (INCL i).
    destruct (m2 !! i) as [a2|] eqn:Eq1, (m1 !! i) as [a1|] eqn:Eq2;
      rewrite Eq1 Eq2; try done.
    + simpl in INCL. by subst.
    + simpl. apply option_included. by left.
Qed.

Lemma to_agreeM_singleton_included m k a :
  {[k := to_agree a]} ≼ to_agreeM m ↔ {[k := a]} ⊆ m.
Proof. rewrite -(map_fmap_singleton to_agree). apply to_agreeM_included. Qed.

(** * Operations *)
(* the side condition guarantees that m1 ∪ m2 = m2 ∪ m1. *)
Lemma to_agreeM_op_valid m1 m2 :
  ✓ (to_agreeM m1 ⋅ to_agreeM m2) →
  to_agreeM m1 ⋅ to_agreeM m2 ≡ to_agreeM (m1 ∪ m2).
Proof.
  intros VALID i. rewrite lookup_op !lookup_fmap.
  destruct (m1 !! i) eqn:Eq1; rewrite Eq1 /=;
    destruct (m2 !! i) eqn:Eq2; rewrite Eq2 /=.
  - rewrite -Some_op (lookup_union_Some_l _ _ _ _ Eq1).
    move : (VALID i).
    rewrite lookup_op !lookup_fmap Eq1 Eq2 /= -Some_op.
    rewrite Some_valid to_agree_op_valid_L. intros <-. by rewrite agree_idemp.
  - by rewrite right_id (lookup_union_Some_l _ _ _ _ Eq1).
  - by rewrite left_id (lookup_union_r _ _ _ Eq1) Eq2.
  - by rewrite left_id (lookup_union_r _ _ _ Eq1) Eq2.
Qed.

Lemma agreeM_absorb (m1 m2 : agreeMR) :
  m1 ⋅ m2 ≡ m1 ↔ m2 ≼ m1.
Proof.
  split; first by (move => <-; apply cmra_included_r).
  move => /lookup_included INCL i.
  rewrite lookup_op. move : (INCL i).
  destruct (m1 !! i) eqn:Hi; rewrite Hi; simpl;
      destruct (m2 !! i) eqn:Hi'; rewrite Hi'; simpl;
      [|done|by rewrite option_included; naive_solver|done].
  rewrite Some_included_total -Some_op.
  move => /agree_included. rewrite cmra_comm. by move => <-.
Qed.

Lemma agreeM_idemp (m : agreeMR) : m ⋅ m ≡ m.
Proof. by apply agreeM_absorb. Qed.

Lemma to_agreeM_insert m k a :
  m !! k = None → to_agreeM (<[k := a]> m) ≡ to_agreeM m ⋅ to_agreeM {[k := a]}.
Proof.
  intros NONE k0. rewrite /to_agreeM lookup_op !lookup_fmap.
  case (decide (k0 = k)) => [->|?].
  - by rewrite !lookup_insert NONE /= left_id.
  - by rewrite !lookup_insert_ne // lookup_empty /= right_id.
Qed.

(** * Local updates *)
Lemma agreeM_local_update (m1 m2 m0 : agreeMR) :
  m1 ≼ m2 → ✓ m2 → (m1, m0) ~l~> (m2, m2).
Proof.
  intros INCL VALID. apply local_update_unital_discrete => z Valid Eq.
  split; [done|]. symmetry. apply agreeM_absorb. etrans; last exact INCL.
  rewrite Eq. apply cmra_included_r.
Qed.

Lemma to_agreeM_local_update m m' (m0 : agreeMR) :
  m ⊆ m' → (to_agreeM m, m0) ~l~> (to_agreeM m', to_agreeM m').
Proof.
  intros. apply agreeM_local_update.
  - by apply to_agreeM_included.
  - by apply to_agreeM_valid.
Qed.

Lemma agreeM_local_update_retain (m m0 m' : agreeMR) :
  ✓ (m ⋅ m') → (m, m0) ~l~> (m ⋅ m', m0 ⋅ m').
Proof.
  intros. apply local_update_unital_discrete => z Valid Eq.
  split; [done|]. by rewrite Eq -cmra_assoc (cmra_comm z m') cmra_assoc.
Qed.

Lemma to_agreeM_local_update_insert m m' k a :
  m !! k = None →
  (to_agreeM m, to_agreeM m')
    ~l~> (to_agreeM (<[k := a]>m), to_agreeM (<[k := a]>m')).
Proof.
  intros NONE.
  have ?: ✓ (to_agreeM m ⋅ to_agreeM {[k := a]}).
  { rewrite -to_agreeM_insert //. apply to_agreeM_valid. }
  rewrite to_agreeM_insert //. apply local_update_valid.
  intros _ _ [<-%to_agreeM_agree|INCL%to_agreeM_included].
  - rewrite to_agreeM_insert //. by apply agreeM_local_update_retain.
  - rewrite to_agreeM_insert.
    + by apply agreeM_local_update_retain.
    + by eapply lookup_weaken_None.
Qed.

Lemma to_agreeM_local_update_insert_singleton m k a :
  m !! k = None →
  (to_agreeM m, ε) ~l~> (to_agreeM (<[k := a]>m), to_agreeM ({[k := a]})).
Proof.
  intros. rewrite -insert_empty.
  rewrite (_: ε = to_agreeM ∅); last first.
  { by rewrite /to_agreeM fmap_empty. }
  by apply to_agreeM_local_update_insert.
Qed.

Lemma agreeM_local_update_fork (m m' m0 : agreeMR) :
  m0 ≼ m' → m' ≼ m → ✓ m' →
  (m, m0) ~l~> (m, m').
Proof.
  intros INCL0 INCL VALID.
  destruct INCL0 as [? Eq0]. destruct INCL as [? Eq'].
  apply local_update_unital_discrete => z Valid Eq. split; [done|].
  rewrite Eq Eq0. rewrite -cmra_assoc (cmra_comm x z) cmra_assoc -Eq.
  symmetry. apply agreeM_absorb. rewrite Eq' Eq0.
  etrans; last apply cmra_included_l. apply cmra_included_r.
Qed.

Lemma to_agreeM_local_update_fork m m' m0 :
  m0 ⊆ m' → m' ⊆ m →
  (to_agreeM m, to_agreeM m0) ~l~> (to_agreeM m, to_agreeM m').
Proof.
  intros. apply agreeM_local_update_fork;
            [by apply to_agreeM_included..|apply to_agreeM_valid].
Qed.

Lemma to_agreeM_local_update_fork_singleton m k a :
  m !! k = Some a →
  (to_agreeM m, ε) ~l~> (to_agreeM m, to_agreeM ({[k := a]})).
Proof.
  intros.
  rewrite (_: ε = to_agreeM ∅); last first.
  { by rewrite /to_agreeM fmap_empty. }
  apply to_agreeM_local_update_fork; [apply map_empty_subseteq|].
  by apply map_singleton_subseteq_l.
Qed.

End to_agree.

Arguments agreeMR _ {_ _} _.
(* end MOVE *)
