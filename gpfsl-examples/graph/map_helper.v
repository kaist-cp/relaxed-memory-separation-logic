Require Import stdpp.gmap.
Require Import iris.prelude.prelude.

Require Import iris.prelude.options.

(* TODO: move to stdpp *)
Lemma map_lookup_subseteq_eq_inv `{FinMap K M} {A : Type}
  (m m': M A) (k : K) (v : A) :
  m ⊆ m' → m' !! k = Some v → is_Some (m !! k) → m !! k = Some v.
Proof.
  move => SUB Eq' [? Eq].
  assert (Eqv:=lookup_weaken_inv _ _ _ _ _ Eq SUB Eq'). by subst.
Qed.

Lemma delete_union_disjoint_l `{FinMap K M} {A} (m1 m2: M A) i
  (DISJ : m1 ##ₘ m2)
  (Hev : is_Some (m1 !! i)) :
  delete i m1 ∪ m2 = delete i (m1 ∪ m2).
Proof.
  rewrite delete_union. destruct Hev as [x Hev].
  eapply map_disjoint_Some_l in DISJ; last apply Hev.
  apply delete_notin in DISJ. by rewrite DISJ.
Qed.

Lemma delete_union_disjoint_r `{FinMap K M} {A} (m1 m2: M A) i
  (DISJ : m1 ##ₘ m2)
  (Hev : is_Some (m2 !! i)) :
  m1 ∪ delete i m2 = delete i (m1 ∪ m2).
Proof.
  rewrite delete_union. destruct Hev as [x Hev].
  eapply map_disjoint_Some_r in DISJ; last apply Hev.
  apply delete_notin in DISJ. by rewrite DISJ.
Qed.

Lemma map_positive_r `{FinMap K M} {A} (m1 m2 : M A) : m1 ∪ m2 = ∅ → m2 = ∅.
Proof.
  intros Hm. assert (EqE := map_positive_l _ _ Hm).
  move : Hm. subst m1. by rewrite left_id_L.
Qed.

Lemma map_self_id `{FinMap K M} {A} (m : M A) : m ∪ m = m.
Proof. by apply map_subseteq_union. Qed.

(* Domain of gmap *)
Definition dom_list `{Countable K} {A: Type} (m: gmap K A) : list K :=
  fst <$> map_to_list m.

Lemma dom_list_correct `{Countable K} {A: Type} (m: gmap K A) :
  ∀ k, k ∈ dom_list m ↔ (∃ v, m !! k = Some v).
Proof.
  intro. rewrite /dom_list elem_of_list_fmap.
  setoid_rewrite <-elem_of_map_to_list. split.
  - move=>[[k' v]] /= [<-] ?. by exists v.
  - move=>[v] ?. by exists (k,v).
Qed.

Lemma NoDup_dom_list `{Countable K} {A: Type} (m: gmap K A) :
  NoDup (dom_list m).
Proof. by apply NoDup_fst_map_to_list. Qed.

(* Codom of gmap *)
Definition codom_list `{Countable K} {A: Type} (m: gmap K A) : list A :=
  snd <$> map_to_list m.

Lemma codom_list_correct `{Countable K} {A: Type} (m: gmap K A) :
  ∀ x : A, x ∈ codom_list m ↔ ∃ k, m !! k = Some x.
Proof.
  intros x. rewrite elem_of_list_fmap. split.
  - intros ([k a] & Eq' & In%elem_of_map_to_list).
    simpl in *. simplify_eq. exists k. by rewrite In.
  - intros [k Eqk]. exists (k,x). split; [done|].
    by rewrite elem_of_map_to_list.
Qed.

Section codom_f.
Context `{Countable K, Countable A} {E: Type}.

Definition codomf (f: E → A) (m: gmap K E) : gset A :=
  list_to_set (f <$> (codom_list m)).

Lemma codomf_correct (f: E → A) (m: gmap K E) :
  ∀ x : A, x ∈ codomf f m ↔ ∃ k, f <$> m !! k = Some x.
Proof.
  intros x. rewrite /codomf elem_of_list_to_set elem_of_list_fmap.
  setoid_rewrite codom_list_correct. split.
  - intros (e & Eqx & k & In). exists k. simpl in Eqx. subst. by rewrite In.
  - intros [k Eqk]. destruct (m !! k) as [e|] eqn: Eqk'; [|done].
    simpl in Eqk. simplify_eq. exists e. naive_solver.
Qed.

End codom_f.

Definition codom `{Countable K, Countable A} (m: gmap K A) := codomf id m.

Lemma codom_insert `{Countable K, Countable A} (m: gmap K A) (k : K) (a : A)
  (FRESH: m !! k = None) :
  codom (<[k := a]> m) = {[a]} ∪ codom m.
Proof.
  apply leibniz_equiv_iff => i.
  rewrite elem_of_union elem_of_singleton !codomf_correct.
  split.
  - intros [k' Eq']. case (decide (k' = k)) => ?.
    + subst k'. rewrite lookup_insert /= in Eq'. simplify_eq. by left.
    + rewrite lookup_insert_ne // in Eq'. right. by eexists.
  - intros [?|[k' Eq']].
    + subst i. exists k. by rewrite lookup_insert.
    + exists k'. rewrite lookup_insert_ne //. intros ?. subst k'.
      by rewrite FRESH in Eq'.
Qed.

Lemma codom_correct `{Countable K, Countable A} (m: gmap K A) :
  ∀ x : A, x ∈ codom m ↔ ∃ k, m !! k = Some x.
Proof.
  intros x. rewrite codomf_correct. split; intros [k Eq]; exists k.
  - destruct (m !! k); simpl in Eq; by simplify_eq.
  - by rewrite Eq.
Qed.

Definition gmap_inj `{Countable K} {A: Type} (m: gmap K A) : Prop :=
  ∀ k1 k2 a, m !! k1 = Some a → m !! k2 = Some a → k1 = k2.

Section coimg.
Context `{Countable K, Countable A}.
Definition coimg (m : gmap K A) (img: gset A) : gset K :=
  list_to_set (map fst (filter (λ p, p.2 ∈ img) (map_to_list m))).

Lemma coimg_correct (m : gmap K A) (img: gset A) :
  ∀ k : K, k ∈ coimg m img ↔ ∃ a, a ∈ img ∧ m !! k = Some a.
Proof.
  intros k. rewrite /coimg elem_of_list_to_set elem_of_list_fmap.
  setoid_rewrite elem_of_list_filter. split.
  - intros ([k' a'] & ? & Ina & InM%elem_of_map_to_list).
    simplify_eq. simpl in *. naive_solver.
  - intros (a & Ina & Eqk). exists (k,a). repeat split; auto.
    by apply elem_of_map_to_list.
Qed.

Lemma coimg_codom (m : gmap K A) :
  coimg m (codom m) ≡ dom m.
Proof.
  intros k. rewrite coimg_correct elem_of_dom. setoid_rewrite codom_correct.
  split.
  - naive_solver.
  - intros [a Eqk]. exists a. naive_solver.
Qed.
End coimg.
