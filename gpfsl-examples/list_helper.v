From stdpp Require Import numbers sorting.
From orc11 Require Import base.

From stdpp Require Import options.

(* TODO: upstream to stdpp *)
(* TODO: cleanup unused lemmas *)
Section prefixes.
Context {A: Type}.
Implicit Types (B: Type) (l: list A) (x : A).

Lemma elem_of_list_prefix l l' x :
  l `prefix_of` l' → x ∈ l → x ∈ l'.
Proof. intros [ly Eql] Inl. subst l'. apply elem_of_app. by left. Qed.

Lemma prefix_length_eq l l' :
  l `prefix_of` l' → length l' ≤ length l → l' = l.
Proof.
  intros [ly ->] LeL. rewrite app_length in LeL. destruct ly.
  - by rewrite app_nil_r.
  - exfalso. simpl in LeL. lia.
Qed.

Lemma prefix_app_inv l l1 l2 :
  l ++ l1 `prefix_of` l ++ l2 → l1 `prefix_of` l2.
Proof. intros [ly Eq]. exists ly. by simplify_list_eq. Qed.

Lemma prefix_lookup_inv l1 l2 i x :
  l2 !! i = Some x → is_Some (l1 !! i) → l1 `prefix_of` l2 → l1 !! i = Some x.
Proof.
  intros Eq2 [x' Eq1] HP.
  rewrite (prefix_lookup_Some _ _ _ _ Eq1 HP) in Eq2.
  by simplify_eq.
Qed.

Global Instance list_sqsubseteq : SqSubsetEq (list A) := prefix.

Global Instance list_sqsubseteq_elem_of_proper a :
  Proper ((@sqsubseteq (list A) _) ==> (impl)) (elem_of a).
Proof. intros ????. by eapply elem_of_list_prefix. Qed.

Lemma list_sqsubseteq_app_inv l l1 l2 :
  l ++ l1 ⊑ l ++ l2 → l1 ⊑ l2.
Proof. apply prefix_app_inv. Qed.
End prefixes.

Global Instance fmap_prefix {A B} (f : A → B) :
  Proper ((⊑) ==> (⊑)) (@fmap list _ _ _ f).
Proof. intros L1 L2 [L3 Eq3]. rewrite Eq3. rewrite fmap_app. by eexists. Qed.

Lemma lookup_fmap_Some' `{FinMap K M} {A B} (f : A → B) (m : M A) i y :
  f <$> (m !! i) = Some y ↔ ∃ x, f x = y ∧ m !! i = Some x.
Proof. rewrite -lookup_fmap. apply lookup_fmap_Some. Qed.

Lemma list_lookup_fmap_inv' {A B : Type}
  (f : A → B) (l : list A) (i : nat) (x : B) :
  f <$> l !! i = Some x ↔ ∃ y : A, x = f y ∧ l !! i = Some y.
Proof.
  split.
  - rewrite -list_lookup_fmap. apply list_lookup_fmap_inv.
  - by intros (? & -> & ->).
Qed.


Section props.
Context {A : Type}.
Implicit Types (l : list A) (x y : A).

Lemma filter_nil_iff (P : A → Prop) `{∀ x, Decision (P x)} (l : list A) :
  Forall (not ∘ P) l ↔ filter P l = [].
Proof.
  induction l as [|x l IH]; [done|].
  rewrite Forall_cons IH filter_cons. clear.
  case decide => ?; naive_solver.
Qed.

Lemma lookup_length_not_Some l x : ¬ l !! length l = Some x.
Proof. rewrite lookup_ge_None_2; [done|lia]. Qed.

Lemma lookup_length_not_is_Some l : ¬ is_Some (l !! length l).
Proof. by intros [? ?%lookup_length_not_Some]. Qed.

Lemma lookup_last_Some l x :
  l !! (length l - 1)%nat = Some x → ∃ l', l = l' ++ [x].
Proof.
  intros Eq.
  apply elem_of_list_split_length in Eq as (l1 & l2 & Eql & EqL).
  subst l.
  move : EqL. rewrite app_length /= -Nat.add_sub_assoc; last lia.
  rewrite /= Nat.sub_0_r.
  destruct l2; simpl.
  - intros _. by exists l1.
  - lia.
Qed.

Lemma lookup_last_Some_2 l x y :
  (l ++ [y]) !! length l = Some x → x = y.
Proof.
  rewrite (_: length l = length (l ++ [y]) - 1); last first.
  { rewrite app_length /=. lia. }
  intros [??]%lookup_last_Some. by simplify_list_eq.
Qed.

Lemma elem_of_last_Some l x :
  last l = Some x → ∃ l', l = l' ++ [x].
Proof.
  rewrite -head_reverse. destruct (reverse l) as [|y l'] eqn:Eq; [done|].
  simpl. inversion 1. subst y. exists (reverse l').
  by rewrite -reverse_cons -Eq reverse_involutive.
Qed.

Lemma last_cons_cons l x y : last (x :: y :: l) = last (y :: l).
Proof. done. Qed.

Lemma lookup_app_1 l y i x :
  (l ++ [y]) !! i = Some x → (l !! i = Some x) ∨ (i = length l ∧ y = x).
Proof.
  intros [?|[? []%list_lookup_singleton_Some]]%lookup_app_Some; [by left|right].
  split; [lia|done].
Qed.

Lemma lookup_app_1_eq l x : (l ++ [x]) !! length l = Some x.
Proof. by apply list_lookup_middle. Qed.

Lemma lookup_app_1_ne l e i :
  i ≠ length l → (l ++ [e]) !! i = l !! i.
Proof.
  case (decide (length l < i)) => [?|NLt] ?.
  - rewrite (lookup_ge_None_2 l); [|lia]. apply lookup_ge_None_2.
    rewrite app_length /=. lia.
  - intros. apply lookup_app_l. lia.
Qed.

Lemma lookup_app_1' l y i x :
  (l ++ [y]) !! i = Some x ↔ (l !! i = Some x) ∨ (i = length l ∧ y = x).
Proof.
  split; [apply lookup_app_1|].
  intros [?|[-> ->]].
  - by apply lookup_app_l_Some.
  - by apply lookup_app_1_eq.
Qed.

Lemma lookup_app_2 l y1 y2 i x :
  (l ++ [y1; y2]) !! i = Some x →
    (l !! i = Some x) ∨ (i = length l ∧ y1 = x) ∨ (i = S (length l) ∧ y2 = x).
Proof.
  rewrite (app_assoc _ [_] [_]).
  intros [[]%lookup_app_1|[-> ?]]%lookup_app_1.
  - by left.
  - by right; left.
  - right; right. rewrite app_length /=. split; [lia|done].
Qed.

Lemma lookup_app_2' l y1 y2 i x :
  (l ++ [y1; y2]) !! i = Some x ↔
    (l !! i = Some x) ∨ (i = length l ∧ y1 = x) ∨ (i = S (length l) ∧ y2 = x).
Proof.
  split; [apply lookup_app_2|].
  intros [?|[[-> ->]|[-> ->]]].
  - by apply lookup_app_l_Some.
  - by apply list_lookup_middle.
  - rewrite (app_assoc _ [_] [_]) (_ : S (length l) = length (l ++ [y1])).
    + apply lookup_app_1_eq.
    + rewrite app_length /=. lia.
Qed.

Lemma list_equal_tail l1 x l2 y :
  l1 ++ [x] = l2 ++ [y] → (l1 = l2) ∧ (x = y).
Proof. intros Heq. by simplify_list_eq. Qed.

Lemma nil_snoc l x : [] ≠ l ++ [x].
Proof. by case l. Qed.

Lemma lookup_last_cons l x :
  (x :: l) !! (length l) = last (x :: l).
Proof. rewrite last_lookup lookup_cons //. Qed.

Lemma elem_of_Permutation_inv l l' x : l ≡ₚ x :: l' → x ∈ l.
Proof. intros ->. set_solver. Qed.

Lemma repeat_lookup_Some x x' i n :
  repeat x n !! i = Some x' → x' = x.
Proof.
  intros Eqi%elem_of_list_lookup_2%elem_of_list_In.
  apply (repeat_spec _ _ _ Eqi).
Qed.

Lemma repeat_lookup_Some_iff x x' i n :
  repeat x n !! i = Some x' ↔ x = x' ∧ (i < n)%nat.
Proof.
  rewrite -{2}(repeat_length x n) -lookup_lt_is_Some. split.
  - intros Eq. split; [|by eexists]. by apply repeat_lookup_Some in Eq.
  - intros [-> [? Eq]]. by rewrite -{2}(repeat_lookup_Some _ _ _ _ Eq).
Qed.

Lemma repeat_lookup_None x i n : repeat x n !! i = None ↔ (n ≤ i)%nat.
Proof. by rewrite lookup_ge_None repeat_length. Qed.

Lemma pre_app_nil l l1 : l = l1 ++ l → l1 = [].
Proof.
  revert l1. induction l  as [|x l IH]=> l1 Eq; simplify_list_eq; [done|].
  destruct l1 as [|y l1]; [done|]. exfalso. simplify_list_eq.
  assert (Eq: l1 ++ [y] = []). { apply IH. by simplify_list_eq. }
  by apply app_nil in Eq as [].
Qed.

Lemma post_app_nil l l1 : l = l ++ l1 → l1 = [].
Proof.
  revert l1. induction l  as [|x l IH]=> l1 Eq; simplify_list_eq; [done|].
  by apply IH.
Qed.

Lemma pre_post_app_nil l l1 l2 : l = l1 ++ l ++ l2 → l1 = [] ∧ l2 = [].
Proof.
  revert l1 l2. induction l  as [|x l IH]=> l1 l2 Eq; simplify_list_eq.
  { by apply app_nil. }
  destruct l1 as [|y l1], l2 as [|z l2]; simplify_list_eq; auto.
  - assert (EqN: l1 ++ [y] = []).
    { apply (pre_app_nil l); eauto. by simplify_list_eq. }
    by apply app_nil in EqN as [].
  - destruct (IH (l1 ++ [y]) (z :: l2)) as [EqN ?].
    { by simplify_list_eq. }
    by apply app_nil in EqN as [].
Qed.
End props.

Section Forall.
Context {A B : Type}.
Implicit Types (P : A → Prop) (Q : A → B → Prop).
Implicit Types x : A.
Implicit Types y : B.
Implicit Types l : list A.
Implicit Types k : list B.

Lemma Forall_snoc_inv P x l :
  Forall P (l ++ [x]) → P x ∧ Forall P l.
Proof. rewrite Forall_app Forall_singleton. naive_solver. Qed.
Lemma Forall_inv_rev P l :
  Forall P l → l = [] ∨ (∃ x l', l = l' ++ [x] ∧ P x ∧ Forall P l').
Proof.
  intro. apply Forall_reverse in H.
  inversion H; [left|right].
  { rewrite -reverse_nil in H1. apply eq_sym, (inj reverse) in H1.  done. }
  exists x, (reverse l0).
  rewrite -reverse_cons.
  apply (f_equal reverse), eq_sym in H0.
  rewrite reverse_involutive in H0.
  split_and!; [done..|]. by apply Forall_reverse.
Qed.
Lemma Forall2_snoc_inv Q x l y k :
  Forall2 Q (l ++ [x]) (k ++ [y]) → Q x y ∧ Forall2 Q l k.
Proof.
  intro. apply Forall2_reverse in H. rewrite !reverse_snoc in H.
  rewrite -(reverse_involutive l) -(reverse_involutive k).
  apply Forall2_cons_1 in H as [??].
  split; [done|]. by apply Forall2_reverse.
Qed.
Lemma Forall2_snoc_inv_l Q x l k :
  Forall2 Q (l ++ [x]) k → ∃ y k', Q x y ∧ Forall2 Q l k' ∧ k = k' ++ [y].
Proof. move/Forall2_app_inv_l=>[k1][k2][H1][H2]Hk. list_simplifier. eauto. Qed.
Lemma Forall2_snoc_inv_r Q l k y :
  Forall2 Q l (k ++ [y]) → ∃ x l', Q x y ∧ Forall2 Q l' k ∧ l = l' ++ [x].
Proof. move/Forall2_app_inv_r=>[l1][l2][H1][H2]Hl. list_simplifier. eauto. Qed.
Lemma Forall2_snoc_nil_inv Q x l : Forall2 Q (l ++ [x]) [] → False.
Proof.
  move/Forall2_app_inv_l=>[k1][k2][H1][H2]Hk.
  list_simplifier. by apply nil_snoc in Hk.
Qed.
Lemma Forall2_nil_snoc_inv Q y k : Forall2 Q [] (k ++ [y]) → False.
Proof.
  move/Forall2_app_inv_r=>[l1][l2][H1][H2]Hl.
  list_simplifier. by apply nil_snoc in Hl.
Qed.

Global Instance Forall_sublist P :
  Proper ((flip sublist) ==> impl) (Forall P).
Proof.
  move => l1 l2 SUB. induction SUB; [done|rewrite !Forall_cons => [[??]]; naive_solver..].
Qed.
End Forall.
(* end move *)

Section filter.
Context {A B : Type}.
Implicit Types (P : A → Prop).

Lemma filter_sublist P `{∀ x, Decision (P x)} l :
  filter P l `sublist_of` l.
Proof.
  induction l; [done|]. rewrite filter_cons. case_decide; by constructor.
Qed.

Lemma Forall_filter P1 P2 `{∀ x, Decision (P2 x)} l :
  Forall P1 l → Forall P1 (filter P2 l).
Proof. specialize (filter_sublist P2 l). apply Forall_sublist. Qed.

Lemma list_filter_iff' P1 P2
    `{!∀ x, Decision (P1 x), !∀ x, Decision (P2 x)} l :
  Forall (λ x, P1 x ↔ P2 x) l →
  filter P1 l = filter P2 l.
Proof.
  intros HPiff. induction HPiff as [|a l IFFa IFFl IH].
  { rewrite !filter_nil //. }
  destruct (decide (P1 a)).
  - rewrite !filter_cons_True; [|naive_solver..]. by rewrite IH.
  - rewrite !filter_cons_False; [|naive_solver..]. by rewrite IH.
Qed.

Lemma filter_prefix P `{!∀ x, Decision (P x)} l1 l2
    (Sub : l1 `prefix_of` l2) :
  filter P l1 `prefix_of` filter P l2.
Proof.
  destruct Sub as [l ->].
  case l1 using rev_ind. { by econstructor. }
  rewrite !filter_app !filter_cons !filter_nil. by eexists.
Qed.

Lemma list_filter_lookup_Some_inv P `{∀ x, Decision (P x)}
    (l : list A) (i : nat) (x : A) :
  filter P l !! i = Some x → ∃ j, l !! j = Some x ∧ P x.
Proof.
  revert i. induction l. { by rewrite filter_nil. }
  intros i. case Ei: i => [|i']; subst.
  - case (decide (P a)) as [?|?].
    + rewrite filter_cons_True; [|done]. intros. simplify_list_eq.
      by exists O.
    + rewrite filter_cons_False; [|done]. move=> /IHl => [[j [? ?]]].
      by exists (S j).
  - case (decide (P a)) as [?|?].
    + rewrite filter_cons_True; [|done]. simplify_list_eq.
      move=> /IHl => [[j [? ?]]]. by exists (S j).
    + rewrite filter_cons_False; [|done].
      move=> /IHl => [[j [? ?]]]. by exists (S j).
Qed.

Lemma filter_seq_inv_snoc (P : nat → Prop) `{∀ (x : nat), Decision (P x)}
    (l : list nat) (n m : nat)
    (Eq : filter P (seq 0 n) = l ++ [m]) :
  l = filter P (seq 0 m).
Proof.
  revert m Eq. induction n; intros; [discriminate_list|].
  rewrite seq_S filter_app filter_cons filter_nil /= in Eq.
  case (decide (P n)) as [?|?].
  { by apply app_inj_tail in Eq as [Eq ->]. }
  rewrite app_nil_r in Eq. by apply IHn.
Qed.

Lemma take_filter_seq (P : nat → Prop) `{∀ (x : nat), Decision (P x)}
    (n i x : nat)
    (Hx : filter P (seq 0 n) !! i = Some x) :
  take i (filter P (seq 0 n)) = filter P (seq 0 x).
Proof.
  assert (HP := Hx).
  apply elem_of_list_lookup_2, elem_of_list_filter in HP as [_ HP].
  apply elem_of_seq in HP.
  assert (n = x + (n-x)) by lia.
  rewrite H0 seq_app filter_app.
  rewrite H0 seq_app filter_app in Hx.
  assert (n-x = 1 + (n-x-1)) by lia.
  rewrite H1 seq_app filter_app in Hx.
  destruct (lt_eq_lt_dec (length (filter P (seq 0 x))) i); last first. {
    rewrite lookup_app_l in Hx; auto.
    apply elem_of_list_lookup_2, elem_of_list_filter in Hx as [_ Hx].
    apply elem_of_seq in Hx; lia.
  }
  destruct s. {
    rewrite lookup_app_r in Hx; last lia.
    rewrite lookup_app_r in Hx; last first. {
      simpl.
      assert (length (filter P [x]) <= 1); last lia.
      trans (length [x]); auto. apply filter_length.
    }
    apply elem_of_list_lookup_2, elem_of_list_filter in Hx as [_ Hx].
    apply elem_of_seq in Hx; lia.
  }
  rewrite take_app_le; last lia.
  rewrite take_ge; last lia; auto.
Qed.
End filter.

(* list before *)
Section list.
Context {A: Type}.
Implicit Types (l: list A) (x y: A).

Definition list_before l x y : Prop :=
  ∃ i j, l !! i = Some x ∧ l !! j = Some y ∧ (i ≤ j)%nat.

Lemma list_before_sqsubseteq l l' x y :
  list_before l x y → l ⊑ l' → list_before l' x y.
Proof.
  intros (i & j & Eqi & Eqj & Le) [l2 Eql]. rewrite Eql.
  exists i, j. repeat split; [by apply lookup_app_l_Some..|done].
Qed.

Lemma list_before_suffix l l' x y :
  list_before l x y → l `suffix_of` l' → list_before l' x y.
Proof.
  intros (i & j & Eqi & Eqj & Le) [l2 Eql]. rewrite Eql.
  exists (i + length l2), (j + length l2). repeat split; [..|lia].
  - rewrite lookup_app_r; [|lia]. by rewrite Nat.add_sub.
  - rewrite lookup_app_r; [|lia]. by rewrite Nat.add_sub.
Qed.

Definition strict_subseq l l' : Prop := (∃ l1 l2, l' = l1 ++ l ++ l2).
Global Instance strict_subseq_po : PartialOrder strict_subseq.
Proof.
  constructor; first constructor.
  - intros l. exists [], []. by rewrite app_nil_r.
  - intros l1 l2 l3 (l11 & l12 & Eq1) (l21 & l22 & Eq2).
    exists (l21 ++ l11), (l12 ++ l22). by simplify_list_eq.
  - intros l1 l2 (l11 & l12 & Eq1) (l21 & l22 & Eq2). simplify_list_eq.
    have Eq' : l2 = (l11 ++ l21) ++ l2 ++ (l22 ++ l12) by simplify_list_eq.
    apply pre_post_app_nil in Eq' as [[]%app_nil []%app_nil]. by subst.
Qed.

Lemma strict_subseq_cons_r L L' a :
  strict_subseq L L' → strict_subseq L (a :: L').
Proof. intros (L1 & L2 & Eq). exists (a :: L1), L2. by simplify_list_eq. Qed.
Lemma strict_subseq_cons_l L L' a :
  strict_subseq (a :: L) L' → strict_subseq L L'.
Proof. intros (L1 & L2 & Eq). exists (L1 ++ [a]), L2. by simplify_list_eq. Qed.

Global Instance strict_subseq_dec `{Countable A} L L':
  Decision (strict_subseq L L').
Proof.
  revert L.
  induction L' as [|a L' IH] => L.
  - destruct L.
    + left. by exists [], [].
    + right. intros (L1 & L2 & Eq). symmetry in Eq.
      apply app_nil in Eq as [? Eq%app_nil]. by destruct Eq.
  - case (decide (strict_subseq L L')) => [SUB|NSUB].
    { left. by apply strict_subseq_cons_r. }
    destruct L as [|b L].
    { left. by exists [], (a :: L'). }
    case (decide (b = a)) => ?.
    { subst b. case (decide (L `prefix_of` L')) => [PRE|NPRE].
      - left. apply choice in PRE as [L2 Eq2].
        + exists [], L2. by simplify_list_eq.
        + intros. solve_decision.
      - right. intros (L1 & L2 & Eq2). simplify_list_eq.
        destruct L1 as [|a1 L1]; simplify_list_eq.
        + apply NPRE. by exists L2.
        + apply NSUB. exists L1, L2. by simplify_list_eq. }
    right. intros (L1 & L2 & Eq2).
    destruct L1 as [|a1 L1]; simplify_list_eq.
    apply NSUB. exists L1, L2. by simplify_list_eq.
Qed.

Lemma NoDup_app_mid_inj (L11 L12 L21 L22 : list A) a :
  NoDup (L11 ++ [a] ++ L12) →
  L11 ++ [a] ++ L12 = L21 ++ [a] ++ L22 → L11 = L21 ∧ L12 = L22.
Proof.
  intros ND Eq.
  have HL1: (L11 ++ [a] ++ L12) !! length L11 = Some a.
  { by apply list_lookup_middle. }
  have HL2: (L21 ++ [a] ++ L22) !! length L21 = Some a.
  { by apply list_lookup_middle. }
  have EqL: length L11 = length L21.
  { revert ND HL1 HL2. rewrite -Eq. by apply NoDup_lookup. }
  have Eq1: L11 = L21.
  { rewrite -(take_app L11 ([a] ++ L12)) -(take_app L21 ([a] ++ L22)).
    by rewrite Eq EqL. }
  by simplify_list_eq.
Qed.

Lemma strict_subseq_NoDup_inj_l L L1 L2 a :
  NoDup L → length L1 = length L2 →
  strict_subseq (L1 ++ [a]) L → strict_subseq (L2 ++ [a]) L → L1 = L2.
Proof.
  intros ND EqL (L11 & L12 & Eq1) (L21 & L22 & Eq2).
  rewrite !app_assoc -(app_assoc (L11 ++ L1)) in Eq1.
  rewrite !app_assoc -(app_assoc (L21 ++ L2)) in Eq2. subst L.
  destruct (NoDup_app_mid_inj _ _ _ _ _ ND Eq2). clear Eq2. by simplify_list_eq.
Qed.

Lemma strict_subseq_NoDup_inj_r L L1 L2 a :
  NoDup L → length L1 = length L2 →
  strict_subseq (a :: L1) L → strict_subseq (a :: L2) L → L1 = L2.
Proof.
  intros ND EqL (L11 & L12 & Eq1) (L21 & L22 & Eq2).
  rewrite -app_comm_cons in Eq1. rewrite -app_comm_cons in Eq2. subst L.
  destruct (NoDup_app_mid_inj _ _ _ _ _ ND Eq2). clear Eq2. by simplify_list_eq.
Qed.

Lemma strict_subseq_NoDup_inj_l_single (L: list A) (b1 b2 a : A) :
  NoDup L →
  strict_subseq ([b1; a]) L → strict_subseq ([b2; a]) L → b1 = b2.
Proof.
  intros ND S1 S2.
  have ?: [b1] = [b2].
  { by apply (strict_subseq_NoDup_inj_l _ _ _ a ND); auto. }
  by simplify_list_eq.
Qed.

Lemma strict_subseq_NoDup_inj_r_single (L: list A) (b1 b2 a : A) :
  NoDup L →
  strict_subseq ([a; b1]) L → strict_subseq ([a; b2]) L → b1 = b2.
Proof.
  intros ND S1 S2.
  have ?: [b1] = [b2].
  { by apply (strict_subseq_NoDup_inj_r _ _ _ a ND); auto. }
  by simplify_list_eq.
Qed.

Lemma strict_subseq_mono_r (L L1 L2 : list A) (SUB: L1 ⊑ L2):
  strict_subseq L L1 → strict_subseq L L2.
Proof.
  intros (L11 & L12 & Eq1). destruct SUB as [L13 Eq2].
  exists L11, (L12 ++ L13). by simplify_list_eq.
Qed.

Global Instance strict_subseq_mono_r_instance :
  Proper ((=) ==> (⊑) ==> (impl)) strict_subseq.
Proof. intros ??-> ?? SUB ?. by apply (strict_subseq_mono_r _ _ _ SUB). Qed.

Lemma lookup_strict_subseq l x y i j :
  l !! i = Some x → l !! j = Some y → (i < j)%nat →
  ∃ x' j', strict_subseq [x; x'] l ∧ l !! j' = Some x' ∧ (j' ≤ j)%nat.
Proof.
  intros Eqi Eqj Ltj.
  destruct (elem_of_list_split_length _ _ _ Eqi) as (l1 & l2 & Eq1 & Len1).
  destruct l2 as [|x' l2].
  - exfalso. clear Eqi. subst i l. rewrite -(app_nil_r (l1 ++ [x])) in Eqj.
    apply lookup_app_Some in Eqj.
    destruct Eqj as [Eqj|[]]; [|done].
    apply lookup_lt_Some in Eqj.
    rewrite app_length /= in Eqj. lia.
  - exists x', (length l1 + 1)%nat. split.
    + exists l1, l2. by simplify_list_eq.
    + rewrite Eq1. rewrite (app_assoc _ [x]). split.
      * apply list_lookup_middle. by rewrite app_length /=.
      * subst i. clear -Ltj. lia.
Qed.

End list.

Section adjacent.
Context {A : Type}.
Implicit Types (L : list A) (a b : A).

Definition adjacent_in a b L : Prop :=
  ∃ i, L !! i = Some a ∧ L !! (i+1)%nat = Some b.

Lemma adjacent_in_mono a b L1 L2 :
  L1 ⊑ L2 → adjacent_in a b L1 → adjacent_in a b L2.
Proof.
  intros [L12 Eq2] (i & Eqa & Eqb).
  exists i. simplify_list_eq. split; by apply lookup_app_l_Some.
Qed.

Global Instance adjacent_in_mono_instance a b :
  Proper ((⊑) ==> (impl)) (adjacent_in a b).
Proof. intros ????. by eapply adjacent_in_mono. Qed.

Global Instance adjacent_in_decide `{Countable A} a b L :
  Decision (adjacent_in a b L).
Proof.
  induction L as [|x L].
  - right. by intros [i [? _]].
  - case (decide (adjacent_in a b L)) => [In|NIn].
    + left. destruct In as [i [Eq1 Eq2]]. by exists (S i).
    + case (decide (x = a)) => [->|NEq].
      * case (decide (L !! 0 = Some b)) => [Eq1|NEq1].
        { left. by exists 0. }
        { right. intros [i [Eqi1 Eqi2]]. case (decide (0 < i)%nat) => Eqi.
          - rewrite (lookup_app_r [a]) in Eqi1; last (by simpl; lia).
            rewrite (lookup_app_r [a]) in Eqi2; last (by simpl; lia).
            apply NIn. exists (i - length [a]). split; [done|].
            rewrite -Eqi2. f_equal. simpl. lia.
          - have ?: i = 0 by lia. subst i. by simplify_eq. }
      * right. intros [i [Eqi1 Eqi2]].
        case (decide (0 < i)%nat) => Eqi.
        { rewrite (lookup_app_r [x]) in Eqi1; last (by simpl; lia).
          rewrite (lookup_app_r [x]) in Eqi2; last (by simpl; lia).
          apply NIn. exists (i - length [a]). split; [done|].
          rewrite -Eqi2. f_equal. simpl. lia. }
        { have ?: i = 0 by lia. subst i. simpl in Eqi1. by simplify_eq. }
Qed.

Lemma adjacent_in_NoDup_inj_l L a1 a2 b :
  NoDup L → adjacent_in a1 b L → adjacent_in a2 b L → a1 = a2.
Proof.
  intros ND [i1 [Eqa1 Eqb1]] [i2 [Eqa2 Eqb2]].
  have Eqi:= NoDup_lookup _ _ _ _ ND Eqb1 Eqb2. apply Nat.add_cancel_r in Eqi.
  subst. rewrite Eqa1 in Eqa2. by simplify_eq.
Qed.

Lemma adjacent_in_NoDup_inj_r L a b1 b2 :
  NoDup L → adjacent_in a b1 L → adjacent_in a b2 L → b1 = b2.
Proof.
  intros ND [i1 [Eqa1 Eqb1]] [i2 [Eqa2 Eqb2]].
  have Eqi:= NoDup_lookup _ _ _ _ ND Eqa1 Eqa2.
  subst. rewrite Eqb1 in Eqb2. by simplify_eq.
Qed.

Lemma strict_subseq_adjacent_in x x' l :
  strict_subseq [x; x'] l → adjacent_in x x' l.
Proof.
  intros (l1 & l2 & ->).
  exists (length l1). split.
  - rewrite (lookup_app_r l1) // Nat.sub_diag //.
  - rewrite (_ : l1 ++ [x; x'] ++ l2 = (l1 ++ [x]) ++ ([x'] ++ l2)).
    + have EqL1 : length (l1 ++ [x]) = length l1 + 1 by rewrite app_length /=.
      rewrite lookup_app_r.
      * by rewrite EqL1 Nat.sub_diag //.
      * by rewrite EqL1.
    + by simplify_list_eq.
Qed.
End adjacent.

Global Instance : Params (@adjacent_in) 3 := {}.

Section alter.
Context {A : Type}.
Lemma alter_take_drop f l i (x: A) :
  l !! i = Some x →
  alter f i l = take i l ++ [f x] ++ drop (S i) l.
Proof.
  revert l.
  induction i; intros.
  - destruct l; inversion H. by list_simplifier.
  - destruct l; inversion H. list_simplifier.
    apply IHi in H. by rewrite H.
Qed.
End alter.

Section xo.
Context {A : Type}.
Implicit Types (l : list A) (ord : list nat).

Lemma lookup_xo : ∀ (n e : nat) (LT : (e < n)%nat), (seq 0 n) !! e = Some e.
Proof. intros. by rewrite lookup_seq_lt. Qed.

Lemma xo_events l : Forall (λ e, is_Some (l !! e)) (seq 0 (length l)).
Proof.
  rewrite Forall_lookup => i e H. have H' := H. apply lookup_lt_is_Some_2.
  rewrite lookup_xo in H; simplify_eq;
    apply lookup_lt_Some in H'; by rewrite seq_length in H'.
Qed.

Lemma ord_nodup N ord (PERM : ord ≡ₚ seq 0 N) : NoDup ord.
Proof. rewrite (NoDup_Permutation_proper _ _ PERM). apply NoDup_seq. Qed.

Lemma ord_idx_event l ord i e
    (PERM : ord ≡ₚ seq 0 (length l))
    (Ee : ord !! i = Some e) :
  is_Some (l !! e).
Proof.
  apply Permutation_inj in PERM as [LEN (f & _ & PERM)].
  rewrite ->PERM,lookup_seq in Ee. destruct Ee as [-> ?]. simpl.
  by apply lookup_lt_is_Some_2.
Qed.

End xo.
