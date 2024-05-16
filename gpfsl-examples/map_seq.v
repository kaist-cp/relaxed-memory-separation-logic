Require Import stdpp.fin_maps.

Require Import stdpp.options.

Definition pos_add_nat (p : positive) (n : nat) : positive :=
  Pos.of_nat (Pos.to_nat p + n).

Infix "+p" := pos_add_nat (at level 50, left associativity).

Lemma pos_add_0_r p : p +p 0 = p.
Proof. unfold pos_add_nat. by rewrite Nat.add_0_r, Pos2Nat.id. Qed.

Lemma pos_add_succ_r p i : (p +p S i) = (Pos.succ p +p i).
Proof. unfold pos_add_nat. f_equal. rewrite Pos2Nat.inj_succ. lia. Qed.

Lemma pos_add_assoc p i j : (p +p (i + j)) = (p +p i +p j).
Proof. unfold pos_add_nat. f_equal. lia. Qed.

Lemma pos_add_succ_r_2 p i : (p +p S i) = Pos.succ (p +p i).
Proof.
  rewrite <-Nat.add_1_r, pos_add_assoc. unfold pos_add_nat at 1.
  rewrite Nat2Pos.inj_add; lia.
Qed.

Global Instance pos_add_nat_inj p : Inj (=) (=) (pos_add_nat p).
Proof.
  intros i j. unfold pos_add_nat.
  rewrite Nat2Pos.inj_iff; [|lia..]. lia.
Qed.

(* TODO upstream *)
(* This should imply maq_seq_cons and map_seq_snoc. *)
Lemma map_seq_insert `{FinMap nat M} {A}
  (start : nat) (xs : list A) (i : nat) (x : A) :
  (i < length xs) →
  (map_seq start (<[i := x]> xs) : M A) = <[i + start := x]>(map_seq start xs).
Proof.
  intros Lti. apply map_eq. intros i'.
  destruct (decide (i' = i + start)) as [Eq|NEq].
  - subst i'. rewrite lookup_insert. apply lookup_map_seq_Some.
    split; [lia|]. rewrite Nat.add_sub. by apply list_lookup_insert.
  - rewrite lookup_insert_ne; [|done].
    destruct (map_seq start xs !! i') as [x'|] eqn:Eqi'.
    + apply lookup_map_seq_Some.
      apply lookup_map_seq_Some in Eqi' as [Lei' Eqi'].
      split; [done|]. rewrite list_lookup_insert_ne; [done|lia].
    + apply lookup_map_seq_None. rewrite insert_length.
      by apply lookup_map_seq_None in Eqi'.
Qed.

(** map_seq for positive *)
(* Copied from map_seq for nat *)
Fixpoint map_seqP `{Insert positive A M, Empty M}
  (start : positive) (xs : list A) : M :=
  match xs with
  | [] => ∅
  | x :: xs => <[start:=x]> (map_seqP (Pos.succ start) xs)
  end.

Local Open Scope positive_scope.

Section map_seqP.
  Context `{FinMap positive M} {A : Type}.
  Implicit Types x : A.
  Implicit Types xs : list A.

  Local Set Default Proof Using "Type*".

  Lemma lookup_map_seqP_Some_inv start xs i x :
    xs !! i = Some x ↔ map_seqP (M:=M A) start xs !! (start +p i) = Some x.
  Proof.
    revert start i. induction xs as [|x' xs IH]; intros start i; simpl.
    { by rewrite lookup_empty, lookup_nil. }
    destruct i as [|i]; simpl.
    { by rewrite pos_add_0_r, lookup_insert. }
    rewrite lookup_insert_ne.
    - by rewrite (IH (Pos.succ start)), pos_add_succ_r.
    - clear. unfold pos_add_nat. rewrite Nat2Pos.inj_add; [|lia..].
      rewrite Pos2Nat.id. lia.
  Qed.
  Lemma lookup_map_seqP_Some start xs i x :
    map_seqP (M:=M A) start xs !! i = Some x ↔
      start ≤ i ∧ xs !! (Pos.to_nat i - Pos.to_nat start)%nat = Some x.
  Proof.
    destruct (decide (start ≤ i)) as [|Hsi].
    { rewrite (lookup_map_seqP_Some_inv start).
      replace (start +p (Pos.to_nat i - Pos.to_nat start)) with i.
      - naive_solver.
      - unfold pos_add_nat. rewrite Nat.add_comm, Nat.sub_add; [by rewrite Pos2Nat.id|lia]. }
    split; [|naive_solver]. intros Hi; destruct Hsi.
    revert start i Hi. induction xs as [|x' xs IH]; intros start i; simpl.
    { by rewrite lookup_empty. }
    rewrite lookup_insert_Some; intros [[-> ->]|[? ?%IH]]; lia.
  Qed.

  Lemma lookup_map_seqP_None start xs i :
    map_seqP (M:=M A) start xs !! i = None ↔
      i < start ∨ start +p (length xs) ≤ i.
  Proof.
    trans (¬start ≤ i ∨ ¬is_Some (xs !! (Pos.to_nat i - Pos.to_nat start)%nat)).
    - rewrite eq_None_not_Some, <-not_and_l. unfold is_Some.
      setoid_rewrite lookup_map_seqP_Some. naive_solver.
    - rewrite lookup_lt_is_Some. unfold pos_add_nat.
      rewrite Nat.nlt_ge, <-Pos.lt_nle.
      destruct (length xs).
      + rewrite Nat.add_0_r, Pos2Nat.id. lia.
      + rewrite Nat2Pos.inj_add; [|lia..].
        rewrite Pos2Nat.id, Pos2Nat.inj_le, Pos2Nat.inj_add, Nat2Pos.id; lia.
  Qed.

  Lemma lookup_map_seqP_last_idx start xs x i :
    map_seqP (M:=M A) start xs !! i = Some x →
    map_seqP (M:=M A) start xs !! (i + 1) = None →
    i + 1 = start +p length xs.
  Proof.
    intros [Lei Eqi]%lookup_map_seqP_Some Eqi1%lookup_map_seqP_None.
    destruct Eqi1 as [Lt1|Lei1].
    - lia.
    - apply Pos.le_antisym; [|done]. clear Lei1.
      apply lookup_lt_Some, Nat.lt_sub_lt_add_l, Nat.le_succ_l in Eqi.
      unfold pos_add_nat. apply Pos2Nat.inj_le.
      rewrite Nat2Pos.id; [|lia].
      by rewrite Pos.add_1_r, Pos2Nat.inj_succ.
  Qed.

  Lemma lookup_map_seqP_last_idx' start xs x i :
    map_seqP (M:=M A) start xs !! i = Some x →
    map_seqP (M:=M A) start xs !! (i + 1) = None →
    (Pos.to_nat i - Pos.to_nat start)%nat = (length xs - 1)%nat.
  Proof.
    intros Eq1 Eq2.
    assert (Eqi := lookup_map_seqP_last_idx _ _ _ _ Eq1 Eq2).
    assert (LeL: (1 ≤ length xs)%nat).
    { apply lookup_map_seqP_Some in Eq1 as [? Eq1].
      apply lookup_lt_Some in Eq1. lia. }
    revert Eqi. unfold pos_add_nat.
    rewrite Nat2Pos.inj_add; [|lia|lia].
    rewrite Pos2Nat.id. lia.
  Qed.

  Lemma lookup_map_seqP_last start xs x i :
    map_seqP (M:=M A) start xs !! i = Some x →
    map_seqP (M:=M A) start xs !! (i + 1) = None →
    xs !! (length xs - 1)%nat = Some x.
  Proof.
    intros Eq1 Eq2.
    assert (Eqi := lookup_map_seqP_last_idx' _ _ _ _ Eq1 Eq2).
    rewrite <-Eqi.
    by apply lookup_map_seqP_Some in Eq1 as [? Eq1].
  Qed.

  Lemma map_seqP_singleton start x :
    map_seqP (M:=M A) start [x] = {[ start := x ]}.
  Proof. done. Qed.

  Lemma map_seqP_app_disjoint start xs1 xs2 :
    map_seqP (M:=M A) start xs1 ##ₘ map_seqP (start +p length xs1) xs2.
  Proof.
    apply map_disjoint_spec; intros i x1 x2. rewrite !lookup_map_seqP_Some.
    unfold pos_add_nat.
    intros [Le1 Lt1%lookup_lt_Some] [Le2%Pos2Nat.inj_le Lt2%lookup_lt_Some].
    revert Le2 Lt2. rewrite Nat2Pos.id; lia.
  Qed.
  Lemma map_seqP_app start xs1 xs2 :
    map_seqP start (xs1 ++ xs2)
    =@{M A} map_seqP start xs1 ∪ map_seqP (start +p length xs1) xs2.
  Proof.
    revert start. induction xs1 as [|x1 xs1 IH]; intros start; simpl.
    - by rewrite (left_id_L _ _), pos_add_0_r.
    - by rewrite IH, pos_add_succ_r, !insert_union_singleton_l, (assoc_L _).
  Qed.

  Lemma map_seqP_cons_disjoint start xs :
    map_seqP (M:=M A) (Pos.succ start) xs !! start = None.
  Proof. rewrite lookup_map_seqP_None. lia. Qed.
  Lemma map_seqP_cons start xs x :
    map_seqP start (x :: xs) =@{M A} <[start:=x]> (map_seqP (Pos.succ start) xs).
  Proof. done. Qed.

  Lemma map_seqP_snoc_disjoint start xs :
    map_seqP (M:=M A) start xs !! (start +p length xs) = None.
  Proof. rewrite lookup_map_seqP_None. lia. Qed.
  Lemma map_seqP_snoc start xs x :
    map_seqP start (xs ++ [x]) =@{M A} <[start +p length xs:=x]> (map_seqP start xs).
  Proof.
    rewrite map_seqP_app, map_seqP_singleton.
    by rewrite insert_union_singleton_r by (by rewrite map_seqP_snoc_disjoint).
  Qed.

  Lemma fmap_map_seqP {B} (f : A → B) start xs :
    f <$> map_seqP start xs =@{M B} map_seqP start (f <$> xs).
  Proof.
    revert start. induction xs as [|x xs IH]; intros start; csimpl.
    { by rewrite fmap_empty. }
    by rewrite fmap_insert, IH.
  Qed.
End map_seqP.
