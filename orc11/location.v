From stdpp Require Import sorting.
From orc11 Require Export base.

Require Import stdpp.options.

(** Classes for locations *)

Class LocFacts (loc: Type) := {
  loc_inhab :> Inhabited loc;
  loc_eqdec :> EqDecision loc;
  loc_count :> Countable loc;
}.
(* The next line is commented out to avoid TC divergence in lambda-rust-weak. *)
(* Hint Mode LocFacts ! : typeclass_instances. *)

Class Shift (loc: Type) := {
  shift : loc → nat → loc;
  shift_nat_inj l (n1 n2: nat) : shift l n1 = shift l n2 → n1 = n2;
  shift_nat_assoc l (n1 n2: nat) : shift (shift l n1) n2 = shift l (n1 + n2);
  shift_0 l : shift l 0 = l;
}.
Global Hint Mode Shift ! : typeclass_instances.

Infix ">>" := shift (at level 50, left associativity) : stdpp_scope.
Notation "(>>)" := shift (only parsing) : stdpp_scope.
Notation "( l >>)" := (shift l) (only parsing) : stdpp_scope.
Arguments shift : simpl never.

Class StateFacts (loc state: Type) `{!LocFacts loc} := {
  state_dom :> Dom state (gset loc);
  state_wf :> Wellformed state;
  state_dealloc : state → gset loc;
  state_dealloc_sub σ : state_dealloc σ ⊆ dom σ;
}.
Arguments StateFacts _ _ {_}.
(* Hint Mode StateFacts ! ! : typeclass_instances. *)

Class Allocator (loc state: Type)
  `{!LocFacts loc} `{!StateFacts loc state} `{!Shift loc} := {
  alloc : state → nat → loc → Prop;
  dealloc : state → nat → loc → Prop;
  alloc_add_fresh σ l n:
    alloc σ n l
      → ∀ (n' : nat), n' < n → l >> n' ∉ dom σ;
  dealloc_remove σ l n :
    dealloc σ n l
      → ∀ (n' : nat), n' < n →
          l >> n' ∈ (dom σ ∖ state_dealloc σ);
}.
Arguments Allocator _ _ {_ _ _}.

Arguments alloc {_ _ _ _ _ _}.
Arguments dealloc {_ _ _ _ _ _}.
Arguments alloc_add_fresh {_ _ _ _ _ _}.
Arguments dealloc_remove {_ _ _ _ _ _}.


(** Locations as positives *)

Global Instance pos_loc : LocFacts positive.
Proof. esplit; apply _. Qed.

Global Program Instance pos_loc_shift : Shift positive
  := {| shift := λ p z, Z.to_pos (Zpos p + Z.of_nat z) |}.
Next Obligation. move => l n1 n2 H. apply Z2Pos.inj in H; lia. Defined.
Next Obligation. intros. simpl. f_equal. rewrite Z2Pos.id; lia. Defined.
Next Obligation. done. Defined.

Global Instance pos_ge_transitive : Transitive Pos.ge.
Proof.
  move => ???/Pos.ge_le? /Pos.ge_le?. apply Pos.le_ge. by etrans.
Qed.

Global Instance pos_ge_total : Total Pos.ge.
Proof.
  move => x y.
  case (decide (x ≤ y)%positive) => [?|].
  - right. by apply Pos.le_ge.
  - rewrite <- Pos.lt_nle. left. by apply Pos.le_ge, Pos.lt_le_incl.
Qed.

Section LocPos.
  Context `{!StateFacts positive state}.

  Implicit Types (σ : state) (l : positive).

  Inductive pos_alloc (σ : state) n l : Prop :=
    | PosAlloc
        (NONEMPTY: 0 < n)
        (NEW: ∀ n', n' < n → l >> n' ∉ dom σ)
        : pos_alloc σ n l.

  Inductive pos_dealloc (σ: state)
    : nat → positive → Prop :=
    | PosDealloc l (ALLOC: l ∈ (dom σ ∖ state_dealloc σ))
      : pos_dealloc σ 1%nat l.

  Definition fresh_pos σ :=
    let loclst := merge_sort (Pos.ge) (elements (dom σ)) in
    match loclst with
    | nil => 1%positive
    | max :: _ => Pos.succ max
    end.

  Lemma fresh_pos_max σ l (In : l ∈ dom σ) :
    (l < fresh_pos σ)%positive.
  Proof.
    rewrite /fresh_pos.
    assert (InL: l ∈ merge_sort Pos.ge (elements (dom σ))).
    { by rewrite (merge_sort_Permutation Pos.ge (elements _)) elem_of_elements. }
    destruct (merge_sort (Pos.ge) (elements (dom σ))) as [|max L] eqn:HEq.
    - by apply elem_of_nil in InL.
    - apply elem_of_cons in InL as [?|InL]; first by (subst max; lia).
      assert (HS := StronglySorted_merge_sort Pos.ge (elements (dom σ))).
      rewrite HEq in HS.
      inversion HS as [|?? SS FA]. subst.
      rewrite -> Forall_forall in FA. apply FA in InL.
      apply Pos.ge_le in InL. by apply Pos.lt_succ_r.
  Qed.

  Lemma is_fresh_pos_block σ (n : nat) :
    fresh_pos σ >> n ∉ dom σ.
  Proof.
    assert (LE: (fresh_pos σ ≤ fresh_pos σ >> n)%positive).
    { rewrite /shift /pos_loc_shift /=. destruct n; simpl; [done|lia]. }
    move => /fresh_pos_max. lia.
  Qed.

  Lemma pos_alloc_fresh n σ:
    let l := fresh_pos σ in
    0 < n → pos_alloc σ n l.
  Proof.
    intros l Hn. constructor; first by assumption. intros.
    by apply is_fresh_pos_block.
  Qed.

  Global Program Instance pos_allocator : Allocator positive state :=
    {| alloc := pos_alloc;
     dealloc := pos_dealloc; |}.
  Next Obligation. intros ??? ALL. inversion ALL. by apply NEW. Qed.
  Next Obligation.
    intros ??? DEL ? Lt. inversion DEL. subst. apply Nat.lt_1_r in Lt. subst.
    by apply ALLOC.
  Qed.
End LocPos.

(** Locations as blocks *)

Definition block := positive.
Definition lblock : Type := block * Z.

Global Instance lblock_loc : LocFacts lblock.
Proof. esplit; apply _. Qed.

Global Program Instance lblock_shift : Shift lblock :=
  {| shift := λ b z, (b.1, (b.2 + Z.of_nat z)%Z) |}.
Next Obligation. move => ???. inversion 1. lia. Defined.
Next Obligation. intros. simpl. f_equal. lia. Defined.
Next Obligation. intros []. f_equal. simpl. lia. Defined.

Implicit Type (l : lblock).
Lemma shift_lblock_assoc l n n':
  (l >> n) >> n' = l >> (n+n').
Proof. rewrite /shift /lblock_shift /=. f_equal. lia. Qed.

Lemma shift_lblock_0 l : l >> 0 = l.
Proof. apply shift_0. Qed.

Global Instance shift_lblock_inj l : Inj (=) (=) (l >>).
Proof. destruct l as [b o]; intros n n' [=?]; lia. Qed.

Lemma shift_lblock l n : (l >> n).1 = l.1.
Proof. done. Qed.

Section LocBlock.
  Context `{!StateFacts lblock state}.

  Implicit Types (σ : state).

  Inductive lblock_alloc σ n l : Prop :=
    | LBlockAlloc
        (NONEMPTY: 0 < n)
        (MAX: ∀ n', (l.1, n') ∉ dom σ)
        : lblock_alloc σ n l.

  Inductive lblock_dealloc σ n l : Prop :=
    | LBlockDealloc
        (NONEMPTY: 0 < n)
        (ALLOC: ∀ n': nat, (n' < n)%nat → l >> n' ∈ (dom σ ∖ state_dealloc σ))
        (SIZE: ∀ n': nat, l >> n' ∈ dom σ ↔ (n' < n)%nat)
      : lblock_dealloc σ n l.

  Definition fresh_block (σ : state) : block :=
    let loclst : list lblock := elements (dom σ) in
    let blockset : gset block := foldr (λ l, ({[l.1]} ∪.)) ∅ loclst in
    fresh blockset.

  Lemma is_fresh_block σ i : (fresh_block σ,i) ∉ dom σ.
  Proof.
    assert (∀ l ls (X : gset block),
      l ∈ ls → l.1 ∈ foldr (λ l, ({[l.1]} ∪.)) X ls) as help.
    { induction 1; set_solver. }
    rewrite /fresh_block /shift /= -elem_of_elements.
    move=> /(help _ _ ∅) /=. apply is_fresh.
  Qed.

  Lemma lblock_alloc_fresh n σ:
    let l := (fresh_block σ, 0%Z) in
    0 < n →
    lblock_alloc σ n l.
  Proof.
    intros l Hn. constructor; [by assumption|].
    intros i. apply (is_fresh_block _ i).
  Qed.


  Global Program Instance lblock_allocator : Allocator lblock state :=
    {| alloc := lblock_alloc;
      dealloc := lblock_dealloc; |}.
    Next Obligation. intros ??? Hl ??. inversion Hl. by apply MAX. Qed.
    Next Obligation. intros ??? Hl ??. inversion Hl. by apply ALLOC. Qed.
End LocBlock.
