From iris.algebra Require Export auth max_prefix_list.
From iris.algebra Require Import updates local_updates proofmode_classes.

From iris.prelude Require Import options.

(* TODO: upstream? *)
Lemma map_relation_iff `{∀ A, Lookup K A (M A)} {A B}
    (R1 R2 : A → B → Prop) (P1 P2 : A → Prop) (Q1 Q2 : B → Prop)
    (IffR : ∀ a b, R1 a b ↔ R2 a b) (IffP : ∀ a, P1 a ↔ P2 a) (IffQ : ∀ b, Q1 b ↔ Q2 b)
    (m1 : M A) (m2 : M B) :
  map_relation R1 P1 Q1 m1 m2 ↔ map_relation R2 P2 Q2 m1 m2.
Proof.
  split; intros REL i; move: (REL i); destruct (m1 !! i), (m2 !! i); simpl; naive_solver.
Qed.

(** List of [mono_listR] *)

Definition max_prefix_list_list (A : Type) := gmap nat (max_prefix_list A).
Definition max_prefix_list_listR (A : ofe) := gmapR nat (max_prefix_listUR A).
Definition max_prefix_list_listUR (A : ofe) := gmapUR nat (max_prefix_listUR A).

Definition to_max_prefix_list_list {A} (l : list (list A)) : max_prefix_list_list A :=
  to_max_prefix_list <$> map_seq 0 l.
Global Instance: Params (@to_max_prefix_list_list) 1 := {}.

Definition prefixes {A} : relation (list (list A)) := map_included prefix.

Infix "`prefixes_of`" := prefixes (at level 70) : stdpp_scope.

Section max_prefix_list_list.
  Context {A : ofe}.
  Implicit Types (l : list A) (ll : list (list A)).

  Global Instance to_max_prefix_list_list_ne : NonExpansive (@to_max_prefix_list_list A).
  Proof. solve_proper. Qed.
  Global Instance to_max_prefix_list_list_proper :
    Proper ((≡) ==> (≡)) (@to_max_prefix_list_list A).
  Proof.
    intros ???. rewrite /to_max_prefix_list_list !fmap_map_seq.
    by do 2 f_equiv.
  Qed.
  Global Instance to_max_prefix_list_list_dist_inj n :
    Inj (dist n) (dist n) (@to_max_prefix_list_list A).
  Proof.
    rewrite /to_max_prefix_list_list. intros ll1 ll2 Hll. apply list_dist_lookup=> i.
    move: (Hll i). rewrite !lookup_fmap !lookup_map_seq Nat.sub_0_r.
    rewrite !option_guard_True; [|lia..].
    case El1: (ll1 !! i) => [l1|]; case El2: (ll2 !! i) => [l2|]; inversion_clear 1; [|done].
    f_equiv. by apply to_max_prefix_list_dist_inj.
  Qed.
  Global Instance to_max_prefix_list_list_inj : Inj (≡) (≡) (@to_max_prefix_list_list A).
  Proof.
    intros ll1 ll2. rewrite !equiv_dist=> ? n. by apply (inj to_max_prefix_list_list).
  Qed.

  Global Instance mono_list_lb_core_id (mll : max_prefix_list_list A) : CoreId mll := _.

  Lemma to_max_prefix_list_list_valid ll : ✓ to_max_prefix_list_list ll.
  Proof.
    intros i.
    rewrite /to_max_prefix_list_list fmap_map_seq lookup_map_seq Nat.sub_0_r list_lookup_fmap.
    rewrite !option_guard_True; [|lia..].
    destruct (ll !! i); [|done].
    simpl. apply Some_valid, to_max_prefix_list_valid.
  Qed.
  Lemma to_max_prefix_list_list_validN n ll : ✓{n} to_max_prefix_list_list ll.
  Proof. apply cmra_valid_validN, to_max_prefix_list_list_valid. Qed.

  Lemma to_max_prefix_list_list_op_l ll1 ll2 :
    ll1 `prefixes_of` ll2 →
    to_max_prefix_list_list ll1 ⋅ to_max_prefix_list_list ll2 ≡ to_max_prefix_list_list ll2.
  Proof.
    rewrite /prefixes /map_included /map_relation => H i. rewrite lookup_op.
    rewrite /to_max_prefix_list_list !fmap_map_seq !lookup_map_seq Nat.sub_0_r !list_lookup_fmap.
    rewrite !option_guard_True; [|lia..].
    move: (H i).
    case El1: (ll1 !! i) => [l1|]; case El2: (ll2 !! i) => [l2|]; inversion_clear 1; simplify_eq/=.
    - rewrite -Some_op. rewrite to_max_prefix_list_op_l; [done|by eexists].
    - rewrite left_id //.
    - done.
  Qed.
  Lemma to_max_prefix_list_list_op_r ll1 ll2 :
    ll1 `prefixes_of` ll2 →
    to_max_prefix_list_list ll2 ⋅ to_max_prefix_list_list ll1 ≡ to_max_prefix_list_list ll2.
  Proof.
    rewrite /prefixes /map_included /map_relation => H i. rewrite lookup_op.
    rewrite /to_max_prefix_list_list !fmap_map_seq !lookup_map_seq Nat.sub_0_r !list_lookup_fmap.
    rewrite !option_guard_True; [|lia..].
    move: (H i).
    case El1: (ll1 !! i) => [l1|]; case El2: (ll2 !! i) => [l2|]; inversion_clear 1; simplify_eq/=.
    - rewrite -Some_op. rewrite to_max_prefix_list_op_r; [done|by eexists].
    - rewrite right_id //.
    - done.
  Qed.

  Lemma max_prefix_list_list_included_includedN (mll1 mll2 : max_prefix_list_list A) :
    mll1 ≼ mll2 ↔ ∀ n, mll1 ≼{n} mll2.
  Proof.
    split; [intros; by apply: cmra_included_includedN|].
    intros Hincl. exists mll2. apply equiv_dist=> n.
    (* NOTE: [rewrite Hdist] fails. Maybe because it can't guess what [cmra] to
    use for [cmra_op_ne]? But then how does [rewrite (Hdist i)] work?? *)
    destruct (Hincl n) as [mll Hdist]. intros i.
    rewrite lookup_op (Hdist i). rewrite lookup_op assoc -core_id_dup. done.
  Qed.

  Local Lemma to_max_prefix_list_list_includedN_aux n ll1 ll2 :
    to_max_prefix_list_list ll1 ≼{n} to_max_prefix_list_list ll2 →
    map_included (λ l1 l2, l2 ≡{n}≡ l1 ++ drop (length l1) l2) ll1 ll2.
  Proof.
    rewrite lookup_includedN => H.
    rewrite /map_included /map_relation => i. move: {H}(H i).
    rewrite /to_max_prefix_list_list !fmap_map_seq.
    rewrite option_includedN_total=> -[|].
    - move=>/lookup_map_seq_None=> -[|]; [lia|].
      rewrite fmap_length /=. move=>/lookup_ge_None_2 => -> /=. by case_match.
    - move=> [?][?]. rewrite !lookup_map_seq_0.
      intros ((? & -> & ->)%list_lookup_fmap_inv & (? & -> & ->)%list_lookup_fmap_inv & ?).
      simpl. by apply max_prefix_list.to_max_prefix_list_includedN_aux.
  Qed.
  Lemma to_max_prefix_list_list_includedN n ll1 ll2 :
    to_max_prefix_list_list ll1 ≼{n} to_max_prefix_list_list ll2
    ↔ map_included (λ l1 l2, ∃ l, l2 ≡{n}≡ l1 ++ l) ll1 ll2.
  Proof.
    split.
    - intros H%to_max_prefix_list_list_includedN_aux i. move: {H}(H i).
      case El1: (ll1 !! i) => [l1|]; case El2: (ll2 !! i) => [l2|]; simpl; by eauto.
    - rewrite lookup_includedN => H i. move: {H}(H i).
      rewrite /to_max_prefix_list_list !fmap_map_seq !lookup_map_seq_0 !list_lookup_fmap.
      case El1: (ll1 !! i) => [l1|]; case El2: (ll2 !! i) => [l2|];
          simpl in *; [|done| |done]; intros.
      + by apply Some_includedN_total, to_max_prefix_list_includedN.
      + apply option_includedN_total. by left.
  Qed.
  Lemma to_max_prefix_list_list_included ll1 ll2 :
    to_max_prefix_list_list ll1 ≼ to_max_prefix_list_list ll2
    ↔ map_included (λ l1 l2, ∃ l, l2 ≡ l1 ++ l) ll1 ll2.
  Proof.
    split.
    - intros IN i.
      have {}IN: ∀ n, to_max_prefix_list_list ll1 ≼{n} to_max_prefix_list_list ll2.
      { intros n. by apply: cmra_included_includedN. (* NOTE: why does this work? *) }
      case El1: (ll1 !! i) => [l1|]; case El2: (ll2 !! i) => [l2|]; simpl; [ | |done|done].
      + eexists. apply equiv_dist=> n. specialize (IN n).
        move: (to_max_prefix_list_list_includedN_aux n ll1 ll2 IN) => INCL.
        move: (INCL i). rewrite El1 El2 //.
      + move: {IN}(IN 0). rewrite lookup_includedN => IN. move: {IN}(IN i).
        rewrite /to_max_prefix_list_list !fmap_map_seq !lookup_map_seq_0 !list_lookup_fmap.
        rewrite El1 El2 /=. rewrite option_includedN. naive_solver.
    - rewrite lookup_included => IN i. move: {IN}(IN i).
      rewrite /to_max_prefix_list_list !fmap_map_seq !lookup_map_seq_0 !list_lookup_fmap.
      case El1: (ll1 !! i) => [l1|]; case El2: (ll2 !! i) => [l2|];
          simpl in *; [ |done| |done]; intros.
      + by apply Some_included_total, to_max_prefix_list_included.
      + apply option_included_total. by left.
  Qed.

  Lemma to_max_prefix_list_list_included_L `{!LeibnizEquiv A} ll1 ll2 :
    to_max_prefix_list_list ll1 ≼ to_max_prefix_list_list ll2 ↔ ll1 `prefixes_of` ll2.
  Proof.
    rewrite to_max_prefix_list_list_included /prefixes /prefix.
    rewrite /map_included. apply map_relation_iff; naive_solver.
  Qed.

  Lemma max_prefix_list_list_local_update ll1 ll2 :
    ll1 `prefixes_of` ll2 →
    (to_max_prefix_list_list ll1, to_max_prefix_list_list ll1) ~l~>
      (to_max_prefix_list_list ll2, to_max_prefix_list_list ll2).
  Proof.
    intros P n oll V EQ. simpl in *. split.
    { apply to_max_prefix_list_list_validN. }
    intros i. move: {P}(P i) {V}(V i) {EQ}(EQ i). rewrite !lookup_opM.
    rewrite /to_max_prefix_list_list !fmap_map_seq !lookup_map_seq Nat.sub_0_r !list_lookup_fmap.
    rewrite !option_guard_True; [|lia..].
    destruct oll as [ll|]; simpl; last by rewrite !right_id.
    destruct (ll !! i) as [l|]; simpl; last by rewrite !right_id.
    destruct (ll1 !! i) as [l1|], (ll2 !! i) as [l2|]; simpl; [|done| |done].
    - rewrite -!Some_op. intros P V EQ%Some_dist_inj. f_equiv.
      move: (max_prefix_list_local_update l1 l2 P n (Some l)). naive_solver.
    - rewrite -!Some_op. intros _ _ EQ. symmetry in EQ. apply dist_None in EQ. done.
  Qed.
End max_prefix_list_list.

Definition mono_list_listR (A : ofe) : cmra  := authR (max_prefix_list_listUR A).
Definition mono_list_listUR (A : ofe) : ucmra  := authUR (max_prefix_list_listUR A).

Definition mono_list_list_auth {A : ofe} (q : dfrac) (l : list (list A)) : mono_list_listR A :=
  ●{q} (to_max_prefix_list_list l) ⋅ ◯ (to_max_prefix_list_list l).
Definition mono_list_list_lb {A : ofe} (l : list (list A)) : mono_list_listR A :=
  ◯ (to_max_prefix_list_list l).
Global Instance: Params (@mono_list_list_auth) 1 := {}.
Global Instance: Params (@mono_list_list_lb) 1 := {}.
#[global] Typeclasses Opaque mono_list_list_auth mono_list_list_lb.

Notation "●MLL dq l" := (mono_list_list_auth dq l) (at level 20, dq custom dfrac at level 1, format "●MLL dq l").
Notation "◯MLL l" := (mono_list_list_lb l) (at level 20).

Section mono_list_list.
  Context {A : ofe}.
  Implicit Types (l : list A) (q : frac) (dq : dfrac) (ll : list (list A)).

  (** Setoid properties *)
  Global Instance mono_list_list_auth_ne dq : NonExpansive (@mono_list_list_auth A dq).
  Proof. solve_proper. Qed.
  Global Instance mono_list_list_auth_proper dq : Proper ((≡) ==> (≡)) (@mono_list_list_auth A dq).
  Proof. solve_proper. Qed.
  Global Instance mono_list_list_lb_ne : NonExpansive (@mono_list_list_lb A).
  Proof. solve_proper. Qed.
  Global Instance mono_list_list_lb_proper : Proper ((≡) ==> (≡)) (@mono_list_list_lb A).
  Proof. solve_proper. Qed.

  Global Instance mono_list_list_lb_dist_inj n : Inj (dist n) (dist n) (@mono_list_list_lb A).
  Proof. rewrite /mono_list_list_lb. by intros ?? ?%(inj _)%(inj _). Qed.
  Global Instance mono_list_list_lb_inj : Inj (≡) (≡) (@mono_list_list_lb A).
  Proof. rewrite /mono_list_list_lb. by intros ?? ?%(inj _)%(inj _). Qed.

  (** * Operation *)
  Global Instance mono_list_list_lb_core_id ll : CoreId (◯MLL ll).
  Proof. rewrite /mono_list_list_lb. apply _. Qed.

  Lemma mono_list_list_lb_op_l ll1 ll2 : ll1 `prefixes_of` ll2 → ◯MLL ll1 ⋅ ◯MLL ll2 ≡ ◯MLL ll2.
  Proof. intros ?. by rewrite /mono_list_list_lb -auth_frag_op to_max_prefix_list_list_op_l. Qed.
  Lemma mono_list_list_lb_op_r ll1 ll2 : ll1 `prefixes_of` ll2 → ◯MLL ll2 ⋅ ◯MLL ll1 ≡ ◯MLL ll2.
  Proof. intros ?. by rewrite /mono_list_list_lb -auth_frag_op to_max_prefix_list_list_op_r. Qed.
  Lemma mono_list_list_auth_lb_op dq ll : ●MLL{dq} ll ≡ ●MLL{dq} ll ⋅ ◯MLL ll.
  Proof.
    by rewrite /mono_list_list_auth /mono_list_list_lb -!assoc -auth_frag_op -core_id_dup.
  Qed.
  Lemma mono_list_list_auth_dfrac_op dq1 dq2 ll :
    ●MLL{dq1 ⋅ dq2} ll ≡ ●MLL{dq1} ll ⋅ ●MLL{dq2} ll.
  Proof.
    rewrite /mono_list_list_auth auth_auth_dfrac_op.
    rewrite (comm _ (●{dq2} _)) -!assoc (assoc _ (◯ _)).
    by rewrite -core_id_dup (comm _ (◯ _)).
  Qed.

  Global Instance mono_list_list_lb_is_op ll : IsOp' (◯MLL ll) (◯MLL ll) (◯MLL ll).
  Proof. by rewrite /IsOp' /IsOp -core_id_dup. Qed.

  (** * Validity *)
  Lemma mono_list_list_auth_dfrac_validN n dq ll : ✓{n} (●MLL{dq} ll) ↔ ✓ dq.
  Proof.
    rewrite /mono_list_list_auth auth_both_dfrac_validN.
    naive_solver apply to_max_prefix_list_list_validN.
  Qed.

  Lemma mono_list_list_auth_validN n ll : ✓{n} (●MLL ll).
  Proof. by apply mono_list_list_auth_dfrac_validN. Qed.

  Lemma mono_list_list_auth_dfrac_valid dq ll : ✓ (●MLL{dq} ll) ↔ ✓ dq.
  Proof.
    rewrite /mono_list_list_auth auth_both_dfrac_valid.
    naive_solver apply to_max_prefix_list_list_valid.
  Qed.

  Lemma mono_list_list_auth_valid ll : ✓ (●MLL ll).
  Proof. by apply mono_list_list_auth_dfrac_valid. Qed.

  Lemma mono_list_list_both_dfrac_validN n dq ll1 ll2 :
    ✓{n} (●MLL{dq} ll1 ⋅ ◯MLL ll2) ↔ ✓dq ∧ map_included (λ l1 l2, ∃ l, l2 ≡{n}≡ l1 ++ l) ll2 ll1.
  Proof.
    rewrite /mono_list_list_auth /mono_list_list_lb -assoc
      -auth_frag_op auth_both_dfrac_validN -to_max_prefix_list_list_includedN.
    split.
    - intros [Hdfrac [Hincl _]]. split; [done|].
      (* NOTE: Can't [etrans]. "not a declared transitive relation". *)
      eapply (@transitivity (max_prefix_list_listR A) _ (cmra_includedN_trans n));
        [apply cmra_includedN_r|done].
    - intros [H1 H2]. split; [done|]; split; [|by apply to_max_prefix_list_list_validN].
      rewrite {2}(core_id_dup (to_max_prefix_list_list ll1)). by f_equiv.
  Qed.

  Lemma mono_list_list_both_validN n ll1 ll2 :
    ✓{n} (●MLL ll1 ⋅ ◯MLL ll2) ↔ map_included (λ l1 l2, ∃ l, l2 ≡{n}≡ l1 ++ l) ll2 ll1.
  Proof.
    rewrite /mono_list_list_auth /mono_list_list_lb -assoc
      -auth_frag_op auth_both_validN -to_max_prefix_list_list_includedN.
    split.
    - intros [Hincl _].
      (* NOTE: Can't [etrans]. "not a declared transitive relation". *)
      eapply (@transitivity (max_prefix_list_listR A) _ (cmra_includedN_trans n));
        [apply cmra_includedN_r|done].
    - intros. split; [|by apply to_max_prefix_list_list_validN].
      rewrite {2}(core_id_dup (to_max_prefix_list_list ll1)). by f_equiv.
  Qed.

  Lemma mono_list_list_both_dfrac_valid dq ll1 ll2 :
    ✓ (●MLL{dq} ll1 ⋅ ◯MLL ll2) ↔ ✓ dq ∧ map_included (λ l1 l2, ∃ l, l2 ≡ l1 ++ l) ll2 ll1.
  Proof.
    rewrite /mono_list_list_auth /mono_list_list_lb -assoc -auth_frag_op
      auth_both_dfrac_valid -max_prefix_list_list_included_includedN
      -to_max_prefix_list_list_included.
    split.
    - intros [Hdfrac [Hincl _]]. split; [done|].
      (* NOTE: Can't [etrans]. "not a declared transitive relation". *)
      eapply (@transitivity (max_prefix_list_listR A) _ cmra_included_trans);
        [apply cmra_included_r|done].
    - intros [H1 H2]. split; [done|]; split; [|by apply to_max_prefix_list_list_valid].
      (* NOTE: can't infer cmra in [cmra_included_proper]? *)
      (* rewrite {2}(core_id_dup (to_max_prefix_list_list ll1)). by f_equiv. *)
      move: H2. rewrite !lookup_included => H2 i. move: {H2}(H2 i).
      rewrite lookup_op.
      rewrite /to_max_prefix_list_list !fmap_map_seq !lookup_map_seq_0 !list_lookup_fmap.
      destruct (ll1 !! i) as [l1|], (ll2 !! i) as [l2|]; simpl; [|done..].
      move=> /Some_included_total H. rewrite -Some_op Some_included_total.
      rewrite {2}(core_id_dup (to_max_prefix_list l1)). by f_equiv.
  Qed.

  Lemma mono_list_list_both_valid ll1 ll2 :
    ✓ (●MLL ll1 ⋅ ◯MLL ll2) ↔ map_included (λ l1 l2, ∃ l, l2 ≡ l1 ++ l) ll2 ll1.
  Proof.
    rewrite /mono_list_list_auth /mono_list_list_lb -assoc -auth_frag_op
      auth_both_valid -max_prefix_list_list_included_includedN
      -to_max_prefix_list_list_included.
    split.
    - intros [Hincl _].
      (* NOTE: Can't [etrans]. "not a declared transitive relation". *)
      eapply (@transitivity (max_prefix_list_listR A) _ cmra_included_trans);
        [apply cmra_included_r|done].
    - intros. split; [|by apply to_max_prefix_list_list_valid].
      (* NOTE: can't infer cmra in [cmra_included_proper]? *)
      (* rewrite {2}(core_id_dup (to_max_prefix_list_list ll1)). by f_equiv. *)
      move: H. rewrite !lookup_included => H i. move: {H}(H i).
      rewrite lookup_op.
      rewrite /to_max_prefix_list_list !fmap_map_seq !lookup_map_seq_0 !list_lookup_fmap.
      destruct (ll1 !! i) as [l1|], (ll2 !! i) as [l2|]; simpl; [|done..].
      move=> /Some_included_total H. rewrite -Some_op Some_included_total.
      rewrite {2}(core_id_dup (to_max_prefix_list l1)). by f_equiv.
  Qed.

  Lemma mono_list_list_both_dfrac_valid_L `{!LeibnizEquiv A} dq ll1 ll2 :
    ✓ (●MLL{dq} ll1 ⋅ ◯MLL ll2) ↔ ✓ dq ∧ ll2 `prefixes_of` ll1.
  Proof.
    rewrite mono_list_list_both_dfrac_valid.
    assert (map_included (λ l1 l2, ∃ l, l2 ≡ l1 ++ l) ll2 ll1 ↔ ll2 `prefixes_of` ll1).
    { apply map_relation_iff; [|done..]. rewrite /prefix. naive_solver. }
    naive_solver.
  Qed.

  Lemma mono_list_list_both_valid_L `{!LeibnizEquiv A} ll1 ll2 :
    ✓ (●MLL ll1 ⋅ ◯MLL ll2) ↔ ll2 `prefixes_of` ll1.
  Proof.
    rewrite mono_list_list_both_valid. apply map_relation_iff; [|done..].
    rewrite /prefix. naive_solver.
  Qed.

  Lemma mono_list_list_included dq ll : ◯MLL ll ≼ ●MLL{dq} ll.
  Proof. apply cmra_included_r. Qed.

  (** * Update *)
  Lemma mono_list_list_update {ll1} ll2 : ll1 `prefixes_of` ll2 → ●MLL ll1 ~~> ●MLL ll2.
  Proof. intros ?. by apply auth_update, max_prefix_list_list_local_update. Qed.

End mono_list_list.
