From stdpp Require Import namespaces.
From iris.algebra Require Import coPset auth gmap excl.
From iris.bi Require Import big_op.
From iris.proofmode Require Import proofmode.

From gpfsl.logic Require Import proofmode.
From gpfsl.gps Require Import surface_iSP surface_iPP protocols escrows.
From gpfsl.logic Require Import repeat_loop new_delete.

From gpfsl.examples Require Import nat_tokens.
From gpfsl.examples.lock Require Import code_ticket_lock.

Require Import iris.prelude.options.

Local Notation ns := 0%nat (only parsing).
Local Notation tc := 1%nat (only parsing).

(** Formalization of the bounded ticket-lock example.
    The proof is simplified by using single-writer protocols and
      a simpler ticket tracker. **)
(* Description of this proof can be found in Appendix E of the iGPS paper.
   URL: http://plv.mpi-sws.org/igps/igps-full.pdf *)

Local Notation gmapNOpN := (gmap nat (excl $ option nat)).
Local Notation Excl2 t := (Excl' (Some t)).
Local Notation ExclN := (Excl' None).
Notation "'{[' m '<-' M | E ']}'" := (filter (λ m, E) M)
  (at level 1) : stdpp_scope.

Section Arith.
Implicit Types (M: gmapNOpN) (i n t : nat).

Local Instance Mtkt_dec M i n: Decision (∃ t, M !! i = Excl2 t ∧ n ≤ t).
Proof.
  case (M !! i).
  - move => [[t|]|].
    + case (decide (n ≤ t)) => [?|?].
      * left. exists t. done.
      * right. by move => [? [[<-] ?]].
    + right. by move => [? [? ]].
    + right. by move => [? [? ]].
  - right. by move => [? [? ]].
Qed.

Definition Waiting M n : gset nat :=
  filter (λ i, ∃ t, M !! i = Excl2 t ∧ n ≤ t) (dom M).
Definition Ws M n : nat := size (Waiting M n).

Definition ns_tkt_bound M t n : Prop :=
  n ≤ t ∧ t ≤ n + Ws M n
  ∧ ∀ (i k: nat), M !! i = Excl2 k →
      (k < t) ∧ ∀ (j: nat), M !! j = Excl2 k → i = j.

Lemma Waiting_ns_nonupdate M n t i (ot: option nat)
  (Eq: M !! i = Excl' ot)
  (Le : n ≤ t):
  {[i]} ∪ Waiting M n  ⊆ Waiting (<[i:= Excl $ Some t]> M) n.
Proof.
  move => j. case (decide (j = i)) => [->|NEq].
  - move => _. apply set_unfold_2. split.
    + exists t. rewrite lookup_insert. split; [auto|lia].
    + auto.
  - move => /elem_of_union [/elem_of_singleton //|].
    apply set_unfold_2.
    setoid_rewrite lookup_insert_ne; last done.
    move => [? ?]. split; auto.
Qed.

Lemma Waiting_subseteq_update M n t t0 i
  (Eq: M !! i = Excl2 t0) (Le : n ≤ t0):
  Waiting (<[i:=Excl $ Some t]> M) (S t0) ⊆  Waiting M n.
Proof.
  move => j. apply set_unfold_2.
  case (decide (j = i)) => [->|NEq].
  - split; [by eexists|apply elem_of_dom; by eexists].
  - move => [[t1 [ ]]].
    rewrite lookup_insert_ne; last by auto.
    move => ? ? [? //|?]. split; last done. exists t1. split; [done|lia].
Qed.

Local Instance Mtkt_dec2 M i n t0 :
  Decision (∃ (t: nat), M !! i = Excl2 t ∧ n ≤ t ∧ t < t0).
Proof.
  case (M !! i).
  - move => [[t|]|].
    + case (decide (n ≤ t)) => [?|?];
      case (decide (t < t0)) => [?|?]; [by left; eexists|..];
      right; by move => [? [[<-] [? ?]]].
    + right. by move => [? [? ]].
    + right. by move => [? [? ]].
  - right. by move => [? [? ]].
Qed.

Definition Mtkt_range M n t0 : gset nat
  := filter (λ i, ∃ t, M !! i = Excl2 t ∧ n ≤ t ∧ t < t0) (dom M).
Definition Mtkt_at M n : gset nat := Mtkt_range M n (S n).

Lemma Waiting_diff M n t t0 i
  (Eq: M !! i = Excl2 t0)
  (Inj : ∀ i k : nat, M !! i = Excl2 k → k < t
          ∧ (∀ j : nat, M !! j = Excl2 k → i = j)):
  Waiting M n ∖ Waiting (<[i:=Excl $ Some t]> M) (S t0)
    ⊆  Mtkt_range M n t0.
Proof.
  move => j.
  apply set_unfold_2.
  destruct (Inj _ _ Eq) as [Le Inj2].
  move => [[[t1 [Eq1 Le1]] E3] E2]. split; last done.
  exists t1. repeat split; [auto|auto|].
  case (decide (t1 < t0)) => [//|/Z.nlt_ge Le3]. exfalso.
  apply E2. split; last by auto.
  case (decide (j = i)) => [->|NEq].
  - exists t. rewrite lookup_insert. split; [done|lia].
  - exists t1. rewrite lookup_insert_ne; last done. split; first done.
    apply Zle_lt_or_eq in Le3 as [|Eq3]; first lia.
    apply Nat2Z.inj_iff in Eq3. subst t1. by apply Inj2 in Eq1.
Qed.

Lemma Mtkt_split M t1 t2 t3
  (Le1: t1 ≤ t2) (Le2: t2 ≤ t3):
  Mtkt_range M t1 t3 ⊆ Mtkt_range M t1 t2 ∪ Mtkt_range M t2 t3.
Proof.
  intros j. apply set_unfold_2.
  move => [[t [Eq [Le3 Le4]]] InD].
  case (decide (t2 ≤ t)) => [Le5|/Z.nle_gt Le6]; [right|left];
    (split; last auto); by eexists.
Qed.

Local Instance Mtkt_dec3 M t :
  Decision (∃ i, i ∈ dom M ∧ M !! i = Excl2 t).
Proof.
  apply set_Exists_dec. intro j.
  case (M !! j); last by right.
  move => [[k|]|]; [|by right|by right].
  case (decide (k = t)) => [->|NEq]; by [left|right; move => []].
Qed.

Lemma Mtkt_singleton M t
  (Inj : ∀ i k : nat, M !! i = Excl2 k →
          (∀ j : nat, M !! j = Excl2 k → i = j)):
  size (Mtkt_range M t (S t)) ≤ 1.
Proof.
  case (decide (∃ i, i ∈ dom M  ∧ M !! i = Excl2 t)).
  - move => [i [InD Eq]].
    etrans;
      [instantiate (1:= size ({[i]}: gset nat))|by rewrite size_singleton].
    apply inj_le, subseteq_size. apply set_unfold_2.
    move => j [[t' [? [? ?]]] _]. apply (Inj _ t); last auto.
    rewrite (_: (t = t')%nat); first done. lia.
  - move => NEq. etrans; [instantiate (1:= 0%nat)|done].
    apply inj_le, Nat.le_0_r, size_empty_iff. apply set_unfold_2.
    move => j [[t' [Eq [? ?]]] ?]. apply NEq.
    exists j. split; first auto. rewrite Eq.
    rewrite (_: (t = t')%nat); [done|lia].
Qed.

Lemma Waiting_bound M n t0
  (Inj : ∀ i k : nat, M !! i = Excl2 k →
          (∀ j : nat, M !! j = Excl2 k → i = j))
  (Le : n ≤ t0):
  n + size (Mtkt_range M n t0) ≤ t0.
Proof.
  induction t0 as [|t0 IHt0].
  - rewrite (_: n = 0%nat); last lia.
    apply Nat2Z.inj_le, Nat.le_0_r, size_empty_iff. apply set_unfold_2.
    move => ? [[? [_ [? ?]]] _]. lia.
  - rewrite Nat2Z.inj_succ in Le. apply Z.le_succ_r in Le as [Le|Eq].
    + assert (LeS: t0 ≤ S t0) by lia.
      assert (LeSub:= subseteq_size _ _ (Mtkt_split M n t0 (S t0) Le LeS)).
      etrans.
      * instantiate (1:= n +
                        size (Mtkt_range M n t0 ∪ Mtkt_range M t0 (S t0))).
        lia.
      * rewrite size_union_alt.
        rewrite Nat2Z.inj_succ Nat2Z.inj_add Zplus_assoc.
        apply Z.add_le_mono; first by apply IHt0.
        etrans.
        { instantiate (1:=  size (Mtkt_range M t0 (S t0))).
          apply inj_le, subseteq_size. set_solver. }
        { by apply Mtkt_singleton. }
    + rewrite Nat2Z.inj_succ -Eq.
      rewrite {2}(_: Z.of_nat n = n + 0%nat); last lia.
      apply Zplus_le_compat_l, inj_le, Nat.le_0_r, size_empty_iff.
      apply set_unfold_2. move => ? [[? [_ [? ?]]] _]. lia.
Qed.

Lemma Waiting_dom_size C M
  (DS : dom M ≡ set_seq 0 (Pos.to_nat C)):
  Z.pos C = size (dom M).
Proof.
  by rewrite (set_size_proper _ _ DS) -positive_nat_Z size_set_seq.
Qed.

Lemma Waiting_size_le C M n
  (DS: dom M ≡ set_seq 0 (Pos.to_nat C)):
  Ws M n ≤ Z.pos C.
Proof.
  rewrite (_: Z.pos C = size (dom M)).
  - apply inj_le, subseteq_size. set_solver.
  - by apply Waiting_dom_size.
Qed.

Lemma Waiting_size_lt C M n i (ot: option nat)
  (DS: dom M ≡ set_seq 0 (Pos.to_nat C))
  (Ini: M !! i = Excl' ot) (Lt: ot = None ∨ ∃ t, ot = Some t ∧ t < n):
  Ws M n < Z.pos C.
Proof.
  rewrite (Waiting_dom_size C M); last done.
  apply inj_lt, subset_size. apply set_unfold_2.
  split.
  - move => j [_ ?] //.
  - move => /(_ i) Eq. destruct Eq as [[t' [Eq ?]] _].
    + apply elem_of_dom. by eexists.
    + rewrite Eq in Ini.
      destruct Lt as [?|[? [? ?]]]; subst; inversion Ini. lia.
Qed.

Lemma ns_inj_insert M t i
 (FA: ∀ i0 k : nat,
     M !! i0 = Excl2 k → k < t ∧ (∀ j : nat, M !! j = Excl2 k → i0 = j)):
 ∀ i0 k : nat,
  <[i:=Excl (Some t)]> M !! i0 = Excl2 k
  → k < (t + 1)%nat
    ∧ (∀ j : nat, <[i:=Excl (Some t)]> M !! j = Excl2 k → i0 = j).
Proof.
  move => j k. case (decide (j = i)) => [->|NEq].
  - rewrite lookup_insert. move => [<-].
    split; first lia.
    move => j'. case (decide (j' = i)) => [-> //| NEq].
    rewrite lookup_insert_ne; last done.
    move => /FA [tLe _]. lia.
  - rewrite lookup_insert_ne; last done.
    move => Eqk. destruct (FA _ _ Eqk) as (kLe & kInj).
    split; first lia.
    move => j'. case (decide (j' = i)) => [->| NEq2].
    + rewrite lookup_insert. move => [?]. subst k. lia.
    + rewrite lookup_insert_ne; [apply kInj|done].
Qed.

Lemma ns_tkt_bound_update C M t n i (ot : option nat)
  (Ini: M !! i = Excl' ot) (BO: ns_tkt_bound M t n)
  (DS: dom M ≡ set_seq 0 (Pos.to_nat C)):
  ∃ (n': nat),
    (ot = None → n' = n) ∧
    (∀ t0, ot = Some t0 → n' = S t0 ∨ n' = n) ∧ t < n' + Z.pos C
    ∧ ns_tkt_bound (<[i:= Excl (Some t)]> M) (t+1) n'.
Proof.
  destruct BO as (LE1 & LE2 & FA).
  destruct ot as [t0|].
  - destruct (FA _ _ Ini) as (iLe & Inj).
    case (decide (n ≤ t0)) => [Le|/Z.nle_gt Gt].
    + exists (S t0). split; first done.
      split; first (move => ? [?]; subst; by left).
      split; [|split; first lia; split].
      * eapply Z.le_lt_trans; first by apply LE2.
        apply Z.add_lt_le_mono; [lia|]. by apply Waiting_size_le.
      * rewrite Nat2Z.inj_succ Nat2Z.inj_add Zplus_assoc_reverse
                (Z.add_comm 1) Zplus_assoc.
        apply Zplus_le_compat_r. etrans; first apply LE2.
        assert (Eqs :=
        subseteq_union_1 _ _ (Waiting_subseteq_update _ _ t _ _ Ini Le)).
        rewrite /Ws -(set_size_proper _ _ Eqs) size_union_alt.
        rewrite Nat2Z.inj_add (Z.add_comm (size _)) Zplus_assoc.
        apply Zplus_le_compat_r. etrans.
        { instantiate (1:= n + size (Mtkt_range M n t0)).
          apply Zplus_le_compat_l, Nat2Z.inj_le, subseteq_size.
          apply Waiting_diff; auto. }
        { apply Waiting_bound; [naive_solver|done]. }
      * by apply ns_inj_insert.
    + exists n. split; first done.
      split; first by right.
      split; [|split; first lia; split].
      * eapply Z.le_lt_trans; first by apply LE2. apply Zplus_lt_compat_l.
        apply (Waiting_size_lt _ _ n i (Some t0) DS);
          [done|right;by eexists].
      * etrans; last first.
        { instantiate (1:= n + size ({[i]} ∪ Waiting M n)).
          apply Zplus_le_compat_l.
          assert (Hle := subseteq_size _ _
                  (Waiting_ns_nonupdate M n t _ _ Ini LE1)).
          by apply inj_le in Hle. }
        { rewrite size_union ; last first.
          { rewrite disjoint_singleton_l /Waiting elem_of_filter.
            rewrite Ini. move => [[? [[<-] ?]] _]. lia. }
          rewrite Nat2Z.inj_add size_singleton Nat2Z.inj_add
                  (Z.add_comm 1) Zplus_assoc.
          by apply Zplus_le_compat_r. }
      * by apply ns_inj_insert.
  - exists n. split; [done|split]; first by right.
    split; [|split; first lia; split].
    * eapply Z.le_lt_trans; first by apply LE2. apply Zplus_lt_compat_l.
      apply (Waiting_size_lt _ _ n i None DS); [done|by left].
    * etrans; last first.
      { instantiate (1:= n + size ({[i]} ∪ Waiting M n)).
        apply Zplus_le_compat_l.
        assert (Hle := subseteq_size _ _
                (Waiting_ns_nonupdate M n t _ _ Ini LE1)).
        by apply inj_le in Hle. }
      { rewrite size_union ; last first.
        { rewrite disjoint_singleton_l /Waiting elem_of_filter.
          rewrite Ini. move => [[? [//]]]. }
        rewrite Nat2Z.inj_add size_singleton Nat2Z.inj_add
                (Z.add_comm 1) Zplus_assoc.
        by apply Zplus_le_compat_r. }
    * by apply ns_inj_insert.
Qed.
End Arith.


Definition ticketLockR
  := prodUR (coPset_disjUR) (authUR (gmapUR nat (exclR (optionO natO)))).

Class tklG Σ := TklG {
  tkl_tokG : inG Σ ticketLockR ;
  tkl_ns_gps_protG : gpsG Σ natProtocol ;
  tkl_tc_gps_protG : gpsG Σ unitProtocol
}.
Local Existing Instances tkl_tokG tkl_ns_gps_protG tkl_tc_gps_protG.

Definition tklΣ : gFunctors
  := #[GFunctor (constRF ticketLockR); gpsΣ natProtocol; gpsΣ unitProtocol].

Global Instance subG_tklΣ {Σ} : subG tklΣ Σ → tklG Σ.
Proof. solve_inG. Qed.

(* Namespace for the invariant *)
Definition tktlckN (q: loc) := nroot .@ "ticketlockN" .@ q.

Section Interp.
Context `{!noprolG Σ, tikG: !tklG Σ, !atomicG Σ} (C: positive).
Implicit Types (γ: gname) (i n : nat) (M: gmapNOpN) (P: vProp Σ).

Local Notation iProp := (iProp Σ).
Local Notation vProp := (vProp Σ).

Definition Perm γ t : vProp := ⎡ own γ (CoPset {[Pos.of_succ_nat t]} , ε) ⎤%I.
Definition Perms γ t : vProp := ⎡ own γ (CoPset $ coPset_from_ex t, ε) ⎤%I.
Definition MyTkt γ i (t: option nat) : vProp := ⎡ own γ (ε, ◯ {[i := Excl t]}) ⎤%I.
Definition AllTkts γ M : vProp := ⎡ own γ (ε, ● M) ⎤%I.

Definition map_excl (S: gset nat) (t : option nat) := gset_to_gmap (Excl t) S.
Definition setC: gset nat := set_seq 0 (Pos.to_nat C).
Definition firstMap := map_excl setC None.

Definition ES (P : vProp) (F : interpO Σ natProtocol) l γ γn n : vProp :=
  (∀ (t: nat), ⌜t ≤ n⌝ →
    [es Perm γ t ⇝
      (P ∗ ∃ ti vi, GPS_iSP_Writer (tktlckN l) F (F false) l ti t vi γn)])%I.
Global Instance ES_proper :
  Proper ((≡) ==> (≡) ==> (=) ==> (=) ==> (=) ==> (=) ==> (≡)) ES.
Proof.
  intros ?? Eq1 ?? Eq2 ????????????. subst.
  apply bi.forall_proper => ?.
  apply bi.impl_proper; [done|].
  apply escrow_proper; [done|].
  apply bi.sep_proper; [done|].
  repeat (apply bi.exist_proper => ?).
  by apply GPS_iSP_Writer_proper.
Qed.

Definition NSP' P γ : _ → interpO Σ natProtocol :=
  (fun F _ l γn _ n z => ⌜z = #(n `mod` (Z.pos C))⌝ ∗ ES P F l γ γn n)%I.
Global Instance NSP'_contractive P γ: Contractive (NSP' P γ).
Proof.
  intros n ?? H ??????.
  apply bi.sep_ne; [done|].
  apply bi.forall_ne =>? /=.
  apply bi.impl_ne; [done|].
  apply escrow_ne; [done|].
  apply bi.sep_ne; [done|].
  repeat (apply bi.exist_ne => ?).
  apply GPS_iSP_Writer_contractive; [done|].
  dist_later_fin_intro. eapply H; si_solver.
Qed.

Definition NSP P γ : interpO Σ natProtocol := fixpoint (NSP' P γ).

Global Instance NSP_persistent P γ b l γn tn n v :
  Persistent (NSP P γ b l γn tn n v).
Proof. rewrite /NSP (fixpoint_unfold (NSP' P γ) _ _ _ _ _ _). by apply _. Qed.

Definition TCP P γ γn (x: loc) : interpO Σ unitProtocol :=
  λ b _ _ _ _ y,
    (∃ (t: nat), ⌜y = #(t `mod` Z.pos C)⌝ ∧
    if b
    then (∃ n M, AllTkts γ M ∗ Perms γ t
          ∗ ⌜dom M ≡ set_seq 0 (Pos.to_nat C) ∧ ns_tkt_bound M t n⌝
          ∗ ∃ ti vi,
            GPS_iSP_Reader (tktlckN x) (NSP P γ) (NSP P γ false)
                           (x >> ns) ti n vi γn)
    else True)%I.

(** Permission needed to acquire a lock, by first acquire a ticket and then wait
  to be served *)
(* TODO: it is possible to break the [lock] function into two functions:
  first [acquire_ticket] and then [try_lock], so that the client can choose how
  to wait. *)
Definition MayAcquire P (x: loc): vProp :=
  (* This permission has last been used to acquire the lock [ot] *)
  (∃ γn γ i ot, MyTkt γ i ot
    ∗ (∃ t1 v1 γ1, GPS_iPP (tktlckN x) (TCP P γ γn x) (x >> tc) t1 () v1 γ1)
    (* If [ot] is [Some t], it means that the permission has last been used to
      acquire the lock with the ticket [t], and the lock has been released.
      The proof that the lock has been released is the fact that this permission
      has observed the increment to [S t] of the now-serving counter.
      This proof will be published to the ticket counter protocol TCP when
      the permission is used next time to acquire a new ticket. For such a
      publication, the FAI in [lock] needs to be 'release'. *)
    ∗ ∀ t, ⌜ot = Some t⌝ → ∃ t2 v2,
        GPS_iSP_Reader (tktlckN x) (NSP P γ) (NSP P γ false) (x >> ns) t2 (S t) v2 γn)%I.

(** Permission needed to release the acquired lock *)
Definition MayRelease P (x: loc): vProp :=
  (∃ γn γ i t, MyTkt γ i (Some t)
    ∗ (∃ t1 v1 γ1, GPS_iPP (tktlckN x) (TCP P γ γn x) (x >> tc) t1 () v1 γ1)
    ∗ (∃ t2 v2, GPS_iSP_Writer (tktlckN x) (NSP P γ) (NSP P γ false)
                                  (x >> ns) t2 t v2 γn))%I.

End Interp.

Section prot.
Context `{!noprolG Σ, tikG: !tklG Σ, !atomicG Σ} (C: positive).
Implicit Types (γ: gname) (i t n : nat) (M: gmapNOpN).

Local Notation iProp := (iProp Σ).
Local Notation vProp := (vProp Σ).

Lemma Perm_exclusive γ t: Perm γ t ∗ Perm γ t ⊢ False.
Proof.
  rewrite -embed_sep -own_op -pair_op own_valid.
  iDestruct 1 as %[Valid _]. exfalso.
  apply coPset_disj_valid_op, disjoint_singleton_l in Valid.
  by apply Valid, elem_of_singleton.
Qed.

Lemma Perms_get γ t :
  Perms γ t ⊢ Perm γ t ∗ Perms γ (S t).
Proof.
  rewrite -embed_sep -own_op -pair_op coPset_disj_union;
    [|by apply coPset_from_disjoint].
  by rewrite -coPset_from_insert left_id.
Qed.

Lemma MyAll_coherent γ i (t: option nat) M:
  AllTkts γ M ∗ MyTkt γ i t ⊢ ⌜M !! i = Excl' t⌝.
Proof.
  rewrite -embed_sep -own_op -pair_op own_valid.
  iDestruct 1 as %[_ [Incl Valid]%auth_both_valid_discrete].
  iPureIntro.
  apply singleton_included_exclusive_l in Incl; [|apply _|done].
  by apply leibniz_equiv_iff in Incl.
Qed.

Lemma MyTkt_get γ i (t t' : option nat) M:
  AllTkts γ M ∗ MyTkt γ i t ==∗ AllTkts γ (<[i := Excl t']> M) ∗ MyTkt γ i t'.
Proof.
  iIntros "Own".
  iDestruct (MyAll_coherent with "Own") as %Eq.
  rewrite -!embed_sep -!own_op -!pair_op.
  iMod (own_update with "Own"); last iAssumption.
  apply prod_update => /=; [done|].
  apply auth_update.
  apply: singleton_local_update; [eauto| exact: exclusive_local_update].
Qed.

Lemma Tkt_set_alloc γ j n (t: option nat):
   ⎡ own γ (ε, ◯ map_excl (set_seq j n) t) ⎤
   ⊢ [∗ set] i ∈ set_seq j n, MyTkt γ i t.
Proof.
  revert j. induction n as [ |n IHn] => j /=; iIntros "MyTkts".
  - by rewrite big_sepS_empty.
  - rewrite big_sepS_insert; last first.
    { move => /elem_of_set_seq [Le _]. lia. }
    rewrite /map_excl gset_to_gmap_union_singleton insert_singleton_op;
      last first.
    { apply lookup_gset_to_gmap_None. move => /elem_of_set_seq [Le _]. lia. }
    iDestruct "MyTkts" as "[$ MyTkts]".
    by iApply IHn.
Qed.

Lemma Tkt_ghost_alloc :
  ⊢ |==> ∃ γ,
    Perms γ 0 ∗ AllTkts γ (firstMap C) ∗ [∗ set] i ∈ (setC C), MyTkt γ i None.
Proof.
  iMod (own_alloc (CoPset $ coPset_from_ex 0, (● (firstMap C) ⋅ ◯ (firstMap C))))
    as (γ) "Own".
  { split; first done. apply auth_both_valid_discrete. split; [done|].
    move => i. destruct (firstMap C !! i) eqn:Eq; last by rewrite Eq.
    rewrite Eq. by move :Eq => /lookup_gset_to_gmap_Some [_ <-]. }
  iExists γ. rewrite pair_split.
  iDestruct "Own" as "[$ [$ MyTkts]]". iModIntro.
  rewrite /firstMap /setC. by iApply Tkt_set_alloc.
Qed.

Lemma NSP_impl P γ b1 b2 x γ1 (t1: time) s1 v1 :
  NSP C P γ b1 x γ1 t1 s1 v1 -∗ NSP C P γ b2 x γ1 t1 s1 v1.
Proof.
  rewrite /NSP 2!(fixpoint_unfold (NSP' C P γ) _ _ _ _ _ _).
  by iDestruct 1 as "[$ $]".
Qed.

Lemma TCP_comparable P γ γn x b y γ1 (t1 : time) s1 v1 (n : Z):
  TCP C P γ γn x b y γ1 t1 s1 v1 -∗ ⌜∃ vl : lit, v1 = #vl ∧ lit_comparable n vl⌝.
Proof.
  iDestruct 1 as (t Eq) "_". subst v1. iPureIntro.
  eexists. split; [done|]. constructor.
Qed.

Lemma TCP_duplicable P γ γn x y γ1 (t1 : time) s1 v1:
  TCP C P γ γn x true y γ1 t1 s1 v1 -∗ TCP C P γ γn x false y γ1 t1 s1 v1.
Proof. iDestruct 1 as (t Eq) "_". by iExists t. Qed.

End prot.

Section proof.
Context `{!noprolG Σ, tikG: !tklG Σ, !atomicG Σ} (C: positive).
Implicit Types (γ: gname) (i n : nat) (M: gmapNOpN) (x: loc) (P: vProp Σ).

Local Notation iProp := (iProp Σ).
Local Notation vProp := (vProp Σ).

Lemma new_lock_spec P tid :
  {{{ ▷ P }}}
      new_lock [] @ tid; ⊤
  {{{ (x: loc), RET #x; [∗ set] _ ∈ (setC C), MayAcquire C P x }}}.
Proof.
  iIntros (Φ) "P Post".
  wp_lam.
  (* allocate *)
  wp_apply wp_new; [done|lia|done|].
  iIntros (x) "([H†|%] & oLs & Hm)"; [|done].
  rewrite own_loc_na_vec_cons own_loc_na_vec_singleton.
  iDestruct "oLs" as "[oNS oTC]".

  wp_let.
  (* initialize now-serving counter *)
  iMod (Tkt_ghost_alloc C) as (γ) "(Perms & AllTkts & MyTkts)".
  wp_op. rewrite shift_0. wp_write.
  iMod (GPS_iSP_Init_strong_inv (tktlckN x) (NSP C P γ) (NSP C P γ false)
           (λ t1 γ1, True)%I _ O
          with "oNS [P]") as (γn t1) "[NSR _]"; [done|..].
  { iIntros (t1 γn) "oW". iSplitR ""; [|done].
    iMod (escrow_alloc (Perm γ O)
           (P ∗ ∃ ti vi, GPS_iSP_Writer (tktlckN x) (NSP C P γ)
                                        (NSP C P γ false) x ti O vi γn)%I
            with "[$P oW]") as "#ES"; [solve_ndisj|..].
    { iNext. by iExists _, _. }
    iIntros "!>".
    rewrite {3}/NSP (fixpoint_unfold (NSP' C P γ) _ _ _ _ _ _).
    iNext. iSplit; [done|].
    iIntros (t ?). have ? : t = O by lia. by subst t. }

  (* initialize ticket counter *)
  wp_op. iApply wp_fupd. wp_write.
  iMod (GPS_iPP_Init (tktlckN x) (TCP C P γ γn x) _ ()
          with "oTC [Perms AllTkts NSR]") as (γ2 t2) "#TCP".
  { iIntros (t2 γ2) "!>". iExists O. iSplit; [done|].
    iExists O, (firstMap C). iFrame "Perms AllTkts".
    iSplit.
    - iPureIntro. split; last split; [|done|].
      + intros i. rewrite elem_of_dom. split.
        * move => [e /lookup_gset_to_gmap_Some [//]].
        * move => In. exists (Excl None). by apply lookup_gset_to_gmap_Some.
      + split; [lia|].
        move => ? ? /lookup_gset_to_gmap_Some [_ //].
    - rewrite shift_0. by iExists _, _. }

  iIntros "!>". iApply "Post". (** leaking freeable .. *)
  iApply (big_sepS_impl with "MyTkts").
  iIntros "!>" (i Ini) "Tkt".
  iExists γn, γ, i, None. iFrame "Tkt".
  iSplitL ""; [by iExists _,_,_|by iIntros (??)].
Qed.

Lemma lock_spec P x tid :
  {{{ MayAcquire C P x }}}
    lock C [ #x] @ tid; ⊤
  {{{ RET #true; P ∗ MayRelease C P x }}}.
Proof.
  iIntros (Φ) "MAcq Post".
  iDestruct "MAcq" as (γn γ i ot) "(Tkt & #TCP & #NS)".
  iDestruct "TCP" as (t1 v1 γ1) "TCP".

  wp_lam.
  (* fetch-and-add to acquire a ticket *)
  wp_bind (FAIm _ _)%E. wp_op.
  iLöb as "IH".
  wp_lam.
  (* read *)
  wp_apply (GPS_iPP_Read _ _ (λ _ _ y, ∃ ti : nat, ⌜y = #(ti `mod` Z.pos C)⌝)%I
              with "[$TCP]"); [solve_ndisj|done|done|by left| |].
  { iIntros "!>" (t' s' v' Lt') "!>". iSplit.
    - iDestruct 1 as (t) "[#Eq _]". iModIntro.
      iSplit; iExists t; by iFrame "Eq".
    - iDestruct 1 as (t) "[#Eq F]". iSplitR ""; iExists t; by iFrame "Eq". }
  iIntros (t' [] v') "(_ & TCP' & %t & ->)".
  wp_pures.
  rewrite Z.add_mod_idemp_l; [|lia].

  (* CAS *)

  set P' : vProp := MyTkt γ i ot.
  set Q' : time → unitProtocol → vProp :=
    (λ _ _, ∃ (t0 n0: nat), ⌜t0 < n0 + Z.pos C ∧ t `mod` Z.pos C = t0 `mod` Z.pos C⌝
              ∗ MyTkt γ i (Some t0) ∗ Perm γ t0
              ∗ (∃ t2 v2,
                  GPS_iSP_Reader (tktlckN x) (NSP C P γ) (NSP C P γ false)
                                 (x >> 0) t2 n0 v2 γn))%I.
  wp_apply (GPS_iPP_CAS_int_simple _ _ _ _ _ _ _
              (t `mod` Z.pos C) #((t + 1) `mod` Z.pos C) _ _
              P' Q'
              (λ t1 s1, TCP C P γ γn x false (x >> 1) γ1 t1 s1 #(t `mod` Z.pos C))
              (λ t1 s1, TCP C P γ γn x true (x >> 1) γ1 t1 s1 #(t `mod` Z.pos C))
              (λ _ _ _, True)%I with "[$TCP' Tkt]");
    [solve_ndisj|done|done|by left|by right|by right|..].
  { iSplitL "".
    - iIntros "!> !>" (t2 [] v2 _) "[F|F]"; by iApply (TCP_comparable with "F").
    - rewrite /=. iFrame "Tkt".
      iIntros (t2 [] _). iSplit; [iSplitL""|].
      + iIntros "!> TCP !>". rewrite -bi.later_sep. iNext.
        iDestruct (TCP_duplicable with "TCP") as "#TCP'". by iFrame "TCP TCP'".
      + iIntros "Tkt TC !>". iExists (). iSplit; [done|].
        iIntros (t3 _) "PP !>". iSplitL ""; [by iIntros "!> $"|].
        iIntros "!> !>". subst P'.
        iDestruct "TC" as (tx Eqv n0 M) "(All & Perms & [%EqD %tB] & #NSR)".
        iDestruct (MyAll_coherent with "[$Tkt $All]") as %Eq.
        destruct (ns_tkt_bound_update _ _ _ _ _ _ Eq tB EqD)
          as (n' & nEq1 & nEq2 & nLt & tB').
        iMod (MyTkt_get _ _ _ (Some tx) with "[$All $Tkt]") as "[All' Tkt']".
        iDestruct (Perms_get with "Perms") as "[Perm Perms]".
        iModIntro. subst Q'. iSplitL "Perm Tkt'".
        * iExists tx, n'. iSplit.
          { iPureIntro. clear -nLt Eqv. by simplify_eq. }
          iFrame "Tkt' Perm".
          destruct ot as [t0|]; first (move: (nEq2 t0) => [//|->|-> //]).
          { by iApply ("NS" $! t0 with "[%]"). }
          { by rewrite nEq1. }
        * iNext. iExists (S tx). iSplit.
          { iPureIntro. clear -Eqv. simplify_eq. f_equal.
            by rewrite -Zplus_mod_idemp_l Eqv Zplus_mod_idemp_l
                       Z.add_1_r Nat2Z.inj_succ. }
          iExists n', (<[i:=Excl (Some tx)]> M).
          iFrame "All' Perms". iSplit.
          { iPureIntro. split.
            - rewrite -EqD. split; last apply dom_insert_subseteq.
              rewrite dom_insert_L elem_of_union.
              move => [/elem_of_singleton ?|//]. subst.
              apply elem_of_dom. by eexists.
            - by rewrite -Nat.add_1_r. }
          destruct ot as [t0|]; first (move: (nEq2 t0) => [//|->|-> //]).
          { by iApply ("NS" $! t0 with "[%]"). (* release CAS needed here *) }
          { by rewrite nEq1. }
      + iIntros "!>" (v NEq) "!>". iSplit; by iIntros "$". }
  iIntros (b t2 [] v2) "(_ & CASE)". subst P' Q'.
  iDestruct "CASE" as "[CASE|([% _] & _ & _ & Tkt)]"; last first.
  { (* CAS fails, retry FAI *)
    subst b. wp_case. iApply ("IH" with "Tkt Post"). }

  (* FAI succeeds, continue *)
  iClear "IH TCP NS".
  iDestruct "CASE" as "((%&%&_) & #TCP' & Q)". subst b v2. clear t1 v1 t' ot.
  iDestruct "Q" as (t0 n0 [Lt0 Eqt]) "(Tkt0 & Perm0 & #NS0)".

  (* wait-to-be served loop *)
  wp_case. wp_let.
  iLöb as "IH".
  iApply wp_repeat; [done|].

  (* read now-serving counter *)
  wp_op. iDestruct "NS0" as (t2' v2) "NS0".

  wp_apply (GPS_iSP_Read _ _ _ (NSP C P γ false (x >> 0) γn) with "[$NS0]");
    [solve_ndisj|done|done|by right| |].
  { iIntros (t' n' v' _) "!> !>". iSplit; last iSplit.
    - by iIntros "#$".
    - iIntros "#NSP !>". iFrame "NSP". by iApply (NSP_impl with "NSP").
    - by iIntros "#$". } iClear "NS0".

  iIntros (t3 n3 v3) "([%Le3 _] & #NSR3 & NSP)".
  rewrite {3}/NSP (fixpoint_unfold (NSP' C P γ) _ _ _ _ _ _).
  iDestruct "NSP" as "[% #ES]". subst v3.

  wp_pures.
  case (decide (t `mod` Z.pos C = n3 `mod` Z.pos C)) => [Eq|NEq]; last first.
  { (* not our turn yet, keep waiting *)
    iExists 0. rewrite bool_decide_false; [|done]. iSplit; [done|].
    simpl. by iApply ("IH" with "Post Tkt0 Perm0"). }

  (* it's our turn! Acquiring lock! *)
  iExists 1. rewrite bool_decide_true; [|done]. iSplit; [done|].
  simpl. iClear "IH".

  (* prove that the abstract ticket [n3] we read must be the same abstract
    ticket we own [t0], exploiting the fact that they correspond to the same
    concrete ticket *)
  (* crazy arithmetic *)
  iAssert (|={⊤}=> (⌜t0 = n3⌝ ∗ Perm γ t0))%I with "[Perm0]" as ">[% Perm0]".
  { case (decide (n3 ≤ t0)) => [LE|/Z.nle_gt Gt].
    - iFrame "Perm0". iModIntro. iPureIntro.
      assert (G0: Z.pos C > 0) by lia.
      assert (Ht := Z_div_mod t0 _ G0).
      assert (Hn := Z_div_mod n3 _ G0).
      rewrite Eqt /Z.modulo in Eq.
      destruct (Z.div_eucl t0 (Z.pos C)) as [qt rt].
      destruct (Z.div_eucl n3 (Z.pos C)) as [qn rn].
      destruct Ht as (tEq & Le1 & Lt1).
      destruct Hn as (nEq & Le2 & Lt2).
      apply Nat2Z.inj_iff. cbv in Le3.
      assert (LT: t0 < n3 + Z.pos C).
      { eapply Z.lt_le_trans; first apply Lt0. apply Zplus_le_compat_r.
        clear -Le3. lia. }
      move : LE LT. rewrite tEq nEq Eq.
      move => LE LT. do 2 f_equal.
      apply Z.add_le_mono_r in LE.
      apply Z.mul_le_mono_pos_l in LE; last lia.
      rewrite -Zplus_assoc (Z.add_comm rn) Zplus_assoc in LT.
      apply Z.add_lt_mono_r in LT. rewrite Zmult_succ_r_reverse in LT.
      apply Z.mul_lt_mono_pos_l in LT; lia.
    - iSpecialize ("ES" $! t0 with "[%]"); [lia|].
      iMod (escrow_elim with "[] ES [$Perm0]") as "[P NSW]"; [done|..].
      { iIntros "pTok". iApply (Perm_exclusive with "pTok"). }
      iDestruct "NSW" as (ti vi) "[>NSW _]".
      iMod (GPS_iSP_SWWriter_latest with "NSW NSR3") as "[[%Le _] NSW]"; [done|].
      exfalso. clear -Le Gt. cbv in Le. lia. }

  subst n3.
  iSpecialize ("ES" $! t0 with "[%//]").
  iMod (escrow_elim with "[] ES [$Perm0]") as "[P NSW]"; [done|..].
  { iIntros "pTok". iApply (Perm_exclusive with "pTok"). }
  iDestruct "NSW" as (ti vi) "[NSW _]".
  iIntros "!> !>". iApply "Post".
  iFrame "P". iExists γn, γ, i, t0. iFrame "Tkt0". iSplitL "".
  - by iExists _,_,_.
  - iExists _,_. iFrame "NSW". by iDestruct "NSR3" as "[_ $]".
Qed.

Lemma unlock_spec P x tid :
  {{{ ▷ P ∗ MayRelease C P x }}}
    unlock C [ #x] @ tid; ⊤
  {{{ RET #☠; MayAcquire C P x }}}.
Proof.
  iIntros (Φ) "[P MRel] Post".
  iDestruct "MRel" as (γn γ i t) "(Tkt & TCP & NSW)".
  wp_lam.

  (* read now-serving counter exclusively *)
  iDestruct "NSW" as (t1 v1) "NSW".
  wp_op.
  wp_apply (GPS_iSP_SWRead _ (NSP C P γ) _ (NSP C P γ true (x >> 0) γn t1 t v1)
              with "[$NSW]"); [solve_ndisj|done|done|by left| |].
  { by iIntros "!> !> #$". }

  iIntros "[NSW NSP]". wp_let.
  rewrite {3}/NSP (fixpoint_unfold (NSP' C P γ) _ _ _ _ _ _).
  iDestruct "NSP" as "[% #ES]". subst v1.

  wp_pures. rewrite Z.add_mod_idemp_l; [|lia].

  set Qi: vProp := NSP C P γ true (x >> 0) γn t1 t #(t `mod` Z.pos C).
  wp_apply (GPS_iSP_SWWrite_rel _ _ _ _ (λ _, True)%I Qi True%I _ _
                (S t : natProtocol) _ #((t + 1) `mod` Z.pos C) with "[P $NSW]");
    [solve_ndisj|done|done|cbv; lia|..].
  { iSplitR ""; [|by iIntros "!> !> #$"].
    iIntros "!>" (t' Lt') "NSW _ !>". iSplitL ""; last iSplitR ""; [..|done].
    { iIntros "!> NSP !>". iApply (NSP_impl with "NSP"). }
    iMod (escrow_alloc (Perm γ (S t))
              (P ∗ ∃ ti vi, GPS_iSP_Writer (tktlckN x) (NSP C P γ)
                                   (NSP C P γ false) (x >> 0) ti (S t) vi γn)%I
              with "[$P NSW]") as "ESSt" ; [solve_ndisj|..].
    { iIntros "!>". by iExists _,_. }
    iIntros "!>".
    rewrite {3}/NSP (fixpoint_unfold (NSP' C P γ) _ _ _ _ _ _).
    rewrite (_: t + 1 = S t); [|lia].
    iSplitL ""; [done|].
    iIntros (tO Le).
    apply Nat2Z.inj_le, Nat.le_succ_r in Le as [Le|EqS].
    + iApply "ES". iPureIntro. lia.
    + subst tO. by rewrite shift_0. }

  iIntros (t2) "(% & R & _)".
  iApply "Post".
  iExists γn, γ, i, (Some t). iFrame "Tkt TCP".
  iIntros (??). simplify_eq. by iExists _, _.
Qed.

End proof.
