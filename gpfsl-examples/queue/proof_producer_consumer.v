From iris.algebra Require Import excl_auth.
From iris.proofmode Require Import tactics.

From gpfsl.lang Require Import notation.
From gpfsl.logic Require Import logatom invariants proofmode.

From gpfsl.examples.queue Require Import spec_spsc code_producer_consumer.
From gpfsl.examples Require Import set_helper.

Require Import iris.prelude.options.

(** Verifying clients that uses a queue in the SPSC (single-producer, single-
  consumer) fashion, using the graph-based LAT spec for queue. *)

Local Notation graph := (graph qevent).

Implicit Types (G : graph).

Local Open Scope nat_scope.

Implicit Types
  (q pa ca : loc) (vl : list Z)
  (es ds xs : list event_id).

Local Hint Constructors Produced Consumed EmpDeqs : core.

Definition to_arr (vl : list Z) := LitV ∘ LitInt <$> vl.

Section producer_consumer.
Context `{!noprolG Σ,
          !inG Σ (graphR qevent),
          !inG Σ (prodR (excl_authR (leibnizO (list event_id)))
                        (excl_authR (leibnizO (list event_id))))}.
Context (pcN qN : namespace)
        (DISJ1: pcN ## histN) (DISJ2: qN ## histN) (DISJ3: pcN ## qN).

(* [queue_FIFO] is sufficient for single-producer/single-consumer. *)
Hypothesis spsc : spsc_spec Σ WeakQueueConsistent.
Local Existing Instances SPSCInv_Objective.

Local Notation iProp := (iProp Σ).
Local Notation vProp := (vProp Σ).

Notation produce_loop := (produce_loop spsc.(enqueue)).
Notation produce := (produce spsc.(enqueue)).
Notation consume_loop := (consume_loop spsc.(dequeue)).
Notation consume := (consume spsc.(dequeue)).
Notation produce_consume_first_half := (produce_consume_first_half spsc.(enqueue) spsc.(dequeue)).

(* There's a prior agreement that the values in [vl] will be produced/consumed
  in that order following SPSC protocol. This is only needed because the threads
  don't join afterwards. If we had them join, then there should be no need to
  fix [vl] up front. *)
Definition PCInv q γg γed vl : vProp := ∃ G es ds xs,
  spsc.(SPSCInv) γg γed q G es ds ∗
  ⌜ ∀ i e (Ei : es !! i = Some e),
        ∃ eV, G.(Es) !! e = Some eV ∧
          ∃ v, eV.(ge_event) = Enq v ∧ vl !! i = Some v ⌝
  .

Instance PCInv_objective q γg γed vl : Objective (PCInv q γg γed vl) := _.

(** Extract the element i in (arr, vl) *)
Lemma array_access (arr : loc) vl (i : nat) v (VAL : vl !! i = Some v):
  arr ↦∗ to_arr vl
  ⊣⊢ (arr ↦∗ (LitV ∘ LitInt <$> take i vl) ∗
     (arr >> i) ↦ #v ∗
     (arr >> i >> 1) ↦∗ (LitV ∘ LitInt <$> (drop (S i) vl))).
Proof.
  rewrite -{1}(take_drop_middle _ _ _ VAL).
  rewrite /to_arr fmap_app fmap_cons /=.
  rewrite ->own_loc_na_vec_app, own_loc_na_vec_cons.
  rewrite fmap_take take_length.
  apply lookup_lt_Some in VAL as LT.
  have {}LT : (i < length (to_arr vl))%nat by rewrite fmap_length.
  rewrite (_ : i `min` (length (to_arr vl)) = i)%nat; [done|lia].
Qed.

(** Specs for a partially produced array, in single-producer mode:
  The events es0 in the graph (G0, M0) have produced the elements [0,i) of vl.
  The elements [i,n) are to be produced.
  The pre-condition here is the loop invariant. *)
Lemma produce_loop_spec γg γed vl n tid q pa G0 M0 es0 i
    (Hn : length vl = n) (Hi : length es0 = i) (LT : i < n)
    (GT : Forall (λ v, 0 < v)%Z vl) :
  inv pcN (PCInv q γg γed vl) -∗
  {{{ spsc.(Producer) qN γg γed q G0 M0 es0 ∗
      pa ↦∗ (to_arr vl) }}}
    produce_loop [ #q; #pa; #n] [ #i] @ tid; ⊤
  {{{ RET #☠; True }}}.
Proof using All.
  iIntros "#PCInv" (Φ) "!> [P PA] Post".
  wp_lam.
  iLöb as "IH" forall (G0 M0 es0 i Hi LT).

  wp_rec. wp_op. rewrite bool_decide_false; [|lia]. wp_if. wp_op.

  (* read the array element *)
  have LT' := LT. rewrite -Hn in LT'. apply lookup_lt_is_Some in LT' as [v VAL].
  rewrite ->(array_access pa _ _ _ VAL).
  iDestruct "PA" as "(PAL & PAi & PAR)".
  rewrite Nat2Z.id. wp_read.
  iCombine "PAL PAi PAR" as "PA".
  rewrite -(array_access pa _ _ _ VAL).

  wp_let.
  iDestruct (monPred_in_intro True%I with "[//]") as (V) "[#⊒V _]".
  awp_apply (enqueue_spsc_spec with "⊒V P"); [done|..].
  { rewrite ->Forall_lookup in GT. by apply (GT i). }

  iInv pcN as (????) "[Inv >%ENQVALS]".

  iAaccIntro with "Inv".
  { iFrame. iIntros "Inv !> !>". iExists _,es,ds,xs. iFrame (ENQVALS) "Inv". }

  iIntros (V' G' es' enqId enq Venq M') "(Inv & #⊒V' & P' & %F)".
  iDestruct (view_at_elim with "⊒V' P'") as "P'".
  rewrite /is_enqueue in F.
  destruct F as (? & ? & -> & ? & ? & -> & ? & EsG' & ? & ? & ?).
  set (eV := mkGraphEvent (Enq v) Venq M') in *.
  iDestruct (Producer_Produced with "P'") as "#%PRODUCED'".

  iIntros "!>". iSplitL "Inv".
  { (* close inv *) iNext. iExists _,es',ds,xs. iFrame. iPureIntro.
    subst es' enqId i. rewrite EsG'.
    intros ?? [Ei0|[-> <-]]%lookup_app_1.
    - specialize (ENQVALS _ _ Ei0) as (eV0 & HeV' & v0 & ? & ?).
      exists eV0. split; [|by eauto]. eapply prefix_lookup_Some; [done|by eexists].
    - exists eV. split; [apply lookup_app_1_eq| by eauto]. }

  iIntros "_". wp_seq. wp_op.
  rewrite -Nat2Z.inj_add.
  case (decide (i + 1 = n)) as [->|NE].
  { wp_rec. wp_op. rewrite bool_decide_true; [|done]. wp_pures. by iApply "Post". }
  iApply ("IH" $! _ _ _ (i + 1) with "[%] [%] P' PA Post").
  { subst es' i. rewrite app_length //=. }
  { lia. }
Qed.

(** Specs for a partially consumed array, in single-consumer mode:
  The events es0 in the graph (G0, M0) have consumed the elements [0,i) of vl,
  and written those to ca. The rest of ca is all 0's.
  The elements [i,m) are to be consumed.
  The pre-condition here is the loop invariant. *)
Lemma consume_loop_spec γg γed vl n m tid q ca G0 M0 ds0 i
    (Hn : length vl = n) (Hm : m ≤ n) (Hi : length ds0 = i) (LT : i < m) :
  inv pcN (PCInv q γg γed vl) -∗
  {{{ spsc.(Consumer) qN γg γed q G0 M0 ds0 ∗
      ca ↦∗ to_arr ((take i vl) ++ replicate (m - i) 0%Z) }}}
    consume_loop [ #q; #ca; #m] [ #i] @ tid; ⊤
  {{{ RET #☠; ca ↦∗ (to_arr (take m vl)) }}}.
Proof using All.
  iIntros "#PCInv" (Φ) "!> [C CA] Post".
  wp_lam.
  iLöb as "IH" forall (G0 M0 ds0 i Hi LT).

  wp_rec. wp_op. rewrite bool_decide_false; [|lia]. wp_if.

  iDestruct (monPred_in_intro True%I with "[//]") as (V) "[#⊒V _]".
  awp_apply (dequeue_spsc_spec with "⊒V C"); [done|].

  iInv pcN as (????) "[Inv >%ENQVALS]".

  iAaccIntro with "Inv".
  { iFrame. iIntros "Inv !> !>". iExists _,es,ds,xs. iFrame (ENQVALS) "Inv". }

  iIntros (v V' G' ds' enqId deqId enq deq Vdeq M') "(Inv & #⊒V' & C' & %F)".
  iDestruct (view_at_elim with "⊒V' C'") as "C'".
  destruct F as (? & ? & -> & ? & ? & CASE).

  destruct CASE as [CASE|CASE].
  { destruct CASE as (-> & -> & ? & EsG' & -> & ?).
    iIntros "!>". iSplitL "Inv".
    { (* close inv *) iNext. iExists _,es,ds,(xs ++ [deqId]). iFrame. iPureIntro.
      intros ?? Ei0. specialize (ENQVALS _ _ Ei0) as (eV0 & HeV' & v0 & ? & ?).
      exists eV0. split; [|by eauto]. eapply prefix_lookup_Some; [done|by eexists]. }
    iIntros "_". wp_let. wp_op. wp_if.
    iApply ("IH" $! _ _ ds i with "[%//] [%//] C' CA Post"). }

  rewrite /is_enqueue /is_dequeue in CASE.
  destruct CASE as (? & -> & -> & HdeqId & EsG' & Hds' & Ei & ? & ? & ? & eV & HeV & Hev & ?).

  (* return value = i-th value of vl *)
  rewrite Hi in Ei.
  have Hvi : vl !! i = Some v.
  { specialize (ENQVALS _ _ Ei) as (eV' & HeV' & v' & ? & ?). congruence. }

  iIntros "!>". iSplitL "Inv".
  { (* close inv *) iNext. iExists _,es,ds',xs. iFrame. iPureIntro.
    intros ?? Ei0. specialize (ENQVALS _ _ Ei0) as (eV0 & HeV' & v0 & ? & ?).
    exists eV0. split; [|by eauto]. eapply prefix_lookup_Some; [done|by eexists]. }

  iIntros "_". wp_let. wp_op. rewrite bool_decide_true; [|done]. wp_if.

  (* write to the array *)
  have LENi : length (take i vl) = i by rewrite take_length; lia.
  have LENi' : length (take (i + 1) vl) = i + 1 by rewrite take_length; lia.
  have VAL0 : (take i vl ++ replicate (m - i) 0%Z) !! i = Some 0%Z.
  { rewrite lookup_app_r; [|lia]. apply lookup_replicate. lia. }
  rewrite ->(array_access ca _ _ _ VAL0).
  iDestruct "CA" as "(CAL & CAi & CAR)".
  wp_op. rewrite Nat2Z.id. wp_write.
  iCombine "CAL CAi CAR" as "CA".
  have VAL' : (take (i + 1) vl ++ replicate (m - (i + 1)) 0%Z) !! i = Some v.
  { rewrite lookup_app_l; [|lia]. rewrite lookup_take; [done|lia]. }
  rewrite (_ : take i (take i vl ++ replicate (m - i) 0%Z)
             = take i (take (i + 1) vl ++ replicate (m - (i + 1)) 0%Z)); last first.
  { rewrite !take_app_le; [|lia..].
    rewrite take_idemp. rewrite take_take Nat.min_l; [done|lia]. }
  rewrite (_ : drop (S i) (take i vl ++ replicate (m - i) 0%Z)
             = drop (S i) (take (i + 1) vl ++ replicate (m - (i + 1)) 0%Z)); last first.
  { rewrite !drop_app_ge; [|lia..]. rewrite LENi LENi' !drop_replicate.
    rewrite (_ : m - i - (S i - i) = m - (i + 1) - (S i - (i + 1))); [done|lia]. }
  rewrite -(array_access ca _ _ _ VAL').

  wp_op. rewrite -Nat2Z.inj_add.
  case (decide (i + 1 = m)) as [->|NE].
  { wp_rec. wp_op. rewrite bool_decide_true; [|done]. wp_pures.
    iApply "Post". rewrite Nat.sub_diag /= app_nil_r. by iFrame "CA". }
  iApply ("IH" $! _ _ ds' (i + 1) with "[%] [%] C' CA Post").
  { subst ds' i. rewrite app_length //=. }
  { lia. }
Qed.

(** The producer is forked and run on a child thread, which the code doesn't
  join with later, so in the post-condition we only have the consumer array [ca]
  left. To also recollect the producer array [pa], we'd need to wait and join
  with the producer thread. *)
Lemma produce_consume_first_half_spec γg γed vl tid q pa ca n
    (Hn : length vl = n + n) (NZ : n > 0) (GT : Forall (λ v, 0 < v)%Z vl) :
  {{{ spsc.(SPSCInv) γg γed q ∅ [] [] ∗
      spsc.(Producer) qN γg γed q ∅ ∅ [] ∗ spsc.(Consumer) qN γg γed q ∅ ∅ [] ∗
      pa ↦∗ (to_arr vl) ∗
      ca ↦∗ (replicate n #0) }}}
    produce_consume_first_half [ #q; #pa; #ca; #n] @ tid; ⊤
  {{{ RET #☠; ca ↦∗ (to_arr (take n vl)) }}}.
Proof using All.
  iIntros (Φ) "(Inv & P & C & PA & CA) Post".
  iMod (inv_alloc pcN _ (PCInv q γg γed vl) with "[Inv]") as "#Inv".
  { iNext. iExists _, [], [], []. simpl. iFrame. done. }
  wp_lam.
  wp_apply (wp_fork with "[P PA]"); first done.
  { iIntros "!>" (?). wp_op. rewrite -Nat2Z.inj_add. wp_lam.
    iApply (produce_loop_spec _ _ vl (n + n) _ _ _ _ _ [] 0
              with "[] [$P $PA //] []"); [done|done|lia|done|done|done]. }
  iIntros "_". wp_seq. wp_lam.
  iApply (consume_loop_spec _ _ vl (n + n) n _ _ _ _ _ [] 0
            with "[] [$C CA] [Post]"); [done|lia|done|lia|done| |done].
  rewrite Nat.sub_0_r /= /to_arr fmap_replicate /=. iFrame "CA".
Qed.

End producer_consumer.
