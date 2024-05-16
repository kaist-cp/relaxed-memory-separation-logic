From iris.proofmode Require Import tactics.

From gpfsl.base_logic Require Import frame_instances.
From gpfsl.logic Require Import logatom invariants proofmode.
From gpfsl.examples.queue Require Import spec_graph.
From gpfsl.examples Require Import set_helper.

Require Import iris.prelude.options.

Local Notation event_list := (event_list qevent).

Section RSL.
Context {Σ : gFunctors} `{noprolG Σ, inG Σ (graphR qevent)}.

#[local] Notation iProp := (iProp Σ).
#[local] Notation vProp := (vProp Σ).

Hypothesis msq : weak_queue_spec Σ.

Implicit Types (N : namespace) (P : Z → vProp) (q : loc).

Definition queue_resources P G : vProp :=
  ([∗ set] eid ∈ filter (unmatched_enq_2 G) (to_set G.(Es)),
      match G.(Es) !! eid with
      | Some (mkGraphEvent (Enq v) V _) => @{V.(dv_in)} P v
      | _ => emp (* this is impossible *)
      end)%I.

Instance queue_resources_objective P G : Objective (queue_resources P G).
Proof.
  apply big_sepS_objective => e.
  destruct (G.(Es) !! e) as [[ ge ??]|]; [|apply _].
  destruct ge; apply _.
Qed.

Definition QueuePerElemInv P γg q : vProp :=
  ∃ G, msq.(QueueInv) γg q G ∗ queue_resources P G.

Local Existing Instance QueueInv_Objective.
Instance QueuePerElemInv_objective P γg q : Objective (QueuePerElemInv P γg q) := _.

Definition QueuePerElem N P γg q : vProp :=
  ∃ G M, msq.(QueueLocal) (N .@ "que") γg q G M ∗
         inv (N .@ "iinv") (QueuePerElemInv P γg q).

(* TODO: we can prove logically-atomic spec here. *)
Lemma per_elem_enqueue N P γg q (x: Z) tid (DISJ: N ## histN) (NZ: 0 < x) :
  {{{ QueuePerElem N P γg q ∗ ▷ P x}}}
      msq.(enqueue) [ #q; #x] @ tid; ⊤
  {{{ RET #☠; QueuePerElem N P γg q }}}.
Proof.
  iIntros (Φ) "[Queue P] Post".
  iDestruct "Queue" as (G0 M0) "[Queue #QPI]".
  iApply (wp_step_fupd _ _ ⊤ _  (_ -∗ _)%I with "[$Post]"); [auto..|].
  (* apply the AU *)
  iDestruct (view_at_intro with "P") as (V) "[#InV P]". rewrite view_at_later.
  awp_apply (enqueue_spec with "InV Queue"); [solve_ndisj|done|].
  iInv "QPI" as (G) "[QI Elems]".
  iAaccIntro with "QI".
  { iIntros "QI !>". iFrame "P". iNext. iExists G. by iFrame. }

  iIntros (V' G' enqId enq Venq M') "(QI' & SV' & Local & F)".
  iDestruct "F" as %(LeG' & SubM' & Sub' & Sub'' & IQ & Eqenq &
                    EsG' & SoG' & ComG' & EqM' & NInM0).
  rewrite /is_enqueue in IQ. subst enq.

  have Eqts : to_set G'.(Es) = {[enqId]} ∪ to_set G.(Es).
  { by rewrite EsG' to_set_append -Eqenq. }
  have EqEm' : G'.(Es) !! enqId = Some (mkGraphEvent (Enq x) Venq M').
  { by rewrite EsG' Eqenq lookup_app_1_eq. }

  iIntros "!>".
  iAssert (▷ queue_resources P G')%I with "[P Elems]" as "Elems'".
  { iNext. rewrite /queue_resources.
    have UMe : unmatched_enq_2 G' enqId.
    { split.
      - rewrite EqEm'. by eexists.
      - move => ??. rewrite SoG'. move => /(gcons_so_included G) [/=].
        rewrite Eqenq. clear; lia. }
    have NIn: enqId ∉ filter (unmatched_enq_2 G) (to_set G.(Es)).
    { move => /elem_of_filter [[? FA] /elem_of_set_seq]. rewrite Eqenq. clear; lia. }
    rewrite (_: filter (unmatched_enq_2 G') (to_set G'.(Es)) =
                {[enqId]} ∪ filter (unmatched_enq_2 G) (to_set G.(Es))); last first.
    { rewrite Eqts filter_union_L filter_singleton_L; [|done].
      f_equal. apply leibniz_equiv => i. rewrite !elem_of_filter.
      assert (Hi: i ∈ to_set (Es G) → (unmatched_enq_2 G' i ↔ unmatched_enq_2 G i)).
      { intros Hi.
        have NEi : i ≠ length G.(Es).
        { apply elem_of_set_seq in Hi. intros ->. clear -Hi. lia. }
        rewrite /unmatched_enq_2 SoG' {1}EsG' lookup_app_1_ne; [|done].
        rewrite Eqts. split; intros [? SA]; (split; [done|]).
        - by apply set_Forall_union_inv_2 in SA.
        - apply set_Forall_union; [|done]. apply set_Forall_singleton.
          move => /gcons_so_included [/= _]. rewrite Eqenq. clear; lia. }
      clear -Hi. split; (intros []; split; [by apply Hi|done]). }
    rewrite big_sepS_union; last by apply disjoint_singleton_l.
    rewrite big_sepS_singleton. iSplitL "P".
    - rewrite EqEm' -Sub'. by iFrame "P".
    - iApply (big_sepS_mono with "Elems").
      move => i /= Ini. rewrite EsG' lookup_app_1_ne.
      + by iIntros "$".
      + move : Ini => /elem_of_filter [_ /elem_of_set_seq]. lia. }
  iSplitL "QI' Elems'".
  - iNext. iExists G'. by iFrame.
  - iIntros "_ HΦ !>". iApply "HΦ".
    iDestruct (view_at_elim with "SV' Local") as "Local".
    iExists _, _. by iFrame.
Qed.

Lemma per_elem_dequeue N P γg q tid (DISJ: N ## histN) :
  {{{ QueuePerElem N P γg q }}}
      msq.(dequeue) [ #q] @ tid; ⊤
  {{{ (x: Z), RET #x; QueuePerElem N P γg q ∗ (⌜x = 0⌝ ∨ ▷ P x) }}}.
Proof.
  iIntros (Φ) "QI Post". iDestruct "QI" as (G0 M0) "[Queue #QPI]".
  iApply (wp_step_fupd _ _ ⊤ _ (∀ _, _-∗ _)%I with "[$Post]"); [auto..|].

  (* apply the AU *)
  iDestruct (monPred_in_intro True%I with "[//]") as (V) "[#InV _]".
  awp_apply (dequeue_spec with "InV Queue"); [solve_ndisj|].
  iInv "QPI" as (G) "[QI Elems]".
  iAaccIntro with "QI".
  { iIntros "QI !>". iSplit; [|done]. iNext. iExists G. by iFrame. }

  iIntros (x V' G' enqId deqId enq deq Vdeq M') "(QI' & sV' & Local & F)".
  iDestruct "F" as %(LeG' & SubM' & Sub' & Sub'' & CASE).
  iIntros "!>". destruct CASE as [[? CASE]|[Lt0 CASE]].
  { destruct CASE as (? & Eqdeq & EsG' & SoG' & ComG' & EqM' & InM').
    iSplitR "Local sV'"; last first.
    { iIntros "_ Post !>". iApply "Post". iSplitL; last by iLeft.
      iDestruct (view_at_elim with "sV' Local") as "Local".
      iExists _, _. by iFrame. }

    have Eqts : to_set G'.(Es) = {[deqId]} ∪ to_set G.(Es).
    { by rewrite EsG' to_set_append -Eqdeq. }
    have EqEm' : G'.(Es) !! deqId = Some (mkGraphEvent EmpDeq Vdeq M').
    { rewrite EsG' Eqdeq lookup_app_1_eq. by subst deq. }

    iNext. iExists G'. iFrame. subst deq.
    iApply (big_sepS_mono' with "Elems"); last first.
    - rewrite Eqts filter_union_L filter_singleton_not_L; last first.
      { intros [[v Eqv] _]. by rewrite EqEm' in Eqv. }
      rewrite left_id_L.
      apply leibniz_equiv => i. rewrite !elem_of_filter.
      assert (Hi: i ∈ to_set (Es G) → (unmatched_enq_2 G' i ↔ unmatched_enq_2 G i)).
      { intros Hi.
        have NEi : i ≠ length G.(Es).
        { apply elem_of_set_seq in Hi. intros ->. clear -Hi. lia. }
        rewrite /unmatched_enq_2 SoG' {1}EsG' lookup_app_1_ne; [|done].
        rewrite Eqts. split; intros [? SA]; (split; [done|]).
        - by apply set_Forall_union_inv_2 in SA.
        - apply set_Forall_union; [|done]. apply set_Forall_singleton.
          move => /gcons_so_included [/= _]. rewrite Eqdeq. clear; lia. }
      clear -Hi. split; (intros []; split; [by apply Hi|done]).
    - intros e. case (decide (deqId = e)) => ?.
      + subst e. rewrite EqEm'. by iIntros "_".
      + rewrite EsG' lookup_app_1_ne; [done|by rewrite -Eqdeq]. }

  destruct CASE as (IE & ID & Eqdeq & FRSo & EsG' & SoG' & ComG' & InEM' & InDM'
                    & NInM & eV & EqEId & EqEnq & SubM).
  rewrite /is_enqueue in IE. rewrite /is_dequeue in ID. subst enq deq.
  destruct eV as [x' Venq Menq]. simpl in *. subst x'.

  have ?: enqId ≠ deqId.
  { intros ?. subst deqId enqId. apply lookup_lt_Some in EqEId. lia. }
  have Eqts : to_set G'.(Es) = {[deqId]} ∪ to_set G.(Es).
  { by rewrite EsG' to_set_append -Eqdeq. }
  have EqDm' : G'.(Es) !! deqId = Some (mkGraphEvent (Deq x) Vdeq M').
  { by rewrite EsG' Eqdeq lookup_app_1_eq. }
  have EqEm' : G'.(Es) !! enqId = Some (mkGraphEvent (Enq x) Venq Menq).
  { rewrite EsG' lookup_app_1_ne; [done|by rewrite -Eqdeq]. }

  iAssert (▷ (@{Venq.(dv_in)} P x ∗ queue_resources P G'))%I
    with "[Elems]" as "[Px Elems]".
  { iNext. rewrite /queue_resources.
    rewrite (_: (@{Venq.(dv_in)} P x)%I
                ≡ ([∗ set] eid ∈ {[enqId]},
                    match G'.(Es) !! eid with
                    | Some (mkGraphEvent (Enq v) V _) => @{V.(dv_in)} P v
                    | _ => emp
                    end)%I); last first.
    { by rewrite big_sepS_singleton EqEm'. }
    rewrite -big_sepS_union; last first.
    { apply disjoint_singleton_l.
      move => /elem_of_filter [[? FA] InG']. apply (FA deqId).
      - rewrite Eqts. set_solver-.
      - rewrite SoG'. clear. set_solver. }
    iApply (big_sepS_mono' with "Elems"); last first.
    { rewrite Eqts filter_union_L filter_singleton_not_L; last first.
      {  intros [[v Eqv] _]. by rewrite EqDm' in Eqv. }
      rewrite left_id_L. apply leibniz_equiv => i.
      rewrite elem_of_union elem_of_singleton !elem_of_filter.
      case (decide (i = enqId)) => ?; last split.
      - subst i. split; [by left|]. intros _. split; first split.
        + rewrite EqEId. by eexists.
        + intros ??. apply FRSo.
        + apply elem_of_set_seq. apply lookup_lt_Some in EqEId. clear -EqEId; lia.
      - intros [[Eqi FA] Ini]. right. split; [split|done].
        + rewrite EsG' lookup_app_1_ne //.
          move : Ini => /elem_of_set_seq. clear; lia.
        + rewrite Eqts SoG'. intros i'.
          rewrite elem_of_union elem_of_singleton.
          move => [?|/FA].
          * subst i'. move => /elem_of_union [/elem_of_singleton|].
            { inversion 1. by subst i. }
            { move => /gcons_so_included [/= _]. rewrite Eqdeq. clear; lia. }
          * move => ? /elem_of_union [/elem_of_singleton|//].
            inversion 1. by subst i.
      - intros [?|[UM Ini]]; [by subst|]. split; [|done].
        move : UM. rewrite /unmatched_enq_2 Eqts EsG' lookup_app_1_ne.
        * rewrite SoG'. intros [? FA]. split; [done|].
          intros i' Ini' Inso'. apply (FA i').
          { clear -Ini'. set_solver. }
          { clear -Inso'. set_solver. }
        * move : Ini => /elem_of_set_seq. clear; lia. }

    intros i. case (decide (i = deqId)) => ?.
    - subst i. rewrite EqDm'. by iIntros "_".
    - rewrite EsG' lookup_app_1_ne; [done|by rewrite -Eqdeq]. }

  iSplitL "QI' Elems".
  - iNext. iExists G'. by iFrame.
  - iIntros "_ Post !>". iApply "Post".
    iDestruct (view_at_elim with "sV' Local") as "Local".
    iAssert (⊒Venq.(dv_in))%I with "[Local]" as "#InVe".
    { rewrite QueueLocal_graph_snap.
      iApply monPred_in_mono; [apply dv_in_com|].
      iApply (graph_snap_lookup with "Local"); [..|exact InEM'].
      by rewrite EqEm'. }
    iSplitR "Px".
    + iExists _,_. by iFrame.
    + iRight. iNext. iApply (view_at_elim with "InVe Px").
Qed.

End RSL.

From gpfsl.logic Require Import atomic_cmra.
From gpfsl.examples.queue Require Import code_ms proof_ms_abs_graph proof_ms_closed.

(* This proof can also be derived from spec_abs. *)
(* TODO: use ther spec_per_elem one. Need try_enq and try_deq *)
Section RSL_instance.
Context {Σ : gFunctors} `{noprolG Σ, !msqueueG Σ, !atomicG Σ}.

Let is_queue := QueuePerElem (msqueue_impl_graph_weak Σ).

Lemma per_elem_enqueue_inst N P γg q (x: Z) tid
  (NZ: (0 < x)%Z) (DISJ: N ## histN) :
  {{{ is_queue N P γg q ∗ ▷ P x }}}
    enqueue [ #q ; #x] @ tid; ⊤
  {{{ RET #☠; is_queue N P γg q }}}.
Proof. by apply : per_elem_enqueue. Qed.

Lemma per_elem_dequeue_inst N P γg q tid (DISJ: N ## histN) :
  {{{ is_queue N P γg q }}}
    dequeue [ #q] @ tid; ⊤
  {{{ (x: Z), RET #x; is_queue N P γg q ∗ (⌜x = 0⌝ ∨ ▷ P x) }}}.
Proof. by apply : per_elem_dequeue. Qed.
End RSL_instance.
