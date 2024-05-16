From gpfsl.logic Require Import logatom proofmode.
From gpfsl.examples.queue Require Export event spec_abs_graph spec_abs.

Require Import iris.prelude.options.

Local Open Scope Z_scope.

Section abs_graph.
Context `{!noprolG Σ, !inG Σ (graphR qevent)}.
(* We only need an extended spec with Weak Consistency *)
Context (weq : spec_abs_graph.extended_queue_spec Σ WeakQueueConsistent).
Local Existing Instances
  spec_abs_graph.QueueInv_Timeless spec_abs_graph.QueueInv_Objective
  spec_abs_graph.QueueLocal_Persistent.

Definition isQueue N γq q : vProp Σ := weq.(QueueLocal) N γq q ∅ ∅.

Definition Queue γq q Q : vProp Σ := ∃ G, weq.(QueueInv) γq q Q G.

#[global] Instance Queue_objective γq q Q : Objective (Queue γq q Q) := _.
#[global] Instance Queue_timeless γq q Q : Timeless (Queue γq q Q) := _.
#[global] Instance isQueue_persistent N γq q : Persistent (isQueue N γq q) := _.

Lemma new_queue_spec :
  new_queue_spec' weq.(spec_abs_graph.new_queue) isQueue Queue.
Proof.
  iIntros (N tid Φ) "_ Post".
  iApply (weq.(spec_abs_graph.new_queue_spec) with "[%//]").
  iIntros "!> * [#QL LI]". iApply "Post". iFrame "QL". by iExists _.
Qed.

Lemma enqueue_spec :
  enqueue_spec' weq.(spec_abs_graph.enqueue) isQueue Queue.
Proof.
  intros N DISJ q tid γq V v Posx. iIntros "#⊒V #QL" (Φ) "AU".
  awp_apply (weq.(spec_abs_graph.enqueue_spec) with "⊒V QL"); [done..|].
  iApply (aacc_aupd_commit with "AU"); [done|].
  iIntros (Q) ">Q". iDestruct "Q" as (?) "QI".
  iAaccIntro with "QI".
  { iIntros ">QI !>". iSplitL "QI"; [|by auto]. iNext. by iExists _. }
  iIntros (V' Q' G' enqId enq Venq M') "(>QI & #⊒V' & #QL' & %F) !>".
  iDestruct (spec_abs_graph.QueueInv_QueueConsistent with "QI") as %QC.
  set (enqE := mkGraphEvent enq Venq M') in *.
  iAssert (Queue γq q Q') with "[QI]" as "Q". { by iExists _. }
  destruct F as (? & _ & ? & ? & ? & ENQ & HenqId & EsG' & ?).
  iExists Venq.(dv_comm), Q'.
  iSplitL; [|by auto]. iFrame "Q". iSplitL.
  + subst V'. iApply (monPred_in_mono with "⊒V'"). simpl.
    change (enqE.(ge_view).(dv_comm) ⊑ enqE.(ge_view).(dv_wrt)).
    apply: QC.(wkq_cons_enqueue_release G').
    * rewrite EsG'. apply lookup_app_1_eq.
    * by exists v.
  + iPureIntro. split; [|done]. trans Venq.(dv_in); [done|]. apply dv_in_com.
Qed.

Lemma dequeue_spec :
  dequeue_spec' weq.(spec_abs_graph.dequeue) isQueue Queue.
Proof.
  intros N DISJ q tid γq V. iIntros "#⊒V #QL" (Φ) "AU".
  awp_apply (weq.(spec_abs_graph.dequeue_spec) with "⊒V QL"); [done..|].
  iApply (aacc_aupd_commit with "AU"); [done|].
  iIntros (Q) ">Q". iDestruct "Q" as (?) "QI".
  iAaccIntro with "QI".
  { iIntros ">QI !>". iSplitL "QI"; [|by auto]. iNext. by iExists _. }
  iIntros (v V' Q' G' enqId deqId enq deq Venq Vdeq M') "(>QI & #⊒V' & #QL' & %F) !>".
  iDestruct (spec_abs_graph.QueueInv_QueueConsistent with "QI") as %QC.
  set (deqE := mkGraphEvent deq Vdeq M') in *.
  iAssert (Queue γq q Q') with "[QI]" as "Q". { by iExists _. }
  destruct F as (? & _ & ? & ? & [CASE|CASE]).
  - destruct CASE as (-> & ? & ?). iExists v, V, Q.
    iSplitL; [|by auto]. iFrame "Q ⊒V". iPureIntro. by left.
  - destruct CASE as (-> & ? & ENQ & DEQ & ? & ? & EsG' & SoG' & ComG' & ? & ? & ?
                     & enqE & ? & ? & ? & ?).
    rewrite /is_enqueue in ENQ. rewrite /is_dequeue in DEQ. subst enq deq.
    iExists v, Venq.(dv_comm), Q'.
    iSplitL; [|by auto]. iFrame "Q". iSplitL.
    { iDestruct (view_at_elim with "⊒V' QL'") as "{QL QL'} QL'".
      rewrite QueueLocal_graph_snap.
      iApply (graph_snap_lookup _ _ _ enqId with "QL'"); [|done].
      apply list_lookup_fmap_inv'. exists enqE. split; [done|].
      eapply prefix_lookup_Some; [done|by eexists]. }
    iPureIntro. by right.
Qed.

Lemma try_enq_spec :
  try_enq_spec' weq.(spec_abs_graph.try_enq) isQueue Queue.
Proof.
  intros N DISJ q tid γq V v Posx. iIntros "#⊒V #QL" (Φ) "AU".
  awp_apply (weq.(spec_abs_graph.try_enq_spec) with "⊒V QL"); [done..|].
  iApply (aacc_aupd_commit with "AU"); [done|].
  iIntros (Q) ">Q". iDestruct "Q" as (?) "QI".
  iAaccIntro with "QI".
  { iIntros ">QI !>". iSplitL "QI"; [|by auto]. iNext. by iExists _. }
  iIntros (b V' Q' G' enqId enq Venq M') "(>QI & #⊒V' & #QL' & %F) !>".
  iDestruct (spec_abs_graph.QueueInv_QueueConsistent with "QI") as %QC.
  set (enqE := mkGraphEvent enq Venq M') in *.
  iAssert (Queue γq q Q') with "[QI]" as "Q". { by iExists _. }
  destruct F as (? & _ & ? & ? & CASE). destruct b.
  - destruct CASE as (? & ENQ & HenqId & EsG' & ?).
    iExists true, Venq.(dv_comm), Q'.
    iSplitL; [|by auto]. iFrame "Q". iSplitL.
    + subst V'. iApply (monPred_in_mono with "⊒V'"). simpl.
      change (enqE.(ge_view).(dv_comm) ⊑ enqE.(ge_view).(dv_wrt)).
      apply: QC.(wkq_cons_enqueue_release G').
      * rewrite EsG'. apply lookup_app_1_eq.
      * by exists v.
    + iPureIntro. split; [|done]. trans Venq.(dv_in); [done|]. apply dv_in_com.
  - destruct CASE as [-> ->].
    iExists false, V, Q.
    iSplitL; [|by auto]. iFrame "Q ⊒V". done.
Qed.

Lemma try_deq_spec :
  try_deq_spec' weq.(spec_abs_graph.try_deq) isQueue Queue.
Proof.
  intros N DISJ q tid γq V.
  iIntros "#⊒V #QL" (Φ) "AU".
  awp_apply (weq.(spec_abs_graph.try_deq_spec) with "⊒V QL"); [done..|].
  iApply (aacc_aupd_commit with "AU"); [done|].
  iIntros (Q) ">Q". iDestruct "Q" as (?) "QI".
  iAaccIntro with "QI".
  { iIntros ">QI !>". iSplitL "QI"; [|by auto]. iNext. by iExists _. }
  iIntros (v V' Q' G' enqId deqId enq deq Venq Vdeq M') "(>QI & #⊒V' & #QL' & %F) !>".
  iDestruct (spec_abs_graph.QueueInv_QueueConsistent with "QI") as %QC.
  set (deqE := mkGraphEvent deq Vdeq M') in *.
  iAssert (Queue γq q Q') with "[QI]" as "Q". { by iExists _. }
  destruct F as (? & _ & ? & ? & [CASE|[CASE|CASE]]).
  - destruct CASE as (-> & ? & ->). iExists v, V, Q.
    iSplitL; [|by auto]. iFrame "Q ⊒V". iPureIntro. by left.
  - destruct CASE as (-> & ? & ?). iExists v, V, Q.
    iSplitL; [|by auto]. iFrame "Q ⊒V". iPureIntro. by right; left.
  - destruct CASE as (-> & ? & ENQ & DEQ & ? & ? & EsG' & SoG' & ComG' & ? & ? & ?
                     & enqE & ? & ? & ? & ?).
    rewrite /is_enqueue in ENQ. rewrite /is_dequeue in DEQ. subst enq deq.
    iExists v, Venq.(dv_comm), Q'.
    iSplitL; [|by auto]. iFrame "Q". iSplitL.
    { iDestruct (view_at_elim with "⊒V' QL'") as "{QL QL'} QL'".
      rewrite QueueLocal_graph_snap.
      iApply (graph_snap_lookup _ _ _ enqId with "QL'"); [|done].
      apply list_lookup_fmap_inv'. exists enqE. split; [done|].
      eapply prefix_lookup_Some; [done|by eexists]. }
    iPureIntro. by right; right.
Qed.
End abs_graph.

Definition abs_graph_abs_queue_spec
  Σ `{!noprolG Σ, !inG Σ (graphR qevent)}
  (weq : spec_abs_graph.extended_queue_spec Σ WeakQueueConsistent) : queue_spec Σ := {|
    spec_abs.Queue              := Queue weq ;
    spec_abs.isQueue            := isQueue weq ;

    spec_abs.Queue_Objective    := Queue_objective weq ;
    spec_abs.Queue_Timeless     := Queue_timeless weq ;
    spec_abs.isQueue_Persistent := isQueue_persistent weq ;

    spec_abs.new_queue_spec     := new_queue_spec weq ;
    spec_abs.enqueue_spec       := enqueue_spec weq ;
    spec_abs.dequeue_spec       := dequeue_spec weq ;
    spec_abs.try_enq_spec       := try_enq_spec weq ;
    spec_abs.try_deq_spec       := try_deq_spec weq ;
  |}%I.
