From gpfsl.logic Require Import logatom proofmode.
From gpfsl.examples.queue Require Export event spec_abs_graph spec_graph.

Require Import iris.prelude.options.

Local Open Scope Z_scope.

Section abs_graph.
Context `{!noprolG Σ, !inG Σ (graphR qevent)}.
Context `(sq : spec_abs_graph.extended_queue_spec Σ QueueConsistent).
Local Existing Instances
  spec_abs_graph.QueueInv_Timeless spec_abs_graph.QueueInv_Objective
  spec_abs_graph.QueueLocal_Persistent.

Definition QueueInv γg q G : vProp Σ := ∃ Q, sq.(spec_abs_graph.QueueInv) γg q Q G.

Definition QueueLocal N γg q G M : vProp Σ := sq.(spec_abs_graph.QueueLocal) N γg q G M.

#[global] Instance QueueInv_objective γg q Q : Objective (QueueInv γg q Q) := _.
#[global] Instance QueueInv_timeless γg q Q : Timeless (QueueInv γg q Q) := _.
#[global] Instance QueueLocal_persistent N γg q G M : Persistent (QueueLocal N γg q G M) := _.

Lemma QueueInv_StrongQueueConsistent_instance :
  ∀ γg q G, QueueInv γg q G ⊢ ⌜ QueueConsistent G ⌝.
Proof.
  intros. iDestruct 1 as (?) "QI".
  by iApply sq.(spec_abs_graph.QueueInv_QueueConsistent).
Qed.

Lemma QueueInv_graph_master_acc_instance :
  ∀ γg q G, QueueInv γg q G ⊢
    graph_master γg (1/2) G ∗
    (graph_master γg (1/2) G -∗ QueueInv γg q G).
Proof.
  intros. iDestruct 1 as (?) "QI".
  iDestruct (sq.(spec_abs_graph.QueueInv_graph_master_acc) with "QI") as "[$ Close]".
  iIntros "Gm". iSpecialize ("Close" with "Gm"). by iExists Q.
Qed.

Lemma QueueLocal_graph_snap_instance :
  ∀ N γg q G M, QueueLocal N γg q G M ⊢ graph_snap γg G M.
Proof. intros. by iApply sq.(spec_abs_graph.QueueLocal_graph_snap). Qed.

Lemma new_queue_spec :
  new_queue_spec' sq.(spec_abs_graph.new_queue) QueueLocal QueueInv.
Proof.
  iIntros (N tid Φ) "_ Post".
  iApply (sq.(spec_abs_graph.new_queue_spec) with "[%//]").
  iIntros "!> * [#QL LI]". iApply "Post". iFrame "QL". by iExists _.
Qed.

Lemma enqueue_spec :
  enqueue_spec' sq.(spec_abs_graph.enqueue) QueueLocal QueueInv.
Proof.
  intros N DISJ q tid γg G1 M V v Posx. iIntros "#⊒V #QL" (Φ) "AU".
  awp_apply (sq.(spec_abs_graph.enqueue_spec) with "⊒V QL"); [done..|].
  iApply (aacc_aupd_commit with "AU"); [done|].
  iIntros (G) ">QI". iDestruct "QI" as (?) "QI".
  iAaccIntro with "QI".
  { iIntros ">QI !>". iSplitL "QI"; [|by auto]. iNext. by iExists _. }
  iIntros (V' Q' G' enqId enq Venq M') "(>QI & #⊒V' & #QL' & %F) !>".
  iAssert (QueueInv γg q G') with "[QI]" as "QI". { by iExists _. }
  destruct F as (? & ? & ? & ? & ? & ENQ & HenqId & EsG' & ? & ? & ? & ?).
  iExists V', G', enqId, enq, Venq, M'. iFrame "QI QL' ⊒V'". auto.
Qed.

Lemma dequeue_spec :
  dequeue_spec' sq.(spec_abs_graph.dequeue) QueueLocal QueueInv.
Proof.
  intros N DISJ q tid γg G1 M V. iIntros "#⊒V #QL" (Φ) "AU".
  awp_apply (sq.(spec_abs_graph.dequeue_spec) with "⊒V QL"); [done..|].
  iApply (aacc_aupd_commit with "AU"); [done|].
  iIntros (G) ">QI". iDestruct "QI" as (?) "QI".
  iAaccIntro with "QI".
  { iIntros ">QI !>". iSplitL "QI"; [|by auto]. iNext. by iExists _. }
  iIntros (v V' Q' G' enqId deqId enq deq Venq Vdeq M') "(>QI & #⊒V' & #QL' & %F) !>".
  iAssert (QueueInv γg q G') with "[QI]" as "QI". { by iExists _. }
  iExists v, V', G', enqId, deqId, enq, deq, Vdeq. iExists M'.
  iFrame "QI QL' ⊒V'". iSplit; [|by auto]. iPureIntro. naive_solver.
Qed.

Lemma try_enq_spec :
  try_enq_spec' sq.(spec_abs_graph.try_enq) QueueLocal QueueInv.
Proof.
  intros N DISJ q tid γg G1 M V v Posx. iIntros "#⊒V #QL" (Φ) "AU".
  awp_apply (sq.(spec_abs_graph.try_enq_spec) with "⊒V QL"); [done..|].
  iApply (aacc_aupd_commit with "AU"); [done|].
  iIntros (G) ">QI". iDestruct "QI" as (?) "QI".
  iAaccIntro with "QI".
  { iIntros ">QI !>". iSplitL "QI"; [|by auto]. iNext. by iExists _. }
  iIntros (b V' Q' G' enqId enq Venq M') "(>QI & #⊒V' & #QL' & %F) !>".
  iAssert (QueueInv γg q G') with "[QI]" as "QI". { by iExists _. }
  destruct F as (? & ? & ? & ? & ?).
  iExists b, V', G', enqId, enq, Venq, M'. iFrame "QI QL' ⊒V'".
  iSplitL; [|by auto]. iPureIntro. destruct b; naive_solver.
Qed.

Lemma try_deq_spec :
  try_deq_spec' sq.(spec_abs_graph.try_deq) QueueLocal QueueInv.
Proof.
  intros N DISJ q tid γg G1 M V. iIntros "#⊒V #QL" (Φ) "AU".
  awp_apply (sq.(spec_abs_graph.try_deq_spec) with "⊒V QL"); [done..|].
  iApply (aacc_aupd_commit with "AU"); [done|].
  iIntros (G) ">QI". iDestruct "QI" as (?) "QI".
  iAaccIntro with "QI".
  { iIntros ">QI !>". iSplitL "QI"; [|by auto]. iNext. by iExists _. }
  iIntros (v V' Q' G' enqId deqId enq deq Venq Vdeq M') "(>QI & #⊒V' & #QL' & %F) !>".
  iAssert (QueueInv γg q G') with "[QI]" as "QI". { by iExists _. }
  iExists v, V', G', enqId, deqId, enq, deq, Vdeq. iExists M'.
  iFrame "QI QL' ⊒V'". iSplit; [|by auto]. iPureIntro. naive_solver.
Qed.

End abs_graph.

Definition abs_graph_graph_extended_queue_spec
  Σ `{!noprolG Σ, !inG Σ (graphR qevent)} {QC}
  (sq : spec_abs_graph.extended_queue_spec Σ QC)
  : spec_graph.extended_queue_spec Σ QC := {|
    spec_graph.extended_core_spec := {|
      spec_graph.QueueInv_Objective         := QueueInv_objective sq ;
      spec_graph.QueueInv_Timeless          := QueueInv_timeless sq ;
      spec_graph.QueueLocal_Persistent      := QueueLocal_persistent sq ;
      spec_graph.QueueInv_QueueConsistent   := QueueInv_StrongQueueConsistent_instance sq;
      spec_graph.QueueInv_graph_master_acc  := QueueInv_graph_master_acc_instance sq ;
      spec_graph.QueueLocal_graph_snap      := QueueLocal_graph_snap_instance sq ;
      spec_graph.new_queue_spec             := new_queue_spec sq ;
      spec_graph.enqueue_spec               := enqueue_spec sq ;
      spec_graph.dequeue_spec               := dequeue_spec sq ;
    |} ;
    spec_graph.try_enq_spec                 := try_enq_spec sq ;
    spec_graph.try_deq_spec                 := try_deq_spec sq ;
  |}%I.
