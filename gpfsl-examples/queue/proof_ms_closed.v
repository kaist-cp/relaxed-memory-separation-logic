From gpfsl.base_logic Require Import history. (* << for noprolG *)
From gpfsl.logic Require Import atomics.

From gpfsl.examples.queue Require Import
  proof_abs_graph_abs proof_abs_graph_graph proof_ms_abs_graph.

Definition msqueue_impl_abs_graph_strong
  Σ `{!noprolG Σ, !msqueueG Σ, !atomicG Σ} :
  spec_abs_graph.strong_queue_spec Σ := {|
    spec_abs_graph.extended_core_spec := {|
      spec_abs_graph.QueueInv_Objective := QueueInv_objective;
      spec_abs_graph.QueueInv_QueueConsistent := QueueInv_StrongQueueConsistent_instance;
      spec_abs_graph.QueueInv_graph_master_acc := QueueInv_graph_master_acc_instance;
      spec_abs_graph.QueueLocal_graph_snap := QueueLocal_graph_snap_instance;
      spec_abs_graph.QueueLocal_Persistent := QueueLocal_persistent;
      spec_abs_graph.new_queue_spec := new_queue_spec;
      spec_abs_graph.enqueue_spec := enqueue_spec;
      spec_abs_graph.dequeue_spec := dequeue_spec;
    |} ;
    spec_abs_graph.try_enq_spec := try_enq_spec;
    spec_abs_graph.try_deq_spec := try_deq_spec;
  |}.

Definition msqueue_impl_abs_graph_weak Σ `{!noprolG Σ, !msqueueG Σ, !atomicG Σ} :
  spec_abs_graph.weak_queue_spec Σ :=
  spec_abs_graph.strong_weak_queue_spec Σ (msqueue_impl_abs_graph_strong _).

Definition msqueue_impl_graph_strong Σ `{!noprolG Σ, !msqueueG Σ, !atomicG Σ} :
  spec_graph.strong_queue_spec Σ :=
  proof_abs_graph_graph.abs_graph_graph_extended_queue_spec Σ
    (msqueue_impl_abs_graph_strong Σ).

Definition msqueue_impl_graph_weak Σ `{!noprolG Σ, !msqueueG Σ, !atomicG Σ} :
  spec_graph.weak_queue_spec Σ :=
  proof_abs_graph_graph.abs_graph_graph_extended_queue_spec Σ
    (extended_strong_weak_queue_spec Σ (msqueue_impl_abs_graph_strong Σ)).

Definition msqueue_impl_abs Σ `{!noprolG Σ, !msqueueG Σ, !atomicG Σ} :
  spec_abs.queue_spec Σ :=
  proof_abs_graph_abs.abs_graph_abs_queue_spec Σ
    (extended_strong_weak_queue_spec Σ (msqueue_impl_abs_graph_strong Σ)).
