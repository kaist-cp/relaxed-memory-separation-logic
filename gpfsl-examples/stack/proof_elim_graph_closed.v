From iris.algebra Require Import lib.mono_list.
From gpfsl.base_logic Require Import history. (* << for noprolG *)

From gpfsl.logic Require Import atomic_cmra.
From gpfsl.logic Require Import readonly_ptsto.

From gpfsl.examples.stack Require Import spec_graph.
From gpfsl.examples.stack Require Import proof_treiber_graph proof_elim_graph.
From gpfsl.examples.exchanger Require Import proof_graph_piggyback.

Require Import iris.prelude.options.

Definition elimination_stack_impl_closed
  `{!noprolG Σ, !tstackG Σ, !xchgG Σ, !atomicG Σ,
    !ro_ptstoG Σ, !inG Σ (mono_listR (leibnizO (event_id + event_id)))}
  : basic_stack_spec Σ
  := elimination_stack_impl Σ (extended_to_basic_stack_spec Σ (treiber_stack_impl Σ))
                              (exchanger_impl Σ).
