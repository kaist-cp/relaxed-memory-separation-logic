From gpfsl.base_logic Require Import history. (* << for noprolG *)

From gpfsl.logic Require Import atomic_cmra.

From gpfsl.examples Require Import gset_disj.
From gpfsl.examples.exchanger Require Import spec_graph_resource.
From gpfsl.examples.exchanger Require Import proof_graph_resource proof_graph_piggyback.

Require Import iris.prelude.options.

Definition exchanger_resource_impl_closed
  Σ `{!noprolG Σ, !noprolG Σ, !xchgG Σ, !atomicG Σ, !gset_disjARG Σ event_id} :
  exchanger_resource_spec Σ :=
  exchanger_resource_impl Σ (proof_graph_piggyback.exchanger_impl Σ).
