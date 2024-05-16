From iris.bi Require Import lib.fractional.
From iris.algebra Require Import excl auth.
From iris.proofmode Require Import tactics.

From gpfsl.algebra Require Import to_agree.
From gpfsl.logic Require Import logatom atomics invariants.

From gpfsl.logic Require Import new_delete.
From gpfsl.logic Require Import proofmode.

From gpfsl.examples Require Import uniq_token map_seq loc_helper.
From gpfsl.examples.exchanger Require Import spec_graph spec_graph_piggyback code.
From gpfsl.examples.exchanger Require Import proof_graph_piggyback.

Require Import iris.prelude.options.

Section from_piggyback.
Context Σ `{!noprolG Σ, !inG Σ (graphR xchg_event)}.
Context `(ex_spec : exchanger_piggyback_spec Σ).

Let EI : bool → vProp Σ := (λ _, True)%I.

Let ExchangerLocal' := spec_graph_piggyback.ExchangerLocal ex_spec EI.
Let ExchangerInv' := spec_graph_piggyback.ExchangerInv ex_spec.

Local Lemma ExchangerInv_ExchangerConsistent_instance :
  ExchangerInv_ExchangerConsistent' ExchangerLocal' ExchangerInv'.
Proof.
  iIntros (N) "* EI EL".
  iMod (fupd_mask_subseteq (↑N ∖ ↑xchgUN N)) as "Close"; [solve_ndisj|].
  iMod (spec_graph_piggyback.ExchangerInv_ExchangerConsistent with "EI EL")
    as "$".
  by iMod "Close" as "_".
Qed.

Local Lemma new_exchanger_ex_spec :
  new_exchanger_spec' ExchangerLocal' ExchangerInv'
                      (spec_graph_piggyback.new_exchanger ex_spec).
Proof.
  iIntros (N tid Φ) "T Post".
  iApply wp_fupd.
  iApply (spec_graph_piggyback.new_exchanger_spec ex_spec with "T").
  iIntros "!>" (γg ex) "[EI EL]".
  iMod ("EL" $! _ EI N) as "EL".
  iIntros "!>". iApply ("Post" with "[$EL $EI]").
Qed.

Local Lemma exchange_ex_spec :
  exchange_spec' ExchangerLocal' ExchangerInv'
                 (spec_graph_piggyback.exchange ex_spec).
Proof using All.
  iIntros (N DISJ x tid γg G1 M V v1 Posv1) "sV EL".
  iIntros (Φ) "AU".
  iMod (inv_alloc (xchgUN N) _ (EI true) with "[//]") as "IE".
  iApply (spec_graph_piggyback.exchange_spec ex_spec with "sV EL IE [] AU");
    [done..|].
  iIntros "!>".
  rewrite /exchange_AU_proof /atomic_update_proof /atomic_update_open /=.
  iIntros (b1 b2) "AU T".
  iAuIntro. iApply (aacc_aupd_commit with "AU"); [done|].
  iIntros (G) "Pre".
  iAaccIntro with "Pre"; first by eauto with iFrame.
  iIntros (V' G' xchg1 xchg2 v2 Vex1' Vex2' M') "(EI & sV' & HF & CASE) !>".
  iExists V', G', xchg1, xchg2. iExists v2, Vex1', Vex2', M'. iFrame.
  iSplitL.
  - iDestruct "CASE" as "[[F EL]|[F CASE]]".
    + iLeft. iFrame. iDestruct "F" as %?. iPureIntro. naive_solver.
    + iRight. iSplitL "F". { iDestruct "F" as %?. iPureIntro. naive_solver. }
      iDestruct "CASE" as "[[F EL]|[F EL]]".
      * iLeft. iFrame. iDestruct "F" as %?. iPureIntro. naive_solver.
      * iRight. iFrame. iDestruct "F" as %?. iPureIntro. naive_solver.
  - by iIntros "$".
Qed.

Definition exchanger_impl_from_piggyback :
  exchanger_spec Σ := {|
  spec_graph.ExchangerLocal := ExchangerLocal' ;
  spec_graph.ExchangerInv := ExchangerInv' ;

  spec_graph.ExchangerInv_Objective :=
    spec_graph_piggyback.ExchangerInv_Objective ex_spec;
  spec_graph.ExchangerInv_Timeless :=
    spec_graph_piggyback.ExchangerInv_Timeless ex_spec;
  spec_graph.ExchangerInv_Fractional :=
    spec_graph_piggyback.ExchangerInv_Fractional ex_spec;
  spec_graph.ExchangerInv_AsFractional :=
    spec_graph_piggyback.ExchangerInv_AsFractional ex_spec;

  spec_graph.ExchangerInv_ExchangerConsistent :=
    ExchangerInv_ExchangerConsistent_instance;

  spec_graph.ExchangerInv_graph_master_acc :=
    spec_graph_piggyback.ExchangerInv_graph_master_acc ex_spec;
  spec_graph.ExchangerInv_graph_snap :=
    spec_graph_piggyback.ExchangerInv_graph_snap ex_spec;
  spec_graph.ExchangerInv_agree :=
    spec_graph_piggyback.ExchangerInv_agree ex_spec;

  spec_graph.ExchangerLocal_Persistent :=
    spec_graph_piggyback.ExchangerLocal_Persistent ex_spec EI;
  spec_graph.ExchangerLocal_graph_snap :=
    spec_graph_piggyback.ExchangerLocal_graph_snap ex_spec EI;

  spec_graph.new_exchanger_spec := new_exchanger_ex_spec;
  spec_graph.exchange_spec := exchange_ex_spec;
|}.

End from_piggyback.

Definition exchanger_impl Σ `{!noprolG Σ, !xchgG Σ, !atomicG Σ} :
  exchanger_spec Σ :=
  exchanger_impl_from_piggyback Σ (proof_graph_piggyback.exchanger_impl Σ).
