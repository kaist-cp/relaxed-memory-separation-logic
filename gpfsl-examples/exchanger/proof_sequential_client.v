From iris.algebra Require Import excl_auth.
From gpfsl.logic Require Import logatom invariants proofmode.

From gpfsl.examples.graph Require Import spec.
From gpfsl.examples.exchanger Require Import spec_graph.

Require Import iris.prelude.options.

Local Notation event_list := (event_list xchg_event).
Local Notation graph := (graph xchg_event).

Section sequential.
Context `{!noprolG Σ, !inG Σ (graphR xchg_event)}.
Context `(ex : exchanger_spec Σ).
Notation vProp := (vProp Σ).

Implicit Types (G : graph) (E : event_list).
Implicit Types (γ : gname).

(** A single call of exchange with full permission (i.e. sequentially with no
  interference) is doomed to fail. *) 
(* TODO : we shouldn't need to assume Σ and co to write this code.
  The spec pattern needs rework. *)
(* We need the let binding to buy us some more steps *)
Definition sequential_1 : val :=
  λ: ["ex"; "v"],
  let: "a" := ex.(exchange) [ "ex" ; "v" ] in
  "a"
  .

Section sequential_1.
Local Existing Instance ExchangerInv_Objective.
Local Existing Instance ExchangerInv_Timeless.
Local Existing Instance ExchangerLocal_Persistent.

Lemma sequential_1_spec N (DISJ: N ## histN)
  γg G M (e : loc) (v : Z) tid :
  {{{ ⌜ 0 ≤ v ⌝ ∗
      ex.(ExchangerLocal) N γg e G M ∗ ex.(ExchangerInv) γg 1%Qp G }}}
    sequential_1 [ #e; #v ] @ tid; ⊤
  {{{ RET #CANCELLED;
      ∃ G' M' Vx xchg,
        ⌜ G'.(Es) = G.(Es) ++ [mkGraphEvent (Exchange v CANCELLED) Vx M'] ∧
          G'.(so) = G.(so) ∧ G'.(com) = G.(com) ∧
          xchg ∈ M' ∧ xchg ∉ M ∧ M ⊑ M' ⌝ ∧
        ex.(ExchangerLocal) N γg e G' M' ∗ ex.(ExchangerInv) γg 1%Qp G' }}}.
Proof.
  iIntros (Φ) "[%Ge0 [#eL eI]] Post".
  wp_lam.

  (* Use the exchanger spec *)
  iDestruct (view_at_intro True%I with "[//]") as (V0) "[#sV0 x1]".
  awp_apply (ex.(exchange_spec) with "sV0 eL"); [done..|].
  rewrite /atomic_acc /=.
  (* Open extra masks to match the masks *)
  iMod (fupd_mask_subseteq (↑histN)) as "Close2"; [solve_ndisj|].
  (* now we can provide the public (atomic) precondition *)
  iIntros "!>". iExists _. iFrame "eI".
  (* the public (atomic) postcondition *)
  iSplit.
  { (* Peeking case: nothing change *)
    iIntros ">EI". iMod "Close2" as "_". by iFrame. }

  (* COMMITed case. If SUCCEED, we need to derive a contradiction *)
  iIntros (V1 G1 xchg1 xchg2 v2 Vx1 Vx2 M1) "(>EI & #sV1 & %F & CASE)".
  destruct F as (SubG' & SubM & EqV0 & EqV1 & Eqxchg1 & EqEs1 & InM1 & NInM1).

  (* Close other masks *)
  iMod "Close2" as "_".

  (* Case analysis on the result of the exchange *)
  iIntros "!> Hv2".
  iDestruct "CASE" as "[[F EL]|[F CASE]]".
  - (* Expected case: FAILURE. *)
    iDestruct "F" as %(-> & EqSo & EqCo & ? & ?).
    wp_let. iApply "Post". iExists G1, M1, Vx1, xchg1.
    iDestruct (view_at_elim with "sV1 EL") as "$". by iFrame "EI".
  - (* Impossible case: SUCCEED.
      In this case, the other AU of the other player is applied immediately,
      then we get the private postcondition, from which we derive a
      contradiction. All of this is done right after the call, so it's actually
      can be done right after the commit (COMM) point. *)
    iDestruct "F" as %(Lev2 & MAX2 & In2 & NInM2 & NEq2 & ?).
    iAssert (∃ G'', ⌜ com G'' = {[(xchg1, xchg2); (xchg2, xchg1)]} ∪ com G ⌝
                ∗ ExchangerLocal ex N γg e G'' M1)%I with "[CASE Hv2]"
                as (G2 EqCo2) "EL".
    { iDestruct "CASE" as "[[F EL]|[F EL]]".
      - iDestruct "F" as %(Lt & InG & _ & EqCo1 & _).
        iExists G1. by iDestruct (view_at_elim with "sV1 EL") as "$".
      - iDestruct "F" as %(Lt & ?).
        iDestruct ("Hv2" with "[%//]") as (G2 (_ & Eqx2 & _ & _ & ? & _)) "EL'".
        iExists G2. by iDestruct (view_at_elim with "sV1 EL'") as "$". }
    iDestruct (ExchangerLocal_graph_snap with "EL") as "#Gs2".
    (* get the right mask to access the exchanger's internal invariant. *)
    iApply fupd_wp. iMod (fupd_mask_subseteq (↑N)); [solve_ndisj|].
    iMod (ExchangerInv_ExchangerConsistent with "EI EL") as "[[%EGs %EC] EI]".
    iDestruct (ExchangerInv_graph_snap with "EI Gs2") as %LeG2.
    exfalso.
    (* We learn that xchg1 and xchg2 are new events inserted into G to get G1,
      but G1 only has 1 extra event compared to G. So xchg1 = xchg2.
      But [ExchangerConsistent] says that successful exchange pairs are irreflexive.
      Contradiction. *)
    have LtL1 : (xchg2 < length G1.(Es))%nat.
    { apply (gcons_com_included G1 (xchg1, xchg2)), LeG2. rewrite EqCo2. set_solver-. }
    have EqL: length G1.(Es) = S (length G.(Es)).
    { rewrite EqEs1 app_length /=. lia. }
    clear -Eqxchg1 NEq2 LtL1 EqL MAX2. lia.
Qed.
End sequential_1.

(* Then we can easily prove that if we sequentially call exchange twice, it fails twice. *)
(* TODO : we shouldn't need to assume Σ and co to write this code.
  The spec pattern needs rework. *)
Definition sequential_2 : val :=
  λ: ["ex"; "v1"; "v2"],
  let: "a" := sequential_1 [ "ex" ; "v1" ] in
  let: "b" := sequential_1 [ "ex" ; "v2" ] in
  if: "a" = #CANCELLED then
    if: "b" = #CANCELLED then #true else #false
  else #false
  .

Section sequential_2.
Lemma sequential_2_spec N (DISJ: N ## histN) γg G M (e : loc) (v1 v2 : Z) tid :
  {{{ ⌜ 0 ≤ v1 ∧ 0 ≤ v2 ⌝ ∗
      ex.(ExchangerLocal) N γg e G M ∗ ex.(ExchangerInv) γg 1%Qp G }}}
    sequential_2 [ #e; #v1 ; #v2 ] @ tid; ⊤
  {{{ RET #true;
        ∃ G' M',
        ex.(ExchangerLocal) N γg e G' M' ∗ ex.(ExchangerInv) γg 1%Qp G' }}}.
Proof.
  iIntros (Φ) "([%Ge01 %Ge02] & EL & EI) Post".
  wp_lam.
  wp_apply (sequential_1_spec with "[$EL $EI]"); [eauto..|].
  iDestruct 1 as (G1 M1 Vx1 xchg1 F1) "[EL EI]".
  wp_let.
  wp_apply (sequential_1_spec with "[$EL $EI]"); [eauto..|].
  iDestruct 1 as (G2 M2 Vx2 xchg2 F2) "[EL EI]".
  wp_let. wp_op. wp_if. wp_op. wp_if.
  iApply "Post". iExists G2, M2. by iFrame.
Qed.
End sequential_2.
End sequential.
