From iris.bi Require Import big_op lib.fractional.
From iris.proofmode Require Import tactics.

From gpfsl.logic Require Import logatom invariants.
From gpfsl.logic Require Import proofmode.

From gpfsl.examples Require Import gset_disj set_helper.
From gpfsl.examples.exchanger Require Import
  spec_graph_resource spec_graph_piggyback.

Require Import iris.prelude.options.

Local Open Scope Z.

Section derived.
Context {Σ} `{!noprolG Σ, !inG Σ (graphR xchg_event),
              !gset_disjARG Σ event_id}.
Context (ex : exchanger_piggyback_spec Σ).

Local Existing Instances
  ExchangerInv_Timeless
  ExchangerInv_Objective
  ExchangerInv_Fractional
  ExchangerInv_AsFractional
  ExchangerLocal_Persistent
  .

Local Notation vProp := (vProp Σ).
Implicit Type (P : Z → vProp) (N : namespace) (γ : gname).

Local Notation ExchangerInvB := (ExchangerInv).
Local Notation ExchangerLocalB := (ExchangerLocal).

Definition TradeResources γb P G : vProp :=
  [∗ list] e1 ↦ Ev ∈ G.(Es),
    match Ev with
    | mkGraphEvent (Exchange v1 v2) V1 _ =>
        ⌜ 0 ≤ v2 ⌝ →
        (* each successful event e1 that exchanges v1 gives up its P v1,
          so that its matching event e2 can trade their token for P v1 *)
          @{V1.(dv_in)} P v1 ∨
          (∀ e2, ⌜ (e1, e2) ∈ G.(so) ∨ e1 ∉ (elements G.(so)).*1 ∧ e2 = S e1 ⌝
            → GsetDisjFrag γb e2)
    end.

(* Our extension of the invariant: *)
Definition ResourceInv γb γg P : vProp :=
  ∃ G,
    (* (0) Base ExchangerInv *)
    ex.(ExchangerInvB) γg (1/2)%Qp G ∗
    (* (1) we maintain a set of tokens for successful exchange events *)
    GsetDisjAuth γb 1 (to_set G.(Es)) ∗
    (* (2) The resource P tied to a successfull exchange event *)
    TradeResources γb P G
    .

Instance ResourceInv_objective γb γg P : Objective (ResourceInv γb γg P).
Proof.
  rewrite /ResourceInv.
  apply exists_objective => ?.
  do 2 (apply sep_objective; [apply _|]).
  apply big_sepL_objective => e [[v1 v2] V M]. apply _.
Qed.

Definition ExchangerInv' : ExchangerInvT Σ :=
  (λ γg q G,
    (* (0) Base ExchangerInv *)
    ex.(ExchangerInvB) γg (q/2)%Qp G)%I
  .

Let EI γb γg P : bool → vProp := λ _, ResourceInv γb γg P.

Definition ExchangerLocal' P : ExchangerLocalNT Σ :=
  (λ N γg x G M,
    ∃ γb, ex.(ExchangerLocalB) (EI γb γg P) N γg x G M ∗
          inv (xchgUN N) (ResourceInv γb γg P))%I.

Global Instance ExchangerInv'_timeless :
  ∀ γg q G, Timeless (ExchangerInv' γg q G) := _.
Global Instance ExchangerInv'_objective :
  ∀ γg q G, Objective (ExchangerInv' γg q G) := _.
Global Instance ExchangerInv'_fractional :
  ∀ γg G, Fractional (λ q, ExchangerInv' γg q G).
Proof.
  intros γg G p q. rewrite /ExchangerInv' Qp.div_add_distr. apply : fractional.
Qed.
Global Instance ExchangerInv'_asfractional :
  ∀ γg q G, AsFractional (ExchangerInv' γg q G) (λ q, ExchangerInv' γg q G) q.
Proof. constructor; [done|apply _]. Qed.

Lemma ExchangerInv'_ExchangerConsistent_instance :
  ∀ P, ExchangerInv_ExchangerConsistent_piggyback (ExchangerLocal' P) ExchangerInv'.
Proof.
  iIntros "* I (%γb & EL & _)".
  iApply (ExchangerInv_ExchangerConsistent with "I EL").
Qed.

Lemma ExchangerInv'_graph_master_acc_instance :
  ExchangerInv_graph_master_acc' ExchangerInv'.
Proof. intros ??. apply ExchangerInv_graph_master_acc. Qed.

Lemma ExchangerInv'_graph_snap_instance : ExchangerInv_graph_snap' ExchangerInv'.
Proof. intros ??. apply ExchangerInv_graph_snap. Qed.

Lemma ExchangerInv'_agree_instance : ExchangerInv_agree' ExchangerInv'.
Proof. intros ????. apply ExchangerInv_agree. Qed.

Lemma ExchangerLocal'_graph_snap_instance :
  ∀ P N, ExchangerLocal_graph_snap' (ExchangerLocal' P N).
Proof.
  iIntros "* (%γb & EL & _)".
  iApply (ExchangerLocal_graph_snap with "EL").
Qed.

Global Instance ExchangerLocal'_persistent :
  ∀ P N γg x G M, Persistent (ExchangerLocal' P N γg x G M) := _.

Lemma new_exchanger_spec_derived P :
  new_exchanger_spec' (ExchangerLocal' P) ExchangerInv'
                      ex.(new_exchanger).
Proof.
  iIntros (N tid Φ) "T Post".
  iApply wp_fupd. iApply (new_exchanger_spec with "T").
  iIntros "!>" (γg x) "[[I1 I2] EL]".
  iMod GsetDisjAuth_alloc as (γb) "GA".
  iMod (inv_alloc (N.@"uinv") _ (ResourceInv γb γg P) with "[I1 GA]") as "II".
  { iNext. iExists ∅. iFrame. by rewrite /TradeResources big_sepL_nil. }
  iMod ("EL" $! _ (EI  γb γg P) N) as "EL".
  iIntros "!>". iApply ("Post" $! γg).
  iSplitR "I2"; iFrame. iExists _; iFrame.
Qed.

Lemma exchanger_resource_spec_derived :
  exchange_resource_spec' (ExchangerLocal') ExchangerInv'
                          ex.(exchange).
Proof.
  iIntros (P N DISJ x tid γg G1 M V v1 Posv1) "#sV #(%γb & EL & II)".
  iIntros (Φ) "AU". iApply wp_fupd.
  wp_apply (exchange_spec with "sV EL II [] AU"); [done..|].
  iIntros "!>" (b1 b2) "AU I".
  iAuIntro.
  iDestruct "I" as (G) "(>I & >GA & Ps)".
  iApply (aacc_aupd with "AU"); [solve_ndisj|].
  (* We do not have access eventgraph_consistent for G *)
  (* connecting our invariant and the AU *)
  iIntros (G') "[>I' P]".
  iDestruct (ExchangerInv_agree with "I I'") as %->.
  iCombine "I I'" as "I".
  iAaccIntro with "I".
  { (* peeking case *)
    iFrame "P". iIntros "[I I'] !>". iSplitL "I".
    - iNext. rewrite /ExchangerInv'. eauto with iFrame.
    - iIntros "$ !>". iNext. iExists G. eauto with iFrame. }
  (* committed case *)
  iIntros (V' G' e1 e2 v2 Ve1 Ve2 M') "([I I'] & #sV' & F & CASE)".
  iDestruct "F" as %(LeG' & LeM' & EqV & EqV' & Eqe1 & EqG' & InM' & NIne1).
  have FRe1': G.(Es) !! e1 = None. { rewrite Eqe1. by apply lookup_ge_None. }
  have FRe1 : e1 ∉ to_set G.(Es).
  { rewrite Eqe1. clear. intros ?%elem_of_set_seq. lia. }
  (* update our ghost state *)
  iMod (GsetDisjAuth_insert _ _ e1 with "GA") as "[GA Tok1]"; [done|].
  have EqL : length G'.(Es) = S (length G.(Es)). { rewrite EqG' app_length /=. lia. }
  iIntros "!>". iRight.
  iExists V', G', e1, e2. iExists v2, Ve1, Ve2, M'. iFrame "I sV'".
  (* case distinction *)
  iDestruct "CASE" as "[[#F2 #EL']|[#F2 #CASE]]".
  { (* Exchange fail case *)
    iDestruct "F2" as %(-> & Eqso' & Eqco').
    iSplitL "P".
    { iSplit; [by iPureIntro|]. iLeft. iSplitR; [iPureIntro; naive_solver|].
      iFrame "P". iExists γb. by iFrame "EL' II". }
    iIntros "HΦ !>". iSplitR "GA I' Ps".
    - iIntros "_ !>". iApply "HΦ". iIntros ([]). lia.
    - iNext. iExists G'. rewrite EqG' to_set_append -Eqe1. iFrame "I' GA".
      rewrite {2}/TradeResources EqG' big_sepL_app Eqso' big_sepL_singleton.
      iFrame "Ps". iIntros (?). lia. }

  (* Exchange succeeds case *)
  iDestruct "F2" as %(Posv2 & MAXe2 & InM2' & NIne2  & NEqe2 & ORD & ?).
  iDestruct "CASE" as "[[%F' EL']|[%F' EL']]".
  - (* my event is later *)
    destruct F' as (Lt21 & ? & Eqe2 & Eqso' & Eqco' & NIe1 & NIe2 & EGCs' & CON').
    have Insom: (e2, e1) ∈ so G'. { rewrite Eqso'. set_solver-. }
    have EqS: e1 = S e2.
    { rewrite (xchg_cons_so_com _ CON') in Insom.
      destruct (xchg_cons_matches _ CON' _ _ Insom) as [[?|?] _]; [lia|done]. }
    iAssert (▷ ((@{Ve2.(dv_in)} P v2) ∗ TradeResources γb P G'))%I
      with "[Ps P Tok1]" as "[P Ps]".
    { iNext.
      iDestruct (big_sepL_lookup_acc _ _ _ _ Eqe2 with "Ps") as "[P2 Ps]".
      iDestruct ("P2" with "[//]") as "[P2|P2]"; last first.
      { (* P v2 cannot have been extracted, we still own the token *)
        iDestruct ("P2" $! e1 with "[%]") as "Tok1'". { by right. }
        by iDestruct (GsetDisjFrag_disj with "Tok1 Tok1'") as %?. }
      iFrame "P2".
      iSpecialize ("Ps" with "[Tok1]").
      { iIntros "_". iRight. iIntros (e1' [Ine1'|[_ Eqe1']]).
        - exfalso. apply NIe2, elem_of_list_fmap.
          exists (e2, e1'). split; [done|]. by apply elem_of_elements.
        - rewrite -Eqe1' in EqS. subst e1' e1. rewrite EqS. by iFrame "Tok1". }
      rewrite /TradeResources EqG' big_sepL_app big_sepL_singleton.
      iSplitR "P"; last first. { iIntros "_". iLeft. rewrite EqV. by iFrame "P". }
      iApply (big_sepL_mono with "Ps").
      intros ei [[vi vj] Vi Mi] Eqei. iIntros "HP" (Posvj).
      iDestruct ("HP" $! Posvj) as "[Pi|HPi]".
      { iLeft. by iFrame "Pi". }
      iRight. iIntros (ej Inj). iApply "HPi". iPureIntro.
      move : Inj. rewrite {1}Eqso' !elem_of_union !elem_of_singleton.
      intros [[[Eq12|Eq21]|InGso]|[NInGso' EqS']].
      - inversion Eq12. subst ei ej. by rewrite FRe1' in Eqei.
      - inversion Eq21. subst ei ej. by right.
      - by left.
      - right. split; [|done]. intros (eij & Eqij & InSo)%elem_of_list_fmap.
        apply NInGso', elem_of_list_fmap. exists eij. split; [done|].
        rewrite Eqso'. set_solver+InSo. }
    iSplitL "P".
    { iSplit; [done|]. iRight. iSplit; [done|]. iLeft. iSplit; [done|].
      iSplitR. { iExists γb. by iFrame "EL' II". }
      rewrite (xchg_cons_so_com _ CON') in Insom.
      destruct (xchg_cons_matches _ CON' _ _ Insom)
        as (EqS' & eV2 & eV1 & _ & _ & EqeV2 & EqeV1 & _ & _ & _ & _ & LtV2 & _).
      rewrite EqG' Eqe1 lookup_app_1_eq in EqeV1;
        inversion EqeV1; clear EqeV1; subst eV1.
      rewrite EqG' lookup_app_1_ne in EqeV2; last by rewrite -Eqe1.
      rewrite Eqe2 in EqeV2; inversion EqeV2; clear EqeV2; subst eV2.
      rewrite /= EqV' in LtV2. iClear "#"; clear -LtV2. iNext.
      apply strict_include in LtV2. by iFrame "P". }
    iIntros "HΦ !>".
    iSplitR "GA I' Ps".
    + iIntros "_ !>". iApply "HΦ". iIntros ([_ ?]). lia.
    + iNext. iExists G'. rewrite EqG' to_set_append -Eqe1. iFrame "I' Ps GA".

  - (* my event is earlier. First put P v1 in our invariant to close it. *)
    destruct F' as (Lt12 & ? & Eqso' & Eqco').
    iSplitR.
    { iSplit; [done|]. iRight. iSplit; [by iPureIntro|]. iRight.
      iSplit; [done|]. iExists γb. by iFrame "EL' II". }
    iIntros "HΦ !>".
    iSplitR "Ps P GA I'"; last first.
    { iNext. iExists G'. rewrite EqG' to_set_append -Eqe1. iFrame "I' GA".
      rewrite /TradeResources EqG' big_sepL_app Eqso' big_sepL_singleton.
      iFrame "Ps". iIntros (_). iLeft. rewrite EqV. iFrame "P". }

    (* then in the private post condition, open our invariant to get P v2 *)
    iIntros "Post". iDestruct ("Post" with "[%//]") as (G'' F'') "#EL''".
    destruct F'' as (LeG'' & Eqe2 & EqG'' & Eqso'' & Eqco'' & NIe1 & NIe2).
    (* opening our invariant *)
    iInv "II" as (Gm) "(>I & GA & Ps)" "HClose".
    (* first, get some facts *)
    iDestruct (view_at_elim with "sV' EL''") as "#EL2".
    iDestruct (ExchangerInv_graph_snap with "I []") as %SubG''.
    { iApply (ExchangerLocal_graph_snap with "EL2"). }
    have EqEm2: Gm.(Es) !! e2 = Some (mkGraphEvent (Exchange v2 v1) Ve2 M').
    { eapply prefix_lookup_Some; [|apply SubG'']. by rewrite EqG'' Eqe2 lookup_app_1_eq. }
    have Insom: (e2, e1) ∈ so Gm. { apply SubG''. rewrite Eqso''. set_solver-. }

    (* now we extract P v2 *)
    rewrite /TradeResources (big_sepL_lookup_acc _ _ _ _ EqEm2).
    iDestruct "Ps" as "[P2 Ps]".
    iDestruct ("P2" with "[//]") as "[P2|P2]"; last first.
    { (* P v2 cannot have been extracted, we still own the token *)
      iDestruct ("P2" $! e1 with "[%]") as ">Tok1'". { by left. }
      by iDestruct (GsetDisjFrag_disj with "Tok1 Tok1'") as %?. }

    (* now we got P v2, we also need consistency of (Gm, Em) to get P v2 in the
      right view *)
    iMod (fupd_mask_subseteq (↑N ∖ ↑xchgUN N)) as "HClose2"; [solve_ndisj|].
    iMod (ExchangerInv_ExchangerConsistent with "I EL2") as "[F I]".
    iMod "HClose2" as "_". iDestruct "F" as %[EGCm CONm].
    (* now we close the invariant first *)
    (* first, complete the trading of resources. *)
    iSpecialize ("Ps" with "[Tok1]").
    { iIntros "!> _". iRight. iIntros (e1' InGm').
      (* thanks to Consistency, we learn that e1' = e1. So we can finish the
        trading by putting the token in in place for P v2 *)
        destruct InGm' as [InGm'|[NIn _]]; last first.
        { exfalso. apply NIn, elem_of_list_fmap. exists (e2, e1).
          split; [done|]. by apply elem_of_elements. }
        destruct (xchg_cons_com_functional _ CONm) as [FUN1 _].
        rewrite -(xchg_cons_so_com _ CONm) in FUN1.
        specialize (FUN1 _ _ Insom InGm' eq_refl). simpl in FUN1. subst e1'.
        by iFrame "Tok1". }
    (* now we can close the invariant *)
    iMod ("HClose" with "[I GA Ps]") as "_".
    { iNext. iExists Gm. by iFrame. }

    iApply "HΦ". iIntros "!> _".
    iExists G''. iSplit; [done|].
    iSplitR "P2". { iExists γb. by iFrame "EL'' II". }
    (* with Consistency, we learn that Ve2.(dv_in) ⊑ V' *)
    have EqEm1: Gm.(Es) !! e1 = Some (mkGraphEvent (Exchange v1 v2) Ve1 M').
    { eapply prefix_lookup_Some; [|apply SubG''].
      rewrite EqG'' lookup_app_1_ne; [|by rewrite -Eqe2].
      by rewrite EqG' Eqe1 lookup_app_1_eq. }
    rewrite (xchg_cons_so_com _ CONm) in Insom.
    destruct (xchg_cons_matches _ CONm _ _ Insom)
      as (EqS & eV2 & eV1 & _ & _ & EqeV2 & EqeV1 & _ & _ & _ & _ & LtV2 & _).
    rewrite EqEm2 in EqeV2; inversion EqeV2; clear EqeV2; subst eV2.
    rewrite EqEm1 in EqeV1; inversion EqeV1; clear EqeV1; subst eV1.
    rewrite /= EqV' in LtV2. iClear "#"; clear -LtV2. iNext.
    apply strict_include in LtV2. by iFrame "P2".
Qed.
End derived.

Definition exchanger_resource_impl
  Σ `{!noprolG Σ, !inG Σ (graphR xchg_event), !gset_disjARG Σ event_id}
  (ex : exchanger_piggyback_spec Σ) :
    exchanger_resource_spec Σ := {|
  spec_graph_resource.ExchangerInv_Objective := (ExchangerInv'_objective ex);
  spec_graph_resource.ExchangerInv_ExchangerConsistent :=
    (ExchangerInv'_ExchangerConsistent_instance ex);
  spec_graph_resource.ExchangerInv_graph_master_acc :=
    (ExchangerInv'_graph_master_acc_instance ex);
  spec_graph_resource.ExchangerInv_graph_snap := (ExchangerInv'_graph_snap_instance ex);
  spec_graph_resource.ExchangerInv_agree := (ExchangerInv'_agree_instance ex);
  spec_graph_resource.ExchangerLocal_graph_snap := (ExchangerLocal'_graph_snap_instance ex);
  spec_graph_resource.ExchangerLocal_Persistent := (ExchangerLocal'_persistent ex);
  spec_graph_resource.new_exchanger_spec := (new_exchanger_spec_derived ex);
  spec_graph_resource.exchange_spec := (exchanger_resource_spec_derived ex);
|}.
