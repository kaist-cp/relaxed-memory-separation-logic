From iris.algebra Require Import auth numbers.
From iris.proofmode Require Import tactics.

From gpfsl.lang Require Import notation.
From gpfsl.logic Require Import atomics.
From gpfsl.logic Require Import logatom invariants proofmode.
From gpfsl.logic Require Import new_delete repeat_loop.

From gpfsl.examples.queue Require Import spec_graph.
From gpfsl.examples Require Import set_helper.

Require Import iris.prelude.options.

Local Notation graph := (graph qevent).

Implicit Types (G : graph).

Section spmc_mp.
Context `{!noprolG Σ,
          !atomicG Σ,
          !inG Σ (graphR qevent),
          !inG Σ (authR natUR)}.
Context (mpN qN : namespace)
        (DISJ1: mpN ## histN) (DISJ2: qN ## histN) (DISJ3: mpN ## qN).

Hypothesis Q : weak_queue_spec Σ.
Local Existing Instances QueueInv_Objective QueueLocal_Persistent.

Local Notation iProp := (iProp Σ).
Local Notation vProp := (vProp Σ).

Definition spmc_mp : expr :=
  let: "q" := Q.(new_queue) [] in
  let: "flag" := new [ #1] in
  "flag" <- #0 ;;

  Fork                    (**)                       (**) (Q.(enqueue) ["q"; #1] ;;
                          (**)                       (**)  Q.(enqueue) ["q"; #2] ;;
                          (**)                       (**)  "flag" <-ʳᵉˡ #1 ) ;;
                          (**)                       (**)
  Fork                    (**) (Q.(dequeue) ["q"]);; (**)
                          (**)                       (**)
  (repeat: !ᵃᶜ "flag") ;; (**)                       (**)
  Q.(dequeue) ["q"]       (**)                       (**)
  .


(** The flag location transfers the knowledge about the enqueue events. *)
Definition FlagProtocol γg γf q f : vProp :=
  (∃ ζ (b : bool) t0 V0 Vx,
    @{Vx} (f sw↦{γf} ζ) ∗
    let ζ0 : absHist := {[t0 := (#0, V0)]} in
    match b with
    | false => ⌜ζ = ζ0⌝
    | true => ∃ t1 V1, ⌜(t0 < t1)%positive ∧ ζ = <[t1 := (#1, V1)]>ζ0⌝ ∗
              ∃ G M e1 e2 eV1 eV2,
              @{V1} (Q.(QueueLocal) qN γg q G M) ∗
              ⌜ e1 ≠ e2 ∧
                G.(Es) !! e1 = Some eV1 ∧ G.(Es) !! e2 = Some eV2 ∧
                eV1.(ge_event) = Enq 1 ∧ eV2.(ge_event) = Enq 2 ∧
                e1 ∈ M ∧ e2 ∈ M ⌝
    end
  )%I.

(** Invariant on the queue state:
- A successful dequeue consumes a token [◯ 1].
- There are only 2 such tokens.
- Only the values 1 or 2 are enqueued. *)
Definition MPInv γg γm γf q f : vProp := ∃ G,
  FlagProtocol γg γf q f ∗
  Q.(QueueInv) γg q G ∗
  ⎡ own γm (● 2%nat) ⎤ ∗
  ⎡ own γm (◯ (size G.(com))) ⎤ ∗
  ⌜ ∀ e eV v, G.(Es) !! e = Some eV → eV.(ge_event) = Enq v → v = 1 ∨ v = 2 ⌝
  .

Local Instance MPInv_objective γg γm γf q f : Objective (MPInv γg γm γf q f).
Proof.
  apply exists_objective => ?. apply sep_objective; [|apply _].
  apply exists_objective => ?. apply exists_objective => [[]]; apply _.
Qed.

Lemma spmc_mp_spec tid :
  {{{ True }}} spmc_mp @ tid; ⊤ {{{ v, RET #v; ⌜v = 1 ∨ v = 2⌝ }}}.
Proof using All.
  iIntros (Φ) "_ Post".
  rewrite /spmc_mp.

  wp_apply (new_queue_spec _ qN with "[//]").
  iIntros (γg q) "[#QL QI]".
  iMod (own_alloc ((● 2%nat ⋅ ◯ 0%nat) ⋅ (◯ 1%nat ⋅ ◯ 1%nat))) as (γm) "[●m [◯m1 ◯m2]]".
  { rewrite -assoc -!auth_frag_op !nat_op /=. by apply auth_both_valid. }
  wp_let.
  wp_apply wp_new; [done..|].
  iIntros (f) "(_ & f↦ & _)". rewrite own_loc_na_vec_singleton.
  wp_let. wp_write.

  (* setup the invariant and the protocol *)
  iMod (AtomicPtsTo_from_na with "f↦") as (γf t Vf0) "(#sVf0 & FPW & Ptsf)".
  iDestruct (AtomicSWriter_AtomicSync with "FPW") as "#FPR".
  iDestruct (view_at_intro with "Ptsf") as (Vf) "[sVf Ptsf]".
  iMod (inv_alloc mpN _ (MPInv γg γm γf q f) with "[QI ●m Ptsf]") as "#I".
  { iNext. iExists ∅. iFrame "QI". rewrite size_empty. iDestruct "●m" as "[$ $]".
    iSplit; [|done].
    iExists _, false, t, Vf0, Vf. by iFrame "Ptsf". }

  (* enqueuing thread *)
  wp_apply (wp_fork with "[FPW]"); [done|..].
  { iIntros "!>" (?).
    (* enqueue 1 *)
    iDestruct (monPred_in_intro True%I with "[//]") as (V) "[#⊒V _]".
    awp_apply (enqueue_spec with "⊒V QL"); [solve_ndisj|done|].
    iInv mpN as (G1) "(FI & QI & >●m & >◯m & >%Hv)".
    iAaccIntro with "QI".
    { iFrame. iIntros "QI !> !>". iExists _. iFrame. done. }
    iIntros (V1 G1' enqId1 enq1 Venq1 M1') "(QI & #⊒V1 & #QL1 & %F) !>".
    set (eV1 := mkGraphEvent enq1 Venq1 M1') in *.
    rewrite /is_enqueue in F.
    destruct F as (SubG11' &_&_&_& -> & ? & EsG1' &_& ComG1' & InM1' &_).
    have HeV1 : G1'.(Es) !! enqId1 = Some eV1.
    { subst enqId1. rewrite EsG1'. apply lookup_app_1_eq. }
    iDestruct (view_at_elim with "⊒V1 QL1") as "{QL QL1} QL1".
    iSplitR "FPW".
    { iNext. iExists G1'. rewrite -ComG1'. iFrame. iPureIntro.
      rewrite EsG1'. intros ??? [?|[-> <-]]%lookup_app_1; [by eapply Hv|].
      injection 1 as <-. by left. }
    clear Hv. iIntros "_". wp_seq.
    (* enqueue 2 *)
    awp_apply (enqueue_spec with "⊒V QL1"); [solve_ndisj|done|].
    iInv mpN as (G2) "(FI & QI & >●m & >◯m & >%Hv)".
    rewrite QueueInv_graph_master_acc. iDestruct "QI" as "[>Gm QI]".
    iDestruct (graph_master_consistent with "Gm") as %EGC.
    iPoseProof (QueueLocal_graph_snap with "QL1") as "Gs".
    iDestruct (graph_master_snap_included with "Gm Gs") as %SubG1'2.
    iSpecialize ("QI" with "[$Gm]").
    iAaccIntro with "QI".
    { iFrame. iIntros "QI !> !>". iExists _. iFrame. done. }
    iIntros (V2 G2' enqId2 enq2 Venq2 M2') "(QI & #⊒V2 & #QL2 & %F) !>".
    set (eV2 := mkGraphEvent enq2 Venq2 M2') in *.
    rewrite /is_enqueue in F.
    destruct F as (SubG22' & SubM1'2' &_&_& -> & ? & EsG2' &_& ComG2' & InM2' &_).
    have HeV2 : G2'.(Es) !! enqId2 = Some eV2.
    { subst enqId2. rewrite EsG2'. apply lookup_app_1_eq. }
    iDestruct (view_at_elim with "⊒V2 QL2") as "{QL2} QL2".
    iSplitR "FPW".
    { iNext. iExists G2'. rewrite -ComG2'. iFrame. iPureIntro.
      rewrite EsG2'. intros ??? [?|[-> <-]]%lookup_app_1; [by eapply Hv|].
      injection 1 as <-. by right. }
    iIntros "_". wp_seq.
    (* set the flag *)
    (* open shared invariant *)
    iInv mpN as (G3) "(FI & QI)" "Close".
    iDestruct "FI" as (ζ' b t0 V0 Vx0) "[>Pts _]".
    iDestruct (AtomicPtsTo_AtomicSWriter_agree_1 with "Pts FPW") as %->.
    (* actualy write of flag *)
    iApply (AtomicSWriter_release_write _ _ _ _ V Vx0 #1
                                        (QueueLocal Q qN γg q G2' M2')
              with "[$FPW $Pts $QL2 $⊒V]"); [solve_ndisj|..].
    iIntros "!>" (t1' V1') "(%MAX & SeenV' & [QL2' FPW'] & Pts')".
    (* reestablishing the invariant *)
    iMod ("Close" with "[-]"); last done.
    iIntros "!>". iExists G3. iFrame "QI".
    iExists _, true, t, Vf0, _. iFrame "Pts'".
    iExists t1', V1'. iSplit.
    { iPureIntro. split; [|done]. apply MAX. rewrite lookup_insert. by eexists. }
    iExists G2', M2', enqId1, enqId2, eV1, eV2. iFrame "QL2'".
    iPureIntro. split_and!; [| |done|done|done| |done].
    - subst enqId1 enqId2.
      have ? : (length (Es G1) < length (Es G1')).
      { rewrite EsG1' app_length /=. lia.  }
      suff ? : (length (Es G1') ≤ length (Es G2))%nat by lia.
      apply prefix_length. by destruct SubG1'2.
    - eapply prefix_lookup_Some; [done|].
      destruct SubG1'2, SubG22'. by trans G2.(Es).
    - set_solver +InM1' SubM1'2'. }

  iIntros "_". wp_seq.

  (* dequeuing thread *)
  wp_apply (wp_fork with "[◯m1]"); [done|..].
  { iIntros "!>" (?).
    iDestruct (monPred_in_intro True%I with "[//]") as (V) "[#⊒V _]".
    awp_apply (dequeue_spec with "⊒V QL"); [solve_ndisj|].
    iInv mpN as (G) "(FI & QI & >●m & >◯m & >%Hv)".
    iDestruct (QueueInv_QueueConsistent with "QI") as "#>%QC".
    iAaccIntro with "QI".
    { iFrame. iIntros "QI !> !>". iExists _. iFrame. done. }
    iIntros (v V' G' enqId deqId enq deq Vdeq M') "(QI & #⊒V' & #QL' & %F) !>".
    iSplitL; last by iIntros. iNext. iExists G'.
    set (dV := mkGraphEvent deq Vdeq M') in *.
    destruct F as (SubG' & SubM' & HVin & HVcomm & [CASE|CASE]).
    - destruct CASE as (_& -> &_& EsG' &_& ComG' &_).
      rewrite ComG'. iFrame. iPureIntro.
      rewrite EsG'. intros ??? [?|[-> <-]]%lookup_app_1; [by eapply Hv|done].
    - destruct CASE as (_& -> & -> &_& NoSo & EsG' &_& ComG' & _).
      iFrame. iCombine "◯m ◯m1" as "◯m".
      rewrite ComG' size_union.
      + rewrite size_singleton (comm plus). iFrame. iPureIntro.
        rewrite EsG'. intros ??? [?|[-> <-]]%lookup_app_1; [by eapply Hv|done].
      + apply disjoint_singleton_l. rewrite -(bsq_cons_so_com _ QC).
        by apply NoSo. }
  iIntros "_". wp_seq.

  (* main thread *)
  iClear "QL".
  (* wait for the flag to be set *)
  wp_bind (repeat: _)%E.
  iLöb as "IH".
  iApply wp_repeat; [done|].

  (* open shared invariant *)
  iInv mpN as (G3) "(FI & QI)" "Close".
  iDestruct "FI" as (ζ' b t0 V0 Vx0) "[>Pts Own]".
  (* actual read *)
  iApply (AtomicSeen_acquire_read with "[$Pts $sVf0]"); [solve_ndisj|..].
  { by iApply (AtomicSync_AtomicSeen with "FPR"). }
  iIntros "!>" (t' v' V' V'' ζ'') "(HF & SV' & SN' & Pts)".
  iDestruct "HF" as %([Sub1 Sub2] & Eqt' & MAX' & LeV'').

  case (decide (t' = t0)) => [?|NEqt'].
  { (* keep looping *)
    subst t'.
    (* we must have read the flag to be 0 (i.e. z = 0). *)
    iAssert (⌜v' = #0⌝)%I as %Eq0.
    { destruct b.
      - iDestruct "Own" as (t1 V1 [Lt1 Eqζ']) "_".
        iPureIntro.
        rewrite Eqζ' in Sub2. apply (lookup_weaken _ _ _ _ Eqt') in Sub2.
        rewrite lookup_insert_ne in Sub2.
        + rewrite lookup_insert in Sub2. by inversion Sub2.
        + clear -Lt1. intros ?. subst. lia.
      - iDestruct "Own" as %Eqζ'. iPureIntro.
        rewrite Eqζ' in Sub2. apply (lookup_weaken _ _ _ _ Eqt') in Sub2.
        rewrite lookup_insert in Sub2. by inversion Sub2. }
    (* then simply keep looping *)
    (* first close the invariant *)
    iMod ("Close" with "[Pts Own QI]").
    { iIntros "!>". iExists G3. iFrame "QI". iExists ζ', b, t0, V0, _. by iFrame. }
    iIntros "!>". iExists 0. iSplit; [done|].
    (* then apply the Löb IH *)
    iIntros "!> !>". by iApply ("IH" with "Post ◯m2"). }

  destruct b; last first.
  { (* b cannot be false *)
    iDestruct "Own" as %Eqζ'. exfalso.
    rewrite Eqζ' in Sub2.
    apply (lookup_weaken _ _ _ _ Eqt'), lookup_singleton_Some in Sub2 as [].
    by apply NEqt'. }
  (* done looping *)
  iClear "IH FPR ".

  iDestruct "Own" as (t1 V1 [Lt1 Eqζ']) "#QL".
  rewrite Eqζ' in Sub2. apply (lookup_weaken _ _ _ _ Eqt') in Sub2.
  have ? : t' = t1.
  { case (decide (t' = t1)) => [//|NEqt1].
    exfalso. by rewrite !lookup_insert_ne // in Sub2. }
  subst t'. rewrite lookup_insert in Sub2. inversion Sub2. subst v' V'.

  (* close the invariant *)
  iMod ("Close" with "[QI Pts]").
  { iIntros "!>". iExists G3. iFrame "QI". iExists ζ', true, t0, V0, _.
    iFrame "Pts". iExists t1, V1. iSplit; [done|]. iFrame "QL". }

  iIntros "!>".
  iDestruct "QL" as (G0 M0 ????)
            "(#QL & %NEe12 & %HeV1 & %HeV2 & %Henq1 & %Henq2 & %HM1 & %HM2)".
  iDestruct (view_at_elim with "[SV'] QL") as "{QL} #QL".
  { iApply (monPred_in_mono with "SV'"). simpl. solve_lat. }
  iExists 1. iSplit; [done|]. simpl. iIntros "!> !>". wp_seq.

  iDestruct (monPred_in_intro True%I with "[//]") as (V) "[#⊒V _]".
  iApply (wp_step_fupd _ _ _ _ (∀ _, _ -∗ _)%I with "[$Post]"); [auto..|].
  awp_apply (dequeue_spec with "⊒V QL"); [solve_ndisj|].

  iInv mpN as (G) "(FI & QI & >●m & >◯m & >%Hv)".

  iDestruct (QueueInv_QueueConsistent with "QI") as "#>%QC".
  rewrite QueueInv_graph_master_acc. iDestruct "QI" as "[>Gm QI]".
  iDestruct (graph_master_consistent with "Gm") as %EGC.
  iPoseProof (QueueLocal_graph_snap with "QL") as "Gs".
  iDestruct (graph_master_snap_included with "Gm Gs") as %SubG0G.
  iSpecialize ("QI" with "[$Gm]").
  apply (prefix_lookup_Some _ G.(Es)) in HeV1; [|by destruct SubG0G].
  apply (prefix_lookup_Some _ G.(Es)) in HeV2; [|by destruct SubG0G].

  iCombine "◯m ◯m2" as "◯m".
  iCombine "●m ◯m" gives %[LT%nat_included _]%auth_both_valid_discrete.
  have {}LT : (size (com G) ≤ 1)%nat by lia.

  iAaccIntro with "QI".
  { iDestruct "◯m" as "[◯m $]". iFrame. iIntros "QI !> !>".
    iExists _. iFrame. done. }

  iIntros (v V' G' enqId deqId enq deq Vdeq M') "(QI & #⊒V' & #QL' & %F)".
  set (dV := mkGraphEvent deq Vdeq M') in *.
  iDestruct (QueueInv_QueueConsistent with "QI") as "#>%QC'".
  destruct F as (SubG' & SubM' & HVin & HVcomm & [CASE|CASE]).
  - (* empty pop *) exfalso.
    destruct CASE as (-> & -> & ? & EsG' & _ & ComG' & ?).
    have HdV : G'.(Es) !! deqId = Some dV.
    { subst deqId. rewrite EsG'. apply lookup_app_1_eq. }
    case (decide (unmatched_enq_2 G e1)) => [[_ UNMATCHED1]|MATCHED1].
    + (* Empty dequeue couldn't have seen an unmatched enqueue. Contradiction. *)
      refine (_ (bsq_cons_non_empty _ QC' _ _ HdV ltac:(done) e1 _ eV1 _ ltac:(done) _)); cycle 1.
      { rewrite EsG'. eapply prefix_lookup_Some; [done|by eexists]. }
      { set_solver +SubM' HM1. }
      intros (d' & Com_ed' & _). rewrite ComG' -(bsq_cons_so_com _ QC) in Com_ed'.
      apply (UNMATCHED1 d'); [|done].
      specialize (egcons_so _ EGC _ _ Com_ed') as (_ & dV' & _ & HdV' & _).
      apply lookup_lt_Some in HdV'.
      rewrite /to_set. apply elem_of_set_seq. lia.
    + (* Since e1 is matched, e2 couldn't have been matched. *)
      have UNMATCHED2 : set_Forall (λ d2 : nat, (e2, d2) ∉ so G) (to_set (Es G)).
      { intros d2 In2 So2. apply MATCHED1. split.
        { exists 1. apply (f_equal (fmap ge_event)) in HeV1.
          move: HeV1. rewrite /= Henq1 //. }
        intros d1 In1 So1.
        rewrite -(bsq_cons_so_com _ QC) in LT.
        have INCL : {[(e1,d1); (e2,d2)]} ⊆ G.(so) by set_solver +So1 So2.
        move: INCL => /(subseteq_size _ _).
        rewrite size_union; [|set_solver +NEe12].
        rewrite !size_singleton. lia. }
      refine (_ (bsq_cons_non_empty _ QC' _ _ HdV ltac:(done) e2 _ eV2 _ ltac:(done) _)); cycle 1.
      { rewrite EsG'. eapply prefix_lookup_Some; [done|by eexists]. }
      { set_solver +SubM' HM2. }
      intros (d' & Com_ed' & _). rewrite ComG' -(bsq_cons_so_com _ QC) in Com_ed'.
      apply (UNMATCHED2 d'); [|done].
      specialize (egcons_so _ EGC _ _ Com_ed') as (_ & dV' & _ & HdV' & _).
      apply lookup_lt_Some in HdV'.
      rewrite /to_set. apply elem_of_set_seq. lia.

  - (* successful dequeue *)
    rewrite /is_enqueue /is_dequeue in CASE.
    destruct CASE as (?& -> & -> & ? & NoSo & EsG' & _ & ComG' &_&_&_& eV & HeV & ? &_).
    iIntros "!>". iSplitL.
    { iNext. iExists _. iFrame.
      rewrite ComG' size_union.
      - rewrite size_singleton (comm plus). iFrame. iPureIntro.
        rewrite EsG'. intros ??? [?|[-> <-]]%lookup_app_1; [by eapply Hv|done].
      - apply disjoint_singleton_l. rewrite -(bsq_cons_so_com _ QC).
        by apply NoSo. }
    iIntros "_ Post". iApply "Post". iPureIntro. by apply (Hv _ _ _ HeV).
Qed.

End spmc_mp.
