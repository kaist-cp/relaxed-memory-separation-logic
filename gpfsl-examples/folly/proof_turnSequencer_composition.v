From gpfsl.examples Require Import sflib.

From iris.algebra Require Import auth gset gmap agree.
From iris.proofmode Require Import tactics.

From gpfsl.base_logic Require Import meta_data.
From gpfsl.logic Require Import logatom atomics invariants.

From gpfsl.logic Require Import repeat_loop new_delete.
From gpfsl.examples Require Import map_seq loc_helper.
From gpfsl.examples.algebra Require Import set.
From gpfsl.examples.folly Require Import spec_turnSequencer_composition code_turnSequencer.
From gpfsl.examples.omo Require Import omo omo_preds append_only_loc.

Require Import iris.prelude.options.

Class tseqG Σ := TSeqG {
  tseq_omoGeneralG :> omoGeneralG Σ;
  tseq_omoG :> omoSpecificG Σ tseq_event tseq_state;
  tseq_aolocG :> appendOnlyLocG Σ;
  tseq_ticketsG :> inG Σ (setUR nat);
}.

Definition tseqΣ : gFunctors := #[omoGeneralΣ; omoSpecificΣ tseq_event tseq_state; appendOnlyLocΣ; GFunctor (setUR nat)].

Global Instance subG_tseqΣ {Σ} : subG tseqΣ Σ → tseqG Σ.
Proof. solve_inG. Qed.

Section TSeq.
Context `{!noprolG Σ, !atomicG Σ, !tseqG Σ}.

#[local] Notation iProp := (iProp Σ).
#[local] Notation vProp := (vProp Σ).

Implicit Types
  (γg γl γs γsl : gname)
  (omo omol : omoT)
  (l : loc)
  (E : history tseq_event) (El : history loc_event)
  (R : nat → vProp) (P : nat → bool).

Local Open Scope nat_scope.

Definition TSeqPerm γg l P : vProp :=
  ∃ (γl γsl γt : gname),
    meta l nroot (γl,γsl,γt) ∗
    ⎡own γt (set_cf P)⎤.

Definition TSeqComplete γg l (n : nat) : vProp :=
  ∃ (γl γsl γt : gname) es el (eVl : omo_event loc_event) V,
    meta l nroot (γl,γsl,γt) ∗
    swriter_token l γl es ∗
    OmoEinfo γl el eVl ∗
    ⊒V ∗
    ⌜ last es = Some el ∧ (loc_event_msg eVl.(type)).1 = #n ∧ eVl.(sync) ⊑ V ⌝.

Definition AllWrEventsInner γl genl el : vProp :=
  ∃ (eVl : omo_event loc_event),
    OmoEinfo γl el eVl ∗
    ⌜ (loc_event_msg eVl.(type)).1 = #genl ⌝.

Definition AllWrEvents γl es : vProp :=
  [∗ list] gen↦e ∈ es, AllWrEventsInner γl gen e.

Definition last_msg_info γg γl γs l R es esl (stlist : list tseq_state) : vProp :=
  ∃ elf eVlf Vf (eVf : omo_event tseq_event) (stf : tseq_state),
    OmoEinfo γl elf eVlf ∗
    OmoEinfo γg stf.1.1.1 eVf ∗
    OmoSnap γg γs stf.1.1.1 stf ∗
    ⌜ last esl = Some elf ∧ last es = Some stf.1.1.1 ∧ loc_event_msg eVlf.(type) = (#stf.1.1.2, Vf) ∧ eVlf.(sync) = eVf.(sync)
    ∧ last stlist = Some stf ∧ stf.1.1.2 = length esl - 1 ∧ stf.1.2 = eVf.(sync) ∧ eVf.(sync) ⊑ Vf ∧ stf.2 = eVf.(eview) ⌝ ∗
    TSeqPerm γg l (λ m, m <? stf.1.1.2) ∗
    ((@{Vf} (swriter_token l γl esl ∗ R stf.1.1.2)) ∨ TSeqPerm γg l (λ m, m =? stf.1.1.2)).

(** ** Top-level predicates & invariant *)
Definition TSeqInv γg γs l E omo stlist R : vProp :=
  ∃ (γl γsl γt : gname) El omol mo,
  meta l nroot (γl,γsl,γt) ∗

  OmoAuth γg γs 1 E omo stlist _ ∗
  OmoAuth γl γsl (1/2)%Qp El omol mo _ ∗

  (∃ Vb uf, @{Vb} append_only_loc l γl uf swriter) ∗

  AllWrEvents γl (omo_write_op omol) ∗
  last_msg_info γg γl γs l R (omo_write_op omo) (omo_write_op omol) stlist.

Definition TSeqLocal (_ : namespace) γg l M : vProp :=
  ∃ (γl γsl γt : gname) Ml,
  meta l nroot (γl,γsl,γt) ∗

  (* Local snapshot of the history and local observation of events *)
  OmoEview γg M ∗
  OmoEview γl Ml.

Global Instance TSeqInv_objective γg γs l E omo stlist R : Objective (TSeqInv γg γs l E omo stlist R) := _.
Global Instance TSeqPerm_objective γg l P : Objective (TSeqPerm γg l P) := _.
Global Instance TSeqLocal_persistent N γg l M : Persistent (TSeqLocal N γg l M) := _.

Local Tactic Notation "simplify_meta" "with" constr(Hs) :=
  iDestruct (meta_agree with Hs) as %[[-> ->]%pair_inj ->]%pair_inj.

Lemma TSeqPerm_equiv γg l P1 P2 :
  (∀ n, P1 n = P2 n) →
  TSeqPerm γg l P1 -∗ TSeqPerm γg l P2.
Proof.
  iIntros "%Equiv (%&%&%& #HM & Hγt)".
  repeat iExists _. iFrame "HM". by rewrite set_cf_equiv.
Qed.

Lemma TSeqPerm_split γg l P1 P2 :
  TSeqPerm γg l P1 -∗ TSeqPerm γg l (λ n, P1 n && P2 n) ∗ TSeqPerm γg l (λ n, P1 n && negb (P2 n)).
Proof.
  iIntros "(%&%&%& #HM & Hγt)".
  rewrite (set_cf_split _ P2). iDestruct "Hγt" as "[Hγt1 Hγt2]".
  iSplitL "Hγt1"; repeat iExists _; iFrame "∗#".
Qed.

Lemma TSeqPerm_combine γg l P1 P2 :
  TSeqPerm γg l P1 -∗ TSeqPerm γg l P2 -∗ TSeqPerm γg l (λ n, P1 n || P2 n).
Proof.
  iIntros "(%&%&%& #HM & Hγt) (%&%&%& #HM' & Hγt')".
  simplify_meta with "HM' HM". iCombine "Hγt Hγt'" as "Hγt".
  iDestruct (own_valid with "Hγt") as %valid.
  rewrite set_cf_combine; [|done].
  repeat iExists _. iFrame "∗#".
Qed.

Lemma TSeqPerm_excl γg l P1 P2 n :
  P1 n = true → P2 n = true →
  TSeqPerm γg l P1 -∗ TSeqPerm γg l P2 -∗ False.
Proof.
  iIntros "%P1n %P2n (%&%&%& #HM & Hγt1) (%&%&%& #HM' & Hγt2)".
  simplify_meta with "HM' HM".
  iCombine "Hγt1 Hγt2" as "Hγt". iDestruct (own_valid with "Hγt") as %VALID%(set_cf_excl _ _ n).
  by rewrite P1n P2n in VALID.
Qed.

Lemma TSeqInv_Linearizable_instance :
  ∀ γg γs l E omo stlist R, TSeqInv γg γs l E omo stlist R ⊢ ⌜ Linearizability_omo E omo stlist ⌝.
Proof.
  intros. iDestruct 1 as (??????) "(_ & M● & _)".
  by iDestruct (OmoAuth_Linearizable with "M●") as %H.
Qed.

Lemma TSeqInv_OmoAuth_acc_instance :
  ∀ γg γs l E omo stlist R,
    TSeqInv γg γs l E omo stlist R ⊢ OmoAuth γg γs 1 E omo stlist _ ∗ (OmoAuth γg γs 1 E omo stlist _ -∗ TSeqInv γg γs l E omo stlist R).
Proof.
  intros. iDestruct 1 as (??????) "(H1 & M● & H2)".
  iFrame "M●". iIntros "M●". repeat iExists _. iFrame.
Qed.

Lemma TSeqLocal_OmoEview_instance :
  ∀ N γg l M, TSeqLocal N γg l M ⊢ OmoEview γg M.
Proof.
  intros. iDestruct 1 as (????) "(_ & M◯ & _)". iFrame.
Qed.

Lemma new_tseq_spec :
  new_tseq_spec' code_turnSequencer.newTS TSeqLocal TSeqInv TSeqPerm.
Proof.
  iIntros (N tid V0 R Φ) "[#⊒V0 R] Post".
  wp_lam. wp_apply wp_new; [done..|].
  iIntros (l) "([H†|%] & l↦ & Hml & _)"; [|done].
  rewrite own_loc_na_vec_singleton. wp_let. wp_apply wp_fupd. wp_write.

  iCombine "R ⊒V0" as "RV".
  iMod (append_only_loc_swriter_from_na_rel with "RV l↦") as (γl γsl V1 eVl0)
    "(#⊒V1 & Ml● & (#Ml◯ & [R@V1 #⊒V0@V1] & SW) & omol↦ & WCOMMITl & #el0✓eVl0 & Pures)"; [done|].
  iDestruct "Pures" as %[eVl0EV eVl0SYNC].
  iAssert (⌜ V0 ⊑ V1 ⌝)%I with "[-]" as %LeV0V1.
  { rewrite !view_at_unfold !monPred_at_in. by iDestruct "⊒V0@V1" as %?. }

  set M := {[0%nat]}.
  set eVinit := mkOmoEvent Init V1 M.
  set initst := (0%nat, 0%nat, eVinit.(sync), eVinit.(eview)).

  iMod (@OmoAuth_alloc _ _ _ _ _ eVinit initst _ _ tseq_interpretable with "WCOMMITl")
    as (γg γs) "(M● & #M◯ & #e0↦el0 & #e0✓eVinit & #e0↪initst & WCOMMIT)".
  { by apply tseq_step_Init. } { done. }
  iDestruct (OmoHbToken_finish with "M●") as "M●".

  iMod (own_alloc (set_cf (λ (n : nat), true))) as (γt) "Hγt"; [done|].
  rewrite (set_cf_split _ (λ n, n <? 0)).
  iDestruct "Hγt" as "[Hγt1 Hγt2]".
  rewrite (set_cf_equiv (λ n, true && (n <? 0)) (λ n, n <? 0)); [|done].
  rewrite (set_cf_equiv (λ n, true && negb (n <? 0)) (λ n, true)); [|done].
  iMod (meta_set _ _ (γl,γsl,γt) nroot with "Hml") as "#HM"; [done|].
  rewrite shift_0.

  iDestruct ("Post" $! γg γs l {[0%nat]} V1 with "[-]") as "HΦ"; last first.
  { iModIntro. by iApply "HΦ". }

  iFrame "⊒V1". iSplitR; last iSplitR "WCOMMIT Hγt2"; last iSplitL "WCOMMIT"; last iSplitL.
  - repeat iExists _. iFrame "HM M◯ Ml◯".
  - repeat iExists _. iFrame "HM M● Ml●". simpl. iSplitL "omol↦"; last iSplitR.
    + iDestruct (view_at_intro with "omol↦") as (Vb) "[_ omol↦]". iExists Vb,∅. iFrame.
    + rewrite /AllWrEvents big_sepL_singleton. iExists _. iFrame "el0✓eVl0". by rewrite eVl0EV.
    + iExists 0,eVl0,V1,eVinit,initst. iFrame "#". iSplitR; last iSplitL "Hγt1".
      * iPureIntro. split_and!; try done. subst initst. by rewrite eVl0EV.
      * repeat iExists _. iFrame "HM Hγt1".
      * iLeft. iFrame.
  - iFrame.
  - repeat iExists _. iFrame "HM Hγt2".
  - iPureIntro. solve_lat.
Qed.

Lemma wait_spec :
  wait_spec' code_turnSequencer.waitForTurn TSeqLocal TSeqInv TSeqPerm TSeqComplete.
Proof.
  intros N DISJ l tid γg γs M V0 n R. iIntros "#⊒V0 #TSeqLocal Perm" (Φ) "AU".
  iDestruct "TSeqLocal" as (??? Ml0) "(HM & M◯0 & Ml◯0)".
  iLöb as "IH". wp_lam. wp_bind (!ᵃᶜ _)%E.

  (* Inv access *)
  iMod "AU" as (E1 omo1 stlist1) "[TSeqInv Close]".
  iDestruct "TSeqInv" as (??? El1 omol1 mo1)
    "(>HM' & >M●1 & >Ml●1 & (%Vb1 & %uf1 & >omol↦1) & >#AllWrEvents1 & LAST1)".
  simplify_meta with "HM' HM". iClear "HM'".
  iDestruct (view_at_intro_incl with "M◯0 ⊒V0") as (V0') "(#⊒V0' & %LeV0V0' & #M◯0@V0')".

  wp_apply (append_only_loc_acquire_read with "[$Ml●1 $Ml◯0 $omol↦1 $⊒V0']"); [solve_ndisj|].
  iIntros (el1 genl1 vl1 Vl1 V1 eVl1 eVln1) "(Pures & Ml●1 & RCOMMIT & #MAXgen_el1 &
    #el1✓eVl1 & #eln1✓eVln1 & #el1=eln1 & #⊒V1 & #Ml◯1' & omol↦1)".
  iDestruct "Pures" as %(Eqgenl1 & eVl1EV & LeV0'Vl1V1 & eVln1EV & eVln1SYNC).

  iDestruct (big_sepL_lookup with "AllWrEvents1") as (eVl1') "[el1✓eVl1' %eVl1'EV]"; [exact Eqgenl1|].
  iDestruct (OmoEinfo_agree with "el1✓eVl1 el1✓eVl1'") as %<-. iClear "el1✓eVl1'".
  rewrite eVl1EV /= in eVl1'EV. subst vl1.

  destruct (decide (genl1 = n)) as [->|NEQ]; last first.
  { (* Wait failed, retry *)
    iAssert (⌜ genl1 < n ⌝)%I with "[-]" as %LT.
    { iDestruct "LAST1" as (elf1 eVlf1 Vf1 eVf1 stf1)
        "(#elf1✓eVlf1 & #ef1✓eVf1 & ##ef1↪stf1 &
            (%LASTelf1 & %LASTef1 & %eVlf1EV & %eVlf1SYNC & %LASTstf1 & %stf1VAL & %stf1VIEWEQ & %stf1VIEW & %stf1EVIEW) & LTPerm & CASE)".
      rewrite last_lookup in LASTelf1.
      have EQ : Init.Nat.pred (length (omo_write_op omol1)) = length (omo_write_op omol1) - 1 by lia.
      rewrite EQ in LASTelf1. clear EQ.
      have LE1 : genl1 ≤ length (omo_write_op omol1) - 1 by apply lookup_lt_Some in Eqgenl1; lia.
      destruct (le_lt_dec (length (omo_write_op omol1) - 1) n) as [LE2|LT]; last first.
      { iDestruct (TSeqPerm_excl _ _ _ _ n with "Perm LTPerm") as %?; [by rewrite Nat.eqb_eq| |done].
        rewrite stf1VAL /= Nat.ltb_lt. done. }
      iPureIntro. lia. }

    iDestruct "Close" as "[Abort _]".
    iMod ("Abort" with "[-Perm]") as "AU".
    { repeat iExists _. iFrame "HM M●1 Ml●1". rewrite omo_insert_r_write_op. iFrame "LAST1 AllWrEvents1". eauto with iFrame. }
    iModIntro. wp_pures. rewrite bool_decide_false; [|lia]. wp_op.
    rewrite bool_decide_false; [|lia]. wp_if. iApply ("IH" with "Perm AU"). }

  (* Wait success, commit *)
  iDestruct "LAST1" as (elf1 eVlf1 Vf1 eVf1 stf1)
    "(#elf1✓eVlf1 & #ef1✓eVf1 & #ef1↪stf1 &
        (%LASTelf1 & %LASTef1 & %eVlf1EV & %eVlf1SYNC & %LASTstf1 & %stf1VAL & %stf1VIEWEQ & %stf1VIEW & %stf1EVIEW) & LTPerm & CASE)".
  iAssert (⌜ n = (length (omo_write_op omol1) - 1)%nat ⌝)%I with "[-]" as %->.
  { destruct (le_lt_dec (length (omo_write_op omol1) - 1)%nat n) as [LE|LT].
    - apply lookup_lt_Some in Eqgenl1. iPureIntro. lia.
    - iDestruct (TSeqPerm_excl with "Perm LTPerm") as %?; [by rewrite /= Nat.eqb_eq| |done].
      simpl. rewrite Nat.ltb_lt. lia. }

  rewrite last_lookup in LASTelf1.
  replace (Init.Nat.pred (length (omo_write_op omol1))) with (length (omo_write_op omol1) - 1)%nat in LASTelf1 by lia.
  rewrite Eqgenl1 in LASTelf1. inversion LASTelf1. subst elf1.
  iDestruct (OmoEinfo_agree with "el1✓eVl1 elf1✓eVlf1") as %<-. iClear "elf1✓eVlf1".
  rewrite eVl1EV in eVlf1EV. inversion eVlf1EV. subst Vf1. clear LASTelf1 H0 eVlf1EV.

  (* Get resource R and [swriter_token] from case analysis *)
  iDestruct "CASE" as "[RES | Perm']"; last first.
  { iDestruct (TSeqPerm_excl with "Perm Perm'") as %?; [by rewrite /= Nat.eqb_eq|by rewrite /= Nat.eqb_eq|done]. }

  have LeV0V1 : V0 ⊑ V1 by solve_lat.
  set waitId := length E1.
  set M' := {[waitId; stf1.1.1.1]} ∪ stf1.2 ∪ M.
  set egV' := mkOmoEvent (Take (length (omo_write_op omol1) - 1)) V1 M'.
  set E1' := E1 ++ [egV'].
  set waitst : tseq_state := (waitId, (length (omo_write_op omol1) - 1)%nat, V1, M').
  set ef1 := stf1.1.1.1.
  have SubE1E1' : E1 ⊑ E1' by apply prefix_app_r.

  iAssert (⌜ OmoUBgen omo1 M (length omo1 - 1)%nat ⌝)%I with "[-]" as %MAXgen_ef1_p1.
  { iIntros "%e %eM". iDestruct (OmoAuth_OmoEview with "M●1 M◯0") as %Incl.
    apply Incl in eM. iDestruct (OmoAuth_wf with "M●1") as %[OMO_GOOD _].
    iDestruct (OmoAuth_omo_nonempty with "M●1") as %Nomo.
    eapply lookup_omo_surjective in eM; [|done].
    destruct eM as [eidx Heidx]. iPureIntro. exists eidx. split; [done|].
    apply lookup_omo_lt_Some in Heidx. destruct omo1; try done. lia. }
  iDestruct (OmoUB_singleton with "ef1✓eVf1") as "#MAXgen_ef1_p2".
  iDestruct (OmoUB_into_gen _ _ _ _ _ _ _ _ (wr_event (length omo1 - 1))  with "M●1 MAXgen_ef1_p2") as %MAXgen_ef1_p2.
  { rewrite lookup_omo_wr_event omo_write_op_length. rewrite last_lookup in LASTef1.
    replace (Init.Nat.pred (length (omo_write_op omo1))) with (length (omo_write_op omo1) - 1) in LASTef1 by lia. done. }
  specialize (OmoUBgen_union _ _ _ _ MAXgen_ef1_p2 MAXgen_ef1_p1) as MAXgen_ef1.

  have LeV0'V1 : V0' ⊑ V1 by clear -LeV0'Vl1V1; solve_lat.
  iDestruct (view_at_mono_2 _ V1 with "M◯0@V0'") as "#M◯0@V1"; [done|].
  iDestruct (OmoEview_insert_new_obj with "M◯0@V1 ef1✓eVf1") as "M◯1@V1"; [clear -stf1VIEW LeV0'Vl1V1; solve_lat|].
  iDestruct (OmoAuth_wf with "M●1") as %[OMO_GOOD1 _].
  iMod (OmoAuth_insert_ro_gen _ _ _ _ _ _ _ _ _ egV' (length omo1 - 1) with "M●1 M◯1@V1 RCOMMIT []")
    as "(M●1 & #M◯0'@V1 & #waitId↦eln1 & _ & #waitId✓egV' & RCOMMIT)".
  { have ? : step waitId egV' stf1 stf1; [|iPureIntro; split_and!; try done; last set_solver].
    - destruct stf1 as [[[a b] c] d]. simpl in *. subst b c d. apply tseq_step_Take.
      + by subst egV'.
      + destruct omol1; [done|by rewrite -omo_write_op_length cons_length; lia].
      + subst egV'. simpl. clear -LeV0'Vl1V1 stf1VIEW. solve_lat.
      + subst egV' M' waitId. simpl. set_solver-.
    - rewrite last_lookup in LASTstf1. eapply omo_stlist_length in OMO_GOOD1 as EQlenST1. rewrite -EQlenST1 in LASTstf1.
      replace (Init.Nat.pred (length omo1)) with (length omo1 - 1) in LASTstf1 by lia. done. }
  iDestruct (OmoHbToken_finish with "M●1") as "M●1".

  iDestruct "Close" as "[_ Commit]".
  iDestruct (TSeqPerm_split _ _ _ (λ m, m =? stf1.1.1.2) with "Perm") as "[PermClose PermReturn]".
  iDestruct (TSeqPerm_equiv _ _ _ (λ m, m =? stf1.1.1.2) with "PermClose") as "PermClose".
  { intros. simpl. destruct (decide (n = stf1.1.1.2)) as [->|NEQ].
    - rewrite -stf1VAL. by destruct (stf1.1.1.2 =? stf1.1.1.2).
    - rewrite -Nat.eqb_neq in NEQ. by rewrite NEQ andb_comm /=. }
  iMod ("Commit" $! V1 M' with "[-RES PermReturn]") as "HΦ".
  { iFrame "⊒V1". iSplitR "RCOMMIT"; last iSplitL; last iSplit.
    - repeat iExists _. iFrame "HM M●1 Ml●1". iSplitL "omol↦1"; [eauto with iFrame|].
      rewrite omo_insert_r_write_op. iFrame "AllWrEvents1".
      iExists el1,eVl1,_,_,stf1. iFrame "el1✓eVl1 ef1✓eVf1 ef1↪stf1 LTPerm". iSplitR; [|by iRight].
      iPureIntro. split_and!; try done.
      + rewrite last_lookup.
        replace (Init.Nat.pred (length (omo_write_op omol1))) with (length (omo_write_op omol1) - 1) by lia. done.
      + by rewrite omo_insert_r_write_op.
      + by rewrite eVl1EV -stf1VAL.
    - iFrame.
    - repeat iExists _. iFrame "HM Ml◯1'". subst M'.
      by replace ({[waitId; stf1.1.1.1]} ∪ stf1.2 ∪ M) with ({[length E1]} ∪ ({[ef1]} ∪ eVf1.(eview) ∪ M)) by set_solver.
    - iPureIntro. split_and!; try done. subst M'. set_solver-. }

  iDestruct (view_at_mono_2 _ V1 with "RES") as "RES"; [clear -LeV0'Vl1V1; solve_lat|].
  iDestruct (view_at_elim with "⊒V1 RES") as "[SW R]".

  iModIntro. wp_pures. rewrite bool_decide_true; [|done]. wp_pures. rewrite stf1VAL.
  iApply ("HΦ" with "[$R SW]").
  repeat iExists _. iFrame "HM SW el1✓eVl1 ⊒V1". iPureIntro. split.
  - rewrite last_lookup. replace (Init.Nat.pred (length (omo_write_op omol1))) with (length (omo_write_op omol1) - 1) by lia. done.
  - rewrite eVl1EV. split; [done|]. rewrite eVlf1SYNC. clear -LeV0'Vl1V1 stf1VIEW. solve_lat.
Qed.

Lemma complete_spec :
  complete_spec' code_turnSequencer.completeTurn TSeqLocal TSeqInv TSeqComplete.
Proof.
  intros N DISJ l tid γg γs M V0 n R. iIntros "#⊒V0 #TSeqLocal RSN CompleteN" (Φ) "AU".
  iDestruct "TSeqLocal" as (??? Ml0) "(HM & M◯0 & Ml◯0)".
  wp_lam. wp_bind (!ʳˡˣ _)%E.

  (* Inv access 1 *)
  iMod "AU" as (E1 omo1 stlist1) "[TSeqInv [Abort _]]".
  iDestruct "TSeqInv" as (??? El1 omol1 mo1)
    "(>HM' & >M●1 & >Ml●1 & (%Vb1 & %uf1 & >omol↦1) & >#AllWrEvents1 & LAST1)".
  simplify_meta with "HM' HM". iClear "HM'".
  iDestruct "CompleteN" as (???? elf1 eVlf1 Vlf1) "(HM' & SW & #elf1✓eVlf1 & #⊒Vlf1 & (%LASTelf1 & %eVlf1EV & %LeeVlf1Vlf))".
  simplify_meta with "HM' HM". iClear "HM'".

  iDestruct (OmoAuth_swriter_token_agree_obj_2 with "Ml●1 omol↦1 SW") as %->.
  iCombine "M◯0 ⊒Vlf1" as "RES".
  iDestruct (view_at_intro_incl with "RES ⊒V0") as (V0') "(⊒V0' & %LeV0V0' & [M◯0@V0' ⊒V0@V0'])".
  iAssert (⌜ Vlf1 ⊑ V0' ⌝)%I with "[-]" as %LeVlf1V0'.
  { rewrite !view_at_unfold !monPred_at_in. by iDestruct "⊒V0@V0'" as %?. }
  wp_apply (append_only_loc_read_with_swriter_token with "[$Ml●1 $Ml◯0 $SW $omol↦1 $⊒V0']"); [done|solve_ndisj|].
  iIntros (el1 vl1 Vl1 V1 eVl1 eVln1) "(Pures & Ml●1 & _ & #MAXgen_el1 & #el1✓eVl1 & #eln1✓eVln1 & #el1=eln1 & #⊒V1 & _ & [SW #Ml◯1@V1] & omol↦1)".
  iDestruct "Pures" as %(LASTel1 & eVl1EV & LeV0'Vl1V1 & eVln1EV & eVln1SYNC).

  rewrite LASTelf1 in LASTel1. inversion LASTel1. subst el1. clear LASTel1.
  iDestruct (OmoEinfo_agree with "elf1✓eVlf1 el1✓eVl1") as %<-. iClear "el1✓eVl1".
  rewrite eVl1EV /= in eVlf1EV. subst vl1.
  iMod ("Abort" with "[-RSN SW]") as "AU".
  { repeat iExists _. iFrame "HM M●1 Ml●1". rewrite omo_insert_r_write_op. iFrame "LAST1 AllWrEvents1". eauto with iFrame. }
  iModIntro. wp_pures. rewrite bool_decide_true; [|done]. wp_op.

  (* Inv access 2 *)
  iMod "AU" as (E2 omo2 stlist2) "[TSeqInv [_ Commit]]".
  iDestruct "TSeqInv" as (??? El2 omol2 mo2)
    "(>HM' & >M●2 & >Ml●2 & (%Vb2 & %uf2 & >omol↦2) & >#AllWrEvents2 & LAST2)".
  simplify_meta with "HM' HM". iClear "HM'".

  iDestruct (view_at_elim with "⊒V1 SW") as "SW".
  iDestruct (OmoAuth_swriter_token_agree_obj_2 with "Ml●2 omol↦2 SW") as %EQes1es2.
  rewrite EQes1es2. rewrite EQes1es2 in LASTelf1.

  wp_apply (append_only_loc_release_write _ _ _ _ _ _ _ _ _ _ _ _ (n + 1)%Z (R (n + 1)%nat) with "[$Ml●2 $Ml◯0 $SW $omol↦2 $RSN $⊒V1]"); [solve_lat|done|].
  iIntros (V2 eVln2 elf2 eVlf2) "(Pures & #⊒V2 & Ml●2 & WCOMMIT & #elf2✓eVlf2 & #eln2✓eVln2 & (SW & #Ml◯2@V2 & RSN) & omol↦2)".
  iDestruct "Pures" as %(LASTelf2 & LeV1V2 & NeV1V2 & eVln2EV & eVln2SYNC).

  iDestruct "LAST2" as (??? eVf1 stf1) "(#elf1'✓eVlf1' & #ef1✓eVf1 & #ef1↪stf1 & Pures & LTPerm & CASE)".
  iDestruct "Pures" as %(LASTelf1' & LASTef1 & eVlf1'EV & eVlf1'OUT & LASTstf1 & stf1VAL & stf1VIEW & eVf1SYNC & stf1EVIEW).
  rewrite LASTelf1 in LASTelf1'. inversion LASTelf1'. subst elf. clear LASTelf1'.
  iDestruct (OmoEinfo_agree with "elf1✓eVlf1 elf1'✓eVlf1'") as %<-. iClear "elf1'✓eVlf1'".
  rewrite eVl1EV in eVlf1'EV. inversion eVlf1'EV.
  have EQ : n = stf1.1.1.2 by lia. subst Vf n. clear eVlf1'EV H0.
  iDestruct "CASE" as "[[SW' _] | PermSN]".
  { by iDestruct (swriter_token_exclusive_obj with "SW SW'") as %?. }

  iDestruct (view_at_mono_2 _ V2 with "M◯0@V0'") as "M◯0@V2"; [solve_lat|].
  iDestruct (OmoEview_insert_new_obj with "M◯0@V2 ef1✓eVf1") as "#M◯2@V2"; [by rewrite -eVlf1'OUT; solve_lat|].

  have LeV0V2 : V0 ⊑ V2 by solve_lat.
  set compId := length E2.
  set M' := {[compId; stf1.1.1.1]} ∪ stf1.2 ∪ M.
  set egV' := mkOmoEvent (Complete stf1.1.1.2) V2 M'.
  set E2' := E2 ++ [egV'].
  set stf2 := (compId, (stf1.1.1.2 + 1)%nat, egV'.(sync), egV'.(eview)).

  iMod (OmoAuth_insert_last with "M●2 M◯2@V2 WCOMMIT []")
    as "(M●2 & #M◯2'@V2 & #compId↦eln2 & #compId✓egV' & #compId↪stf2 & WCOMMIT)".
  { have ? : step compId egV' stf1 stf2.
    { destruct stf1 as [[[a b] c] d]. simpl in *. subst stf2 egV' M' c.
      apply tseq_step_Complete; try done; [lia|..]; simpl; [|set_solver-].
      rewrite -eVlf1'OUT. clear -LeeVlf1Vlf LeVlf1V0' LeV0'Vl1V1 LeV1V2. solve_lat. }
    iPureIntro. split_and!; try done. subst egV' M' compId. simpl. set_solver. }
  iDestruct (OmoHbToken_finish with "M●2") as "M●2".

  iDestruct (TSeqPerm_combine with "LTPerm PermSN") as "LTPerm".
  iDestruct (TSeqPerm_equiv _ _ _ (λ n, n <? (stf1.1.1.2 + 1)%nat) with "LTPerm") as "LTPerm".
  { intros. simpl. destruct (lt_eq_lt_dec n stf1.1.1.2) as [LTEQ|LT]; first destruct LTEQ as [LT|EQ].
    - have EQ1 : n <? stf1.1.1.2 = true by apply Nat.ltb_lt.
      have EQ2 : n <? stf1.1.1.2 + 1 = true by apply Nat.ltb_lt; lia.
      by rewrite EQ1 EQ2.
    - have EQ1 : n =? stf1.1.1.2 = true by apply Nat.eqb_eq.
      have EQ2 : n <? stf1.1.1.2 + 1 = true by apply Nat.ltb_lt; lia.
      rewrite EQ1 EQ2. by destruct (n <? stf1.1.1.2).
    - have EQ1 : n <? stf1.1.1.2 = false by apply Nat.ltb_ge; lia.
      have EQ2 : n =? stf1.1.1.2 = false by apply Nat.eqb_neq; lia.
      have EQ3 : n <? stf1.1.1.2 + 1 = false by apply Nat.ltb_ge; lia.
      by rewrite EQ1 EQ2 EQ3. }

  iMod ("Commit" $! V2 M' with "[-]") as "HΦ"; last first. { iModIntro. by iApply "HΦ". }
  have NZ : length (omo_write_op omol2) ≠ 0 by rewrite -omo_write_op_length; destruct omol2.
  iFrame "⊒V2". iSplitR "WCOMMIT"; last iSplitL; last iSplit.
  - repeat iExists _. iFrame "HM M●2 Ml●2". rewrite omo_append_w_write_op. subst E2'.
    iSplitL "omol↦2"; [eauto with iFrame|]. iSplitR.
    + rewrite /AllWrEvents big_sepL_snoc. iFrame "AllWrEvents2".
      repeat iExists _. iFrame "eln2✓eVln2". rewrite eVln2EV stf1VAL. simpl.
      have EQ : (Z.of_nat (length (omo_write_op omol2) - 1)%nat + 1)%Z = Z.of_nat (length (omo_write_op omol2)) by lia.
      by rewrite EQ.
    + iExists (length El2),eVln2,V2,egV',stf2. subst stf2. simpl. iFrame "eln2✓eVln2 compId✓egV' compId↪stf2 LTPerm".
      iSplitR; [|iLeft; iFrame "SW RSN"]. iPureIntro. split_and!; try done; try by rewrite last_app.
      * by rewrite omo_append_w_write_op last_app /=.
      * rewrite eVln2EV.
        have EQ : (Z.of_nat stf1.1.1.2 + 1)%Z = (Z.of_nat (stf1.1.1.2 + 1)) by lia. by rewrite EQ.
      * rewrite app_length stf1VAL /=. lia.
  - iFrame.
  - repeat iExists _. subst E2' M'. iFrame "HM Ml◯2@V2". rewrite stf1EVIEW.
    replace ({[compId; stf1.1.1.1]} ∪ eVf1.(eview) ∪ M) with ({[length E2]} ∪ ({[stf1.1.1.1]} ∪ eVf1.(eview) ∪ M)) by set_solver-.
    iFrame "M◯2'@V2".
  - iPureIntro. split_and!; try done. subst M'. set_solver-.
Qed.
End TSeq.

Definition tseq_composition_impl `{!noprolG Σ, !atomicG Σ, !tseqG Σ}
  : tseq_composition_spec Σ := {|
    spec_turnSequencer_composition.TSeqInv_Linearizable := TSeqInv_Linearizable_instance ;
    spec_turnSequencer_composition.TSeqInv_OmoAuth_acc := TSeqInv_OmoAuth_acc_instance;
    spec_turnSequencer_composition.TSeqLocal_OmoEview := TSeqLocal_OmoEview_instance;
    spec_turnSequencer_composition.TSeqPerm_Equiv := TSeqPerm_equiv;
    spec_turnSequencer_composition.TSeqPerm_Split := TSeqPerm_split;
    spec_turnSequencer_composition.TSeqPerm_Combine := TSeqPerm_combine;
    spec_turnSequencer_composition.TSeqPerm_Excl := TSeqPerm_excl;

    spec_turnSequencer_composition.new_tseq_spec := new_tseq_spec;
    spec_turnSequencer_composition.wait_spec := wait_spec;
    spec_turnSequencer_composition.complete_spec := complete_spec;
  |}.
