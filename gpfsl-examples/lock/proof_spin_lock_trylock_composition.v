From gpfsl.examples.lock Require Import code_spin_lock spec_trylock_composition.
From gpfsl.examples Require Import uniq_token.
From gpfsl.logic Require Import proofmode repeat_loop new_delete logatom atomics invariants.


From gpfsl.lang Require Import notation.

From gpfsl.base_logic Require Import meta_data.
From gpfsl.examples.omo Require Import omo omo_preds append_only_loc.

Require Import iris.prelude.options.

Local Open Scope nat_scope.

Section spinlock.

Context `{!noprolG Σ, !uniqTokG Σ, !atomicG Σ, !omoGeneralG Σ, !omoSpecificG Σ lock_event_type lock_state, !appendOnlyLocG Σ}.

Implicit Types
  (γg γl γs γsl γm : gname)
  (omo omol : omoT)
  (E : history lock_event_type)
  (El : history loc_event)
  (eV : omo_event lock_event_type)
  (eVl : omo_event loc_event)
  (uf : gset val)
  (ty : append_only_type).

Notation iProp := (iProp Σ).
Notation vProp := (vProp Σ).

Definition Locked: LockedT Σ :=
  λ (γg : gname) (l : loc),
    (∃ γl γs γsl γm es M e el (st : lock_state),
      meta l nroot (γl,γs,γsl,γm) ∗ swriter_token l γl es ∗ OmoEview γg M ∗
      OmoCW γg γl e el ∗ OmoSnap γg γs e st ∗
      ⌜ last es = Some el ∧ st.1.1.1 ∈ M ∧ st.2 ⊆ M ⌝)%I.

Definition AllWrEvents_inner γg γl γs γm el : vProp :=
  ∃ (v : Z) (V : view) eVl e eV (st : lock_state),
    OmoEinfo γl el eVl ∗
    OmoEinfo γg e eV ∗
    OmoCW γg γl e el ∗ CWMonoValid γm e ∗
    OmoSnap γg γs e st ∗
    ⌜ loc_event_msg eVl.(type) = (#v, V)
    ∧ (v = 0%Z ↔ st.1.1.2 = false) ⌝.

Definition AllWrEvents γg γl γs γm es : vProp :=
  [∗ list] el ∈ es, AllWrEvents_inner γg γl γs γm el.

Global Instance AllWrEvents_inner_persistent γg γl γs γm el : Persistent (AllWrEvents_inner γg γl γs γm el) := _.
Global Instance AllWrEvents_persistent γg γl γs γm es : Persistent (AllWrEvents γg γl γs γm es) := _.

Definition last_msg_info γg γl γs es P ty (stf : lock_state) : vProp :=
  ∃ elf eVlf (vf : Z) Vf (eVf : omo_event lock_event_type),
    ⌜ last es = Some elf ∧ loc_event_msg eVlf.(type) = (#vf, Vf) ∧ eVf.(sync) = stf.1.2 ∧ eVf.(eview) = stf.2 ⌝ ∗
    OmoEinfo γl elf eVlf ∗
    OmoEinfo γg stf.1.1.1 eVf ∗
    OmoCW γg γl stf.1.1.1 elf ∗
    OmoSnap γg γs stf.1.1.1 stf ∗
    if decide (vf = 0%Z) then (@{Vf} P ∗ ⌜ ty = cas_only ∧ stf.1.1.2 = false ∧ stf.1.2 ⊑ Vf⌝)
    else ⌜ ty = swriter ∧ stf.1.1.2 = true ⌝.

Global Instance last_msg_info_objective γg γl γs es P ty stf : Objective (last_msg_info γg γl γs es P ty stf).
Proof.
  repeat (apply exists_objective; intros). repeat (apply sep_objective; [apply _|]).
  destruct (decide (x1 = 0%Z)); apply _.
Qed.

Definition seen_event_info γg γl γm E : vProp :=
  [∗ list] e↦eV ∈ E,
    ∃ e', OmoHb γg γl e e' ∗ OmoCW γg γl e e' ∗ CWMonoValid γm e.

Definition LockInv (γg γs : gname) (l : loc) E omo stlist (P : vProp) : vProp :=
  ∃ γl γsl γm El omol stf mo uf ty Mono,
    meta l nroot (γl,γs,γsl,γm) ∗

    OmoAuth γg γs 1 E omo stlist _ ∗
    OmoAuth γl γsl (1/2)%Qp El omol mo _ ∗

    (∃ Vb, @{Vb} append_only_loc l γl uf ty) ∗

    AllWrEvents γg γl γs γm (omo_write_op omol) ∗
    last_msg_info γg γl γs (omo_write_op omol) P ty stf ∗
    seen_event_info γg γl γm E ∗
    CWMono γg γl γm Mono ∗

    ⌜ last stlist = Some stf ∧ #0 ∉ uf ⌝.

Definition LockLocal: LockLocalNT Σ :=
  (λ (_: namespace) γg l M,
  ∃ γl γs γsl γm Ml,
    meta l nroot (γl,γs,γsl,γm) ∗
    OmoEview γg M ∗
    OmoEview γl Ml)%I.

Global Instance LockInv_objective γg γs l E omo stlist P : Objective (LockInv γg γs l E omo stlist P) := _.
Global Instance LockLocal_persistent N γg l M : Persistent (LockLocal N γg l M) := _.

Lemma AllWrEvents_acc γg γl γs γm es el :
  el ∈ es →
  AllWrEvents γg γl γs γm es -∗ AllWrEvents_inner γg γl γs γm el.
Proof.
  iIntros "%INCL #AllWrEvents". apply elem_of_list_lookup in INCL as [gen LOOKUP].
  by rewrite /AllWrEvents big_sepL_lookup.
Qed.

Local Tactic Notation "simplify_meta" "with" constr(Hs) :=
  iDestruct (meta_agree with Hs) as %[[[-> ->]%pair_inj ->]%pair_inj ->]%pair_inj.

Lemma LockInv_Linearizable_instance :
  ∀ γg γs l E omo stlist P, LockInv γg γs l E omo stlist P ⊢ ⌜ Linearizability_omo E omo stlist ⌝.
Proof. iIntros (???????) "(%&%&%&%&%&%&%&%&%&%& _ & M● & _)". by iDestruct (OmoAuth_Linearizable with "M●") as %?. Qed.

Lemma LockInv_OmoAuth_acc_instance :
  ∀ γg γs l E omo stlist P,
    LockInv γg γs l E omo stlist P ⊢ OmoAuth γg γs 1 E omo stlist _ ∗ (OmoAuth γg γs 1 E omo stlist _ -∗ LockInv γg γs l E omo stlist P).
Proof.
  iIntros (???????) "(%&%&%&%&%&%&%&%&%&%& H1 & M● & H2)". iFrame. iIntros "M●". repeat iExists _. iFrame.
Qed.

Lemma LockLocal_OmoEview_instance :
  ∀ N γg l M, LockLocal N γg l M ⊢ OmoEview γg M.
Proof. intros. by iDestruct 1 as "(%&%&%&%&%& _ & ⊒M & _)". Qed.

Definition new_lock_spec :
  new_lock_spec' code_spin_lock.new_lock LockLocal LockInv.
Proof.
  iIntros (N tid Vi P φ) "[#⊒Vi P] Hφ".
  wp_lam. wp_apply wp_new; [done..|].
  iIntros (l) "([l†|%] & l↦ & Hms & _)"; [|done].
  rewrite own_loc_na_vec_singleton. wp_lam. iApply wp_fupd. wp_write.
  iCombine "⊒Vi P" as "RES".

  iMod (append_only_loc_cas_only_from_na_rel with "RES l↦") as (γl γsl V0 eVl0)
    "(#⊒V0 & Ml● & [#Ml◯ [#⊒Vi@V0 P@V0]] & omol↦ & WCOMMIT & #el0✓eVl0 & [%HeVl0 %eVl0SYNC])"; [done|].

  iAssert (⌜ Vi ⊑ V0 ⌝)%I with "[]" as %LeViV0.
  { rewrite !view_at_unfold !monPred_at_in. by iDestruct "⊒Vi@V0" as %?. }
  set M := {[0%nat]}.
  set eVinit := mkOmoEvent Init V0 M.
  set initst := (0%nat, false, V0, M).

  iMod (@OmoAuth_alloc _ _ _ _ _ eVinit initst _ _ lock_interpretable with "WCOMMIT") as (γg γs)
        "(M● & #M◯ & #e0↦el0 & #e0✓eVinit & #e0↪init & WCOMMIT)"; [by apply lock_step_Init|done|].
  iMod (OmoHb_new_1 with "M● e0✓eVinit el0✓eVl0") as "[M● #e0⊒el0]"; [rewrite eVl0SYNC;solve_lat|].
  iDestruct (OmoHbToken_finish with "M●") as "M●".
  iMod (CWMono_new γg γl) as (γm) "MONO".
  iMod (CWMono_insert_last_last (wr_event 0) with "MONO M● Ml● e0↦el0") as "(MONO & #MONO✓e0 & M● & Ml●)"; [done|done|].
  iMod (meta_set _ _ (γl,γs,γsl,γm) nroot with "Hms") as "#Hms"; [done|].
  iDestruct (view_at_intro with "omol↦") as (Vb) "[#⊒Vb omol↦]".
  rewrite shift_0. iApply ("Hφ" $! γg γs l V0 M). iModIntro. iFrame "⊒V0 WCOMMIT". iSplitL; last iSplit; [..|done].
  - unfold LockInv. do 5 iExists _. iExists initst,_,∅,cas_only,_. iFrame. iFrame "Hms".
    iSplitL "omol↦"; [eauto with iFrame|]. iSplitR; last iSplitL; last iSplit.
    + rewrite /AllWrEvents big_sepL_singleton. repeat iExists _. iFrame "#". by rewrite HeVl0.
    + iExists 0%nat,_,0%Z,_,eVinit. simpl. iFrame "P@V0". iFrame "#". iPureIntro. split_and!; try done. by rewrite HeVl0.
    + rewrite /seen_event_info big_sepL_singleton. iExists 0. iFrame "#".
    + iPureIntro. split; [done|]. set_solver-.
  - repeat iExists _. iFrame "#".
Qed.

Definition do_lock_spec :
  do_lock_spec' code_spin_lock.do_lock LockLocal LockInv Locked.
Proof.
  intros N DISJ l tid γg M V0. iIntros "#⊒V0 #LockLocal" (Φ) "AU".
  iDestruct "LockLocal" as (???? Ml0) "(MS & M◯0 & Ml◯0)".

  wp_lam. iLöb as "IH". wp_pures. wp_bind (casᵃᶜ(_, _, _))%E.

  (* Inv access *)
  iMod "AU" as (? E1 omo1 stlist1 P) "[LockInv CLOSE]".
  iDestruct "LockInv" as (??? El1 omol1 stf1 mo1 uf1 ty1 Mono1)
    "(>MS' & >M●1 & >Ml●1 & >[%Vb1 omol↦1] & >#AllWrEvents1 & LASTMSG1 & >#SeenEs1 & >MONO1 & >%LASTST & >%NINCLnc1)".
  iDestruct "LASTMSG1" as (elf1 eVlf1 vf1 Vf1 eVf1)
    "((>%LAST1 & >%eVlf1EV & >%eVf1SYNC & >%eVf1EVIEW) & >#elf1✓eVlf1 & >#ef1✓eVf1 & >#ef1↦elf1 & >#ef1↪stf1 & CASEvf1)".
  simplify_meta with "MS' MS".

  (* Prepare for CAS *)
  iDestruct (view_at_intro_incl with "M◯0 ⊒V0") as (V0') "(#⊒V0' & %LeV0V0' & #M◯0A)".
  iMod (rel_objectively_intro (⊒∅) tid with "[]") as "⊒∅".
    { iApply objective_objectively. iApply monPred_in_bot. }

  wp_apply (append_only_loc_cas_general _ _ _ _ _ _ _ uf1 _ _ _ _ (LitInt 0%Z) 1 _ ∅ with "[$Ml●1 $Ml◯0 $omol↦1 $⊒V0' ⊒∅]"); try done.
  iIntros (b1 el1 gen1 vr1 Vr1 V1 mo1' omol1' eVl1 eVln1)
    "(Pures & #MAXgen_el1 & #el1✓eVl1 & #eln1✓eVln1 & Ml●1 & #⊒V1 & #Ml◯1 & CASE)".
  iDestruct "Pures" as %(Eqgen1 & eVl1EV & LeV0'V1).
  iDestruct "CASE" as "[(Pures & _ & omol↦1 & #el1=eln1 & RCOMMIT) | [Pures sVw1]]".
  { (* CAS failed, retry *)
    iDestruct "Pures" as %(-> & NEvr1 & -> & EQomol1' & eVln1EV & eVln1SYNC).
    iDestruct "CLOSE" as "[Abort _]".
    iMod ("Abort" with "[-]") as "AU"; last first. { iModIntro. wp_let. wp_op. wp_if. by iApply "IH". }
    iExists _,_,_,_,omol1'. iExists stf1,_,uf1,ty1,_. iFrame "∗#". subst omol1'. rewrite omo_insert_r_write_op. iFrame "#".
    iSplitL "omol↦1"; [eauto with iFrame|]. iSplitL; [|done]. iExists elf1,eVlf1,vf1,_,eVf1. iFrame "CASEvf1". by iFrame "#". }

  (* CAS success, commit *)
  iDestruct "Pures" as %(-> & -> & ->).
  iDestruct "sVw1" as (Vw1 (Eqmo1' & Homol1' & eVln1EV & eVln1SYNC & LeVr1Vw1 & NEqVr1Vw1 & NLeV1Vr1 & NEqV0'V1 & LeEmpVw1))
    "(_ & omol↦1 & %LEVw1V1 & WCOMMIT)".
  destruct (decide (vf1 = 0%Z)) as [->|NEQ]; last first.
  { rewrite last_lookup -omo_write_op_length in LAST1. replace (Init.Nat.pred (length omol1)) with (length omol1 - 1)%nat in LAST1 by lia.
    rewrite LAST1 in Eqgen1. inversion Eqgen1. subst elf1.
    iDestruct (OmoEinfo_agree with "elf1✓eVlf1 el1✓eVl1") as %<-. rewrite eVl1EV in eVlf1EV. inversion eVlf1EV. done. }
  iDestruct "CASEvf1" as "[P (-> & %Hstf1 & %LEstf1Vf1)]".

  iAssert (⌜ elf1 = el1 ∧ Vf1 = Vr1 ⌝)%I with "[]" as %[-> ->].
  { rewrite last_lookup in LAST1. rewrite omo_write_op_length in Eqgen1.
    replace (Init.Nat.pred (length (omo_write_op omol1))) with (length (omo_write_op omol1) - 1)%nat in LAST1; [|lia].
    rewrite LAST1 in Eqgen1. inversion Eqgen1. subst elf1.
    iDestruct (OmoEinfo_agree with "el1✓eVl1 elf1✓eVlf1") as %<-. rewrite eVlf1EV in eVl1EV. by inversion eVl1EV. }

  have LeV0V1 : V0 ⊑ V1 by solve_lat.
  set lockId := length E1.
  set M' := {[lockId; stf1.1.1.1]} ∪ stf1.2 ∪ M.
  set egV' := mkOmoEvent Lock V1 M'.
  set E1' := E1 ++ [egV'].
  set lockst := (lockId, true, V1, M').
  set omo2' := omo_append_w omo1 lockId [].
  have SubE1E1' : E1 ⊑ E1' by apply prefix_app_r.

  iDestruct (view_at_mono_2 _ V1 with "M◯0A") as "M◯0A'"; [solve_lat|].
  iDestruct (OmoEview_insert_new_obj with "M◯0A' ef1✓eVf1") as "#M◯0A''"; [rewrite eVf1SYNC;solve_lat|].

  iMod (OmoAuth_insert_last with "M●1 M◯0A'' WCOMMIT []")
    as "(M●1 & #M◯1A & #en1↦eln1 & #en1✓egV' & #en1↪lockst & WCOMMIT)".
  { iPureIntro. have ? : step lockId egV' stf1 lockst.
    { destruct stf1 as [[[a b] c] d]. simpl in Hstf1, LEstf1Vf1. subst b egV' M'. apply lock_step_Lock; [done|solve_lat|set_solver-]. }
    split_and!; try done. subst egV' M' lockId. rewrite eVf1EVIEW /=. set_solver-. }
  iMod (OmoHb_new_1 with "M●1 en1✓egV' eln1✓eVln1") as "[M●1 #en1⊒eln1]"; [rewrite eVln1SYNC;solve_lat|].
  iDestruct (OmoHbToken_finish with "M●1") as "M●1".
  iMod (@CWMono_insert_last_last _ loc_event _ _ _ _ _ _ (wr_event (length omo1)) with "MONO1 M●1 [Ml●1] en1↦eln1") as "(MONO1 & #MONO✓en1 & M●1 & Ml●1)".
  { by rewrite lookup_omo_wr_event omo_append_w_write_op omo_write_op_length lookup_app_1_eq. } { by rewrite omo_append_w_length Nat.add_sub. }
  { subst omol1'. iFrame. }

  iDestruct (view_at_elim with "⊒V1 Ml◯1") as "Ml◯1'".
  iDestruct (cas_only_to_swriter_obj _ _ _ _ _ _ _ _ (length El1) (wr_event (length omol1)) with "Ml●1 Ml◯1' omol↦1")
    as "(Ml●1 & omol↦1 & omolSW)".
  { set_solver-. } { subst omol1'. by rewrite lookup_omo_wr_event omo_append_w_write_op omo_write_op_length lookup_app_1_eq. }
  { subst omol1'. rewrite omo_append_w_length /=. lia. }

  iDestruct "CLOSE" as "[_ Commit]".
  iDestruct (OmoUB_singleton with "en1✓egV'") as "MAXen1".
  iDestruct (big_sepS_subseteq _ _ M with "MAXen1") as "MAXen1'"; [set_solver-|].
  iMod ("Commit" $! V1 lockst M' with "[-P omolSW]") as "HΦ"; last first.
  { iModIntro. wp_pures. iApply "HΦ".
    iDestruct (view_at_mono_2 _ V1 with "P") as "P"; [solve_lat|].
    iDestruct (view_at_elim with "⊒V1 P") as "P". iFrame.
    iDestruct (view_at_elim with "⊒V1 M◯1A") as "M◯1".
    iExists _,_,_,_,_,_,(length E1),(length El1). iExists lockst. iFrame "∗#".
    iPureIntro. split.
    - subst omol1'. by rewrite omo_append_w_write_op last_app.
    - subst lockst lockId M'. rewrite eVf1EVIEW. simpl. set_solver-. }

  iFrame "⊒V1 WCOMMIT MAXen1'". iSplitL; last iSplit.
  - iExists _,_,_,(El1 ++ [eVln1]),omol1'. iExists lockst,_,uf1,swriter,_. subst omol1'. iFrame "∗#".
    iSplitL; [eauto with iFrame|]. rewrite omo_append_w_write_op. iSplit; last iSplit; last iSplit; last iSplit.
    + rewrite /AllWrEvents big_sepL_snoc. iFrame "#". iExists _,_,_,_,_,_. iFrame "#". by rewrite eVln1EV.
    + iExists (length El1),_,1%Z,_,_. iFrame "#". iSplit; [|done].
      iPureIntro. split_and!; try done; [by rewrite last_app|by rewrite eVln1EV].
    + rewrite big_sepL_singleton. iExists (length El1). rewrite Nat.add_0_r. iFrame "#".
    + by rewrite last_app.
    + done.
  - iExists γl. repeat iExists _. rewrite eVf1EVIEW. iFrame "#".
    replace ({[length E1]} ∪ ({[stf1.1.1.1]} ∪ stf1.2 ∪ M)) with M'; [iFrame "#"|set_solver-].
  - iPureIntro. split_and!; try done. set_solver-.
Qed.

Definition try_lock_spec :
  try_lock_spec' code_spin_lock.try_lock LockLocal LockInv Locked.
Proof.
  intros N DISJ l tid γg M V0. iIntros "#⊒V0 #LockLocal" (Φ) "AU".
  iDestruct "LockLocal" as (???? Ml0) "(MS & M◯0 & Ml◯0)". wp_lam.

  (* Inv access *)
  iMod "AU" as (? E1 omo1 stlist1 P) "[LockInv CLOSE]".
  iDestruct "LockInv" as (??? El1 omol1 stf1 mo1 uf1 ty1 Mono1)
    "(>MS' & >M●1 & >Ml●1 & >[%Vb1 omol↦1] & >#AllWrEvents1 & LASTMSG1 & >#SeenEs1 & >MONO1 & >%LASTST & >%NINCLnc1)".
  iDestruct "LASTMSG1" as (elf1 eVlf1 vf1 Vf1 eVf1)
    "((>%LAST1 & >%eVlf1EV & >%eVf1SYNC & >%eVf1EVIEW) & >#elf1✓eVlf1 & >#ef1✓eVf1 & >#ef1↦elf1 & >#ef1↪stf1 & CASEvf1)".
  simplify_meta with "MS' MS".

  (* Prepare for CAS *)
  iDestruct (view_at_intro_incl with "M◯0 ⊒V0") as (V0') "(#⊒V0' & %LeV0V0' & #M◯0A)".
  iMod (rel_objectively_intro (⊒∅) tid with "[]") as "⊒∅".
    { iApply objective_objectively. iApply monPred_in_bot. }
  iDestruct (OmoEview_update with "M●1 M◯0 Ml◯0") as (Ml0') "(M●1 & #Ml◯0' & M⊢Ml0' & %LEMl0Ml0')".

  wp_apply (append_only_loc_cas_general _ _ _ _ _ _ _ uf1 _ _ _ _ (LitInt 0%Z) 1 _ ∅ with "[$Ml●1 $Ml◯0' $omol↦1 $⊒V0' ⊒∅]"); try done.
  iIntros (b1 el1 gen1 vr1 Vr1 V1 mo1' omol1' eVl1 eVln1)
    "(Pures & #MAXgen_el1 & #el1✓eVl1 & #eln1✓eVln1 & Ml●1 & #⊒V1 & #Ml◯1 & CASE)".
  iDestruct "Pures" as %(Eqgen1 & eVl1EV & LeV0'V1).
  iDestruct "CASE" as "[(Pures & _ & omol↦1 & #el1=eln1 & RCOMMIT) | [Pures sVw1]]".
  { (* CAS failed, commit Trylock *)
    iDestruct "Pures" as %(-> & NEvr1 & -> & EQomol1' & eVln1EV & eVln1SYNC).
    iDestruct (AllWrEvents_acc _ _ _ _ _ el1 with "AllWrEvents1")
      as "(%vr1' & %Vr1' & %eVl1' & %e1 & %eV1 & %st1 & #el1✓eVl1' & #e1✓eV1 & #e1↦el1 & #MONO✓e1 & #e1↪st1 & %eVl1'EV & %Equiv)".
    { rewrite elem_of_list_lookup. by eexists. }
    iAssert (⌜ eVl1 = eVl1' ∧ eq vr1 vr1' ∧ Vr1 = Vr1' ⌝)%I with "[]" as %(<- & -> & <-).
    { iDestruct (OmoEinfo_agree with "el1✓eVl1 el1✓eVl1'") as %<-. rewrite eVl1'EV in eVl1EV. by inversion eVl1EV. }

    iAssert (OmoUB γg M e1)%I with "[-]" as "#MAXgen_e1".
    { iApply big_sepS_forall. iIntros "%e %eM".
      iDestruct (OmoAuth_OmoEview with "M●1 M◯0") as %MIncl.
      specialize (MIncl _ eM) as [eV Elookup].
      rewrite /seen_event_info big_sepL_lookup; [|done]. iDestruct "SeenEs1" as "(%e' & e⊒e' & e↦e' & MONO✓e)".
      iDestruct (OmoHb_HbIncluded with "e⊒e' M⊢Ml0'") as %e'Ml0'; [done|].
      iDestruct (big_sepS_elem_of with "MAXgen_el1") as "e'≤el1"; [exact e'Ml0'|].
      iApply (CWMono_acc with "MONO1 MONO✓e MONO✓e1 e↦e' e1↦el1 e'≤el1"). }

    have LeV0V1 : V0 ⊑ V1 by solve_lat.
    set tryId := length E1.
    set M' := {[tryId]} ∪ M.
    set egV' := mkOmoEvent Trylock V1 M'.
    set E1' := E1 ++ [egV'].
    have SubE1E1' : E1 ⊑ E1' by apply prefix_app_r.

    iDestruct (view_at_mono_2 _ V1 with "M◯0A") as "M◯0A'"; [solve_lat|].
    iMod (OmoAuth_insert_ro _ _ _ _ _ _ _ _ _ _ egV' st1 with "M●1 M◯0A' RCOMMIT e1↪st1 MAXgen_e1 []")
      as (gen1') "(M●1 & #M◯0A'' & #en1↦eln1 & #e1=en1 & #en1✓egV' & RCOMMIT & _)".
    { iPureIntro. split_and!; try done.
      destruct st1 as [[[a b] c] d]. simpl in *.
      destruct b; last first. { have EQ : vr1' = 0%Z by apply Equiv. subst vr1'. by inversion NEvr1. }
      apply lock_step_Trylock; try done. subst egV' M'. set_solver-. }
    iMod (OmoHb_new_1 with "M●1 en1✓egV' eln1✓eVln1") as "[M●1 #en1⊒eln1]"; [rewrite eVln1SYNC;solve_lat|].
    iDestruct (OmoHbToken_finish with "M●1") as "M●1".
    iMod (CWMono_insert_Eq with "MONO1 MONO✓e1 e1↦el1 en1↦eln1 e1=en1 el1=eln1") as "[MONO1 #MONO✓en1]".

    iDestruct (OmoLe_get_from_Eq with "e1=en1") as "e1≤en1".
    iDestruct (OmoUB_mono with "MAXgen_e1 e1≤en1") as "MAXen1".
    iDestruct "CLOSE" as "[_ Commit]".
    iMod ("Commit" $! false V1 Trylock _ _ M' with "[-]") as "HΦ"; last first. { iModIntro. by iApply "HΦ". }
    iFrame "⊒V1 RCOMMIT MAXen1". iSplitL; last iSplit.
    - iExists _,_,_,_,omol1'. iExists stf1,_,uf1,ty1,_. iFrame "∗#". subst omol1'. rewrite omo_insert_r_write_op.
      iFrame "#". iSplitL "omol↦1"; [eauto with iFrame|]. iSplitL; last iSplit; [..|done].
      + iExists elf1,eVlf1,vf1,_,eVf1. simpl. iFrame "elf1✓eVlf1 ef1✓eVf1 ef1↦elf1 CASEvf1". by iPureIntro.
      + rewrite big_sepL_singleton. iExists _. rewrite Nat.add_0_r. iFrame "#".
    - iExists γl. repeat iExists _. by iFrame "#".
    - iPureIntro. split_and!; try done; [set_solver-|]. by eexists. }

  (* CAS success -> lock should be in unlocked state *)
  iDestruct "Pures" as %(-> & -> & ->).
  iDestruct "sVw1" as (Vw1 (Eqmo1' & Homol1' & eVln1EV & eVln1SYNC & LeVr1Vw1 & NEqVr1Vw1 & NLeV1Vr1 & NEqV0'V1 & LeEmpVw1))
    "(_ & omol↦1 & %LEVw1V1 & WCOMMIT)".
  destruct (decide (vf1 = 0%Z)) as [->|NEQ]; last first.
  { rewrite last_lookup -omo_write_op_length in LAST1. replace (Init.Nat.pred (length omol1)) with (length omol1 - 1)%nat in LAST1 by lia.
    rewrite LAST1 in Eqgen1. inversion Eqgen1. subst elf1.
    iDestruct (OmoEinfo_agree with "elf1✓eVlf1 el1✓eVl1") as %<-. rewrite eVl1EV in eVlf1EV. inversion eVlf1EV. done. }
  iDestruct "CASEvf1" as "[P (-> & %Hstf1 & %LEstf1Vf1)]".

  iAssert (⌜ elf1 = el1 ∧ Vf1 = Vr1 ⌝)%I with "[]" as %[-> ->].
  { rewrite last_lookup in LAST1. rewrite omo_write_op_length in Eqgen1.
    replace (Init.Nat.pred (length (omo_write_op omol1))) with (length (omo_write_op omol1) - 1)%nat in LAST1; [|lia].
    rewrite LAST1 in Eqgen1. inversion Eqgen1. subst elf1.
    iDestruct (OmoEinfo_agree with "el1✓eVl1 elf1✓eVlf1") as %<-. rewrite eVlf1EV in eVl1EV. by inversion eVl1EV. }

  have LeV0V1 : V0 ⊑ V1 by solve_lat.
  set lockId := length E1.
  set M' := {[lockId; stf1.1.1.1]} ∪ stf1.2 ∪ M.
  set egV' := mkOmoEvent Lock V1 M'.
  set E1' := E1 ++ [egV'].
  set lockst := (lockId, true, V1, M').
  set omo2' := omo_append_w omo1 lockId [].
  have SubE1E1' : E1 ⊑ E1' by apply prefix_app_r.

  iDestruct (view_at_mono_2 _ V1 with "M◯0A") as "M◯0A'"; [solve_lat|].
  iDestruct (OmoEview_insert_new_obj with "M◯0A' ef1✓eVf1") as "#M◯0A''"; [rewrite eVf1SYNC;solve_lat|].

  iMod (OmoAuth_insert_last with "M●1 M◯0A'' WCOMMIT []")
    as "(M●1 & #M◯1A & #en1↦eln1 & #en1✓egV' & #en1↪lockst & WCOMMIT)".
  { iPureIntro. have ? : step lockId egV' stf1 lockst.
    { destruct stf1 as [[[a b] c] d]. simpl in Hstf1, LEstf1Vf1. subst b egV' M'. apply lock_step_Lock; [done|solve_lat|set_solver-]. }
    split_and!; try done. subst egV' M' lockId. rewrite eVf1EVIEW /=. set_solver-. }
  iMod (OmoHb_new_1 with "M●1 en1✓egV' eln1✓eVln1") as "[M●1 #en1⊒eln1]"; [rewrite eVln1SYNC;solve_lat|].
  iDestruct (OmoHbToken_finish with "M●1") as "M●1".
  iMod (@CWMono_insert_last_last _ loc_event _ _ _ _ _ _ (wr_event (length omo1)) with "MONO1 M●1 [Ml●1] en1↦eln1") as "(MONO1 & #MONO✓en1 & M●1 & Ml●1)".
  { by rewrite lookup_omo_wr_event omo_append_w_write_op omo_write_op_length lookup_app_1_eq. } { by rewrite omo_append_w_length Nat.add_sub. }
  { subst omol1'. iFrame. }

  iDestruct (view_at_elim with "⊒V1 Ml◯1") as "Ml◯1'".
  iDestruct (cas_only_to_swriter_obj _ _ _ _ _ _ _ _ (length El1) (wr_event (length omol1)) with "Ml●1 Ml◯1' omol↦1")
    as "(Ml●1 & omol↦1 & omolSW)".
  { set_solver-. } { subst omol1'. by rewrite lookup_omo_wr_event omo_append_w_write_op omo_write_op_length lookup_app_1_eq. }
  { subst omol1'. rewrite omo_append_w_length /=. lia. }

  iDestruct (OmoUB_singleton with "en1✓egV'") as "MAXen1".
  iDestruct (big_sepS_subseteq _ _ M with "MAXen1") as "MAXen1'"; [set_solver-|].
  iDestruct "CLOSE" as "[_ Commit]".
  iMod ("Commit" $! true V1 Lock _ _ M' with "[-P omolSW]") as "HΦ"; last first.
  { iModIntro. wp_pures. iApply "HΦ".
    iDestruct (view_at_mono_2 _ V1 with "P") as "P"; [solve_lat|].
    iDestruct (view_at_elim with "⊒V1 P") as "P". iFrame.
    iDestruct (view_at_elim with "⊒V1 M◯1A") as "M◯1".
    iExists _,_,_,_,_,_,(length E1),(length El1). iExists lockst. iFrame "∗#".
    iPureIntro. split.
    - subst omol1'. by rewrite omo_append_w_write_op last_app.
    - subst lockst lockId M'. rewrite eVf1EVIEW. simpl. set_solver-. }

  iFrame "⊒V1 WCOMMIT MAXen1'". iSplitL; last iSplit.
  - iExists _,_,_,(El1 ++ [eVln1]),omol1'. iExists lockst,_,uf1,swriter,_. subst omol1'. iFrame "∗#".
    iSplitL; [eauto with iFrame|]. rewrite omo_append_w_write_op. iSplit; last iSplit; last iSplit; last iSplit.
    + rewrite /AllWrEvents big_sepL_snoc. iFrame "#". iExists _,_,_,_,_,_. iFrame "#". by rewrite eVln1EV.
    + iExists (length El1),_,1%Z,_,_. iFrame "#". iSplit; [|done].
      iPureIntro. split_and!; try done; [by rewrite last_app|by rewrite eVln1EV].
    + rewrite big_sepL_singleton. iExists (length El1). rewrite Nat.add_0_r. iFrame "#".
    + by rewrite last_app.
    + done.
  - iExists γl. repeat iExists _. rewrite eVf1EVIEW. iFrame "#".
    replace ({[length E1]} ∪ ({[stf1.1.1.1]} ∪ stf1.2 ∪ M)) with M'; [iFrame "#"|set_solver-].
  - iPureIntro. split_and!; try done; [set_solver-|]. by eexists.
Qed.

Definition unlock_spec :
  unlock_spec' code_spin_lock.unlock LockLocal LockInv Locked.
Proof.
  intros N DISJ l tid γg M V0 P. iIntros "#⊒V0 #LockLocal P Locked" (Φ) "AU".
  iDestruct "LockLocal" as (???? Ml0) "(MS & M◯0 & Ml◯0)".
  wp_lam. wp_bind (_ <-ʳᵉˡ _)%E.

  (* Inv access *)
  iMod "AU" as (? E1 omo1 stlist1) "[LockInv CLOSE]".
  iDestruct "LockInv" as (??? El1 omol1 stf1 mo1 uf1 ty1 Mono1)
    "(>MS' & >M●1 & >Ml●1 & >[%Vb1 omol↦1] & >#AllWrEvents1 & LASTMSG1 & >#SeenEs1 & >MONO1 & >%LASTST & >%NINCLnc1)".
  iDestruct "LASTMSG1" as (elf1 eVlf1 vf1 Vf1 eVf1)
    "((>%LAST1 & >%eVlf1EV & >%eVf1SYNC & >%eVf1EVIEW) & >#elf1✓eVlf1 & >#ef1✓eVf1 & >#ef1↦elf1 & >#ef1↪stf1 & CASEvf1)".
  simplify_meta with "MS' MS". iClear "MS'".

  (* Access [Locked] *)
  iDestruct "Locked" as (???? es M' ef elf stf) "(MS' & omolSW & #M◯0' & #ef↦elf & #ef↪stf & (%LASTes & %M'IN & %M'INCL))".
  simplify_meta with "MS' MS". iClear "MS'".
  iDestruct (swriter_token_type_obj_2 with "omolSW omol↦1") as %->.
  iDestruct (OmoEview_union with "M◯0 M◯0'") as "#M◯1".
  iDestruct (view_at_intro_incl with "M◯1 ⊒V0") as (V0') "(#⊒V0' & %LEV0V0' & #M◯1A)".

  destruct (decide (vf1 = 0%Z)) as [->|NEvf1]; [by iDestruct "CASEvf1" as "[_ >[% _]]"|].
  iDestruct "CASEvf1" as ">[_ %Hstf1]".

  iAssert (⌜ elf = elf1 ∧ stf = stf1 ⌝)%I with "[M●1 Ml●1 omol↦1 omolSW]" as %[-> ->].
  { iDestruct (OmoAuth_swriter_token_agree_obj_2 with "Ml●1 omol↦1 omolSW") as %->.
    rewrite LASTes in LAST1. inversion LAST1. subst elf.
    iDestruct (OmoCW_agree_2 with "ef1↦elf1 ef↦elf") as %[_ <-].
    by iDestruct (OmoSnap_agree with "ef1↪stf1 ef↪stf") as %->. }
  iDestruct (OmoEinfo_OmoEview with "ef1✓eVf1 M◯0'") as "#⊒eVf1"; [set_solver|].
  iCombine "⊒V0' ⊒eVf1" as "⊒V0''".
  rewrite monPred_in_view_op.

  wp_apply (append_only_loc_release_write _ _ _ _ _ _ _ _ _ _ _ _ 0 P
      with "[$Ml●1 $Ml◯0 $omol↦1 $omolSW $⊒V0'' $P]"); [done|done|].

  iIntros (V1 eVln1 el1 eVl1) "(PURES & #⊒V1 & Ml●1 & WCOMMIT & #el1✓eVl1 & #eln1✓eVln1 & (omolSW & #Ml◯1 & P) & omol↦1)".
  iDestruct "PURES" as %(LASTel1 & LEV0''V1 & NEqV0''V1 & eVln1EV & eVln1SYNC).

  iAssert (⌜ el1 = elf1 ∧ eVl1 = eVlf1 ⌝)%I with "[]" as %[-> ->].
  { rewrite LAST1 in LASTel1. inversion LASTel1. subst el1.
    by iDestruct (OmoEinfo_agree with "elf1✓eVlf1 el1✓eVl1") as %<-. } iClear "el1✓eVl1".

  have LeV0V1 : V0 ⊑ V1 by solve_lat.
  set unlockId := length E1.
  set (M'' := {[unlockId]} ∪ (M ∪ M')).
  set egV' := mkOmoEvent Unlock V1 M''.
  set E1' := E1 ++ [egV'].
  set unlockst := (unlockId, false, V1, M'').
  set omo2' := omo_append_w omo1 unlockId [].
  have SubE1E1' : E1 ⊑ E1' by apply prefix_app_r.
  have LEV0'V0'' : V0' ⊑ (V0' ⊔ eVf1.(sync)) by solve_lat.
  have LEeVlf1V0'' : eVf1.(sync) ⊑ (V0' ⊔ eVf1.(sync)) by solve_lat.

  iDestruct (view_at_mono_2 _ V1 with "M◯1A") as "M◯1A'"; [solve_lat|].
  iMod (OmoAuth_insert_last with "M●1 M◯1A' WCOMMIT []")
    as "(M●1 & #M◯1A'' & #en1↦eln1 & #en1✓egV' & #en1↪unlockst & WCOMMIT)".
  { iPureIntro. have ? : step unlockId egV' stf1 unlockst; [|done].
    destruct stf1 as [[[a b] c] d]. simpl in Hstf1, M'IN, M'INCL, eVf1SYNC. subst b egV' c.
    apply lock_step_Unlock; simpl; [done|solve_lat|set_solver]. }
  iMod (OmoHb_new_1 with "M●1 en1✓egV' eln1✓eVln1") as "[M●1 #en1⊒eln1]"; [rewrite eVln1SYNC;solve_lat|].
  iDestruct (OmoHbToken_finish with "M●1") as "M●1".
  iMod (@CWMono_insert_last_last _ loc_event _ _ _ _ _ _ (wr_event (length omo1)) with "MONO1 M●1 Ml●1 en1↦eln1") as "(MONO1 & #MONO✓en1 & M●1 & Ml●1)".
  { by rewrite lookup_omo_wr_event omo_append_w_write_op omo_write_op_length lookup_app_1_eq. } { by rewrite omo_append_w_length Nat.add_sub. }
  iDestruct (swriter_to_cas_only_obj_1 with "omol↦1 omolSW") as "omol↦1".

  iDestruct (OmoUB_singleton with "en1✓egV'") as "MAXen1".
  iDestruct (big_sepS_subseteq _ _ M with "MAXen1") as "MAXen1'"; [set_solver-|].
  iDestruct "CLOSE" as "[_ Commit]".
  iMod ("Commit" $! V1 unlockst ({[unlockId]} ∪ (M ∪ M')) with "[-]") as "HΦ"; last first.
  { iModIntro. wp_pures. by iApply "HΦ". }

  iFrame "⊒V1 WCOMMIT MAXen1'". iSplitL; last iSplit.
  - iExists _,_,_,(El1 ++ [eVln1]),(omo_append_w omol1 _ _). iExists unlockst,_,_,cas_only,_.
    rewrite omo_append_w_write_op. iFrame "∗". iFrame "MS". iSplitL "omol↦1"; [eauto with iFrame|].
    iNext. iSplitR; last iSplitL; last iSplit.
    + rewrite /AllWrEvents big_sepL_snoc. iFrame "#". iExists _,_,_,_,_,_. iFrame "#". by rewrite eVln1EV.
    + iExists (length El1),_,0%Z,_,_. simpl. iFrame "eln1✓eVln1 en1✓egV' en1↦eln1 en1↪unlockst P". iSplit; [|done].
      iPureIntro. split_and!; try done; [by rewrite last_app|by rewrite eVln1EV].
    + rewrite /seen_event_info big_sepL_snoc. iFrame "#". iExists _. iFrame "#".
    + iPureIntro. split; [by rewrite last_app|]. rewrite eVlf1EV. simpl. set_solver.
  - iExists γl. repeat iExists _. by iFrame "#".
  - iPureIntro. split_and!; try done. set_solver-.
Qed.

End spinlock.

Definition spinlock_trylock_impl `{!noprolG Σ, !atomicG Σ, !omoGeneralG Σ, !omoSpecificG Σ lock_event_type lock_state, !appendOnlyLocG Σ}
  : lock_spec Σ := {|
    spec_trylock_composition.LockInv_Linearizable := LockInv_Linearizable_instance;
    spec_trylock_composition.LockInv_OmoAuth_acc := LockInv_OmoAuth_acc_instance;
    spec_trylock_composition.LockLocal_OmoEview := LockLocal_OmoEview_instance;
    spec_trylock_composition.new_lock_spec := new_lock_spec;
    spec_trylock_composition.do_lock_spec := do_lock_spec;
    spec_trylock_composition.try_lock_spec := try_lock_spec;
    spec_trylock_composition.unlock_spec := unlock_spec;
  |}.
