From gpfsl.examples Require Import sflib.

From iris.algebra Require Import auth gset gmap agree.
From iris.algebra Require Import lib.mono_list.
From iris.proofmode Require Import tactics.
From iris.base_logic.lib Require Import ghost_var ghost_map.

From gpfsl.base_logic Require Import meta_data.
From gpfsl.examples.algebra Require Import mono_list_list saved_vprop.
From gpfsl.logic Require Import logatom atomics invariants.

From gpfsl.logic Require Import repeat_loop new_delete.
From gpfsl.examples Require Import uniq_token map_seq loc_helper.
From gpfsl.examples.omo Require Import omo omo_preds append_only_loc.
From gpfsl.examples.exchanger Require Import spec_composition_diaframe code_split.

From gpfsl.diaframe Require Import vprop_weakestpre spec_notation
 vprop_weakestpre_logatom atom_spec_notation proof_automation omo_specs omo_hints ghost_map_hints.
From diaframe Require Import proofmode_base lib.except_zero own_hints steps.verify_tac util_instances.
From diaframe.symb_exec Require Import weakestpre_logatom.
 From Hammer Require Import Tactics.

 Require Import iris.prelude.options.

Class xchgG Σ := XchgG {
  xchg_emoGeneralG :> omoGeneralG Σ;
  xchg_xchgG :> omoSpecificG Σ xchg_event xchg_state;
  xchg_aolG :> appendOnlyLocG Σ;
  xchg_stlG :> ghost_mapG Σ event_id (Z * view * eView);
  xchg_strG :> ghost_mapG Σ event_id (event_id * Z * view * eView);
  xchg_OFG :> ghost_mapG Σ event_id loc;
  xchg_uniqTokG :> uniqTokG Σ;
}.

Definition xchgΣ : gFunctors := #[omoGeneralΣ; omoSpecificΣ xchg_event xchg_state; appendOnlyLocΣ; ghost_mapΣ event_id (Z * view * eView); ghost_mapΣ event_id (event_id * Z * view * eView); ghost_mapΣ event_id loc; uniqTokΣ].

Global Instance subG_xchgΣ {Σ} : subG xchgΣ Σ → xchgG Σ.
Proof. solve_inG. Qed.

Section Xchg.
Context `{!noprolG Σ, !atomicG Σ, !xchgG Σ}.

Local Notation iProp := (iProp Σ).
Local Notation vProp := (vProp Σ).
Local Open Scope nat_scope.

Implicit Types
  (γg γs γx γsx γl γsl γstl γstr γu γof : gname)
  (omo omox omol : omoT) (x l : loc) (mox mol : list loc_state)
  (OF : gmap event_id loc) (stl : xchg_state_l) (str : xchg_state_r)
  (eV : omo_event xchg_event) (xeV : omo_event loc_event)
  (E : history xchg_event) (El Ex : history loc_event).

Definition xchgN (N : namespace) := N .@ "xchg".

Definition CheckToken γg (x l : loc) (e : event_id) : vProp :=
  ∃ γs γx γsx γof γstl γstr γl γsl γu,
    meta x nroot (γs,γx,γsx,γof,γstl,γstr) ∗
    meta l nroot (γl,γsl,γu) ∗
    ⎡e ↪[γof]□ l⎤ ∗ OmoEview γl {[0%nat]} ∗ UTok γu.

Definition AllWritesInner γg γx γof xe : vProp :=
  ∃ xeV v V,
    OmoEinfo γx xe xeV ∗
    MatchValue (v, V) (loc_event_msg xeV.(type)) ∗
    ((⌜ v = #0 ⌝) (* Null value is written *)
    ∨ (∃ (l : loc) e eV, ⌜ v = #l ⌝ ∗ ⎡e ↪[γof]□ l⎤ ∗ OmoEinfo γg e eV ∗ ⌜ eV.(sync) ⊑ V ⌝ )). (* Offer is written *)

Definition AllWrites γg γx γof (xes : list event_id) : vProp :=
  [∗ list] xe ∈ xes, AllWritesInner γg γx γof xe.


Definition AllOffersInnerCase γg γstl γstr e γl γu omol (v : Z) eV : vProp :=
  ( (⌜ omo_write_op omol = [0] ⌝ ∗ ⎡e ↪[γstl] (v, eV.(sync), eV.(eview))⎤) (* Offer registered *)
      ∨ (∃ el eVl v V, ⌜ omo_write_op omol = [0; el] ⌝ ∗ OmoEinfo γl el eVl ∗ MatchValue (v, V) (loc_event_msg eVl.(type)) ∗ ⌜ v ≠ #(-1) ⌝ ∗
          ( (UTok γu ∗ ⌜ v = #(-2) ⌝) (* Offer revoked by registerer *)
          ∨ (∃ e' eV' (v' : Z) eV'_sync eV'_eview, ⌜ v = #v' ∧ (0 ≤ v')%Z ⌝ ∗ ⎡e ↪[γstr]□ (e', v', eV'_sync, eV'_eview)⎤ ∗ (* Offer accepted *)
            OmoEinfo γg e' eV' ∗ ⌜ eV'_sync = eV'.(sync) ∧ eV'_eview = eV'.(eview) ∧ eV'_sync ⊑ V ⌝ )))).


Definition AllOffersInner γg γstl γstr e l : vProp :=
  ∃ γl γsl γu El omol mol Vbl q (v : Z) eV (eVl0 : omo_event loc_event) eVl0_type_V,
      meta l nroot (γl,γsl,γu) ∗
      OmoAuth γl γsl (1/2)%Qp El omol mol _ ∗
      @{Vbl} append_only_loc l γl ∅ cas_only ∗
      OmoEinfo γg e eV ∗ OmoEinfo γl 0 eVl0 ∗
      @{eV.(sync)} (OmoEview γl {[0%nat]} ∗ (l >> 1) ↦{q} #v) ∗
      MatchValue (#(-1), eVl0_type_V) (loc_event_msg eVl0.(type)) ∗
      ⌜ (0 ≤ v)%Z ⌝ ∗
      AllOffersInnerCase γg γstl γstr e γl γu omol v eV.

Definition AllOffers γg γstl γstr OF : vProp :=
  [∗ map] e↦l ∈ OF,
    AllOffersInner γg γstl γstr e l.

Definition OF_valid E OF : Prop :=
  ∀ e, is_Some (OF !! e) → e < length E.

Definition stl_valid E stl : Prop :=
  ∀ e, is_Some (stl !! e) → e < length E.

Definition str_valid E str : Prop :=
  ∀ e, is_Some (str !! e) → e < length E.

Definition stl_str_valid stl str : Prop :=
  ∀ e, ¬(is_Some (stl !! e) ∧ is_Some (str !! e)).

Definition XchgInternalInv γg x E : vProp :=
  ∃ γs γx γsx γof γstl γstr Ex omo omox stlist mox OF stl str Vb oOF,
    meta x nroot (γs,γx,γsx,γof,γstl,γstr) ∗
    @{Vb} append_only_loc x γx ∅ cas_only ∗
    try_update_OmoAuth_to γg E omo stlist ∗
    try_update_OmoAuth_to γx Ex omox mox ∗

    ⌜ last stlist = Some (stl, str) ⌝ ∗
    ask_optional oOF OF ∗

    ⎡ghost_map_auth γof 1 OF⎤ ∗
    ⎡ghost_map_auth γstl 1 stl⎤ ∗
    ⎡ghost_map_auth γstr 1 str⎤ ∗

    AllWrites γg γx γof (omo_write_op omox) ∗
    AllOffers γg γstl γstr OF ∗

    ⌜ OF_valid E OF ∧ stl_valid E stl ∧ str_valid E str ∧ stl_str_valid stl str ⌝ ∗

    OmoAuth γg γs (1/2)%Qp E omo stlist _ ∗
    OmoAuth γx γsx (1/2)%Qp Ex omox mox _.

Definition InternalInv_inner γg x : vProp := ∃ E, XchgInternalInv γg x E ∗ emp.
Definition InternInv N γg x := inv (xchgN N) (InternalInv_inner γg x).

Definition XchgInv γg γs (x : loc) E omo stlist : vProp :=
  try_update_OmoAuth_to γg E omo stlist ∗ OmoAuth γg γs (1/2)%Qp E omo stlist _ .

Definition XchgLocal (N : namespace) γg x M : vProp :=
  ∃ γs γx γsx γof γstl γstr Mx,
    meta x nroot (γs,γx,γsx,γof,γstl,γstr) ∗
    InternInv N γg x ∗

    OmoEview γg M ∗
    OmoEview γx Mx.

Local Tactic Notation "simplify_meta" "with" constr(Hs) :=
  iDestruct (meta_agree with Hs) as %[[[[[-> ->]%pair_inj ->]%pair_inj ->]%pair_inj ->]%pair_inj ->]%pair_inj.

Local Tactic Notation "simplify_meta3" "with" constr(Hs) :=
  iDestruct (meta_agree with Hs) as %[[-> ->]%pair_inj ->]%pair_inj.

Lemma XchgInv_Linearizable_instance :
  ∀ γg γs x E omo stlist, XchgInv γg γs x E omo stlist ⊢ ⌜ Linearizability_omo E omo stlist ⌝.
Proof.
  iIntros (??????) "[_ M●]". by iDestruct (OmoAuth_Linearizable with "M●") as %H.
Qed.

Lemma XchgInv_OmoAuth_acc_instance :
  ∀ γg γs x E omo stlist,
    XchgInv γg γs x E omo stlist ⊢ OmoAuth γg γs (1/2)%Qp E omo stlist _ ∗ (OmoAuth γg γs (1/2)%Qp E omo stlist _ -∗ XchgInv γg γs x E omo stlist).
Proof. iSteps. Qed.

Lemma XchgLocal_OmoEview_instance :
  ∀ N γg x M, XchgLocal N γg x M ⊢ OmoEview γg M.
Proof. iSteps. Qed.

Set Nested Proofs Allowed.

#[local] Hint Extern 10 (BehindModal (fupd ?El ?Er) (?N ⊆ ?Er)) =>
unify El Er; unfold BehindModal; pure_solver.trySolvePure : solve_pure_add.
#[local] Remove Hints ssrbool.not_false_is_true : core.


Lemma new_exchanger_dspec :
  new_exchanger_dspec' new_exchanger XchgLocal XchgInv.
Proof.
  unfold new_exchanger_dspec'. iSteps as (tid N V0 l) "⊒V0 x† x↦ HM". rewrite !omo_rewrite_hints. iStep 8 as "x↦".

  iMod (append_only_loc_cas_only_from_na_rel with "⊒V0 x↦") as "H"; [done|].
  iDecompose "H" as (γx γsx xeV0 ?? ?) "xe0✓xeV0 ⊒Mx@V1 ⊒V _ _ omox↦ WCOMMIT Mx●".

  set V1 := xeV0.(sync).
  set M : eView := {[0%nat]}.
  set eVop := mkOmoEvent Init V1 M.
  set initst : xchg_state := (∅, ∅).

  iMod (@OmoAuth_alloc _ _ _ _ _ eVop initst _ _ xchg_interpretable with "WCOMMIT")
    as (γg γs) "(M● & #⊒M@V1 & _ & #opId✓eVop & _ & WCOMMIT)".
  { eapply xchg_step_Init; try done. } { done. }
  iDestruct (OmoHbToken_finish with "M●") as "M●".
  iMod (@ghost_map_alloc_empty _ _ loc) as (γof) "Hγof".
  iMod (@ghost_map_alloc_empty _ _ (Z * view * eView)) as (γstl) "Hγstl".
  iMod (@ghost_map_alloc_empty _ _ (event_id * Z * view * eView)) as (γstr) "Hγstr".
  iMod (meta_set _ _ (γs,γx,γsx,γof,γstl,γstr) nroot with "HM") as "#HM"; [done|].
  iApply (bi.wand_elim_r (do_intro_view_forall)).
  iSteps. iExists None. iStepsSafest. iLeft. unseal_diaframe;simpl. rewrite H1. iStepsSafest.
  iSplitR. { by iApply big_sepM_empty. }
  iStepsSafest.
  all: try iPureIntro; rewrite /OF_valid /stl_valid /str_valid /stl_str_valid.
  1-3: intros; rewrite lookup_empty in H3; by destruct H3.
  intros. unfold not. intros. rewrite !lookup_empty in H3. destruct H3 as [H3 _]. by destruct H3.
Qed.


#[global] Instance new_offer_dspec :
  new_offer_dspec' new_offer XchgLocal XchgInv CheckToken.
Proof using All.
  intros ? x ????. iStepsSafest as (tid φ ??????????? l E1 ????? OF1 stl1 str1 ????????) "?????????????? l0↦ ????????".
  rewrite !omo_rewrite_hints. iMod (append_only_loc_cas_only_from_na with "l0↦") as "H"; [done|].
  iDecompose "H" as (γl γsl ????) "????????".
  (* CAS *) iExists None. iStepSafest as (??) "??? AU ???".
  iDestruct (view_at_elim with "[] AU") as "AU"; [iSteps|]. iStep 14.
  { (* CAS failed, commit failure. *)
    iApply wp_hist_inv; [done|].
    iMod "AU" as (????) "[>H HAUcl]". iDestruct (atomic.diaframe_close_right_quant with "HAUcl") as "HAU ".
    iSpecialize ("HAU" $! 0%Z). oSteps. iExists None. oSteps. rewrite /own_loc_vec. oSteps. }
  (* CAS success, commit [Reg v] event *)
  iMod "AU" as (????) "[>H HAUcl]". iDestruct (atomic.diaframe_close_right_quant with "HAUcl") as "HAU".
  iSpecialize ("HAU" $! l). iDecompose "H". oSteps.

  set opId := length E1. have [? [FRESHr ?]] : stl1 !! opId = None ∧ str1 !! opId = None ∧ OF1 !! opId = None.
  { split_and!; eapply eq_None_not_Some => ?; (enough (opId < opId); [lia|eauto]). }
  iExists _. iSplitR. { iPureIntro. eapply xchg_step_Reg; try done. set_solver-. }
  oSteps. iExists (Some (<[opId:=l]> OF1)).
  iStepSafest.

  iMod UTok_alloc as (γu) "Hγu".
  iMod (meta_set _ l (γl,γsl,γu) nroot with "[$]") as "#?"; [done|].

  oSteps. { iPureIntro. sauto. } iLeft. unseal_diaframe; simpl.
  oSteps. { iPureIntro. unfold OF_valid. intros e HS. rewrite app_length /=. destruct (decide (e = opId)) as [->|NEQ]; [lia|].
    rewrite lookup_insert_ne in HS; [|done]. apply H5 (* TODO:OF_valid E1 OF1 *) in HS. lia. }
  { iPureIntro. unfold stl_valid. intros e HS. rewrite app_length /=. destruct (decide (e = opId)) as [->|NEQ]; [lia|].
  rewrite lookup_insert_ne in HS; [|done]. apply H6 (* TODO: stl_valid E1 stl1 *)  in HS. lia. }
  { iPureIntro. unfold str_valid. intros e HS. rewrite app_length /=. apply (* TODO: *) H7 in HS. lia. }
  { iPureIntro. unfold stl_str_valid. intros. destruct (decide (e = opId)) as [->|NEQ].
    * rewrite lookup_insert FRESHr. sauto.
    * rewrite lookup_insert_ne; [|done]. eauto. }
  iExists None. oSteps.
Qed.

Definition do_access_all_offers (e : event_id) (γof : gname) (l : loc) : vProp := emp.

#[global] Instance biabd_access_AllOffers e γof l :
  HINT ε₀ ✱ [γof' γstl γstr OF γg;
    ⎡ e ↪[γof]□ l ⎤ ∗
    ⎡ ghost_map_auth (* (K := event_id) (V := loc) *) γof' 1 OF ⎤ ∗
    ⌜ γof' = γof ⌝ ∗  (* we defer proving this equality since we won't know this information before we open the invariant and do a meta agree. *)
    AllOffers γg γstl γstr OF
  ]
  ⊫ [id]
  ; do_access_all_offers e γof l ✱ [
    AllOffersInner γg γstl γstr e l ∗
    ⎡ ghost_map_auth γof 1 OF  ⎤ ∗
    (AllOffersInner γg γstl γstr e l -∗ AllOffers γg γstl γstr OF)
  ].
Proof.
  iStep 7 as (γstl γstr OF γg) "e↪γof Hγof AllOffers".
  iDestruct (ghost_map_lookup with "Hγof e↪γof") as %OFe.
  iDestruct (big_sepM_lookup_acc with "AllOffers") as "[Inner Close]"; [done|iFrame].
Qed.

#[global] Typeclasses Opaque do_access_all_offers.
#[global] Opaque do_access_all_offers.
#[global] Arguments do_access_all_offers _ _ _ : simpl never.

#[global] Instance biabd_append_only_loc_from_AllOffers p e γof l :
  HINT  □⟨ p ⟩ ⎡ e ↪[γof]□ l ⎤ ✱ [V' γl';
    do_access_all_offers e γof l ∗
    @{V'} append_only_loc l γl' ∅ cas_only
  ]
  ⊫ [id]
    γl uf ty V; ▷(@{V} @append_only_loc Σ _ _ _ _ (l >> 0) γl uf ty) ✱ [ ⌜uf = ∅ ∧ ty = cas_only ∧ γl = γl' ∧ V = V'⌝ ].
Proof. oSteps. Qed.

#[local] Hint Resolve biabd_OmoAuth_insert_ro_gen : typeclass_instances.

Lemma check_offer_dspec :
  check_offer_dspec' check_offer XchgLocal XchgInv CheckToken.
Proof using All.
  intros ? x l ????. iStep 9 as (tid φ γs γx γsx γof γstl γstr Mx ?? γl γsl γu ??) "? HM XInv ?? Hml ? ⊒Ml ? AU".
  (* CAS *)
  iStep 2 as (???????????????????????????????|E1 Ex1 omo1 omox1 stlist1 mox1 OF1 stl1 str1 ?? LASTst1 ? VALOF1 VALstl1 VALstr1 VALstlstr1 El omol mol ?? v eV eVl0 ???? el eVl ?? v' ?? e' eV' ?????)
   "?????????????????????" | "??????????? e'✓eV' ???????????".
  all: iMod "AU" as (???? P) "[H HAUcl]"; iDestruct (atomic.diaframe_close_right_quant with "HAUcl") as "?";
    iDecompose "H" as "?? Commit M● ?".
  { (* Offer was not taken. CAS should succeed. commit [Rvk e]. *)
    iExists None. iDecompose "⊒Ml". oSteps;[shelve|]. iExists (-1)%Z. oSteps.
    iExists _. iSplitR. { iPureIntro. eapply xchg_step_Rvk; try done. set_solver-. }
    oSteps. iExists None. oSteps. iRight. oSteps. rewrite H12. oSteps. iLeft. unseal_diaframe; simpl.
    iSteps. { iPureIntro. unfold OF_valid. intros e0 HS. rewrite app_length /=. enough (e0 < length x2); [lia|]. eauto. }
    { iPureIntro. unfold stl_valid. intros e0 HS. rewrite app_length /=. destruct (decide (e = e0)) as [->|NEQ].
      - rewrite lookup_delete in HS. by destruct HS.
      - rewrite lookup_delete_ne in HS; [|done]. enough (e0 < length x2); [lia|]. eauto. }
    { iPureIntro. unfold str_valid. intros e0 HS. rewrite app_length /=. enough (e0 < length x2); [lia|]. eauto. }
    iPureIntro. unfold stl_str_valid. intros e0 HS. destruct (decide (e = e0)) as [->|NEQ].
    - rewrite lookup_delete in HS. destruct HS as [HS _]. by destruct HS.
    - rewrite lookup_delete_ne in HS; [|done]. by eapply H8. }
  (* Offer was  taken. CAS should fail. commit [Ack e vl]. *)
  iSpecialize ("Commit" $! v'). iExists None. iDecompose "⊒Ml".
  iStep 5 as (???? gen1) "⊒V ⊒M ⊒Mx ?? Commit P".
  destruct gen1. { iSteps. } iStep 10 as (????????) "??????? RCOMMIT ??".
  iDestruct (OmoAuth_wf γg with "[$]") as %[OMO_GOOD1 _]. eapply omo_stlist_length in OMO_GOOD1 as EQlenST1.
  set V1' := x5 ⊔ x23.
  set E' := E1 ++ [mkOmoEvent (Ack e v') V1' ({[length E1]} ∪ ({[e']} ∪ eview eV' ∪ M))].
  iAssert (|={↑histN,_}=> @{V1'} (χ ∗ φ #v' ∗ OmoAuth γg γs (1/2)%Qp E' _ _ _))%I with "[Commit P M● RCOMMIT]" as ">H".
  { iCombine "XInv e'✓eV' ⊒Mx HM M● RCOMMIT ⊒M Commit P" as "RES".
    iDestruct (view_at_objective_iff _ V1' with "RES") as "RES".
    iAssert (@{V1'} ⊒V1')%I with "[]" as "#⊒V1'@V1'"; [done|].
    iCombine "RES ⊒V1'@V1'" as "RES".

    rewrite -view_at_fupd. iApply (view_at_mono with "RES"); [done|]. iStep.

    iAssert (⌜ OmoUBgen omo1 ({[e']} ∪ eV'.(eview) ∪ M) (length omo1 - 1) ⌝)%I with "[-]" as %MAXgen.
    { iDestruct (OmoAuth_OmoEview_obj _ _ V1' _ _ _ _ ({[e']} ∪ eview eV' ∪ M) with "[$] []") as %VALID.
      { subst V1'. iSteps.  }
      iIntros "%e'' %INCL". apply VALID in INCL. eapply lookup_omo_surjective in INCL as [eidx Heidx]; [|done].
      iPureIntro. exists eidx. split; [done|]. apply lookup_omo_lt_Some in Heidx. lia. }

    subst V1'. iStep. iExists _. rewrite decide_False; [|lia].
    iSteps. iExists _. iSplitR. { iPureIntro.  eapply xchg_step_Ack; simpl. 1, 2, 5: done.
      - solve_lat. - instantiate (1 := {[e']} ∪ eview eV' ∪ M). set_solver-. }
    rewrite last_lookup -EQlenST1 in LASTst1.
    replace (Init.Nat.pred (length omo1)) with (length omo1 - 1) in LASTst1 by lia. iSteps. }
  iDecompose "H". subst V1' E'. rewrite view_at_objective_iff.
  iStep. iExists None. oSteps. iRight. iStepSafest. iRight. iStepSafest.

  (* acquire read. *)
  oSteps. { exfalso. rewrite H31 omo_insert_r_write_op H12 in G3. clear -G3. sauto. }
  iExists (Some {[length El; 0]}). iRename select (@{x0} OmoEview_or_empty γl {[0]})%I into "H". iDecompose "H".
  iStep. iStep 11 as (el2 gen2 vr2 Vr2 V2 eVl2 ????????) "???? MAXel2 ??????".
  iAssert (⌜ x2 = el ⌝)%I as "H". { rewrite H31 omo_insert_r_write_op H12 in G3. destruct G3. iPureIntro. sauto. } iDecompose "H".
  rewrite H31 in H38.
  iAssert (⌜ gen2 = 1 ∧ el2 = el ⌝)%I with "[-]" as "#H"; last iDecompose "H".
  { iDestruct (big_sepS_elem_of _ _ (length El) with "MAXel2") as "#eln1≤el2"; [set_solver-|].
    iAssert (OmoEq γl el (length El)) as "#el=eln1". { iSteps. }
    iDestruct (OmoEq_Le_trans with "el=eln1 eln1≤el2") as "el≤el2".
    iRename select ( OmoAuth γl _ _ _ _ _ _) into "Ml●".
    iDestruct (OmoLe_Le γl _ _ _ _ _ (wr_event 1) (wr_event gen2) with "Ml● el≤el2") as %LEgen.
    1,2: by rewrite lookup_omo_wr_event omo_insert_r_write_op H31.
    destruct gen2; [simpl in *;lia|]. destruct gen2; [|done]. iPureIntro. sauto. }
  rewrite -H13 in H40. inversion H40. subst.
  iExists None. iRename select (@{eV.(sync)} OmoEview_or_empty γl {[0]})%I into "H". iDecompose "H".
  oSteps. iRight. oSteps. iRight. oSteps.
  Unshelve. all: try pure_solver.trySolvePure. 4: apply inhabitant.
  1-3: iPureIntro; intros e0 HS; rewrite app_length; enough (e0 < length E1) by lia; eauto.
Qed.

#[global] Instance AllOffersInnerCase_timeless γg γstl γstr e γl γu omol v eV : Timeless (AllOffersInnerCase γg γstl γstr e γl γu omol v eV) := _.
#[global] Instance AllOffersInnerCase_objective γg γstl γstr e γl γu omol v eV : Objective (AllOffersInnerCase γg γstl γstr e γl γu omol v eV) := _.
#[local] Typeclasses Opaque AllOffersInnerCase.

Lemma take_offer_dspec :
  take_offer_dspec' take_offer XchgLocal XchgInv.
Proof using All.
  intros ? x ????. iStep 3 as (tid φ γs γx γsx γof γstl γstr Mx ????) "????? AU".
  oSteps. iMod "AU" as (???? P) "[H HAUcl]". iDecompose "H". iExists None. iStep as (??) "? ⊒M ⊒Mx ? Close P".
  iDestruct (view_at_elim with "[] Close") as "Close"; [iSteps|]. iStep 10.
  { (* Read Null, commit nothing *)
    iDestruct (atomic.diaframe_close_right_quant with "Close") as "Commit". oSteps.
    iExists (-1)%Z. oSteps. iExists None. oSteps. }
  iDestruct (atomic.diaframe_close_left with "Close") as "Abort".
  iStep as "?? M● AU". iDecompose "M●".
  iStep. iExists None. iStep. rewrite !omo_rewrite_hints. iStep. iStep 12.
  (* CAS *)
  iStepSafest. iStepSafest.
  iMod "AU" as (???? P') "[H Close]". iDestruct (atomic.diaframe_close_right_quant with "Close") as "Commit". iDecompose "H".
  iExists None. iStep 15.
  { (* CAS failed. commit nothing. *) oSteps. iExists (-1)%Z. oSteps. iExists None. oSteps. rewrite /AllOffersInnerCase !omo_rewrite_hints.
    unseal_diaframe; simpl. iFrame. oSteps. iExists None. oSteps; iExists None; last iClear select (_ (_ ↪[γof]□ _))%I; oSteps. }
  (* CAS succeed, commit [Acp v' v] *)
  iRename select (AllOffersInnerCase _ _ _ _ _ _ _ _ _) into "Case". rewrite /AllOffersInnerCase. iDecompose "Case".
  2, 3: rewrite omo_write_op_length H38 /= in H35; iAssert ⌜x46 = x47⌝%I as "H"; [by inversion H35|]; iDecompose "H"; exfalso; sauto.
  iAssert (⌜x46 = 0 ⌝)%I as "H". { iPureIntro. rewrite H38 in H35. symmetry in H35. rewrite list_lookup_singleton_Some in H35. sauto. }
  iDecompose "H".

  oSteps. iExists x41. rewrite decide_False; [|lia]. oSteps.
  assert (x38 !! x21 = None). { destruct (x38 !! x21) eqn: Heq; [|done]. exfalso. eapply H21. sauto. }
  iExists _. iSplitR. { iPureIntro. eapply xchg_step_Acp; simpl. 1, 2, 5, 6: done.
    - solve_lat. - instantiate (1 := {[x21]} ∪ eview x22 ∪ M). set_solver-. }
  iClear select (@{x42} OmoEview_or_empty x3 {[0]})%I. oSteps.
  iExists None. iStepSafest. rewrite /AllOffersInnerCase. iStepSafest. iRight.
  oSteps. rewrite H38. oSteps. { iPureIntro. intros Heq. inversion Heq. lia. }
  iRight. oSteps. Unshelve. all: try pure_solver.trySolvePure. 1-4 : shelve. 2-3 : shelve.
  iExists None. oSteps; iExists None; last (iClear select (_ (_ ↪[γof]□ _))%I); oSteps.
  Unshelve. all: iPureIntro; intros e0 HS; destruct (decide (x21 = e0)) as [->|NEQ];
  rewrite ?app_length; rewrite ?lookup_delete in HS; try (rewrite ?lookup_delete_ne ?lookup_insert_ne in HS; [|done..]).
  all: try (enough (e0 < length x24) by lia; eauto).
  { by destruct HS as [[? ?] _]. }  { by eapply H21. }
Qed.

End Xchg.

Definition xchg_impl `{!noprolG Σ, !atomicG Σ, !xchgG Σ}
  : xchg_dspec Σ := {|
    spec_composition_diaframe.ExchangerInv_Linearizable := XchgInv_Linearizable_instance;
    spec_composition_diaframe.ExchangerInv_OmoAuth_acc := XchgInv_OmoAuth_acc_instance;
    spec_composition_diaframe.ExchangerLocal_OmoEview := XchgLocal_OmoEview_instance;

    spec_composition_diaframe.new_exchanger_dspec := new_exchanger_dspec;
    spec_composition_diaframe.new_offer_dspec := new_offer_dspec;
    spec_composition_diaframe.check_offer_dspec := check_offer_dspec;
    spec_composition_diaframe.take_offer_dspec := take_offer_dspec;
  |}.
