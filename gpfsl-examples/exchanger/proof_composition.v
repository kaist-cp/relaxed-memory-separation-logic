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
From gpfsl.examples.exchanger Require Import spec_composition code_split.

Require Import iris.prelude.options.

Class xchgG Σ := XchgG {
  xchg_omoGeneralG :> omoGeneralG Σ;
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
    OmoEinfo γx xe xeV ∗ ⌜ loc_event_msg xeV.(type) = (v, V) ⌝ ∗
    ( (⌜ v = #0 ⌝) (* Null value is written *)
    ∨ (∃ (l : loc) e eV, ⌜ v = #l ∧ eV.(sync) ⊑ V ⌝ ∗ OmoEinfo γg e eV ∗ ⎡e ↪[γof]□ l⎤)). (* Offer is written *)

Definition AllWrites γg γx γof (xes : list event_id) : vProp :=
  [∗ list] xe ∈ xes, AllWritesInner γg γx γof xe.

Definition AllOffers γg γstl γstr OF : vProp :=
  [∗ map] e↦l ∈ OF,
    ∃ γl γsl γu El omol mol Vbl q (v : Z) eV (eVl0 : omo_event loc_event),
      meta l nroot (γl,γsl,γu) ∗
      OmoAuth γl γsl (1/2)%Qp El omol mol _ ∗
      @{Vbl} append_only_loc l γl ∅ cas_only ∗
      OmoEinfo γg e eV ∗ OmoEinfo γl 0 eVl0 ∗
      @{eV.(sync)} (OmoEview γl {[0%nat]} ∗ (l >> 1) ↦{q} #v) ∗
      ⌜ (loc_event_msg eVl0.(type)).1 = #(-1) ∧ (0 ≤ v)%Z ⌝ ∗

      ( (⌜ omo_write_op omol = [0] ⌝ ∗ ⎡e ↪[γstl] (v, eV.(sync), eV.(eview))⎤) (* Offer registered *)
      ∨ (∃ el eVl v V, ⌜ omo_write_op omol = [0; el] ∧ loc_event_msg eVl.(type) = (v, V) ∧ v ≠ #(-1) ⌝ ∗ OmoEinfo γl el eVl ∗
          ( (⌜ v = #(-2) ⌝ ∗ UTok γu) (* Offer revoked by registerer *)
          ∨ (∃ e' eV' (v' : Z), ⌜ v = #v' ∧ (0 ≤ v')%Z ∧ eV'.(sync) ⊑ V ⌝ ∗ (* Offer accepted *)
              OmoEinfo γg e' eV' ∗ ⎡e ↪[γstr]□ (e', v', eV'.(sync), eV'.(eview))⎤)))).

Definition OF_valid E OF : Prop :=
  ∀ e, is_Some (OF !! e) → e < length E.

Definition stl_valid E stl : Prop :=
  ∀ e, is_Some (stl !! e) → e < length E.

Definition str_valid E str : Prop :=
  ∀ e, is_Some (str !! e) → e < length E.

Definition stl_str_valid stl str : Prop :=
  ∀ e, ¬(is_Some (stl !! e) ∧ is_Some (str !! e)).

Definition XchgInternalInv γg x E : vProp :=
  ∃ γs γx γsx γof γstl γstr Ex omo omox stlist mox OF stl str,
    meta x nroot (γs,γx,γsx,γof,γstl,γstr) ∗

    OmoAuth γg γs (1/2)%Qp E omo stlist _ ∗
    OmoAuth γx γsx (1/2)%Qp Ex omox mox _ ∗
    (∃ Vb, @{Vb} append_only_loc x γx ∅ cas_only) ∗
    ⎡ghost_map_auth γof 1 OF⎤ ∗
    ⎡ghost_map_auth γstl 1 stl⎤ ∗
    ⎡ghost_map_auth γstr 1 str⎤ ∗

    AllWrites γg γx γof (omo_write_op omox) ∗
    AllOffers γg γstl γstr OF ∗

    ⌜ last stlist = Some (stl, str)
    ∧ OF_valid E OF ∧ stl_valid E stl ∧ str_valid E str ∧ stl_str_valid stl str ⌝.

Definition InternalInv_inner γg x : vProp := ∃ E, XchgInternalInv γg x E.
Definition InternInv N γg x := inv (xchgN N) (InternalInv_inner γg x).

Definition XchgInv γg γs (x : loc) E omo stlist : vProp := OmoAuth γg γs (1/2)%Qp E omo stlist _.
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
  ∀ γg γs x E omo stlist, XchgInv γg γs x E omo stlist ⊢ ⌜ Linearizability E ⌝.
Proof.
  iIntros (??????) "M●". iDestruct (OmoAuth_Linearizable with "M●") as %H. by apply omo_compatible in H.
Qed.

Lemma XchgInv_OmoAuth_acc_instance :
  ∀ γg γs x E omo stlist,
    XchgInv γg γs x E omo stlist ⊢ OmoAuth γg γs (1/2)%Qp E omo stlist _ ∗ (OmoAuth γg γs (1/2)%Qp E omo stlist _ -∗ XchgInv γg γs x E omo stlist).
Proof.
  iIntros (??????) "M●". iFrame "M●". iIntros "M●". iFrame.
Qed.

Lemma XchgLocal_OmoEview_instance :
  ∀ N γg x M, XchgLocal N γg x M ⊢ OmoEview γg M.
Proof.
  intros. iDestruct 1 as (???????) "(_ & _ & M◯ & _)". iFrame.
Qed.

Lemma new_exchanger_spec :
  new_exchanger_spec' new_exchanger XchgLocal XchgInv.
Proof.
  iIntros (N tid V0 Φ) "#⊒V0 Post". wp_lam. wp_apply wp_new; [done..|].
  iIntros (x) "([x†|%] & x↦ & HM & _)"; [|done]. rewrite own_loc_na_vec_singleton shift_0.
  wp_pures. wp_apply wp_fupd. wp_write.

  iMod (append_only_loc_cas_only_from_na_rel with "⊒V0 x↦") as (γx γsx V1 xeV0)
    "(#⊒V1 & Mx● & [#⊒Mx@V1 #⊒V0@V1] & omox↦ & WCOMMIT & #xe0✓xeV0 & [%xeV0EV _])"; [done|].
  iAssert (⌜ V0 ⊑ V1 ⌝)%I with "[-]" as %LeV0V1.
  { rewrite !view_at_unfold !monPred_at_in. by iDestruct "⊒V0@V1" as %?. }

  set M : eView := {[0%nat]}.
  set eVop := mkOmoEvent Init V1 M.
  set initst : xchg_state := (∅, ∅).

  iMod (@OmoAuth_alloc _ _ _ _ _ eVop initst _ _ xchg_interpretable with "WCOMMIT") as (γg γs) "(M● & #⊒M@V1 & _ & #opId✓eVop & _ & WCOMMIT)".
  { eapply xchg_step_Init; try done. } { done. }
  iDestruct (OmoHbToken_finish with "M●") as "[M● M●']".
  iMod (@ghost_map_alloc_empty _ _ loc) as (γof) "Hγof".
  iMod (@ghost_map_alloc_empty _ _ (Z * view * eView)) as (γstl) "Hγstl".
  iMod (@ghost_map_alloc_empty _ _ (event_id * Z * view * eView)) as (γstr) "Hγstr".
  iMod (meta_set _ _ (γs,γx,γsx,γof,γstl,γstr) nroot with "HM") as "#HM"; [done|].

  iMod (inv_alloc (xchgN N) _ (InternalInv_inner γg x) with "[-Post M● WCOMMIT]") as "#XInv".
  { iModIntro. repeat iExists _. iFrame. iFrame "HM". iSplitL "omox↦".
    { iDestruct (view_at_intro with "omox↦") as (?) "[_ omox↦]". iExists _. iFrame. }
    iSplit; last iSplit.
    - rewrite omo_append_w_write_op /AllWrites big_sepL_singleton. iExists xeV0,#0,V1. iFrame "xe0✓xeV0".
      rewrite xeV0EV. iSplit; [done|]. by iLeft.
    - rewrite /AllOffers big_sepM_empty. done.
    - iPureIntro. split_and!; try done; [unfold OF_valid|unfold stl_valid|unfold str_valid|unfold stl_str_valid];
      try (intros; rewrite lookup_empty in H; by destruct H).
      intros. unfold not. intros. rewrite !lookup_empty in H. destruct H as [H _]. by destruct H. }

  iDestruct ("Post" $! γg γs x V1 M with "[M● WCOMMIT]") as "HΦ".
  { iFrame "⊒V1 WCOMMIT". iSplit; [iFrame|]. iSplit; [|done].
    repeat iExists _. iFrame "HM XInv ⊒M@V1 ⊒Mx@V1". }
  iModIntro. by iApply "HΦ".
Qed.

Lemma new_offer_spec :
  new_offer_spec' new_offer XchgLocal XchgInv CheckToken.
Proof.
  intros N DISJ x tid γg M V0 v NZ. iIntros "#⊒V0 #XchgLocal" (Φ) "AU".
  iDestruct "XchgLocal" as (???????) "(HM & XInv & ⊒M & ⊒Mx)".

  wp_lam. wp_apply wp_new; [done..|].
  iIntros (l) "([l†|%] & l↦ & HMl & _)"; [|done]. rewrite own_loc_na_vec_cons own_loc_na_vec_singleton.
  iDestruct "l↦" as "[l0↦ l1↦]". wp_pures. rewrite -[Z.to_nat 0]/(0%nat) shift_0. wp_write.
  wp_pures. rewrite -[Z.to_nat 1]/(1%nat). wp_write. wp_bind (casʳᵉˡ(_,_,_))%E.

  iCombine "l1↦ ⊒M ⊒Mx" as "RES".
  iDestruct (view_at_intro_incl with "RES ⊒V0") as (V0') "(#⊒V0' & %LeV0V0' & (l1↦@V0' & #⊒M@V0' & #⊒Mx@V0'))".

  iMod (append_only_loc_cas_only_from_na_rel with "⊒V0' l0↦") as (γl γsl V0'' eVl0)
    "(#⊒V0'' & Ml● & [#⊒Ml@V0'' #⊒V0'@V0''] & omol↦ & _ & #el0✓eVl0 & [%eVl0EV %eVl0SYNC])"; [done|].
  iAssert (⌜ V0' ⊑ V0'' ⌝)%I with "[-]" as %LeV0'V0''.
  { rewrite !view_at_unfold !monPred_at_in. by iDestruct "⊒V0'@V0''" as %?. }

  (* Inv access 1 *)
  iInv "XInv" as (E1) ">H" "Hclose".
  iDestruct "H" as (?????? Ex1 omo1 omox1 stlist1) "(%mox1 & %OF1 & %stl1 & %str1 & HM' & M●1 & Mx●1 & [%Vb1 omox1↦]
    & Hγof & Hγstl & Hγstr & #AllWrites1 & AllOffers1 & (%LASTst1 & %VALOF1 & %VALstl1 & %VALstr1 & %VALstlstr1))".
  simplify_meta with "HM' HM". iClear "HM'".

  wp_apply (append_only_loc_cas_only_cas _ _ _ _ _ _ _ _ _ _ _ _ _ _ ∅ with "[$Mx●1 $⊒Mx $omox1↦ $⊒V0'']"); try done; [solve_ndisj|].
  iIntros (b1 xe1 gen1 vr1 Vr1 V1 mox1' omox1' xeV1 xeVn1)
    "(Pures & #MAXxe1 & #xe1✓xeV1 & #xen1✓xeVn1 & Mx●1 & #⊒V1 & #⊒Mx1@V1 & omox1↦ & CASE)".
  iDestruct "Pures" as %(Eqgen1 & xeV1EV & LeV0''V1).

  iDestruct "CASE" as "[(Pures & _) | [Pures Vw1]]".
  { (* CAS failed, commit nothing *)
    iDestruct "Pures" as %(-> & NEq & -> & Homox1' & xeVn1EV & xeVn1SYNC).

    iMod "AU" as (γs1' E1' omo1' stlist1') "[>M●1' [_ Commit]]".
    iMod ("Commit" $! 0%Z V1 E1' omo1' stlist1' M with "[M●1']") as "HΦ".
    { iFrame "⊒V1 M●1'". simpl. iSplit; [|done]. repeat iExists _. iFrame "HM XInv ⊒M@V0' ⊒Mx@V0'". }
    iMod ("Hclose" with "[-HΦ l† l1↦@V0' omol↦ Ml●]") as "_".
    { repeat iExists _. iFrame. subst omox1'. rewrite omo_insert_r_write_op.
      iFrame "HM AllWrites1". iSplit; [eauto with iFrame|]. done. }

    iModIntro. iApply wp_hist_inv; [done|]. iIntros "#HInv".
    iMod (append_only_loc_to_na with "HInv Ml● omol↦") as (vl el eVl) "(l0↦ & Ml● & #el✓eVl & [%LASTomol %eVlEV])"; [done|].
    iDestruct (view_at_elim with "⊒V0' l1↦@V0'") as "l1↦".
    iCombine "l0↦ l1↦" as "l↦". rewrite -(own_loc_na_vec_singleton (l >> 1)) -own_loc_na_vec_cons.
    wp_if. wp_apply (wp_delete with "[$l↦ $l†]"); [done..|]. iIntros "_". wp_pures. by iApply "HΦ". }

  (* CAS success, commit [Reg v] event *)
  iDestruct "Pures" as %(-> & -> & EQgen1).
  iDestruct "Vw1" as (Vw1) "((%Hmox1' & %Homox1' & %xeVn1EV & %xeVn1SYNC & %LeVr1Vw1 & %NEqVr1Vw1 & %NLeV1Vr1 & %NEqV0''V1 & %LeV1Vw1)
    & #⊒Mx1@Vw1 & _ & WCOMMIT)".

  have LeV0V1 : V0 ⊑ V1 by solve_lat.
  set opId := length E1.
  set M1 := {[opId]} ∪ M.
  set eVop := mkOmoEvent (Reg v) V1 M1.
  set E1' := E1 ++ [eVop].
  set nstl1 := <[ opId := (v, eVop.(sync), eVop.(eview)) ]> stl1.

  have [FRESHl [FRESHr FRESHOF1]] : stl1 !! opId = None ∧ str1 !! opId = None ∧ OF1 !! opId = None.
  { split_and!; [destruct (stl1 !! opId) eqn:Heq; [|done]|destruct (str1 !! opId) eqn:Heq; [|done]|destruct (OF1 !! opId) eqn:Heq; [|done]];
    apply mk_is_Some in Heq; [apply VALstl1 in Heq|apply VALstr1 in Heq|apply VALOF1 in Heq]; lia. }

  iMod "AU" as (????) "[>M●1' [_ Commit]]".
  iDestruct (OmoAuth_agree with "M●1 M●1'") as %(<- & <- & <- & <-).
  iCombine "M●1 M●1'" as "M●1".
  iDestruct (view_at_mono_2 _ V1 with "⊒M@V0'") as "⊒M@V1"; [solve_lat|].
  iMod (OmoAuth_insert_last with "M●1 ⊒M@V1 WCOMMIT []") as "(M●1 & #⊒M1@V1 & _ & #opId✓eVop & _ & WCOMMIT)".
  { have ? : step opId eVop (stl1, str1) (nstl1, str1); [|done]. eapply xchg_step_Reg; try done. set_solver-. }
  iDestruct (OmoHbToken_finish with "M●1") as "[M●1 M●1']".

  iMod (ghost_map_insert opId (v, eVop.(sync), eVop.(eview)) with "Hγstl") as "[Hγstl opId↪γstl]"; [done|].
  iMod (ghost_map_insert_persist opId l with "Hγof") as "[Hγof #opId↪γof]"; [done|]. iMod UTok_alloc as (γu) "Hγu".
  iMod (meta_set _ _ (γl,γsl,γu) nroot with "HMl") as "#HMl"; [done|].

  iMod ("Commit" $! l V1 E1' _ _ M1 with "[M●1' WCOMMIT]") as "HΦ".
  { iFrame "⊒V1". iSplitL "M●1'"; [iFrame|]. simpl. iFrame "WCOMMIT". iSplit.
    - repeat iExists _. iFrame "HM XInv ⊒M1@V1 ⊒Mx@V0'".
    - iPureIntro. split_and!; try done; [by eexists|by eexists|set_solver-]. }

  iMod ("Hclose" with "[-HΦ Hγu]") as "_".
  { iModIntro. repeat iExists _. iFrame. iFrame "HM". iSplitL "omox1↦"; [eauto with iFrame|]. iSplitR; last iSplit.
    - subst omox1'. rewrite /AllWrites omo_append_w_write_op big_sepL_snoc. iFrame "AllWrites1".
      iExists xeVn1,#l,Vw1. iFrame "xen1✓xeVn1". rewrite xeVn1EV.
      iSplit; [done|]. iRight. iExists l,opId,eVop. iFrame "opId✓eVop opId↪γof". done.
    - rewrite /AllOffers big_sepM_insert; [|done]. iFrame "AllOffers1".
      iDestruct (view_at_intro with "omol↦") as (Vbl) "[#⊒Vbl omol1↦]".
      iExists γl,γsl,γu,_,_,_,Vbl,1%Qp. iExists v,eVop,eVl0. iFrame "HMl opId✓eVop el0✓eVl0 ⊒Ml@V0'' Ml● l1↦@V0' omol1↦".
      rewrite eVl0EV. iSplit; [done|]. iLeft. iFrame "opId↪γstl". done.
    - iPureIntro. rewrite last_app /=. split_and!; try done.
      + unfold OF_valid. intros. rewrite app_length /=. destruct (decide (e = opId)) as [->|NEQ]; [lia|].
        rewrite lookup_insert_ne in H; [|done]. apply VALOF1 in H. lia.
      + unfold stl_valid. intros. rewrite app_length /=. destruct (decide (e = opId)) as [->|NEQ]; [lia|].
        rewrite lookup_insert_ne in H; [|done]. apply VALstl1 in H. lia.
      + unfold str_valid. intros. rewrite app_length /=. apply VALstr1 in H. lia.
      + unfold stl_str_valid. intros. destruct (decide (e = opId)) as [->|NEQ].
        * rewrite lookup_insert FRESHr. unfold not. intros [H1 H2]. by destruct H2.
        * rewrite lookup_insert_ne; [|done]. apply VALstlstr1. }

  iModIntro. wp_pures. iApply "HΦ". iExists l. iSplit; [done|]. repeat iExists _. iFrame "HM HMl opId↪γof Hγu".
  iDestruct (view_at_elim with "⊒V0'' ⊒Ml@V0''") as "#⊒Ml". done.
Qed.

Lemma check_offer_spec :
  check_offer_spec' check_offer XchgLocal XchgInv CheckToken.
Proof.
  intros N DISJ x l tid γg M V0 e. iIntros "#⊒V0 #XchgLocal CheckToken" (Φ) "AU".
  iDestruct "XchgLocal" as (???????) "(HM & XInv & ⊒M & ⊒Mx)".
  wp_lam. wp_pures. rewrite -[Z.to_nat 0]/(0%nat) shift_0. wp_bind (casʳˡˣ(_,_,_))%E.

  (* Inv access 1 *)
  iInv "XInv" as (E1) ">H" "Hclose".
  iDestruct "H" as (?????? Ex1 omo1 omox1 stlist1) "(%mox1 & %OF1 & %stl1 & %str1 & HM' & M●1 & Mx●1 & [%Vb1 omox1↦]
    & Hγof & Hγstl & Hγstr & #AllWrites1 & AllOffers1 & (%LASTst1 & %VALOF1 & %VALstl1 & %VALstr1 & %VALstlstr1))".
  simplify_meta with "HM' HM". iClear "HM'".
  iMod "AU" as (???? P) "[[>M●1' P] [_ Commit]]".
  iDestruct (OmoAuth_agree with "M●1 M●1'") as %(<- & <- & <- & <-). iCombine "M●1 M●1'" as "M●1".

  iCombine "⊒M ⊒Mx Commit P" as "RES".
  iDestruct (view_at_intro_incl with "RES ⊒V0") as (V0') "(#⊒V0' & %LeV0V0' & (#⊒M@V0' & #⊒Mx@V0' & Commit@V0' & P@V0'))".

  iDestruct "CheckToken" as (?????????) "(HM' & #HMl & #e↪γof & #⊒Ml & Hγu)".
  simplify_meta with "HM' HM". iClear "HM'".
  iDestruct (ghost_map_lookup with "Hγof e↪γof") as %OF1e.
  iDestruct (big_sepM_lookup_acc with "AllOffers1") as "[Inner AllOffersClose]"; [exact OF1e|].
  iDestruct "Inner" as (??????????) "(%& HMl' & Ml● & omol↦ & #e✓eV & #el0✓eVl0 & RES@eV & [%eVl0EV %GZv] & CASE)".
  simplify_meta3 with "HMl' HMl". iClear "HMl'".

  iMod (rel_objectively_intro (⊒∅) tid with "[]") as "⊒∅"; [by iApply objective_objectively; iApply monPred_in_bot|].
  wp_apply (append_only_loc_cas_only_cas _ _ _ _ _ _ _ _ _ _ _ _ _ _ ∅ with "[$Ml● $⊒Ml $omol↦ $⊒V0' ⊒∅]"); try done.
  iIntros (b1 el1 gen1 vr1 Vr1 V1 mol1' omol1' eVl1 eVln1)
    "(Pures & #MAXel1 & #el1✓eVl1 & #eln1✓eVln1 & Ml● & #⊒V1 & #⊒Ml1@V1 & omol1↦ & CASEcas)".
  iDestruct "Pures" as %(Eqgen1 & eVl1EV & LeV0'V1).

  iDestruct "CASEcas" as "[(Pures & _ & #el=eln1 & RCOMMIT) | [Pures Vw1]]".
  - (* CAS failed, commit [Ack e vl] *)
    iDestruct "Pures" as %(-> & NEq & -> & Homol1' & eVln1EV & eVln1SYNC).
    iDestruct "CASE" as "[[%Hwr _]|(%el & %eVl & %vl & %Vl & (%Hwr & %eVlEV & %NEQvl) & #el✓eVl & [[_ Hγu']|CASE])]".
    { rewrite Hwr in Eqgen1. destruct gen1; [|done]. inversion Eqgen1. subst el1.
      iDestruct (OmoEinfo_agree with "el0✓eVl0 el1✓eVl1") as %<-.
      rewrite eVl1EV in eVl0EV. inversion eVl0EV. subst vr1. by inversion NEq. }
    { by iDestruct (UTok_unique with "Hγu Hγu'") as %?. }

    iDestruct "CASE" as (???) "((%EQvl & %GZv' & %eV'OUT) & #e'✓eV' & #e↪γstr)". subst vl.
    rewrite Hwr in Eqgen1. destruct gen1.
    { inversion Eqgen1. subst el1. iDestruct (OmoEinfo_agree with "el0✓eVl0 el1✓eVl1") as %<-.
      rewrite eVl1EV in eVl0EV. inversion eVl0EV. subst vr1. by inversion NEq. }
    destruct gen1; [|done]. inversion Eqgen1. subst el1. iDestruct (OmoEinfo_agree with "el✓eVl el1✓eVl1") as %<-.
    rewrite eVl1EV in eVlEV. inversion eVlEV. subst vr1 Vl.

    set V1' := V1 ⊔ Vr1.
    have LeV0V1' : V0 ⊑ V1' by solve_lat.
    set opId := length E1.
    set M1 := {[opId; e']} ∪ eV'.(eview) ∪ M.
    set eVop := mkOmoEvent (Ack e v') V1' M1.
    set E1' := E1 ++ [eVop].
    set omo1' := omo_insert_r omo1 (length omo1 - 1) opId.

    iDestruct (ghost_map_lookup with "Hγstr e↪γstr") as %str1e.
    iDestruct (OmoAuth_wf with "M●1") as %[OMO_GOOD1 _]. eapply omo_stlist_length in OMO_GOOD1 as EQlenST1.

    iAssert (|={_,_}=> @{V1'} (Φ #v' ∗ OmoAuth γg γs (1/2)%Qp E1' omo1' stlist1 _))%I with "[Commit@V0' P@V0' M●1 RCOMMIT]" as ">[HΦ M●1]".
    { iCombine "XInv e'✓eV' ⊒Mx@V0' HM M●1 RCOMMIT ⊒M@V0' Commit@V0' P@V0'" as "RES".
      iDestruct (view_at_objective_iff _ V1' with "RES") as "RES".
      iAssert (@{V1'} ⊒V1')%I with "[]" as "#⊒V1'@V1'"; [done|].
      iCombine "RES ⊒V1'@V1'" as "RES".

      rewrite -view_at_fupd. iApply (view_at_mono with "RES"); [done|].
      iIntros "[(#XInv & #e'✓eV' & #⊒Mx@V0' & #HM & M●1 & RCOMMIT & RES) #⊒V1']".
      iDestruct (view_at_mono_2 _ V1' with "RES") as "[#⊒M@V1' RES]"; [solve_lat|].
      iDestruct (view_at_elim with "⊒V1' RES") as "[Commit P]".
      iDestruct (OmoEview_insert_new_obj with "⊒M@V1' e'✓eV'") as "#⊒M'@V1'"; [solve_lat|].

      iAssert (⌜ OmoUBgen omo1 ({[e']} ∪ eV'.(eview) ∪ M) (length omo1 - 1) ⌝)%I with "[-]" as %MAXgen.
      { iDestruct (OmoAuth_OmoEview_obj with "M●1 ⊒M'@V1'") as %VALID.
        iIntros "%e'' %INCL". apply VALID in INCL. eapply lookup_omo_surjective in INCL as [eidx Heidx]; [|done].
        iPureIntro. exists eidx. split; [done|]. apply lookup_omo_lt_Some in Heidx. lia. }

      iMod (OmoAuth_insert_ro_gen with "M●1 ⊒M'@V1' RCOMMIT []") as "(M●1 & #⊒M1@V1' & _ & _ & #opId✓eVop & RCOMMIT)".
      { have ? : step opId eVop (stl1,str1) (stl1,str1); [|iPureIntro; split_and!; try done; [|set_solver-]].
        - eapply (xchg_step_Ack _ _ _ _ _ eV'.(sync)); try done; [solve_lat|set_solver].
        - rewrite last_lookup -EQlenST1 in LASTst1. replace (Init.Nat.pred (length omo1)) with (length omo1 - 1) in LASTst1 by lia. done. }
      iDestruct (OmoHbToken_finish with "M●1") as "[M●1 M●1']".

      iMod ("Commit" $! v' V1' (Ack e v') _ stlist1 M1 with "[M●1' RCOMMIT P]") as "HΦ".
      { rewrite decide_False; [|lia]. iFrame "P ⊒V1' RCOMMIT". iSplitL "M●1'"; [iFrame|]. iSplit; last iSplit; try done.
        - repeat iExists _. iFrame "HM XInv ⊒Mx@V0'".
          replace ({[length E1]} ∪ ({[e']} ∪ eV'.(eview) ∪ M)) with M1 by set_solver-. done.
        - iPureIntro. split_and!; try done. set_solver-. }

      iModIntro. iFrame "M●1". by iApply "HΦ". }

    iDestruct (OmoSnapOmo_get with "Ml●") as "#omol1'◯".
    iDestruct ("AllOffersClose" with "[Ml● omol1↦ RES@eV]") as "AllOffers1".
    { repeat iExists _. iFrame "HMl Ml● omol1↦ e✓eV el0✓eVl0 RES@eV". iSplit; [done|]. iRight.
      repeat iExists _. iFrame "el✓eVl". rewrite Homol1' omo_insert_r_write_op. iSplit; [done|]. iRight.
      iExists e',eV',v'. iFrame "e'✓eV' e↪γstr". done. }

    iMod ("Hclose" with "[-HΦ Hγu]") as "_".
    { rewrite !view_at_objective_iff. iModIntro. repeat iExists _. iFrame. iFrame "HM AllWrites1". iSplit; [eauto with iFrame|].
      iPureIntro. split_and!; try done; subst E1'; [unfold OF_valid|unfold stl_valid|unfold str_valid]; intros;
      [apply VALOF1 in H|apply VALstl1 in H|apply VALstr1 in H]; rewrite app_length /=; lia. }

    iApply fupd_mask_intro_subseteq; [done|]. wp_pures. rewrite -[Z.to_nat 0]/(0%nat) shift_0.

    (* Inv access 2 *)
    iInv "XInv" as (E2) ">H" "Hclose".
    iDestruct "H" as (?????? Ex2 omo2 omox2 stlist2) "(%mox2 & %OF2 & %stl2 & %str2 & HM' & M●2 & Mx●2 & omox2↦
      & Hγof & Hγstl & Hγstr & #AllWrites2 & AllOffers2 & (%LASTst2 & %VALOF2 & %VALstl2 & %VALstr2 & %VALstlstr2))".
    simplify_meta with "HM' HM". iClear "HM'".

    iDestruct (ghost_map_lookup with "Hγof e↪γof") as %OF2e.
    iDestruct (big_sepM_lookup_acc with "AllOffers2") as "[Inner AllOffersClose]"; [exact OF2e|].

    iDestruct "Inner" as (??? El2 omol2 mol2 Vbl2 q2 v2 ?)
      "(%& HMl' & Ml● & omol↦ & #e✓eV' & #el0✓eVl0' & RES@eV & [%eVl0EV' %GZv2] & CASE)".
    simplify_meta3 with "HMl' HMl". iClear "HMl'".
    iDestruct (OmoEinfo_agree with "e✓eV e✓eV'") as %<-. iClear "e✓eV'".
    iDestruct (OmoEinfo_agree with "el0✓eVl0 el0✓eVl0'") as %<-. iClear "el0✓eVl0'".
    iDestruct (OmoAuth_OmoSnapOmo with "Ml● omol1'◯") as %PREFIX.

    iDestruct (view_at_elim with "⊒V1 ⊒Ml1@V1") as "#⊒Ml1".
    wp_apply (append_only_loc_acquire_read with "[$Ml● $⊒Ml1 $omol↦ $⊒V1]"); [solve_ndisj|].

    iIntros (el2 gen2 vr2 Vr2 V2 eVl2 eVln2) "(Pures & Ml● & _ & #MAXel2 & #el2✓eVl2 & #eln2✓eVln2 & #el2=eln2 & #⊒V2 & _ & omol↦)".
    iDestruct "Pures" as %(Hgen2 & eVl2EV & LeV1Vr2V2 & eVln2EV & eVln2SYNC).
    iDestruct "CASE" as "[[%Hwr' _]|(%el' & %eVl' & %vl' & %Vl' & (%Hwr' & %eVlEV' & %NEQvl') & #el✓eVl' & [[_ Hγu']|CASE])]".
    { destruct PREFIX as [_ H]. rewrite Homol1' omo_insert_r_write_op Hwr Hwr' in H. apply prefix_length in H. simpl in H. lia. }
    { by iDestruct (UTok_unique with "Hγu Hγu'") as %?. }

    iAssert (⌜ el' = el ⌝)%I with "[-]" as %->.
    { destruct PREFIX as [_ H]. rewrite Homol1' omo_insert_r_write_op Hwr Hwr' in H. destruct H as [l' Hl].
      destruct l'; [|apply (f_equal length) in Hl; simpl in *; lia].
      rewrite app_nil_r in Hl. inversion Hl. done. }
    iDestruct (big_sepS_elem_of _ _ (length El) with "MAXel2") as "#eln1≤el2"; [set_solver-|].
    iDestruct (OmoEq_Le_trans with "el=eln1 eln1≤el2") as "el≤el2".
    iDestruct (OmoLe_Le _ _ _ _ _ _ (wr_event 1) (wr_event gen2) with "Ml● el≤el2") as %LEgen.
    { rewrite lookup_omo_wr_event omo_insert_r_write_op Hwr'. done. } { rewrite lookup_omo_wr_event omo_insert_r_write_op. done. }

    destruct gen2; [simpl in *;lia|]. rewrite Hwr' in Hgen2. destruct gen2; [|done]. inversion Hgen2. subst el2.
    iDestruct (OmoEinfo_agree with "el✓eVl el2✓eVl2") as %<-. rewrite eVl1EV in eVl2EV. inversion eVl2EV. subst vr2 Vr2.
    iDestruct (OmoEinfo_agree with "el✓eVl el✓eVl'") as %<-. rewrite eVl1EV in eVlEV'. inversion eVlEV'. subst vl' Vl'.

    iDestruct ("AllOffersClose" with "[Ml● omol↦ CASE RES@eV]") as "AllOffers2".
    { repeat iExists _. iFrame "HMl Ml● omol↦ e✓eV el0✓eVl0 RES@eV". iSplit; [done|]. iRight.
      repeat iExists _. iFrame "el✓eVl". rewrite omo_insert_r_write_op. iSplit; [done|]. iRight. done. }

    iMod ("Hclose" with "[-HΦ]") as "_". { repeat iExists _. iFrame. iFrame "HM AllWrites2". done. }
    iDestruct (view_at_mono_2 _ V2 with "HΦ") as "HΦ"; [solve_lat|]. iDestruct (view_at_elim with "⊒V2 HΦ") as "HΦ".
    iModIntro. by iApply "HΦ".
  - (* CAS succeed, commit [Rvk e] *)
    iDestruct "Pures" as %(-> & -> & EQgen1).
    iDestruct "Vw1" as (Vw1) "((%Hmol1' & %Homol1' & %eVln1EV & %eVln1SYNC & %LeVr1Vw1 & %NEqVr1Vw1 & %NLeV1Vr1 & %NEqV0'V1 & _)
      & _ & _ & WCOMMIT)".
    iDestruct "CASE" as "[[%Homol e↪γstl]|(%&%&%&%& (%Homol & %eVlEV & %NEQv1) & #el✓eVl & _)]"; last first.
    { rewrite omo_write_op_length Homol /= in EQgen1. subst gen1. rewrite Homol in Eqgen1. inversion Eqgen1. subst el1.
      iDestruct (OmoEinfo_agree with "el✓eVl el1✓eVl1") as %<-. rewrite eVl1EV in eVlEV. inversion eVlEV. subst v0 V. done. }

    iDestruct (ghost_map_lookup with "Hγstl e↪γstl") as %stl1e. iMod (ghost_map_delete with "Hγstl e↪γstl") as "Hγstl".

    have LeV0V1 : V0 ⊑ V1 by solve_lat.
    set opId := length E1.
    set M1 := {[opId]} ∪ M.
    set eVop := mkOmoEvent (Rvk e) V1 M1.
    set E1' := E1 ++ [eVop].
    set nstl1 := base.delete e stl1.

    iDestruct (view_at_mono_2 _ V1 with "⊒M@V0'") as "⊒M@V1"; [solve_lat|].
    iMod (OmoAuth_insert_last with "M●1 ⊒M@V1 WCOMMIT []") as "(M●1 & #⊒M1@V1 & _ & #opId✓eVop & _ & WCOMMIT)".
    { have ? : step opId eVop (stl1,str1) (nstl1,str1); [|done]. eapply xchg_step_Rvk; try done. set_solver-. }
    iDestruct (OmoHbToken_finish with "M●1") as "[M●1 M●1']".

    iDestruct ("AllOffersClose" with "[Ml● omol1↦ RES@eV Hγu]") as "AllOffers1".
    { repeat iExists _. iFrame "HMl Ml● omol1↦ RES@eV e✓eV el0✓eVl0". iSplit; [done|]. iRight.
      repeat iExists _. rewrite Homol1' omo_append_w_write_op Homol. iFrame "eln1✓eVln1". rewrite eVln1EV. iSplit; [done|].
      iLeft. iFrame "Hγu". done. }

    iDestruct (view_at_elim with "⊒V0' Commit@V0'") as "Commit". iDestruct (view_at_elim with "⊒V0' P@V0'") as "P".
    iMod ("Commit" $! (-1)%Z V1 (Rvk e) _ _ M1 with "[M●1' WCOMMIT P]") as "HΦ".
    { iFrame "P ⊒V1 WCOMMIT". iSplit; [iFrame|]. iSplit; [|iPureIntro; split_and!; try done; [set_solver-|by eexists]].
      repeat iExists _. iFrame "HM XInv ⊒M1@V1 ⊒Mx@V0'". }

    iMod ("Hclose" with "[-HΦ]") as "_".
    { repeat iExists _. iFrame. iFrame "HM AllWrites1". iSplitL; [eauto with iFrame|]. rewrite last_app /=. iPureIntro. split_and!; try done.
      - unfold OF_valid. intros. apply VALOF1 in H. rewrite app_length /=. lia.
      - unfold stl_valid. intros. subst nstl1. destruct (decide (e = e0)) as [->|NEQ].
        + rewrite lookup_delete in H. by destruct H.
        + rewrite lookup_delete_ne in H; [|done]. apply VALstl1 in H. rewrite app_length /=. lia.
      - unfold str_valid. intros. apply VALstr1 in H. rewrite app_length /=. lia.
      - unfold stl_str_valid. intros. unfold not. intros H. subst nstl1. destruct (decide (e = e0)) as [->|NEQ].
        + rewrite lookup_delete in H. destruct H as [H _]. by destruct H.
        + rewrite lookup_delete_ne in H; [|done]. apply VALstlstr1 in H. done. }

    iApply fupd_mask_intro_subseteq; [solve_ndisj|]. wp_pures. by iApply "HΦ".
Qed.

Lemma take_offer_spec :
  take_offer_spec' take_offer XchgLocal XchgInv.
Proof.
  intros N DISJ x tid γg M V0 v NZ. iIntros "#⊒V0 #XchgLocal" (Φ) "AU".
  iDestruct "XchgLocal" as (???????) "(HM & XInv & ⊒M & ⊒Mx)". iCombine "⊒M ⊒Mx" as "RES".
  iDestruct (view_at_intro_incl with "RES ⊒V0") as (V0') "(⊒V0' & %LeV0V0' & [⊒M@V0' ⊒Mx@V0'])". iClear "RES".
  wp_lam. wp_bind (!ᵃᶜ _)%E.

  (* Inv access 1 *)
  iInv "XInv" as (E1) ">H" "Hclose".
  iDestruct "H" as (?????? Ex1 omo1 omox1 stlist1) "(%mox1 & %OF1 & %stl1 & %str1 & HM' & M●1 & Mx●1 & [%Vb1 omox1↦]
    & Hγof & Hγstl & Hγstr & #AllWrites1 & AllOffers1 & (%LASTst1 & %VALOF1 & %VALstl1 & %VALstr1 & %VALstlstr1))".
  simplify_meta with "HM' HM". iClear "HM'".
  iMod "AU" as (???? P) "[[>M●1' P] Close]".
  iDestruct (OmoAuth_agree with "M●1 M●1'") as %(<- & <- & <- & <-).

  wp_apply (append_only_loc_acquire_read with "[$Mx●1 $⊒Mx $omox1↦ $⊒V0']"); [done|].
  iIntros (xe1 gen1 vr1 Vr1 V1 xeV1 xeVn1) "(Pures & Mx●1 & _ & _ & #xe1✓xeV1 & #xen1✓xeVn1 & _ & #⊒V1 & #⊒Mx1@V1 & omox1↦)".
  iDestruct "Pures" as %(Hgen1 & xeV1EV & LeV0'Vr1V1 & xeVn1EV & xeVn1SYNC).
  have LeV0'V1 : V0' ⊑ V1 by solve_lat.

  iDestruct (big_sepL_lookup with "AllWrites1") as (???) "(#xe1✓xeV1' & %xeV1EV' & CASE)"; [exact Hgen1|].
  iDestruct (OmoEinfo_agree with "xe1✓xeV1 xe1✓xeV1'") as %<-. rewrite xeV1EV in xeV1EV'. inversion xeV1EV'. subst v0 V.
  iDestruct "CASE" as "[%EQvr1|(%&%&%& [%EQVr1 %LeeVVr1] & #e✓eV & #e↪γof)]".
  { (* Read Null, commit nothing *)
    subst vr1. iDestruct "Close" as "[_ Commit]".

    have LeV0V1 : V0 ⊑ V1 by solve_lat.

    iMod ("Commit" $! (-1)%Z V1 _ _ _ M with "[P M●1']") as "HΦ".
    { iFrame "P ⊒V1". iSplitL; [iFrame|]. iSplit; last iSplit; try done. repeat iExists _. iFrame "HM XInv ⊒M@V0' ⊒Mx@V0'". }
    iMod ("Hclose" with "[-HΦ]") as "_".
    { repeat iExists _. iFrame. rewrite omo_insert_r_write_op. iFrame "HM AllWrites1". iSplit; [eauto with iFrame|]. done. }

    iApply fupd_mask_intro_subseteq; [solve_ndisj|]. wp_pures. by iApply "HΦ". }

  (* Found an offer, try exchanging *)
  subst vr1. iDestruct "Close" as "[Abort _]". iMod ("Abort" with "[M●1' P]") as "AU"; [iFrame|].
  iMod ("Hclose" with "[-AU]") as "_".
  { repeat iExists _. iFrame. rewrite omo_insert_r_write_op. iFrame "HM AllWrites1". iSplit; [eauto with iFrame|]. done. }

  iApply fupd_mask_intro_subseteq; [solve_ndisj|]. wp_pures. rewrite -[Z.to_nat 0]/(0%nat) shift_0. wp_bind (casʳᵉˡ(_,_,_))%E.

  (* Inv access 2 *)
  iInv "XInv" as (E2) ">H" "Hclose".
  iDestruct "H" as (?????? Ex2 omo2 omox2 stlist2) "(%mox2 & %OF2 & %stl2 & %str2 & HM' & M●2 & Mx●2 & omox2↦
    & Hγof & Hγstl & Hγstr & #AllWrites2 & AllOffers2 & (%LASTst2 & %VALOF2 & %VALstl2 & %VALstr2 & %VALstlstr2))".
  simplify_meta with "HM' HM". iClear "HM'".
  iMod "AU" as (???? P') "[[>M●2' P] [_ Commit]]".
  iDestruct (OmoAuth_agree with "M●2 M●2'") as %(<- & <- & <- & <-).

  iDestruct (ghost_map_lookup with "Hγof e↪γof") as %OF2e.
  iDestruct (big_sepM_lookup_acc with "AllOffers2") as "[Inner AllOffersClose]"; [exact OF2e|].
  iDestruct "Inner" as (???????? v' ?)
    "(%& #HMl & Ml● & omol↦ & #e✓eV' & #el0✓eVl0 & [#⊒Ml@eV [l1↦ l1↦']] & [%eVlEV %GZv'] & CASE)".
  iDestruct (OmoEinfo_agree with "e✓eV e✓eV'") as %<-. iClear "e✓eV'".
  iDestruct (view_at_mono_2 _ V1 with "⊒Ml@eV") as "⊒Ml@V1"; [clear -LeV0'Vr1V1 LeeVVr1;solve_lat|].
  iDestruct (view_at_elim with "⊒V1 ⊒Ml@V1") as "⊒Ml".

  wp_apply (append_only_loc_cas_only_cas _ _ _ _ _ _ _ _ _ _ _ _ _ _ ∅ with "[$Ml● $⊒Ml $omol↦ $⊒V1]"); try done.
  iIntros (b2 el2 gen2 vr2 Vr2 V2 mol2' omol2' eVl2 eVln2)
    "(Pures & #MAXel2 & #el2✓eVl2 & #eln2✓eVln2 & Ml● & #⊒V2 & #⊒Ml2@V2 & omol2↦ & CASEcas)".
  iDestruct "Pures" as %(Eqgen2 & eVl2EV & LeV1V2).

  set vret := match b2 with | true => v' | false => (-1)%Z end.
  have LeeVV2 : eV.(sync) ⊑ V2 by clear -LeeVVr1 LeV0'Vr1V1 LeV1V2; solve_lat.
  have LeV0V2 : V0 ⊑ V2 by solve_lat.
  iAssert (|={_,_}=> Φ #vret)%I with "[-l1↦]" as ">HΦ".
  { iDestruct "CASEcas" as "[(Pures & _ & _ & RCOMMIT) | [Pures Vw2]]".
    - (* CAS failed, commit nothing *)
      iDestruct "Pures" as %(-> & NEq & -> & Homol2' & eVln2EV & eVln2SYNC).

      iMod ("Commit" $! (-1)%Z V2 E2 omo2 stlist2 M with "[M●2 P]") as "HΦ".
      { iFrame "P ⊒V2". iSplitL; [iFrame|]. iSplit; last iSplit; try done.
        repeat iExists _. iFrame "HM XInv ⊒M@V0' ⊒Mx@V0'". }
      iDestruct ("AllOffersClose" with "[Ml● omol2↦ CASE l1↦']") as "AllOffers2".
      { repeat iExists _. iFrame "HMl Ml● omol2↦ l1↦' e✓eV el0✓eVl0 ⊒Ml@eV". iSplit; [done|].
        rewrite Homol2' omo_insert_r_write_op. iFrame "CASE". }
      iMod ("Hclose" with "[-HΦ]") as "_"; [repeat iExists _; iFrame; iFrame "HM AllWrites2"; done|]. iModIntro. by iApply "HΦ".
    - (* CAS succeed, commit [Acp v' v] *)
      iDestruct "Pures" as %(-> & -> & EQgen2).
      iDestruct "Vw2" as (Vw2) "((%Hmol2' & %Homol2' & %eVln2EV & %eVln2SYNC & %LeVr2Vw2 & %NEqVr2Vw2 & %NLeV2Vr2 & %NEqV1V2 & %LeV2Vw2)
        & _ & _ & WCOMMIT)".

      iDestruct "CASE" as "[[%Homol e↪γstl]|(%&%&%&%& (%Homol & %eVlEV' & %NEQv1) & #el✓eVl & _)]"; last first.
      { rewrite omo_write_op_length Homol /= in EQgen2. subst gen2. rewrite Homol in Eqgen2. inversion Eqgen2. subst el2.
        iDestruct (OmoEinfo_agree with "el✓eVl el2✓eVl2") as %<-. rewrite eVl2EV in eVlEV'. inversion eVlEV'. subst v0 V. done. }

      iDestruct (ghost_map_lookup with "Hγstl e↪γstl") as %stl2e.
      have str2e : str2 !! e = None.
      { destruct (str2 !! e) eqn:Heq; [|done]. apply mk_is_Some in stl2e,Heq.
        unfold stl_str_valid, not in VALstlstr2. exfalso. apply (VALstlstr2 e). done. }

      set opId := length E2.
      set M2 := {[opId; e]} ∪ eV.(eview) ∪ M.
      set eVop := mkOmoEvent (Acp v' v) V2 M2.
      set E1' := E1 ++ [eVop].
      set nstl2 := base.delete e stl2.
      set nstr2 := <[ e := (opId, v, eVop.(sync), eVop.(eview)) ]> str2.

      iMod (ghost_map_delete with "Hγstl e↪γstl") as "Hγstl".
      iMod (ghost_map_insert_persist e (opId, v, eVop.(sync), eVop.(eview)) with "Hγstr") as "[Hγstr #e↪γstr]"; [exact str2e|].
      iDestruct (view_at_mono_2 _ V2 with "⊒M@V0'") as "⊒M@V2"; [solve_lat|].
      iDestruct (OmoEview_insert_new_obj with "⊒M@V2 e✓eV") as "⊒M'@V2"; [done|].
      iCombine "M●2 M●2'" as "M●2".
      iMod (OmoAuth_insert_last with "M●2 ⊒M'@V2 WCOMMIT []") as "(M●2 & #⊒M2@V2 & _ & #opId✓eVop & _ & WCOMMIT)".
      { have ? : step opId eVop (stl2,str2) (nstl2,nstr2).
        { eapply (xchg_step_Acp _ _ v e v' eV.(sync)); try done. set_solver-. }
        iPureIntro. split_and!; try done. set_solver-. }
      iDestruct (OmoHbToken_finish with "M●2") as "[M●2 M●2']".

      iMod ("Commit" $! v' V2 _ _ _ M2 with "[P M●2' WCOMMIT]") as "HΦ".
      { rewrite decide_False; [|lia]. iFrame "P ⊒V2 WCOMMIT".
        iSplit; [iFrame|]. iSplit; [|iPureIntro; split_and!; try done; [set_solver-|by eexists]].
        repeat iExists _. iFrame "HM XInv ⊒Mx@V0'". replace ({[length E2]} ∪ ({[e]} ∪ eV.(eview) ∪ M)) with M2 by set_solver-. done. }

      iDestruct ("AllOffersClose" with "[Ml● omol2↦ l1↦']") as "AllOffers2".
      { repeat iExists _. iFrame "HMl Ml● omol2↦ l1↦' e✓eV el0✓eVl0 ⊒Ml@eV". iSplit; [done|]. iRight.
        iExists (length El),eVln2,#v,Vw2. rewrite Homol2' omo_append_w_write_op Homol /=. iFrame "eln2✓eVln2". iSplit.
        - iPureIntro. rewrite eVln2EV. split_and!; try done. unfold not. intros. inversion H. lia.
        - iRight. iExists opId,eVop,v. iFrame "opId✓eVop e↪γstr". iPureIntro. split_and!; try done. }

      iDestruct (OmoAuth_OmoEinfo with "M●2 e✓eV") as %HeV.
      iMod ("Hclose" with "[-HΦ]") as "_".
      { repeat iExists _. iFrame. iFrame "HM AllWrites2". rewrite last_app /=. iPureIntro. split_and!; try done.
        - unfold OF_valid. intros. apply VALOF2 in H. rewrite app_length /=. lia.
        - unfold stl_valid. intros. rewrite app_length /=. destruct (decide (e0 = e)) as [->|NEQ].
          + rewrite lookup_delete in H. by destruct H.
          + rewrite lookup_delete_ne in H; [|done]. apply VALstl2 in H. lia.
        - unfold str_valid. intros. rewrite app_length /=. destruct (decide (e0 = e)) as [->|NEQ].
          + apply lookup_lt_Some in HeV. rewrite app_length /= in HeV. done.
          + rewrite lookup_insert_ne in H; [|done]. apply VALstr2 in H. lia.
        - unfold stl_str_valid. intros. unfold not. intros. destruct (decide (e0 = e)) as [->|NEQ].
          + rewrite lookup_delete in H. destruct H as [H _]. by destruct H.
          + rewrite lookup_delete_ne in H; [|done]. rewrite lookup_insert_ne in H; [|done]. apply VALstlstr2 in H. done. }

      iModIntro. by iApply "HΦ". }

  iApply fupd_mask_intro_subseteq; [done|]. wp_pures. wp_bind (casʳˡˣ(_,_,_))%E.

  (* Inv access 3 *)
  iInv "XInv" as (E3) ">H" "Hclose".
  iDestruct "H" as (?????? Ex3 omo3 omox3 stlist3) "(%mox3 & %OF3 & %stl3 & %str3 & HM' & M●3 & Mx●3 & [%Vb3 omox3↦]
    & Hγof & Hγstl & Hγstr & #AllWrites3 & AllOffers3 & (%LASTst3 & %VALOF3 & %VALstl3 & %VALstr3 & %VALstlstr3))".
  simplify_meta with "HM' HM". iClear "HM'".

  iMod (rel_objectively_intro (⊒∅) tid with "[]") as "⊒∅"; [by iApply objective_objectively;iApply monPred_in_bot|].
  wp_apply (append_only_loc_cas_only_cas _ _ _ _ _ _ _ _ _ _ _ _ _ _ ∅ with "[$Mx●3 $⊒Mx $omox3↦ $⊒V2 ⊒∅]"); try done; [solve_ndisj|].
  iIntros (b3 xe3 gen3 vr3 Vr3 V3 mox3' omox3' xeV3 xeVn3)
    "(Pures & _ & #xe3✓xeV2 & #xen3✓xeVn3 & Mx●3 & #⊒V3 & #⊒Mx3@V3 & omox3↦ & CASE)".
  iDestruct "Pures" as %(Eqgen3 & xeV3EV & LeV2V3).

  iMod ("Hclose" with "[-HΦ l1↦]") as "_".
  { iModIntro. repeat iExists _. iFrame. iFrame "HM". iSplitL "omox3↦"; [eauto with iFrame|]. iSplit; [|done].
    iDestruct "CASE" as "[(Pures & _) | [Pures Vw2]]".
    - iDestruct "Pures" as %(-> & _ & -> & -> & _). rewrite omo_insert_r_write_op. done.
    - iDestruct "Vw2" as (Vw2) "[(%Hmox3' & %Homox3' & %xeVn3EV & _) _]".
      rewrite Homox3' omo_append_w_write_op /AllWrites big_sepL_snoc. iFrame "AllWrites3".
      iExists xeVn3,#0,Vw2. iFrame "xen3✓xeVn3". rewrite xeVn3EV. iSplit; [done|]. iLeft. done. }

  iModIntro. wp_pures. destruct b2.
  - wp_pures. rewrite -[Z.to_nat 1]/(1%nat). iDestruct (view_at_mono_2 _ V2 with "l1↦") as "l1↦"; [solve_lat|].
    iDestruct (view_at_elim with "⊒V2 l1↦") as "l1↦". wp_read. by iApply "HΦ".
  - wp_pures. by iApply "HΦ".
Qed.

End Xchg.

Definition xchg_impl `{!noprolG Σ, !atomicG Σ, !xchgG Σ}
  : xchg_spec Σ := {|
    spec_composition.ExchangerInv_Linearizable := XchgInv_Linearizable_instance;
    spec_composition.ExchangerInv_OmoAuth_acc := XchgInv_OmoAuth_acc_instance;
    spec_composition.ExchangerLocal_OmoEview := XchgLocal_OmoEview_instance;

    spec_composition.new_exchanger_spec := new_exchanger_spec;
    spec_composition.new_offer_spec := new_offer_spec;
    spec_composition.check_offer_spec := check_offer_spec;
    spec_composition.take_offer_spec := take_offer_spec;
  |}.
