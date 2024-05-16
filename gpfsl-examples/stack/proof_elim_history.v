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
From gpfsl.examples.stack Require Import spec_history spec_treiber_composition code_elim.
From gpfsl.examples.exchanger Require Import spec_composition code_split.

Require Import iris.prelude.options.

Class elimG Σ := ElimG {
  elim_omoGeneralG :> omoGeneralG Σ;
  elim_stackG :> omoSpecificG Σ sevent_hist stack_state;
  elim_exG :> omoSpecificG Σ xchg_event xchg_state;
  elim_helpingG :> ghost_mapG Σ event_id (gname * view);
  elim_uniqTokG :> uniqTokG Σ;
  elim_savedvPropG :> savedvPropG Σ;
}.

Definition elimΣ : gFunctors := #[omoGeneralΣ; omoSpecificΣ sevent_hist stack_state; omoSpecificΣ xchg_event xchg_state; ghost_mapΣ event_id (gname * view); uniqTokΣ; savedvPropΣ].

Global Instance subG_elimΣ {Σ} : subG elimΣ Σ → elimG Σ.
Proof. solve_inG. Qed.

Section Elimstack.
Context `{!noprolG Σ, !atomicG Σ, !elimG Σ}.

Local Notation iProp := (iProp Σ).
Local Notation vProp := (vProp Σ).
Local Open Scope nat_scope.

Implicit Types
  (γg γs γgt γst γgx γsx γm γh γi γu : gname)
  (omo omot : omoT)
  (E Et : history sevent_hist) (Ex : history xchg_event).

Hypothesis (ts : stack_spec Σ).
Hypothesis (xc : xchg_spec Σ).

Definition estackN (N : namespace) := N .@ "estack".
Definition tstackN (N : namespace) := N .@ "tstack".
Definition xchgN (N : namespace) := N .@ "xchg".
Definition helpN (N : namespace) := N .@ "helping".

Notation new_stack' := (spec_treiber_composition.new_stack ts).
Notation try_push' := (spec_treiber_composition.try_push ts).
Notation try_pop' := (spec_treiber_composition.try_pop ts).
Notation new_exchanger := (spec_composition.new_exchanger xc).
Notation new_offer := (spec_composition.new_offer xc).
Notation check_offer := (spec_composition.check_offer xc).
Notation take_offer := (spec_composition.take_offer xc).

Definition field_info γg (s lt lx : loc) : vProp :=
  ∃ (eV0 : omo_event sevent_hist) (q : Qp),
    OmoEinfo γg 0%nat eV0 ∗
    @{eV0.(sync)} (s ↦{q} #lt ∗ (s >> 1) ↦{q} #lx).

Definition last_state γg γgt (stlist tstlist : list stack_state) : vProp :=
  ∃ stf tstf,
    ⌜ last stlist = Some stf ∧ last tstlist = Some tstf ⌝ ∗
    [∗ list] st; tst ∈ stf; tstf,
      ∃ (eV teV : omo_event sevent_hist),
        OmoEinfo γg st.1.1.1 eV ∗ OmoEinfo γgt tst.1.1.1 teV ∗
        ⌜ st.1.1.2 = tst.1.1.2 ∧ st.1.2 = tst.1.2
        ∧ eV.(sync) = st.1.2 ∧ teV.(sync) = tst.1.2 ∧ eV.(eview) = st.2 ⌝.

Definition EStackInv γg (s : loc) E : vProp := ∃ γs omo stlist, OmoAuth γg γs (1/2)%Qp E omo stlist _.

Definition EStackLocal_inner N γg (s : loc) E M : vProp :=
  ∃ γgt γst γgx γsx γm γh (lt lx : loc) Mt Mx (eV0 : omo_event sevent_hist),
    meta s nroot (γgt,γgx,γst,γsx,γm,γh,lt,lx) ∗
    OmoSnapHistory γg E ∗
    OmoEview γg M ∗
    StackLocal ts (tstackN N) γgt lt Mt ∗
    ExchangerLocal xc (xchgN N) γgx lx Mx ∗
    OmoEinfo γg 0%nat eV0 ∗ ⊒(eV0.(sync)).

Definition atomic_update_push (N : namespace) γg s (v : Z) (V : view) (M : eView) (Q : bool → vProp) : vProp :=
  atomic_update (⊤ ∖ ↑N) (↑histN)
    (tele_app (TT:= [tele _]) (λ E, ▷ EStackInv γg s E)%I)
    (tele_app (TT:= [tele _])
      (λ E, tele_app (TT:= [tele _ _ _ _ _])
        (λ (b: bool) V' E' ps M',
          (* PUBLIC POST *)
          ▷ EStackInv γg s E' ∗
          ⌜ if b then (
            (* successful case *)
            E' = E ++ [mkOmoEvent ps V' M'] ∧
            V ⊑ V' ∧
            is_push ps v ∧
            M ⊆ M')
            else (
              (* FAIL_RACE case *)
              E' = E ∧ M' = M
            ) ⌝ ∗
            ⊒V' ∗ @{V'} EStackLocal_inner N γg s E' M')%I))
    (tele_app (TT:= [tele _])
      (λ E, tele_app (TT:= [tele _ _ _ _ _])
        (λ b V' E' ps M', Q b)%I)).

Definition last_state_xchg N γg s γgx γh (xstlist : list xchg_state) (hmap : gmap event_id (gname * view)) : vProp :=
  ∃ xstl xstr, ⌜ last xstlist = Some (xstl, xstr) ⌝ ∗
    ([∗ map] xe↦xinfo ∈ xstl,
      ∃ (γi γpt γpf γu : gname) (Vi : view) M Q E,
        ⌜ γi = encode (γpt,γpf,γu) ∧ Vi ⊑ xinfo.1.2 ∧ (0 < xinfo.1.1)%Z ⌝ ∗
        @{xinfo.1.2} (atomic_update_push N γg s xinfo.1.1 Vi M Q ∗ EStackLocal_inner N γg s E M) ∗
        OmoTokenW γgx xe ∗
        saved_vProp_own γpt DfracDiscarded (Q true) ∗ saved_vProp_own γpf DfracDiscarded (Q false) ∗
        ⎡xe ↪[γh]□ (γi,xinfo.1.2)⎤) ∗
    ([∗ map] xe↦xinfo ∈ xstr,
      ∃ (γi γpt γpf γu : gname) (Vb : view) P,
        ⌜ γi = encode (γpt,γpf,γu) ∧ xinfo.1.1.2 = 0%Z ⌝ ∗
        ⎡xe ↪[γh]□ (γi,Vb)⎤ ∗ saved_vProp_own γpt DfracDiscarded P ∗
        (@{Vb ⊔ xinfo.1.2} P ∨ UTok γu)).

Definition AllEvents γg γs γgt γgx γm E ezfs ezfl : vProp :=
  OmoSnap γg γs ezfl [] ∗
  [∗ list] e↦eV ∈ E,
    OmoLe γg e ezfl ∨
    (∃ e' te', OmoLt γg ezfs e' ∗ OmoLe γg e' e ∗ OmoHb γg γg e e' ∗
      OmoHb γg γgt e' te' ∗ OmoCW γg γgt e' te' ∗ CWMonoValid γm e').

Definition last_empty_t γg γgt γm ezfs (tes : list event_id) (tstlist : list stack_state) : vProp :=
  ∃ tezf tgenzf,
    OmoCW γg γgt ezfs tezf ∗ CWMonoValid γm ezfs ∗
    ⌜ tes !! tgenzf = Some tezf ∧ tstlist !! tgenzf = Some [] ∧ (∀ tgen' st', tstlist !! tgen' = Some st' → (tgenzf < tgen')%nat → st' ≠ []) ⌝.

Definition last_empty ezfl (es : list event_id) (stlist : list stack_state) : Prop :=
  ∃ genzfl,
    es !! genzfl = Some ezfl ∧ (∀ i st, stlist !! i = Some st → (genzfl < i)%nat → st ≠ []).

Definition hmap_valid Ex (hmap : gmap event_id (gname * view)) : Prop :=
  ∀ e, is_Some (hmap !! e) → e < length Ex.

Definition EStackInternalInv (N : namespace) γg s E : vProp :=
  ∃ (γs γgt γst γgx γsx γm γh : gname) (lt lx : loc) Et Ex omo omot omox stlist tstlist xstlist Mono hmap ezfs ezfl,
    meta s nroot (γgt,γgx,γst,γsx,γm,γh,lt,lx) ∗

    OmoAuth γg γs (1/2)%Qp E omo stlist _ ∗
    StackInv ts γgt γst lt Et omot tstlist ∗
    ExchangerInv xc γgx γsx lx Ex omox xstlist ∗
    CWMono γg γgt γm Mono ∗
    ⎡ghost_map_auth γh 1 hmap⎤ ∗

    field_info γg s lt lx ∗
    last_state γg γgt stlist tstlist ∗
    last_state_xchg N γg s γgx γh xstlist hmap ∗
    AllEvents γg γs γgt γgx γm E ezfs ezfl ∗
    last_empty_t γg γgt γm ezfs (omo_write_op omot) tstlist ∗

    ⌜ hmap_valid Ex hmap ∧ last_empty ezfl (omo_write_op omo) stlist ⌝.

Definition InternalInv_inner N γg s : vProp := ∃ E, EStackInternalInv N γg s E.
Definition InternInv N γg s := inv (estackN N) (InternalInv_inner N γg s).

Definition EStackLocal N γg s E M : vProp :=
  EStackLocal_inner N γg s E M ∗ InternInv N γg s.

Local Tactic Notation "simplify_meta" "with" constr(Hs) :=
  iDestruct (meta_agree with Hs) as %[[[[[[[-> ->]%pair_inj ->]%pair_inj ->]%pair_inj ->]%pair_inj ->]%pair_inj ->]%pair_inj ->]%pair_inj.

Lemma field_info_dup γg s lt lx :
  field_info γg s lt lx -∗ field_info γg s lt lx ∗ field_info γg s lt lx.
Proof.
  iDestruct 1 as (??) "[#ELEM [[s0↦ s0↦'] [s1↦ s1↦']]]".
  iSplitL "s0↦ s1↦"; repeat iExists _; iFrame "∗#".
Qed.

Lemma EStackInv_Linearizable_instance :
  ∀ γg s E, EStackInv γg s E ⊢ ⌜ Linearizability E ⌝.
Proof.
  intros. iDestruct 1 as (???) "M●".
  iDestruct (OmoAuth_Linearizable with "M●") as %H. by apply omo_compatible in H.
Qed.

Lemma EStackInv_history_wf_instance :
  ∀ γg s E, EStackInv γg s E ⊢ ⌜ history_wf E ⌝.
Proof.
  intros. iDestruct 1 as (???) "M●".
  by iDestruct (OmoAuth_wf with "M●") as "[_ %H2]".
Qed.

Lemma EStackInv_StackLocal_instance :
  ∀ N γg s E E' M',
    EStackInv γg s E -∗ EStackLocal N γg s E' M' -∗ ⌜ E' ⊑ E ⌝.
Proof.
  intros. iDestruct 1 as (???) "M●".
  iDestruct 1 as "[(%&%&%&%&%&%&%&%&%&%&%& _ & E◯ & _) _]".
  by iDestruct (OmoAuth_OmoSnapHistory with "M● E◯") as %?.
Qed.

Lemma EStackLocal_lookup_instance :
  ∀ N γg s E M e V,
    sync <$> E !! e = Some V → e ∈ M →
    EStackLocal N γg s E M -∗ ⊒V.
Proof.
  intros. iDestruct 1 as "[(%&%&%&%&%&%&%&%&%&%&%& _ & E◯ & M◯ & _) _]".
  by iApply (OmoSnapHistory_OmoEview with "E◯ M◯").
Qed.

Lemma new_stack_spec :
  spec_history.new_stack_spec' (new_estack new_stack' new_exchanger) EStackLocal EStackInv.
Proof.
  iIntros (N tid Φ) "_ Post". wp_lam. wp_apply wp_new; [done..|].
  iIntros (s) "([s†|%] & s↦ & HM & _)"; [|done]. rewrite own_loc_na_vec_cons own_loc_na_vec_singleton.
  iDestruct "s↦" as "[s0↦ s1↦]".
  wp_pures. rewrite -[Z.to_nat 0]/(0%nat) shift_0.

  iDestruct (view_at_intro emp with "[]") as (V0) "[#⊒V0 _]"; [done|].
  wp_apply (new_stack_spec ts (tstackN N) _ V0 with "⊒V0").
  iIntros (γgt γst lt Mt V1) "(#⊒V1 & Mt● & #⊒Mt@V1 & WCOMMIT & %LeV0V1)".
  wp_write. wp_pures. rewrite -[Z.to_nat 1]/(1%nat).
  wp_apply (new_exchanger_spec xc (xchgN N) _ V1 with "⊒V1").
  iIntros (γgx γsx lx V2 Mx) "(#⊒V2 & Mx● & #⊒Mx@V2 & _ & %LeV1V2)".
  wp_apply wp_fupd. wp_write.

  iCombine "s0↦ s1↦" as "s↦".
  iDestruct (view_at_intro_incl with "s↦ ⊒V2") as (V3) "(#⊒V3 & %LeV2V3 & s↦@V3)".

  set Minit : eView := {[0%nat]}.
  set eVinit := mkOmoEvent (stack_event_omo.Init) V3 Minit.
  set initst : stack_state := [].

  iMod (@OmoAuth_alloc _ _ _ _ _ eVinit initst _ _ stack_interpretable with "WCOMMIT") as (γg γs) "(M● & #⊒M@V2 & #e0↦te0 & #einit✓eVinit & #einit↪emp & _)".
  { eapply stack_step_Init; try done. } { done. }
  iDestruct (OmoHbToken_finish with "M●") as "[M● M●']".
  iDestruct (OmoSnapHistory_get with "M●") as "#E◯".

  iMod (ghost_map_alloc_empty) as (γh) "Hγh".
  iMod (CWMono_new γg γgt) as (γm) "MONO".
  iMod (meta_set _ _ (γgt,γgx,γst,γsx,γm,γh,lt,lx) nroot with "HM") as "#HM"; [done|].

  iDestruct (StackInv_OmoAuth_acc with "Mt●") as "[Mt● Close]".
  iMod (CWMono_insert_last_last (wr_event 0) with "MONO M● Mt● e0↦te0") as "(MONO & #MONO✓e0 & M● & Mt●)"; [done|done|].
  iDestruct ("Close" with "Mt●") as "Mt●".

  iMod (inv_alloc (estackN N) _ (InternalInv_inner N γg s) with "[-Post M●]") as "#SInv".
  { iModIntro. do 20 iExists _. iExists 0,0. iFrame "HM M●' Hγh MONO Mt● Mx●". rewrite !omo_append_w_write_op /=.
    iSplitL; last iSplit; last iSplit; last iSplit; last iSplit.
    - iExists _,1%Qp. iFrame "einit✓eVinit". subst eVinit. done.
    - iExists initst,initst. iSplit; [|done]. done.
    - iExists ∅,∅. iSplit; try done. rewrite !big_sepM_empty. done.
    - iFrame "einit↪emp". rewrite big_sepL_singleton. iLeft. iApply OmoLe_get_from_Eq. iApply (OmoEq_get_from_Einfo with "einit✓eVinit").
    - iExists 0,0. iFrame "e0↦te0 MONO✓e0". iPureIntro. split_and!; try done. intros. destruct tgen'; try done. lia.
    - iPureIntro. split.
      + unfold hmap_valid. intros. rewrite lookup_empty in H. destruct H. done.
      + exists 0. split; [done|]. intros. destruct i; try done. lia. }

  iDestruct ("Post" $! γg s V3 _ Minit with "[M●]") as "HΦ".
  { iFrame "⊒V3". iSplitL; [repeat iExists _; iFrame|]. iSplit; [done|]. iFrame "SInv".
    repeat iExists _. iFrame "HM ⊒M@V2 ⊒Mt@V1 ⊒Mx@V2 einit✓eVinit E◯". subst eVinit. simpl. done. }

  iModIntro. by iApply "HΦ".
Qed.

Lemma try_push_spec :
  spec_history.try_push_spec' (try_push try_push' new_offer check_offer) EStackLocal EStackInv.
Proof.
  intros N DISJ s tid γg E0 M V0 v NZ. iIntros "#⊒V0 #EStackLocal" (Φ) "AU".
  iDestruct "EStackLocal" as "[(%&%&%&%&%&%&%&%&%&%&%& HM & #E◯0 & ⊒M & ⊒Mt & ⊒Mx & e0✓eV0 & ⊒eV0) SInv]".
  wp_lam. wp_pures. rewrite -[Z.to_nat 0]/(0%nat) shift_0. wp_bind (! _)%E.

  (* Inv access 1 *)
  iInv "SInv" as (E1) "H" "Hclose".
  iDestruct "H" as (γs1 ???????? Et1) "(%Ex1 & %omo1 & %omot1 & %omox1 & %stlist1 & %tstlist1 & %xstlist1 & %Mono1 & %hmap1 & %ezfs1 & %ezfl1 &
    >HM' & >M●1 & Mt●1 & Mx●1 & MONO1 & Hγh1 & >Field1 & >LASTst1 & LASTxchg1 & #AllEvents1 & >#LASTemp1 & >[%VALhmap1 %LASTemp1])".
  simplify_meta with "HM' HM".  iClear "HM'".
  iDestruct (field_info_dup with "Field1") as "[Field1 (%&%& #e0✓eV0' & s↦)]".
  iDestruct (OmoEinfo_agree with "e0✓eV0 e0✓eV0'") as %<-. iClear "e0✓eV0'".
  iDestruct (view_at_elim with "⊒eV0 s↦") as "[s0↦ s1↦]".
  iCombine "⊒M ⊒Mt ⊒Mx ⊒eV0" as "⊒INFO".
  iDestruct (view_at_intro_incl with "⊒INFO ⊒V0") as (V0') "(⊒V0' & %LeV0V0' & (⊒M@V0' & ⊒Mt@V0' & ⊒Mx@V0' & ⊒eV0@V0'))".

  iMod ("Hclose" with "[-AU s0↦ s1↦]") as "_".
  { repeat iExists _. iFrame. iFrame "HM AllEvents1 LASTemp1". done. }
  wp_read. iApply fupd_mask_intro_subseteq; [done|]. wp_pures.

  (* Inv access 2 *)
  have NDISJ' : (tstackN N) ## histN by solve_ndisj.
  awp_apply (try_push_spec ts _ NDISJ' lt _ γgt _ V0' v with "⊒V0' ⊒Mt"); [done|].
  iInv "SInv" as (E2) "H".
  iDestruct "H" as (γs2 ???????? Et2) "(%Ex2 & %omo2 & %omot2 & %omox2 & %stlist2 & %tstlist2 & %xstlist2 & %Mono2 & %hmap2 & %ezfs2 & %ezfl2 &
    >HM' & >M●2 & >Mt●2 & Mx●2 & >MONO2 & >Hγh2 & >Field2 & >LASTst2 & LASTxchg2 & #AllEvents2 & >#LASTemp2 & >[%VALhmap2 %LASTemp2])".
  simplify_meta with "HM' HM". iClear "HM'".
  iDestruct (StackInv_OmoAuth_acc with "Mt●2") as "[Mt●2 Close]".
  iDestruct (OmoAuth_wf with "Mt●2") as %[OMO_GOODt2 _].
  iDestruct (OmoAuth_omo_nonempty with "Mt●2") as %Nomot2.
  have NZomot2 : length omot2 ≠ 0 by destruct omot2.
  eapply omo_stlist_length in OMO_GOODt2 as EQlentST2.
  iDestruct ("Close" with "Mt●2") as "Mt●2".

  iAaccIntro with "Mt●2".
  { (* Peeking case *)
    iIntros "Mt●2". iModIntro. iFrame "AU s0↦ s1↦". repeat iExists _. iFrame. iFrame "HM AllEvents2 LASTemp2". done. }

  iIntros (b2 V2 Et2' omot2' tstlist2' Mt2') "(#⊒V2 & >Mt●2 & #⊒Mt2'@V2 & CASE)".
  destruct b2.
  { (* Push on tstack success: commit here *)
    iDestruct "CASE" as "((%HEt2' & %Homot2' & [%tst2 %Htstlist2'] & %LeV0'V2 & %SubMtMt2') & #MAXgenMt & WCOMMIT)".
    iMod "AU" as (?) "[>(%&%&%& M●2') [_ Commit]]".
    iDestruct (OmoAuth_agree with "M●2 M●2'") as %(<- & <- & <- & <-).
    iCombine "M●2 M●2'" as "M●2".

    iDestruct "LASTemp2" as (tezf2 tgenzf2) "(#ezfs2↦tezf2 & #MONO✓ezfs2 & (%Htezf2 & %Htgenzf2st & %LASTemp))".
    iDestruct (OmoAuth_OmoCW_l with "M●2 ezfs2↦tezf2") as %[eVzfs2 Hezfs2].

    iDestruct "LASTst2" as (stf2 tstf2) "[[%LASTstf2 %LASTtstf2] BIG2]".
    iDestruct (StackInv_OmoAuth_acc with "Mt●2") as "[Mt●2 Close]".
    iDestruct (OmoAuth_wf with "Mt●2") as %[OMO_GOODt2' _].
    iDestruct (OmoEinfo_get _ _ _ _ _ _ (length Et2) with "Mt●2") as "#ten2✓teV2"; [by rewrite HEt2' lookup_app_1_eq|].
    iDestruct ("Close" with "Mt●2") as "Mt●2".

    eapply (omo_write_op_step _ _ _ (length omot2 - 1) (length Et2)) in OMO_GOODt2' as STEP; last first.
    { rewrite Nat.sub_add; [|lia]. rewrite EQlentST2 Htstlist2' lookup_app_1_eq. done. }
    { rewrite last_lookup in LASTtstf2. replace (Init.Nat.pred (length tstlist2)) with (length tstlist2 - 1) in LASTtstf2 by lia.
      rewrite Htstlist2' EQlentST2 lookup_app_1_ne; [done|]. lia. }
    { by rewrite HEt2' lookup_app_1_eq. }
    { rewrite Nat.sub_add; [|lia]. rewrite Homot2' omo_append_w_write_op omo_write_op_length lookup_app_1_eq. done. }
    inversion STEP; [|inversion POP|inversion EMPPOP|inversion INIT]. inversion PUSH. subst v0. clear PUSH. subst u uV stk.

    have LeV0V2 : V0 ⊑ V2 by solve_lat.
    set psId := length E2.
    set M' := {[psId]} ∪ M.
    set eVpush := mkOmoEvent (Push v) V2 M'.
    set E2' := E2 ++ [eVpush].
    set nst : stack_state := (psId, v, V2, M') :: stf2.

    iDestruct (view_at_mono_2 _ V2 with "⊒M@V0'") as "⊒M@V2"; [done|].
    iMod (OmoAuth_insert_last with "M●2 ⊒M@V2 WCOMMIT []") as "(M●2 & #⊒M'@V2 & #psId↦ten2 & #psId✓eVpush & _)".
    { have ? : step psId eVpush stf2 nst; [|done].
      apply stack_step_Push; try done. set_solver. }
    iMod (OmoHb_new_1 with "M●2 psId✓eVpush ten2✓teV2") as "[M●2 #psId⊒ten2]"; [done|].
    iMod (OmoHb_new_1 with "M●2 psId✓eVpush psId✓eVpush") as "[M●2 #psId⊒psId]"; [done|].
    iDestruct (OmoHbToken_finish with "M●2") as "[M●2 M●2']".
    iDestruct (OmoSnapHistory_get with "M●2") as "#E◯2".

    iDestruct (StackInv_OmoAuth_acc with "Mt●2") as "[Mt●2 Close]". rewrite Homot2'.
    iMod (CWMono_insert_last_last (wr_event (length omo2)) with "MONO2 M●2 Mt●2 psId↦ten2") as "(MONO2 & #MONO✓psId & M●2 & Mt●2)".
    { rewrite lookup_omo_wr_event omo_append_w_write_op omo_write_op_length lookup_app_1_eq. done. } { rewrite omo_append_w_length /=. lia. }
    iDestruct ("Close" with "Mt●2") as "Mt●2".

    iMod ("Commit" $! true V2 E2' (Push v) M' with "[M●2']") as "HΦ".
    { iFrame "⊒V2". iSplitL "M●2'"; [by repeat iExists _|]. iSplit.
      - iPureIntro. split_and!; try done. set_solver.
      - iSplit; [|by iFrame "SInv"]. repeat iExists _. iFrame "HM E◯2 ⊒eV0@V0' ⊒M'@V2 ⊒Mt@V0' ⊒Mx@V0' e0✓eV0". done. }

    iDestruct (OmoEinfo_get _ _ _ _ _ _ ezfs2 with "M●2") as "#ezfs2✓eVzfs2".
    { rewrite lookup_app_1_ne; [done|]. apply lookup_lt_Some in Hezfs2. lia. }
    iDestruct (OmoLt_get_append_w with "M●2 ezfs2✓eVzfs2") as "#ezfs2<psId"; [by apply lookup_lt_Some in Hezfs2; lia|].

    iModIntro. iSplitR "HΦ".
    { repeat iExists _. iFrame. iFrame "HM". iSplitL "BIG2"; last iSplit; last iSplit.
      - iModIntro. iExists nst,tst2. rewrite Htstlist2'. iSplit.
        + rewrite !last_app /=. done.
        + subst nst tst2. rewrite big_sepL2_cons. iFrame "BIG2". repeat iExists _. iFrame "psId✓eVpush ten2✓teV2". done.
      - iModIntro. rewrite /AllEvents big_sepL_snoc. iDestruct "AllEvents2" as "[ezfl2↪emp BIG]".
        iFrame "ezfl2↪emp BIG". subst eVpush. simpl. iRight.
        iExists psId,(length Et2). iDestruct (OmoEq_get_from_Einfo with "psId✓eVpush") as "#psId=psId".
        iDestruct (OmoLe_get_from_Eq with "psId=psId") as "psId≤psId".
        iFrame "ezfs2<psId psId≤psId psId⊒psId psId⊒ten2 psId↦ten2 MONO✓psId".
      - iModIntro. iExists tezf2,tgenzf2. iFrame "ezfs2↦tezf2 MONO✓ezfs2". iPureIntro. split_and!.
        + rewrite omo_append_w_write_op lookup_app_1_ne; [done|]. apply lookup_lt_Some in Htezf2. lia.
        + rewrite Htstlist2' lookup_app_1_ne; [done|]. apply lookup_lt_Some in Htgenzf2st. lia.
        + intros. subst tstlist2'. destruct (decide (tgen' = length tstlist2)) as [->|NEQ].
          * rewrite lookup_app_1_eq in H. inversion H. subst st'. subst tst2. done.
          * rewrite lookup_app_1_ne in H; [|done]. by eapply LASTemp.
      - iPureIntro. split; [done|]. rewrite omo_append_w_write_op. destruct LASTemp2 as (genzfl2 & Hgenzfl2 & H).
        exists genzfl2. split.
        + rewrite lookup_app_1_ne; [done|]. apply lookup_lt_Some in Hgenzfl2. lia.
        + intros. destruct (decide (i = length stlist2)) as [->|NEQ].
          * rewrite lookup_app_1_eq in H0. inversion H0. subst nst. done.
          * rewrite lookup_app_1_ne in H0; [|done]. eapply H; try done. }

    iIntros "_". wp_pures. by iApply "HΦ". }

  (* Push on tstack failed, use exchanger *)
  iDestruct "CASE" as %(-> & -> & -> & ->).
  iModIntro. iSplitR "AU s0↦ s1↦". { repeat iExists _. iFrame. iFrame "HM AllEvents2 LASTemp2". done. }
  iIntros "_". wp_pures. rewrite -[Z.to_nat 1]/(1%nat). wp_read. wp_pures.

  iDestruct (view_at_intro_incl with "AU ⊒V0'") as (V0'') "(#⊒V0'' & %LeV0'V0'' & AU@V0'')".

  (* Inv access 3 *)
  have NDISJ'' : (xchgN N) ## histN by solve_ndisj.
  awp_apply (new_offer_spec xc _ NDISJ'' lx _ γgx _ V0'' v with "⊒V0'' ⊒Mx"); [lia|].
  iInv "SInv" as (E3) "H".
  iDestruct "H" as (γs3 ???????? Et3) "(%Ex3 & %omo3 & %omot3 & %omox3 & %stlist3 & %tstlist3 & %xstlist3 & %Mono3 & %hmap3 & %ezfs3 & %ezfl3 &
    >HM' & >M●3 & >Mt●3 & >Mx●3 & >MONO3 & >Hγh3 & >Field3 & >LASTst3 & LASTxchg3 & #AllEvents3 & >#LASTemp3 & >[%VALhmap3 %LASTemp3])".
  simplify_meta with "HM' HM". iClear "HM'".
  iDestruct (ExchangerInv_OmoAuth_acc with "Mx●3") as "[Mx●3 Close]".
  iDestruct (OmoAuth_wf with "Mx●3") as %[OMO_GOODx3 _].
  iDestruct (OmoAuth_omo_nonempty with "Mx●3") as %Nomox3.
  have NZomox3 : length omox3 ≠ 0 by destruct omox3.
  eapply omo_stlist_length in OMO_GOODx3 as EQlenxST3.
  iDestruct ("Close" with "Mx●3") as "Mx●3".

  iAaccIntro with "Mx●3".
  { (* Peeking case *)
    iIntros "Mx●3". iModIntro. iFrame "AU@V0'' s0↦ s1↦ ". repeat iExists _. iFrame. iFrame "HM AllEvents3 LASTemp3". done. }

  iIntros (v3 V3 Ex3' omox3' xstlist3' Mx3) "(#⊒V3 & >Mx●3 & #⊒Mx3@V3 & CASE)".
  destruct (decide (v3 = 0%Z)) as [->|NEQ].
  { (* [new_offer] failed, commit nothing *)
    iDestruct "CASE" as %(-> & -> & -> & ->). iDestruct (view_at_elim with "⊒V0'' AU@V0''") as "AU".
    iMod "AU" as (E3'') "[M●3' [_ Commit]]". iDestruct "M●3'" as (???) ">M●3'".
    iDestruct (OmoSnapHistory_get with "M●3'") as "#E◯3'".
    iMod ("Commit" $! false V0' E3'' dummy_sevt_hist M with "[M●3']") as "HΦ".
    { iFrame "⊒V0'". iSplitL "M●3'"; [repeat iExists _; iFrame "M●3'"|]. iSplit; [done|].
      iSplit; [|by iFrame "SInv"]. repeat iExists _. iFrame "HM E◯3' ⊒M@V0' ⊒Mt@V0' ⊒Mx@V0' e0✓eV0 ⊒eV0@V0'". }
    iModIntro. iSplitR "HΦ". { repeat iExists _. iFrame. iFrame "HM AllEvents3 LASTemp3". done. }
    iIntros "_". wp_pures. by iApply "HΦ". }

  (* [new_offer] succeeded, register helping *)
  iDestruct "CASE" as "[([%l3 %EQv3] & %LeV2'V3 & %Homox3' & [%xst3 %Hxstlist3'] & %HEx3' & %SubMxMx3) WCOMMIT]".
  iAssert (@{V3} atomic_update_push N γg s v V0 M (λ b, Φ #b))%I with "[AU@V0'']" as "AU@V3".
  { iDestruct (view_at_objective_iff _ V0'' with "SInv") as "SInv@V0''".
    iCombine "SInv@V0'' AU@V0''" as "RES".
    iApply (view_at_mono with "RES"); [done|]. iIntros "[#SInv AU]".
    rewrite /atomic_update_push. iAuIntro. iApply (aacc_aupd with "AU"); [done|].
    iIntros (E) "H". iAaccIntro with "H".
    { iIntros "H !>". iFrame. iIntros "AU !>". iFrame. }
    iIntros (b V' E' ps M') "(H & %CASE & ⊒V' & LocalInner)". iRight. iModIntro.
    iExists b,V',E',ps,M'. iFrame. iFrame "SInv". iSplit; [destruct b; des; done|]. iIntros "HΦ". iModIntro. by iApply "HΦ". }

  (* Obtain latest state and corresponding information of exchanger *)
  iDestruct (ExchangerInv_OmoAuth_acc with "Mx●3") as "[Mx●3 Close]".
  iDestruct (OmoAuth_wf with "Mx●3") as %[OMO_GOODx3' _].
  iDestruct ("Close" with "Mx●3") as "Mx●3".
  iDestruct "LASTxchg3" as (xstl3 xstr3) "(>%LASTxst3 & BIGxstl3 & BIGxstr3)".

  eapply (omo_write_op_step _ _ _ (length omox3 - 1) (length Ex3)) in OMO_GOODx3' as STEP; last first.
  { rewrite Nat.sub_add; [|lia]. rewrite EQlenxST3 Hxstlist3' lookup_app_1_eq. done. }
  { rewrite last_lookup in LASTxst3. replace (Init.Nat.pred (length xstlist3)) with (length xstlist3 - 1) in LASTxst3 by lia.
    rewrite Hxstlist3' EQlenxST3 lookup_app_1_ne; [done|]. lia. }
  { by rewrite HEx3' lookup_app_1_eq. }
  { rewrite Nat.sub_add; [|lia]. rewrite Homox3' omo_append_w_write_op omo_write_op_length lookup_app_1_eq. done. }
  inversion STEP; [inversion INIT|..|inversion ACK|inversion RVK|inversion ACP].
  inversion REG. subst e eV stl str v0. clear STEP REG. rename H1 into Hxst3.

  iMod UTok_alloc as (γu) "Hγu".
  iMod (saved_vProp_alloc DfracDiscarded (Φ #true)) as (γpt) "#Hγpt"; [done|].
  iMod (saved_vProp_alloc DfracDiscarded (Φ #false)) as (γpf) "#Hγpf"; [done|].
  remember (encode (γpt,γpf,γu)) as γi eqn:Hγi.
  iMod (ghost_map_insert_persist (length Ex3) (γi,V3) with "Hγh3") as "[Hγh3 #KEY]".
  { destruct (hmap3 !! length Ex3) eqn:Heq; try done.
    have LOOKUP : is_Some (hmap3 !! length Ex3) by done. apply VALhmap3 in LOOKUP. lia. }

  iModIntro. iSplitR "Hγu".
  { repeat iExists _. iFrame. iFrame "HM AllEvents3 LASTemp3". iModIntro. iSplit.
    - repeat iExists _. iSplit; [by rewrite Hxstlist3' -Hxst3 last_app|].
      rewrite big_sepM_insert; [|done]. iFrame "BIGxstr3 BIGxstl3".
      iExists γi,γpt,γpf,γu,V0,M,(λ b, Φ #b),E0. simpl. iFrame "AU@V3 WCOMMIT Hγpt Hγpf KEY". iSplit.
      + iPureIntro. split_and!; try done. solve_lat.
      + repeat iExists _. iFrame "HM E◯0 ⊒M@V0' ⊒Mt@V0' ⊒Mx@V0' e0✓eV0 ⊒eV0@V0'".
    - iPureIntro. split; [|done]. unfold hmap_valid in *. intros. destruct H as [γ He]. destruct (decide (e = length Ex3)) as [->|NEe].
      + subst Ex3'. rewrite app_length /=. lia.
      + have LOOKUP : is_Some (hmap3 !! e) by rewrite lookup_insert_ne in He.
        apply VALhmap3 in LOOKUP. subst Ex3'. rewrite app_length /=. lia. }

  subst v3. iIntros "(%&%& Token)". inversion H. subst l'. clear H. wp_pures.

  (* Inv access 4 *)
  awp_apply (check_offer_spec xc _ NDISJ'' lx l3 _ γgx _ V3 with "⊒V3 ⊒Mx Token").
  iInv "SInv" as (E4) "H".
  iDestruct "H" as (γs4 ???????? Et4) "(%Ex4 & %omo4 & %omot4 & %omox4 & %stlist4 & %tstlist4 & %xstlist4 & %Mono4 & %hmap4 & %ezfs4 & %ezfl4 &
    >HM' & >M●4 & >Mt●4 & >Mx●4 & >MONO4 & >Hγh4 & >Field4 & >LASTst4 & LASTxchg4 & #AllEvents4 & >#LASTemp4 & >[%VALhmap4 %LASTemp4])".
  simplify_meta with "HM' HM". iClear "HM'".
  iDestruct (ExchangerInv_OmoAuth_acc with "Mx●4") as "[Mx●4 Close]".
  iDestruct (OmoAuth_wf with "Mx●4") as %[OMO_GOODx4 _].
  iDestruct (OmoAuth_omo_nonempty with "Mx●4") as %Nomox4.
  have NZomox4 : length omox4 ≠ 0 by destruct omox4.
  eapply omo_stlist_length in OMO_GOODx4 as EQlenxST4.
  iDestruct ("Close" with "Mx●4") as "Mx●4".

  iAaccIntro with "[Mx●4 LASTxchg4]".
  { instantiate (1 := [tele_arg γsx; Ex4; omox4; xstlist4; (last_state_xchg N γg s γgx γh xstlist4 hmap4)]). iFrame "Mx●4 LASTxchg4". }
  { (* Peeking case *)
    iIntros "[Mx●4 LASTxchg4]". iModIntro. iFrame "Hγu". repeat iExists _. iFrame. iFrame "HM AllEvents4 LASTemp4". done. }

  iIntros (v4 V4 xev4 omox4' xstlist4' Mx4) "(LASTxchg4 & #⊒V4 & >Mx●4 & #⊒Mx4@V4 & [%LeV3V4 %SubMxMx4] & CASE)".
  iDestruct (ExchangerInv_OmoAuth_acc with "Mx●4") as "[Mx●4 Close]".
  iDestruct (OmoAuth_wf with "Mx●4") as %[OMO_GOODx4' _].
  iDestruct ("Close" with "Mx●4") as "Mx●4".
  iDestruct "LASTxchg4" as (xstl4 xstr4) "(%LASTxst4 & BIGxstl4 & BIGxstr4)".

  destruct (decide (v4 = (-1)%Z)) as [->|NEQv4].
  { (* revoked my offer, commit nothing *)
    iDestruct "CASE" as "[(-> & %Homox4' & [%xst4 %Hxstlist4']) _]".

    eapply (omo_write_op_step _ _ _ (length omox4 - 1) (length Ex4)) in OMO_GOODx4' as STEP; last first.
    { rewrite Nat.sub_add; [|lia]. rewrite EQlenxST4 Hxstlist4' lookup_app_1_eq. done. }
    { rewrite last_lookup in LASTxst4. replace (Init.Nat.pred (length xstlist4)) with (length xstlist4 - 1) in LASTxst4 by lia.
      rewrite Hxstlist4' EQlenxST4 lookup_app_1_ne; [done|]. lia. }
    { by rewrite lookup_app_1_eq. }
    { rewrite Nat.sub_add; [|lia]. rewrite Homox4' omo_append_w_write_op omo_write_op_length lookup_app_1_eq. done. }
    inversion STEP; [inversion INIT|inversion REG|inversion ACK|inversion RVK|inversion ACP].
    subst e eV stl str e'. rename H1 into Hxst4.

    destruct ACKS as [xinfo4 Hxinfo4].
    iDestruct (big_sepM_delete with "BIGxstl4") as "[H BIGxstl4]"; [done|].
    iDestruct "H" as (????????) "((%Hγi' & %LeVixinfo4 & %GZ) & [AU #⊒M0] & WCOMMIT & #Hγpt' & #Hγpf' & #KEY')".
    iDestruct (ghost_map_elem_agree with "KEY KEY'") as %H. inversion H. rewrite -H1 in Hγi'. encode_agree Hγi. subst γi0 V3. clear H.
    iDestruct (view_at_elim with "⊒V3 AU") as "AU".

    iMod "AU" as (?) "[>M● [_ Commit]]". iDestruct "M●" as (???) "M●".
    iDestruct (OmoSnapHistory_get with "M●") as "#E◯".
    iMod ("Commit" $! false V4 x dummy_sevt_hist M0 with "[M●]") as "HΦ".
    { iFrame "⊒V4". iSplitL; [repeat iExists _; iFrame|]. iSplit; [done|].
      iDestruct (view_at_objective_iff _ xinfo4.1.2 with "E◯") as "E◯'".
      iCombine "⊒M0 E◯'" as "RES". iApply (view_at_mono with "RES"); [done|]. iIntros "[#⊒M #E◯]".
      iDestruct "⊒M" as (??????????) "(%& H1 & H2 & H3 & H4 & H5 & H6 & H7)". repeat iExists _. iFrame "E◯". iFrame "#". }

    iModIntro. iSplitR "HΦ".
    { repeat iExists _. iFrame. iFrame "HM AllEvents4 LASTemp4". iModIntro. iSplit.
      - repeat iExists _. iFrame "BIGxstr4 BIGxstl4". rewrite Hxstlist4' Hxst4 last_app /=. done.
      - iPureIntro. split; [|done]. unfold hmap_valid in *. intros. apply VALhmap4 in H. rewrite app_length /=. lia. }

    iIntros "_". iDestruct (saved_vProp_agree with "Hγpf Hγpf'") as "EQ". wp_pures. iRewrite "EQ". done. }

  (* Exchange success, already committed by Pop thread *)
  iDestruct "CASE" as "[(_ & -> & -> & %Homox4') _]".

  have [[xe xes] Hxgen4] : is_Some (omox4 !! (length omox4 - 1)) by rewrite lookup_lt_is_Some; lia.
  eapply (omo_read_op_step _ _ _ (length omox4 - 1) (length xes) (length Ex4)) in OMO_GOODx4' as STEP; last first.
  { rewrite last_lookup -EQlenxST4 in LASTxst4. replace (Init.Nat.pred (length omox4)) with (length omox4 - 1) in LASTxst4 by lia. done. }
  { rewrite lookup_app_1_eq. done. }
  { rewrite lookup_omo_ro_event Homox4' omo_insert_r_read_op list_lookup_alter /omo_read_op list_lookup_fmap Hxgen4 /= lookup_app_1_eq. done. }
  inversion STEP; [inversion INIT|inversion REG|inversion ACK|inversion RVK|inversion ACP].
  subst e eV stl str e' v0.

  iDestruct (big_sepM_lookup_acc with "BIGxstr4") as "[Inner BIGxstr4]"; [exact ACKS|].
  iDestruct "Inner" as (??????) "([%Hγi' %EQv4] & #KEY' & #Hγpt' & CASE)". simpl in EQv4. subst v4.
  iDestruct (ghost_map_elem_agree with "KEY KEY'") as %H. inversion H. subst γi0 Vb. encode_agree Hγi. clear H.
  iDestruct "CASE" as "[HΦ|Hγu']"; [|by iDestruct (UTok_unique with "Hγu Hγu'") as %?]. simpl.

  iDestruct ("BIGxstr4" with "[Hγu]") as "BIGxstr4".
  { repeat iExists _. iFrame "KEY Hγpt'". iSplit; [done|]. iRight. done. }
  iModIntro. iSplitR "HΦ".
  { repeat iExists _. iFrame. iFrame "HM AllEvents4 LASTemp4". iSplit.
    - repeat iExists _. iFrame. done.
    - iPureIntro. split; [|done]. unfold hmap_valid in *. intros. apply VALhmap4 in H. rewrite app_length /=. lia. }

  iDestruct (saved_vProp_agree with "Hγpt Hγpt'") as "EQ". iIntros "_". wp_pures.
  simpl in *.
  iDestruct (view_at_mono_2 _ V4 with "HΦ") as "HΦ"; [solve_lat|].
  iDestruct (view_at_elim with "⊒V4 HΦ") as "HΦ". iRewrite "EQ". done.
Qed.

Lemma push_spec :
  spec_history.push_spec' (push try_push' new_offer check_offer) EStackLocal EStackInv.
Proof.
  intros N DISJ s tid γg E0 M V0 v NZ. iIntros "#⊒V0 #EStackLocal" (Φ) "AU".

  iLöb as "IH" forall "#". wp_rec. awp_apply (try_push_spec with "⊒V0 EStackLocal"); [done|done|].
  iApply (aacc_aupd with "AU"); [done|].
  iIntros (E) "M●". iAaccIntro with "M●"; first by eauto with iFrame.

  iIntros (b V1 E1 ps M1) "(M● & %CASE & #⊒V1 & #⊒M1@V1)".
  iModIntro. destruct b.
  - iRight. destruct CASE as (EQE1 & PS & LeV0V1 & SubMM1).
    iExists V1,E1,ps,M1. iFrame "⊒V1 M● ⊒M1@V1". iSplit; [done|]. iIntros "HΦ !> _". wp_pures. by iApply "HΦ".
  - iLeft. destruct CASE as [-> ->]. iFrame "M●". iIntros "AU !> _". wp_if. iApply ("IH" with "AU"); try done.
Qed.

Lemma try_pop_spec :
  spec_history.try_pop_spec' (try_pop try_pop' take_offer) EStackLocal EStackInv.
Proof.
  intros N DISJ s tid γg E0 M V0. iIntros "#⊒V0 #EStackLocal" (Φ) "AU".
  iDestruct "EStackLocal" as "[(%&%&%&%&%&%&%&%&%&%&%& HM & #E◯0 & ⊒M & ⊒Mt & ⊒Mx & e0✓eV0 & ⊒eV0) SInv]".
  wp_lam. wp_pures. rewrite -[Z.to_nat 0]/(0%nat) shift_0. wp_bind (! _)%E.

  (* Inv access 1 *)
  iInv "SInv" as (E1) "H" "Hclose".
  iDestruct "H" as (γs1 ???????? Et1) "(%Ex1 & %omo1 & %omot1 & %omox1 & %stlist1 & %tstlist1 & %xstlist1 & %Mono1 & %hmap1 & %ezfs1 & %ezfl1 &
    >HM' & >M●1 & Mt●1 & Mx●1 & MONO1 & Hγh1 & >Field1 & >LASTst1 & LASTxchg1 & #AllEvents1 & >#LASTemp1 & >[%VALhmap1 %LASTemp1])".
  simplify_meta with "HM' HM".  iClear "HM'".
  iDestruct (field_info_dup with "Field1") as "[Field1 (%&%& #e0✓eV0' & s↦)]".
  iDestruct (OmoEinfo_agree with "e0✓eV0 e0✓eV0'") as %<-. iClear "e0✓eV0'".
  iDestruct (view_at_elim with "⊒eV0 s↦") as "[s0↦ s1↦]".
  iDestruct (StackLocal_OmoEview with "⊒Mt") as "⊒Mt'".
  iDestruct (OmoEview_update with "M●1 ⊒M ⊒M") as (M') "(M●1 & #⊒M' & M⊢M' & %LeMM')".
  iDestruct (OmoEview_update with "M●1 ⊒M' ⊒Mt'") as (Mt1) "(M●1 & #⊒Mt1 & M'⊢Mt1 & %LEMh0Mh1)".
  iDestruct (StackLocal_Eview_update with "⊒Mt ⊒Mt1") as "⊒Mt1'".
  replace (Mt ∪ Mt1) with Mt1; [|set_solver].
  iCombine "⊒M ⊒Mt1' ⊒Mx ⊒eV0" as "⊒INFO".
  iDestruct (view_at_intro_incl with "⊒INFO ⊒V0") as (V0') "(⊒V0' & %LeV0V0' & (⊒M@V0' & ⊒Mt1@V0' & ⊒Mx@V0' & ⊒eV0@V0'))".

  iMod ("Hclose" with "[-AU s0↦ s1↦ M⊢M' M'⊢Mt1]") as "_".
  { repeat iExists _. iFrame. iFrame "HM AllEvents1 LASTemp1". done. }
  wp_read. iApply fupd_mask_intro_subseteq; [done|]. wp_pures.

  (* Inv access 2 *)
  have NDISJ' : (tstackN N) ## histN by solve_ndisj.
  awp_apply (try_pop_spec ts _ NDISJ' lt _ γgt _ V0' with "⊒V0' ⊒Mt1'").
  iInv "SInv" as (E2) "H".
  iDestruct "H" as (γs2 ???????? Et2) "(%Ex2 & %omo2 & %omot2 & %omox2 & %stlist2 & %tstlist2 & %xstlist2 & %Mono2 & %hmap2 & %ezfs2 & %ezfl2 &
    >HM' & >M●2 & >Mt●2 & Mx●2 & >MONO2 & >Hγh2 & >Field2 & >LASTst2 & LASTxchg2 & >#AllEvents2 & >#LASTemp2 & >[%VALhmap2 %LASTemp2])".
  simplify_meta with "HM' HM". iClear "HM'".
  iDestruct (StackInv_OmoAuth_acc with "Mt●2") as "[Mt●2 Close]".
  iDestruct (OmoAuth_wf with "Mt●2") as %[OMO_GOODt2 _].
  iDestruct (OmoAuth_omo_nonempty with "Mt●2") as %Nomot2.
  have NZomot2 : length omot2 ≠ 0 by destruct omot2.
  eapply omo_stlist_length in OMO_GOODt2 as EQlentST2.
  iDestruct ("Close" with "Mt●2") as "Mt●2".

  iAaccIntro with "Mt●2".
  { (* Peeking case *)
    iIntros "Mt●2". iModIntro. iFrame "AU s0↦ s1↦ M⊢M' M'⊢Mt1". repeat iExists _. iFrame. iFrame "HM AllEvents2 LASTemp2". done. }

  iIntros (v2 V2 Et2' omot2' tstlist2' Mt2) "(#⊒V2 & >Mt●2 & #⊒Mt2@V2 & CASE)".
  destruct (decide (v2 = (-1)%Z)) as [->|NEv2]; last first.
  { (* If there was no race, then commit here, either Pop or EmpPop *)
    iDestruct "CASE" as "([%LeV0'V2 %SubMt1Mt2] & #MAXgenMt1 & CASE)".
    destruct (decide (v2 = 0%Z)) as [->|NEv2'].
    - (* Commit EmpPop *)
      iDestruct "CASE" as "[(%HEt2' & -> & (%tgen2 & %Homot2' & %LTtgen2)) RCOMMIT]".

      iAssert (OmoUB γg M ezfl2 ∗ OmoSnap γg γs2 ezfl2 [])%I with "[-]" as "[#MAXgenM #ezf2↪emp]".
      { iDestruct "LASTemp2" as (tezf2 tgenzf2) "(#ezfs2↦tezf2 & #MONO✓ezfs2 & (%Htezf2 & %Htgenzf2st & %LASTemp))".
        iDestruct "AllEvents2" as "[ezfl2↪emp AllEvents2]". iFrame "ezfl2↪emp".
        rewrite {2}/OmoUB. iApply big_sepS_forall. iIntros "%e %IN".
        iDestruct (OmoAuth_OmoEview with "M●2 ⊒M") as %CLOSED.
        apply CLOSED in IN as He. destruct He as [eV He].
        iDestruct (big_sepL_lookup with "AllEvents2") as "[CASE|CASE]"; [exact He|iFrame "CASE"|].
        (* Only one contradiction case remains *)
        iDestruct "CASE" as (??) "(#ezfs2<e' & #e'≤e & #e⊒e' & #e'⊒te' & #e'↦te' & #MONO✓e')".
        iDestruct (OmoHb_HbIncluded with "e⊒e' M⊢M'") as %IN'; [done|].
        iDestruct (OmoHb_HbIncluded with "e'⊒te' M'⊢Mt1") as %tIN; [done|].
        iDestruct (big_sepS_elem_of with "MAXgenMt1") as "#te'≤ten2"; [exact tIN|].

        iDestruct (StackInv_OmoAuth_acc with "Mt●2") as "[Mt●2 Close]".
        iDestruct (OmoAuth_wf with "Mt●2") as %[OMO_GOODt2' _].
        have [[te tes] Htgen2] : is_Some (omot2 !! tgen2) by rewrite lookup_lt_is_Some.
        have Htgen2st : tstlist2 !! tgen2 = Some [].
        { have [st Hst] : is_Some (tstlist2 !! tgen2) by rewrite lookup_lt_is_Some -EQlentST2.
          eapply (omo_read_op_step _ _ _ tgen2 (length tes) (length Et2)) in OMO_GOODt2'; last first; [done|..].
          - rewrite HEt2' lookup_app_1_eq. done.
          - rewrite lookup_omo_ro_event Homot2' omo_insert_r_read_op list_lookup_alter /omo_read_op list_lookup_fmap Htgen2 /= lookup_app_1_eq. done.
          - inversion OMO_GOODt2'; try done. subst st. done. }
        destruct (le_lt_dec tgen2 tgenzf2) as [LE|LT]; [|by specialize (LASTemp _ _ Htgen2st LT)].
        iDestruct (OmoLe_get _ _ _ _ _ _ (ro_event tgen2 (length tes)) (wr_event tgenzf2) with "Mt●2") as "#ten2≤tezf2"; [..|done|].
        { rewrite lookup_omo_ro_event Homot2' omo_insert_r_read_op list_lookup_alter /omo_read_op list_lookup_fmap Htgen2 /= lookup_app_1_eq. done. }
        { rewrite lookup_omo_wr_event Homot2' omo_insert_r_write_op. done. }
        iDestruct (OmoLe_trans with "te'≤ten2 ten2≤tezf2") as "te'≤tezf2".

        iDestruct (CWMono_acc with "MONO2 MONO✓e' MONO✓ezfs2 e'↦te' ezfs2↦tezf2 te'≤tezf2") as "#e'≤ezfs2".
        iDestruct (OmoLe_Lt_contra with "e'≤ezfs2 ezfs2<e'") as %?. done. }

      have LeV0V2 : V0 ⊑ V2 by solve_lat.
      set ppId := length E2.
      set M2 := {[ppId]} ∪ M.
      set eVpop := mkOmoEvent EmpPop V2 M2.
      set E2' := E2 ++ [eVpop].

      iDestruct (view_at_mono_2 _ V2 with "⊒M@V0'") as "⊒M@V2"; [done|].
      iMod "AU" as (?) "[M●2' [_ Commit]]". iDestruct "M●2'" as (???) ">M●2'".
      iDestruct (OmoAuth_agree with "M●2 M●2'") as %(<- & <- & <- & <-).
      iCombine "M●2 M●2'" as "M●2".
      iMod (OmoAuth_insert_ro with "M●2 ⊒M@V2 RCOMMIT ezf2↪emp MAXgenM []") as (gen2) "(M●2 & #⊒M2@V2 & #ppId↦ten2 & #ezf2=ppId & _)".
      { have ? : step ppId eVpop [] []; [|done]. apply stack_step_EmpPop; try done. set_solver. }
      iDestruct (OmoHbToken_finish with "M●2") as "[M●2 M●2']".
      iDestruct (OmoSnapHistory_get with "M●2") as "#E◯2".

      iMod ("Commit" $! 0%Z V2 E2' EmpPop M2 with "[M●2']") as "HΦ".
      { iFrame "⊒V2". iSplitL; [repeat iExists _; iFrame "M●2'"|]. iSplit; last iSplit; [|done|].
        - iFrame "SInv". repeat iExists _. iFrame "HM E◯2 ⊒M2@V2 ⊒Mt1@V0' ⊒Mx@V0' e0✓eV0 ⊒eV0@V0'".
        - iPureIntro. simpl. split_and!; try done. set_solver. }

      iModIntro. iSplitR "HΦ".
      { repeat iExists _. iFrame. rewrite Homot2' !omo_insert_r_write_op. iFrame "HM LASTemp2". iSplit; [|done].
        iModIntro. rewrite /AllEvents big_sepL_snoc. iDestruct "AllEvents2" as "[ezfl2↪emp AllEvents2]".
        iFrame "ezfl2↪emp AllEvents2". iLeft. iApply OmoLe_get_from_Eq. by iApply OmoEq_sym. }

      iIntros "_". wp_pures. by iApply "HΦ".
    - (* Commit Pop *)
      iDestruct "CASE" as "[(%HEt2' & %Homot2' & [%tst2 %Htstlist2']) WCOMMIT]".
      iDestruct "LASTemp2" as (tezf2 tgenzf2) "(#ezfs2↦tezf2 & #MONO✓ezfs2 & (%Htezf2 & %Htgenzf2st & %LASTemp))".
      iDestruct (OmoAuth_OmoCW_l with "M●2 ezfs2↦tezf2") as %[eVzfs2 Hezfs2].

      iDestruct "LASTst2" as (stf2 tstf2) "[[%LASTstf2 %LASTtstf2] BIG2]".
      iDestruct (StackInv_OmoAuth_acc with "Mt●2") as "[Mt●2 Close]".
      iDestruct (OmoAuth_wf with "Mt●2") as %[OMO_GOODt2' _].
      iDestruct (OmoEinfo_get _ _ _ _ _ _ (length Et2) with "Mt●2") as "#ten2✓teV2"; [by rewrite HEt2' lookup_app_1_eq|].
      iDestruct ("Close" with "Mt●2") as "Mt●2".
      iDestruct (OmoAuth_wf with "M●2") as %[OMO_GOOD2 _].
      eapply omo_stlist_length in OMO_GOOD2 as EQlenST2.

      eapply (omo_write_op_step _ _ _ (length omot2 - 1) (length Et2)) in OMO_GOODt2' as STEP; last first.
      { rewrite Nat.sub_add; [|lia]. rewrite EQlentST2 Htstlist2' lookup_app_1_eq. done. }
      { rewrite last_lookup in LASTtstf2. replace (Init.Nat.pred (length tstlist2)) with (length tstlist2 - 1) in LASTtstf2 by lia.
        rewrite Htstlist2' EQlentST2 lookup_app_1_ne; [done|]. lia. }
      { by rewrite HEt2' lookup_app_1_eq. }
      { rewrite Nat.sub_add; [|lia]. rewrite Homot2' omo_append_w_write_op omo_write_op_length lookup_app_1_eq. done. }
      inversion STEP; [inversion PUSH|inversion POP|inversion EMPPOP|inversion INIT]. subst o oV stk v tstf2. rename tst2 into ntstf2.
      simpl in *.

      destruct stf2 as [|stf2 nstf2].
      { iDestruct (big_sepL2_length with "BIG2") as %H. simpl in H. lia. }
      iDestruct (big_sepL2_cons with "BIG2") as "[H BIG2]".
      iDestruct (big_sepL2_length with "BIG2") as %EQlenSTs.
      iDestruct "H" as (eVf2 teVf2) "(#ef2✓eVf2 & #tef2✓teVf2 & (%EQ1 & %EQ2 & %eVf2OUT & %teVf2OUT & %eVf2LVIEW))".
      destruct stf2 as [[[ef2 zf2] Vf2] lVf2]. simpl in *. subst zf2 V lVf2.

      iDestruct (view_at_mono_2 _ V2 with "⊒M@V0'") as "⊒M@V2"; [solve_lat|].
      iDestruct (OmoEview_insert_new_obj with "⊒M@V2 ef2✓eVf2") as "⊒M2@V2"; [by rewrite eVf2OUT|].

      have LeV0V2 : V0 ⊑ V2 by solve_lat.
      set ppId := length E2.
      set M2 := {[ef2]} ∪ eVf2.(eview) ∪ M.
      set M2' := {[ppId]} ∪ M2.
      set eVpop := mkOmoEvent (Pop v2) V2 M2'.
      set E2' := E2 ++ [eVpop].

      iMod "AU" as (?) "[M●2' [_ Commit]]". iDestruct "M●2'" as (???) ">M●2'".
      iDestruct (OmoAuth_agree with "M●2 M●2'") as %(<- & <- & <- & <-).
      iCombine "M●2 M●2'" as "M●2".
      iMod (OmoAuth_insert_last with "M●2 ⊒M2@V2 WCOMMIT []") as "(M●2 & #⊒M2'@V2 & #ppId↦ten2 & #ppId✓eVpop & #ppId↪nstf2 & _)".
      { have ? : step ppId eVpop ((ef2, v2, Vf2, eVf2.(eview)) :: nstf2) nstf2; [|done].
        apply stack_step_Pop; try done. set_solver. }
      iMod (OmoHb_new_1 with "M●2 ppId✓eVpop ppId✓eVpop") as "[M●2 #ppId⊒ppId]"; [done|].
      iMod (OmoHb_new_1 with "M●2 ppId✓eVpop ten2✓teV2") as "[M●2 #ppId⊒ten2]"; [done|].
      iDestruct (OmoHbToken_finish with "M●2") as "[M●2 M●2']".
      iDestruct (OmoSnapHistory_get with "M●2") as "#E◯2".

      iDestruct (StackInv_OmoAuth_acc with "Mt●2") as "[Mt●2 Close]". rewrite Homot2'.
      iMod (CWMono_insert_last_last (wr_event (length omo2)) with "MONO2 M●2 Mt●2 ppId↦ten2") as "(MONO2 & #MONO✓ppId & M●2 & Mt●2)".
      { rewrite lookup_omo_wr_event omo_append_w_write_op omo_write_op_length lookup_app_1_eq. done. } { rewrite omo_append_w_length /=. lia. }
      iDestruct ("Close" with "Mt●2") as "Mt●2".

      iDestruct (OmoEinfo_get _ _ _ _ _ _ ezfs2 with "M●2") as "#ezfs2✓eVzfs2".
      { rewrite lookup_app_1_ne; [done|]. apply lookup_lt_Some in Hezfs2. lia. }
      iDestruct (OmoLt_get_append_w with "M●2 ezfs2✓eVzfs2") as "#ezfs2<ppId"; [by apply lookup_lt_Some in Hezfs2; lia|].

      iMod ("Commit" $! v2 V2 E2' (Pop v2) M2' with "[M●2']") as "HΦ".
      { iFrame "⊒V2". iSplit; [repeat iExists _; iFrame "M●2'"|]. iSplit; last iSplit; [|done|].
        - iFrame "SInv". repeat iExists _. iFrame "HM E◯2 ⊒M2'@V2 ⊒Mt2@V2 ⊒Mx@V0' e0✓eV0 ⊒eV0@V0'".
        - iPureIntro. rewrite decide_False; [|lia]. rewrite decide_False; [|lia]. split_and!; try done. set_solver. }

      set ezfs2' := match ntstf2 with | [] => ppId | _ => ezfs2 end.
      set ezfl2' := match ntstf2 with | [] => ppId | _ => ezfl2 end.
      iAssert (AllEvents γg γs2 γgt γgx γm E2' ezfs2' ezfl2' ∗ last_empty_t γg γgt γm ezfs2' (omo_write_op (omo_append_w omot2 (length Et2) [])) tstlist2'
        ∗ ⌜ last_empty ezfl2' (omo_write_op (omo_append_w omo2 ppId [])) (stlist2 ++ [nstf2]) ⌝)%I
        with "[-]" as "(#AllEvents2' & #LASTemp2' & %LASTemp2')".
      { destruct ntstf2; subst ezfs2' ezfl2'; (iSplit; last iSplit).
        - destruct nstf2; [|done]. iFrame "ppId↪nstf2".
          iApply big_sepL_forall. iIntros "%e %eV %Lookup". destruct (decide (e = length E2)) as [->|NEQ].
          + iLeft. iDestruct (OmoEq_get_from_Einfo with "ppId✓eVpop") as "#ppId=ppId".
            iApply OmoLe_get_from_Eq. done.
          + iLeft. iDestruct (OmoEinfo_get with "M●2") as "#ELEM"; [done|]. iApply OmoLe_get_from_Lt.
            iApply (OmoLt_get_append_w with "M●2 ELEM"). done.
        - iExists (length Et2),(length omot2). iFrame "ppId↦ten2 MONO✓ppId". iPureIntro. split_and!.
          + rewrite omo_append_w_write_op omo_write_op_length lookup_app_1_eq. done.
          + rewrite Htstlist2' EQlentST2 lookup_app_1_eq. done.
          + intros. apply lookup_lt_Some in H. subst tstlist2'. rewrite app_length -EQlentST2 /= in H. lia.
        - iPureIntro. rewrite omo_append_w_write_op. destruct nstf2; [|done]. exists (length omo2). split.
          + rewrite omo_write_op_length lookup_app_1_eq. done.
          + intros. apply lookup_lt_Some in H. rewrite app_length -EQlenST2 /= in H. lia.
        - subst E2'. iDestruct "AllEvents2" as "[ezfl2↪emp AllEvents2]". iFrame "ezfl2↪emp".
          iApply big_sepL_snoc. iFrame "AllEvents2". iRight. iExists ppId,(length Et2).
          iDestruct (OmoEq_get_from_Einfo with "ppId✓eVpop") as "ppId=ppId".
          iDestruct (OmoLe_get_from_Eq with "ppId=ppId") as "ppId≤ppId".
          iFrame "ezfs2<ppId ppId≤ppId ppId⊒ppId ppId⊒ten2 ppId↦ten2 MONO✓ppId".
        - iExists tezf2,tgenzf2. iFrame "ezfs2↦tezf2 MONO✓ezfs2". iPureIntro. split_and!.
          + rewrite omo_append_w_write_op lookup_app_1_ne; [done|]. apply lookup_lt_Some in Htezf2. lia.
          + rewrite Htstlist2' lookup_app_1_ne; [done|]. apply lookup_lt_Some in Htgenzf2st. lia.
          + intros. destruct (decide (tgen' = length tstlist2)) as [->|NEQ].
            * rewrite Htstlist2' lookup_app_1_eq in H. inversion H. done.
            * eapply LASTemp; try done. by rewrite Htstlist2' lookup_app_1_ne in H.
        - iPureIntro. rewrite omo_append_w_write_op. destruct LASTemp2 as (genzfl2 & Hezfl2 & LASTemp2).
          exists genzfl2. split.
          + rewrite lookup_app_1_ne; [done|]. apply lookup_lt_Some in Hezfl2. lia.
          + intros. destruct (decide (i = length stlist2)) as [->|NEQ].
            * rewrite lookup_app_1_eq in H. inversion H. subst st. unfold not. intros. subst nstf2. done.
            * rewrite lookup_app_1_ne in H; [|done]. eapply LASTemp2; try done. }

      iModIntro. iSplitR "HΦ".
      { iModIntro. repeat iExists _. iFrame. iFrame "HM LASTemp2' AllEvents2'". iSplit; [|done].
        repeat iExists _. iFrame "BIG2". subst tstlist2'. rewrite !last_app. done. }

      iIntros "_". wp_pures. rewrite bool_decide_false; [|lia]. wp_pures. by iApply "HΦ". }

  (* Race happened, try using exchanger *)
  iDestruct "CASE" as %(-> & -> & -> & ->).
  iModIntro. iSplitR "AU s0↦ s1↦ M⊢M' M'⊢Mt1".
  { repeat iExists _. iFrame. iFrame "HM AllEvents2 LASTemp2". done. }

  iIntros "_". wp_pures. rewrite -[Z.to_nat 1]/(1%nat). wp_read. wp_pures.

  (* Inv access 3 *)
  iDestruct (view_at_intro_incl with "AU ⊒V0'") as (V0'') "(#⊒V0'' & %LeV0'V0'' & AU@V0'')".
  have NDISJ'' : (xchgN N) ## histN by solve_ndisj.
  awp_apply (take_offer_spec xc _ NDISJ'' lx _ γgx _ V0'' 0%Z with "⊒V0'' ⊒Mx"); [done|].
  iInv "SInv" as (E3) "H".
  iDestruct "H" as (γs3 ???????? Et3) "(%Ex3 & %omo3 & %omot3 & %omox3 & %stlist3 & %tstlist3 & %xstlist3 & %Mono3 & %hmap3 & %ezfs3 & %ezfl3 &
    >HM' & >M●3 & >Mt●3 & >Mx●3 & >MONO3 & >Hγh3 & >Field3 & >#LASTst3 & LASTxchg3 & >#AllEvents3 & >#LASTemp3 & >[%VALhmap3 %LASTemp3])".
  simplify_meta with "HM' HM". iClear "HM'".
  iDestruct (ExchangerInv_OmoAuth_acc with "Mx●3") as "[Mx●3 Close]".
  iDestruct (OmoAuth_wf with "Mx●3") as %[OMO_GOODx3 _].
  iDestruct (OmoAuth_omo_nonempty with "Mx●3") as %Nomox3.
  have NZomox3 : length omox3 ≠ 0 by destruct omox3.
  eapply omo_stlist_length in OMO_GOODx3 as EQlenxST3.
  iDestruct ("Close" with "Mx●3") as "Mx●3".

  iAaccIntro with "[Mx●3 LASTxchg3]".
  { instantiate (1 := [tele_arg γsx; Ex3; omox3; xstlist3; (last_state_xchg N γg s γgx γh xstlist3 hmap3)]). iFrame "Mx●3 LASTxchg3". }
  { (* Peeking case *)
    iIntros "[Mx●3 LASTxchg3]". iModIntro. iFrame "AU@V0'' s0↦ s1↦ M⊢M' M'⊢Mt1". repeat iExists _. iFrame. iFrame "HM AllEvents3 LASTemp3 LASTst3". done. }

  iIntros (v3 V3 Ex3' omox3' xstlist3' Mx3) "(LASTxchg3 & #⊒V3 & >Mx●3 & #⊒Mx3@V3 & [%LeV0''V3 %SubMxMx3] & CASE)".
  destruct (decide (v3 = (-1)%Z)) as [->|NEQv3].
  { (* [take_offer] failed. [try_pop] also fails. Commit nothing *)
    iDestruct "CASE" as %(-> & -> & -> & ->).

    iDestruct (view_at_elim with "⊒V0'' AU@V0''") as "AU".
    iMod "AU" as (?) "[>M●3' [_ Commit]]". iDestruct "M●3'" as (???) "M●3'".
    iDestruct (OmoSnapHistory_get with "M●3'") as "#E◯3'".
    iMod ("Commit" $! (-1)%Z V0' x dummy_sevt_hist M with "[M●3']") as "HΦ".
    { iFrame "⊒V0'". iSplitL; [repeat iExists _; iFrame|]. iSplit; last iSplit; [|done|done].
      iFrame "SInv". repeat iExists _. iFrame "HM ⊒M@V0' ⊒Mx@V0' ⊒Mt1@V0' E◯3' e0✓eV0 ⊒eV0@V0'". }

    iModIntro. iSplitR "HΦ". { repeat iExists _. iFrame. iFrame "HM AllEvents3 LASTemp3 LASTst3". done. }
    iIntros "_". wp_pures. by iApply "HΦ". }

  (* [take_offer] succeeded. Commit Pop *)
  iDestruct "CASE" as "[(%HEx3' & %Homox3' & [%xst3 %Hxstlist3']) WCOMMIT]".
  iDestruct (ExchangerInv_OmoAuth_acc with "Mx●3") as "[Mx●3 Close]".
  iDestruct (OmoAuth_wf with "Mx●3") as %[OMO_GOODx3' _].
  iDestruct ("Close" with "Mx●3") as "Mx●3".
  iDestruct "LASTxchg3" as (xstl3 xstr3) "(%LASTxst3 & BIGxstl3 & BIGxstr3)".

  eapply (omo_write_op_step _ _ _ (length omox3 - 1) (length Ex3)) in OMO_GOODx3' as STEP; last first.
  { rewrite Nat.sub_add; [|lia]. rewrite EQlenxST3 Hxstlist3' lookup_app_1_eq. done. }
  { rewrite last_lookup in LASTxst3. replace (Init.Nat.pred (length xstlist3)) with (length xstlist3 - 1) in LASTxst3 by lia.
    rewrite Hxstlist3' EQlenxST3 lookup_app_1_ne; [done|]. lia. }
  { by rewrite HEx3' lookup_app_1_eq. }
  { rewrite Nat.sub_add; [|lia]. rewrite Homox3' omo_append_w_write_op omo_write_op_length lookup_app_1_eq. done. }
  inversion STEP; [inversion INIT|inversion REG|inversion ACK|inversion RVK|inversion ACP].
  subst e eV stl str v' v. rename H1 into Hxst3.

  iDestruct "LASTemp3" as (tezf3 tgenzf3) "(#ezfs3↦tezf3 & #MONO✓ezfs3 & (%Htezf3 & %Htgenzf3st & %LASTemp))".
  iDestruct "AllEvents3" as "[ezfl3↪emp AllEvents3]".
  iDestruct (big_sepM_delete with "BIGxstl3") as "[H BIGxstl3]"; [exact ACKS|].
  iDestruct "H" as (????????) "((%Hγi & %LeViV' & %NZv3) & AU' & WCOMMIT' & #Hγpt & #Hγpf & #KEY)".

  iAssert (|={⊤ ∖ ↑(xchgN N) ∖ ↑(estackN N)}=> @{V' ⊔ V3} (∃ E3' omo3' stlist3' γs3' ezfl3',
    Q true ∗ (emp -∗ Φ #v3) ∗ OmoAuth γg γs3' (1/2)%Qp E3' omo3' stlist3' stack_interpretable ∗
    AllEvents γg γs3' γgt γgx γm E3' ezfs3 ezfl3' ∗ last_state γg γgt stlist3' tstlist3 ∗ ⌜ last_empty ezfl3' (omo_write_op omo3') stlist3' ⌝))%I
      with "[M●3 AU@V0'' AU' WCOMMIT WCOMMIT']" as ">(%&%&%&%&%& HQ & HΦ & M●3 & #AllEvents3' & #LASTst3' & %LASTemp3')".
  { iDestruct "AU'" as "[AU' ⊒M0]".
    iCombine "⊒M@V0' MONO✓ezfs3 M●3 ⊒M0 WCOMMIT WCOMMIT' AllEvents3 ezfl3↪emp HM SInv LASTst3" as "RES".
    iDestruct (view_at_objective_iff _ (V' ⊔ V3) with "RES") as "RES".
    iDestruct (view_at_mono_2 _ (V' ⊔ V3) with "AU@V0''") as "AU@V"; [solve_lat|].
    iDestruct (view_at_mono_2 _ (V' ⊔ V3) with "AU'") as "AU'@V"; [solve_lat|].
    iAssert (@{V' ⊔ V3} ⊒(V' ⊔ V3))%I with "[]" as "#⊒V@V"; [done|].
    iCombine "RES AU@V AU'@V ⊒V@V" as "RES".
    rewrite -view_at_fupd. iApply (view_at_mono with "RES"); [done|].
    iIntros "((#⊒M@V0' & #MONO✓ezfs3 & M●3 & #⊒M0@V' & WCOMMIT2 & WCOMMIT1 & #AllEvents3 & #ezfl3↪emp & #HM & #SInv & #LASTst3) & AU2 & AU1 & #⊒V3')".

    set V3' := V' ⊔ V3. clear eV0.
    iDestruct (view_at_mono_2 _ V3' with "⊒M@V0'") as "⊒M@V3'"; [solve_lat|].
    iDestruct (view_at_mono_2 _ V3' with "⊒M0@V'") as "⊒M0@V3'"; [solve_lat|].
    iDestruct "⊒M0@V3'" as (??????????) "(%eV0 & HM' & _ & ⊒M0@V3' & ⊒Mt@V3' & ⊒Mx@V3' & #e0✓eV0 & ⊒eV0@V3')".
    rewrite !view_at_objective_iff. simplify_meta with "HM' HM". iClear "HM'".
    iDestruct (OmoEview_union_obj with "⊒M@V3' ⊒M0@V3'") as "⊒M3@V3'".
    set M3 := M ∪ M0.

    (* Pick latest observed event (e3) *)
    iDestruct (OmoEview_latest_elem_obj with "⊒M3@V3'") as (e3) "[MAXe3 %e3IN]".
    iDestruct (OmoAuth_wf with "M●3") as %[OMO_GOOD3 _].
    iDestruct (OmoAuth_OmoEview_obj with "M●3 ⊒M3@V3'") as %INCL.
    apply INCL in e3IN as e3IN'. eapply lookup_omo_surjective in e3IN'; [|done]. destruct e3IN' as [eidx3 Heidx3].
    eapply omo_stlist_length in OMO_GOOD3 as EQlenST3.
    set gen3 := gen_of eidx3.

    have LeViV3' : Vi ⊑ V3' by solve_lat.
    set psId := length E3.
    set M3' := {[psId]} ∪ M3.
    set eVpush := mkOmoEvent (Push v3) V3' M3'.
    set E3' := E3 ++ [eVpush].

    have LeV0V3' : V0 ⊑ V3' by solve_lat.
    set ppId := length E3'.
    set M3'' := {[ppId]} ∪ M3'.
    set eVpop := mkOmoEvent (Pop v3) V3' M3''.
    set E3'' := E3' ++ [eVpop].

    destruct LASTemp3 as (genzfl3 & Hgenzfl3 & LASTemp3).
    destruct (le_lt_dec gen3 genzfl3) as [LEgen|LTgen].
    - (* If current observation is ealier than [genzfl3], then commit Push and Pop consecutively at [genzfl3] *)
      iDestruct (OmoAuth_OmoSnap with "M●3 ezfl3↪emp") as %Hst; [by rewrite -lookup_omo_wr_event in Hgenzfl3|]. simpl in Hst.

      iAssert (∀ len, ∃ stnew, ⌜ interp_omo E3' ((psId, []) :: take len (drop (genzfl3 + 1)%nat omo3)) [] stnew ∧ (∀ i st1 st2,
        stlist3 !! (genzfl3 + i)%nat = Some st1 → stnew !! i = Some st2 → st2 = st1 ++ [(psId, v3, V3', M3')]) ⌝)%I with "[M●3]" as "%Hgengood".
      { iIntros "%len". iInduction len as [|] "IH".
        - rewrite take_0. iExists [[(psId,v3,V3',M3')]]. iPureIntro. split.
          + rewrite -(app_nil_l [(psId, [])]) -(app_nil_l [[(psId, v3, V3', M3')]]). eapply interp_omo_snoc. split_and!; try done.
            * rewrite lookup_app_1_eq. done.
            * apply interp_omo_nil.
            * eapply stack_step_Push; try done. set_solver-.
          + intros. destruct i; [|done]. inversion H0. subst st2. rewrite Nat.add_0_r Hst in H. inversion H. done.
        - iDestruct ("IH" with "M●3") as %(stnew & IH1 & IH2).
          destruct (le_lt_dec (length (drop (genzfl3 + 1) omo3)) len) as [LE'|LT'].
          { rewrite take_ge in IH1; [|done]. do 2 (rewrite take_ge; [|lia]). iExists stnew. done. }
          have [ees Hlast] : is_Some ((drop (genzfl3 + 1) omo3) !! len) by rewrite lookup_lt_is_Some.
          destruct ees as [e es]. rewrite (take_S_r _ _ (e, es)); [|done]. rewrite lookup_drop in Hlast.
          specialize (omo_gen_info _ _ _ _ _ _ OMO_GOOD3 Hlast) as (eV & eeVs & st' & EID_MATCH & EEVS_VALID & E3e & Lookup_stlist3 & Interp & ES).

          eapply LASTemp3 in Lookup_stlist3 as Nempst'; [|lia].
          destruct es; last first.
          { rewrite Forall_cons in ES. destruct ES as [(?&?&?&?) _].
            inversion H0; try done; apply (f_equal length) in H5; rewrite cons_length in H5; lia. }

          have [stp Hstp] : is_Some (stlist3 !! (genzfl3 + len)).
          { rewrite lookup_lt_is_Some. apply lookup_lt_Some in Lookup_stlist3. lia. }
          have STEP' : step e eV stp st'.
          { eapply omo_write_op_step; try done; replace (genzfl3 + len + 1) with (genzfl3 + 1 + len) by lia; try done.
            rewrite list_lookup_omo_destruct in Hlast. by destruct Hlast as [? _]. }

          apply interp_omo_length in IH1 as EQlen. apply lookup_lt_Some in Hlast as LTlen.
          rewrite /= take_length drop_length Nat.min_l in EQlen; [|lia].
          have [stp' Hstp'] : is_Some (stnew !! len) by rewrite lookup_lt_is_Some; lia.
          eapply IH2 in Hstp' as EQstp'; [|done].
          replace ((psId, []) :: take len (drop (genzfl3 + 1)%nat omo3) ++ [(e, [])]) with
              (((psId, []) :: take len (drop (genzfl3 + 1)%nat omo3)) ++ [(e, [])]); [|by simplify_list_eq].

          inversion STEP'; try (by subst).
          + iExists (stnew ++ [(e, v, eV.(sync), eV.(eview)) :: stp']). iPureIntro. split.
            * eapply interp_omo_snoc. split_and!; try done.
              -- rewrite lookup_app_1_ne; [done|]. apply lookup_lt_Some in E3e. lia.
              -- rewrite last_cons last_lookup -EQlen. replace (Init.Nat.pred (S len)) with len by lia. rewrite Hstp'. done.
              -- eapply stack_step_Push; try done.
            * intros. destruct (decide (i = length stnew)) as [->|NEQ].
              -- rewrite lookup_app_1_eq in H4. inversion H4. rewrite -EQlen in H3.
                 replace (genzfl3 + S len) with (genzfl3 + 1 + len) in H3 by lia. rewrite Lookup_stlist3 in H3. inversion H3.
                 subst st1. rewrite EQstp' -H2. clear. simplify_list_eq. done.
              -- eapply IH2; try done. by rewrite lookup_app_1_ne in H4.
          + iExists (stnew ++ [stk ++ [(psId, v3, V3', M3')]]). iPureIntro. split.
            * eapply interp_omo_snoc. split_and!; try done.
              -- rewrite lookup_app_1_ne; [done|]. apply lookup_lt_Some in E3e. lia.
              -- rewrite last_cons last_lookup -EQlen. replace (Init.Nat.pred (S len)) with len by lia. rewrite Hstp'. done.
              -- rewrite EQstp' -H1.
                 replace (((u, v, V, lV) :: stk) ++ [(psId, v3, V3', M3')]) with ((u, v, V, lV) :: (stk ++ [(psId, v3, V3', M3')])); [|by simplify_list_eq].
                 eapply stack_step_Pop; try done.
            * intros. destruct (decide (i = length stnew)) as [->|NEQ].
              -- rewrite lookup_app_1_eq in H4. inversion H4. rewrite -EQlen in H3.
                 replace (genzfl3 + S len) with (genzfl3 + 1 + len) in H3 by lia. rewrite Lookup_stlist3 in H3. inversion H3. subst. done.
              -- eapply IH2; try done. by rewrite lookup_app_1_ne in H4. }

      specialize (Hgengood (length (drop (genzfl3 + 1) omo3))) as (stnew & Hgengood & Hstnew).
      rewrite take_ge in Hgengood; [|done].
      iDestruct (OmoUB_into_gen with "M●3 MAXe3") as %MAXe3; [done|].
      apply (OmoUBgen_mono _ _ _ genzfl3) in MAXe3 as MAXgenzfl3; [|done].

      (* Commit Push *)
      iMod "AU1" as (?) "[M●3' [_ Commit]]". iDestruct "M●3'" as (???) ">M●3'".
      iDestruct (OmoAuth_agree with "M●3 M●3'") as %(<- & <- & <- & <-). iCombine "M●3 M●3'" as "M●3".
      iMod (OmoAuth_insert with "M●3 ⊒M3@V3' WCOMMIT1 []") as (γs3') "(M●3 & #⊒M3'@V3' & _ & #psId✓eVpush & _)".
      { iPureIntro. split_and!; try done; by subst eVpush. }
      iDestruct (OmoHbToken_finish with "M●3") as "[M●3 M●3']".
      iDestruct (OmoSnapHistory_get with "M●3") as "#E◯3'".

      iMod ("Commit" $! true V3' E3' (Push v3) M3' with "[M●3']") as "HQ".
      { iFrame "⊒V3'". iSplit; [repeat iExists _; iFrame|]. iSplit.
        - iPureIntro. split_and!; try done. set_solver-.
        - repeat iExists _. iFrame "HM E◯3' ⊒M3'@V3' ⊒Mt@V3' ⊒Mx@V3' e0✓eV0 ⊒eV0@V3'". }

      (* Commit Pop *)
      set omo3' := omo_insert_w omo3 (genzfl3 + 1) psId [].
      set stlist3' := take (genzfl3 + 1) stlist3 ++ stnew.
      set gen := (genzfl3 + 1)%nat.
      iDestruct (OmoAuth_wf with "M●3") as %[OMO_GOOD3' _].
      eapply omo_stlist_length in OMO_GOOD3' as EQlenST3'.

      iAssert (∀ len, ∃ stnew', ⌜ interp_omo E3'' ((ppId, []) :: take len (drop (gen + 1)%nat omo3')) [(psId, v3, V3', M3')] stnew' ∧ (∀ i st1 st2,
        stlist3 !! (genzfl3 + i)%nat = Some st1 → stnew' !! i = Some st2 → st1 = st2) ⌝)%I with "[M●3]" as "%Hgengood'".
      { iIntros "%len". iInduction len as [|] "IH".
        - rewrite take_0. iExists [[]]. iPureIntro. split.
          + rewrite -(app_nil_l [(ppId, [])]) -(app_nil_l [[]]). eapply interp_omo_snoc. split_and!; try done.
            * rewrite lookup_app_1_eq. done.
            * apply interp_omo_nil.
            * eapply stack_step_Pop; try done. set_solver-.
          + intros. destruct i; [|done]. inversion H0. subst st2. rewrite Nat.add_0_r Hst in H. inversion H. done.
        - iDestruct ("IH" with "M●3") as %(stnew' & IH1 & IH2).
          destruct (le_lt_dec (length (drop (gen + 1) omo3')) len) as [LE'|LT'].
          { rewrite take_ge in IH1; [|done]. do 2 (rewrite take_ge; [|lia]). iExists stnew'. done. }
          have [ees Hlast] : is_Some ((drop (gen + 1) omo3') !! len) by rewrite lookup_lt_is_Some.
          destruct ees as [e es]. rewrite (take_S_r _ _ (e, es)); [|done]. rewrite lookup_drop in Hlast.
          specialize (omo_gen_info _ _ _ _ _ _ OMO_GOOD3' Hlast) as (eV & eeVs & st' & EID_MATCH & EEVS_VALID & E3e & Lookup_stlist3' & Interp & ES).

          apply interp_omo_length in Hgengood as EQlenstnew. rewrite /= drop_length in EQlenstnew.
          have Lookup_stnew : stnew !! (len + 1)%nat = Some st'.
          { have EQ : length (take (genzfl3 + 1) stlist3) = gen.
            { rewrite take_length -EQlenST3 Nat.min_l; [lia|]. apply lookup_lt_Some in Hgenzfl3. rewrite -omo_write_op_length in Hgenzfl3. lia. }
            rewrite lookup_app_r in Lookup_stlist3'; [|lia]. rewrite EQ in Lookup_stlist3'.
            replace (gen + 1 + len - gen) with (len + 1) in Lookup_stlist3' by lia. done. }
          have [st3 Lookup_stlist3] : is_Some (stlist3 !! (genzfl3 + (len + 1))).
          { rewrite lookup_lt_is_Some. apply lookup_lt_Some in Lookup_stnew. apply lookup_lt_Some in Hgenzfl3. rewrite -omo_write_op_length in Hgenzfl3.
            replace (S (length omo3 - (genzfl3 + 1))) with (length omo3 - genzfl3) in EQlenstnew by lia.
            rewrite -EQlenstnew in Lookup_stnew. lia. }
          eapply Hstnew in Lookup_stlist3 as EQst'; [|done].

          destruct es; last first.
          { rewrite Forall_cons in ES. destruct ES as [(?&?&?&?) _].
            inversion H0; try done; subst st'; try (apply (f_equal length) in H5; rewrite cons_length in H5);
            try (apply (f_equal length) in H4; rewrite app_length /= in H4); lia. }

          have [stp Hstp] : is_Some (stlist3' !! (gen + len)).
          { rewrite lookup_lt_is_Some. apply lookup_lt_Some in Lookup_stlist3'. lia. }
          have STEP' : step e eV stp st'.
          { eapply omo_write_op_step; try done; replace (gen + len + 1) with (gen + 1 + len) by lia; try done.
            rewrite list_lookup_omo_destruct in Hlast. by destruct Hlast as [? _]. }

          apply interp_omo_length in IH1 as EQlen. apply lookup_lt_Some in Hlast as LTlen.
          rewrite /= take_length drop_length Nat.min_l in EQlen; [|lia].
          have [stp' Hstp'] : is_Some (stnew' !! len) by rewrite lookup_lt_is_Some; lia.
          have [stp'' Hstp''] : is_Some (stlist3 !! (genzfl3 + len)).
          { rewrite lookup_lt_is_Some -EQlenST3. apply lookup_lt_Some in Hstp.
            rewrite -EQlenST3' in Hstp. subst gen omo3'. rewrite omo_insert_w_length in Hstp. lia. }
          eapply IH2 in Hstp' as EQstp'; [|done]. subst stp''.
          have Hstp''' : stnew !! len = Some stp.
          { have EQ : length (take (genzfl3 + 1) stlist3) = gen.
            { rewrite take_length Nat.min_l; [done|]. rewrite -EQlenST3. apply lookup_lt_Some in Hgenzfl3. rewrite -omo_write_op_length in Hgenzfl3. lia. }
            rewrite lookup_app_r in Hstp; [|lia]. rewrite EQ in Hstp. replace (gen + len - gen) with len in Hstp by lia. done. }
          eapply Hstnew in Hstp'''; [|done]. subst stp st'.
          replace ((ppId, []) :: take len (drop (gen + 1)%nat omo3') ++ [(e, [])]) with
              (((ppId, []) :: take len (drop (gen + 1)%nat omo3')) ++ [(e, [])]); [|by simplify_list_eq].

          inversion STEP'.
          + replace ((e, v, eV.(sync), eV.(eview)) :: stp' ++ [(psId, v3, V3', M3')])
            with (((e, v, eV.(sync), eV.(eview)) :: stp') ++ [(psId, v3, V3', M3')]) in H3; [|by simplify_list_eq].
            apply app_inj_2 in H3 as [H3 _]; [|done]. iExists (stnew' ++ [(e, v, eV.(sync), eV.(eview)) :: stp']).
            iPureIntro. split.
            * eapply interp_omo_snoc. split_and!; try done.
              -- rewrite lookup_app_1_ne; [done|]. apply lookup_lt_Some in E3e. subst E3'. lia.
              -- rewrite last_cons last_lookup -EQlen. replace (Init.Nat.pred (S len)) with len by lia. rewrite Hstp'. done.
              -- eapply stack_step_Push; try done.
            * intros. destruct (decide (i = length stnew')) as [->|NEQ].
              -- rewrite lookup_app_1_eq in H4. inversion H4. subst st2. rewrite -EQlen in H2.
                 replace (genzfl3 + S len) with (genzfl3 + (len + 1)) in H2 by lia. rewrite Lookup_stlist3 in H2. inversion H2. rewrite -H6 -H3. done.
              -- eapply IH2; try done. by rewrite lookup_app_1_ne in H4.
          + rewrite H1 in H2. have EQ : (u, v, V, lV) :: st3 ++ [(psId, v3, V3', M3')] = ((u, v, V, lV) :: st3) ++ [(psId, v3, V3', M3')] by simplify_list_eq.
            rewrite EQ in H2. apply app_inj_2 in H2 as [H2 _]; [|done]. clear EQ H1.
            iExists (stnew' ++ [st3]). iPureIntro. split.
            * eapply interp_omo_snoc. split_and!; try done.
              -- rewrite lookup_app_1_ne; [done|]. apply lookup_lt_Some in E3e. subst E3'. lia.
              -- rewrite last_cons last_lookup -EQlen. replace (Init.Nat.pred (S len)) with len by lia. rewrite Hstp'. done.
              -- subst stp'. eapply stack_step_Pop; try done.
            * intros. destruct (decide (i = length stnew')) as [->|NEQ].
              -- rewrite lookup_app_1_eq in H3. inversion H3. subst st2. rewrite -EQlen in H1.
                 replace (genzfl3 + S len) with (genzfl3 + (len + 1)) in H1 by lia. rewrite Lookup_stlist3 in H1. inversion H1. done.
              -- eapply IH2; try done. by rewrite lookup_app_1_ne in H3.
          + apply (f_equal length) in H2. rewrite app_length /= in H2. lia.
          + apply (f_equal length) in H2. rewrite app_length /= in H2. lia. }

      specialize (Hgengood' (length (drop (gen + 1) omo3'))) as (stnew' & Hgengood' & Hstnew').
      rewrite take_ge in Hgengood'; [|done].
      iDestruct (OmoUB_singleton with "psId✓eVpush") as "#MAXpsId".
      iDestruct (OmoUB_into_gen _ _ _ _ _ _ _ _ (wr_event gen) with "M●3 MAXpsId") as %MAXpsId.
      { subst omo3'. rewrite lookup_omo_wr_event omo_insert_w_write_op.
        have EQ : length (take (genzfl3 + 1) (omo_write_op omo3)) = gen.
        { rewrite take_length Nat.min_l; [done|]. apply lookup_lt_Some in Hgenzfl3. lia. }
        rewrite lookup_app_r; [|lia]. rewrite EQ. replace (gen - gen) with 0 by lia. done. }

      iMod "AU2" as (?) "[M●3' [_ Commit]]". iDestruct "M●3'" as (???) ">M●3'".
      iDestruct (OmoAuth_agree with "M●3 M●3'") as %(<- & <- & <- & <-). iCombine "M●3 M●3'" as "M●3".
      iMod (OmoAuth_insert with "M●3 ⊒M3'@V3' WCOMMIT2 []") as (γs3'') "(M●3 & #⊒M3''@V3' & _ & #ppId✓eVpop & _)".
      { iPureIntro. split_and!; try done; try (by subst eVpop).
        - subst stlist3'.
          have EQ : length (take (genzfl3 + 1) stlist3) = gen.
          { rewrite take_length Nat.min_l; [done|]. apply lookup_lt_Some in Hgenzfl3. rewrite -EQlenST3 omo_write_op_length. lia. }
          rewrite lookup_app_r; [|lia]. rewrite EQ. replace (gen - gen) with 0 by lia.
          rewrite -(Nat.add_0_r genzfl3) in Hst.
          have [st' Hst'] : is_Some (stnew !! 0).
          { rewrite lookup_lt_is_Some. apply interp_omo_length in Hgengood. destruct stnew; simpl; try lia; try done. }
          eapply Hstnew in Hst; [|done]. subst st'. rewrite Hst'. clear. by simplify_list_eq.
        - simpl in *. replace ({[length E3]} ∪ M3') with ({[length E3]} ∪ M3) in MAXpsId by set_solver-. done. }
      iDestruct (OmoHbToken_finish with "M●3") as "[M●3 M●3']".
      iDestruct (OmoSnapHistory_get with "M●3") as "#E◯3''".

      iMod ("Commit" $! v3 V3' E3'' (Pop v3) M3'' with "[M●3']") as "HΦ".
      { iFrame "⊒V3'". iSplitL; [repeat iExists _;iFrame|]. rewrite decide_False; [|lia]. rewrite decide_False; [|simpl in *;lia]. iSplit; last iSplit; try done.
        - iFrame "SInv". repeat iExists _. iFrame "HM E◯3'' ⊒M3''@V3' ⊒Mt@V3' ⊒Mx@V3' e0✓eV0 ⊒eV0@V3'".
        - iPureIntro. split_and!; try done. set_solver-. }

      have HppId : lookup_omo (omo_insert_w omo3' (gen + 1) ppId []) (wr_event (genzfl3 + 2)) = Some ppId.
      { rewrite lookup_omo_wr_event omo_insert_w_write_op.
        have EQ : length (take (gen + 1) (omo_write_op omo3')) = (genzfl3 + 2).
        { rewrite take_length Nat.min_l; [lia|]. rewrite omo_insert_w_write_op !app_length /= take_length Nat.min_l; [lia|].
          apply lookup_lt_Some in Hgenzfl3. lia. }
        rewrite lookup_app_r; [|lia]. rewrite EQ. replace (genzfl3 + 2 - (genzfl3 + 2)) with 0 by lia. done. }

      iDestruct (OmoLe_get _ _ _ _ _ _ (wr_event genzfl3) (wr_event (genzfl3 + 2)) with "M●3") as "#ezlf3≤ppId"; [|done|simpl;lia|].
      { rewrite lookup_omo_wr_event omo_insert_w_write_op lookup_app_l.
        - rewrite lookup_take; [|lia]. rewrite omo_insert_w_write_op. rewrite lookup_app_l.
          + rewrite lookup_take; [|lia]. done.
          + rewrite take_length. apply lookup_lt_Some in Hgenzfl3. lia.
        - rewrite take_length omo_insert_w_write_op !app_length /= take_length.
          apply lookup_lt_Some in Hgenzfl3. lia. }

      iDestruct (OmoLe_get _ _ _ _ _ _ (wr_event (genzfl3 + 1)) (wr_event (genzfl3 + 2)) with "M●3") as "#psId≤ppId"; [|done|simpl;lia|].
      { rewrite lookup_omo_wr_event omo_insert_w_write_op lookup_app_l.
        - rewrite lookup_take; [|lia]. rewrite omo_insert_w_write_op.
          have EQ : length (take (genzfl3 + 1) (omo_write_op omo3)) = genzfl3 + 1.
          { rewrite take_length Nat.min_l; [done|]. apply lookup_lt_Some in Hgenzfl3. lia. }
          rewrite lookup_app_r; [|lia]. rewrite EQ. replace (genzfl3 + 1 - (genzfl3 + 1)) with 0 by lia. done.
        - rewrite take_length omo_insert_w_write_op !app_length /= take_length. apply lookup_lt_Some in Hgenzfl3. lia. }

      set stlist3'' := take (gen + 1) stlist3' ++ stnew'.
      have STemp : stlist3'' !! (genzfl3 + 2)%nat = Some [].
      { have EQ : length (take (gen + 1) stlist3') = genzfl3 + 2.
        { rewrite take_length Nat.min_l; [lia|]. rewrite -EQlenST3' omo_insert_w_length. apply lookup_lt_Some in Hgenzfl3.
          rewrite -omo_write_op_length in Hgenzfl3. lia. }
        rewrite lookup_app_r; [|by rewrite EQ; lia]. rewrite EQ. replace (genzfl3 + 2 - (genzfl3 + 2)) with 0 by lia.
        have [st' Hst'] : is_Some (stnew' !! 0).
        { rewrite lookup_lt_is_Some. apply interp_omo_length in Hgengood'. destruct stnew'; simpl; try lia; try done. }
        rewrite -(Nat.add_0_r genzfl3) in Hst. eapply Hstnew' in Hst; [|done]. subst st'. done. }
      iDestruct (OmoSnap_get _ _ _ _ _ _ _ (wr_event (genzfl3 + 2)) (genzfl3 + 2) with "M●3") as "#ppId↪emp"; [done|done|done|].

      iModIntro. iExists E3'',_,_,γs3'',ppId. iFrame. iSplit; last iSplit.
      + iFrame "ppId↪emp". subst E3'' E3'. rewrite !big_sepL_snoc. iSplit; [iSplit|].
        * iApply big_sepL_forall. iIntros "%e %eV %E3e". iDestruct (big_sepL_lookup with "AllEvents3") as "[CASE|CASE]"; [done|..].
          -- iLeft. iApply OmoLe_trans; try done.
          -- iRight. done.
        * iLeft. done.
        * iLeft. iApply OmoLe_get_from_Eq. iApply (OmoEq_get_from_Einfo with "ppId✓eVpop").
      + iDestruct "LASTst3" as (??) "[[%LASTstf %LASTtstf] BIG]".
        have EQ : last stlist3'' = Some stf.
        { rewrite last_app last_lookup. apply interp_omo_length in Hgengood' as EQlen.
          rewrite /= drop_length omo_insert_w_length in EQlen.
          have EQ : Init.Nat.pred (length stnew') = length omo3 - gen by lia. rewrite EQ.
          rewrite last_lookup in LASTstf. replace (Init.Nat.pred (length stlist3)) with (length omo3 - 1) in LASTstf by lia.
          have EQ' : length omo3 - 1 = genzfl3 + (length omo3 - gen).
          { have ? : gen ≤ length omo3; [|lia]. apply lookup_lt_Some in Hgenzfl3. rewrite -omo_write_op_length in Hgenzfl3. lia. }
          rewrite EQ' in LASTstf.
          have [st' Hst'] : is_Some (stnew' !! (length omo3 - gen)) by rewrite lookup_lt_is_Some -EQlen; lia.
          eapply Hstnew' in LASTstf; [|done]. subst stf. by rewrite Hst'. }
        iExists stf,tstf. rewrite EQ. iFrame "BIG". done.
      + iPureIntro. unfold last_empty in *. exists (genzfl3 + 2). split; [done|]. intros. eapply (LASTemp3 (i - 2)); [|lia].
        have EQlen1 : length (take (gen + 1) stlist3') = genzfl3 + 2.
        { rewrite take_length Nat.min_l; [lia|]. rewrite app_length take_length -EQlenST3 omo_write_op_length Nat.min_l.
          - apply interp_omo_length in Hgengood. rewrite -Hgengood /=. lia.
          - apply lookup_lt_Some in Hgenzfl3. lia. }
        rewrite lookup_app_r in H; [|rewrite EQlen1;lia]. rewrite EQlen1 in H.
        have [st' Hst'] : is_Some (stlist3 !! (genzfl3 + (i - (genzfl3 + 2)))).
        { rewrite lookup_lt_is_Some. apply lookup_lt_Some in H. apply interp_omo_length in Hgengood'. rewrite -Hgengood' /= in H.
          rewrite -EQlenST3. rewrite drop_length omo_insert_w_length in H. lia. }
        eapply Hstnew' in H; [|done]. subst st'. replace (genzfl3 + (i - (genzfl3 + 2))) with (i - 2) in Hst' by lia. done.
    - (* If current observation is later than [genzfl3], then commit Push and Pop consecutively at the end of generation *)
      iDestruct "LASTst3" as (??) "[[%LASTstf %LASTtstf] BIG]".
      set nstf := (psId, v3, V3', M3') :: stf.
      iDestruct (OmoLt_get _ _ _ _ _ _ (wr_event genzfl3) eidx3 with "M●3") as "#ezfl3<e3"; [by rewrite lookup_omo_wr_event|done|done|].
      iDestruct (OmoAuth_OmoLt with "M●3 ezfl3<e3") as %[_ [eV3 HeV3]].
      iDestruct (OmoEinfo_get with "M●3") as "#e3✓eV3"; [done|].
      iDestruct (big_sepL_lookup with "AllEvents3") as "[CASE|CASE]"; [exact HeV3|..].
      { by iDestruct (OmoLe_Lt_contra with "CASE ezfl3<e3") as %?. }
      iDestruct "CASE" as (e3' te3') "(ezfs3<e3' & e3'≤e3 & e3⊒e3' & e3'⊒te3' & e3'↦te3' & MONO✓e3')".

      (* Commit Push *)
      iMod "AU1" as (?) "[M●3' [_ Commit]]". iDestruct "M●3'" as (???) ">M●3'".
      iDestruct (OmoAuth_agree with "M●3 M●3'") as %(<- & <- & <- & <-). iCombine "M●3 M●3'" as "M●3".
      iMod (OmoAuth_insert_last with "M●3 ⊒M3@V3' WCOMMIT1 []") as "(M●3 & #⊒M3'@V3' & _ & #psId✓eVpush & _)".
      { have ? : step psId eVpush stf nstf; [|done]. eapply stack_step_Push; try done. set_solver-. }
      iMod (OmoHb_new_2 with "M●3 [] psId✓eVpush") as "[M●3 #psId⊒e3]". { exact e3IN. } { done. }
      iMod (OmoHb_new_3 with "M●3 psId⊒e3 e3⊒e3'") as "[M●3 #psId⊒e3']".
      iDestruct (OmoHbToken_finish with "M●3") as "[M●3 M●3']".
      iDestruct (OmoSnapHistory_get with "M●3") as "#E◯3'".
      iDestruct (OmoLt_get_append_w with "M●3 e3✓eV3") as "#e3<psId"; [by apply lookup_lt_Some in HeV3;lia|].

      iMod ("Commit" $! true V3' E3' (Push v3) M3' with "[M●3']") as "HQ".
      { iFrame "⊒V3'". iSplitL; [repeat iExists _; iFrame|]. iSplit.
        - iPureIntro. split_and!; try done. set_solver-.
        - repeat iExists _. iFrame "HM E◯3' ⊒M3'@V3' ⊒Mt@V3' ⊒Mx@V3' e0✓eV0 ⊒eV0@V3'". }

      (* Commit Pop *)
      iMod "AU2" as (?) "[M●3' [_ Commit]]". iDestruct "M●3'" as (???) ">M●3'".
      iDestruct (OmoAuth_agree with "M●3 M●3'") as %(<- & <- & <- & <-). iCombine "M●3 M●3'" as "M●3".
      iMod (OmoAuth_insert_last with "M●3 ⊒M3'@V3' WCOMMIT2 []") as "(M●3 & #⊒M3''@V3' & _ & #ppId✓eVpop & _)".
      { have ? : step ppId eVpop nstf stf by eapply stack_step_Pop; try set_solver-.
        iPureIntro. split_and!; try done. rewrite last_app. done. }
      iMod (OmoHb_new_2 with "M●3 [] ppId✓eVpop") as "[M●3 #ppId⊒e3]". { exact e3IN. } { done. }
      iMod (OmoHb_new_3 with "M●3 ppId⊒e3 e3⊒e3'") as "[M●3 #ppId⊒e3']".
      iDestruct (OmoHbToken_finish with "M●3") as "[M●3 M●3']".
      iDestruct (OmoSnapHistory_get with "M●3") as "#E◯3''".
      iDestruct (OmoLt_get_append_w with "M●3 e3✓eV3") as "#e3<ppId"; [by rewrite app_length /=;apply lookup_lt_Some in HeV3;lia|].

      iMod ("Commit" $! v3 V3' E3'' (Pop v3) M3'' with "[M●3']") as "HΦ".
      { iFrame "⊒V3'". rewrite decide_False; [|lia]. rewrite decide_False; [|simpl in *;lia]. iSplitL; [repeat iExists _;iFrame|]. iSplit; last iSplit; [|done|].
        - iFrame "SInv". repeat iExists _. iFrame "HM E◯3'' ⊒M3''@V3' ⊒Mt@V3' ⊒Mx@V3' e0✓eV0 ⊒eV0@V3'".
        - iPureIntro. split_and!; try done. set_solver-. }

      iModIntro. do 4 iExists _. iExists ezfl3. iFrame. iSplit; last iSplit.
      + iFrame "ezfl3↪emp". rewrite !big_sepL_snoc. iFrame "AllEvents3". iSplit.
        * iRight. iExists e3',te3'. iFrame "ezfs3<e3' e3'↦te3' e3'⊒te3' MONO✓e3' psId⊒e3'".
          iApply OmoLe_get_from_Lt. iApply OmoLe_Lt_trans; try done.
        * iRight. iExists e3',te3'. iFrame "ezfs3<e3' e3'↦te3' e3'⊒te3' MONO✓e3' ppId⊒e3'".
          iApply OmoLe_get_from_Lt. iApply OmoLe_Lt_trans; try done.
      + iExists stf,tstf. iFrame "BIG". iPureIntro. split; [|done]. rewrite last_app /=. done.
      + iPureIntro. exists genzfl3. split.
        * rewrite !omo_append_w_write_op lookup_app_l; last first.
          { rewrite app_length /=. apply lookup_lt_Some in Hgenzfl3. lia. }
          rewrite lookup_app_l; [done|]. apply lookup_lt_Some in Hgenzfl3. lia.
        * intros. destruct (decide (i = length (stlist3 ++ [nstf]))) as [->|NEQ].
          -- rewrite lookup_app_1_eq in H. inversion H. subst st. rewrite last_lookup in LASTstf. eapply LASTemp3; [done|].
             rewrite -EQlenST3. apply lookup_omo_lt_Some in Heidx3. lia.
          -- rewrite lookup_app_1_ne in H; [|done]. destruct (decide (i = length stlist3)) as [->|NEQ'].
             ++ rewrite lookup_app_1_eq in H. inversion H. subst nstf. done.
             ++ rewrite lookup_app_1_ne in H; [|done]. eapply LASTemp3; try done. }

  rewrite !view_at_objective_iff. iModIntro. iSplitR "HΦ".
  { iModIntro. repeat iExists _. iFrame. iFrame "HM LASTst3' AllEvents3'". iSplitL; last iSplit.
    - iExists _,_. iSplitR; [by rewrite Hxstlist3' last_app -Hxst3|]. iFrame "BIGxstl3". rewrite big_sepM_insert; [|done].
      iFrame "BIGxstr3". iExists γi,γpt,γpf,γu,V',(Q true). iFrame "KEY Hγpt". iSplit; [done|]. iLeft. simpl. done.
    - iExists tezf3,tgenzf3. iFrame "ezfs3↦tezf3 MONO✓ezfs3". done.
    - iPureIntro. split; [|done]. unfold hmap_valid. intros. apply VALhmap3 in H. subst Ex3'. rewrite app_length /=. lia. }

  replace (V' ⊔ V3) with V3 by solve_lat.
  iDestruct (view_at_elim with "⊒V3 HΦ") as "HΦ".

  iIntros "_". wp_pures. by iApply "HΦ".
Qed.

Lemma pop_spec :
  spec_history.pop_spec' (pop try_pop' take_offer) EStackLocal EStackInv.
Proof.
  intros N DISJ s tid γg E0 M V0. iIntros "#⊒V0 #EStackLocal" (Φ) "AU".

  iLöb as "IH" forall "#". wp_rec. awp_apply (try_pop_spec with "⊒V0 EStackLocal"); [done|].
  iApply (aacc_aupd with "AU"); [done|].
  iIntros (E) "M●". iAaccIntro with "M●"; first by eauto with iFrame.

  iIntros (v1 V1 E1 pp M1) "(M● & #⊒V1 & #⊒M1@V1 & %LeV0V1 & %CASE)".
  iModIntro. destruct (decide (v1 = (-1)%Z)) as [->|NEv1].
  - iLeft. destruct CASE as [-> ->]. iFrame "M●". iIntros "AU !> _". wp_let. wp_op. wp_if. iApply ("IH" with "AU"); try done.
  - iRight. destruct CASE as (EQE1 & SubMM1 & CASE). iExists v1,V1,E1,pp,M1. iFrame "M● ⊒V1 ⊒M1@V1". iSplit; [done|].
    iIntros "HΦ !> _". wp_pures. rewrite bool_decide_false; [|done]. wp_pures. by iApply "HΦ".
Qed.

End Elimstack.

Definition elim_stack_impl `{!noprolG Σ, !atomicG Σ, !elimG Σ} (ts : stack_spec Σ) (xc : xchg_spec Σ)
  : spec_history.stack_spec Σ := {|
    spec_history.StackInv_Linearizable := EStackInv_Linearizable_instance ;
    spec_history.StackInv_history_wf := EStackInv_history_wf_instance;
    spec_history.StackInv_StackLocal := EStackInv_StackLocal_instance ts xc;
    spec_history.StackLocal_lookup := EStackLocal_lookup_instance ts xc;
    spec_history.new_stack_spec := new_stack_spec ts xc;
    spec_history.try_push_spec := try_push_spec ts xc;
    spec_history.push_spec := push_spec ts xc;
    spec_history.try_pop_spec := try_pop_spec ts xc;
    spec_history.pop_spec := pop_spec ts xc;
  |}.
