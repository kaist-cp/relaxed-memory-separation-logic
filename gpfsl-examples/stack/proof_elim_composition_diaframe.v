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
From gpfsl.examples.stack Require Import spec_elim_composition_diaframe spec_treiber_composition_diaframe code_elim.
From gpfsl.examples.exchanger Require Import spec_composition_diaframe.

From gpfsl.diaframe Require Import vprop_weakestpre spec_notation
 vprop_weakestpre_logatom atom_spec_notation proof_automation omo_specs omo_hints ghost_map_hints.
From diaframe Require Import proofmode_base lib.except_zero own_hints steps.verify_tac util_instances.
From diaframe.symb_exec Require Import weakestpre_logatom.

 From Hammer Require Import Tactics.
Require Import iris.prelude.options.

Class elimG Σ := ElimG {
  elim_emoGeneralG :> omoGeneralG Σ;
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
  (Et : history sevent_hist) (Ex : history xchg_event).

Hypothesis (ts : stack_dspec Σ).
Hypothesis (xc : xchg_dspec Σ).

Definition estackN (N : namespace) := N .@ "estack".
Definition tstackN (N : namespace) := N .@ "tstack".
Definition xchgN (N : namespace) := N .@ "xchg".
Definition helpN (N : namespace) := N .@ "helping".


Notation new_stack' := (spec_treiber_composition_diaframe.new_stack ts).
Notation try_push' := (spec_treiber_composition_diaframe.try_push ts).
Notation try_pop' := (spec_treiber_composition_diaframe.try_pop ts).
Notation new_exchanger := (spec_composition_diaframe.new_exchanger xc).
Notation new_offer := (spec_composition_diaframe.new_offer xc).
Notation check_offer := (spec_composition_diaframe.check_offer xc).
Notation take_offer := (spec_composition_diaframe.take_offer xc).

Definition field_info γg (s lt lx : loc) : vProp :=
  ∃ (q1 q2 : Qp) et Vsync M,
    OmoEinfo γg 0%nat (@mkOmoEvent sevent_hist et Vsync M) ∗
    @{Vsync} (s ↦{q1} #lt) ∗
    @{Vsync} ((s >> 1) ↦{q2} #lx).

Definition last_state γg γgt (stlist tstlist : list stack_state) : vProp :=
  ∃ stf tstf,
    MatchValue (Some stf) (last stlist) ∗
    MatchValue (Some tstf) (last tstlist) ∗
    [∗ list] st; tst ∈ stf; tstf,
      ∃ st_eid st_val st_V st_M tst_eid tst_val tst_V tst_M
          eV_et eV_sync eV_M teV_et teV_sync teV_M,
        ⌜ st = (st_eid, st_val, st_V, st_M) ⌝ ∗
        ⌜ tst = (tst_eid, tst_val, tst_V, tst_M) ⌝ ∗
        OmoEinfo γg st_eid (@mkOmoEvent sevent_hist eV_et eV_sync eV_M) ∗
        OmoEinfo γgt tst_eid (@mkOmoEvent sevent_hist teV_et teV_sync teV_M) ∗
        ⌜ st_val = tst_val ∧ st_V = tst_V
        ∧ eV_sync = st_V ∧ teV_sync = tst_V ∧ eV_M = st_M ⌝.

Definition EStackInv γg γs (s : loc) (E : history sevent_hist) omo stlist : vProp :=
  try_update_OmoAuth_to γg E omo stlist ∗ ∃ p : (), ask_for p ∗ OmoAuth γg γs (1/2)%Qp E omo stlist _.

Definition EStackLocal_inner N γg (s : loc) M : vProp :=
  ∃ γgt γst γgx γsx γm γh (lt lx : loc) Mt Mx eV0_et eV0_sync eV0_M,
    meta s nroot (γgt, γgx, γst, γsx, γm, γh, lt, lx) ∗
    OmoEview γg M ∗
    ts.(StackLocal) (tstackN N) γgt lt Mt ∗
    xc.(ExchangerLocal) (xchgN N) γgx lx Mx ∗
    OmoEinfo γg 0%nat (@mkOmoEvent sevent_hist eV0_et eV0_sync eV0_M)
    ∗ ⊒(eV0_sync).

Definition atomic_update_push (N : namespace) γg s (v : Z) (V : view) (M : eView) (Q : bool → vProp) : vProp :=
  atomic_update (⊤ ∖ ↑N) (↑histN)
    (tele_app (TT:= [tele _ _ _ _]) (λ γs E omo stlist, ▷ EStackInv γg γs s E omo stlist)%I)
    (tele_app (TT:= [tele _ _ _ _])
      (λ γs E omo stlist, tele_app (TT:= [tele _])
        (λ (b: bool) ,
          (* PUBLIC POST *)
          ∃V', ⊒V' ∗
          if b then (
            (* successful case *)
            ∃ γs' M' omo' stlist' gen,
            let E' := E ++ [mkOmoEvent (Push v) V' M'] in
            ▷ EStackInv γg γs' s E' omo' stlist' ∗ @{V'} EStackLocal_inner N γg s M' ∗
            ⌜ omo' = omo_insert_w omo gen (length E) [] ⌝ ∗
            OmoTokenW γg (length E) ∗
            OmoUB γg M (length E) ∗
            ⌜ V ⊑ V' ∧ M ⊆ M' ⌝
          ) else (
            (* FAIL_RACE case *)
            ▷ EStackInv γg γs s E omo stlist ∗ @{V'} EStackLocal_inner N γg s M
          ))%I))
    (tele_app (TT:= [tele _ _ _ _])
      (λ γs E omo stlist, tele_app (TT:= [tele _ ])
        (λ b, Q b)%I)).

Definition last_state_xchg N γg s γgx γh (xstlist : list xchg_state) : vProp :=
  ∃ xstl xstr, MatchValue (Some (xstl, xstr)) (last xstlist) ∗
    ([∗ map] xe↦xinfo ∈ xstl,
      ∃ (γi : positive) (γpt γpf γu : gname) (Vi : view) M Q xinfo_val xinfo_V xinfo_M,
        ⌜ xinfo = (xinfo_val, xinfo_V, xinfo_M) ⌝ ∗
        ⎡xe ↪[γh]□ (γi, xinfo_V)⎤ ∗ ⌜ γi = encode (γpt, γpf, γu) ⌝ ∗
        @{xinfo_V} (atomic_update_push N γg s xinfo.1.1 Vi M Q ∗ EStackLocal_inner N γg s M) ∗
        ⌜ Vi ⊑ xinfo_V ∧ (0 < xinfo_val)%Z ⌝ ∗
        OmoTokenW γgx xe ∗
        saved_vProp_own γpt DfracDiscarded (Q true) ∗ saved_vProp_own γpf DfracDiscarded (Q false)
        ) ∗
    ([∗ map] xe↦xinfo ∈ xstr,
      ∃ (cs : bool) (γi : positive) ( γpt γpf γu : gname) (Vb : view) P xinfo_eid xinfo_V xinfo_M ,
        ⌜ xinfo = (xinfo_eid, 0%Z, xinfo_V, xinfo_M) ⌝ ∗
        ⎡xe ↪[γh]□ (γi,Vb)⎤ ∗
        ⌜ γi = encode (γpt,γpf,γu) ⌝ ∗
        saved_vProp_own γpt DfracDiscarded P ∗
        (if cs then @{Vb ⊔ xinfo_V} P else UTok γu)).

#[global] Instance last_state_xchg_Objective N γg s γgx γh xstlist : Objective (last_state_xchg N γg s γgx γh xstlist).
Proof.
  assert (∀ {I : biIndex} {PROP : bi} (P Q : monPred I PROP) (b : bool) `{!Objective P, !Objective Q}, Objective (if (b) then P else Q)).
  { intros. by destruct b. } tc_solve.
Qed.

Definition AllEvents γg γs γgt γgx γm (E : history sevent_hist) ezfs ezfl : vProp :=
  OmoSnap γg γs ezfl [] ∗
  [∗ list] e↦eV ∈ E,
    ∃ (cs : bool),
    if cs then OmoLe γg e ezfl else
    (∃ e' te', OmoHb γg γg e e' ∗ OmoLt γg ezfs e' ∗ OmoLe γg e' e ∗
     CWMonoValid γm e' ∗ OmoCW γg γgt e' te' ∗ OmoHb γg γgt e' te').


#[global] Instance AllEvents_Objective γg γs γgt γgx γm E ezfs ezfl : Objective (AllEvents γg γs γgt γgx γm E ezfs ezfl).
Proof.
  assert (∀ {I : biIndex} {PROP : bi} (P Q : monPred I PROP) (b : bool) `{!Objective P, !Objective Q}, Objective (if (b) then P else Q)).
  { intros. by destruct b. } tc_solve.
Qed.

#[global] Instance if_bool_Timeless {I : biIndex} {PROP : bi} (P Q : monPred I PROP) (b : bool) `{!Timeless P, !Timeless Q} :
   Timeless (if (b) then P else Q).
Proof. destruct b; tc_solve. Qed.

Definition last_empty_t γg γgt γm ezfs (tes : list event_id) (tstlist : list stack_state) : vProp :=
  ∃ tezf tgenzf,
    OmoCW γg γgt ezfs tezf ∗ CWMonoValid γm ezfs ∗
    MatchValue (Some tezf) (tes !! tgenzf) ∗
    MatchValue (Some []) (tstlist !! tgenzf) ∗
    ⌜ (∀ tgen' st', tstlist !! tgen' = Some st' → (tgenzf < tgen')%nat → st' ≠ []) ⌝.

Definition last_empty ezfl (es : list event_id) (stlist : list stack_state) : vProp :=
  ∃ genzfl,
    MatchValue (Some ezfl) (es !! genzfl) ∗ ⌜ (∀ i st, stlist !! i = Some st → (genzfl < i)%nat → st ≠ []) ⌝.

Definition hmap_valid Ex (hmap : gmap event_id (gname * view)) : Prop :=
  ∀ e, is_Some (hmap !! e) → e < length Ex.

Definition EStackInternalInv (N : namespace) γg s E : vProp :=
  ∃ (γs γgt γst γgx γsx γm γh : gname) (lt lx : loc) Et Ex omo omot omox stlist tstlist xstlist Mono hmap ezfs ezfl oezfl,
    meta s nroot (γgt,γgx,γst,γsx,γm,γh,lt,lx) ∗

    Peek (OmoAuth γg γs (1/2)%Qp E omo stlist _) ∗
    field_info γg s lt lx ∗
    ExchangerInv xc γgx γsx lx Ex omox xstlist ∗
    Peek (StackInv ts γgt γst lt Et omot tstlist) ∗

    ask_optional oezfl ezfl ∗
    AllEvents γg γs γgt γgx γm E ezfs ezfl ∗
    last_state_xchg N γg s γgx γh xstlist ∗
    ⎡ghost_map_auth γh 1 hmap⎤ ∗
    last_state γg γgt stlist tstlist ∗
    last_empty_t γg γgt γm ezfs (omo_write_op omot) tstlist ∗
    CWMono γg γgt γm Mono ∗

    ⌜ hmap_valid Ex hmap ⌝ ∗
    last_empty ezfl (omo_write_op omo) stlist ∗
    StackInv ts γgt γst lt Et omot tstlist ∗
    OmoAuth γg γs (1/2)%Qp E omo stlist _ .

Definition InternalInv_inner N γg s : vProp := ∃ E, EStackInternalInv N γg s E ∗ emp.

Definition InternInv N γg s := inv (estackN N) (InternalInv_inner N γg s).

Definition EStackLocal N γg s M : vProp :=
  EStackLocal_inner N γg s M ∗ InternInv N γg s.

#[global] Instance EStackLocal_Persistent N γg s M : Persistent (EStackLocal N γg s M) := _.

Lemma EStackInv_Linearizable_instance :
  ∀ γg γs s E omo stlist, EStackInv γg γs s E omo stlist ⊢ ⌜ Linearizability_omo E omo stlist ⌝.
Proof.
  iSteps. by iApply @OmoAuth_Linearizable.
Qed.

Lemma EStackInv_OmoAuth_acc_instance :
  ∀ γg γs s E omo stlist,
    EStackInv γg γs s E omo stlist
    ⊢ OmoAuth γg γs (1/2)%Qp E omo stlist _ ∗ (OmoAuth γg γs (1/2)%Qp E omo stlist _ -∗ EStackInv γg γs s E omo stlist).
Proof.
  iSteps. iExists (). iSteps.
Qed.

Lemma EStackLocal_OmoEview_instance :
  ∀ N γg s M, EStackLocal N γg s M ⊢ OmoEview γg M.
Proof. intros. iSteps. Qed.

Lemma EStackLocal_Eview_update_instance :
  ∀ N γg s M1 M2, EStackLocal N γg s M1 -∗ OmoEview γg M2 -∗ EStackLocal N γg s (M1 ∪ M2).
Proof. intros. iSteps. Qed.

Class ElimComponent `{!omoSpecificG Σ eventT absStateT} (A : vProp) (γe γs : gname) q (E : history eventT) (omo : omoT) (stlist : list absStateT) `{Interpretable eventT absStateT} :=
  access_master : A -∗ (OmoAuth γe γs q E omo stlist _ ∗ (OmoAuth γe γs q E omo stlist _ -∗ A)).

#[local] Instance StackInv_ElimComponent γe γs s E omo stlist : ElimComponent (StackInv ts γe γs s E omo stlist) γe γs 1 E omo stlist.
Proof. unfold ElimComponent. iIntros "SI". iDestruct (StackInv_OmoAuth_acc with "SI") as "$". Qed.

#[local] Instance ExchangerInv γe γs l Ex omo stlist : ElimComponent (ExchangerInv xc γe γs l Ex omo stlist) γe γs (1/2) Ex omo stlist.
Proof. unfold ElimComponent. iIntros "EI". iDestruct (ExchangerInv_OmoAuth_acc with "EI") as "$". Qed.

#[local] Instance mergable_consume_ElimComponent_access_master `{omoSpecificG Σ eventT absStateT} P γe γs q E omo stlist {Interp: Interpretable eventT absStateT} :
  ElimComponent P γe γs q E omo stlist →
  MergableConsume (P) true (λ p Pin Pout,
    TCAnd (TCEq Pin (ε₀)%I)
    (TCEq Pout (⌜ Linearizability_omo E omo stlist ⌝ ∗ OmoAuth γe γs q E omo stlist Interp ∗ (OmoAuth γe γs q E omo stlist Interp -∗ P))))%I | 500.
Proof.
  intros [acc] p Pin Pout [-> ->]. iIntros "[P _]".
  iDestruct (monPred_in_intro with "P") as (V) "[⊒V P]". rewrite acc.
  iDestruct (monPred_in_elim with "[$] P") as "[M● Close]".
  iDestruct (OmoAuth_wf with "M●") as "#[$ _]". iFrame.
Qed.

#[local] Instance mergable_consume_OmoAuth_appended_induce_step `{omoSpecificG Σ eventT absStateT} γe γs q E eV omo es' stlist st st' {Interp: Interpretable eventT absStateT} :
  let E' := E ++ [eV] in
  let omo' := omo_append_w omo (length E) es' in
  let stlist' := stlist ++ [st'] in
  MergableConsume (OmoAuth γe γs q E' omo' stlist' Interp) true (λ p Pin Pout,
    TCAnd (TCEq Pin (ε₀)) $
    TCAnd (FindEq (last stlist) (Some st)) $
    (* TODO: if there are any `evar`'s, then solvesepsidecondition doesn't work. *)
    TCAnd (TCIf (SolveSepSideCondition (omo.step (length E) eV st st')) False TCTrue) $
    TCAnd (SolveSepSideCondition (Linearizability_omo E omo stlist)) $
    (TCEq Pout (⌜ omo.step (length E) eV st st' ⌝ ∗  OmoAuth γe γs q E' omo' stlist' Interp)))%I | 300.
Proof.
  intros. subst E' omo' stlist'. intros p Pin Pout (-> & ? & _ & good & ->).
  unfold SolveSepSideCondition, FindEq in *. rewrite bi.intuitionistically_if_elim.
  eapply (omo_stlist_length) in good as lenEq.
  assert (length omo > 0). {  destruct omo, stlist; simpl in *; try done. lia. }
  iStep as "_ _ M●". iDestruct (OmoAuth_wf with "M●") as %[good' _].
  eapply (omo_write_op_step _ _ _ (length stlist - 1) (length E)) in good' as STEP; last first.
  { rewrite Nat.sub_add; [|lia]. rewrite lookup_app_1_eq //. }
  { apply lookup_app_l_Some. replace (length stlist - 1) with (Init.Nat.pred (length stlist)) by lia. rewrite -last_lookup. done. }
  { apply lookup_app_1_eq. }
  { rewrite Nat.sub_add; [|lia]. by rewrite -lenEq omo_rewrite_hints omo_write_op_length lookup_app_1_eq. } eauto.
Qed.


#[global] Instance new_stack_spec :
  spec_elim_composition_diaframe.new_stack_dspec' (new_estack new_stack' new_exchanger) EStackLocal EStackInv.
Proof using All.
  (* intros *)
  rewrite /spec_elim_composition_diaframe.new_stack_dspec'. iStep 7 as (tid N V0) "?".
  (* new *)
  iStep 8 as (s) "??? HM _".
  (* new_stack' *)
  iSteps. iExists (tstackN N). iStep 9 as (lt γgt γst ????) "????????".
  (* new_exchanger *)
  iSteps. iExists ((xchgN N)). iStep 9 as (lx γgx γsx ? V2 ??) "????????".
  (* prove postcondition *)
  iApply (bi.wand_elim_r (do_intro_view_forall)). iStepDebug. iStep as (V3 ?) "???". iIntros "_".
  set Minit : eView := {[0%nat]}.
  set eVinit := mkOmoEvent (stack_event_omo.Init) V3 Minit.
  set initst : stack_state := [].

  iMod (@OmoAuth_alloc _ _ _ _ _ (eVinit) initst γgt _ stack_interpretable with "[$]") as (γg γs) "H"; last iDecompose "H".
  { eapply stack_step_Init; try done. } { done. }
  iMod (ghost_map_alloc_empty) as (γh) "Hγh".
  iMod (CWMono_new γg γgt) as (γm) "MONO". rewrite !omo_rewrite_hints.
  iMod (meta_set _ _ (γgt,γgx,γst,γsx,γm,γh,lt,lx) nroot with "HM") as "#HM"; [done|]. iStep 2. iExists γg. iStep.
  rewrite try_update_OmoAuth_to_eq. iStep. iExists (). iSteps. iExists None. iStep.
  iExists _, true. iSplitR. { iApply OmoLe_get_from_Eq. iApply (@OmoEq_get_from_Einfo with "[$]"). }
  iStep. rewrite !big_sepM_empty. replace ([(@pair event_id (list event_id) (0) [])]) with (omo_append_w [] 0 []); last done.
  iStep. iExists 0. iSteps.
  - iPureIntro. intros. destruct tgen'; [lia|done].
  - iPureIntro. intros e HS. rewrite lookup_empty in HS. by destruct HS.
  - iExists 0. rewrite !omo_rewrite_hints /=. iSteps.
    iPureIntro. intros. rewrite list_lookup_singleton_Some in H6. lia.
Qed.

#[local] Instance read_NonAtomic (l: loc) (E : coPset):
  SolveSepSideCondition (↑histN ⊆ E) →
  SPEC [ε₀] ⟨E⟩ (q : Qp) v V, {{  ▷ @{V} l ↦{q} v ∗ ⊒V }}
    !#l
  {{ RET v; l ↦{q} v }} | 10.
Proof. move => HE. iSteps. Qed.

Set Nested Proofs Allowed.
#[local] Remove Hints read_own_loc_na_spec biabd_big_sepL_mono : typeclass_instances.

#[global] Instance try_push_spec :
  spec_elim_composition_diaframe.try_push_dspec' (try_push try_push' new_offer check_offer) EStackLocal EStackInv.
Proof using All.
  (* intros *)
  intros ??????. iStep 3 as (tid Φ γgt γst γgx γsx γm γh lt lx Mt Mx eV0_type ???????) "HM ⊒M ⊒Mt ⊒Mx e0✓eV0 ? SInv AU".
  (* load tstack *)
  iStep 6. rewrite !omo_rewrite_hints. iStep 3. iExists None. iStep 5.
  (* intro view before calling tstack.try_push. *)
  iApply (bi.sep_elim_r (do_intro_view_forall)). iStep as (??) "? ⊒M ⊒Mt ⊒Mx AU s↦".
  (* try_push' *)
  iStep 6. iInv "SInv" as (E2) "H". iDecompose "H".
  iStep 2. { iSteps. iExists None. iSteps. }
  iIntros (b). destruct b.
  { (* Push on tstack success: commit here *)
    iStep. iDestruct (view_at_elim with "[] AU") as "AU"; [iSteps|]. iMod "AU" as (????) "[H Close]".
    iDestruct (atomic.diaframe_close_right_quant with "Close") as "?". iDecompose "H" as (?) "??? M●2".
    (* invert omo_step *)
    inversion H32; [|inversion POP|inversion EMPPOP|inversion INIT]. inversion PUSH. subst v0. clear PUSH. subst u uV stk.
    iDestruct (OmoAuth_OmoCW_l with "M●2 [$]") as %[eVzfs2 Hezfs2]. iSteps. iExists true. (* return true. *) iStep.
    iExists _. iSplitR. { iPureIntro. eapply stack_step_Push; try done. simpl. instantiate (1 := M). set_solver-. }
    iStep as (?) "????? M●2".
    (* create seen events. These can't be done lazily because we only have access to seen_event_reg_token before we close the AU. *)
    iRename select (OmoAuth γgt _ _ _ _ _ _) into "Mt●2".
    iDestruct (OmoEinfo_get _ _ _ _ _ _ (length x36) with "Mt●2") as "#ten2✓teV2"; [by rewrite !omo_rewrite_hints|].
    iMod (OmoHb_new_1 with "M●2 [] ten2✓teV2") as "[M●2 #psId⊒ten2]"; [|done|]. { solve_lat. }
    iMod (OmoHb_new_1 (eventT2:=sevent_hist) _ γg _ _ _ _ (length E2) (length E2) with "M●2 [$] [$]") as "[M●2 #psId⊒psId]"; [done|].
    (* close AU *)
    iExists (). iStep as (??) "?? M●2". iExists (length x38). rewrite omo_insert_w_append_w; [|lia].
    iStep. iSplitR. { iApply big_sepS_subseteq; last first. - by iApply @OmoUB_singleton. - set_solver-. } iStep.
    (* closed AU *)
    (* create OmoLt *)
    iDestruct (OmoEinfo_get with "M●2") as "#ezfs2✓eVzfs2". { by apply lookup_app_l_Some. }
    iDestruct (OmoLt_get_append_w with "M●2 ezfs2✓eVzfs2") as "#ezfs2<psId". { apply lookup_lt_Some in Hezfs2. lia. }
    (* close Inv *)
    iStep. iExists (Some x47). iStep. iExists false. iStep. rewrite !omo_rewrite_hints. iStep. iSplitR. { iApply OmoLe_get_from_Eq. iSteps. }
    oSteps. { enough (x ⊑ x51) by solve_lat. by eapply bool_decide_unpack. }
    do 2 (iExists _; iSplitR; first (iPureIntro; symmetry; by eapply lookup_app_l_Some); iStep). (* Closed Inv. Rest is simple. *) iSteps.
    Unshelve. all: try pure_solver.trySolvePure; iPureIntro.
    - symmetry. by eapply lookup_app_l_Some.
    - (* last_empty_t *) intros ?? Hl ?. destruct (decide (tgen' = length x42)) as [->|NEQ]; sauto using @lookup_app_1_eq, @lookup_app_1_ne.
    - (* last_empty *) intros ?? Hl ?. destruct (decide (i = length x41)) as [->|NEQ]; sauto using @lookup_app_1_eq, @lookup_app_1_ne. }
  (* Push on tstack failed, use exchanger *)
  (* Reduction & load exchanger *)
  iStep 3. iExists None. iStep 15.
  (* new_offer *)
  iStep 6. iInv "SInv" as (E3) "H". iDecompose "H". iStep 2. { iSteps. iExists None. iSteps. }
  iIntros (v3). destruct (decide (v3 = 0%Z)) as [->|NEQ].
  { (* [new_offer] failed, commit nothing *)
    iSteps. iDestruct (view_at_elim with "[] AU") as "AU"; [iSteps|]. iMod "AU" as (????) "[H Close]".
    iDestruct (atomic.diaframe_close_right_quant with "Close") as "?". iExists None. iStep. iExists false. iStep. iExists (). iSteps. }
  (* [new_offer] succeeded, register helping *)
  iStep 2.

  inversion H48; [inversion INIT|..|inversion ACK|inversion RVK|inversion ACP].
  inversion REG. subst e eV stl str v0. clear REG H48. subst.

  iStep. iExists None. iStep. rewrite !omo_rewrite_hints /=. iStep.

  iMod UTok_alloc as (γu) "Hγu".
  iMod (saved_vProp_alloc DfracDiscarded (Φ #true)) as (γpt) "#Hγpt"; [done|].
  iMod (saved_vProp_alloc DfracDiscarded (Φ #false)) as (γpf) "#Hγpf"; [done|].

  iMod (ghost_map_insert_persist (length x62) (encode (γpt,γpf,γu),x76) with "[$]") as "[? #KEY]".
  { destruct (x70 !! length x62) eqn:Heq; try done. assert (length x62 < length x62) by eauto. lia. }

  assert (x ⊔ x51 ⊑ x76). { by eapply bool_decide_unpack. }
  do 10solveStep. iExists V, M, (λ b, Φ #b). iSplitL "AU". {
    iModIntro. iDestruct (view_at_objective_iff _ x with "SInv") as "SInv@x".
    iCombine "SInv@x AU" as "RES". iApply (view_at_mono with "RES"). { solve_lat. }
    iIntros "[#SInv AU]". iSteps. iExists (). iStep 2. { iSteps. iExists (). iSteps. }
    iIntros (b). destruct (b); iSteps; [iExists true|iExists false]; iSteps; iExists (); iSteps. } iStep.
  (* closed inv *)
  (* clear spatial context *)
  iAssert (emp%I) with "[-Hγu]" as "_"; [done|].
  (* reduction & check_offer *)
  iSteps. iInv "SInv" as (E4) "H". iDecompose "H". iStep. iExists (last_state_xchg N γg s γgx γh x94). iStep 2. { iSteps. iExists None. iSteps. }
  iIntros (v4). destruct (decide (v4 = (-1)%Z)) as [->|NEQv4].
  { (* revoked my offer, commit nothing *)
    iStep. inversion H69; [inversion INIT|inversion REG|inversion ACK|inversion RVK|inversion ACP]. subst e eV stl str e'.
    destruct ACKS as [xinfo4 Hxinfo4].
    iRename select (big_opM _ _ x82) into "BIGxstl4". iDestruct (big_sepM_delete with "BIGxstl4") as "H"; [done|]. iDecompose "H".
    iRename select (@{_} atomic_update_push _ _ _ _ _ _ _)%I into "AU". iDestruct (view_at_elim with "[] AU") as "AU"; [iSteps|].
    iMod "AU" as (????) "[H Close]". iDestruct (atomic.diaframe_close_right_quant with "Close") as "?". iDecompose "H". iStep.
    iAssert (▷ (_ false ≡ Φ #false))%I as "EQ". { by iApply saved_vProp_agree. }
    iStep. iExists false. iStep. iExists (). oSteps. iExists None. oSteps. 1: shelve.
    iRename select (_ ≡ _)%I into "EQ". iRewrite -"EQ". eauto. }

  (* Exchange success, already committed by Pop thread *)
  iStep. rename x91 into omox4, x88 into Ex4, x94 into xstlist4.
  assert (length xstlist4 > 0). { destruct xstlist4; [done|simpl;lia]. }
  have EQlenxST4: (length omox4 = length xstlist4). { by eapply omo_stlist_length. }
  have [[xe xes] Hxgen4] : is_Some (omox4 !! (length omox4 - 1)) by rewrite lookup_lt_is_Some; lia.
  eapply (omo_read_op_step _ _ _ (length omox4 - 1) (length xes) (length Ex4)) in H67 as STEP; last first.
  { replace (length omox4 - 1) with (Init.Nat.pred (length omox4)) by lia. rewrite EQlenxST4 -last_lookup //. }
  { rewrite lookup_app_1_eq. done. }
  { rewrite lookup_omo_ro_event omo_insert_r_read_op list_lookup_alter /omo_read_op list_lookup_fmap Hxgen4 /= lookup_app_1_eq. done. }
  inversion STEP; [inversion INIT|inversion REG|inversion ACK|inversion RVK|inversion ACP]. subst e eV stl str e' v0.

  iDestruct (big_sepM_lookup_acc _ _ _ _ ACKS with "[$]") as "H". iDecompose "H".
  iAssert (⌜x88 = true ∨ x88 = false⌝)%I as "H". { destruct x88; eauto. } iDecompose "H".
  iAssert (▷ (_ ≡ Φ #true))%I as "EQ". { by iApply saved_vProp_agree. }
  iStep 2. iExists None. iStep. iExists false. iStep 7 as "EQ". iRewrite -"EQ". simpl in *. iSteps.
  Unshelve. all: iPureIntro; unfold hmap_valid.
  - intros e [γ He]. rewrite app_length /=. destruct (decide (e = length x62)) as [-> | ?]; first lia.
    enough (e < length x62) by lia. rewrite lookup_insert_ne in He; eauto.
  - intros. rewrite app_length /=. enough (e < length x88) by lia. eauto.
  - intros. rewrite app_length /=. enough (e < length Ex4) by lia. eauto.
Qed.


#[global] Instance if_bool_Persistent {I : biIndex} {PROP : bi} (P Q : monPred I PROP) (b : bool) `{!Persistent P, !Persistent Q} :
Persistent (if (b) then P else Q) | 999.
Proof. destruct b; tc_solve. Qed.

#[global] Instance if_bool_Objective {I : biIndex} {PROP : bi} (P Q : monPred I PROP) (b : bool) `{!Objective P, !Objective Q} :
  Objective (if (b) then P else Q) | 999.
Proof. destruct b; tc_solve. Qed.

#[local] Hint Resolve mergable_consume_remove_view_at_from_objective : typeclass_instances.

#[global] Instance try_pop_spec :
  spec_elim_composition_diaframe.try_pop_dspec' (try_pop try_pop' take_offer) EStackLocal EStackInv.
Proof using All.
  intros ???? V0. iStep 3 as (tid Φ γgt γst γgx γsx γm γh lt lx Mt Mx ???????) "HM ⊒M ⊒Mt ⊒Mx e0✓eV0 ? SInv AU".
  (* load tstack *)
  iStep 6. rewrite !omo_rewrite_hints. iStep 3. iExists None.
  iDestruct (StackLocal_OmoEview with "[$]") as "H". iDecompose "H".
  iDestruct (OmoEview_update γg γg _ _ x2 _ _ M M with "[$] [] []") as (M') "H"; [iSteps..|]. iDecompose "H".
  iDestruct (OmoEview_update γg γgt _ _ x2 _ _ M' Mt with "[$] [] []") as (Mt1) "H"; [iSteps..|]. iDecompose "H".
  iDestruct (StackLocal_Eview_update _ _ _ _ Mt Mt1 with "[] []") as "?"; [iSteps..|].
  replace (Mt ∪ Mt1) with Mt1; [|set_solver]. iStep 5.
  (* intro view before tstack.try_pop *)
  iApply (bi.sep_elim_r (do_intro_view_forall)). iStep as (??) "???????? AU s↦".
  (* tstack.try_pop *)
  iStep 6. iInv "SInv" as (E2) "H". iDecompose "H". iStep 2. { iSteps. iExists None. iSteps. }
  iIntros (v2). destruct (decide (v2 = (-1)%Z)) as [->|NEv2]; last first.
  { (* If there was no race, then commit here, either Pop or EmpPop *)
    eapply omo_stlist_length in H32 as EQlentST2.
    assert (length x43 > 0). { destruct x40; [done|simpl in *; lia]. }
    iDestruct (view_at_elim with "[] AU") as "AU"; [iSteps|]. destruct (decide (v2 = 0%Z)) as [->|NEv2'].
    - (* Commit EmpPop *)
      iStep. iMod "AU" as (????) "[H Close]".
      iDestruct (atomic.diaframe_close_right_quant with "Close") as "?". iDecompose "H" as (?) "??? M●2".
      iAssert (OmoUB γg M x48)%I with "[-]" as "#?".
      { rewrite {2}/OmoUB. iApply big_sepS_forall. iIntros "%e %IN". iDestruct (OmoAuth_OmoEview _ _ _ _ _ _ M with "M●2 []") as %CLOSED; [iSteps|].
        apply CLOSED in IN as He. destruct He as [eV He]. iDestruct (big_sepL_lookup with "[$]") as (cs) "CASE"; [exact He|]. destruct cs; [done|].
        iDecompose "CASE" as (e' te') "e⊒e' ezfs2<e' e'≤e MONO✓e' e'↦te' e'⊒te'".
        iDestruct (OmoHb_HbIncluded with "e⊒e' [$]") as %IN'; [done|]. iDestruct (OmoHb_HbIncluded _ _ M' with "e'⊒te' [$]") as %tIN; [done|].
        iDestruct (big_sepS_elem_of with "[$]") as "#te'≤ten2"; [exact tIN|]. rename x37 into Et2, x40 into omot2, x56 into tgen2, x43 into tstlist2, x50 into tgenzf2.
        have [[te tes] Htgen2] : is_Some (omot2 !! tgen2) by rewrite lookup_lt_is_Some. have Htgen2st : tstlist2 !! tgen2 = Some [].
        { have [st Hst] : is_Some (tstlist2 !! tgen2) by rewrite lookup_lt_is_Some -EQlentST2.
          eapply (omo_read_op_step _ _ _ tgen2 (length tes) (length Et2)) in H36; last first; [done|..].
          - by rewrite lookup_app_1_eq.
          - by rewrite lookup_omo_ro_event omo_insert_r_read_op list_lookup_alter /omo_read_op list_lookup_fmap Htgen2 /= lookup_app_1_eq.
          - inversion H36; try done. subst. done. }
        destruct (le_lt_dec tgen2 tgenzf2) as [LE|LT]; [|exfalso; sauto].
        iDestruct (OmoLe_get (eventT := sevent_hist) γgt _ _ _ _ _ (ro_event tgen2 (length tes)) (wr_event tgenzf2) with "[$]") as "#ten2≤tezf2"; [..|done|].
        { rewrite lookup_omo_ro_event omo_insert_r_read_op list_lookup_alter /omo_read_op list_lookup_fmap Htgen2 /= lookup_app_1_eq. done. }
        { rewrite lookup_omo_wr_event omo_insert_r_write_op. done. }
        iDestruct (OmoLe_trans with "te'≤ten2 ten2≤tezf2") as "te'≤tezf2".
        iExFalso. iApply (OmoLe_Lt_contra with "[-] ezfs2<e'"). iApply (CWMono_acc with "[$] [] [] []"); try done. }
      iStep 2. iExists 0. iStep. iExists _. iSplitR. { iPureIntro. eapply stack_step_EmpPop; try done. instantiate (1 := M). set_solver-. }
      iStep. iExists (). iStep. iSplitR. { iApply (OmoUB_mono with "[$] []"). iApply OmoLe_get_from_Eq. iSteps. }
      oSteps. iExists (Some x48) (* ezfl *). oSteps. iExists true. iSplitR. { iApply OmoLe_get_from_Eq. iSteps. } oSteps.
      Unshelve. all: try pure_solver.trySolvePure.
      + iPureIntro. apply lookup_omo_lt_Some in H40. rewrite !omo_rewrite_hints in H40. done.
    - (* Commit Pop *)
      iStep. rename x43 into tstlist2, x56 into ntstf2, x37 into Et2.
      iDestruct (OmoAuth_OmoCW_l (eventT := sevent_hist) γg with "[$] [$]") as %[eVzfs2 Hezfs2].
      iDestruct (OmoEinfo_get (eventT := sevent_hist) γgt _ _ _ _ _ (length Et2) with "[$]") as "#ten2✓teV2". { by rewrite lookup_app_1_eq. }
      iDestruct (OmoAuth_wf (eventT := sevent_hist) γg with "[$]") as %[OMO_GOOD2 _]. eapply omo_stlist_length in OMO_GOOD2 as EQlenST2.
      iMod "AU" as (????) "[H Close]".
      iDestruct (atomic.diaframe_close_right_quant with "Close") as "?". iDecompose "H" as (?) "??? M●2".
      inversion H38; [inversion PUSH|inversion POP|inversion EMPPOP|inversion INIT]. subst. simpl in *.
      destruct x34 as [|stf2 nstf2]. { iDestruct (big_sepL2_length with "[$]") as %?. simpl in *. lia. }
      iRename select (big_sepL2 _ _ _) into "H". rewrite (big_sepL2_cons _ stf2). iDecompose "H".
      iDestruct (big_sepL2_length with "[$]") as %EQlenSTs.
      iStep 2. iExists x54. rewrite decide_False; [|lia]. iStep. iExists _, _. rewrite decide_False; [|lia].
      iStep. iExists _. iSplitR. { iPureIntro. apply stack_step_Pop; try done; simpl; [solve_lat|]. instantiate (1 := x43 ∪ {[x34]} ∪ M). set_solver-. } iStep.
      (* create seen_events *)
      unseal_diaframe; simpl. iApply (fupd_mono).
      { iApply (bi.wand_elim_r (OmoHb γg γg (length E2) (length E2) ∗ OmoHb γg γgt (length E2) (length Et2))). }
      iStep 2. iExists (). Unshelve. 2: pure_solver.trySolvePure. iSteps. iExists _. iSplitR. { rewrite omo_insert_w_append_w; done. }
      iStep 2. iSplitR. { iApply (big_sepS_subseteq _ _ M); last by iApply @OmoUB_singleton. set_solver-. }
      iStep 3. rename x47 into ezfs2, x48 into ezfl2.
      destruct ntstf2.
      + destruct nstf2; [|done]. iExists (Some (length E2)). iStep. iExists (length E2). iSplit.
        { iApply big_sepL_forall. iIntros "%e %eV %Lookup". iExists true. iApply OmoLe_get_from_Lt.
          iDestruct (OmoEinfo_get (eventT := sevent_hist) γg with "[$]") as "#?"; first by apply lookup_app_l_Some.
          iApply (OmoLt_get_append_w γg (eventT := sevent_hist) with "[$] [$]").
          intros <-. by eapply lookup_length_not_is_Some. }
        iStep. iExists true. iSplit. { rewrite omo_rewrite_hints. iApply OmoLe_get_from_Eq. iSteps. }
        oSteps. iExists (length x40). iStep. iExists (length x39). iSteps; [shelve..|]. rewrite bool_decide_false; [|lia]. iSteps.
        Unshelve. all: try iPureIntro; rewrite ?omo_rewrite_hints; try pure_solver.trySolvePure.
        * tc_solve.
        * by rewrite omo_write_op_length lookup_app_1_eq.
        * by rewrite EQlentST2 ?omo_write_op_length lookup_app_1_eq.
        * rewrite EQlentST2. intros ?? Lookup%lookup_lt_Some HLen. rewrite app_length /= in Lookup. set L := (length tstlist2). rewrite -/L in Lookup HLen. lia.
        * by rewrite omo_write_op_length lookup_app_1_eq.
        * rewrite EQlenST2. intros ?? Lookup%lookup_lt_Some HLen. rewrite app_length /= in Lookup. set L := (length x42). rewrite -/L in Lookup HLen. lia.
      + iExists (Some ezfl2). iStep. iExists false. iStep. rewrite !omo_rewrite_hints. iStep.
        assert (ezfs2 < length E2). { by eapply lookup_lt_Some. }
        iSplit. { iDestruct (OmoEinfo_get (eventT := sevent_hist) γg with "[$]") as "#?"; first by apply lookup_app_l_Some.
          iApply (OmoLt_get_append_w γg (eventT := sevent_hist) with "[$] [$]"). lia. }
        iStep. iSplit. { iApply OmoLe_get_from_Eq. iSteps. } oSteps.
        do 2(iExists _; iSplitR; [(iPureIntro; symmetry; by eapply lookup_app_l_Some)|]; iStep). iSteps. rewrite bool_decide_false; [|lia]. iSteps.
        Unshelve. all: iPureIntro.
        * symmetry; by eapply lookup_app_l_Some.
        * intros ?? Lookup HLen. destruct (decide (tgen' = length tstlist2)) as [->|NEQ].
          ** rewrite lookup_app_1_eq in Lookup. by inversion Lookup.
          ** rewrite lookup_app_1_ne in Lookup; [|done]. eauto.
        * intros ?? Lookup HLen. destruct (decide (i = length x42)) as [->|NEQ].
          ** rewrite lookup_app_1_eq in Lookup. inversion Lookup. intros ?. subst. done.
          ** rewrite lookup_app_1_ne in Lookup; [|done]. eauto. }
  (* Race happened, try using exchanger *)
  iSteps. iExists None. iSteps. iInv "SInv" as (E3) "H".
  iDecompose "H" as (γs3 Et3 Ex3 omo3 omot3 omox3 stlist3 tstlist3 xstlist3 Mono3 hmap3 ezfs3 ezfl3 ????????????????????????????) "?????????????????????? M●".
  iStep. iExists (last_state_xchg N γg s γgx γh _). iStep 2. { iSteps. iExists None. iSteps. }
  iIntros (v3). destruct (decide (v3 = (-1)%Z)) as [->|NEv3].
  { (* [take_offer] failed. [try_pop] also fails. Commit nothing *)
    iStep. iDestruct (view_at_elim with "[] AU") as "AU"; [iSteps|]. iMod "AU" as (????) "[H Close]".
    iDestruct (atomic.diaframe_close_right_quant with "Close") as "?". iDecompose "H".
    iSteps. iExists (-1)%Z. iSteps. iExists (). iSteps. iExists None. iSteps. }

  (* [take_offer] succeeded. Commit Pop *)
  iStep as (V3 ?????? STEP ?) "?????? Mx●3 ? WCOMMIT". inversion STEP; simpl in *; try done. inversion ACP. subst e eV stl str v' v.
  iStep.  iRename select (big_opM _ _ x57) into "H". iDestruct (big_sepM_delete with "H") as "H"; [done|].
  iDecompose "H" as (v3 V' lV' γpt γpf γu Vi M0 Q ?????????) "?????? Hγpt Hγpf ? Mx●3 AU' WCOMMIT' ?". eassert (x ⊔ _ ⊑ V3). { done. }
  iAssert (@{V' ⊔ V3}(meta s nroot _ ∗ (@{V' ⊔ V3} OmoEview_or_empty γg M) ∗ CWMonoValid γm ezfs3 ∗ OmoAuth γg γs3 (1 / 2) _ _ _ stack_interpretable ∗
    (@{V' ⊔ V3} EStackLocal_inner N γg s M0) ∗ OmoTokenW γgx _ ∗ OmoTokenW γgx _ ∗ AllEvents γg γs3 γgt γgx γm E3 ezfs3 ezfl3 ∗ InternInv N γg s ∗
    last_state γg γgt stlist3 tstlist3 ∗ atomic_update_push _ _ _ _ _ _ _ ∗ atomic_update _ _ _ _ _  ∗ ⊒(V' ⊔ V3)))%I with "[AU AU' WCOMMIT WCOMMIT' M●]" as "RES".
  { iAssert ⌜∃ Md, M' = M ⊔ Md⌝%I as "H". { iPureIntro. clear -H16. set_solver. } iDecompose "H". iSteps. }

  iAssert (|={⊤ ∖ ↑(xchgN N) ∖ ↑(estackN N)}=> @{V' ⊔ V3} (∃ E3' omo3' stlist3' γs3' ezfl3',
    Q true ∗ (emp -∗ Φ #v3) ∗ Peek (OmoAuth γg γs3' (1/2)%Qp E3' omo3' stlist3' stack_interpretable) ∗ AllEvents γg γs3' γgt γgx γm E3' ezfs3 ezfl3' ∗
    last_state γg γgt stlist3' tstlist3 ∗ last_empty ezfl3' (omo_write_op omo3') stlist3' ∗ OmoAuth γg γs3' (1/2)%Qp E3' omo3' stlist3' _))%I with "[RES]" as ">H".
  { rewrite -view_at_fupd. iApply (view_at_mono with "RES"); [done|].
    iStep as (Mt0 Mx0 ????????) "???????????? SInv ?? M●3 WCOMMIT1 WCOMMIT2 AU1 AU2".
    (* Pick latest observed event (e3) *)
    iDestruct (OmoEview_latest_elem γg (M ∪ M0) with "[]") as (e3) "[MAXe3 %e3IN]"; [iSteps|].
    iDestruct (OmoAuth_wf (eventT := sevent_hist) γg with "[$]") as %[OMO_GOOD3 _]. eapply omo_stlist_length in OMO_GOOD3 as EQlenST3.
    iDestruct (OmoAuth_OmoEview (eventT := sevent_hist) γg _ _ _ _ _ (M ∪ M0) with "[$] []") as %INCL; [iSteps|].
    apply INCL in e3IN as e3IN'. eapply lookup_omo_surjective in e3IN' as [eidx3 Heidx3]; [|done]. pose gen3 := gen_of eidx3.
    epose (E3' := E3 ++ [mkOmoEvent (Push v3) (V' ⊔ V3) ({[length E3]} ∪ (M ∪ M0))]). rename x76 into genzfl3. (* H47 *)

    destruct (le_lt_dec gen3 genzfl3) as [LEgen|LTgen].
    - (* If current observation is ealier than [genzfl3], then commit Push and Pop consecutively at [genzfl3] *)
      iDestruct (OmoAuth_OmoSnap _ _ _ _ _ _ ezfl3 with "M●3 []") as %Hst; [by rewrite -lookup_omo_wr_event in H46|iSteps|]. simpl in Hst.

      iAssert (∀ len, ∃ stnew, ⌜ interp_omo E3' ((length E3, []) :: take len (drop (genzfl3 + 1)%nat omo3)) [] stnew ∧ (∀ i st1 st2,
          stlist3 !! (genzfl3 + i)%nat = Some st1 → stnew !! i = Some st2 → st2 = st1 ++ [(length E3, v3, (V' ⊔ V3), {[length E3]} ∪ (M ∪ M0)) ]) ⌝)%I with "[M●3]" as "%Hgengood".
      {  iIntros "%len". iInduction len as [|] "IH".
        - rewrite take_0. iExists [_]. iPureIntro. split.
          + rewrite -(app_nil_l [_]) -(app_nil_l [(_, [])]). eapply interp_omo_snoc. split_and!; rewrite ?omo_rewrite_hints; try done.
            * eapply interp_omo_nil. * eapply stack_step_Push; try done. set_solver-.
          + intros ??? HstL HL. destruct i; [|done]. inversion HL. subst. rewrite Nat.add_0_r Hst in HstL. by inversion HstL.
        - iDestruct ("IH" with "M●3") as %(stnew & IH1 & IH2).

          destruct (le_lt_dec (length (drop (genzfl3 + 1) omo3)) len) as [LE'|LT']. { rewrite !take_ge in IH1 |- *; [|lia..]. eauto. }
          have [[e es] Hlast] : is_Some ((drop (genzfl3 + 1) omo3) !! len) by rewrite lookup_lt_is_Some.
          rewrite (take_S_r _ _ (e, es)); [|done]. rewrite lookup_drop in Hlast. specialize (omo_gen_info _ _ _ _ _ _ OMO_GOOD3 Hlast) as (eV&?&st'&?&?&E3e&Lookup_stlist3&?&ES).

          have Nempst' : st' ≠ [] by eapply H47; [done|lia]. destruct es; last first.
          { rewrite Forall_cons in ES. destruct ES as [(?&?&Hstep&?) _]. inversion Hstep; try done; apply (f_equal length) in H71; rewrite cons_length in H71; lia. }

          have [stp Hstp] : is_Some (stlist3 !! (genzfl3 + len)) by rewrite lookup_lt_is_Some; apply lookup_lt_Some in Lookup_stlist3; lia.
          have STEP' : omo.step e eV stp st'.
          { eapply omo_write_op_step; try done; replace (genzfl3 + len + 1) with (genzfl3 + 1 + len) by lia; try done.
            rewrite list_lookup_omo_destruct in Hlast. by destruct Hlast as [? _]. }

          apply interp_omo_length in IH1 as EQlen. apply lookup_lt_Some in Hlast as LTlen.
          rewrite /= take_length drop_length Nat.min_l in EQlen; [|lia].
          have [stp' Hstp'] : is_Some (stnew !! len) by rewrite lookup_lt_is_Some; lia.
          eapply IH2 in Hstp' as EQstp'; [|done].
          replace ((length E3, []) :: take len (drop (genzfl3 + 1)%nat omo3) ++ [(e, [])]) with
              (((length E3, []) :: take len (drop (genzfl3 + 1)%nat omo3)) ++ [(e, [])]); [|by simplify_list_eq].

          apply lookup_lt_Some in E3e as ?. have lastStn: (last stnew = Some (stp')). { rewrite last_lookup -Hstp'. f_equal. lia. }
          inversion STEP'; try (by subst); [iExists (stnew ++ [_ :: stp'])|iExists (stnew ++ [stk ++ [_]])]; iPureIntro; subst.
          all: split; first (eapply interp_omo_snoc; split_and!; try done; [rewrite lookup_app_1_ne; [done|lia] | by rewrite last_cons lastStn |]).
          1: by eapply stack_step_Push. 2: by eapply stack_step_Pop.
          all: intros ??? Hi1 Hi2; destruct (decide (i = length stnew)) as [->|NEQ]; first ( rewrite lookup_app_1_eq in Hi2; inversion Hi2; rewrite -EQlen in Hi1;
           replace (_ + _) with (genzfl3 + 1 + len) in Hi1 by lia; rewrite Lookup_stlist3 in Hi1; by inversion Hi1).
          all: eapply IH2; try done; by rewrite lookup_app_1_ne in Hi2. }

      specialize (Hgengood (length (drop (genzfl3 + 1) omo3))) as (stnew & Hgengood & Hstnew). rewrite take_ge in Hgengood; [|done].
      iDestruct (OmoUB_into_gen with "M●3 MAXe3") as %MAXe3; [done|]. apply (OmoUBgen_mono _ _ _ genzfl3) in MAXe3 as MAXgenzfl3; [|done].
      iMod "AU1" as (????) "[H Close]". iDestruct (atomic.diaframe_close_right_quant with "Close") as "?". iDecompose "H" as (_) "??? M●3".
      iMod (OmoAuth_insert _ _ _ _ _ _ _ _ _ (M ∪ M0) with "M●3 [] WCOMMIT1 []") as (γs3') "H".
      { iSteps. } { iPureIntro. split_and!; try done; simpl; done. } iDecompose "H". iStep. rewrite try_update_OmoAuth_to_eq. iStep. iExists ().
      iStep as "?? M●3". iSplitR. { iApply big_sepS_subseteq; last by iApply @OmoUB_singleton. set_solver-. } iStep.
      (* Commit Pop *)
      pose omo3' := omo_insert_w omo3 (genzfl3 + 1) (length E3) [].
      pose stlist3' := take (genzfl3 + 1) stlist3 ++ stnew.
      pose gen := (genzfl3 + 1)%nat.
      epose (E3'' := E3' ++ [mkOmoEvent (Pop v3) (V' ⊔ V3) ({[length E3; length E3']} ∪ (M ∪ M0))]).
      iDestruct (OmoAuth_wf with "M●3") as %[OMO_GOOD3' _]. eapply omo_stlist_length in OMO_GOOD3' as EQlenST3'.
      apply eq_sym in H46 as Hgenzfl3. apply lookup_lt_Some in Hgenzfl3.
      have EQ' : length (take (genzfl3 + 1) stlist3) = gen. { rewrite take_length -EQlenST3 Nat.min_l; [lia|]. rewrite -omo_write_op_length in Hgenzfl3. lia. }
      Unshelve. all: try pure_solver.trySolvePure.

      iAssert (∀ len, ∃ stnew', ⌜ interp_omo E3'' ((length E3', []) :: take len (drop (gen + 1)%nat omo3')) [(length E3, v3, (V' ⊔ V3), {[length E3]} ∪ (M ∪ M0))] stnew' ∧ (∀ i st1 st2,
        stlist3 !! (genzfl3 + i)%nat = Some st1 → stnew' !! i = Some st2 → st1 = st2) ⌝)%I with "[M●3]" as "%Hgengood'".
      { iIntros "%len". iInduction len as [|] "IH".
        - rewrite take_0. iExists [[]]. iPureIntro. split.
          + rewrite -(app_nil_l [[]]) -(app_nil_l [(_, [])]). eapply interp_omo_snoc. split_and!; rewrite ?omo_rewrite_hints; try done.
            * eapply interp_omo_nil. * eapply stack_step_Pop; try done. simpl. set_solver-.
          + intros ??? HstL HL. destruct i; [|done]. inversion HL. subst. rewrite Nat.add_0_r Hst in HstL. by inversion HstL.
        - iDestruct ("IH" with "M●3") as %(stnew' & IH1 & IH2).
          destruct (le_lt_dec (length (drop (gen + 1) omo3')) len) as [LE'|LT']. { fold omo3' stlist3'. rewrite !take_ge in IH1 |- *; [|lia..]. eauto. }
          have [[e es] Hlast] : is_Some ((drop (gen + 1) omo3') !! len) by rewrite lookup_lt_is_Some.
          rewrite (take_S_r _ _ (e, es)); [|done]. rewrite lookup_drop in Hlast. specialize (omo_gen_info _ _ _ _ _ _ OMO_GOOD3' Hlast) as (eV&?&st'&?&?&E3e&Lookup_stlist3'&?&ES).

          apply interp_omo_length in Hgengood as EQlenstnew. rewrite /= drop_length in EQlenstnew.
          have Lookup_stnew : stnew !! (len + 1)%nat = Some st'.
          { rewrite lookup_app_r in Lookup_stlist3'; [|lia]. rewrite EQ' in Lookup_stlist3'. replace (gen + 1 + len - gen) with (len + 1) in Lookup_stlist3' by lia. done. }
          have [st3 Lookup_stlist3] : is_Some (stlist3 !! (genzfl3 + (len + 1))).
          { rewrite lookup_lt_is_Some. apply lookup_lt_Some in Lookup_stnew. rewrite -omo_write_op_length in Hgenzfl3.
            replace (S (length omo3 - (genzfl3 + 1))) with (length omo3 - genzfl3) in EQlenstnew by lia. rewrite -EQlenstnew in Lookup_stnew. lia. }
          eapply Hstnew in Lookup_stlist3 as EQst'; [|done].
          destruct es; last first.
          { rewrite Forall_cons in ES. destruct ES as [(?&?&ST&?) _].
            inversion ST; try done; subst st'; try (apply (f_equal length) in H72; rewrite cons_length in H72);
            try (apply (f_equal length) in H71; rewrite app_length /= in H71); lia. }

          have [stp Hstp] : is_Some (stlist3' !! (gen + len)). { rewrite lookup_lt_is_Some. apply lookup_lt_Some in Lookup_stlist3'. subst stlist3'. lia. }

          have STEP' : omo.step e eV stp st'.
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
          { rewrite lookup_app_r in Hstp; [|lia]. rewrite EQ' in Hstp. replace (gen + len - gen) with len in Hstp by lia. done. }
          eapply Hstnew in Hstp'''; [|done]. subst stp st'.
          replace ((_, []) :: take len _ ++ [(e, [])]) with (((length E3', []) :: take len (drop (gen + 1)%nat omo3')) ++ [(e, [])]); [|by simplify_list_eq].

          apply lookup_lt_Some in E3e as ?. have lastStn: (last stnew' = Some (stp')). { rewrite last_lookup -Hstp'. f_equal. lia. }
          inversion STEP'; iPureIntro; subst E3'; subst.
          3, 4: apply (f_equal length) in H71; rewrite app_length /= in H71; lia.
          1: replace (_ :: _) with (((e, v, eV.(sync), eV.(eview)) :: stp') ++ [(length E3, v3, (V' ⊔ V3), {[length E3]} ∪ (M ∪ M0))]) in H72;
            [|by simplify_list_eq]; apply app_inj_2 in H72 as [? _]; [|done]; eexists (stnew' ++ [_ :: stp']).
          2: replace (_ :: _) with (((u, v, V, lV) :: st3) ++ [(length E3, v3, V' ⊔ V3, {[length E3]} ∪ (M ∪ M0))]) in H71; [|by simplify_list_eq];
            apply app_inj_2 in H71 as [? _]; [|done]; eexists (stnew' ++ [st3]).
          all: subst; split; first (eapply interp_omo_snoc; split_and!; try done; [rewrite lookup_app_1_ne; [done|lia] | by rewrite last_cons lastStn |]).
          1: by eapply stack_step_Push. 2: by eapply stack_step_Pop.
          all: intros ??? Hi1 Hi2; destruct (decide (i = length stnew')) as [->|NEQ]; first (rewrite lookup_app_1_eq in Hi2; inversion Hi2; rewrite -EQlen in Hi1;
            replace (genzfl3 + S len) with (genzfl3 + (len + 1)) in Hi1 by lia; rewrite Lookup_stlist3 in Hi1; inversion Hi1; by subst).
          all: eapply IH2; try done; by rewrite lookup_app_1_ne in Hi2. }

      specialize (Hgengood' (length (drop (gen + 1) omo3'))) as (stnew' & Hgengood' & Hstnew'). rewrite take_ge in Hgengood'; [|done].
      iDestruct (OmoUB_into_gen _ _ _ _ _ _ _ _ (wr_event gen) with "M●3 []") as %MAXpsId; [|by iApply @OmoUB_singleton|].
      { rewrite lookup_omo_wr_event omo_insert_w_write_op. have EQ : length (take (genzfl3 + 1) (omo_write_op omo3)) = gen.
        { rewrite take_length Nat.min_l; [done|lia]. } rewrite lookup_app_r EQ; [|lia]. rewrite Nat.sub_diag //. }
      simpl in *. replace (_ ∪ _) with ({[length E3]} ∪ (M ∪ M0)) in MAXpsId; [|set_solver-].
      iMod "AU2" as (????) "[H Close]". iDestruct (atomic.diaframe_close_right_quant with "Close") as "?". iDecompose "H" as (_) "??? M●3".

      iMod (OmoAuth_insert _ _ _ _ _ _ _ _ _ ({[length E3]} ∪ (M ∪ M0)) with "M●3 [] WCOMMIT2 []") as (γs3'') "H".
      { iSteps. } { iPureIntro. split_and!; try done; simpl; try done.
        - subst E3'. rewrite app_length. set_solver-.
        - rewrite lookup_app_r; [|lia]. rewrite EQ' Nat.sub_diag. rewrite -(Nat.add_0_r genzfl3) in Hst.
          have [st' Hst'] : is_Some (stnew !! 0).
          { rewrite lookup_lt_is_Some. apply interp_omo_length in Hgengood. destruct stnew; simpl; [done|lia]. }
          eapply Hstnew in Hst; [|done]. subst st'. rewrite Hst'. clear. by simplify_list_eq. } iDecompose "H".
      (* Close AU *)
      iApply (fupd_mono _ _ _ _ (bi.sep_elim_r (χ) _)). iStep. iExists v3. rewrite decide_False; [|lia]. iStep. iExists _, _. rewrite decide_False; [|lia]. iStep.
      rewrite try_update_OmoAuth_to_eq. iStep. iExists (). iStep as "?? M●3".
      iSplitR. { iApply big_sepS_subseteq; last by iApply @OmoUB_singleton. rewrite app_length /=. set_solver-. } iStep as "HΦ".
      (* Close Inv *)
      have HppId : lookup_omo (omo_insert_w omo3' (gen + 1) (length E3') []) (wr_event (genzfl3 + 2)) = Some (length E3').
      { rewrite lookup_omo_wr_event omo_insert_w_write_op. have EQ : length (take (gen + 1) (omo_write_op omo3')) = (genzfl3 + 2).
        { rewrite take_length Nat.min_l; [lia|]. rewrite omo_insert_w_write_op !app_length /= take_length Nat.min_l; lia. }
        rewrite lookup_app_r; [|lia]. rewrite EQ. replace (genzfl3 + 2 - (genzfl3 + 2)) with 0 by lia. done. }

      pose stlist3'' := take (gen + 1) stlist3' ++ stnew'.
      have STemp : stlist3'' !! (genzfl3 + 2)%nat = Some [].
      { have EQ : length (take (gen + 1) stlist3') = genzfl3 + 2.
        { rewrite take_length Nat.min_l; [lia|]. rewrite -EQlenST3' omo_insert_w_length. rewrite -omo_write_op_length in Hgenzfl3. lia. }
        rewrite lookup_app_r; [|by rewrite EQ; lia]. rewrite EQ. replace (genzfl3 + 2 - (genzfl3 + 2)) with 0 by lia.
        have [st' Hst'] : is_Some (stnew' !! 0).
        { rewrite lookup_lt_is_Some. apply interp_omo_length in Hgengood'. destruct stnew'; simpl; try lia; try done. }
        rewrite -(Nat.add_0_r genzfl3) in Hst. eapply Hstnew' in Hst; [|done]. subst st'. done. }
      iDestruct (OmoSnap_get _ _ _ _ _ _ _ (wr_event (genzfl3 + 2)) (genzfl3 + 2) with "M●3") as "#H"; [done..|]. iDecompose "H".

      iDestruct (OmoLe_get _ _ _ _ _ _ (wr_event genzfl3) (wr_event (genzfl3 + 2)) ezfl3 with "M●3") as "#ezlf3≤ppId"; [shelve|done|simpl;lia|].
      iDestruct (OmoLe_get _ _ _ _ _ _ (wr_event (genzfl3 + 1)) (wr_event (genzfl3 + 2)) (length E3) with "M●3") as "#psId≤ppId"; [shelve|done|simpl;lia|].

      iStep. iSplitL "HΦ"; [done|]. iStep as "?? M●3". iExists (length E3'). iStep. iSplit.
      { iApply big_sepL_forall. iIntros "%e %eV %E3e". iDestruct (big_sepL_lookup with "[$]") as (cs) "#CASE"; [done|]. iExists cs. destruct cs; [by iApply OmoLe_trans|done]. }
      oSteps. iExists true. iStep. iExists true. iSplit. { iApply @OmoLe_get_from_Eq. fold E3'. iSteps. }
      iStep 2. rewrite !omo_rewrite_hints. iExists x59. iSteps.

      Unshelve. all: try pure_solver.trySolvePure; try iPureIntro. all: cycle 2.
      1-2: rewrite lookup_omo_wr_event omo_insert_w_write_op lookup_app_l; last (rewrite take_length omo_insert_w_write_op !app_length /= take_length; lia).
      1-2: rewrite lookup_take; [|lia]; rewrite omo_insert_w_write_op.
      + rewrite lookup_app_l; [rewrite lookup_take|rewrite take_length]; try done; lia.
      + have EQ : length (take (genzfl3 + 1) (omo_write_op omo3)) = genzfl3 + 1. { rewrite take_length Nat.min_l; [done|lia]. }
        rewrite lookup_app_r; [|lia]. rewrite EQ. replace (genzfl3 + 1 - (genzfl3 + 1)) with 0 by lia. done.
      + rewrite last_lookup. apply interp_omo_length in Hgengood' as EQlen. rewrite /= drop_length omo_insert_w_length in EQlen.
        have EQ : Init.Nat.pred (length stnew') = length omo3 - gen by lia. rewrite EQ.
        rewrite last_lookup in H40. replace (Init.Nat.pred (length stlist3)) with (length omo3 - 1) in H40 by lia.
        have EQ'' : length omo3 - 1 = genzfl3 + (length omo3 - gen).
        { have ? : gen ≤ length omo3; [|lia]. rewrite -omo_write_op_length in Hgenzfl3. lia. }
        rewrite EQ'' in H40. have [st' Hst'] : is_Some (stnew' !! (length omo3 - gen)) by rewrite lookup_lt_is_Some -EQlen; lia.
        eapply eq_sym, Hstnew' in H40; [|done]. subst. by rewrite Hst'.
      + intros ?? Hi1 Hi2. eapply (H47 (i - 2)); [|lia]. have EQlen1 : length (take (gen + 1) stlist3') = genzfl3 + 2.
        { rewrite take_length Nat.min_l; [lia|]. rewrite -EQlenST3' omo_insert_w_length. rewrite -omo_write_op_length in Hgenzfl3. lia. }
        rewrite lookup_app_r in Hi1; [|rewrite EQlen1;lia]. rewrite EQlen1 in Hi1.
        have [st' Hst'] : is_Some (stlist3 !! (genzfl3 + (i - (genzfl3 + 2)))).
        { rewrite lookup_lt_is_Some. apply lookup_lt_Some in Hi1. apply interp_omo_length in Hgengood'. rewrite -Hgengood' /= in Hi1.
          rewrite -EQlenST3. rewrite drop_length omo_insert_w_length in Hi1. lia. }
        eapply Hstnew' in Hi1; [|done]. subst st'. replace (genzfl3 + (i - (genzfl3 + 2))) with (i - 2) in Hst' by lia. done.
    - (* If current observation is later than [genzfl3], then commit Push and Pop consecutively at the end of generation *)
      iDestruct (OmoLt_get _ _ _ _ _ _ (wr_event genzfl3) eidx3 with "M●3") as "#ezfl3<e3"; [by rewrite lookup_omo_wr_event|done|done|].
      iDestruct (OmoAuth_OmoLt with "M●3 ezfl3<e3") as %[_ [eV3 HeV3]].
      iDestruct (OmoEinfo_get with "M●3") as "#e3✓eV3"; [done|].
      iDestruct (big_sepL_lookup with "[$]") as (cs) "CASE"; [exact HeV3|]. destruct cs. { iExFalso. iApply (OmoLe_Lt_contra with "[$] [$]"). }
      iDecompose "CASE" as  (e3' te3') "??????". Remove Hints mergable_consume_OmoAuth_appended_induce_step : typeclass_instances.

      iMod "AU1" as (????) "[H Close]". iDestruct (atomic.diaframe_close_right_quant with "Close") as "?". iDecompose "H" as (_) "??? M●3".
      iStep. iExists _. iSplitR. { iPureIntro. eapply stack_step_Push; try done. simpl. instantiate (1 := (M ∪ M0)). set_solver-. } iStep as (?) "????? M●".
      iMod (OmoHb_new_2 with "M● [] [$]") as "[M● #psId⊒e3]". { exact e3IN. } { iSteps. }
      iMod (OmoHb_new_3 with "M● psId⊒e3 [$]") as "[M● #psId⊒e3']".
      iExists (). iStep. iExists (length omo3). rewrite omo_insert_w_append_w; [|done].
      iDestruct (OmoLt_get_append_w (eventT := sevent_hist) with "[$] e3✓eV3") as "#e3<psId"; [by apply lookup_lt_Some in HeV3;lia|].
      iStep. iSplitR. { iApply big_sepS_subseteq; last by iApply @OmoUB_singleton. set_solver-. } iStep.

      iMod "AU2" as (????) "[H Close]". iDestruct (atomic.diaframe_close_right_quant with "Close") as "?". iDecompose "H" as (_) "??? M●3".
      iApply (fupd_mono _ _ _ _ (bi.sep_elim_r (χ) _)). iStep. iExists v3. rewrite decide_False;[|done]. iStep. iExists _, _. rewrite decide_False; [|lia].
      oSteps. iExists _. iSplitR. { iPureIntro. eapply stack_step_Pop; try done. rewrite app_length /=. instantiate (1 := {[length E3]} ∪ (M ∪ M0)). set_solver-. } iStep as (?) "????? M●".
      iMod (OmoHb_new_2 with "M● [] [$]") as "[M● #ppId⊒e3]". { exact e3IN. } { iSteps. }
      iMod (OmoHb_new_3 with "M● ppId⊒e3 [$]") as "[M●3 #ppId⊒e3']".
      iExists (). iStep. rewrite app_length /=. iExists (length (omo_append_w omo3 (length E3) [])). rewrite omo_insert_w_append_w; [|done].
      iDestruct (OmoLt_get_append_w (eventT := sevent_hist) with "[$] e3✓eV3") as "#e3<ppId"; [by apply lookup_lt_Some in HeV3;lia|].
      iStep. iSplitR. { iApply big_sepS_subseteq; last by iApply @OmoUB_singleton. set_solver-. } iStep as "HΦ".

      iStep. iSplitL "HΦ"; [done|]. iStep 2. iExists false. oSteps. iSplitR. { iApply OmoLe_get_from_Lt. iApply OmoLe_Lt_trans; done. }
      iStep. iExists false. oSteps. rewrite !app_length /=. iStep. iSplitR. { iApply OmoLe_get_from_Lt. iApply OmoLe_Lt_trans; done. }
      oSteps. iExists genzfl3. iSplitR.
      { apply eq_sym, lookup_lt_Some in H46 as ?. rewrite lookup_app_l; [|rewrite app_length /=; lia]. rewrite lookup_app_l; [done|]. lia. }
      iSteps. iPureIntro. set (stlist3' := stlist3 ++ [_]). intros ?? Hi1 Hi2. destruct (decide (i = length (stlist3'))) as [->|NEQ].
      -- rewrite lookup_app_1_eq in Hi1. inversion Hi1. subst. rewrite last_lookup in H40. eapply H47; [done|].
         rewrite -EQlenST3. apply lookup_omo_lt_Some in Heidx3. lia.
      -- rewrite lookup_app_1_ne in Hi1; [|done]. destruct (decide (i = length stlist3)) as [->|NEQ'].
         ++ rewrite lookup_app_1_eq in Hi1. inversion Hi1. done.
         ++ rewrite lookup_app_1_ne in Hi1; [|done]. eapply H47; done. }
  iDecompose "H". iStep. iExists None. oSteps. iExists true. iSteps.
  Unshelve. all: try pure_solver.trySolvePure.
  - iPureIntro. unfold hmap_valid. intros ? Hi. rewrite app_length /=. enough (e < length Ex3) by lia. eauto.
Qed.

#[local] Opaque EStackInv EStackLocal.

#[global] Instance push_spec :
  spec_elim_composition_diaframe.push_dspec' (push try_push' new_offer check_offer) EStackLocal EStackInv.
Proof using All.
  intros ??????. iStep 3. iLöb as "IH". iStep 10. { iStepsSafest. iRight. iSteps. }
  iIntros (b). destruct (b).
  - iStep. iAssert (⊒x1)%I as "?"; [iSteps|]. iSteps.
  - iStepsSafest. iRight. iSteps.
Qed.

#[global] Instance pop_spec :
  spec_elim_composition_diaframe.pop_dspec' (pop try_pop' take_offer) EStackLocal EStackInv.
Proof using All.
  intros ?????. iStep 3. iLöb as "IH". iStep 10. { iStepsSafest. iRight. iSteps. }
  iIntros (v). destruct (decide (v = (-1)%Z)) as [->|?]; last destruct (decide (v = 0)) as [->|?].
  - (* try_pop failed. retry *) iStepsSafest. iRight. iSteps.
  - (* Empty pop case *) iStep. iAssert (⊒x1)%I as "?"; [iSteps|]. iSteps. iExists 0. repeat iExists _. iSteps.
  - (* Value pop case *) iStep as "?? H". rewrite decide_False; [|done]. iDecompose "H". iAssert (⊒x1)%I as "?"; [iSteps|]. iSteps.
    iExists v. repeat iExists _. rewrite decide_False; [|done]. iStepsSafest. rewrite bool_decide_false; [|done]. iSteps.
Qed.
End Elimstack.

Definition elim_stack_impl `{!noprolG Σ, !atomicG Σ, !elimG Σ} (ts : stack_dspec Σ) (xc : xchg_dspec Σ)
  : spec_elim_composition_diaframe.stack_spec Σ := {|
    spec_elim_composition_diaframe.StackInv_Linearizable := EStackInv_Linearizable_instance;
    spec_elim_composition_diaframe.StackInv_OmoAuth_acc := EStackInv_OmoAuth_acc_instance;
    spec_elim_composition_diaframe.StackLocal_OmoEview := EStackLocal_OmoEview_instance ts xc;
    spec_elim_composition_diaframe.StackLocal_Eview_update := EStackLocal_Eview_update_instance ts xc;
    spec_elim_composition_diaframe.new_stack_dspec := new_stack_spec ts xc;
    spec_elim_composition_diaframe.try_push_dspec := try_push_spec ts xc;
    spec_elim_composition_diaframe.push_dspec := push_spec ts xc;
    spec_elim_composition_diaframe.try_pop_dspec := try_pop_spec ts xc;
    spec_elim_composition_diaframe.pop_dspec := pop_spec ts xc;
  |}.
