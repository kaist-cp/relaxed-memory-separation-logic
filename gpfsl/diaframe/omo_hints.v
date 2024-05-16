From diaframe Require Import proofmode_base own_hints.
From gpfsl.logic Require Import proofmode atomics invariants.
From gpfsl.base_logic Require Import meta_data.
From gpfsl.diaframe Require Import base_hints view_hints.
From Hammer Require Import Tactics.
From gpfsl.examples.omo Require Import omo omo_preds omo_preds_diaframe append_only_loc.
From gpfsl.examples.algebra Require Import mono_list_list.
From diaframe.steps Require Import namer_tacs.

Require Import iris.prelude.options.


Section hints.
Context `{!noprolG Σ, !atomicG Σ, !omoGeneralG Σ, !omoSpecificG Σ eventT2 absStateT2, !omoSpecificG Σ eventT absStateT}.
Context `{Interp2 : Interpretable eventT2 absStateT2}.
Context `{Interp : Interpretable eventT absStateT}.

#[local] Notation iProp := (iProp Σ).
#[local] Notation vProp := (vProp Σ).

#[global] Arguments omo_write_op _ : simpl never.

(* hints for OmoAuth, OmoEinfo, and snapshots *)
#[global] Instance mergable_persist_OmoAuth_take_snapshots γe γs q E omo stlist :
  MergablePersist ( OmoAuth γe γs q E omo stlist Interp) (λ p Pin Pout,
    TCAnd (TCEq Pin ( ε₀ )%I) $
        TCEq Pout (
          OmoSnapOmo γe γs omo ∗ OmoSnapHistory γe E
    )%I) | 500.
Proof.
  intros p Pin Pout [-> ->].
  rewrite bi.intuitionistically_if_elim.
  iIntros "[master _]".
  iDestruct (OmoSnapOmo_get with "master") as "#$".
  iDestruct (OmoSnapHistory_get with "master") as "#$".
Qed.


#[global] Instance mergable_consume_OmoAuth_snap_valid γe γs q E omo1 omo2 stlist :
  MergableConsume ( OmoAuth γe γs q E omo1 stlist Interp) true (λ p Pin Pout,
    TCAnd (TCEq Pin ( OmoSnapOmo γe γs omo2 )%I) $
      TCIf (TCEq omo1 omo2)
        (TCEq Pout (OmoAuth γe γs q E omo1 stlist Interp))
        (TCEq Pout ( ⌜omo_prefix omo2 omo1⌝ ∗ OmoAuth γe γs q E omo1 stlist Interp)))%I | 500.
Proof.
  intros p Pin Pout [-> [-> -> | ->]]; rewrite bi.intuitionistically_if_elim; [iSteps|].
  iIntros "[master snap]".
  iDestruct (OmoAuth_OmoSnapOmo with "master snap") as "#$". iFrame.
Qed.


#[global] Instance mergable_consume_OmoAuth_OmoSnapHistory γe γs q E1 E2 omo stlist :
  MergableConsume ( OmoAuth γe γs q E1 omo stlist Interp) true (λ p Pin Pout,
    TCAnd (TCEq Pin (OmoSnapHistory (eventT := eventT) γe E2)) $
    (* evar in proposition [_ ⊑ _] is causing strange interactions with set_unfold.... temporarily disabling the hint until we find out what's wrong. *)
        TCEq Pout ( (* ⌜E2 ⊑ E1⌝ ∗ *) OmoAuth γe γs q E1 omo stlist Interp)%I) | 500.
Proof.
  intros p Pin Pout [-> ->].
  rewrite bi.intuitionistically_if_elim.
  iIntros "[master snap]".
  iDestruct (OmoAuth_OmoSnapHistory with "master snap") as "%". iFrame.
Qed.

#[global] Instance mergable_consume_OmoEinfo_agree γe e eV eV' :
    MergableConsume (OmoEinfo γe e eV) false (λ p Pin Pout,
      TCAnd (TCEq Pin (OmoEinfo γe e eV')) $
            TCEq Pout (⌜eV = eV'⌝)%I).
Proof.
  rewrite /MergableConsume => p Pin Pout [-> ->].
  rewrite bi.intuitionistically_if_elim.
  iStep as "H1 H2".
  iDestruct (OmoEinfo_agree with "H1 H2") as %->. auto.
Qed.

(* simplifying omo_prefix *)
#[global] Instance destruct_omo_prefix omo1 omo2:
  SimplifyPureHypSafe (omo_prefix omo1 omo2) ((omo_read_op omo1 `prefixes_of` omo_read_op omo2) ∧ (omo_write_op omo1 `prefix_of` omo_write_op omo2)).
Proof. split; done. Qed.

#[global] Instance mergable_consume_OmoAuth_combine γe γs γs' q q' q'' E E' omo omo' stlist stlist' :
  MergableConsume ( OmoAuth γe γs q E omo stlist Interp) true (λ p Pin Pout,
      (TCAnd (TCEq Pin (OmoAuth γe γs' q' E' omo' stlist' _)) $
      TCAnd (IsOp q'' q q') $
        TCEq Pout (⌜γs = γs' ∧ E = E' ∧ omo = omo' ∧ stlist = stlist'⌝ ∗ OmoAuth γe γs' q'' E omo stlist _))
  )%I | 400.
Proof.
  intros p Pint Pout [-> [-> ->]]. rewrite bi.intuitionistically_if_elim.
  iIntros "[A B]". iDestruct (OmoAuth_agree with "A B") as "(-> & -> & -> & ->)". iCombine "A B" as "A". auto.
Qed.


#[global] Instance biabd_OmoAuth_divide γe γs q q' mq E omo stlist :
  FracSub q' q (Some mq) →
  HINT OmoAuth γe γs q' E omo stlist _ ✱ [-; emp]
  ⊫ [id]
  ; OmoAuth γe γs q E omo stlist _ ✱ [ OmoAuth γe γs mq E omo stlist _ ].
Proof. intros <-. iStep as "_ _ M●". iDestruct "M●" as "[A B]". iSteps. Qed.


#[global] Instance biabd_OmoAuth_join γe γs q q' p E omo stlist :
  FracSub q q' (Some p) →
  HINT OmoAuth γe γs q' E omo stlist _ ✱ [γs2 E2 omo2 stlist2; OmoAuth γe γs2 p E2 omo2 stlist2 _ ]
  ⊫ [id]
  ; OmoAuth γe γs q E omo stlist _ ✱ [ emp ].
Proof. intros <-. iSteps. Qed.


(* This helper resource comes first at the invariant to trigger the omo_mater update.
   We use this because the updated OmoAuth (or equivalent OmoHbToken) are often used
   to prove other parts of the invariant. *)
Definition try_update_OmoAuth_to_def (γe : gname) (E : omo_history.history eventT) (omo : omoT) (stlist : list absStateT) : vProp := emp%I.
Definition try_update_OmoAuth_to_aux : seal (@try_update_OmoAuth_to_def). Proof. by eexists. Qed.
Definition try_update_OmoAuth_to := try_update_OmoAuth_to_aux.(unseal).
#[global] Opaque try_update_OmoAuth_to.
#[global] Arguments try_update_OmoAuth_to _ _ _ _ : simpl never.
Lemma try_update_OmoAuth_to_eq : @try_update_OmoAuth_to = @try_update_OmoAuth_to_def.
Proof. rewrite -try_update_OmoAuth_to_aux.(seal_eq) //. Qed.

#[global] Instance mergable_consume_remove_try_update_OmoAuth_to γe E omo stlist :
  MergableConsume (try_update_OmoAuth_to γe E omo stlist) true (λ p Pin Pout,
    TCAnd (TCEq Pin (ε₀)) $
      TCEq Pout emp)%I.
Proof. intros p Pin Pout [-> ->]. iSteps. Qed.

#[global] Instance try_update_OmoAuth_to_objective γe E omo stlist : Objective (try_update_OmoAuth_to γe E omo stlist).
Proof. rewrite try_update_OmoAuth_to_eq. apply _. Qed.
#[global] Instance try_update_OmoAuth_to_timeless γe E omo stlist : Timeless (try_update_OmoAuth_to γe E omo stlist).
Proof. rewrite try_update_OmoAuth_to_eq. apply _. Qed.


Definition OmoAuth_do_update γe γs E omo stlist (eV : omo_event eventT) R : vProp :=
   OmoAuth γe γs 1 E omo stlist Interp  ==∗
    ∃ omo' stlist',
      OmoHbToken γe γs (E ++ [eV]) omo' stlist' (length E) _ ∗
      R omo' stlist'.


(* try_update rules *)
#[global] Instance biabd_OmoAuth_as_is γe γs q E omo omo' stlist stlist'  :
  let master := OmoAuth γe γs q E omo stlist _ in
  HINT master ✱ [-; ⌜omo' = omo ∧ stlist' = stlist⌝]
  ⊫ [id]
  (* Todo: omo' and stlist' to existential quantifier. *)
  ; try_update_OmoAuth_to γe E omo' stlist'✱ [ master ] | 10.
Proof. rewrite try_update_OmoAuth_to_eq => ?. iSteps. Qed.

#[global] Instance biabd_OmoAuth_start_update Mk γe γs q mp E eV omo stlist :
  FracSub 1 q mp →
  HINT OmoAuth γe γs q E omo stlist Interp ✱ [γs2 E2 omo2 stlist2 R;
    match mp with
    | Some p => OmoAuth γe γs2 p E2 omo2 stlist2 _
    | None => ⌜(γs2, E2, omo2, stlist2) = (γs, E, omo, stlist)⌝
    end ∗
    OmoAuth_do_update γe γs E omo stlist eV R ]
  ⊫ [fupd Mk Mk]
  omo'2 stlist'2; try_update_OmoAuth_to γe (E ++ [eV]) omo'2 stlist'2 ✱ [
    ∃ omo' stlist',
      R omo' stlist' ∗
      ⌜ omo'2 = omo' ∧ stlist'2 = stlist' ⌝ ∗
      OmoHbToken γe γs (E ++ [eV]) omo' stlist' (length E) _ ] | 700.
Proof.
  rewrite /OmoAuth_do_update try_update_OmoAuth_to_eq => HSub. iStep 6 as (?????) "_ _ M●1 M●2 upd".
  iMod ("upd" with "[-]") as "H".
  { destruct mp; first iSteps. rewrite HSub. iSteps. }
  iDecompose "H". iSteps.
Qed.

(* Actual updates *)
#[global] Instance biabd_OmoAuth_insert_last Mk γe1 γe2 γs1 E1 omo1 stlist1 eV e' :
  let Vb := eV.(sync) in
  let e := length E1 in
  HINT OmoTokenW γe2 e' ✱ [ M1 st st' ;
    ⌜ Some st = last stlist1 ⌝ ∗
    ⌜ eV.(eview) = {[e]} ∪ M1 ⌝ ∗
    ⌜ omo.step e eV st st' ⌝ ∗
    @{Vb} (OmoEview γe1) M1
  ]
  ⊫ [fupd Mk Mk]
  R; OmoAuth_do_update γe1 γs1 E1 omo1 stlist1 eV R ✱ [
  ⌜ R = (λ omo1' stlist1',
    ⌜ omo1' = omo_append_w omo1 e [] ⌝ ∗
    ⌜ stlist1' = stlist1 ++ [st'] ⌝ ∗
    OmoEinfo γe1 e eV ∗
    OmoCW γe1 γe2 e e' ∗
    OmoSnap γe1 γs1 e st' ∗
    OmoTokenW γe1 e) ⌝
  ] | 700.
Proof.
  intros. rewrite /OmoAuth_do_update /BiAbd /=.
  iIntros (M1 st st') "(WCOMMIT & %eq_st & %omo_step & %eq_eview_eV & M1◯)".
  iExists _. iSplitL; last done. iStep as "_ _ M1●".
  iMod (OmoAuth_insert_last  with "M1● [M1◯] WCOMMIT []") as "(M1● & #M1◯' & #e↦e' & #e✓eV & #e↪st' & WCOMMIT')"; [done..|].
  iSteps.
Qed.


#[global] Instance biabd_OmoAuth_insert_ro Mk γe γe' γs1 E1 omo1 stlist1 eV e' :
  let Vb := eV.(sync) in
  let en := length E1 in
  HINT OmoTokenR γe' e' ✱ [M st e;
    ⌜ eV.(eview) = {[en]} ∪ M ⌝ ∗
    ⌜ omo.step en eV st st ⌝ ∗
    @{Vb} OmoEview γe M ∗
    OmoSnap γe γs1 e st ∗
    OmoUB γe M e
  ]
  ⊫ [fupd Mk Mk]
  R; OmoAuth_do_update γe γs1 E1 omo1 stlist1 eV R ✱ [
    ⌜ R = (λ omo1' stlist1',
      ∃ gen eidx,
      ⌜ omo1' = (omo_insert_r omo1 gen en) ⌝ ∗
      ⌜ stlist1' = stlist1 ⌝ ∗
      OmoCW γe γe' en e' ∗
      OmoEq γe e en ∗
      OmoEinfo γe en eV ∗
      OmoTokenR γe en ∗
      ⌜ lookup_omo (omo_insert_r omo1 gen en) eidx = Some en ∧ gen = gen_of eidx ⌝)%I ⌝
  ] | 700.
Proof.
  intros. rewrite /OmoAuth_do_update /BiAbd /=.
  iIntros (M st e) "(RCOMMIT & % & % & M◯ & e↪st & MAXgen_e)".
  iExists _. iSplitL; last done.
  iSteps as "_ _ M●".
  iMod (OmoAuth_insert_ro with "M● M◯ RCOMMIT e↪st MAXgen_e []")
    as (gen) "(M● & #M◯ & #en↦e' & #e=en & #en✓eV & RCOMMIT & %eidx & %eidx_lookup & %eidx_gen)"; [done|].
  iSteps.
Qed.

#[global] Instance biabd_OmoAuth_insert_ro_gen Mk γe γe' γs1 E1 omo1 stlist1 eV e' gen :
  let Vb := eV.(sync) in
  let en := length E1 in
  HINT OmoTokenR γe' e' ✱ [M st;
    ⌜ eV.(eview) = {[en]} ∪ M ⌝ ∗
    ⌜ omo.step en eV st st ⌝ ∗
    ⌜ stlist1 !! gen = Some st ⌝ ∗
    ⌜ OmoUBgen omo1 M gen ⌝ ∗
    @{Vb} OmoEview γe M
  ]
  ⊫ [fupd Mk Mk]
  RR; OmoAuth_do_update γe γs1 E1 omo1 stlist1 eV RR ✱ [
    ⌜ RR = (λ omo1' stlist1',
      ⌜ omo1' = (omo_insert_r omo1 gen en) ⌝ ∗
      ⌜ stlist1' = stlist1 ⌝ ∗
      OmoCW γe γe' en e' ∗
      OmoEinfo γe en eV ∗
      OmoTokenR γe en)%I ⌝
  ] | 400.
Proof.
  intros. rewrite /OmoAuth_do_update /BiAbd /=.
  iIntros (M st) "(RCOMMIT & %&%&%&%& M◯)".
  iExists _. iSplitL; [|done]. iSteps as "??M●".
  iMod (OmoAuth_insert_ro_gen with "M● M◯ RCOMMIT []") as "H"; [done|]. iSteps.
Qed.


#[global] Instance biabd_remove_later_from_try_update_OmoAuth_to γe E :
  HINT ε₀ ✱ [omo stlist; try_update_OmoAuth_to γe E omo stlist ]
  ⊫ [id]
  omo' stlist'; ▷ try_update_OmoAuth_to γe E omo' stlist' ✱ [ ⌜ omo' = omo ∧ stlist' = stlist ⌝].
Proof. rewrite try_update_OmoAuth_to_eq. iSteps. Qed.


#[global] Instance biabd_emo_seen_event_reg_token_destroy γe γs p oq E omo stlist e :
  FracSub 1 p oq →
  HINT OmoHbToken γe γs E omo stlist e _ ✱ [-; emp]
  ⊫ [id]
  ; OmoAuth γe γs p E omo stlist _ ✱ [
      match oq with
      | Some q => OmoAuth γe γs q E omo stlist _
      | None => OmoSnapOmo γe γs omo ∗ OmoSnapHistory γe E
      end ].
Proof.
  iStep 2 as (Hsub) "A".
  iDestruct (OmoHbToken_finish with "A") as "A".
  destruct oq.
  - iSteps.
  - iDecompose "A". rewrite Hsub. iSteps.
Qed.


(*

TODO: the Omo lemma has changed for this agreement has changed, now also needing an [append_only_loc].
  This mergableconsume would thus require also to look for that resource.
  This is problematic for Diaframe, since the [append_only_loc] will be consumed as precondition for writes.
  I was not able to make this work, there are also some non-trivial interactions with views going on there.
  The proof of spinlock release now manually opens the invariant
#[global] Instance mergable_persist_OmoAuth_swriter_token_agree_obj γl γs q E omo mo V l es `{!appendOnlyLocG Σ} V2 uf ty :
  MergableConsume (@OmoAuth loc_event _ _ _ _ γl γs q E omo mo _) true (λ p Pin Pout,
    TCAnd (TCEq Pin (@{V} swriter_token l γl es)) $
      TCEq Pout (⌜es = omo_write_op omo⌝ ∗ OmoAuth γl γs q E omo mo _ ∗ @{V} swriter_token l γl es))%I.
Proof.
  intros p Pin Pout [-> ->]. rewrite bi.intuitionistically_if_elim. iIntros "[??]".
  iDestruct (OmoAuth_swriter_token_agree_obj_1 with "[$] [$] [$]") as "%". iSteps.
Qed. *)

(*
#[global] Instance mergable_persist_swriter_token_type_obj V1 V2 l γl es uf ty :
  MergablePersist (PROP := vProp) (@{V2} append_only_loc l γl uf ty) (λ p Pin Pout,
  TCAnd (TCEq Pin (@{V1} swriter_token l γl es)) $
    TCEq Pout (⌜ty = swriter⌝))%I.
Proof.
  intros p Pin Pout [-> ->]. rewrite bi.intuitionistically_if_elim. iIntros "[A B]".
  iDestruct (swriter_token_type_obj_1 with "B A") as "->". auto.
Qed. *)

Definition CWMonoValid_from_CWMono γe γe' γm M e e' R : vProp :=
  CWMono γe γe' γm M -∗
  OmoCW γe γe' e e'
  ==∗ CWMonoValid γm e ∗ R.

Definition CWMonoValid_try_insert_last `{omoSpecificG Σ eventT0 absStateT0} γe γe' γm γs' M e e' q' E' omo' stlist' (Interp: Interpretable eventT0 absStateT0) R : vProp :=
  CWMono γe γe' γm M -∗
  OmoCW γe γe' e e' -∗
  OmoAuth γe' γs' q' E' (omo_append_w omo' e' []) stlist' Interp
  ==∗
    CWMonoValid γm e ∗ R.

#[global] Instance biabd_start_search_for_CWMonoValid Mk γm e :
  HINT ε₁ ✱ [γe γe' e' M R;
    CWMono γe γe' γm M ∗
    OmoCW γe γe' e e' ∗
    CWMonoValid_from_CWMono γe γe' γm M e e' R]
  ⊫ [fupd Mk Mk]
  ; CWMonoValid γm e ✱ [ R ].
Proof. iSteps. Qed.

#[global] Instance biabd_emap_mono_try_insert_last γe γe' γm M e e' omo' γs' q' E' stlist' :
  HINT OmoAuth γe' γs' q' E' (omo_append_w omo' e' []) stlist' Interp2 ✱ [R2;
    CWMonoValid_try_insert_last γe γe' γm γs' M e e' q' E' omo' stlist' _ R2
  ]
  ⊫ [id]
  R1; CWMonoValid_from_CWMono γe γe' γm M e e' R1 ✱ [ ⌜ R1 = R2 ⌝ ].
Proof.
  iSteps. iExists _. iSplitL; [|done]. iSteps.
Qed.

#[global] Instance biabd_CWMono_insert_last_last_write γe γe' γm γs γs' M e e' q' E E' omo omo' stlist stlist' el :
  HINT OmoHbToken γe γs E omo stlist el Interp ✱ [-;
    ⌜ Some e = lookup_omo omo (wr_event (length omo - 1))⌝
    (* Todo: this pure condition is being shelved. Maybe we should use SolveSepCondition with MatchValue(to allow rewrites) to
      control whether this hint should be applied.
      Todo: maybe we should just ask_for what event should the mono be induced from. *)
    ]
  ⊫ [id]
  R; CWMonoValid_try_insert_last γe γe' γm γs' M e e' q' E' omo' stlist' Interp2 R ✱ [ ⌜R =
    (CWMono γe γe' γm ({[e]} ∪ M) ∗
    OmoAuth γe' γs' q' E' (omo_append_w omo' e' []) stlist' Interp2 ∗
    OmoHbToken γe γs E omo stlist el Interp)⌝
    ].
Proof.
  iStep 2 as (?) "M●". iExists _. iSplitL; [|done].
  iStep 3 as "e↦e' Mono M'●".
  iMod (CWMono_insert_last_last_from_HbToken_1 (wr_event (length omo - 1)) with "Mono M● M'● e↦e'") as "($ & $ & $ & $)"; done.
Qed.

#[global] Instance biabd_CWMono_insert_last_last_write' γe γe' γm γs γs' M e e' q q' E E' omo omo' stlist stlist' :
  HINT OmoAuth γe γs q E omo stlist Interp ✱ [-;
    ⌜ Some e = lookup_omo omo (wr_event (length omo - 1))⌝
    ]
  ⊫ [id]
  R; CWMonoValid_try_insert_last γe γe' γm γs' M e e' q' E' omo' stlist' Interp2 R ✱ [ ⌜R =
    (CWMono γe γe' γm ({[e]} ∪ M) ∗
    OmoAuth γe' γs' q' E' (omo_append_w omo' e' []) stlist' Interp2 ∗
    OmoAuth γe γs q E omo stlist Interp)⌝
    ].
Proof.
  iStep 2 as (?) "_ _ M●". iExists _. iSplitL; [|done].
  iStep 3 as "e↦e' Mono M'●".
  iMod (CWMono_insert_last_last (wr_event (length omo - 1)) with "Mono M● M'● e↦e'") as "($ & $ & $ & $)"; done.
Qed.


#[global] Instance biabd_CWMono_insert_Eq γe γe' γm M e2 e2' :
  HINT ε₁ ✱ [e1 e1'; ask_for e1 ∗
    OmoEq γe e1 e2 ∗
    CWMonoValid γm e1 ∗
    OmoCW γe γe' e1 e1' ∗
    OmoEq γe' e1' e2']
  ⊫ [id]
  R; CWMonoValid_from_CWMono γe γe' γm M e2 e2' R ✱ [ ⌜R =
    CWMono γe γe' γm ({[e2]} ∪ M)⌝ ].
Proof.
  iStep 4. iExists _. iSplitL; last done. iStep 2 as "? Mono".
  iMod (CWMono_insert_Eq with "Mono [$] [$] [$] [] []") as "[$ $]"; [iSteps..|]. done.
Qed.


(* We use below definition to hide M ≠ ∅ from automatic solvers, especially set_solver.
  If a pure M ≠ ∅ is in the context, solvers will try to use this to prove False goal, taking much time to fail. *)
Definition eView_not_empty (M : eView) := M ≠ ∅.
Definition OmoEview_or_empty γe M : vProp := ⌜ eView_not_empty M ⌝ -∗ OmoEview γe M.

#[global] Instance OmoEview_or_empty_persistent γe M : Persistent (OmoEview_or_empty γe M) := _.
#[global] Instance OmoEview_or_empty_timeless γe M : Timeless (OmoEview_or_empty γe M) := _.

#[global] Instance mergable_consume_destruct_OmoEview γe M :
  MergableConsume (OmoEview γe M) true (λ p Pin Pout,
    TCAnd (TCEq Pin (ε₀)) $
      TCEq Pout (⌜ eView_not_empty M ⌝ ∗ OmoEview_or_empty γe M))%I.
Proof.
  intros p Pin Pout [-> ->]. rewrite bi.intuitionistically_if_elim.
  iStep. iDestruct (OmoEview_nonempty with "[$]") as "%". iSteps.
Qed.


#[global] Instance mergable_consume_destruct_OmoEview_obj V γe M :
  MergableConsume (@{V} OmoEview γe M) true (λ p Pin Pout,
    TCAnd (TCEq Pin (ε₀)) $
      TCEq Pout (⌜ eView_not_empty M ⌝ ∗ @{V} OmoEview_or_empty γe M))%I.
Proof.
  intros p Pin Pout [-> ->]. rewrite bi.intuitionistically_if_elim.
  iStep. iDestruct (OmoEview_nonempty_obj with "[$]") as "%". iSteps.
Qed.


#[local] Lemma OmoEview_or_empty_empty γe :
  ⊢ OmoEview_or_empty γe ∅.
Proof. iIntros "% //". Qed.

#[global] Lemma OmoEview_or_empty_mono γe M1 M2 :
  M1 ⊑ M2 →
  OmoEview_or_empty γe M2 -∗ OmoEview_or_empty γe M1.
Proof.
  iIntros (?) "A %". unfold OmoEview_or_empty.
  iApply OmoEview_mono; [done..|]. iApply "A". iPureIntro. unfold eView_not_empty in *. set_solver.
Qed.

#[local] Lemma eView_not_empty_join M1 M2 : eView_not_empty M1 ∨ eView_not_empty M2 → eView_not_empty (M1 ∪ M2).
Proof. unfold eView_not_empty. set_solver. Qed.

#[local] Lemma OmoEview_or_empty_union γe M1 M2 :
  OmoEview_or_empty γe M1 ∗ OmoEview_or_empty γe M2 ⊣⊢ OmoEview_or_empty γe (M1 ⊔ M2).
Proof.
  iSplit.
  - iIntros "#[A B]". destruct (decide (M1 = ∅)) as [Eq1|Neq1], (decide (M2 = ∅)) as [Eq2|Neq2].
    1, 2, 3: (have [->|->]: (M1 ⊔ M2 = M1 ∨ M1 ⊔ M2 = M2) by set_solver); done.
    unfold OmoEview_or_empty. iIntros (?). iApply OmoEview_union; iSteps.
  - iIntros "#A". destruct (decide (M1 = ∅)) as [->|Neq1], (decide (M2 = ∅)) as [->|Neq2].
    all: iSplit; try iApply OmoEview_or_empty_empty.
    3, 4: iApply (OmoEview_or_empty_mono with "A"); solve_lat.
    + by have -> : (∅ ⊔ M2 = M2) by set_solver-.
    + by have -> : (M1 ⊔ ∅ = M1) by set_solver-.
Qed.

(* #[local] Lemma OmoEview_or_empty_union_obj V γe M1 M2 :
  @{V} OmoEview_or_empty γe M1 ∗ @{V} OmoEview_or_empty γe M2 ⊣⊢ @{V} OmoEview_or_empty γe (M1 ⊔ M2).
Proof.
  rewrite -view_at_sep OmoEview_or_empty_union. done.
Qed. *)

#[global] Instance mergable_consume_divide_eView γe M1 M2 :
  MergableConsume (OmoEview_or_empty γe (M1 ⊔ M2)) true (λ p Pin Pout,
    TCAnd (TCEq Pin (ε₀)) $
      TCEq Pout (OmoEview_or_empty γe M1 ∗ OmoEview_or_empty γe M2))%I.
Proof.
  intros p Pin Pout [-> ->]. rewrite bi.intuitionistically_if_elim.
  iStep. rewrite -OmoEview_or_empty_union //.
Qed.

#[global] Instance mergable_consume_divide_eView_obj V γe M1 M2 :
  MergableConsume (@{V} OmoEview_or_empty γe (M1 ⊔ M2)) true (λ p Pin Pout,
    TCAnd (TCEq Pin (ε₀)) $
      TCEq Pout (@{V} OmoEview_or_empty γe M1 ∗ @{V} OmoEview_or_empty γe M2))%I.
Proof.
  intros p Pin Pout [-> ->]. rewrite bi.intuitionistically_if_elim.
  iStep. rewrite -OmoEview_or_empty_union. by iApply view_at_sep.
Qed.

#[global] Instance biabd_OmoEview_or_empty_union γe M1 M2 :
  TCOr (SolveSepSideCondition (M1 = M1)) (SolveSepSideCondition (M2 = M2)) →
  HINT ε₀ ✱ [-; OmoEview_or_empty γe M1 ∗ OmoEview_or_empty γe M2]
  ⊫ [id]
  ; OmoEview_or_empty γe (M1 ∪ M2) ✱ [ emp ].
Proof.
  intros _. rewrite -OmoEview_or_empty_union. iStep. iFrame "#".
Qed.

#[global] Instance biabd_OmoEview_or_empty_union_obj V γe M1 M2 :
  TCOr (SolveSepSideCondition (M1 = M1)) (SolveSepSideCondition (M2 = M2)) →
  HINT ε₀ ✱ [-; @{V} OmoEview_or_empty γe M1 ∗ @{V} OmoEview_or_empty γe M2]
  ⊫ [id]
  ; @{V} OmoEview_or_empty γe (M1 ∪ M2) ✱ [ emp ].
Proof.
  intros _. rewrite -OmoEview_or_empty_union. iSteps.
Qed.

#[global] Instance biabd_OmoEview_from_or_empty γe M :
  HINT ε₀ ✱ [-; OmoEview_or_empty γe M ∗ ⌜ eView_not_empty M ⌝]
  ⊫ [id]
  ; OmoEview γe M ✱ [ emp ].
Proof. iSteps. Qed.

#[global] Instance biabd_OmoEview_from_or_empty_obj V γe M :
  HINT ε₀ ✱ [-; @{V} OmoEview_or_empty γe M ∗ ⌜ eView_not_empty M ⌝]
  ⊫ [id]
  ; @{V} OmoEview γe M ✱ [ emp ].
Proof. iStep. iSplit; last done. iApply view_at_wand; done. Qed.


#[local] Typeclasses Opaque OmoEview_or_empty.

#[global] Instance biabd_OmoEview_or_empty_from_obj γe M :
  HINT ε₁ ✱ [V; ⊒V ∗ @{V} OmoEview_or_empty γe M]
  ⊫ [id]
  ; OmoEview_or_empty γe M ✱ [ emp ].
Proof. iSteps. Qed.

#[global] Instance biabd_OmoEview_or_empty_get_from_Einfo_1 p V γe e eV M :
  SolveSepSideCondition (V = V ∧ M = M) →
  TCEq M {[e]} →
  HINT □⟨ p ⟩ OmoEinfo γe e eV ✱ [-;
    ⌜ eV.(sync) ⊑ V ⌝
  ]
  ⊫ [id]
  ; @{V} OmoEview_or_empty γe M ✱ [ emp ].
Proof.
  intros _ ->. iStep as (?) "elem". rewrite bi.intuitionistically_if_elim.
  iDestruct (OmoEview_get_from_Einfo with "elem") as "H". iDecompose "H". iSteps.
Qed.

Lemma check_from_Einfo_1_M_unknown_blocked γe e eV :
  OmoEinfo γe e eV -∗
  ∃ M, @{eV.(sync)} OmoEview γe M.
Proof. iSteps. Abort.

Lemma check_from_Einfo_1_2 γe e eV :
  OmoEinfo γe e eV -∗
  @{eV.(sync)} OmoEview γe {[e]}.
Proof. iSteps. unfold eView_not_empty. iPureIntro. set_solver-. Qed.

#[global] Instance biabd_OmoEview_or_empty_new_from_Einfo_2 p V γe e et V' lv M :
  SolveSepSideCondition (V = V ∧ M = M) →
  TCEq M lv →
  HINT □⟨ p ⟩ OmoEinfo γe e (mkOmoEvent et V' lv) ✱ [-;
    ⌜ V' ⊑ V ⌝
  ]
  ⊫ [id]
  ; @{V} OmoEview_or_empty γe M ✱ [ emp ].
Proof.
  intros _ ->. iStep as (?) "elem". rewrite bi.intuitionistically_if_elim.
  iDestruct (OmoEview_get_from_Einfo with "elem") as "H". iDecompose "H". iSteps.
Qed.

#[global] Instance biabd_OmoEview_or_empty_new_from_Einfo_2' p V γe e eV M :
  SolveSepSideCondition (V = V ∧ M = M) →
  TCEq M (eview eV) →
  HINT □⟨ p ⟩ OmoEinfo γe e eV ✱ [-;
    ⌜ eV.(sync) ⊑ V ⌝
  ]
  ⊫ [id]
  ; @{V} OmoEview_or_empty γe M ✱ [ emp ].
Proof.
  intros _ ->. destruct eV. iStep. rewrite bi.intuitionistically_if_elim. iSteps.
Qed.


#[local] Remove Hints biabd_OmoEview_from_or_empty mergable_consume_destruct_OmoEview_obj : typeclass_instances.

#[global] Instance biabd_OmoHb_new Mk γe γe' e e' γs E omo stlist :
  HINT OmoHbToken γe γs E omo stlist e _ ✱ [eV;
    OmoEinfo γe e eV ∗
    @{eV.(sync)} OmoEview γe' {[ e' ]} ]
  ⊫ [fupd Mk Mk]
  ; OmoHb γe γe' e e' ✱ [ OmoHbToken γe γs E omo stlist e _ ].
Proof.
  iStep 2 as (?) "elem ◯e' M●".
  iMod (OmoHb_new_2 with "[$] [$] [$]") as "[$ $]"; [set_solver-|done].
Qed.


End hints.

Section hints_OmoGid.
Context {absStateT : Type}.
Context {Σ : gFunctors} `{!omoGeneralG Σ}.

Notation iProp := (iProp Σ).
Notation vProp := (vProp Σ).

#[global] Instance mergable_consume_OmoGid_agree γe e gid gid' :
  MergableConsume (PROP := vProp) (OmoGid γe e gid) false (λ p Pin Pout,
    TCAnd (TCEq Pin (OmoGid γe e gid')) $
      TCEq Pout ⌜gid = gid'⌝%I).
Proof.
  intros p Pin Pout [-> ->].
  rewrite bi.intuitionistically_if_elim.
  iIntros "[A B]".
  iDestruct (OmoGid_agree with "A B") as %->. done.
Qed.


#[global] Instance destruct_OmoEq γe e1 e2 :
  MergableConsume (@OmoEq Σ _ γe e1 e2) true (λ p Pin Pout,
    TCAnd (TCEq Pin empty_hyp_first) $
      TCEq Pout (∃ gid, OmoGid γe e1 gid ∗ OmoGid γe e2 gid)%I
  ).
Proof.
  intros p Pin Pout [-> ->].
  rewrite OmoEq_internal.
  iSteps.
Qed.

(* #[global] Instance destruct_OmoLe γe e1 e2 :
  MergableConsume (@OmoLe Σ γe e1 e2) true (λ p Pin Pout,
    TCAnd (TCEq Pin empty_hyp_first) $
      TCEq Pout (∃ gid1 gid2, OmoGid γe e1 gid1 ∗ OmoGid γe e2 gid2 ∗ ⌜ (gid1 ≤ gid2)%Qp ⌝)%I
  ).
Proof.
  intros p Pin Pout [-> ->].
  rewrite OmoLe_internal.
  iSteps.
Qed.

#[global] Instance destruct_OmoLt γe e1 e2 :
  MergableConsume (@OmoLt Σ γe e1 e2) true (λ p Pin Pout,
    TCAnd (TCEq Pin empty_hyp_first) $
      TCEq Pout (∃ gid1 gid2, OmoGid γe e1 gid1 ∗ OmoGid γe e2 gid2 ∗ ⌜ (gid1 < gid2)%Qp ⌝)%I
  ).
Proof.
  intros p Pin Pout [-> ->].
  rewrite OmoLt_internal.
  iSteps.
Qed. *)

#[global] Instance biabd_OmoEq_from_Gid γe e1 e2 :
  HINT ε₀ ✱ [gid; OmoGid γe e1 gid ∗ OmoGid γe e2 gid]
  ⊫ [id]
  ; @OmoEq Σ _ γe e1 e2 ✱ [ emp ] | 10.
Proof. iStep 2. iSplitL; [|done]. iApply OmoEq_from_Gid; done. Qed.

(* #[global] Instance biabd_OmoLe_from_Gid γe e1 e2 :
  HINT ε₀ ✱ [gid1 gid2; OmoGid γe e1 gid1 ∗ OmoGid γe e2 gid2 ∗ ⌜gid1 ≤ gid2⌝%Qp ]
  ⊫ [id]
  ; @OmoLe Σ γe e1 e2 ✱ [ emp ] | 10.
Proof. iStep 3. iSplitL; [|done]. iApply OmoLe_from_Gid; done. Qed.

#[global] Instance biabd_OmoLt_from_Gid γe e1 e2 :
  HINT ε₀ ✱ [gid1 gid2; OmoGid γe e1 gid1 ∗ OmoGid γe e2 gid2 ∗ ⌜gid1 < gid2⌝%Qp ]
  ⊫ [id]
  ; @OmoLt Σ γe e1 e2 ✱ [ emp ] | 10.
Proof. iStep 3. iSplitL; [|done]. iApply OmoLt_from_Gid; done. Qed. *)


#[global] Instance mergable_consume_OmoCW_agree_1 γe γe' γe'' e e' e'':
  MergableConsume (PROP := vProp) (OmoCW γe γe' e e') false (λ p Pin Pout,
    TCAnd (TCEq Pin (OmoCW γe γe'' e e'')) $
      TCEq Pout ⌜ γe' = γe'' ∧ e' = e'' ⌝%I).
Proof.
  intros p Pin Pout [-> ->].  rewrite bi.intuitionistically_if_elim.
  iIntros "[A B]". iDestruct (OmoCW_agree_1 with "A B") as "$".
Qed.


#[global] Instance mergable_consume_OmoCW_agree_2 γe1 γe2 γe' e1 e2 e' :
  MergableConsume (PROP := vProp) (OmoCW γe1 γe' e1 e') false (λ p Pin Pout,
    TCAnd (TCEq Pin (OmoCW γe2 γe' e2 e')) $
      TCEq Pout ⌜ γe1 = γe2 ∧ e1 = e2 ⌝%I).
Proof.
  intros p Pin Pout [-> ->].  rewrite bi.intuitionistically_if_elim.
  iIntros "[A B]". iDestruct (OmoCW_agree_2 with "A B") as "$".
Qed.

#[global] Instance mergable_consume_OmoGidState_agree γe γs gid st st' `{!omoSpecificG Σ eventT absStateT} :
    MergableConsume (@OmoGidState _ _ _ _ _ γe γs gid st) false (λ p Pin Pout,
      TCAnd (TCEq Pin (OmoGidState γe γs gid st')) $
            TCEq Pout (⌜st = st'⌝)%I).
Proof.
  intros p Pin Pout [-> ->]. rewrite bi.intuitionistically_if_elim.
  iStep as "H1 H2".
  iDestruct (OmoGidState_agree with "H1 H2") as %->. auto.
Qed.

#[global] Instance destruct_OmoSnap γe γs e st `{!omoSpecificG Σ eventT absStateT} :
  MergableConsume (OmoSnap γe γs e st) true (λ p Pin Pout,
    TCAnd (TCEq Pin empty_hyp_first) $
      TCEq Pout (∃ gid, OmoGid γe e gid ∗ OmoGidState γe γs gid st)%I
  ).
Proof.
  intros p Pin Pout [-> ->].
  rewrite OmoSnap_internal.
  iSteps.
Qed.

#[global] Instance biabd_OmoSnap_from_GidState_e_known γe γs e st `{!omoSpecificG Σ eventT absStateT} :
  HINT ε₀ ✱ [gid; OmoGid γe e gid ∗ OmoGidState γe γs gid st]
  ⊫ [id]
  ; OmoSnap γe γs e st ✱ [ emp ].
Proof. iStep 3. iSplitL; [|done]. iApply OmoSnap_from_GidState; done. Qed.


#[global] Instance biabd_OmoSnap_from_GidState_e_unknown γe γs st `{!omoSpecificG Σ eventT absStateT} :
  HINT ε₀ ✱ [gid e2; OmoGidState γe γs gid st ∗ OmoGid γe e2 gid ]
  ⊫ [id]
  e; OmoSnap γe γs e st ✱ [ ⌜ e = e2 ⌝ ].
Proof. iSteps. Qed.


End hints_OmoGid.


(* This form appears as an result of `biabd_CWMono_insert_last_last_write` hint. *)
Definition add_1_minus_1 x :
  x + 1 - 1 = x.
Proof. lia. Qed.

#[local] Lemma omo_write_op_length_rev omo:
 length (omo_write_op omo) = length omo.
Proof. rewrite omo_write_op_length //. Qed.

Lemma omo_specs_decide_True {A : Type} (x y : A) :
  (if decide (true = true ∧ swriter = swriter) then x else y) = x.
Proof. apply decide_True. done. Qed.

Lemma omo_specs_decide_False {A : Type} (x y : A) :
  (if decide (true = true ∧ cas_only = swriter) then x else y) = y.
Proof. apply decide_False. unfold not. intros [_ ?]. done. Qed.

Definition omo_rewrite_hints := (
  omo_insert_r_write_op, omo_insert_r_length,  omo_append_w_length, omo_append_w_write_op, omo_write_op_length_rev(*, Z2Nat.inj_0*),
  Nat.add_0_r, Nat.add_0_l, @shift_0, @last_app, @list_lookup_fmap, @lookup_app_1_eq, add_1_minus_1, @omo_specs_decide_True, @omo_specs_decide_False).

Import automation_state pure_solver_utils disj_chooser_tacs.

Ltac safeSolveStep :=
  ltac2:(
    let (state, gid) := automation_state.new () in
    let _ := solveStepWithOptTacs chooser_safest handle__shelve_unsolved_noevars state gid in
    ()
  ).
Ltac oSteps := iStepsSafest; repeat (rewrite !omo_rewrite_hints; try iStepsSafest).

#[global] Remove Hints biabd_OmoAuth_insert_ro_gen : typeclass_instances.
#[global] Hint Extern 30 (eView_not_empty (?M1 ∪ ?M2)) => (eapply eView_not_empty_join; pure_solver.trySolvePure) : solve_pure_add.
#[global] Hint Extern 50 (eView_not_empty _) => fast_done || (unfold eView_not_empty; set_solver-) : solve_pure_add.
#[global] Typeclasses Opaque OmoAuth_do_update CWMonoValid_try_insert_last CWMonoValid_from_CWMono eView_not_empty OmoEview_or_empty.
#[global] Opaque OmoAuth_do_update CWMonoValid_try_insert_last CWMonoValid_from_CWMono OmoEview_or_empty.
#[global] Opaque OmoAuth OmoEinfo OmoEview OmoHbToken OmoSnapHistory OmoSnapOmo OmoCW CWMono CWMonoValid
 OmoTokenR OmoTokenW OmoLe OmoLt OmoEq OmoHb OmoHbs HbIncluded OmoSnap
 OmoSnapStates.
