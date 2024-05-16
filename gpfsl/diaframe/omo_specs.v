From gpfsl.base_logic Require Export weakestpre.
From gpfsl.logic Require Import lifting proofmode atomics invariants.
From diaframe Require Import proofmode_base lib.except_zero tele_utils.
From diaframe.symb_exec Require Import defs.
From gpfsl.base_logic Require Import na meta_data.

From gpfsl.examples.omo Require Import omo omo_preds append_only_loc.
From gpfsl.diaframe Require Import vprop_weakestpre spec_notation vprop_weakestpre_logatom atom_spec_notation inv_hints base_hints view_hints.
From Hammer Require Import Tactics.

Require Import iris.prelude.options.


Section omo_specs.
  Context `{!noprolG Σ, !atomicG Σ, !omoGeneralG Σ, !appendOnlyLocG Σ}.

#[local] Typeclasses Transparent sqsubseteq.

#[global] Instance append_only_loc_relaxed_read_no_fence_spec_sepL_access E1 E2 l  :
  SPEC [ ε₁ ] ⟨E1, E2⟩ (V : view) γl γs mo omo oM M (E : history loc_event) nc ty Vb Φ (do_access : bool),
    {{
      ▷(@{Vb} append_only_loc l γl nc ty ∗
        ask_optional oM M ∗
        OmoEview γl M ∗
        OmoAuth γl γs (1/2) E omo mo loc_interpretable) ∗
        If do_access ([∗ list] gen'↦e ∈ (omo_write_op omo), Φ gen' e) ∗
        do_intro_view_forall ∗
        ⊒V ∗
        ⌜↑histN ⊆ E2⌝ }}
    !ʳˡˣ#l
    {{ (e : event_id) (gen : nat) (v' : val) (V' : view) (V'' : view_bi_index)
        (eV eV': omo_event loc_event) eV'_eview, RET v';
      let En := E ++ [eV'] in
      let en := length E in
      let omon := omo_insert_r omo gen en in
      ∃ writes,
        MatchValue writes (omo_write_op omo) ∗
        MatchValue (Some e) (writes !! gen) ∗
        ⌜ eV' = mkOmoEvent (ReadE (v', V')) V'' eV'_eview ∧
        V ⊑ V''⌝ ∗
        OmoEinfo γl e eV ∗
        MatchValue (v', V') (loc_event_msg (type eV)) ∗
        OmoEinfo γl en eV' ∗
        OmoAuth γl γs (1/2) En omon mo loc_interpretable ∗
        OmoTokenR γl en ∗
        (match oM with
        | Some _ => OmoUB γl M e
        | _ => emp end) ∗
        OmoEq γl e en ∗
        ⊒V'' ∗
        @{Vb ⊔ V''} append_only_loc l γl nc ty ∗
        (if do_access then (Φ gen e ∗
        (Φ gen e -∗ [∗ list] gen'↦e ∈ (omo_write_op omo), Φ gen' e)) else emp)
    }}.
Proof.
  iSteps as (??????????????do_access??) "????H5 _".
  wp_apply (append_only_loc_relaxed_read with "[-H5]"); [done|iSteps|].
  iStep 8. destruct x18 as [???]. simpl in *. subst.
  iSteps. iSplitR. { destruct x5; iSteps. } iSteps.
  destruct do_access; [|iSteps].
  iDestruct (big_sepL_lookup_acc with "H5") as "[? ?]"; [done|]. iSteps.
Qed.


#[global] Instance append_only_loc_cas_general_no_fence_spec_sepL_access E1 E2 l orf or ow (vr : lit) (vw : lit) :
  SolveSepSideCondition (Relaxed ⊑ orf) →
  SolveSepSideCondition (Relaxed ⊑ or) →
  SolveSepSideCondition (Relaxed ⊑ ow) →
  SolveSepSideCondition (vr ≠ ☠%V) →
  SPEC [ ε₁ ] ⟨E1, E2⟩ (γl : gname) γs mo (E : history loc_event)
            omo oM M (uf : gset val)
            (V : view) Φ ty (Vb : view) do_access,
  {{  ▷ (@{Vb} append_only_loc l γl uf ty) ∗
      ask_optional oM M ∗
      OmoEview γl M ∗
      OmoAuth γl γs (1/2) E omo mo _ ∗
      ⌜ #vr ∉ uf ⌝ ∗
      ⌜vw ≠ ☠%V⌝ ∗
      If do_access ([∗ list] gen'↦e ∈ (omo_write_op omo), Φ gen' e) ∗
      do_intro_view_forall ∗
      ⊒V ∗
      ⌜↑histN ⊆ E2⌝ }}
      CAS #l #vr #vw orf or ow
    {{ (b : bool) (e : event_id) (gen : nat) (v' : lit) (Vr : view) (V'' : view_bi_index) mo'
      (omo' : omoT) (eV eV' : omo_event loc_event) eV'_type eV'_eview, RET #b;
      let E' := E ++ [eV'] in
      let en := length E in
      ∃ writes,
        MatchValue writes (omo_write_op omo) ∗
        (
        (* cas fail *)
          ⌜b = false ∧
          mo' = mo ∧
          omo' = omo_insert_r omo gen en ∧
          eV'_type = ReadE (#v', Vr)⌝ ∧
          (if decide (AcqRel ⊑ orf)
            then ⌜Vr ⊑ V''⌝
            else emp) ∗
          OmoEq γl e en ∗
          OmoTokenR γl en
        ∨
          (* cas success *)
          ⌜b = true ∧ v' = vr ∧ gen = length omo - 1⌝ ∗
          MatchValue (Some e) (last writes) ∗
          (∃ (Vw : view),
            ⌜mo' = mo ++ [(en, (#vw, Vw))] ∧
            omo' = omo_append_w omo en [] ∧
            eV'_type = UpdateE e (#vw, Vw) ∧
            Vr ⊑ Vw ∧
            Vr ≠ Vw ∧
            ¬ V'' ⊑ Vr ∧
            V ≠ V'' ∧
            (if decide (AcqRel ⊑ ow)
            then
              if decide (AcqRel ⊑ or)
                then Vw = V''
                else V'' ⊑ Vw
            else True)⌝ ∧
            (if decide (AcqRel ⊑ or)
              then ⌜Vw ⊑ V''⌝
              else emp) ∗
            OmoTokenW γl en)) ∗
        ⌜ V ⊑ V'' ∧
          eV' = mkOmoEvent eV'_type V'' (eV'_eview) ⌝ ∗
        MatchValue (Some e) (writes !! gen) ∗
        (if do_access then (Φ gen e ∗
        (Φ gen e -∗ [∗ list] gen'↦e ∈ (omo_write_op omo), Φ gen' e)) else emp) ∗
        OmoEinfo γl e eV ∗
        MatchValue (#v', Vr) (loc_event_msg (type eV)) ∗
        ⌜ b = true ∨ b = false ∧ lit_neq vr v' ⌝ ∗
        OmoUB γl M e ∗
        OmoEinfo γl en eV' ∗
        OmoAuth γl γs (1/2) E' omo' mo' _ ∗
        ⊒V'' ∗
        (if (decide (b = true ∧ ty = swriter)) then
          ∀ es Vs, @{Vs} swriter_token l γl es ==∗ @{Vs ⊔ V''} swriter_token l γl (omo_write_op omo') ∗ @{Vb ⊔ V''} append_only_loc l γl uf ty
        else
          @{Vb ⊔ V''} append_only_loc l γl uf ty)
    }}.
Proof.
  rewrite /SolveSepSideCondition. move => Rx1 Rx2 Rx3 Hvr.
  iSteps as (tid?????????????do_access????) "H1 H2 H3 H4 H5 _".

  iMod (rel_objectively_intro (⊒∅) tid with "[]") as "#rel_empty".
  { iApply objective_objectively. iApply monPred_in_bot. }

  wp_apply (append_only_loc_cas_general with "[-H5]"); try done.
  { destruct (decide _); iFrame "∗#". }
  iIntros (b e gen v' Vr V'' mo' omo' eV eV') "H".
  iExists b, e, gen, v', Vr, V'', mo', omo'. iExists eV, eV', _, (eview eV').
  iDestruct "H" as "((% & % & %) & ? & ? & ? & ? & ? & ? & case)".
  set access_result := (if do_access then (_ ∗ _) else _)%I.
  iAssert (access_result) with "[H5]" as "?". {
    subst access_result. destruct do_access; [|done].
    - iDestruct (big_sepL_lookup_acc with "H5") as "[? ?]"; [done|]. iSteps. }
  iFrame.
  iDestruct "case" as "[fail | success]".
  - iDecompose "fail" as (??) "H11 H12 H13 H14 H15". iStepsSafest. iLeft. unseal_diaframe; simpl.
    iSplitL "H13". { destruct (decide _); done. }
    iFrame "#∗".
    iSteps.
    destruct eV'. done.
  - iDecompose "success" as (???????) "H12 H13 H14 H15 H16". iSplitR; [done|].
    iStepsSafest. iRight. iSplitR "H14".
    + rewrite last_lookup -omo_write_op_length. replace (pred _) with (length (x4) - 1); [|lia]. iSteps; repeat destruct (decide _); iSteps; done.
    + iSteps.
      * destruct eV'. done.
      * destruct x10; [rewrite decide_False; [|by unfold not; intros [_ ?]]|rewrite decide_True; [|done]]; iFrame.
Qed.


#[global] Instance append_only_loc_acquire_read_spec_sepL_access E1 E2 l :
  SPEC [ ε₁ ] ⟨E1, E2⟩ (V : view) γl γs mo omo oM M (E: omo_history.history loc_event) uf ty Vb Φ do_access,
    {{
      ▷(@{Vb} append_only_loc l γl uf ty ∗
        ask_optional oM M ∗
        OmoEview γl M ∗
        OmoAuth γl γs (1/2) E omo mo _ ∗
        If do_access ([∗ list] gen'↦e ∈ (omo_write_op omo), Φ gen' e) ∗
        do_intro_view_forall ∗
        ⊒V
        ) ∗ ⌜↑histN ⊆ E2⌝ }}
    !ᵃᶜ#l
    {{ (e : event_id) (gen : nat) (v' : val) (V' : view) (V'' : view_bi_index)
        (eV eV': omo_event.omo_event loc_event) eV'_eview , RET v';
      let E' := E ++ [eV'] in
      let e' := length E in
      let omo' := omo_insert_r omo gen e' in
      MatchValue (Some e) (omo_write_op omo !! gen) ∗
      ⌜ eV' = mkOmoEvent (ReadE (v', V')) V'' eV'_eview ∧
      V ⊔ V' ⊑ V''⌝ ∗
      OmoEinfo γl e eV ∗
      MatchValue (v', V') (loc_event_msg (type eV)) ∗
      OmoEinfo γl e' eV' ∗
      OmoAuth γl γs (1/2) E' omo' mo _ ∗
      OmoTokenR γl e' ∗
      OmoUB γl M e ∗
      OmoEq γl e e' ∗
      ⊒V'' ∗
      @{Vb ⊔ V''} append_only_loc l γl uf ty ∗
      (if do_access then (Φ gen e ∗
      (Φ gen e -∗ [∗ list] gen'↦e ∈ (omo_write_op omo), Φ gen' e)) else emp)
    }}.
Proof.
  iSteps as (??????????????do_access??) "H1 H2 H3 H4 Writes _".
  wp_apply (append_only_loc_acquire_read with "[-Writes]"); try done; first iSteps.
  iStep 8. destruct x18 as [???]. simpl in *. subst.
  iSteps. destruct do_access; last done.
  iDestruct (big_sepL_lookup_acc with "Writes") as "[? ?]"; [done|].
  iSteps.
Qed.

#[global] Instance append_only_loc_release_write_spec E1 E2 l v' :
  SPEC [ ε₁ ] ⟨E1, E2⟩ (V : view) γl uf ty Vb γs mo omo M (E: omo_history.history loc_event) es,
    {{
      ▷(@{Vb} append_only_loc l γl uf ty ∗
        OmoAuth γl γs (1/2) E omo mo _ ∗
        OmoEview γl M ∗
        swriter_token l γl es ∗
        do_intro_view_forall ∗
        ⊒V
        ) ∗
        ⌜v' ≠ ☠%V ∧ ↑histN ⊆ E2⌝ }}
      #l <-ʳᵉˡ #v'
    {{ RET #☠; ∃ (e : event_id) (gen : nat) (V' : view)
        (eV eV': omo_event.omo_event loc_event) eV'_eview,
      let E' := E ++ [eV'] in
      let e' := length E in
      let omo' := omo_append_w omo e' [] in
      let uf' := {[(loc_event_msg (type eV)).1]} ∪ uf in
      ⌜es = omo_write_op omo⌝ ∗
      MatchValue (Some e) (last (omo_write_op omo)) ∗
      ⌜ty = swriter ∧
      eV' = mkOmoEvent (WriteE (#v', V')) V' eV'_eview ∧
      V ⊑ V' ∧ V ≠ V'⌝ ∗
      OmoEinfo γl e eV ∗
      OmoEinfo γl e' eV' ∗
      OmoAuth γl γs (1/2) E' omo' (mo ++ [(e', (#v', V'))]) _ ∗
      OmoTokenW γl e' ∗
      ⊒V' ∗
      @{V'} swriter_token l γl (omo_write_op omo') ∗
      @{Vb ⊔ V'} append_only_loc l γl uf' swriter
    }}.
Proof.
  iSteps as (??????????????) "Hlogview H⊒ Happloc Hmaster Hwriter_token _".
  iDestruct (OmoAuth_swriter_token_agree_obj_2 with "[$Hmaster] [$Happloc] [$Hwriter_token]") as %->.
  iDestruct (swriter_token_type_obj_2 with "[$] [$]") as %->.
  wp_apply (append_only_loc_release_write with "[-]"); try done.
  { instantiate (2 := emp%I). iSteps. }
  iStep 6. destruct x10 as [???]. simpl in *. subst.
  iSteps.
Qed.



#[global] Instance biabd_append_only_loc_cas_only_to_swriter_obj V l γl uf :
  HINT @{V} @append_only_loc _ _ _ _ _ l γl uf cas_only ✱
    [γs q E omo mo eidx e;
      OmoAuth (eventT := loc_event) γl γs q E omo mo _ ∗
      ask_for eidx ∗
      ⌜ gen_of eidx = (length omo - 1)%nat ∧
        lookup_omo omo eidx = Some e ⌝ ∗
      OmoEview γl {[e]}
    ]
  ⊫ [id]
  ; @{V} append_only_loc l γl uf swriter ✱
  [OmoAuth γl γs q E omo mo _ ∗ swriter_token l γl (omo_write_op omo)] | 55.
Proof.
  rewrite /BiAbd; simpl. iIntros (γs q E omo mo eidx e) "(l↦ & M● & _ & (% & %) & M◯)".
  iDestruct (cas_only_to_swriter_obj with "M● M◯ l↦") as "($ & $ & $)"; [|done..]. set_solver-.
Qed.


#[global] Instance biabd_append_only_loc_swriter_to_cas_obj V0 l γl uf :
      HINT @{V0} @append_only_loc _ _ _ _ _ l γl uf swriter ✱
      [V1 es; @{V1} swriter_token l γl es]
      ⊫ [id]
      ; @{V0} append_only_loc l γl uf cas_only ✱
      [emp] | 55.
Proof.
  rewrite /BiAbd; simpl. iSteps as (??) "A B".
  iDestruct (swriter_to_cas_only_obj_1 with "A B") as "?". iSteps.
Qed.

#[global] Instance biabd_append_only_loc_to_na Ec l γe uf ty :
  HINT append_only_loc l γe uf ty ✱ [γs q omo (E : history loc_event) mo; ⎡ hist_inv ⎤ ∗ OmoAuth (eventT := loc_event) γe γs q E omo mo _ ∗ ⌜ ↑histN ⊆ Ec ⌝]
  ⊫ [fupd Ec Ec]
  v; l ↦ v ✱ [ ∃ e (eV : omo_event loc_event),
    ⌜ v = (loc_event_msg eV.(type)).1 ⌝ ∗ ⌜ Some e = last (omo_write_op omo) ⌝ ∗
    OmoAuth γe γs (q + 1/2)%Qp E omo mo _ ∗ OmoEinfo γe e eV].
Proof.
  intros. iSteps. iMod (append_only_loc_to_na with "[$] [$] [$]") as "H"; [done|].
  iDecompose "H". iSteps.
Qed.

End omo_specs.