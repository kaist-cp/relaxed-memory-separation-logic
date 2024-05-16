From iris.algebra Require Import excl_auth gset.
From iris.bi.lib Require Import fractional.
From iris.proofmode Require Import tactics.

From gpfsl.lang Require Import notation.
From gpfsl.logic Require Import new_delete logatom invariants proofmode.
From gpfsl.examples.stack Require Import spec_treiber_composition.
From gpfsl.examples.omo Require Import omo omo_preds append_only_loc.
From gpfsl.examples Require Import set_helper uniq_token.

Require Import iris.prelude.options.

Definition clN := nroot .@ "clN".

Section Client.
  Context `{!noprolG Σ,
            !uniqTokG Σ,
            !omoGeneralG Σ,
            !omoSpecificG Σ sevent_hist stack_state}.

  Implicit Types
    (E : history sevent_hist) (omo : omoT) (stlist : list stack_state)
    (s d : loc).

  Local Notation iProp := (iProp Σ).
  Local Notation vProp := (vProp Σ).
  Local Open Scope nat_scope.

  (** Assuming composable linearizability spec of Stack *)
  Hypothesis stk : stack_spec Σ.

  Definition prog  : expr :=
    let: "d" := new [ #1] in
    let: "s" := stk.(new_stack) [] in
    Fork
      ("d" <- #42;;
       stk.(push) ["s"; #1]);;(* || *)
                              (* || *) stk.(try_pop) ["s"];;
                              (* || *) if: stk.(try_pop) ["s"] = #1
                              (* || *) then !"d" else #(-1). (* Access to "d" should return 42 *)

  Definition clientInv γg γs γu s d : vProp :=
    ∃ E omo stlist,
      stk.(StackInv) γg γs s E omo stlist ∗
      ( ⌜ stlist = [[]] ⌝
      ∨ (UTok γu ∗ ( (∃ e V lV, ⌜ stlist = [[]; [(e, 1%Z, V, lV)]] ⌝ ∗ @{V} (d ↦ #42))
                   ∨ (∃ e V lV, ⌜ stlist = [[]; [(e, 1%Z, V, lV)]; []] ⌝)))).

  Local Instance clientInv_objective γg γs γu s d : Objective (clientInv γg γs γu s d) := _.

  Lemma client_stack_spec tid :
    {{{ True }}}
      prog @ tid; ⊤
    {{{ z, RET #z; ⌜(z = 42 ∨ z = -1)%Z⌝ }}}.
  Proof using All.
    iIntros (Φ) "_ Post". rewrite /prog.
    wp_apply wp_new; [done..|]. iIntros (d) "(_ & d↦ & _ & _)".
    rewrite own_loc_na_vec_singleton. wp_pures.
    iDestruct (view_at_intro with "d↦") as (V1) "[#⊒V1 d↦]". iDestruct (view_at_elim with "⊒V1 d↦") as "d↦".
    wp_apply (new_stack_spec stk (clN .@ "stk") with "⊒V1").
    iIntros (γg γs s M1 V2) "(#⊒V2 & M● & #⊒M1@V2 & _)".

    iMod UTok_alloc as (γu) "Hγu".
    iMod (inv_alloc (clN .@ "inv") _ (clientInv γg γs γu s d) with "[M●]") as "#I".
    { repeat iExists _. iFrame. iLeft. done. }

    wp_let. wp_apply (wp_fork with "[d↦ Hγu]"); [done|..].
    - (* Left thread *)
      iIntros "!>" (tid'). wp_write.
      iDestruct (view_at_intro_incl with "d↦ ⊒V2") as (V3) "(#⊒V3 & %LeV2V3 & d↦@V3)".
      iDestruct (view_at_elim with "⊒V2 ⊒M1@V2") as "⊒M1".

      (* Inv access #1 *)
      awp_apply (push_spec stk with "⊒V3 ⊒M1"); [solve_ndisj|lia|].
      iInv "I" as (E1 omo1 stlist1) "[>M● >CASE]".
      iDestruct (StackInv_OmoAuth_acc with "M●") as "[M● Close]".
      iDestruct (OmoAuth_wf with "M●") as %[OMO_GOOD _]. apply omo_stlist_length in OMO_GOOD as EQlenST.
      iDestruct ("Close" with "M●") as "M●".
      iAaccIntro with "M●".
      { iIntros "M● !>". iFrame "Hγu d↦@V3". repeat iExists _. iFrame "M● CASE". }

      iIntros (V4 st2 M2) "(#⊒V4 & M● & #⊒M2@V4 & _ & _ & [%LeV3V4 _])".
      iDestruct (StackInv_OmoAuth_acc with "M●") as "[>M● Close]".
      iDestruct (OmoAuth_wf with "M●") as %[OMO_GOOD' _].
      iDestruct ("Close" with "[M●]") as "M●"; [done|].

      iDestruct "CASE" as "[->|[Hγu' _]]"; last first.
      { by iDestruct (UTok_unique with "Hγu Hγu'") as %?. }

      have [e He] : is_Some (omo_write_op omo1 !! 0) by rewrite lookup_lt_is_Some -omo_write_op_length EQlenST /=; lia.
      eapply (omo_write_op_step _ _ _ 0 (length E1)) in OMO_GOOD' as STEP; try done; [..|by rewrite lookup_app_1_eq]; last first.
      { rewrite omo_append_w_write_op lookup_app_r; rewrite -omo_write_op_length EQlenST /=; [done|lia]. }
      inversion STEP; subst; simpl; try done. inversion PUSH. subst v.

      iModIntro. iSplitL; [|by iIntros "_"].
      repeat iExists _. iFrame "M●". iRight. iFrame "Hγu". iLeft. repeat iExists _. iSplitR; [done|]. iFrame "d↦@V3".
    - (* Right thread *)
      iIntros "_". wp_pures.
      iDestruct (view_at_elim with "⊒V2 ⊒M1@V2") as "⊒M1".

      (* Inv access #1 *)
      awp_apply (try_pop_spec stk with "⊒V2 ⊒M1"); [solve_ndisj|].
      iInv "I" as (E1 omo1 stlist1) "[>M● >CASE]".
      iDestruct (StackInv_OmoAuth_acc with "M●") as "[M● Close]".
      iDestruct (OmoAuth_wf with "M●") as %[OMO_GOOD _]. apply omo_stlist_length in OMO_GOOD as EQlenST.
      iDestruct (OmoAuth_omo_nonempty with "M●") as %Nomo1.
      have NZomo1 : length omo1 ≠ 0 by destruct omo1.
      iDestruct ("Close" with "M●") as "M●".
      iAaccIntro with "M●".
      { iIntros "M● !>". iFrame "Post". repeat iExists _. iFrame "M● CASE". }

      iIntros (z2 V3 E1' omo1' stlist1' M2) "(#⊒V3 & M● & #⊒M2@V3 & CASEz2)".
      iDestruct (StackInv_OmoAuth_acc with "M●") as "[>M● Close]".
      iDestruct (OmoAuth_wf with "M●") as %[OMO_GOOD' _].
      iDestruct ("Close" with "[M●]") as "M●"; [done|].

      iModIntro. iSplitR "Post".
      { repeat iExists _. iFrame "M●".
        destruct (decide (z2 = (-1)%Z)) as [->|NEQ1]; last destruct (decide (z2 = 0%Z)) as [->|NEQ2].
        - iDestruct "CASEz2" as %(-> & -> & -> & ->). iFrame "CASE".
        - iDestruct "CASEz2" as "(_ & _ & (_ & -> & _) & _)". iFrame "CASE".
        - iDestruct "CASEz2" as "(_ & _ & (-> & -> & [%st2 ->]) & _)".
          have [st Hst] : is_Some (stlist1 !! (length omo1 - 1)%nat) by rewrite lookup_lt_is_Some -EQlenST; lia.
          eapply (omo_write_op_step _ _ _ (length omo1 - 1) (length E1)) in OMO_GOOD' as STEP; last first.
          { rewrite Nat.sub_add; [|lia]. rewrite EQlenST lookup_app_1_eq. done. }
          { rewrite lookup_app_l; [done|]. rewrite -EQlenST. lia. } { rewrite lookup_app_1_eq. done. }
          { rewrite Nat.sub_add; [|lia]. rewrite omo_append_w_write_op omo_write_op_length lookup_app_1_eq. done. }

          have Nlast : st ≠ [] by inversion STEP. rewrite EQlenST in Hst.
          iDestruct "CASE" as "[->|[Hγu [(%e & %V & %lV & -> & d↦@V)|(%e & %V & %lV & ->)]]]"; inversion Hst; try done.
          iRight. iFrame "Hγu". iRight. subst st. inversion STEP; try done. subst. simpl in *.
          repeat iExists _. done. }

      iIntros "_". wp_pures.

      (* Inv access #2 *)
      awp_apply (try_pop_spec stk with "⊒V2 ⊒M1"); [solve_ndisj|].
      iInv "I" as (E2 omo2 stlist2) "[>M● >CASE]".
      iDestruct (StackInv_OmoAuth_acc with "M●") as "[M● Close]".
      iDestruct (OmoAuth_wf with "M●") as %[OMO_GOOD2 _]. apply omo_stlist_length in OMO_GOOD2 as EQlenST2.
      iDestruct (OmoAuth_omo_nonempty with "M●") as %Nomo2.
      have NZomo2 : length omo2 ≠ 0 by destruct omo2.
      iDestruct ("Close" with "M●") as "M●".
      iAaccIntro with "M●".
      { iIntros "M● !>". iFrame "Post". repeat iExists _. iFrame "M● CASE". }

      iIntros (z3 V4 E2' omo2' stlist2' M3) "(#⊒V4 & M● & #⊒M3@V4 & CASEz3)".
      iDestruct (StackInv_OmoAuth_acc with "M●") as "[>M● Close]".
      iDestruct (OmoAuth_wf with "M●") as %[OMO_GOOD2' _].
      iDestruct ("Close" with "[M●]") as "M●"; [done|].

      destruct (decide (z3 = (-1)%Z)) as [->|NEQ1]; last destruct (decide (z3 = 0%Z)) as [->|NEQ2].
      + iDestruct "CASEz3" as %(-> & -> & -> & ->).
        iModIntro. iSplitR "Post".
        { repeat iExists _. iFrame "M● CASE". }
        iIntros "_". wp_pures. iApply "Post". by iRight.
      + iDestruct "CASEz3" as "(_ & _ & (_ & -> & _) & _)".
        iModIntro. iSplitR "Post".
        { repeat iExists _. iFrame "M● CASE". }
        iIntros "_". wp_pures. iApply "Post". by iRight.
      + iDestruct "CASEz3" as "([%LeV2V4 _] & _ & (-> & -> & [%st3 ->]) & _)".
        have [st Hst] : is_Some (stlist2 !! (length omo2 - 1)%nat) by rewrite lookup_lt_is_Some -EQlenST2; lia.
        eapply (omo_write_op_step _ _ _ (length omo2 - 1) (length E2)) in OMO_GOOD2' as STEP; last first.
        { rewrite Nat.sub_add; [|lia]. rewrite EQlenST2 lookup_app_1_eq. done. }
        { rewrite lookup_app_l; [done|]. rewrite -EQlenST2. lia. } { rewrite lookup_app_1_eq. done. }
        { rewrite Nat.sub_add; [|lia]. rewrite omo_append_w_write_op omo_write_op_length lookup_app_1_eq. done. }

        have Nlast : st ≠ [] by inversion STEP. rewrite EQlenST2 in Hst.
        iDestruct "CASE" as "[->|[Hγu [(%e & %V & %lV & -> & d↦@V)|(%e & %V & %lV & ->)]]]"; inversion Hst; try done.
        inversion STEP; try done. subst. simpl in *. inversion POP. subst v. inversion H2. subst.
        iModIntro. iSplitR "Post d↦@V".
        { repeat iExists _. iFrame "M●". iRight. iFrame "Hγu". iRight. repeat iExists _. done. }
        iIntros "_".
        iDestruct (view_at_mono_2 _ V4 with "d↦@V") as "d↦@V4"; [solve_lat|].
        iDestruct (view_at_elim with "⊒V4 d↦@V4") as "d↦".
        wp_pures. wp_read. iApply "Post". by iLeft.
Qed.
End Client.
