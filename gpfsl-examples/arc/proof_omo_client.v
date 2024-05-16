From iris.algebra Require Import excl_auth gset.
From iris.bi.lib Require Import fractional.
From iris.proofmode Require Import tactics.

From gpfsl.lang Require Import notation.
From gpfsl.logic Require Import new_delete logatom invariants proofmode.
From gpfsl.examples.arc Require Import spec_composition.
From gpfsl.examples.omo Require Import omo omo_preds append_only_loc.
From gpfsl.examples Require Import set_helper uniq_token.

Require Import iris.prelude.options.

Definition clN := nroot .@ "clN".

Section Client.
  Context `{!noprolG Σ,
            !uniqTokG Σ,
            !omoGeneralG Σ,
            !omoSpecificG Σ arc_event arc_state}.

  Implicit Types
    (E : history arc_event) (omo : omoT) (stlist : list arc_state).

  Local Notation iProp := (iProp Σ).
  Local Notation vProp := (vProp Σ).
  Local Open Scope nat_scope.

  (** Assuming composable linearizability spec of Arc *)
  Hypothesis arc : arc_spec Σ.

  Definition prog  : expr :=
    let: "l" := new [ #2] in
    "l" <- #1;;
    "l" +ₗ #1 <- #1;;
    (* Must succeed in complete destruction of `Arc` *)
    let: "res1" := arc.(drop_arc) ["l"] in
    let: "res2" := arc.(drop_weak) ["l"] in
    new_delete.delete [ #2; "l"];;
    if: "res1"
    then if: "res2"
         then #true
         else #false
    else #false.

  Lemma client_lock_spec tid :
    {{{ True }}}
      prog @ tid; ⊤
    {{{ RET #true; True }}}.
  Proof using All.
    iIntros (Φ) "_ Post". rewrite /prog.
    wp_apply wp_new; [done..|]. iIntros (l) "(†l & l↦ & _ & _)".
    iDestruct "†l" as "[†l|%]"; [|done].
    rewrite own_loc_na_vec_cons own_loc_na_vec_singleton. iDestruct "l↦" as "[l0↦ l1↦]".
    wp_pures. wp_write. wp_pures. rewrite -[Z.to_nat 1]/(1%nat). wp_write.

    (* Create an `ArcInv` object (i.e., register a valid Arc object) *)
    iDestruct (view_at_intro emp with "[]") as (V1) "[#⊒V1 _]"; [done|].
    iMod (create_strong arc ⊤ l (λ q, emp)%I emp%I _ (clN .@ "arc") with "⊒V1 l0↦ l1↦ []")
      as (γg γs V2 M1 q1) "(#⊒V2 & M● & [SArc@V2 _] & _)".
    { intros. constructor; [done|]. constructor. intros. iSplit; iIntros "_"; done. } { done. }

    iDestruct (view_at_elim with "⊒V2 SArc@V2") as "SArc".
    iAssert (▷ _)%I with "[M●]" as "M●"; [iClear "⊒V1 ⊒V2"; done|].
    awp_apply (drop_arc_spec arc with "⊒V1 SArc []"); [solve_ndisj| |done|].
    { intros. constructor; [done|]. constructor. intros. iSplit; iIntros "_"; done. }
    iAaccIntro with "M●".
    { iIntros "M● !>". iFrame. }

    iIntros (b2 V3 st2 M2) "(#⊒V3 & M● & _ & _ & CASE)".
    iDestruct (ArcInv_OmoAuth_acc with "M●") as "[>M● Close]".
    iDestruct (OmoAuth_wf with "M●") as %[OMO_GOOD2 _].
    iDestruct ("Close" with "[M●]") as "M●"; [done|].

    (* Prove that `drop_arc` succeeds *)
    eapply (omo_write_op_step _ _ _ 0 1) in OMO_GOOD2 as STEP; [|done..].
    inversion STEP; try done; subst; simpl in *; [set_solver +STRICT|].
    inversion EVENT. subst.

    iModIntro. iIntros "_". wp_pures.
    iAssert (▷ _)%I with "[M●]" as "M●"; [iClear "⊒V1 ⊒V2 ⊒V3"; done|].

    iDestruct "CASE" as "[FArc _]". iDestruct (view_at_elim with "⊒V3 FArc") as "FArc".
    awp_apply (drop_fake_spec arc with "⊒V1 FArc []"); [solve_ndisj|done|].
    iAaccIntro with "M●".
    { iIntros "M● !>". iFrame. }

    iIntros (b3 V4 γs3 omo3 stlist3 M3) "(#⊒V4 & M● & _ & _ & (_ & %SubM2M3 & [%gen3 ->]))".
    iDestruct (ArcInv_OmoAuth_acc with "M●") as "[>M● _]".
    iDestruct (OmoAuth_wf with "M●") as %[OMO_GOOD3 _].
    iDestruct (OmoEinfo_get _ _ _ _ _ _ 2 with "M●") as "#He2"; [done|].
    iDestruct (OmoUB_singleton with "He2") as "MAXM3".

    iDestruct (big_sepS_elem_of _ _ 0 with "MAXM3") as "LE1"; [set_solver|].
    iDestruct (big_sepS_elem_of _ _ 1 with "MAXM3") as "LE2"; [set_solver|].

    have [->|[->|LEgen3]] : gen3 = 0 ∨ gen3 = 1 ∨ 2 ≤ gen3 by lia.
    { iDestruct (OmoLe_Le _ _ _ _ _ _ (wr_event 1) (wr_event 0) with "M● LE1") as %LE; [done|done|]. simpl in LE. lia. }
    { iDestruct (OmoLe_Le _ _ _ _ _ _ (wr_event 2) (wr_event 1) with "M● LE2") as %LE; [done|done|]. simpl in LE. lia. }

    (* Prove that `weak_drop` succeeds *)
    rewrite omo_insert_w_append_w in OMO_GOOD3; [|done]. simpl in OMO_GOOD3.
    apply omo_stlist_length in OMO_GOOD3 as EQlenST3. simpl in EQlenST3.
    destruct stlist3 as [|st1 stlist3]; [done|]. destruct stlist3 as [|st2 stlist3]; [done|].
    destruct stlist3 as [|st3 stlist3]; [done|]. destruct stlist3; [|done].
    eapply (omo_write_op_init_step _ _ _ 0) in OMO_GOOD3 as STEP1; [|done..].
    eapply (omo_write_op_step _ _ _ 0 1) in OMO_GOOD3 as STEP2; [|done..].
    eapply (omo_write_op_step _ _ _ 1 2) in OMO_GOOD3 as STEP3; [|done..].
    inversion STEP1; try done; subst; simpl in *.
    inversion STEP2; try done; subst; simpl in *.
    inversion STEP3; try done; subst; simpl in *; [set_solver +STRICT|].
    inversion EVENT2. subst.

    (* Deallocate the Arc *)
    iModIntro. iIntros "(_ & l0↦ & l1↦)". wp_let.
    iCombine "l0↦ l1↦" as "l↦". rewrite -(own_loc_na_vec_singleton (l >> 1)) -own_loc_na_vec_cons.
    wp_apply (wp_delete with "[$l↦ †l]"); [solve_ndisj|done|by iLeft|].
    iIntros "_". wp_pures. by iApply "Post".
  Qed.
End Client.
