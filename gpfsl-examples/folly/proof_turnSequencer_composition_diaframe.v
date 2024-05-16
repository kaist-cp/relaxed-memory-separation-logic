From gpfsl.examples Require Import sflib.

From iris.algebra Require Import auth gset gmap agree.
From iris.proofmode Require Import tactics.

From gpfsl.base_logic Require Import meta_data.
From gpfsl.logic Require Import logatom atomics invariants.

From gpfsl.logic Require Import repeat_loop new_delete.
From gpfsl.examples Require Import map_seq loc_helper.
From gpfsl.examples.algebra Require Import set.
From gpfsl.examples.folly Require Import spec_turnSequencer_composition code_turnSequencer.
From gpfsl.examples.omo Require Import omo omo_preds omo_preds_diaframe append_only_loc.

From gpfsl.diaframe Require Import vprop_weakestpre spec_notation
 vprop_weakestpre_logatom atom_spec_notation proof_automation omo_specs omo_hints.

From diaframe Require Import proofmode_base lib.except_zero own_hints steps.verify_tac util_instances.
From diaframe.symb_exec Require Import weakestpre_logatom.


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
    MatchValue (Some stf) (last stlist) ∗
    MatchValue (Some elf) (last esl) ∗
    OmoEinfo γl elf eVlf ∗
    MatchValue (#stf.1.1.2, Vf) (loc_event_msg eVlf.(type)) ∗
    OmoEinfo γg stf.1.1.1 eVf ∗
    OmoSnap γg γs stf.1.1.1 stf ∗
    ⌜ last es = Some stf.1.1.1 ∧ eVlf.(sync) = eVf.(sync)
    ∧ stf.1.1.2 = length esl - 1 ∧ stf.1.2 = eVf.(sync) ∧ eVf.(sync) ⊑ Vf ∧ stf.2 = eVf.(eview) ⌝ ∗
    TSeqPerm γg l (λ m, m <? stf.1.1.2) ∗
    ((@{Vf} (swriter_token l γl esl ∗ R stf.1.1.2)) ∨ TSeqPerm γg l (λ m, m =? stf.1.1.2)).

(** ** Top-level predicates & invariant *)
Definition TSeqInv γg γs l E omo stlist R : vProp :=
  ∃ (γl γsl γt : gname) El omol mo Vb uf,
  meta l nroot (γl,γsl,γt) ∗

  try_update_OmoAuth_to γl El omol mo ∗
  try_update_OmoAuth_to γg E omo stlist ∗

  @{Vb} append_only_loc l γl uf swriter ∗

  last_msg_info γg γl γs l R (omo_write_op omo) (omo_write_op omol) stlist ∗
  AllWrEvents γl (omo_write_op omol) ∗

  OmoAuth γl γsl (1/2)%Qp El omol mo _ ∗
  OmoAuth γg γs 1 E omo stlist _.

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
Proof. intros. iDestruct 1 as (????????) "(?&?&?&?&?&?&?&M●)". by iDestruct (OmoAuth_Linearizable with "M●") as %?. Qed.

Lemma TSeqInv_OmoAuth_acc_instance :
  ∀ γg γs l E omo stlist R,
    TSeqInv γg γs l E omo stlist R ⊢ OmoAuth γg γs 1 E omo stlist _ ∗ (OmoAuth γg γs 1 E omo stlist _ -∗ TSeqInv γg γs l E omo stlist R).
Proof. intros. iDestruct 1 as (????????) "(?&?&?&?&?&?&?&M●)". iFrame "M●". iIntros "M●". repeat iExists _. iFrame. Qed.

Lemma TSeqLocal_OmoEview_instance :
  ∀ N γg l M, TSeqLocal N γg l M ⊢ OmoEview γg M.
Proof. oSteps. Qed.


#[local] Remove Hints biabd_OmoAuth_insert_ro : typeclass_instances.
#[local] Hint Resolve biabd_OmoAuth_insert_ro_gen : typeclass_instances.

#[global] Instance append_only_loc_relaxed_read_no_fence_spec_sepL_access_swriter (E1 E2 : coPset) l  :
  SPEC [ ε₁ ] ⟨E1, E2⟩ (V : view) γl γs mo omo es oM M (E : history loc_event) nc ty Vb Φ (do_access : bool),
    {{
      ▷(@{Vb} append_only_loc l γl nc ty ∗
        ask_optional oM M ∗
        OmoEview γl M ∗
        OmoAuth γl γs (1/2) E omo mo loc_interpretable ∗
        swriter_token l γl es) ∗
        base_hints.If do_access ([∗ list] gen'↦e ∈ (omo_write_op omo), Φ gen' e) ∗
        do_intro_view_forall ∗
        ⊒V ∗
        ⌜↑histN ⊆ E2⌝ }}
    !ʳˡˣ#l
    {{ (e : event_id) (v' : val) (V' : view) (V'' : view_bi_index)
       (eV eV': omo_event loc_event) eV'_eview, RET v';
      let En := E ++ [eV'] in
      let en := length E in
      let gen := length (omo_write_op omo) - 1 in
      let omon := omo_insert_r omo (length omo - 1) en in
      MatchValue (Some e) (omo_write_op omo !! gen) ∗
      MatchValue (Some e) (last es) ∗
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
      @{V''} swriter_token l γl es ∗
      (if do_access then (Φ gen e ∗
      (Φ gen e -∗ [∗ list] gen'↦e ∈ (omo_write_op omo), Φ gen' e)) else emp)
    }}.
Proof.
  iStep 16 as (??V?????????????do_access??) "??? ⊒V omol↦ Ml● SW Hacc H".
  iDestruct (swriter_token_type_obj_2 with "SW omol↦") as %->. iDestruct (OmoAuth_swriter_token_agree_obj_2 with "Ml● omol↦ SW") as %->.
  wp_apply (append_only_loc_read_with_swriter_token with "[$Ml● $omol↦ $SW]"); [done|done|oSteps|]. oSteps. destruct x15. simpl in *. iExists x0. oSteps.
  { rewrite last_lookup -omo_write_op_length /omo_write_op list_lookup_fmap in H2.
    replace (Init.Nat.pred (length x4)) with (length x4 - 1) in H2 by lia. done. }
  iSplitR; [by destruct x6|]. oSteps. destruct do_access; iSteps. iDestruct (big_sepL_lookup_acc with "Hacc") as "[Acc Close]"; [|oSteps].
  rewrite last_lookup -omo_write_op_length in H2. replace (Init.Nat.pred (length x4)) with (length x4 - 1) in H2 by lia. done.
Qed.

#[local] Remove Hints append_only_loc_relaxed_read_no_fence_spec_sepL_access : core.

#[global] Instance hint_swriter_token_exclusive_1 l γl es es' V :
  MergableConsume (@{V} swriter_token l γl es) true (λ p Pin Pout,
    TCAnd (TCEq Pin (swriter_token l γl es')) $
      TCEq Pout (False))%I.
Proof.
  intros p Pin Pout [-> ->]. rewrite bi.intuitionistically_if_elim. iIntros "[A B]".
  iDestruct (view_at_intro with "B") as (?) "[_ B]". by iDestruct (swriter_token_exclusive_obj with "A B") as %?.
Qed.

#[global] Instance hint_swriter_token_exclusive_2 l γl es es' V V' :
  MergableConsume (@{V} swriter_token l γl es) true (λ p Pin Pout,
    TCAnd (TCEq Pin (@{V'} swriter_token l γl es')) $
      TCEq Pout (False))%I.
Proof.
  intros p Pin Pout [-> ->]. rewrite bi.intuitionistically_if_elim. iIntros "[A B]". by iDestruct (swriter_token_exclusive_obj with "A B") as %?.
Qed.

Lemma last_lookup' `{A : Type} (l : list A) :
  last l = l !! (length l - 1).
Proof. rewrite last_lookup. replace (Init.Nat.pred (length l)) with (length l - 1) by lia. done. Qed.

Lemma new_tseq_spec :
  new_tseq_spec' code_turnSequencer.newTS TSeqLocal TSeqInv TSeqPerm.
Proof.
  iSteps as (???V0) "⊒V0 R??? Hml". rewrite shift_0. iStep 6 as "l↦". iCombine "R ⊒V0" as "RV".
  iMod (append_only_loc_swriter_from_na_rel with "RV l↦") as (γl γsl V1 eVl0)
    "(#⊒V1 & Ml● & (#Ml◯ & [R@V1 #⊒V0@V1] & SW) & omol↦ & WCOMMITl & #el0✓eVl0 & Pures)"; [done|].
  iDestruct "Pures" as %[eVl0EV eVl0SYNC]. iDecompose "⊒V0@V1". iClear "⊒V0".

  set eVinit := mkOmoEvent Init V1 {[0%nat]}.
  set initst := (0%nat, 0%nat, eVinit.(sync), eVinit.(eview)).

  iMod (@OmoAuth_alloc _ _ _ _ _ eVinit initst _ _ tseq_interpretable with "WCOMMITl") as (γg γs)
    "(M● & #M◯ & #e0↦el0 & #e0✓eVinit & #e0↪initst & WCOMMIT)"; [by apply tseq_step_Init|done|].
  iDestruct (OmoHbToken_finish with "M●") as "M●".

  iMod (own_alloc (set_cf (λ (n : nat), true))) as (γt) "Hγt"; [done|]. rewrite (set_cf_split _ (λ n, n <? 0)). iDestruct "Hγt" as "[Hγt1 Hγt2]".
  rewrite (set_cf_equiv (λ n, true && (n <? 0)) (λ n, n <? 0)); [|done]. rewrite (set_cf_equiv (λ n, true && negb (n <? 0)) (λ n, true)); [|done].
  iMod (meta_set _ _ (γl,γsl,γt) nroot with "Hml") as "#HM"; [done|]. iDecompose "M◯". iDecompose "Ml◯". iDecompose "e0↪initst".
  iDestruct (view_at_intro with "omol↦") as (?) "[_ omol↦]". iStep 2.
  iExists γg. iStep 2. rewrite /TSeqInv !try_update_OmoAuth_to_eq. oSteps. iExists 0.
  iSplitR; [iPureIntro; by instantiate (1 := [(0, [])])|].
  oSteps; [by rewrite eVl0EV|by rewrite eVl0EV|]. iLeft. rewrite eVl0EV. oSteps. by rewrite eVl0EV.
Qed.

#[global] Instance wait_dspec N γg γs l V M n R :
  SPEC ⟨ ⊤ , ↑N , ↑histN⟩ E omo stlist, <<
    ⊒V ∗ TSeqLocal N γg l M ∗ TSeqPerm γg l (λ m, m =? n) ∗
    ⌜ N ## histN ⌝
  ¦
    ▷ TSeqInv γg γs l E omo stlist R  > >
      code_turnSequencer.waitForTurn [ #l; #n ]
  << RET #☠;
      R n ∗ TSeqComplete γg l n
      ¦
      (
      ∃ V', ask_for V' ∗ (* ask for dv_out *)
      ∃ M' omo' stlist',
      let E' := E ++ [mkOmoEvent (Take n) V' M'] in
      ▷ TSeqInv γg γs l E' omo' stlist' R ∗ OmoTokenR γg (length E) ∗
      ⊒V' ∗ @{V'} TSeqLocal N γg l M' ∗ ⌜ V ⊑ V' ∧ M ⊆ M' ∧ omo' = omo_insert_r omo (length omo - 1) (length E) ∧ stlist' = stlist ⌝)
    > >.
Proof using All.
  iStep 3. iLöb as "IH". oSteps.
  - iExists None. oSteps. have [LE1 LE2] : x5 ⊑ x24 ∧ x23 ⊑ x24 by clear -H13; solve_lat.
    rewrite -H14 /= in H16. subst x8. destruct (decide (x7 = n)) as [->|NEQ].
    + iLeft. iExists x24. iRename select (OmoAuth γg γs _ _ _ _ _)%E into "M●". iDestruct (OmoAuth_wf with "M●") as %[OMO_GOOD _].
      iDestruct (OmoAuth_omo_nonempty with "M●") as %Nomo. have NZomo : length x10 ≠ 0 by destruct x10. apply omo_stlist_length in OMO_GOOD as EQlenST.
      have Hst : x11 !! (length x10 - 1)%nat = Some x21 by rewrite last_lookup' -EQlenST in H2.
      iAssert (⌜ OmoUBgen x10 ({[x21.1.1.1]} ∪ x21.2 ∪ M) (length x10 - 1) ⌝)%I with "[-]" as %MAXgen.
      { iIntros "%e %eIN". have [eIN'|eIN'] : e ∈ {[x21.1.1.1]} ∪ x21.2 ∨ e ∈ M; [set_solver +eIN|..];
        [iDestruct (OmoEview_get_from_Einfo _ x21.1.1.1 with "[$]") as "#⊒x21"; rewrite -H10|];
        [iDestruct (OmoAuth_OmoEview_obj _ _ x20.(sync) _ _ _ _ ({[x21.1.1.1]} ∪ x21.2) with "M● [$]") as %VALM
        |iDestruct (OmoAuth_OmoEview_obj _ _ x5 _ _ _ _ M with "M● []") as %VALM; [oSteps|]];
        apply VALM in eIN'; (eapply lookup_omo_surjective in OMO_GOOD as [eidx Heidx]; [|exact eIN']); apply lookup_omo_lt_Some in Heidx as LT;
        iPureIntro; exists eidx; (split; [done|lia]). }
      iStepSafest. iAssert (⌜ n = length (omo_write_op x16) - 1 ⌝)%I with "[-]" as %EQgen.
      { destruct (decide (n = length (omo_write_op x16) - 1)) as [->|NEQ]; [done|].
        symmetry in H12. apply lookup_lt_Some in H12 as LT. have LT' : n < x21.1.1.2 by lia.
        iRename select (⎡own x3 (set_cf (λ m, m =? n))⎤)%I into "H". iRename select (⎡own x3 (set_cf _)⎤)%I into "H'".
        iCombine "H H'" as "H". iDestruct (own_valid with "H") as %VALID%(set_cf_excl _ _ n). simpl in VALID.
        destruct (x21.1.1.2); try lia. have LE : n ≤ n0 by lia. rewrite -Nat.leb_le in LE. rewrite LE (_: n =? n = true) in VALID; [done|by rewrite Nat.eqb_eq]. }
      have EQx12 : x12 = x6 by rewrite last_lookup' -EQgen -H12 in H3; inversion H3.
      subst x12. iDestruct (OmoEinfo_agree _ _ x13 x25 with "[$] [$]") as %<-. rewrite -H4 in H14. inversion H14. subst n x14.
      have EQgen : x21.1.1.2 = length (omo_write_op x16) - 1 by lia. have LEx20x24 : x20.(sync) ⊑ x24 by solve_lat.
      iExists _. iSplitR; [|iSplitR; first iSplitR; [by iPureIntro|iModIntro; iSplit; try done|oSteps]].
      { iPureIntro. destruct x21 as [[[? ?] ?] ?]. simpl in *. eapply tseq_step_Take;
        [by rewrite /= EQgen|lia|simpl; rewrite -H8 in H9; clear -H9 H13; solve_lat|simpl; set_solver-]. }
      { have LE : x5 ⊑ x24 by clear -H13; solve_lat. iApply OmoEview_union_obj; [|oSteps].
        iDestruct (OmoEview_get_from_Einfo _ x21.1.1.1 with "[$]") as "#⊒x21". rewrite -H10.
        iDestruct (view_at_mono_2 _ x24 with "⊒x21") as "⊒x21'"; [done|]. done. } { by rewrite omo_rewrite_hints in H7. }
      iRight. oSteps. iRename select (⎡own x3 (set_cf (λ m, m =? length x16 - 1))⎤)%I into "Hx3".
      rewrite {1}(set_cf_split _ (λ m : nat, m =? x21.1.1.2)). iDestruct "Hx3" as "[Hx3 Hx3']".
      rewrite (set_cf_equiv _ (λ m, m =? x21.1.1.2)); last first.
      { intros. simpl. destruct (decide (a = x21.1.1.2)) as [->|NEQ]; [|by rewrite -Nat.eqb_neq in NEQ;rewrite NEQ andb_comm].
        rewrite omo_rewrite_hints in H7. rewrite -H7. by destruct (x21.1.1.2 =? x21.1.1.2). }
      oSteps; [by rewrite -H4 H7 omo_rewrite_hints|]. iSplitR; [|oSteps; rewrite bool_decide_true; [|lia]; oSteps].
      { iAssert (@{x24} OmoEview_or_empty γg (x20.(eview)))%I with "[-]" as "?"; [destruct x20; oSteps|]. iModIntro. by rewrite H10. }
      rewrite H7 omo_rewrite_hints. do 3 iStepSafest. iExists x6. oSteps; [by rewrite -H4 -H17 omo_rewrite_hints|by rewrite H6].
    + iAssert (⌜ x7 < n ⌝)%I with "[-]" as %LTx7.
      { destruct (le_lt_dec n x7) as [LE|LT]; [|iPureIntro;lia]. symmetry in H12. apply lookup_lt_Some in H12 as LT. have LTn : n < x21.1.1.2 by lia.
        iRename select (⎡own x3 (set_cf (λ m, m =? n))⎤)%I into "H". iRename select (⎡own x3 (set_cf _)⎤)%I into "H'".
        iCombine "H H'" as "H". iDestruct (own_valid with "H") as %VALID%(set_cf_excl _ _ n). simpl in VALID.
        destruct (x21.1.1.2); try lia. have LE' : n ≤ n0 by lia. rewrite -Nat.leb_le in LE'. rewrite LE' (_: n =? n = true) in VALID; [done|by rewrite Nat.eqb_eq]. }
      iRight. oSteps; [by rewrite omo_rewrite_hints in H7|]. iLeft. unseal_diaframe. simpl. oSteps; [by rewrite -H14|].
      rewrite bool_decide_false; [|lia]. oSteps. rewrite bool_decide_false; [|lia]. oSteps.
  - iExists None. oSteps. have [LE1 LE2] : x5 ⊑ x24 ∧ x23 ⊑ x24 by clear -H13; solve_lat. iRight. destruct (decide (x7 = n)) as [->|NEQ].
    { symmetry in H12. apply lookup_lt_Some in H12 as LT. destruct (decide (n = x21.1.1.2)) as [EQ|NEQ'].
      - iRename select (⎡own x3 (set_cf (λ m, m =? n))⎤)%I into "H". iRename select (⎡own x3 (set_cf _)⎤)%I into "H'". subst n.
        iCombine "H H'" as "H". iDestruct (own_valid with "H") as %VALID%(set_cf_excl _ _ x21.1.1.2).
        rewrite (_: x21.1.1.2 =? x21.1.1.2 = true) in VALID; [done|by rewrite Nat.eqb_eq].
      - have LTn : n < x21.1.1.2 by lia. iRename select (⎡own x3 (set_cf (λ m, m =? n))⎤)%I into "H".
        iRename select (⎡own x3 (set_cf (λ m, match x21.1.1.2 with | 0 => false | S m' => m <=? m' end))⎤)%I into "H'".
        iCombine "H H'" as "H". iDestruct (own_valid with "H") as %VALID%(set_cf_excl _ _ n). simpl in VALID.
        destruct (x21.1.1.2); try lia. have LE' : n ≤ n0 by lia. rewrite -Nat.leb_le in LE'. rewrite LE' (_: n =? n = true) in VALID; [done|by rewrite Nat.eqb_eq]. }
    iAssert (⌜ x7 < n ⌝)%I with "[-]" as %LTx7.
    { destruct (le_lt_dec n x7) as [LE|LT]; [|iPureIntro;lia]. symmetry in H12. apply lookup_lt_Some in H12 as LT. have LTn : n < x21.1.1.2 by lia.
      iRename select (⎡own x3 (set_cf (λ m, m =? n))⎤)%I into "H".
      iRename select (⎡own x3 (set_cf (λ m, match x21.1.1.2 with | 0 => false | S m' => m <=? m' end))⎤)%I into "H'".
      iCombine "H H'" as "H". iDestruct (own_valid with "H") as %VALID%(set_cf_excl _ _ n). simpl in VALID.
      destruct (x21.1.1.2); try lia. have LE' : n ≤ n0 by lia. rewrite -Nat.leb_le in LE'. rewrite LE' (_: n =? n = true) in VALID; [done|by rewrite Nat.eqb_eq]. }
    oSteps; [by rewrite omo_rewrite_hints in H7|]. iRight. oSteps. rewrite -H14 /= in H16. subst x8.
    oSteps. rewrite bool_decide_false; [|lia]. oSteps. rewrite bool_decide_false; [|lia]. oSteps.
    Unshelve. all: pure_solver.trySolvePure.
Qed.

#[global] Instance complete_dspec N γg γs l V M n R :
  SPEC ⟨ ⊤ , ↑N , ↑histN⟩ E omo stlist, <<
    ⊒V ∗ TSeqLocal N γg l M ∗ R (n + 1)%nat ∗ TSeqComplete γg l n
  ¦
    ▷ TSeqInv γg γs l E omo stlist R  > >
      code_turnSequencer.completeTurn [ #l; #n ]
  << RET #☠;
      emp
      ¦
      (
      ∃ V', ask_for V' ∗ (* ask for dv_out *)
      ∃ M' omo' stlist',
      let E' := E ++ [mkOmoEvent (Complete n) V' M'] in
      ▷ TSeqInv γg γs l E' omo' stlist' R ∗ OmoTokenW γg (length E) ∗
      ⊒V' ∗ @{V'} TSeqLocal N γg l M' ∗ ⌜ V ⊑ V' ∧ M ⊆ M' ∧ omo' = omo_append_w omo (length E) [] ∧ stlist' = stlist ++ [(length E, (n + 1)%nat, V', M')] ⌝)
    > >.
Proof using All.
  oSteps. iExists None. oSteps. iDestruct (OmoAuth_swriter_token_agree_obj_1 l x1 x2 (x22 ⊔ x27) with "[$] [$] [$]") as %?.
  iRight. rewrite H19 omo_rewrite_hints -H5 in H1. inversion H1. subst x16. clear H1.
  iDestruct (OmoEinfo_agree _ _ x10 x17 with "[$] [$]") as %<-. rewrite -H6 /= in H2. inversion H2. have EQ : n = x25.1.1.2 by lia. subst n. clear H20 H2.
  oSteps; [by rewrite omo_rewrite_hints in H9|]. iRight. oSteps; [by rewrite -H6 H9 omo_rewrite_hints|].
  rewrite -H6 in H16. inversion H16. subst x7 x12. clear H16. oSteps. rewrite bool_decide_true; [|done]. oSteps. iLeft. iExists x16. oSteps.
  rewrite -H28 -H5 in H2. inversion H2. subst x31. iDestruct (OmoEinfo_agree _ _ x10 x32 with "[$] [$]") as %<-.
  iAssert (@{x16} OmoEview_or_empty γg x39.(eview))%I with "[-]" as "#?".
  { rewrite H20 in H3. have LE : x39.(sync) ⊑ x16 by solve_lat.
    iDestruct (OmoEview_get_from_Einfo _ x40.1.1.1 x39 with "[$]") as "H". iApply (view_at_mono with "H"); [done|]. oSteps. }
  destruct x40 as [[[? ?] ?] ?]. simpl in *. iExists _. iSplitR.
  { iPureIntro. apply tseq_step_Complete; [|lia|simpl;rewrite H22 -H20; solve_lat|instantiate (1 := ({[x40.1.1.1]} ∪ x40.2 ∪ M)); set_solver-].
    simpl. rewrite -H6 in H16. inversion H16. have EQ : n = x25.1.1.2 by lia. rewrite EQ. done. }
  oSteps; [iPureIntro; rewrite -H20; solve_lat|]. iSplitR; [by rewrite H24|]. have NZ : length x35 ≠ 0 by destruct x35, x20. oSteps.
  { rewrite H9 omo_write_op_length H28 !omo_rewrite_hints. by replace (Z.of_nat (length x35 - 1) + 1)%Z with (Z.of_nat (length x35 - 1 + 1)) by lia. }
  { rewrite app_length omo_rewrite_hints /=. iPureIntro. lia. } iRename select (⎡own x3 _⎤)%I into "H1".
  iRename select (⎡own x3 (set_cf (λ m, match length x35 - 1 with | 0 => false | S m' => m <=? m' end))⎤)%I into "H2".
  iCombine "H1 H2" as "H". iSplitL "H".
  { iDestruct (own_valid with "H") as %valid. rewrite set_cf_combine; [|done]. rewrite set_cf_equiv; [iModIntro; oSteps|].
    intros. simpl. rewrite Nat.sub_add; [|lia]. replace (length x35) with (S (length x35 - 1)) by lia. simpl. rewrite Nat.sub_0_r.
    have [CASE|[CASE|CASE]] : a < length x35 - 1 ∨ a = length x35 - 1 ∨ length x35 - 1 < a by lia.
    - replace (length x35 - 1) with (S (length x35 - 2)) by lia. rewrite (_: a <=? length x35 - 2 = true); [|rewrite Nat.leb_le; lia].
      rewrite (_: a <=? S (length x35 - 2) = true); [|rewrite Nat.leb_le; lia]. rewrite (_: a =? S (length x35 - 2) = false); [done|rewrite Nat.eqb_neq; lia].
    - have LEa : a ≤ length x35 - 1 by lia. rewrite -Nat.leb_le in LEa. rewrite -Nat.eqb_eq in CASE. rewrite LEa CASE. done.
    - rewrite (_: a =? length x35 - 1 = false); [|rewrite Nat.eqb_neq; lia]. rewrite (_: a <=? length x35 - 1 = false); [|rewrite Nat.leb_gt; lia].
      destruct (length x35 - 1); [done|]. rewrite (_: a <=? n = false); [done|rewrite Nat.leb_gt; lia]. }
  oSteps. iLeft. rewrite {5}H9 omo_rewrite_hints (omo_write_op_length x20) H28 omo_rewrite_hints Nat.sub_add; [|lia].
  unseal_diaframe. oSteps; [|rewrite H20 in H3; clear -H3 H13 H15 H27 H29; solve_lat|by rewrite H9 H28 omo_rewrite_hints Nat.sub_add; [|lia]].
  rewrite H9 H28 omo_rewrite_hints. replace (Z.of_nat (length x35 - 1) + 1)%Z with (Z.of_nat (length x35)) by lia. done.
Qed.

#[local] Opaque TSeqLocal TSeqInv TSeqPerm TSeqComplete.

Lemma wait_spec :
  wait_spec' code_turnSequencer.waitForTurn TSeqLocal TSeqInv TSeqPerm TSeqComplete.
Proof using All. oSteps; [iRight; oSteps|]. iLeft. unseal_diaframe. oSteps. Qed.

Lemma complete_spec :
  complete_spec' code_turnSequencer.completeTurn TSeqLocal TSeqInv TSeqComplete.
Proof using All. oSteps. instantiate (1 := x8). oSteps; [iRight; oSteps|iLeft]. unseal_diaframe. oSteps. Qed.
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
