From gpfsl.examples.lock Require Import code_spin_lock spec_trylock_history.
From gpfsl.examples Require Import uniq_token.
From gpfsl.logic Require Import proofmode repeat_loop new_delete atomics invariants.

From gpfsl.lang Require Import notation.

From gpfsl.base_logic Require Import meta_data.
From gpfsl.examples.omo Require Import omo omo_preds omo_preds_diaframe append_only_loc.

From gpfsl.diaframe Require Import vprop_weakestpre spec_notation
 vprop_weakestpre_logatom atom_spec_notation proof_automation omo_specs omo_hints.

From diaframe Require Import proofmode_base lib.except_zero own_hints steps.verify_tac util_instances.
From diaframe.symb_exec Require Import weakestpre_logatom.
From Hammer Require Import Tactics.

Require Import iris.prelude.options.

Local Open Scope nat_scope.

Section spinlock.

Context `{!noprolG Σ, !uniqTokG Σ, !atomicG Σ, !omoGeneralG Σ, !omoSpecificG Σ lock_event_hist lock_state, !appendOnlyLocG Σ}.

Implicit Types
  (γg γl γs γsl γtok γm : gname)
  (omo omol : omoT)
  (E : history lock_event_hist)
  (El : history loc_event)
  (eV : omo_event lock_event_hist)
  (eVl : omo_event loc_event)
  (uf : gset val)
  (ty : append_only_type).

Notation iProp := (iProp Σ).
Notation vProp := (vProp Σ).

Definition Locked : LockedT Σ :=
  λ (γg : gname) (l : loc),
    (∃ γl γs γsl γm es M e el (st : lock_state) st_e st_b st_V st_lV,
      meta l nroot (γl,γs,γsl,γm) ∗ swriter_token l γl es ∗ OmoEview γg M ∗
      MatchValue (Some el) (last es) ∗
      OmoCW γg γl e el ∗ OmoSnap γg γs e st ∗
      ⌜ st = (st_e, st_b, st_V, st_lV) ⌝ ∗
      ⌜ st_e ∈ M ∧ st_lV ⊆ M ⌝)%I.

Definition AllWrEvents_inner γg γl γs γm el : vProp :=
  ∃ (v : Z) (V : view) eVl e eV (st : lock_state) st_e st_b st_V st_lV,
    OmoEinfo γl el eVl ∗
    OmoCW γg γl e el ∗ CWMonoValid γm e ∗
    OmoSnap γg γs e st ∗
    ⌜ st = (st_e, st_b, st_V, st_lV) ⌝ ∗
    OmoEinfo γg e eV ∗
    MatchValue (#v, V) (loc_event_msg eVl.(type)) ∗
    ⌜ (v = 0%Z ↔ st_b = false) ⌝.

Definition AllWrEvents γg γl γs γm es : vProp :=
  [∗ list] el ∈ es, AllWrEvents_inner γg γl γs γm el.

Global Instance AllWrEvents_inner_persistent γg γl γs γm el : Persistent (AllWrEvents_inner γg γl γs γm el) := _.
Global Instance AllWrEvents_inner_timeless γg γl γs γm el : Timeless (AllWrEvents_inner γg γl γs γm el) := _.
Global Instance AllWrEvents_persistent γg γl γs γm es : Persistent (AllWrEvents γg γl γs γm es) := _.
Global Instance AllWrEvents_timeless γg γl γs γm es : Persistent (AllWrEvents γg γl γs γm es) := _.

Definition last_msg_info γg γl γs (is_locked : bool) es P (stf : lock_state) : vProp :=
  ∃ elf eVlf (vf : Z) Vf (eVf : omo_event lock_event_hist) et st_e st_b st_V st_lV ,
    MatchValue (Some elf) (last es) ∗
    ⌜ stf = (st_e, st_b, st_V, st_lV) ⌝ ∗

    OmoEinfo γl elf eVlf ∗
    MatchValue (#vf, Vf) (loc_event_msg eVlf.(type)) ∗
    (⌜is_locked = true ∧ vf ≠ 0%Z ∧ st_b = true ⌝ ∨ (@{Vf} P ∗ ⌜is_locked = false ∧ vf = 0%Z ∧ st_b = false ∧ stf.1.2 ⊑ Vf ⌝)) ∗

    OmoEinfo γg st_e eVf ∗
    (⌜ eVf = mkOmoEvent et st_V st_lV ⌝ ∗ emp) ∗
    OmoCW γg γl st_e elf ∗
    OmoSnap γg γs st_e stf.

Global Instance last_msg_info_objective γg γl γs is_locked es P stf : Objective (last_msg_info γg γl γs is_locked es P stf).
Proof. repeat (apply exists_objective; intros). repeat (apply sep_objective; [apply _|]). destruct (is_locked); apply _. Qed.

Definition seen_event_info γg γl γm E : vProp :=
  [∗ list] e↦eV ∈ E,
    ∃ e', OmoCW γg γl e e' ∗ OmoHb γg γl e e' ∗ CWMonoValid γm e.

Definition LockInv (γg : gname) (l : loc) (P : vProp) E : vProp :=
  ∃ γl γs γsl γm (is_locked : bool) El omo omol stlist stf mo uf ty Vb Mono,
    meta l nroot (γl,γs,γsl,γm) ∗
    ask_for is_locked ∗
    ⌜(is_locked = true ∧ ty = swriter) ∨ (is_locked = false ∧ ty = cas_only)⌝ ∗
    @{Vb} append_only_loc l γl uf ty ∗
    ⌜ #0 ∉ uf ⌝ ∗

    try_update_OmoAuth_to γl El omol mo ∗
    try_update_OmoAuth_to γg E omo stlist ∗

    MatchValue (Some stf) (last stlist) ∗
    last_msg_info γg γl γs is_locked (omo_write_op omol) P stf ∗

    AllWrEvents γg γl γs γm (omo_write_op omol) ∗
    seen_event_info γg γl γm E ∗
    CWMono γg γl γm Mono ∗

    OmoAuth γl γsl (1/2)%Qp El omol mo _ ∗
    OmoAuth γg γs 1 E omo stlist _
    .

Definition LockLocal: LockLocalNT Σ :=
  (λ (_: namespace) γg l E M,
  ∃ γl γs γsl γm Ml,
    meta l nroot (γl,γs,γsl,γm) ∗
    OmoSnapHistory γg E ∗
    OmoEview γg M ∗
    OmoEview γl Ml)%I.

Global Instance LockInv_objective γg l P E : Objective (LockInv γg l P E) := _.
Global Instance LockLocal_persistent N γg l E M : Persistent (LockLocal N γg l E M) := _.

Lemma AllWrEvents_acc γg γl γs γm es el :
  el ∈ es →
  AllWrEvents γg γl γs γm es -∗ AllWrEvents_inner γg γl γs γm el.
Proof. iIntros "%INCL #AllWrEvents". apply elem_of_list_lookup in INCL as [gen LOOKUP]. by rewrite /AllWrEvents big_sepL_lookup. Qed.

Local Tactic Notation "simplify_meta" "with" constr(Hs) :=
  iDestruct (meta_agree with Hs) as %[[-> ->]%pair_inj ->]%pair_inj.

Lemma LockInv_Linearizable_instance :
  ∀ γg l P E, LockInv γg l P E ⊢ ⌜ Linearizability E ⌝.
Proof. intros. iStep; iDestruct (OmoAuth_Linearizable with "[$]") as %LIN; by apply omo_compatible in LIN. Qed.

Lemma LockInv_history_wf_instance :
  ∀ γg l P E, LockInv γg l P E ⊢ ⌜ history_wf E ⌝.
Proof. intros. iStep; by iDestruct (OmoAuth_wf with "[$]") as %[_ ?]. Qed.

Lemma LockInv_LockLocal_instance :
  ∀ N γg l P E E' M',
    LockInv γg l P E -∗ LockLocal N γg l E' M' -∗ ⌜ E' ⊑ E ⌝.
Proof. intros. iStep 2; by iDestruct (OmoAuth_OmoSnapHistory with "[$] [$]") as %?. Qed.

Lemma LockLocal_lookup_instance :
  ∀ N γg l E M e V,
    sync <$> E !! e = Some V → e ∈ M →
    LockLocal N γg l E M -∗ ⊒V.
Proof. intros. iDestruct 1 as (?????) "(_ & E◯ & M◯ & _)". by iApply (OmoSnapHistory_OmoEview with "E◯ M◯"). Qed.

Definition new_lock_spec :
  new_lock_spec' code_spin_lock.new_lock LockInv LockLocal.
Proof.
  iSteps as (??P???l) "P????". rewrite shift_0. iStep 8 as "l↦". iDestruct (view_at_intro with "P") as (V) "[#⊒V P]".
  iMod (append_only_loc_cas_only_from_na_rel with "⊒V [l↦]") as (γl γsl V0 eVl0)
    "(#⊒V0 & Ml● & [#Ml◯ H] & omol↦ & WCOMMIT & #el0✓eVl0 & [%HeVl0 %eVl0SYNC])"; [|iSteps|]; [done|].
  iDecompose "H". iDecompose "⊒V0" as "⊒V".

  set M := {[0%nat]}.
  set eVinit := mkOmoEvent Init V0 M.
  set initst := (0%nat, false, V0, M).

  iMod (@OmoAuth_alloc _ _ _ _ _ eVinit initst _ _ lock_interpretable with "WCOMMIT") as (γg γs)
        "(M● & #M◯ & #e0↦el0 & #e0✓eVinit & #e0↪init & _)"; [by apply lock_step_Init|done|].
  iMod (OmoHb_new_1 with "M● e0✓eVinit el0✓eVl0") as "[M● #e0⊒el0]"; [rewrite eVl0SYNC;solve_lat|].
  iDestruct (OmoHbToken_finish with "M●") as "M●".
  iMod (CWMono_new γg γl) as (γm) "MONO".
  iMod (CWMono_insert_last_last (wr_event 0) with "MONO M● Ml● e0↦el0") as "(MONO & #MONO✓e0 & M● & Ml●)"; [done|done|].
  iMod (meta_set _ _ (γl,γs,γsl,γm) nroot with "[$]") as "#Hms"; [done|].
  iDestruct (view_at_intro with "omol↦") as (?) "[_ omol↦]". iDecompose "M●" as "????????". iDecompose "e0↪init" as "?????".

  subst initst eVinit. iExists _, _, M. iSteps. iExists M. oSteps. iExists false.
  rewrite try_update_OmoAuth_to_eq. iStepSafest. iExists 0. iSplitR. { iPureIntro. instantiate (1 := (omo_append_w [] 0 [])). done. }
  do 2 (try (oSteps; iExists 0%Z,(eVl0.(sync)); rewrite HeVl0; oSteps); try iRight).
Qed.

(* When doing solveStep for [False] goal, not_false_is_true will be applied recursively to make meaningless tries. *)
#[local] Remove Hints ssrbool.not_false_is_true : core.

Set Nested Proofs Allowed.


#[global] Instance do_lock_dspec N γ l V M E1 :
  SPEC ⟨ ⊤ , ↑N , ↑histN⟩ E P, <<
    ⊒V ∗
    LockLocal N γ l E1 M ∗
    ⌜ N ## histN ⌝
  ¦
    ▷ LockInv γ l P E  > >
      code_spin_lock.do_lock [ #l ]
  << RET #☠;
      P ∗ Locked γ l
      ¦
      (
      ∃ V', ask_for V' ∗ (* ask for sync view *)
      ∃ M',
      let E' := E ++ [mkOmoEvent Lock V' M'] in
      ▷ LockInv γ l P E' ∗
      ⌜ V ⊑ V' ∧ M ⊆ M' ⌝ ∗
      ⊒V' ∗ @{V'} LockLocal N γ l E' M')
    > >.
Proof using All.
  iStep 6. iLöb as "IH". oSteps.
  - (* lock was locked. cas must fail. retry. *) iExists None. oSteps. iExists x33. oSteps. iRight. oSteps. iExists true. oSteps.
  - (* lock was unlocked. *) iExists (Some x5). oSteps; [iRight; oSteps; iExists false; oSteps; iSteps|].
    (* unlock succeeded. *) iLeft. iExists x28. oSteps. iExists true. oSteps. iExists (wr_event (length x19)).
    oSteps. iExists _. iSplitR. { iPureIntro. apply lock_step_Lock; simpl; try done; [solve_lat|]. instantiate (1 := ({[x35]} ∪ x39 ∪ M)). set_solver-. }
    do 3 (iStepSafest; iExists _; rewrite omo_rewrite_hints). do 18 iStepSafest. iExists _, ({[length x10; x35]} ∪ x39 ∪ M).
    oSteps. Unshelve. all: try by rewrite !omo_rewrite_hints.
Qed.

#[global] Instance unlock_dspec N γ l V M E1 P :
  SPEC ⟨ ⊤ , ↑N , ↑histN⟩ E, <<
    ⊒V ∗
    LockLocal N γ l E1 M ∗
    P ∗ Locked γ l ∗
    ⌜ N ## histN ⌝
  ¦
    ▷ LockInv γ l P E  > >
      code_spin_lock.unlock [ #l ]
  << RET #☠;
      emp
      ¦
      (
      ∃ V', ask_for V' ∗ (* ask for sync view *)
      ∃ M',
      let E' := E ++ [mkOmoEvent Unlock V' M'] in
      ▷ LockInv γ l P E' ∗
      ⌜ V ⊑ V' ∧ M ⊆ M' ⌝ ∗
      ⊒V' ∗ @{V'} LockLocal N γ l E' M')
    > >.
Proof using All.
  iStep 7 as "?????????? Hwriter_token HAU". iIntros "!>".
  iMod "HAU" as (xs) "[HL HAUcl]". iDecompose "HL" as "??????????? Happloc ? Hmaster ?"| ""; [|iSteps].
  iDestruct (OmoAuth_swriter_token_agree_obj_2 with "Hmaster Happloc Hwriter_token") as %->.
  iAssert ⌜x13 = x7⌝%I as "Hpure"; [iPureIntro; congruence|]. iDecompose "Hpure".
  iDestruct (atomic.diaframe_close_right with "HAUcl") as "HAU". oSteps. (* commit AU *)
  iExists x13. oSteps. iExists false. oSteps; [iPureIntro; rewrite -H9; set_solver|].
  iAssert ⌜{| type := x27; sync := x32; eview := x33 |}.(sync) ⊑ x6⌝%I with "[]" as %LE.
  { iApply OmoEinfo_OmoEview_obj; try done. oSteps. }
  iExists _. iSplitR.
  { iPureIntro. apply lock_step_Unlock; simpl; try done; [solve_lat|]. instantiate (1 := {[x30]} ∪ x33 ∪ M). set_solver-. }
  oSteps; [solve_lat|solve_lat|]. iRight. oSteps; solve_lat.
Qed.

#[global] Instance try_lock_dspec N γ l V M E1 P :
  SPEC ⟨ ⊤ , ↑N , ↑histN⟩ E, <<
    ⊒V ∗
    LockLocal N γ l E1 M ∗
    ⌜ N ## histN ⌝
  ¦
    ▷ LockInv γ l P E  > >
      code_spin_lock.try_lock [ #l ]
  << (b : bool) ev, RET #b;
    if b then (P ∗ Locked γ l) else emp
      ¦
      (
      ∃ V', ask_for V' ∗ (* ask for sync view *)
      ∃ M',
      let E' := E ++ [mkOmoEvent ev V' M'] in
      ⌜if b then ev = Lock else ev = Trylock⌝ ∗
      ▷ LockInv γ l P E' ∗
      ⌜ V ⊑ V' ∧ M ⊆ M' ⌝ ∗
      ⊒V' ∗ @{V'} LockLocal N γ l E' M')
  > >.
Proof using All.
  oSteps; (iDestruct (OmoEview_update γ x1 with "[$] [] []") as (Ml1) "H"; [iSteps..|]); iDecompose "H"; iExists (Some Ml1); oSteps.
  - (* lock is locked *) iLeft. iExists x30. oSteps. iExists false,_. oSteps. iExists true. iAssert (OmoUB γ M x35) as "#?".
    { rewrite {2}/OmoUB big_sepS_forall. iIntros "%e %eM". iAssert (OmoEview γ M) as "M◯". { iApply view_at_elim; iSteps. }
      iRename select (OmoAuth γ _ _ _ _ _ _) into "M●". iRename select (OmoAuth x1 _ _ _ _ _ _) into "Ml●".
      iDestruct (OmoAuth_OmoEview with "M● M◯") as %MIncl.
      specialize (MIncl _ eM) as [eV Elookup]. iRename select (seen_event_info γ _ _ _) into "Seen".
      rewrite /seen_event_info big_sepL_lookup; [|done]. iDestruct "Seen" as "(%e' &  e↦e' & e⊒e' & MONO✓e)".
      iDestruct (OmoHb_HbIncluded with "e⊒e' [$]") as %e'Ml0'; [done|].
      rewrite /OmoUB (big_sepS_elem_of _ _ e'); [|set_solver].
      iApply (CWMono_acc with "[$] MONO✓e [$] e↦e' [$] [$]"). }
    assert (x40 = true) as ->; first by destruct x40; sauto. oSteps. iExists (x39, true, x41, x42). iSplitR.
    { iPureIntro. apply lock_step_Trylock; try done. instantiate (1 := M). simpl. set_solver-. }
    oSteps. iExists x35. oSteps.
  - (* lock is unlocked but cas failed *) iLeft. iExists x27. oSteps. iExists false,_. oSteps. iExists false. iAssert (OmoUB γ M x34) as "#?".
    { rewrite {2}/OmoUB big_sepS_forall. iIntros "%e %eM". iAssert (OmoEview γ M) as "M◯". { iApply view_at_elim; iSteps. }
      iRename select (OmoAuth γ _ _ _ _ _ _) into "M●". iRename select (OmoAuth x1 _ _ _ _ _ _) into "Ml●".
      iDestruct (OmoAuth_OmoEview with "M● M◯") as %MIncl.
      specialize (MIncl _ eM) as [eV Elookup]. iRename select (seen_event_info γ _ _ _) into "Seen".
      rewrite /seen_event_info big_sepL_lookup; [|done]. iDestruct "Seen" as "(%e' &  e↦e' & e⊒e' & MONO✓e)".
      iDestruct (OmoHb_HbIncluded with "e⊒e' [$]") as %e'Ml0'; [done|].
      rewrite /OmoUB (big_sepS_elem_of _ _ e'); [|set_solver].
      iApply (CWMono_acc with "[$] MONO✓e [$] e↦e' [$] [$]"). }
    assert (x39 = true) as ->; first by destruct x39; sauto. oSteps. iExists (x38, true, x40, x41). iSplitR.
    { iPureIntro. apply lock_step_Trylock; try done. instantiate (1 := M). simpl. set_solver-. }
    oSteps. iRight. oSteps. iExists x34. oSteps.
  - (* cas success *) iLeft. iExists x27. oSteps. iExists true,_. oSteps.
    iExists true. oSteps. iExists (wr_event (length x18)). oSteps. iExists _. iSplitR.
    { iPureIntro. apply lock_step_Lock; try done; [solve_lat|]. instantiate (1 := {[x34]} ∪ x38 ∪ M). set_solver-. }
    do 3 (iStepSafest; iExists _; rewrite omo_rewrite_hints). do 7 iStepSafest. iExists ({[length x10; x34]} ∪ x38 ∪ M). oSteps.
    Unshelve. all: try pure_solver.trySolvePure; try by rewrite !omo_rewrite_hints.
Qed.

Section spec_translation.

#[local] Opaque LockInv Locked LockLocal.

Definition do_lock_spec :
  do_lock_spec' code_spin_lock.do_lock LockInv LockLocal Locked.
Proof using All.
  iStepsSafest. { iRight. iSteps. }
  iLeft. unseal_diaframe; simpl.
  iRename select (⊒_)%I into "⊒V". iAssert (⊒x9)%I as "{⊒V} ?". { iSteps. }
  iStepsSafest.
Qed.

Definition try_lock_spec :
  try_lock_spec' code_spin_lock.try_lock LockInv LockLocal Locked.
Proof using All.
  iStepsSafest. { iRight. iSteps. }
  iLeft. unseal_diaframe; simpl.
  iRename select (⊒_)%I into "⊒V". iAssert (⊒x12)%I as "{⊒V} ?". { iSteps. }
  iStepsSafest.
Qed.

Definition unlock_spec :
  unlock_spec' code_spin_lock.unlock LockInv LockLocal Locked.
Proof using All.
  iStepsSafest. instantiate (1 := x3). iStepsSafest. { iRight. iSteps. }
  iLeft. unseal_diaframe; simpl.
  iRename select (⊒_)%I into "⊒V". iAssert (⊒x9)%I as "{⊒V} ?". { iSteps. }
  iStepsSafest.
Qed.

End spec_translation.


End spinlock.

Definition spinlock_trylock_impl `{!uniqTokG Σ, !noprolG Σ, !atomicG Σ, !omoGeneralG Σ, !omoSpecificG Σ lock_event_hist lock_state, !appendOnlyLocG Σ}
  : lock_spec Σ := {|
    spec_trylock_history.LockInv_Objective := LockInv_objective;
    spec_trylock_history.LockInv_Linearizable := LockInv_Linearizable_instance;
    spec_trylock_history.LockInv_history_wf := LockInv_history_wf_instance;
    spec_trylock_history.LockInv_LockLocal := LockInv_LockLocal_instance;
    spec_trylock_history.LockLocal_lookup := LockLocal_lookup_instance;
    spec_trylock_history.LockLocal_Persistent := LockLocal_persistent;
    spec_trylock_history.new_lock_spec := new_lock_spec;
    spec_trylock_history.do_lock_spec := do_lock_spec;
    spec_trylock_history.try_lock_spec := try_lock_spec;
    spec_trylock_history.unlock_spec := unlock_spec;
  |}.
