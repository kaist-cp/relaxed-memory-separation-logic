From gpfsl.examples Require Import sflib.

From iris.algebra Require Import auth gset gmap agree.
From iris.algebra Require Import lib.mono_list.
From iris.proofmode Require Import tactics.

From gpfsl.base_logic Require Import meta_data.
From gpfsl.examples.algebra Require Import mono_list_list.
From gpfsl.logic Require Import logatom atomics invariants.

From gpfsl.logic Require Import repeat_loop new_delete.
From gpfsl.examples Require Import map_seq loc_helper.
From gpfsl.examples.stack Require Import spec_history code_treiber.
From gpfsl.examples.omo Require Import omo omo_preds omo_preds_diaframe append_only_loc.

From gpfsl.diaframe Require Import vprop_weakestpre spec_notation
 vprop_weakestpre_logatom atom_spec_notation proof_automation omo_specs omo_hints.

From diaframe Require Import proofmode_base lib.except_zero own_hints steps.verify_tac util_instances.
From diaframe.symb_exec Require Import weakestpre_logatom.

From Hammer Require Import Tactics.
From iris.proofmode Require Import intro_patterns.


Require Import iris.prelude.options.

(** Prove that Treiber stack satisfies the logically atomic, history-based
  specifications *)

#[local] Notation next := 0%nat (only parsing).
#[local] Notation data := 1%nat (only parsing).

#[local] Notation history := (history sevent_hist).
#[local] Notation omo_event := (omo_event sevent_hist).

Implicit Types
  (stk : stack_state) (node : event_id * Z * view * eView)
  (mo : list loc_state)
  (omo omoh : omoT)
  (Eh : omo_history.history loc_event)
  (M : eView)
  (s n: loc) (tid: thread_id) (γg γh γs : gname).

(** * The invariant and local assertions *)
Section Interp.
Context `{!noprolG Σ, !atomicG Σ, !omoGeneralG Σ, !omoSpecificG Σ sevent_hist stack_state, !appendOnlyLocG Σ}.

#[local] Notation iProp := (iProp Σ).
#[local] Notation vProp := (vProp Σ).
Local Open Scope nat_scope.

(** Physical resources of the node at loc [n] with a possible next node at [on'] *)
Definition StackNode n (on' : option loc) (v : Z) : vProp :=
  ∃ q, (n >> next) ↦{q} #(oloc_to_lit on') ∗
  (n >> data) ↦ #v
  (* ∗ ⎡ † n … 2 ⎤ *)
  .

(** [StackNode] for each nodes in having values in [vs]. *)
Fixpoint StackNodes (on : option loc) (vs : list Z) : vProp :=
  match (on, vs) with
  | (None, []) => True
  | (Some n, v :: vs') =>
      ∃ on', StackNode n on' v ∗ StackNodes on' vs'
  | _ => False
  end.

#[global] Instance StackNodes_timeless on vs : Timeless (StackNodes on vs).
Proof. elim: vs on => [|v vs' IH] [n|]; apply _. Qed.

Definition AllLinks_inner γg γh γs γm e' : vProp :=
  ∃ (ont : option loc) (st : stack_state) eV' (V : view) e,
    OmoEinfo γh e' eV' ∗
    OmoCW γg γh e e' ∗ CWMonoValid γm e ∗
    OmoSnap γg γs e st ∗
    MatchValue (#(oloc_to_lit ont), V) (loc_event_msg eV'.(type)) ∗
    match ont with
    | Some n => ∃ q on', @{V} (n >> next) ↦{q} #(oloc_to_lit on')
    | None => emp
    end ∗
    ⌜ (ont = None ↔ st = []) ⌝.

(** There's a node for each head ptr msgs. Used for [!("h" +ₗ #next)] in pop. *)
Definition AllLinks γg γh γs γm es : vProp :=
  [∗ list] e ∈ es, AllLinks_inner γg γh γs γm e.

Global Instance AllLinks_inner_objective γg γh γs γm e' : Objective (AllLinks_inner γg γh γs γm e').
Proof.
  do 5 (apply exists_objective; intros). repeat (apply sep_objective; [by apply _|]).
  by destruct x; apply _.
Qed.

Global Instance AllLinks_objective γg γh γs γm es : Objective (AllLinks γg γh γs γm es) := _.
Global Instance AllLinks_timeless γg γh γs γm es : Timeless (AllLinks γg γh γs γm es) := _.


Definition seen_event_info γg γh γm s (E : history) : vProp :=
  [∗ list] e↦eV ∈ E,
    ∃ el, OmoCW γg γh e el ∗ OmoHb γg γh e el ∗ CWMonoValid γm e.

Definition last_msg_info γg γh es stlist stk ont Vt : vProp :=
  ∃ el eVl,
    MatchValue (Some el) (last es) ∗
    OmoEinfo γh el eVl ∗
    MatchValue (#(oloc_to_lit ont), Vt) (loc_event_msg eVl.(type)) ∗
    ⌜ Some stk = last stlist ⌝ ∗
    [∗ list] st ∈ stk,
        OmoEinfo γg st.1.1.1 (mkOmoEvent (Push st.1.1.2) st.1.2 st.2) ∗
      ⌜ (0 < st.1.1.2)%Z ∧ st.1.2 ⊑ Vt ⌝.

(** ** Top-level predicates & invariant *)
Definition StackInv γg s E : vProp :=
  ∃ (γh : gname) Vb,
  (* head *)
  @{Vb} append_only_loc s γh ∅ cas_only ∗
  ∃ (γs γsh γm : gname) omo stlist stk Eh omoh mo (ont : option loc) Vt Mono,
  meta s nroot (γh,γs,γsh,γm) ∗

  try_update_OmoAuth_to γh Eh omoh mo ∗
  try_update_OmoAuth_to γg E omo stlist ∗

  (* Physical resources *)
  (* physical stack *)
  last_msg_info γg γh (omo_write_op omoh) stlist stk ont Vt ∗
  (* all nodes, including the popped ones *)
  AllLinks γg γh γs γm (omo_write_op omoh) ∗
  @{Vt} StackNodes ont stk.*1.*1.*2 ∗
  seen_event_info γg γh γm s E ∗
  CWMono γg γh γm Mono ∗
  (* Logical state *)
  OmoAuth γh γsh (1/2)%Qp Eh omoh mo _ ∗
  OmoAuth γg γs 1 E omo stlist _
  .

Global Instance StackInv_objective γg s E : Objective (StackInv γg s E) := _.
Global Instance StackInv_timeless γg s E : Timeless (StackInv γg s E) := _.

Definition StackLocal (_ : namespace) γg s (E : history) M : vProp :=
  ∃ (γh γs γsh γm : gname) Mh,
  meta s nroot (γh,γs,γsh,γm) ∗

  (* Local snapshot of the history and local observation of events *)
  OmoSnapHistory γg E ∗
  OmoEview γg M ∗
  OmoEview γh Mh
  .

Global Instance StackLocal_persistent N γg s E M :
  Persistent (StackLocal N γg s E M) := _.

#[global] Instance Inhabited_sevent_hist: Inhabited sevent_hist := populate Init.

End Interp.

(** * Proofs *)
Section proof.
Context `{!noprolG Σ, !atomicG Σ, !omoGeneralG Σ, !omoSpecificG Σ sevent_hist stack_state, !appendOnlyLocG Σ}.

#[local] Notation iProp := (iProp Σ).
#[local] Notation vProp := (vProp Σ).

Local Tactic Notation "simplify_meta" "with" constr(Hs) :=
  iDestruct (meta_agree with Hs) as %[[-> ->]%pair_inj ->]%pair_inj.

#[local] Ltac iDestructNth_ Hin n Hout :=
  let A := iFresh in
  iDestruct Hin as A;
  let H1 :=constr:(IList [cons (IDrop) (cons (IIdent A) nil)]) in
  let H2 :=constr:(IList [cons (IPure IGallinaAnon) (cons (IIdent A) nil)]) in
  do n (iDestruct A as H1 || iDestruct A as H2);
  iDestruct A as Hout
  .

#[local] Tactic Notation "iDestructNth" open_constr(Hin) integer(n) "as" constr(Hout) :=
  iDestructNth_ Hin n Hout.

Lemma StackInv_Linearizable_instance :
  ∀ γg s E, StackInv γg s E ⊢ ⌜ Linearizability E ⌝.
Proof.
  intros. iSteps.
  by iDestruct (OmoAuth_Linearizable with "[$]") as %LIN; apply omo_compatible in LIN.
Qed.

Lemma StackInv_history_wf_instance :
  ∀ γg s E, StackInv γg s E ⊢ ⌜ history_wf E ⌝.
Proof.
  intros. iSteps.
  by iDestruct (OmoAuth_wf with "[$]") as "[_ %H2]".
Qed.

Lemma StackInv_StackLocal_instance :
  ∀ N γg s E E' M',
    StackInv γg s E -∗ StackLocal N γg s E' M' -∗ ⌜ E' ⊑ E ⌝.
Proof.
  intros.
  iSteps.
  by iDestruct (OmoAuth_OmoSnapHistory with "[$] [$]") as %?.
Qed.

Lemma StackLocal_lookup_instance :
  ∀ N γg s E M e V,
    sync <$> E !! e = Some V → e ∈ M →
    StackLocal N γg s E M -∗ ⊒V.
Proof.
  intros. iSteps.
  by iApply (OmoSnapHistory_OmoEview with "[$] []"); try done; iSteps.
Qed.

Lemma new_stack_spec :
  new_stack_spec' new_tstack StackLocal StackInv.
Proof.
  iSteps. rewrite shift_0. iStep 9 as "Hs".
  (* The initial updates can't be automated since it creates variables needed for proving meta, but meta has to be at the start of the invariant for other proofs. *)
  iMod (append_only_loc_cas_only_from_na with "Hs") as (γh γsh ? ?) "H"; [done|]. iDecompose "H".
  set M := {[0%nat]}.
  set eVinit := mkOmoEvent Init eV.(sync) M.
  iMod (@OmoAuth_alloc _ _ _ _ _ eVinit init _ _ stack_interpretable with "[$]") as (γg γs) "H"; [by apply stack_step_Init|done| ..]. iDecompose "H".
  iMod (@OmoHb_new_1 _ loc_event _ _ _ _ _ _ γg γh with "[$] [$] [$]") as "[M● #e0⊒eh0]". { subst eVinit. simpl. solve_lat. }
  iDestruct (OmoHbToken_finish with "M●") as "M●".
  iMod (CWMono_new γg γh) as (γm) "MONO".
  iRename select (meta_token _ _) into "Hms". iMod (meta_set _ _ (γh,γs,γsh,γm) nroot with "Hms") as "#Hms"; [done|].
  iMod (@CWMono_insert_last_last _ loc_event _ _ _ _ _ _ (wr_event 0) with "MONO [$] [$] [$]") as "H"; [done..|]. iDecompose "H".
  iRename select (append_only_loc _ _ _ _)%I into "omo↦". iDestruct (view_at_intro with "omo↦") as (?) "[_ omo↦]".
  rewrite /StackInv !try_update_OmoAuth_to_eq. iStepSafest. iExists _,[eVinit]. oSteps.
  iExists 0. iSplitR. { iPureIntro. instantiate (1 := omo_append_w [] 0 []). done. }
  do 2 (try (oSteps; iExists None,(eV.(sync)); rewrite H0; oSteps); try (iExists []; iSplitR; [by iPureIntro; instantiate (1 := [[]])|])).
Qed.

#[local] Hint Extern 10 (BehindModal (fupd ?El ?Er) (?N ⊆ ?Er)) =>
  unify El Er; unfold BehindModal; pure_solver.trySolvePure : solve_pure_add.

#[local] Remove Hints ssrbool.not_false_is_true : core.

Set Nested Proofs Allowed.

#[global] Instance atom_try_push_internal N γg s E0 M V (v : Z) (n : loc) :
  SPEC ⟨ ⊤ , ↑N , ↑histN⟩ E, <<
    ⊒V ∗
    StackLocal N γg s E0 M ∗
    (n >> next) ↦ - ∗
    (n >> data) ↦ #v ∗
    ⌜ (0 < v)%Z ⌝ ∗
    ⌜ N ## histN ⌝
  ¦
    ▷ StackInv γg s E  > >
      try_push_internal [ #s ; #n]
  << (b : bool), RET #b;
      emp
      ¦
      (* PUBLIC POST *)
      (if b then (
        ∃ V', ⊒V' ∗
        ∃ M',
          let ps := Push v in
          let E' := E ++ [mkOmoEvent ps V' M'] in
          (* ps is a new push event with which E' strictly extends E *)
             ▷ StackInv γg s E' ∗ @{V'} StackLocal N γg s E' M' ∗ ⌜ V ⊑ V' ∧ M ⊆ M' ⌝
      ) else (
        ∃ somewhere,
        (* FAIL_RACE case *)
        (n >> next) ↦ somewhere ∗ (n >> data) ↦ #v ∗
        ▷ StackInv γg s E ∗
        ∃ V', ⊒V' ∗ @{V'} StackLocal N γg s E M
      ) ∗ emp )
    > >.
Proof using All.
  oSteps. iExists None. oSteps. iRight. oSteps. iExists None. oSteps; iLeft; [iExists false|iExists true]; oSteps.
  iExists _. iSplitR. { iPureIntro. apply stack_step_Push; [done..|shelve]. } oSteps. iPureIntro. iSteps.
  Unshelve. all: try pure_solver.trySolvePure.
Qed.

#[global] Instance dspec_atom_try_pop N V γg s E1 M :
  SPEC ⟨ ⊤ , ↑N , ↑histN⟩ E, <<
    ⊒V ∗
    StackLocal N γg s E1 M
  ¦
    ▷ StackInv γg s E  > >
      try_pop [ #s]
  << (v : Z), RET #v;
      emp
      ¦
      (* PUBLIC POST *)
      (if (decide (v = FAIL_RACE)) then (
        (* FAIL_RACE case *)
        ▷ StackInv γg s E ∗
        ∃ V', ⊒V' ∗ @{V'} StackLocal N γg s E M
      ) else (
        ∃ V', ⊒V' ∗ ⌜ V ⊑ V' ⌝ ∗
        ∃ pp, ⌜if (decide (v = EMPTY)) then pp = EmpPop  (* EMPTY case *)
          else (0 < v)%Z ∧ pp = Pop v⌝ ∗ (* successful case *)
        ∃ M'add e,
          let M' := {[e]} ∪ (M ∪ M'add) in
          let E' := E ++ [mkOmoEvent pp V' M'] in
             ▷ StackInv γg s E' ∗ @{V'} StackLocal N γg s E' M'
      ) ∗ emp )
    > >.
Proof using All.
  (* Read head *)
  oSteps. iDestruct (OmoEview_update γg x1 with "[$] [] []") as (Mh1) "H"; [iSteps..|]. iDecompose "H".
  iExists (Some Mh1). oSteps. iRename select (match x28 with |Some _ => _ | None => _ end)%I into "Case".
  destruct x28 as [n1|]; last first.
  { (* EMPTY POP. The commit point is the read. *)
    have -> : x29 = [] by sauto. iDestruct (OmoAuth_OmoEview γg _ _ _ _ _ M with "[$] []") as %MIncl; first iSteps.
    iLeft. iExists (EMPTY)%Z. oSteps. iExists _. iSplitR. { iPureIntro. eapply stack_step_EmpPop; [done|]. shelve. }
    replace (M ∪ M) with M; last set_solver-. iStep.
    iAssert (OmoUB γg M x32)%I with "[-]" as "#?". {
      rewrite {2}/OmoUB big_sepS_forall. iIntros "%e %eM".
      specialize (MIncl _ eM) as [eV Elookup]. iRename select (seen_event_info _ _ _ _ _) into "Seen".
      iDestruct (big_sepL_lookup with "Seen") as (?) "(e↦el & e⊒el & MONO✓e)"; [exact Elookup|].
      iDestruct (OmoHb_HbIncluded with "e⊒el [$]") as %e'Mh1; [done|].
      iApply (CWMono_acc γg x1 with "[$] MONO✓e [] e↦el []"); [done..|].
      by rewrite /OmoUB big_sepS_elem_of. }
    oSteps. iExists x32. oSteps. }
  (* Abort AU *)
  (* We have read a node from the head. Try to pop the node.. *)
  iRight. oSteps. iExists None. oSteps. { iLeft. iExists FAIL_RACE. oSteps. }
  iLeft. iRename select (@{_} StackNodes _ _)%I into "Nodes". iRename select (big_opL _ _ x44) into "LM".
  (* stk should have not been empty since the cas succeeded. *)
  destruct x44 (* stk2 *) as [| [[[node_1 node_2] node_3] node_4] stk2']; [by iDestruct "Nodes" as %?|].
  iDecompose "Nodes". iDecompose "LM". iExists (node_2). rewrite decide_False; [|lia]. iStep. iExists _. rewrite decide_False; [|lia].
  iStep. iExists _. iSplitR.
  { iPureIntro. apply stack_step_Pop; simpl in *; try pure_solver.trySolvePure.
    instantiate ( 1 := {[node_1]} ⊔ node_4). set_solver-. }
  oSteps; [iPureIntro; iSteps|]. iRename select (@{_} StackNodes x33 _)%I into "Nodes".
  destruct x33; destruct stk2'; iDecompose "Nodes"; oSteps. Unshelve. all: pure_solver.trySolvePure.
Qed.

Section use_try_push_internal.

#[local] Opaque StackInv StackLocal.

Lemma atom_try_push :
  try_push_spec' try_push StackLocal StackInv.
Proof using All.
  iStepsSafest; [iRight; iSteps|]. iLeft. destruct x11; iStep; [iExists true|iExists false]; iSteps.
  1: apply inhabitant. rewrite /own_loc_vec. iSteps.
Qed.

Lemma atom_push_internal :
  ∀ N (DISJ: N ## histN) s tid γg E0 M V (v : Z) (Posv: (0 < v)%Z) (n : loc),
  (* E1 is a snapshot of the history, locally observed by M *)
  ⊒V -∗ StackLocal N γg s E0 M -∗
  (n >> next) ↦ - -∗ (n >> data) ↦ #v -∗
  (* PUBLIC PRE *)
  <<< ∀ E, ▷ StackInv γg s E >>>
    push_internal [ #s ; #n] @ tid; ↑N
  <<< ∃ V' E' ps M',
      (* PUBLIC POST *)
      ▷ StackInv γg s E' ∗
      ⊒V' ∗ @{V'} StackLocal N γg s E' M' ∗
      ⌜ V ⊑ V' ∧
        is_push ps v ∧
        E' = E ++ [mkOmoEvent ps V' M'] ∧ M ⊆ M' ⌝,
      (* RETURN VALUE AT COMMITTING POINT *)
      RET #☠, emp >>>
  .
Proof using All.
  unfold is_push. iStep 17. iLöb as "IH" forall (x10). iStepsSafest; [iRight; iSteps|].
  iRename select (if x12 then _ else _) into "Case". destruct x12; iDecompose "Case"; [|iRight; iSteps].
  iLeft. iRename select (⊒_)%I into "⊒V". iAssert (⊒x12)%I with "[⊒V]" as "{⊒V} ?"; iSteps.
Qed.

Lemma atom_push :
  push_spec' push StackLocal StackInv.
Proof using All.
  intros N DISJ s tid γg E0 M V v Posv. iIntros "⊒V Es" (Φ) "AU". wp_lam.
  (* allocate node *)
  wp_apply wp_new; [done..|]. iIntros (n) "([H†|%] & n↦ & Hmn)"; [|done].
  (* initialize n's data as v *)
  rewrite own_loc_na_vec_cons own_loc_na_vec_singleton. iDestruct "n↦" as "[n↦ Hd]". wp_let. wp_op. wp_write.
  wp_apply (atom_push_internal with "⊒V Es [n↦] Hd AU"); [eauto..|]. rewrite shift_0. by iExists _.
Qed.

End use_try_push_internal.


Section use_try_pop_internal.

#[local] Opaque StackInv StackLocal.

Lemma atom_try_pop :
  try_pop_spec' try_pop StackLocal StackInv.
Proof using All.
  iStepsSafest; [iRight; iSteps|]. iLeft. destruct (decide (x8 = -1)%Z).
  - (* fail race case *) iSteps. iExists FAIL_RACE. iSteps. apply inhabitant.
  - iRename select (_ ∗ emp)%I into "H". iDecompose "H".
    iRename select (⊒_)%I into "⊒V". iAssert (⊒x10)%I with "[]" as "{⊒V} ?"; iSteps.
    iExists x8, _. rewrite decide_False; [|done]. iSteps.
Qed.

Lemma atom_pop :
  pop_spec' pop StackLocal StackInv.
Proof using All.
  iStep 12. iLöb as "IH". iStepsSafest; [iRight; iSteps|]. destruct (decide (x8 = -1)%Z); [iRight; iSteps|iLeft].
  iRename select (_ ∗ emp)%I into "H". iDecompose "H".
  iRename select (⊒_)%I into "⊒V". iAssert (⊒x10)%I with "[]" as "{⊒V} ?"; [iSteps|].
  iSteps. rewrite bool_decide_false; [|done]. iSteps.
Qed.

End use_try_pop_internal.
End proof.

Definition treiber_stack_impl `{!noprolG Σ, !atomicG Σ, !omoGeneralG Σ, !omoSpecificG Σ sevent_hist stack_state, !appendOnlyLocG Σ}
  : stack_spec Σ := {|
    spec_history.StackInv_Objective := _ ;
    spec_history.StackInv_Linearizable := StackInv_Linearizable_instance ;
    spec_history.StackInv_history_wf := StackInv_history_wf_instance;
    spec_history.StackInv_StackLocal := StackInv_StackLocal_instance;
    spec_history.StackLocal_lookup := StackLocal_lookup_instance;
    spec_history.StackLocal_Persistent := StackLocal_persistent ;
    spec_history.new_stack_spec := new_stack_spec;
    spec_history.try_push_spec := atom_try_push ;
    spec_history.push_spec := atom_push ;
    spec_history.try_pop_spec := atom_try_pop ;
    spec_history.pop_spec := atom_pop ;
  |}.
