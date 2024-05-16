From gpfsl.examples Require Import sflib.

From iris.algebra Require Import auth gset gmap agree.
From iris.algebra Require Import lib.mono_list.
From iris.proofmode Require Import tactics.

From gpfsl.base_logic Require Import meta_data.
From gpfsl.examples.algebra Require Import mono_list_list.
From gpfsl.logic Require Import logatom atomics invariants.

From gpfsl.logic Require Import repeat_loop new_delete.
From gpfsl.examples Require Import map_seq loc_helper.
From gpfsl.examples.stack Require Import spec_treiber_composition_diaframe code_treiber.
From gpfsl.examples.omo Require Import omo omo_preds omo_preds_diaframe append_only_loc.

From gpfsl.diaframe Require Import vprop_weakestpre spec_notation
 vprop_weakestpre_logatom atom_spec_notation proof_automation omo_specs omo_hints.

From diaframe Require Import proofmode_base lib.except_zero own_hints steps.verify_tac util_instances.
From diaframe.symb_exec Require Import weakestpre_logatom.

From Hammer Require Import Tactics.
From iris.proofmode Require Import intro_patterns.


Require Import iris.prelude.options.

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
Definition StackInv γg γs s E omo stlist : vProp :=
  ∃ (γh : gname) Vb,
  (* head *)
  @{Vb} append_only_loc s γh ∅ cas_only ∗
  ∃ (γsh γm : gname) stk Eh omoh mo (ont : option loc) Vt Mono,
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

Global Instance StackInv_objective γg γs s E omo stlist : Objective (StackInv γg γs s E omo stlist) := _.
Global Instance StackInv_timeless γg γs s E omo stlist : Timeless (StackInv γg γs s E omo stlist) := _.

Definition StackLocal (_ : namespace) γg s M : vProp :=
  ∃ (γh γs γsh γm : gname) Mh,
  meta s nroot (γh,γs,γsh,γm) ∗

  (* Local snapshot of the history and local observation of events *)
  OmoEview γg M ∗
  OmoEview γh Mh
  .

Global Instance StackLocal_persistent N γg s M :
  Persistent (StackLocal N γg s M) := _.

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
  ∀ γg γs s E omo stlist, StackInv γg γs s E omo stlist ⊢ ⌜ Linearizability_omo E omo stlist ⌝.
Proof. oSteps. by iDestruct (@OmoAuth_Linearizable sevent_hist with "[$]") as %?. Qed.

Lemma StackInv_OmoAuth_acc_instance :
  ∀ γg γs s E omo stlist,
    StackInv γg γs s E omo stlist ⊢ OmoAuth γg γs 1 E omo stlist _ ∗ (OmoAuth γg γs 1 E omo stlist _ -∗ StackInv γg γs s E omo stlist).
Proof. oSteps. Qed.

Lemma StackLocal_OmoEview_instance :
  ∀ N γg s M, StackLocal N γg s M ⊢ OmoEview γg M.
Proof. oSteps. Qed.

Lemma StackLocal_Eview_update_instance :
  ∀ N γg s M1 M2, StackLocal N γg s M1 -∗ OmoEview γg M2 -∗ StackLocal N γg s (M1 ∪ M2).
Proof. oSteps. Qed.

Lemma new_stack_dspec :
  new_stack_dspec' new_tstack StackLocal StackInv.
Proof.
  rewrite /spec_treiber_composition_diaframe.new_stack_dspec'. iSteps as "⊒x1". rewrite shift_0. iStep 9 as "Hs".
  (* The initial updates can't be automated since it creates variables needed for proving meta, but meta has to be at the start of the invariant for other proofs. *)
  iMod (append_only_loc_cas_only_from_na_rel with "⊒x1 Hs") as (γh γsh ? ?) "H"; [done|]. iDecompose "H".
  set M := {[0%nat]}.
  set eVinit := mkOmoEvent Init eV.(sync) M.
  iMod (@OmoAuth_alloc _ _ _ _ _ eVinit init _ _ stack_interpretable with "[$]") as (γg γs) "H"; [by apply stack_step_Init|done| ..]. iDecompose "H".
  iMod (@OmoHb_new_1 _ loc_event _ _ _ _ _ _ γg γh with "[$] [$] [$]") as "[M● #e0⊒eh0]". { subst eVinit. simpl. solve_lat. }
  iDestruct (OmoHbToken_finish with "M●") as "M●".
  iMod (CWMono_new γg γh) as (γm) "MONO".
  iRename select (meta_token _ _) into "Hms". iMod (meta_set _ _ (γh,γs,γsh,γm) nroot with "Hms") as "#Hms"; [done|].
  iMod (@CWMono_insert_last_last _ loc_event _ _ _ _ _ _ (wr_event 0) with "MONO [$] [$] [$]") as "H"; [done..|]. iDecompose "H".
  iRename select (append_only_loc _ _ _ _)%I into "omo↦". iDestruct (view_at_intro with "omo↦") as (?) "[_ omo↦]".
  rewrite /StackInv !try_update_OmoAuth_to_eq. iStepSafest. iExists 0. iSplitR. { iPureIntro. instantiate (1 := omo_append_w [] 0 []). done. }
  oSteps. do 2 (iExists None,(eV.(sync)); rewrite H1; oSteps).
Qed.

#[local] Hint Extern 10 (BehindModal (fupd ?El ?Er) (?N ⊆ ?Er)) =>
  unify El Er; unfold BehindModal; pure_solver.trySolvePure : solve_pure_add.

#[local] Remove Hints ssrbool.not_false_is_true : core.

Set Nested Proofs Allowed.

#[global] Instance atom_try_push_internal N γg s M V (v : Z) (n : loc) :
  SPEC ⟨ ⊤ , ↑N , ↑histN⟩ E γs omo stlist, <<
    ⊒V ∗
    StackLocal N γg s M ∗
    (n >> next) ↦ - ∗
    (n >> data) ↦ #v ∗
    ⌜ (0 < v)%Z ⌝ ∗
    ⌜ N ## histN ⌝
  ¦
    ▷ StackInv γg γs s E omo stlist  > >
      try_push_internal [ #s ; #n]
  << (b : bool), RET #b;
      emp
      ¦
      (∃ V', ⊒V' ∗
      (* PUBLIC POST *)
      if b then (
        ∃ M' omo' stlist' st,
          let ps := Push v in
          let E' := E ++ [mkOmoEvent ps V' M'] in
          (* Vpush ⊑ V' ∧ *) (* << only works if push is also acquiring*)
          (* ps is a new push event with which E' strictly extends E *)
             ▷ StackInv γg γs s E' omo' stlist' ∗ @{V'} StackLocal N γg s M' ∗ OmoUB γg M (length E) ∗ OmoTokenW γg (length E) ∗
             ⌜ V ⊑ V' ∧ M ⊆ M' ∧ omo' = omo_append_w omo (length E) [] ∧ stlist' = stlist ++ [st] ⌝
      ) else (
        ∃ somewhere,
        (* FAIL_RACE case *)
        (n >> next) ↦ somewhere ∗ (n >> data) ↦ #v ∗
        ▷ StackInv γg γs s E omo stlist ∗
        @{V'} StackLocal N γg s M
      ) ∗ emp )
    > >.
Proof using All.
  oSteps. iExists None. oSteps. iRight. oSteps. iExists None. oSteps; iLeft; unseal_diaframe; oSteps; [iExists false|iExists true]; oSteps.
  iExists _. iSplitR. { iPureIntro. apply stack_step_Push; [done..|shelve]. } oSteps; [iPureIntro;iSteps|]. iSplitR; [|oSteps].
  iApply big_sepS_subseteq; [|by iApply OmoUB_singleton]; set_solver-. Unshelve. all: try pure_solver.trySolvePure.
Qed.

#[global] Instance dspec_atom_try_pop N V γg s M :
  SPEC ⟨ ⊤ , ↑N , ↑histN⟩ E γs omo stlist, <<
    ⊒V ∗
    StackLocal N γg s M
  ¦
    ▷ StackInv γg γs s E omo stlist  > >
      try_pop [ #s]
  << (v : Z), RET #v;
      emp
      ¦
      (∃ V', ⊒V' ∗
      (* PUBLIC POST *)
      if (decide (v = FAIL_RACE)) then (
        (* FAIL_RACE case *)
        ▷ StackInv γg γs s E omo stlist ∗
        @{V'} StackLocal N γg s M
      ) else (
        ∃ pp, ⌜if (decide (v = EMPTY)) then pp = EmpPop (* EMPTY case *)
          else (0 < v)%Z ∧ pp = Pop v ⌝ ∗ (* successful case *)
        ∃ M'add e omo' stlist',
          let M' := {[e]} ∪ (M ∪ M'add) in
          let E' := E ++ [mkOmoEvent pp V' M'] in
             ▷ StackInv γg γs s E' omo' stlist' ∗ @{V'} StackLocal N γg s M' ∗ ⌜ V ⊑ V' ⌝ ∗
              if (decide (v = EMPTY)) then (
                ⌜ ∃ gen, omo' = omo_insert_r omo gen (length E) ∧ (gen < length omo)%nat ∧ stlist' = stlist ⌝ ∗
                OmoTokenR γg (length E)
              ) else (
                ⌜ ∃ st, omo' = omo_append_w omo (length E) [] ∧ stlist' = stlist ++ [st] ⌝ ∗
                OmoTokenW γg (length E)
              )
      ) ∗ OmoUB γg M (length E) ∗ emp )
    > >.
Proof using All.
  (* Read head *)
  oSteps. iDestruct (OmoEview_update γg x1 with "[$] [] []") as (Mh1) "H"; [iSteps..|]. iDecompose "H".
  iExists (Some Mh1). oSteps. iRename select (match x28 with |Some _ => _ | None => _ end)%I into "Case".
  destruct x28 as [n1|]; last first.
  { (* EMPTY POP. The commit point is the read. *)
    have -> : x29 = [] by sauto. iDestruct (OmoAuth_OmoEview γg _ _ _ _ _ M with "[$] []") as %MIncl; first iSteps.
    iLeft. unseal_diaframe. oSteps. iExists (EMPTY)%Z. oSteps. iExists _. iSplitR. { iPureIntro. eapply stack_step_EmpPop; [done|]. shelve. }
    replace (M ∪ M) with M; last set_solver-. iStep.
    iAssert (OmoUB γg M x32)%I with "[-]" as "#?". {
      rewrite {2}/OmoUB big_sepS_forall. iIntros "%e %eM".
      specialize (MIncl _ eM) as [eV Elookup]. iRename select (seen_event_info _ _ _ _ _) into "Seen".
      iDestruct (big_sepL_lookup with "Seen") as (?) "(e↦el & e⊒el & MONO✓e)"; [exact Elookup|].
      iDestruct (OmoHb_HbIncluded with "e⊒el [$]") as %e'Mh1; [done|].
      iApply (CWMono_acc γg x1 with "[$] MONO✓e [] e↦el []"); [done..|].
      by rewrite /OmoUB big_sepS_elem_of. }
    oSteps. iExists x32. oSteps; [iPureIntro; eexists; (split_and!; try done); apply lookup_omo_lt_Some in H12; by rewrite omo_insert_r_length in H12|].
    iSplitR; [|oSteps]. iApply big_sepS_subseteq; [|by iApply OmoUB_singleton]. set_solver-. }
  (* Abort AU *)
  (* We have read a node from the head. Try to pop the node.. *)
  iRight. oSteps. iExists None. oSteps. { iLeft. unseal_diaframe. oSteps. iExists FAIL_RACE. oSteps. }
  iLeft. iRename select (@{_} StackNodes _ _)%I into "Nodes". iRename select (big_opL _ _ x44) into "LM".
  (* stk should have not been empty since the cas succeeded. *)
  destruct x44 (* stk2 *) as [| [[[node_1 node_2] node_3] node_4] stk2']; [by iDestruct "Nodes" as %?|].
  iDecompose "Nodes". iDecompose "LM". unseal_diaframe. oSteps. iExists (node_2). rewrite decide_False; [|lia]. iStep. iExists _. rewrite decide_False; [|lia].
  iStep. iExists _. iSplitR. { iPureIntro. apply stack_step_Pop; simpl in *; try pure_solver.trySolvePure. instantiate ( 1 := {[node_1]} ⊔ node_4). set_solver-. }
  oSteps; [iPureIntro; iSteps|]. iRename select (@{_} StackNodes x33 _)%I into "Nodes".
  iAssert (OmoUB γg M (length x36))%I with "[]" as "#?"; [by iApply big_sepS_subseteq; [|by iApply OmoUB_singleton]; set_solver-|].
  destruct x33; destruct stk2'; iDecompose "Nodes"; oSteps; (rewrite decide_False; [|lia]); oSteps. Unshelve. all: pure_solver.trySolvePure.
Qed.

Section use_try_push_internal.

#[local] Opaque StackInv StackLocal.

Lemma try_push_dspec :
  try_push_dspec' try_push StackLocal StackInv.
Proof using All.
  rewrite /try_push_dspec'. intros. iStep 30 as "?????H"|"????H"; [iStep as "M●"; iMod ("H" $! true true with "[M●]") as "H"; oSteps|].
  iStep 2 as "⊒V' Hx2". iAssert (⊒x3)%I with "[]" as "⊒x3"; [oSteps|]. iClear "⊒V'". iSteps.
  destruct x2; iDecompose "Hx2"; [iExists true|iExists false]; iSteps. rewrite /own_loc_vec. iSteps.
Qed.

Lemma push_dspec :
  push_dspec' push StackLocal StackInv.
Proof using All.
  rewrite /push_dspec'. intros. iStep 23 as "???? n↦". iAssert ((x1 >> 0) ↦ -)%I with "[n↦]" as "n↦"; [by iExists _|]. iLöb as "IH".
  iStep 10 as "?"|"????H"; [oSteps;iRight;oSteps|]. iStep 2 as "⊒V' Hx2". iAssert (⊒x4)%I with "[]" as "⊒x4"; [oSteps|]. iClear "⊒V'".
  destruct x2; iDecompose "Hx2"; oSteps; [iLeft; unseal_diaframe|iRight]; oSteps.
Qed.

End use_try_push_internal.

Section use_try_pop_internal.

#[local] Opaque StackInv StackLocal.

Lemma try_pop_dspec :
  try_pop_dspec' try_pop StackLocal StackInv.
Proof using All.
  rewrite /try_pop_dspec'. intros. iStep 10 as "??H"|"??H"; [iStep as "M●"; iMod ("H" $! true 1%Z with "[M●]") as "H"; oSteps|].
  iStep 2 as "⊒V' Hx1". iAssert (⊒x2)%I with "[]" as "⊒x2"; [oSteps|]. iClear "⊒V'". iSteps.
  destruct (decide (x1 = (-1)%Z)) as [->|NEQ1]; iDecompose "Hx1" as "???Hx1"; [iExists (-1)%Z; oSteps|iExists x1].
  destruct (decide (x1 = 0%Z)) as [->|NEQ2]; iDecompose "Hx1"; [oSteps|]. rewrite decide_False; [|done]. oSteps. destruct H0 as [? ?]. subst x3. oSteps.
Qed.

Lemma pop_dspec :
  pop_dspec' pop StackLocal StackInv.
Proof using All.
  rewrite /pop_dspec'. intros. iStep 3. iLöb as "IH". iStep 10; [oSteps; iRight; oSteps|]. iStep 2 as "⊒V' Hx1".
  iAssert (⊒x2)%I with "[]" as "⊒x2"; [oSteps|]. iClear "⊒V'". oSteps. unseal_diaframe. oSteps. destruct (decide (x1 = (-1)%Z)).
  { iRight. oSteps. rewrite bool_decide_true; [|done]. oSteps. } iLeft. unseal_diaframe. iSteps as "???Hx1".
  destruct (decide (x1 = 0%Z)) as [->|NEQ]; iDecompose "Hx1"; [iExists 0%Z; oSteps|].
  iExists x1,_,_,_. destruct H0 as [? ?]. subst x3. rewrite decide_False; [|done]. oSteps. rewrite bool_decide_false; [|done]. oSteps.
Qed.

End use_try_pop_internal.
End proof.

Definition treiber_stack_impl `{!noprolG Σ, !atomicG Σ, !omoGeneralG Σ, !omoSpecificG Σ sevent_hist stack_state, !appendOnlyLocG Σ}
  : stack_dspec Σ := {|
    spec_treiber_composition_diaframe.StackInv_Linearizable := StackInv_Linearizable_instance;
    spec_treiber_composition_diaframe.StackInv_OmoAuth_acc := StackInv_OmoAuth_acc_instance;
    spec_treiber_composition_diaframe.StackLocal_OmoEview := StackLocal_OmoEview_instance;
    spec_treiber_composition_diaframe.StackLocal_Eview_update := StackLocal_Eview_update_instance;
    spec_treiber_composition_diaframe.new_stack_dspec := new_stack_dspec;
    spec_treiber_composition_diaframe.try_push_dspec := try_push_dspec;
    spec_treiber_composition_diaframe.push_dspec := push_dspec;
    spec_treiber_composition_diaframe.try_pop_dspec := try_pop_dspec;
    spec_treiber_composition_diaframe.pop_dspec := pop_dspec;
  |}.
