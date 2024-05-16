From gpfsl.logic Require Import logatom proofmode.
From gpfsl.examples.stack Require Export event spec_history_old spec_abs.

Require Import iris.prelude.options.

Local Open Scope nat_scope.

Section abs_graph.
Context `{!noprolG Σ, !inG Σ (historyR sevent)}.
(* We only need an extended spec with Weak Consistency *)
Context (hs : spec_history_old.stack_spec Σ).
Local Existing Instances
  spec_history_old.StackInv_Timeless spec_history_old.StackInv_Objective
  spec_history_old.StackLocal_Persistent.

Definition isStack N γs s : vProp Σ := hs.(StackLocal) N γs s [] ∅.

Definition Stack γs s S : vProp Σ := ∃ E stk,
  hs.(StackInv) γs s E ∗
  ⌜ stack_interp E (filter (not_empty_pop E) (seq 0 (length E))) [] stk ∧
    Forall2 (λ '(_, v, V, _) '(v', V'), v = v' ∧ V = V' ) stk S ⌝
  .

#[global] Instance Stack_objective γs s S : Objective (Stack γs s S) := _.
#[global] Instance Stack_timeless γs s S : Timeless (Stack γs s S) := _.
#[global] Instance isStack_persistent N γs s : Persistent (isStack N γs s) := _.

Lemma new_stack_spec :
  new_stack_spec' hs.(spec_history_old.new_stack) isStack Stack.
Proof.
  iIntros (N tid Φ) "_ Post".
  iApply (hs.(spec_history_old.new_stack_spec) with "[%//]").
  iIntros "!> * [#SL SI]". iApply "Post". iFrame "SL". iExists [],[].
  iDestruct (StackInv_StackLinearizability with "SI") as %[].
  iFrame "SI".
  iPureIntro. subst xo. simpl in *. rewrite ->filter_nil in * |- *.
  split; constructor.
Qed.

Lemma push_spec :
  push_spec' hs.(spec_history_old.push) isStack Stack.
Proof.
  intros N DISJ s tid γs V v Posx. iIntros "#⊒V #SL" (Φ) "AU".
  awp_apply (hs.(spec_history_old.push_spec) with "⊒V SL"); [done..|].
  iApply (aacc_aupd_commit with "AU"); [done|].
  iIntros (S) ">S". iDestruct "S" as (??) "(SI & %INTERP & %EQUIV)".
  iAaccIntro with "SI".
  { iIntros ">SI !>". iSplitL "SI"; [|by auto]. iNext. iExists _,_. by iFrame. }
  iIntros (V' E' pushId push Vpush M') "(>SI & #⊒V' & #SL' & %F) !>".
  iDestruct (spec_history_old.StackInv_StackLinearizability with "SI") as %SC.
  set (pushE := mkGraphEvent push Vpush M') in *.
  set (S' := (v, V') :: S).
  rewrite /is_push in F. destruct F as (? & ? & -> & -> & ? & ->).
  have HpushE : E' !! (length E) = Some pushE.
  { subst E'. apply lookup_app_1_eq. }
  have SubEE' : E ⊑ E' by eexists.
  iAssert (Stack γs s S') with "[SI]" as "S".
  { destruct SC as [xo' lin' stk']. subst E' xo'.
    iExists _, stk'. iFrame "SI". iPureIntro.
    rewrite app_length /= seq_app /= in INTERP_XO *.
    rewrite filter_app filter_cons_True in INTERP_XO *; last first.
    { intros ??. rewrite HpushE in EV. by injection EV as <-. }
    rewrite filter_nil in INTERP_XO *.
    split; [done|].
    apply stack_interp_snoc_inv in INTERP_XO as (pushE' & stk0 & INTERP0 & HpushE' & RUN).
    rewrite HpushE in HpushE'. injection HpushE' as <-.
    rewrite -(write_xo_stable E _) in INTERP0; [|done..].
    apply (stack_interp_mono_prefix _ (E ++ [pushE])) in INTERP; [|done].
    specialize (stack_interp_functional _ _ _ _ _ INTERP INTERP0) as <-.
    inversion RUN; simplify_eq/=. by constructor. }
  iExists V',S'. iFrame "∗#". iSplit; [|by auto]. iPureIntro.
  split; [|done]. subst V V'. apply dv_in_com.
Qed.

Lemma pop_spec :
  pop_spec' hs.(spec_history_old.pop) isStack Stack.
Proof.
  intros N DISJ s tid γs V. iIntros "#⊒V #SL" (Φ) "AU".
  awp_apply (hs.(spec_history_old.pop_spec) with "⊒V SL"); [done..|].
  iApply (aacc_aupd_commit with "AU"); [done|].
  iIntros (S) ">S". iDestruct "S" as (??) "(SI & %INTERP & %EQUIV)".
  iAaccIntro with "SI".
  { iIntros ">SI !>". iSplitL "SI"; [|by auto]. iNext. iExists _,_. by iFrame. }
  iIntros (v V' E' pushId popId push pop Vpop M') "(>SI & #⊒V' & #SL' & %F) !>".
  destruct F as [(? & ?) CASE].
  iDestruct (spec_history_old.StackInv_StackLinearizability with "SI") as %SC.
  set (popE := mkGraphEvent pop Vpop M') in *.
  have [HpopE SubEE'] : E' !! (length E) = Some popE ∧ E ⊑ E'.
  { destruct_or! CASE; destruct_and! CASE; subst E'; (split; [apply lookup_app_1_eq|by eexists]). }
  rewrite /is_push /is_pop in CASE.
  destruct CASE as [CASE|CASE].
  - destruct CASE as (? & ? & ? & ? & ?).
    iExists v, V, S. iFrame "⊒V".
    iSplitL; [|by auto]. iSplitL; [|by iLeft].
    iNext. iExists _,_. iFrame. iPureIntro. split; [|done].
    subst E'. rewrite app_length /= seq_app /=.
    rewrite filter_app filter_cons_False; last first.
    { intros NE. by specialize (NE _ HpopE). }
    rewrite filter_nil app_nil_r.
    rewrite -(write_xo_stable E _); [|done..].
    by apply (stack_interp_mono_prefix _ (E ++ [popE])) in INTERP.
  - destruct CASE as (? & -> & -> & ? & -> & ? & pushE & HpushE & ? & ?).
    (* reconstruct the state before the pop *)
    destruct SC as [xo' lin' stk']. subst E' xo'.
    rewrite app_length /= seq_app /= in INTERP_XO *.
    rewrite filter_app filter_cons_True in INTERP_XO *; last first.
    { intros ??. rewrite HpopE in EV. by injection EV as <-. }
    rewrite filter_nil in INTERP_XO *.
    have INTERP_XO' := INTERP_XO.
    apply stack_interp_snoc_inv in INTERP_XO' as (popE' & stk'' & INTERP' & HpopE' & RUN).
    rewrite HpopE in HpopE'. injection HpopE' as <-.
    inversion RUN as [|u o oV vp Vp lV stkp|]; [simplify_eq| |simplify_eq].
    clear RUN. subst o oV stkp stk''. injection POP as <-.
    apply (stack_interp_mono_prefix _ (E ++ [popE])) in INTERP; [|done].
    rewrite -(write_xo_stable E _) in INTERP'; [|done..].
    specialize (stack_interp_functional _ _ _ _ _ INTERP INTERP') as ->.
    apply Forall2_cons_inv_l in EQUIV as ([??] & S' & [<- <-] & EQUIV & ->).
    iExists v, Vp, S'. subst V'. simpl in *.
    iDestruct (monPred_in_mono _ _ SYNC with "⊒V'") as "$".
    iSplitL; [|by auto]. iSplitL; [|by iRight].
    iNext. iExists _,_. iFrame. iPureIntro. split; [|done].
    rewrite app_length /= seq_app /= in INTERP_XO *.
    rewrite filter_app filter_cons_True in INTERP_XO *; last first.
    { intros ??. rewrite HpopE in EV. by injection EV as <-. }
    done.
Qed.

Lemma try_push_spec :
  try_push_spec' hs.(spec_history_old.try_push) isStack Stack.
Proof.
  intros N DISJ s tid γs V v Posx. iIntros "#⊒V #SL" (Φ) "AU".
  awp_apply (hs.(spec_history_old.try_push_spec) with "⊒V SL"); [done..|].
  iApply (aacc_aupd_commit with "AU"); [done|].
  iIntros (S) ">S". iDestruct "S" as (??) "(SI & %INTERP & %EQUIV)".
  iAaccIntro with "SI".
  { iIntros ">SI !>". iSplitL "SI"; [|by auto]. iNext. iExists _,_. by iFrame. }
  iIntros (b V' E' pushId push Vpush M') "(>SI & #⊒V' & #SL' & %F) !>".
  iDestruct (spec_history_old.StackInv_StackLinearizability with "SI") as %SC.
  set (pushE := mkGraphEvent push Vpush M') in *.
  destruct F as [(->&->&->)|CASE].
  { iExists false,V,S. iFrame "⊒V". iSplitL; [|by auto]. iSplit; [|done].
    iNext. iExists _,_. by iFrame. }
  rewrite /is_push in CASE.
  destruct CASE as (-> & ? & ? & -> & -> & ? & ?).
  have HpushE : E' !! (length E) = Some pushE.
  { subst E'. apply lookup_app_1_eq. }
  have SubEE' : E ⊑ E' by eexists.
  set (S' := (v, V') :: S).
  iAssert (Stack γs s S') with "[SI]" as "S".
  { destruct SC as [xo' lin' stk']. subst E' xo'.
    iExists _, stk'. iFrame "SI". iPureIntro.
    rewrite app_length /= seq_app /= in INTERP_XO *.
    rewrite filter_app filter_cons_True in INTERP_XO *; last first.
    { intros ??. rewrite HpushE in EV. by injection EV as <-. }
    rewrite filter_nil in INTERP_XO *.
    split; [done|].
    apply stack_interp_snoc_inv in INTERP_XO as (pushE' & stk0 & INTERP0 & HpushE' & RUN).
    rewrite HpushE in HpushE'. injection HpushE' as <-.
    rewrite -(write_xo_stable E _) in INTERP0; [|done..].
    apply (stack_interp_mono_prefix _ (E ++ [pushE])) in INTERP; [|done].
    specialize (stack_interp_functional _ _ _ _ _ INTERP INTERP0) as <-.
    inversion RUN; simplify_eq/=. by constructor. }
  iExists true,V',S'. iFrame "∗#". iSplit; [|by auto]. iPureIntro.
  split; [|done]. subst V V'. apply dv_in_com.
Qed.

Lemma try_pop_spec :
  try_pop_spec' hs.(spec_history_old.try_pop) isStack Stack.
Proof.
  intros N DISJ s tid γs V. iIntros "#⊒V #SL" (Φ) "AU".
  awp_apply (hs.(spec_history_old.try_pop_spec) with "⊒V SL"); [done..|].
  iApply (aacc_aupd_commit with "AU"); [done|].
  iIntros (S) ">S". iDestruct "S" as (??) "(SI & %INTERP & %EQUIV)".
  iAaccIntro with "SI".
  { iIntros ">SI !>". iSplitL "SI"; [|by auto]. iNext. iExists _,_. by iFrame. }
  iIntros (v V' E' pushId popId push pop Vpop M') "(>SI & #⊒V' & #SL' & %F) !>".
  destruct F as [(? & ?) CASE].
  iDestruct (spec_history_old.StackInv_StackLinearizability with "SI") as %SC.
  set (popE := mkGraphEvent pop Vpop M') in *.
  destruct CASE as [(->&->&->)|CASE].
  { iExists (-1)%Z,V,S. iFrame "⊒V". iSplitL; [|by auto].
    iSplit; [|by iLeft]. iExists _,_. iNext. by iFrame. }
  have [HpopE SubEE'] : E' !! (length E) = Some popE ∧ E ⊑ E'.
  { destruct_or! CASE; destruct_and! CASE; subst E'; (split; [apply lookup_app_1_eq|by eexists]). }
  rewrite /is_push /is_pop in CASE.
  destruct CASE as [CASE|CASE].
  - destruct CASE as (? & ? & ? & ? & ?).
    iExists v, V, S. iFrame "⊒V".
    iSplitL; [|by auto]. iSplitL; [|by iRight; iLeft].
    iNext. iExists _,_. iFrame. iPureIntro. split; [|done].
    subst E'. rewrite app_length /= seq_app /=.
    rewrite filter_app filter_cons_False; last first.
    { intros NE. by specialize (NE _ HpopE). }
    rewrite filter_nil app_nil_r.
    rewrite -(write_xo_stable E _); [|done..].
    by apply (stack_interp_mono_prefix _ (E ++ [popE])) in INTERP.
  - destruct CASE as (? & -> & -> & ? & -> & ? & pushE & HpushE & ? & ?).
    (* reconstruct the state before the pop *)
    destruct SC as [xo' lin' stk']. subst E' xo'.
    rewrite app_length /= seq_app /= in INTERP_XO *.
    rewrite filter_app filter_cons_True in INTERP_XO *; last first.
    { intros ??. rewrite HpopE in EV. by injection EV as <-. }
    rewrite filter_nil in INTERP_XO *.
    have INTERP_XO' := INTERP_XO.
    apply stack_interp_snoc_inv in INTERP_XO' as (popE' & stk'' & INTERP' & HpopE' & RUN).
    rewrite HpopE in HpopE'. injection HpopE' as <-.
    inversion RUN as [|u o oV vp Vp lV stkp|]; [simplify_eq| |simplify_eq].
    clear RUN. subst o oV stkp stk''. injection POP as <-.
    apply (stack_interp_mono_prefix _ (E ++ [popE])) in INTERP; [|done].
    rewrite -(write_xo_stable E _) in INTERP'; [|done..].
    specialize (stack_interp_functional _ _ _ _ _ INTERP INTERP') as ->.
    apply Forall2_cons_inv_l in EQUIV as ([??] & S' & [<- <-] & EQUIV & ->).
    iExists v, Vp, S'. subst V'. simpl in *.
    iDestruct (monPred_in_mono _ _ SYNC with "⊒V'") as "$".
    iSplitL; [|by auto]. iSplitL; [|by iRight; iRight].
    iNext. iExists _,_. iFrame. iPureIntro. split; [|done].
    rewrite app_length /= seq_app /= in INTERP_XO *.
    rewrite filter_app filter_cons_True in INTERP_XO *; last first.
    { intros ??. rewrite HpopE in EV. by injection EV as <-. }
    done.
Qed.
End abs_graph.

Definition history_abs_stack_spec
  Σ `{!noprolG Σ, !inG Σ (historyR sevent)}
  (hs : spec_history_old.stack_spec Σ) : stack_spec Σ := {|
    spec_abs.Stack              := Stack hs ;
    spec_abs.isStack            := isStack hs ;

    spec_abs.Stack_Objective    := Stack_objective hs ;
    spec_abs.Stack_Timeless     := Stack_timeless hs ;
    spec_abs.isStack_Persistent := isStack_persistent hs ;

    spec_abs.new_stack_spec     := new_stack_spec hs ;
    spec_abs.push_spec       := push_spec hs ;
    spec_abs.pop_spec       := pop_spec hs ;
    spec_abs.try_push_spec       := try_push_spec hs ;
    spec_abs.try_pop_spec       := try_pop_spec hs ;
  |}%I.

