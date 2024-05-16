From iris.algebra Require Import excl_auth gset.
From iris.bi.lib Require Import fractional.
From iris.proofmode Require Import tactics.

From gpfsl.lang Require Import notation.
From gpfsl.logic Require Import logatom invariants proofmode.

From gpfsl.examples.stack Require Import spec_history_old.
From gpfsl.examples.queue Require Import spec_per_elem.
From gpfsl.examples Require Import set_helper.

Require Import iris.prelude.options.

Local Notation EMPTY := 0%Z (only parsing).

Definition mpN := nroot .@ "mpN".

Local Notation history := (history sevent).

Implicit Types (E : history) (S : gset event_id).

Section Stack.
  Context `{!noprolG Σ,
            !inG Σ (historyR sevent),
            !inG Σ (excl_authR (gset_disjR event_id))}.

  Local Notation iProp := (iProp Σ).
  Local Notation vProp := (vProp Σ).

  (** Assuming per-elem Queue spec *)
  Hypothesis qu : queue_per_elem_spec Σ.

  (** Assuming history-based Stack spec *)
  Hypothesis stk : stack_spec Σ.

  Definition prog  : expr :=
    let: "s" := stk.(new_stack) [] in
    let: "q" := qu.(new_queue) [] in
    Fork
      (stk.(push) ["s"; #1 ];;
       qu.(enqueue) ["q"; #2]);;(* || *)
                                (* || *)  let: "b" := qu.(dequeue) [ "q" ] in
                                (* || *)  if: "b" = #2
                                (* || *)  then stk.(pop) ["s"] else #(-1).

  Lemma Ghost_alloc S :
    ⊢ |==> ∃ γs, own γs (●E (GSet S)) ∗ own γs (◯E (GSet S)).
  Proof.
    setoid_rewrite <- own_op.
    rewrite -own_alloc; first eauto. by apply excl_auth_valid.
  Qed.

  (* Stack Invariant *)
  Definition StackInv1 γh γg s: vProp :=
    ∃ E, stk.(StackInv) γh s E ∗ ⎡ own γg (●E (GSet (to_set E)))⎤.

  Local Existing Instances
    StackInv_Objective StackInv_Timeless StackLocal_Persistent
    queue_persistent.

  Instance StackInv_obj γh γg s : Objective (StackInv1 γh γg s) := _.

  Definition QueueInv s γh γg (v : Z) : vProp :=
    ( if decide (v = 2)
      then ∃ E i e k, ⌜ E !! i = Some e /\ e.(ge_event) = Push 1 /\ i ∈ k⌝ ∗
                stk.(StackLocal) (mpN .@ "stk") γh s E k ∗
                ⎡ own γg (◯E (GSet {[i]})) ⎤
      else True)%I.

  Lemma mp_stack_spec tid :
    {{{ True }}}
      prog @ tid; ⊤
    {{{ n, RET #n; ⌜n = 1 ∨ n = -1⌝ }}}.
  Proof using All.
    iIntros (Φ) "_ Post".
    rewrite /prog.
    wp_apply (new_stack_spec _ (mpN .@ "stk") with "[//]").
    iIntros (γh s) "[#S SI]".
    iMod (Ghost_alloc ∅) as (γg) "[SA nodes]".
    wp_let.
    wp_apply (new_queue_spec _ (QueueInv s γh γg) with "[//]").
    iIntros (q) "#Q".
    wp_let.

    (* allocate invariants *)
    iMod (inv_alloc (mpN .@ "inv") _ (StackInv1 γh γg s) with "[SI SA]") as "#I".
    { iModIntro. rewrite / StackInv1. iExists []. iFrame. }

    (*forking *)
    wp_apply (wp_fork with "[nodes]"); first auto.
    - (* first thread *)
      iIntros "!>" (t').
      iDestruct (monPred_in_intro True%I with "[//]") as (V) "[#InV _]".
      awp_apply (push_spec with "InV S"); [solve_ndisj|lia|].
      iInv "I" as (E) "[SI >nodesA]".
      iAaccIntro with "SI".
      { iIntros "QI". iModIntro. iFrame "nodes". iNext. iExists E. iFrame. }
      iIntros (V' E' pushId push Vpush M') "(SI' & sV' & Local & F)".
      iDestruct "F" as %(? & ? & IP & HpushId & HE' & HM').
      rewrite /is_push in IP. subst push.
      iDestruct (own_valid_2 with "nodesA nodes") as %[= EQL]%excl_auth_agree_L.
      iMod (own_update_2 with "nodesA nodes") as "[nodesA nodes]".
      { apply (excl_auth_update _ _ (GSet {[pushId]})). }
      iIntros "!>".
      iSplitL "SI' nodesA".
      { iNext. iExists E'. rewrite HE' to_set_append -HpushId EQL right_id_L.
        iFrame. }
      iIntros "_". wp_seq.
      wp_apply (enqueue_spec _ _ _ 2 _ (λ _, True%I) with "[-$Q]"); [|auto].
      iExists E', pushId, (mkGraphEvent (Push 1) Vpush M'), M'.
      iFrame. iDestruct (view_at_elim with "sV' Local") as "$".
      iPureIntro. subst; simpl; split_and!; [by rewrite lookup_app_1_eq|done|set_solver].

    - (* second thread *)
      iIntros "_".
      wp_seq.
      wp_apply (dequeue_spec with "Q").
      iIntros (v) "R".
      wp_let. wp_op. rewrite bool_decide_decide.
      case decide => ?.
      { subst. wp_if. iApply "Post". iPureIntro; auto. }
      rewrite {2} /QueueInv.
      case decide => ?; wp_if; last first.
      { iApply "Post". auto. }

      subst; simpl.
      iApply (wp_step_fupd _ _ _ _ (∀ _, _ -∗ _)%I with "[$Post]"); [auto..|].

      iDestruct "R" as (E2 e eV M) "(F & #Q2 & nodes1)".
      iDestruct "F" as %(Eqe & Eqve & Inm).
      iDestruct (monPred_in_intro True%I with "[//]") as (V) "[#InV _]".
      awp_apply (pop_spec with "InV Q2"); [solve_ndisj|].
      iInv "I" as (E) ">[SI nodes]".
      iDestruct (StackLocal_history_snap with "Q2") as "Es".
      iDestruct (StackInv_history_snap with "SI Es") as %SubE2.
      iDestruct (StackInv_history_master_acc with "SI") as "[Em SI]".
      iDestruct (history_master_wf with "Em") as %EWF.
      iSpecialize ("SI" with "[$Em]").
      iAaccIntro with "SI".
      { iIntros "SI !>". iFrame. iNext. rewrite /StackInv1. iExists E. iFrame. }

      iIntros (v V' E' pushId popId push1 pop Vpush M') "(SI' & sV' & Local & F)".
      iDestruct "F" as %((? & ?) & CASE).
      iDestruct (own_valid_2 with "nodes nodes1") as %[= He]%excl_auth_agree_L.
      apply to_set_singleton in He as [-> EQL].
      assert (E = [eV]) as ->; last clear EQL.
      { eapply prefix_lookup_Some in Eqe; [|done]. destruct E; [done|].
        clear -Eqe EQL. simplify_list_eq. by apply nil_length_inv in EQL as ->. }
      iDestruct (StackInv_StackLinearizability with "SI'") as "#>%LIN".

      iMod (own_update_2 with "nodes nodes1") as "[nodes nodes1]".
      { by apply (excl_auth_update _ _ (GSet (to_set E'))). }
      destruct CASE as [CASE|[Lt0 CASE]].
      + exfalso.
        destruct CASE as (-> & -> & Eqde & HE' & HM').
        destruct LIN as [? lin ? ? ? _ _ ? _ ?].
        rewrite HE' app_length /= in XO.
        assert (lin = (([] ++ [0]) ++ [1]) ∨ lin = [1; 0])%nat as [->| ->].
        { simpl. apply Permutation_length_2_inv. by subst xo. }
        * apply stack_interp_snoc_inv in INTERP_LIN as (? & ? & INTERP1 & ? & RUN1).
          apply stack_interp_snoc_inv in INTERP1 as (? & ? & INTERP0 & ? & RUN0).
          apply stack_interp_nil_inv in INTERP0 as ->.
          simplify_list_eq.
          inversion RUN0; [|congruence].
          inversion RUN1; simplify_list_eq.
        * suff ? : (1 <= 0)%nat by lia.
          subst E'. eapply (HB_LIN 1 0 0 1)%nat; [done..|].
          simpl. set_solver +HM' Inm.
      + destruct CASE as (IE & ID & ? & ? & ? & ? & ? & ? & ?).
        rewrite /is_push in IE. rewrite /is_pop in ID. subst push1 pop.
        simplify_list_eq. rewrite Eqve in IE. injection IE as <-.
        iIntros "!>". iSplitL.
        { iNext. iExists _. by iFrame. }
        iIntros "_ H". iApply "H"; auto.
Qed.
End Stack.
