From iris.algebra Require Import excl_auth gset.
From iris.bi.lib Require Import fractional.
From iris.proofmode Require Import tactics.

From gpfsl.lang Require Import notation.
From gpfsl.logic Require Import logatom invariants proofmode.

From gpfsl.examples.stack Require Import spec_graph.
From gpfsl.examples.queue Require Import spec_per_elem.
From gpfsl.examples Require Import set_helper.

Require Import iris.prelude.options.

Local Notation EMPTY := 0%Z (only parsing).

Definition mpN := nroot .@ "mpN".

Local Notation graph := (graph sevent).

Implicit Types (G : graph) (E : gset event_id).

Section Stack.
  Context `{!noprolG Σ,
            !inG Σ (graphR sevent),
            !inG Σ (excl_authR (gset_disjR event_id))}.

  Local Notation iProp := (iProp Σ).
  Local Notation vProp := (vProp Σ).

  (** Assuming per-elem Queue spec *)
  Hypothesis qu : queue_per_elem_spec Σ.

  (** Assuming graph-based Stack spec *)
  Hypothesis stk : basic_stack_spec Σ.

  Definition prog  : expr :=
    let: "s" := stk.(new_stack) [] in
    let: "q" := qu.(new_queue) [] in 
    Fork
      (stk.(push) ["s"; #1 ];;
       qu.(enqueue) ["q"; #2]);;(* || *)
                                (* || *)  let: "b" := qu.(dequeue) [ "q" ] in
                                (* || *)  if: "b" = #2
                                (* || *)  then stk.(pop) ["s"] else #(-1).

  Lemma Ghost_alloc E :
    ⊢ |==> ∃ γs, own γs (●E (GSet E)) ∗ own γs (◯E (GSet E)).
  Proof.
    setoid_rewrite <- own_op.
    rewrite -own_alloc; first eauto. by apply excl_auth_valid.
  Qed.

  (* Stack Invariant *)
  Definition StackInv1 γg γs s: vProp :=
    ∃ G, stk.(StackInv) γg s 1%Qp G ∗ ⎡ own γs (●E (GSet (to_set G.(Es))))⎤.

  Local Existing Instances
    StackInv_Objective StackInv_Timeless StackLocal_Persistent
    queue_persistent.

  Instance StackInv_obj γg γs s : Objective (StackInv1 γg γs s) := _.

  Definition QueueInv s γg γs (v : Z) : vProp :=
    ( if decide (v = 2)
      then ∃ G i e k, ⌜ G.(Es) !! i = Some e /\ e.(ge_event) = Push 1 /\ i ∈ k⌝ ∗
                stk.(StackLocal) (mpN .@ "stk") γg s G k ∗
                ⎡ own γs (◯E (GSet {[i]})) ⎤
      else True)%I.

  Lemma mp_stack_spec tid :
    {{{ True }}}
      prog @ tid; ⊤
    {{{ n, RET #n; ⌜n = 1 ∨ n = -1⌝ }}}.
  Proof using All.
    iIntros (Φ) "_ Post".
    rewrite /prog.
    wp_apply (new_stack_spec _ (mpN .@ "stk") with "[//]").
    iIntros (γg s) "[#S SI]".
    iMod (Ghost_alloc ∅) as (γs) "[SA nodes]".
    wp_let.
    wp_apply (new_queue_spec _ (QueueInv s γg γs) with "[//]").
    iIntros (q) "#Q".
    wp_let.

    (* allocate invariants *)
    iMod (inv_alloc (mpN .@ "inv") _ (StackInv1 γg γs s) with "[SI SA]") as "#I".
    { iModIntro. rewrite / StackInv1. iExists ∅. iFrame. }

    (*forking *)
    wp_apply (wp_fork with "[nodes]"); first auto.
    - (* first thread *)
      iIntros "!>" (t').
      iDestruct (monPred_in_intro True%I with "[//]") as (V) "[#InV _]".
      awp_apply (push_spec with "InV S"); [solve_ndisj|lia|].
      iInv "I" as (G) "[SI >nodesA]".
      iAaccIntro with "SI".
      { iIntros "QI". iModIntro. iFrame "nodes". iNext. iExists G. iFrame. }
      iIntros (V' G' pushId push Vpush M') "(SI' & sV' & Local & F)".
      iDestruct "F" as %(SubG' & SubM' & Sub' & Sub'' & IQ & MAX' &
                        EsG' & SoG' & ComG' & EqM' & _).
      rewrite / is_push in IQ. subst push.
      iCombine "nodesA nodes" gives %[= EQL]%excl_auth_agree_L.

      iMod (own_update_2 with "nodesA nodes") as "[nodesA nodes]".
      { apply (excl_auth_update _ _ (GSet {[pushId]})). }
      iIntros "!>".
      iSplitL "SI' nodesA".
      { iNext. iExists G'. rewrite EsG' to_set_append -MAX' EQL right_id_L.
        iFrame. }
      iIntros "_". wp_seq.
      wp_apply (enqueue_spec _ _ _ 2 _ (λ _, True%I) with "[-$Q]"); [|auto].
      iExists G', pushId, (mkGraphEvent (Push 1) Vpush M'), M'.
      iFrame. iDestruct (view_at_elim with "sV' Local") as "$".
      iPureIntro. subst; simpl. by rewrite EsG' lookup_app_1_eq.

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

      iDestruct "R" as (G2 e eV M) "(F & #Q2 & nodes1)".
      iDestruct "F" as %(Eqe & Eqve & Inm).
      iDestruct (monPred_in_intro True%I with "[//]") as (V) "[#InV _]".
      awp_apply (pop_spec with "InV Q2"); [solve_ndisj|].
      iInv "I" as (G) ">[SI nodes]".
      iDestruct (StackLocal_graph_snap with "Q2") as "Gs".
      iDestruct (StackInv_graph_snap with "SI Gs") as %SubG2.
      iDestruct (StackInv_graph_master_acc with "SI") as (q') "[Gm SI]".
      iDestruct (graph_master_consistent with "Gm") as %EGC.
      iSpecialize ("SI" with "[$Gm]").
      iAaccIntro with "SI".
      { iIntros "SI !>". iFrame. iNext. rewrite /StackInv1. iExists G. iFrame. }

      iIntros (v V' G' pushId popId push1 pop Vpush M') "(SI' & sV' & Local & F)".
      iDestruct "F" as %((SubG' & SubM' & Sub' & Sub'') & CASE).
      iCombine "nodes nodes1" gives %[= He]%excl_auth_agree_L.
      have He' := He. apply to_set_singleton in He' as [EqeO EQL].

      iMod (own_update_2 with "nodes nodes1") as "[nodes nodes1]".
      { by apply (excl_auth_update _ _ (GSet (to_set G'.(Es)))). }
      destruct CASE as [CASE|[Lt0 CASE]].
      + destruct CASE as (-> & -> & Eqde & EsG' & SoG' & ComG' & EqM' & NInM').
        rewrite StackInv_StackConsistent.
        iDestruct "SI'" as ">%SC". exfalso.
        destruct SC as [_ Hcom _ _ HNE HSoCom _ _].
        have Eqd : G'.(Es) !! popId = Some (mkGraphEvent EmpPop Vpush M').
        { rewrite Eqde. rewrite  EsG'. rewrite lookup_app_1_eq. auto. }
        have Ine' : e ∈ M'. { set_solver+SubM' Inm. }
        have SubG2' : G2 ⊑ G' by etrans.

        assert (EqeV := prefix_lookup_Some _ _ _ _ Eqe (graph_sqsubseteq_E _ _ SubG2')).
        apply (HNE _ _ Eqd eq_refl _ Ine').
        split. { rewrite EqeV /= Eqve; eauto. }
        rewrite HSoCom. intros ? InG'.
        destruct (Hcom _ _ InG') as [Lee _].
        move : InG'. rewrite ComG'. move => /gcons_com_included /= [_ ].
        clear -He Lee. intros Lede.
        apply to_set_singleton in He as [-> EqL]. rewrite EqL in Lede. lia.
      + destruct CASE as (IE & ID & Eqpop & FRSo & EsG' & SoG' &
                    ComG' & InEM' & InDM' & NInM & eV' & EqEId & EqPush & SublV).
        assert (Ine : pushId ∈ to_set G.(Es)).
        { apply elem_of_set_seq. apply lookup_lt_Some in EqEId. lia. }
        rewrite He in Ine. apply elem_of_singleton in Ine. clear EqeO. subst e.
        rewrite (prefix_lookup_Some _ _ _ _ Eqe (graph_sqsubseteq_E _ _ SubG2)) in EqEId.
        inversion EqEId. subst eV'.
        rewrite -EqPush /is_push Eqve in IE; inversion IE; subst.
        iIntros "!>". iSplitL.
        { iNext. iExists G'. by iFrame. }
        iIntros "_ H". iApply "H"; auto.
Qed.
End Stack.
