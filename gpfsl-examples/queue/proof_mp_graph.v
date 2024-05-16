From iris.algebra Require Import excl_auth gset.
From iris.proofmode Require Import tactics.

From gpfsl.lang Require Import notation.
From gpfsl.logic Require Import logatom invariants proofmode.

From gpfsl.examples.stack Require Import spec_per_elem.
From gpfsl.examples.queue Require Import spec_graph.
From gpfsl.examples Require Import set_helper.

Require Import iris.prelude.options.

Definition mpN := nroot .@ "mpN".

Local Notation graph := (graph qevent).

Implicit Types (G : graph) (E : gset event_id).

Section StackQueue.

Context {Σ : gFunctors}.
Context `{noprolG Σ, inG Σ (graphR qevent),
                     inG Σ (excl_authR (gset_disjR event_id))}.

Local Notation iProp := (iProp Σ).
Local Notation vProp := (vProp Σ).

(** Assuming per-elem Stack spec *)
Hypothesis stk : stack_per_elem_spec Σ.

(** Assuming logical-atomicity graph-based spec of Queue *)
Hypothesis msq : basic_queue_spec Σ.

(* Message Passing with stack and queue *)
Definition prog : expr :=
  let: "q" := msq.(new_queue) [] in
  let: "s" := stk.(new_stack) [] in
  Fork
  ( msq.(enqueue) [ "q" ; #1 ];;  (* || *)
    stk.(push)    [ "s" ; #2 ]);; (* || *)
                                  (* || *) let: "b" := stk.(pop) [ "s" ] in
                                  (* || *) if: "b" = #2
                                  (* || *) then msq.(dequeue) [ "q" ] else #(-1)
  .

(* Authoritative set of Queue events *)
Definition QEAuth γs E : vProp := ⎡ own γs (●E (GSet E)) ⎤.
(* Fragment set of Queue events, asserting ownership of the subset E *)
Definition QEFrag γs E : vProp := ⎡ own γs (◯E (GSet E)) ⎤.

Lemma QE_ghost_alloc E : ⊢ |==> ∃ γ, QEAuth γ E ∗ QEFrag γ E.
Proof.
  rewrite /QEAuth /QEFrag.
  setoid_rewrite <- embed_sep. setoid_rewrite <- own_op.
  rewrite -embed_exist -embed_bupd -own_alloc; first eauto.
  by apply excl_auth_valid.
Qed.

Definition QueueInv1 q γg γs : vProp :=
  ∃ G, msq.(QueueInv) γg q G ∗ QEAuth γs (to_set G.(Es)).

Local Existing Instances
  QueueInv_Objective QueueLocal_Persistent
  stack_persistent.

Instance QueueInv_obj q γg γs : Objective (QueueInv1 q γg γs) := _.

Definition StackInv q γg γs (v : Z) : vProp :=
  (if decide (v = 2)
  then ∃ G i e k,
        (* the push of 2 has observed the Enq of 1 *)
        ⌜ G.(Es) !! i = Some e ∧ e.(ge_event) = Enq 1 ∧ i ∈ k ⌝ ∗
        msq.(QueueLocal) (mpN .@ "que") γg q G k ∗
        (* and in fact the Queue can only have that event so far *)
        QEFrag γs {[i]}
  else True)%I.

Lemma prog_spec tid :
  {{{ True }}}
    prog @ tid; ⊤
  {{{ n, RET #n; ⌜n = 1 ∨ n = -1⌝ }}}.
Proof using All.
  iIntros (Φ) "_ Post".
  rewrite /prog.

  (* setting up *)
  wp_apply (new_queue_spec _ (mpN .@ "que") with "[//]").
  iIntros (γg q) "[#Q QI]".
  iMod (QE_ghost_alloc ∅) as (γs) "[QA nodes]".
  wp_let.
  wp_apply (new_stack_spec _ (StackInv q γg γs) with "[//]").
  iIntros (s) "#S".
  wp_let.
  iMod (inv_alloc (mpN .@ "inv") _ (QueueInv1 q γg γs) with "[QI QA]") as "#I".
  { iNext. iExists _. by iFrame "QI QA". }
  (* forking *)
  wp_apply (wp_fork with "[nodes]"); first auto.
  - (* left thread *)
    iIntros "!>" (t').
    iDestruct (monPred_in_intro True%I with "[//]") as (V) "[#InV _]".
    awp_apply (enqueue_spec with "InV Q"); [solve_ndisj|lia|].
    iInv "I" as (G) "[QI >nodesA]".
    iAaccIntro with "QI".
    { simpl. iIntros "QI !>". iFrame "nodes". iNext.
      iExists G. by iFrame. }

    iIntros (V' G' enqId enq Venq M') "(QI' & sV' & Local & F)".
    iDestruct "F" as %(SubG' & SubM' & Sub' & Sub'' & IQ & MAX' &
                        EsG' & SoG' & ComG' & EqM' & _).
    rewrite /is_enqueue in IQ. subst enq.
    iCombine "nodesA nodes" gives %EqL%excl_auth_agree_L.
    inversion EqL as [EQL].

    iMod (own_update_2 with "nodesA nodes") as "[nodesA nodes]".
    { apply (excl_auth_update _ _ (GSet {[enqId]})). }
    iIntros "!>".
    iSplitL "QI' nodesA".
    { iNext. iExists G'. rewrite EsG' to_set_append EQL right_id_L -MAX'. iFrame. }

    iIntros "_". wp_seq.
    wp_apply (push_spec _ _ _ 2 _ (λ _, True%I) with "[-$S]"); [|auto].
    iExists G', enqId, (mkGraphEvent (Enq 1) Venq M'), M'.
    iDestruct (view_at_elim with "sV' Local") as "$".
    iFrame. iPureIntro; subst; simpl. by rewrite EsG' lookup_app_1_eq.

  - (* right thread *)
    iIntros "_".
    wp_seq.
    wp_apply (pop_spec with "S").
    iIntros (v) "R".
    wp_let.
    wp_op.
    rewrite bool_decide_decide.
    case decide => ?.
    { subst. wp_if. iApply "Post". auto. }
    rewrite {2}/StackInv.
    case decide => ?; wp_if; last first.
    { iApply "Post". auto. }

    subst; simpl.
    iApply (wp_step_fupd _ _ _ _ (∀ _, _ -∗ _)%I with "[$Post]"); [auto..|].

    iDestruct "R" as (G2 e eV M) "(F & #Q2 & nodes1)".
    iDestruct "F" as %(Eqe & Eqve & Inm).
    iDestruct (monPred_in_intro True%I with "[//]") as (V) "[#InV _]".
    awp_apply (dequeue_spec with "InV Q2"); [solve_ndisj|].
    iInv "I" as (G) "[QI >nodes]".
    rewrite QueueInv_graph_master_acc. iDestruct "QI" as "[>Gm QI]".
    iDestruct (graph_master_consistent with "Gm") as %EGC.
    iPoseProof (QueueLocal_graph_snap with "Q2") as "Gs".
    iDestruct (graph_master_snap_included with "Gm Gs") as %SubG2.
    iSpecialize ("QI" with "[$Gm]").
    iAaccIntro with "QI".
    { iIntros "QI !>". iFrame "nodes1". iNext. iExists G. by iFrame. }

    iIntros (v V' G' enqId deqId enq1 deq Venq M') "(QI' & sV' & Local & F)".
    iDestruct "F" as %(SubG' & SubM' & Sub' & Sub'' & CASE).
    iCombine "nodes nodes1" gives %EqL%excl_auth_agree_L.
    inversion EqL as [He].
    have He' := He. apply to_set_singleton in He' as [EqeO EQL]. clear EqL.

    iMod (own_update_2 with "nodes nodes1") as "[nodes nodes1]".
    { by apply (excl_auth_update _ _ (GSet (to_set G'.(Es)))). }
    eapply lookup_weaken in Eqe; last done.
    destruct CASE as [CASE|[Lt0 CASE]].
    + destruct CASE as
        (-> & -> & Eqde & EsG' & SoG' & ComG' & EqM' & NInM').
      rewrite QueueInv_QueueConsistent.
      iDestruct "QI'" as ">%QC". exfalso.
      destruct QC as [_ Hcom _ _ HNE HSoCom HBa HBb].
      have Eqd : G'.(Es) !! deqId = Some (mkGraphEvent EmpDeq Venq M').
      { by rewrite Eqde EsG' lookup_app_1_eq. }
      have Ine' : e ∈ M'. { set_solver+EqM' Inm. }
      have SubG2' : G2 ⊑ G' by etrans.
      assert (EqeV := prefix_lookup_Some _ _ _ _ Eqe (graph_sqsubseteq_E _ _ SubG2')).
      specialize (HNE _ _ Eqd eq_refl _ _ _ EqeV Eqve Ine').
      destruct HNE as (de & InG' & ?).
      destruct (Hcom _ _ InG') as [Lee _].
      move : InG'. rewrite ComG'. move => /gcons_com_included /= [_ ].
      clear -He Lee. intros Lede.
      apply to_set_singleton in He as [-> EqL]. rewrite EqL in Lede. lia.
    + destruct CASE as (IE & ID & Eqdeq & FRSo & EsG' & SoG' &
                    ComG' & InEM' & InDM' & NInM & eV' & EqEId & EqEnq & SublV).
      assert (Ine : enqId ∈ to_set G.(Es)).
      { apply elem_of_set_seq. apply lookup_lt_Some in EqEId. lia. }
      rewrite He in Ine. apply elem_of_singleton in Ine. clear EqeO. subst e.
      rewrite (prefix_lookup_Some _ _ _ _ Eqe (graph_sqsubseteq_E _ _ SubG2)) in EqEId.
      inversion EqEId; clear EqEId; subst eV'.
      rewrite -EqEnq /is_enqueue Eqve in IE; inversion IE; subst.
      iIntros "!>". iSplitR "nodes1".
      { iNext. iExists G'. by iFrame. }
      iIntros "_ H"; iApply "H"; auto.
Qed.
End StackQueue.
