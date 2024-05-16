From iris.algebra Require Import excl_auth.
From gpfsl.lang Require Import notation.
From gpfsl.logic Require Import logatom invariants proofmode.
From gpfsl.examples.graph Require Import spec.
From gpfsl.examples.queue Require Import spec_graph.
From gpfsl.examples Require Import set_helper.

Require Import iris.prelude.options.

(** * A proof that the graph-based queue specs imply the sequential spec *)

Local Notation event_list := (event_list qevent).
Local Notation graph := (graph qevent).

Implicit Types (G : graph) (E : event_list).
Implicit Types (γ : gname).

Local Notation ge := (flip (≤)%nat) (only parsing).
Local Notation elem_filter G G' :=
  (elements (filter (unmatched_enq_2 G') (to_set G.(Es)))) (only parsing).

(* Current enqueue events that are in the queue *)
Definition run_queue G : list event_id := merge_sort ge (elem_filter G G).

(* Retrieve the list of qevent from the list of event ids *)
Definition event_list_graph E (l: list event_id): list (option qevent) :=
  reverse ((λ h, ge_event <$> (E !! h)) <$> l).

(* The list [l] of events generate the queue values [lv] *)
Fixpoint run_queue_aux (l: list (option qevent)) : list Z :=
  match l with
  | [] => []
  | Some (Enq v) :: rest => run_queue_aux rest ++ [v]
  | Some (Deq v) :: rest => removelast (run_queue_aux rest)
  | _ :: _ => []
  end.
Definition queue_list (l : list (option qevent)) (lv : list Z) : Prop :=
  run_queue_aux l = lv.

Lemma list_add_G E1 E2 l:
  Forall (λ (i : event_id), i < length E1)%nat l →
  event_list_graph (E1 ++ E2) l = event_list_graph E1 l.
Proof.
  intros FA. rewrite /event_list_graph. f_equal.
  apply list_eq => i. rewrite !list_lookup_fmap.
  case lookup eqn:Eqe; [|done].
  rewrite ->Forall_forall in FA. apply elem_of_list_lookup_2, FA in Eqe.
  by rewrite /= lookup_app_l.
Qed.

Lemma list_add_levent E l1 l2:
  event_list_graph E (l1 ++ l2) = event_list_graph E l2 ++ event_list_graph E l1.
Proof. by rewrite /event_list_graph fmap_app reverse_app. Qed.

Lemma elem_in_set x G G' :
  x ∈ elem_filter G G' → x ∈ to_set G.(Es).
Proof. set_solver. Qed.

Lemma set_to_Lt (x : nat) G: x ∈ to_set G.(Es) ↔ (x < length G.(Es))%nat.
Proof. rewrite elem_of_set_seq. lia. Qed.

Lemma return_enq_1 G:
  set_Forall (λ i, ∃ v, ge_event <$> G.(Es) !! i = Some (Enq v))
             (filter (unmatched_enq_2 G) (to_set G.(Es))).
Proof.
  apply set_Forall_elements; rewrite Forall_forall.
  by intros ? [[??]?]%elem_of_elements%elem_of_filter.
Qed.

Lemma return_enq_2 G l:
  Forall (λ i, ∃ v, ge_event <$> G.(Es) !! i = Some (Enq v)) l →
  Forall (λ e, ∃ v, e = Some (Enq v)) (event_list_graph G.(Es) l).
Proof.
  induction l as [|?? IH]; intros H; simpl; first apply Forall_nil_2.
  rewrite /event_list_graph fmap_cons reverse_cons.
  apply Forall_app. split.
  + apply IH. by apply Forall_inv_tail in H.
  + apply Forall_inv in H. by apply Forall_singleton.
Qed.

Lemma merge_in_list x l : x ∈ merge_sort ge l ↔ x ∈ l.
Proof. by rewrite merge_sort_Permutation. Qed.

Lemma event_in_list e G l:
  e ∈ event_list_graph G.(Es) l → ∃ i, (ge_event <$> Es G !! i = e) ∧ i ∈ l.
Proof.
  rewrite /event_list_graph elem_of_reverse elem_of_list_fmap. naive_solver.
Qed.

Lemma merge_len_Lt G G':
  Forall (λ (i : event_id), i < length G.(Es))%nat
         (merge_sort ge (elem_filter G G')).
Proof.
  rewrite Forall_forall. intros ?. rewrite merge_in_list => /elem_in_set.
  by apply set_to_Lt.
Qed.

Lemma merge_return_enq G:
  Forall (λ e, ∃ v, e = Some (Enq v)) (event_list_graph G.(Es) (run_queue G)).
Proof.
  apply return_enq_2, Forall_forall; intros.
  apply return_enq_1, elem_of_elements. by eapply merge_in_list.
Qed.

Lemma len_Lt G G':
  Forall (λ i : event_id, i < length G.(Es))%nat (elem_filter G G').
Proof. rewrite -> Forall_forall. by intros ? ?%elem_in_set%set_to_Lt. Qed.

Lemma enqId_elem P (eid: event_id) (l : gset event_id) :
  Forall P (elements ({[eid]} ∪ l)) → Forall P (elements l).
Proof. rewrite !Forall_forall. set_solver. Qed.

Lemma not_in_set l (x: event_id) : x ∉ l → Forall (λ (i :event_id), i ≠ x) l.
Proof. rewrite Forall_forall; set_solver. Qed.

Lemma sort_max (x : nat) l:
  Forall (λ (i : event_id), i < x)%nat l →
  StronglySorted ge l → StronglySorted ge (x :: l).
Proof.
  intros FA HS; constructor; auto.
  eapply Forall_impl; first apply FA.
  simpl; lia.
Qed.

Lemma merge_max (x : event_id) l:
  Forall (λ (i : event_id), i < x)%nat l →
  merge_sort ge ([x] ++ l) = [x] ++ merge_sort ge l.
Proof.
  intros; apply : (StronglySorted_unique ge).
  - apply : StronglySorted_merge_sort.
  - apply sort_max.
    + rewrite merge_sort_Permutation; auto.
    + apply : StronglySorted_merge_sort.
  - by rewrite /= !merge_sort_Permutation Permutation_cons_append.
Qed.

Lemma sort_min (x : nat) l:
  Forall (λ (i : event_id), i > x)%nat l →
  StronglySorted ge l → StronglySorted ge (l ++ [x]).
Proof.
  intros FA HS.
  intros; induction l as [|?? IH].
  - constructor; auto.
  - simpl; inversion HS; subst. inversion FA; subst.
    constructor.
    + apply IH; auto.
    + apply Forall_app_2; auto. constructor; auto; simpl; lia.
Qed.

Lemma merge_min (x : event_id) l:
  Forall (λ (i : event_id), i > x)%nat l →
  merge_sort ge ([x] ++ l) = merge_sort ge l ++ [x].
Proof.
  intros; apply : (StronglySorted_unique ge).
  - apply : StronglySorted_merge_sort.
  - apply sort_min.
    + rewrite merge_sort_Permutation; auto.
    + apply : StronglySorted_merge_sort.
  - by rewrite /= !merge_sort_Permutation Permutation_cons_append.
Qed.

Lemma merge_elem_1 (eid : event_id) (l : gset event_id) :
  {[eid]} ## l →
  Forall (λ x : event_id, x < eid)%nat (elements l) →
  merge_sort ge (elements ({[eid]} ∪ l)) =
  elements ({[eid]} : gset _) ++ merge_sort ge (elements l).
Proof.
  intros. rewrite elements_singleton -merge_max; last done.
  apply (Sorted_unique ge); try apply : Sorted_merge_sort.
  rewrite !merge_sort_Permutation elements_disj_union; auto.
  by rewrite elements_singleton.
Qed.

Lemma merge_elem_2 (eid : event_id) (l : gset event_id) :
  {[eid]} ## l →
  Forall (λ x : event_id, x > eid)%nat (elements l) →
  merge_sort ge (elements ({[eid]} ∪ l)) =
  merge_sort ge (elements l) ++ [eid].
Proof.
  intros. rewrite -merge_min; last done.
  apply (Sorted_unique ge); try apply : Sorted_merge_sort.
  rewrite !merge_sort_Permutation elements_disj_union; auto.
  by rewrite elements_singleton.
Qed.

Lemma add_run_queue_aux l v:
  Forall (λ e, ∃ v, e = Some (Enq v)) l →
  run_queue_aux (l ++ [Some (Enq v)]) =
  run_queue_aux [Some (Enq v)] ++ run_queue_aux l.
Proof.
  intros HA; induction l as [|?? IH]; simpl; first done.
  apply Forall_cons in HA as [[? ->] ?]. by rewrite IH.
Qed.

Lemma remove_last (v : Z) l : v ∈ removelast l → v ∈ l.
Proof.
  induction l as [|?? IH]; auto; simpl.
  destruct l; [set_solver|]. intros [->|]%elem_of_cons; apply elem_of_cons; auto.
Qed.

Lemma run_queue_inv l v: v ∈ run_queue_aux l → Some (Enq v) ∈ l.
Proof.
  induction l as [|e ? IH]; simpl; [set_solver|]; intros H.
  apply elem_of_cons. destruct e as [[]|].
  - apply elem_of_app in H as [?%IH| <-%elem_of_list_singleton]; auto.
  - apply remove_last in H. auto.
  - set_solver+H.
  - set_solver+H.
Qed.

Lemma exists_enq z l levent G:
  run_queue_aux (event_list_graph G.(Es) levent) = z :: l →
  ∃ eid, ge_event<$> Es G !! eid = Some (Enq z) ∧ eid ∈ levent.
Proof.
  intros H. apply event_in_list, run_queue_inv.
  rewrite H. apply elem_of_cons; auto.
Qed.

Definition InLogView G (M : logView) : Prop :=
  set_Forall (λ (i : event_id), ∃ eV, Es G !! i = Some eV ∧ i ∈ M ∧
                                ∀ (j : event_id), (j < i)%nat → j ∈ eV.(ge_lview))
             (to_set G.(Es)).

Lemma extend_LogView G M G' M' e V :
  InLogView G M →
  G'.(Es) = Es G ++ [ (mkGraphEvent e V M') ] →
  M ⊑ M' →
  length G.(Es) ∈ M' →
  InLogView G' M'.
Proof.
  unfold InLogView. intros H HEs HM Hi. rewrite HEs to_set_append.
  apply set_Forall_union.
  - apply set_Forall_singleton.
    rewrite list_lookup_middle; last done.
    eexists; split; eauto; split; auto.
    intros ? Hin; simpl.
    destruct (H j) as (? & ? & ? & ?); auto.
    by apply set_to_Lt.
  - apply (set_Forall_impl _ _ _ H). intros ? (?&?&?&?).
    eexists. split; [|eauto]. by apply lookup_app_l_Some.
Qed.

Section SequentialQueue.
  Context `{!noprolG Σ, !inG Σ (graphR qevent)}.
  Context `(qu : weak_queue_spec Σ).

  Local Notation vProp := (vProp Σ).

  Local Existing Instances
    QueueInv_Objective
    QueueInv_Timeless
    QueueLocal_Persistent
    .

  Definition SeqQueue N γg q l : vProp :=
    ∃ G M,
      ⌜ queue_list (event_list_graph G.(Es) (run_queue G)) l ∧ InLogView G M ⌝ ∗
      qu.(QueueLocal) N γg q G M ∗
      qu.(QueueInv) γg q G.

  (* PROOF FOR ENQUEUE *)
  Lemma seq_enqueue_spec N (DISJ: N ## histN)
    γg (q : loc) (l: list Z) (v : Z) tid:
    {{{ ⌜0 < v⌝ ∗ SeqQueue N γg q l }}}
      qu.(enqueue) [ #q; #v ] @ tid ; ⊤
    {{{ RET #☠; SeqQueue N γg q (v :: l) }}}.
  Proof using All.
    iIntros (Φ) "[%Ge0 Q] Post".
    iDestruct "Q" as (G M) "[[%eList %iLog] [#QL QI]]".
    iDestruct (monPred_in_intro True%I with "[//]") as (V) "[#InV _]".
    iApply (wp_step_fupd _ _ ⊤ _ (SeqQueue N γg q (v :: l) -∗ Φ #☠)%I
              with "[$Post]"); [auto..|].
    awp_apply (qu.(enqueue_spec) with "InV QL"); [solve_ndisj|done|].
    iAaccIntro with "QI".
    { iIntros ">QI !>"; iFrame. }
    iIntros (V' G' enqId enq Venq M') "(>QI & #sV1 & #QL1 & %F)".

    destruct F as (SubG' & SubM & EqV0 & EqV1 &
                   Eqenq & Eqlen & EsG' & SoG' & ComG' & InM1 & NInM1).
    iIntros "!> _ Post !>".
    iApply "Post".
    iExists G', M'.
    iFrame "QI".
    iSplit; last by iDestruct (view_at_elim with "sV1 QL1") as "$".
    iPureIntro; split; last by eapply extend_LogView; subst; eauto.

    have Eqts : to_set G'.(Es) = {[enqId]} ∪ to_set G.(Es).
    { by rewrite EsG' to_set_append -Eqlen. }
    have EqEm' : G'.(Es) !! enqId = Some (mkGraphEvent (Enq v) Venq M').
    { by rewrite EsG' Eqenq Eqlen lookup_app_1_eq. }
    have UMe: unmatched_enq_2 G' enqId.
    { split.
      - rewrite EqEm'; by eexists.
      - move => ??. rewrite SoG'. move => /(gcons_so_included G) [/=]. lia. }
    have NIn: enqId ∉ filter (unmatched_enq_2 G) (to_set G.(Es)).
    { move => /elem_of_filter [[? FA] /elem_of_set_seq]; lia. }

    rewrite /run_queue.
    rewrite (_: filter (unmatched_enq_2 G') (to_set G'.(Es)) =
                {[enqId]} ∪ filter (unmatched_enq_2 G) (to_set G.(Es))); last first.
    { rewrite Eqts filter_union_L filter_singleton_L; auto.
      f_equal. apply leibniz_equiv => i. rewrite !elem_of_filter.
      assert (Hi: i ∈ to_set G.(Es) → (unmatched_enq_2 G' i ↔ unmatched_enq_2 G i)).
      { intros Hi.
        have NEi : i ≠ length G.(Es).
        { apply elem_of_set_seq in Hi. intros ->. clear -Hi. lia. }
        rewrite /unmatched_enq_2 SoG' {1}EsG' lookup_app_1_ne; [|done].
        rewrite Eqts. split; intros [? SA]; (split; [done|]).
        - by apply set_Forall_union_inv_2 in SA.
        - apply set_Forall_union; [|done]. apply set_Forall_singleton.
        move => /gcons_so_included [/= _]. lia. }
      clear -Hi. split; (intros []; split; [by apply Hi|done]). }

    rewrite  merge_elem_1; last first; auto.
    { rewrite Eqlen; by apply len_Lt. }
    { by apply disjoint_singleton_l. }
    rewrite elements_singleton list_add_levent.
    rewrite {2}/event_list_graph list_fmap_singleton reverse_singleton.
    rewrite EqEm' EsG'.
    pose proof merge_len_Lt as LeLen.
    specialize (LeLen G).
    rewrite list_add_G; auto.
    rewrite /queue_list add_run_queue_aux.
    - by rewrite -eList.
    - apply merge_return_enq.
  Qed.

  (* PROOF FOR DEQUEUE *)
  Lemma seq_dequeue_spec N (DISJ: N ## histN)
    γg (q : loc) (l: list Z) (v : Z) tid:
   {{{ SeqQueue N γg q l }}}
      qu.(dequeue) [ #q ] @ tid ; ⊤
    {{{ (v : Z), RET #v;
        ⌜ if bool_decide (v = 0) then l = [] else last l = Some v ⌝ ∗
          SeqQueue N γg q (removelast l) }}}.
  Proof using All.
    iIntros (Φ) "Q Post".
    rewrite {1} /SeqQueue.
    iDestruct "Q" as (G M) "[[%eList %iLog] [#QL QI]]".
    rewrite QueueInv_graph_master_acc. iDestruct "QI" as "[Gm QI]".
    iDestruct (graph_master_consistent with "Gm") as %EGC.
    iSpecialize ("QI" with "[$Gm]").
    iPoseProof (QueueInv_QueueConsistent with "QI") as "%WQ1".
    iDestruct (monPred_in_intro True%I with "[//]") as (V) "[#InV _]".
    iApply (wp_step_fupd _ _ ⊤ _ (∀ v : Z, _ -∗ Φ #v)%I with "[$Post]"); [auto..|].
    awp_apply (qu.(dequeue_spec) with "InV QL"); first solve_ndisj.
    iAaccIntro with "QI".
    { iIntros ">QI !>"; iFrame. }
    iIntros (v1 V' G' enqId deqId enq1 deq Vdeq M') "(QI' & sV' & Local & F)".
    iDestruct "F" as %(SubG' & SubM' & Sub' & Sub'' & CASE).
    iIntros "!> _ Post".
    iApply "Post".
    set (dV := mkGraphEvent deq Vdeq M') in *.
    rewrite QueueInv_graph_master_acc. iDestruct "QI'" as "[>Gm >QI']".
    iDestruct (graph_master_consistent with "Gm") as %EGC'.
    iSpecialize ("QI'" with "[$Gm]").
    iPoseProof (QueueInv_QueueConsistent with "QI'") as "%WQ".
    destruct WQ1 as [_ _ _ QC1].
    destruct WQ as [_ _ _ QC].
    pose proof QC as QC'.
    destruct QC as [_ Hcom _ _ HNE HSoCom HBa HBb].
    unfold graph_xo_eco in HBa.
    unfold queue_FIFO in HBb.
    iIntros "!>".
    destruct CASE as [CASE|[Lt0 CASE]].
    + (* EMPTY CASE *)
      destruct CASE as (-> & -> & Eqde & EsG' & SoG' & ComG' & EqM' & NInM').
      simpl.
      have HdV : G'.(Es) !! deqId = Some dV.
      { subst deqId. rewrite EsG'. apply lookup_app_1_eq. }
      have Eqts : to_set G'.(Es) = {[deqId]} ∪ to_set G.(Es).
      { by rewrite EsG' to_set_append Eqde. }
      have EqEm' : G'.(Es) !! deqId = Some (mkGraphEvent EmpDeq Vdeq M').
      { by rewrite EsG' Eqde lookup_app_1_eq. }
      have Hi: ∀ i, i ∈ to_set G.(Es) → (unmatched_enq_2 G' i ↔ unmatched_enq_2 G i).
      { intros i Hi.
        have NEi : i ≠ length G.(Es).
        { apply elem_of_set_seq in Hi. intros ->. clear -Hi. lia. }
        rewrite /unmatched_enq_2 SoG' {1}EsG' lookup_app_1_ne; [|done].
        rewrite Eqts. split; intros [? SA]; (split; [done|]).
        - by apply set_Forall_union_inv_2 in SA.
        - apply set_Forall_union; [|done]. apply set_Forall_singleton.
          move => /gcons_so_included [/= _]. rewrite Eqde. clear; lia. }
      have UNMATCHG: filter (unmatched_enq_2 G) (to_set G.(Es)) =
                     filter (unmatched_enq_2 G') (to_set (G'.(Es))).
      { rewrite Eqts filter_union_L filter_singleton_not_L; last first.
        { intros [[v' Eqv] _]. by rewrite EqEm' in Eqv. }
        rewrite left_id_L.
        apply leibniz_equiv => i. rewrite !elem_of_filter.
        split; (intros []; split; [by apply Hi|done]). }
      (* Prove l = []*)
      have HlEmp: l = [].
      { destruct l; auto.
        exfalso. (*Prove by contradiction*)
        unfold run_queue in eList.
        apply set_Forall_elements in iLog.
        rewrite -> Forall_forall in iLog.
        apply exists_enq in eList.
        destruct eList as (eid & (EsEid & EidG')).
        apply list_lookup_fmap_inv' in EsEid.
        destruct EsEid as [eV1 (? & ?)].
        have EidG: eid ∈ filter (unmatched_enq_2 G) (to_set G.(Es)).
        { rewrite -> merge_in_list in EidG'; clear -EidG'; set_solver. }
        apply elem_of_filter in EidG.
        destruct EidG as (UNMATCHED & EidG).
        have eIdEs: eid ∈ elements (to_set G.(Es)).
        { set_solver + EidG. }
        destruct UNMATCHED as (_ & UNMATCHED).
        apply iLog in eIdEs.
        destruct eIdEs as (? & eIdM).
        refine (_ (bsq_cons_non_empty _ QC' _ _ HdV
                  ltac:(done) eid _ eV1 _ ltac:(done) _)); cycle 1.
        { rewrite EsG'. eapply prefix_lookup_Some; [done|by eexists]. }
        { set_solver + eIdM dV SubM'. }
        intros (d' & ComEd' & _).
        rewrite ComG' -(bsq_cons_so_com _ QC1) in ComEd'.
        apply (UNMATCHED d'); [|done].
        specialize (egcons_so _ EGC _ _ ComEd') as (_ & dV' & _ & HdV' & _).
        apply lookup_lt_Some in HdV'.
        rewrite /to_set. apply elem_of_set_seq; lia. }
      subst; iSplit; auto; simpl.
      iExists _, _; iFrame.
      iSplit; last by iDestruct (view_at_elim with "sV' Local") as "$".
      iPureIntro.
      (* Prove queue_list (event_list_graph (G'.(Es)) (run_queue G')) l *)
      apply union_subseteq in EqM' as [?%singleton_subseteq_l _].
      split; last eapply extend_LogView; subst; eauto.
      unfold queue_list in *.
      rewrite EsG' list_add_G.
      { unfold run_queue in *; by rewrite -UNMATCHG. }
      unfold run_queue.
      rewrite -UNMATCHG Forall_forall.
      intros ? Ine.
      rewrite -> merge_in_list in Ine.
      have xInG: x ∈ to_set G.(Es).
      { set_solver + Ine. }
      apply elem_of_set_seq in xInG; lia.

    + (*NOT EMPTY*)
      rewrite bool_decide_false; [|lia].
      destruct CASE as
          (IE & ID & Eqdeq & FRSo & EsG' & SoG' & ComG' & InEM' & InDM'
                  & NInM & eV & EqEId & EqEnq & SubM).
      rewrite /is_enqueue in IE. rewrite /is_dequeue in ID. subst enq1 deq.
      destruct eV as [x' Venq Menq]. simpl in *. subst x'.
      have ?: enqId ≠ deqId.
      { intros ?. subst deqId enqId. apply lookup_lt_Some in EqEId. lia. }
      have Eqts : to_set G'.(Es) = {[deqId]} ∪ to_set G.(Es).
      { by rewrite EsG' to_set_append -Eqdeq. }
      have EqDm' : G'.(Es) !! deqId = Some (mkGraphEvent (Deq v1) Vdeq M').
      { by rewrite EsG' Eqdeq lookup_app_1_eq. }
      have EqEm' : G'.(Es) !! enqId = Some (mkGraphEvent (Enq v1) Venq Menq).
      { rewrite EsG' lookup_app_1_ne; [done|by rewrite -Eqdeq]. }
      have FGG': filter (unmatched_enq_2 G) (to_set G.(Es)) =
                 {[enqId]} ∪ filter (unmatched_enq_2 G') (to_set (G'.(Es))).
      { rewrite Eqts filter_union_L filter_singleton_not_L; last first.
        { intros [[v' Eqv] _]. by rewrite EqDm' in Eqv. }
        rewrite left_id_L. apply leibniz_equiv => i.
        rewrite elem_of_union elem_of_singleton !elem_of_filter.
        case (decide (i = enqId)) => ?; last split.
        - subst i. split; [by left|]. intros _. split; first split.
          + rewrite EqEId. by eexists.
          + intros ??. apply FRSo.
          + apply elem_of_set_seq. apply lookup_lt_Some in EqEId.
            clear -EqEId; lia.
        - intros [[Eqi FA] Ini]. right. split; [split|done].
          + rewrite EsG' lookup_app_1_ne //.
            move : Ini => /elem_of_set_seq. clear; lia.
          + rewrite Eqts SoG'. intros i'.
            rewrite elem_of_union elem_of_singleton.
            move => [?|/FA].
            * subst i'. move => /elem_of_union [/elem_of_singleton|].
              { inversion 1. by subst i. }
              { move => /gcons_so_included [/= _]. rewrite Eqdeq. clear; lia. }
            * move => ? /elem_of_union [/elem_of_singleton|//].
              inversion 1. by subst i.
        - intros [?|[UM Ini]]; [by subst|]. split; [|done].
          move : UM. rewrite /unmatched_enq_2 Eqts EsG' lookup_app_1_ne.
          * rewrite SoG'. intros [? FA]. split; [done|].
            intros i' Ini' Inso'. apply (FA i').
            { clear -Ini'. set_solver. }
            { clear -Inso'. set_solver. }
          * move : Ini => /elem_of_set_seq. clear; lia. }

      have enqIdNUM: {[enqId]} ## filter (unmatched_enq_2 G') (to_set (G'.(Es))).
      { apply disjoint_singleton_l.
        move => /elem_of_filter [[? FA] InG']. apply (FA deqId).
        - rewrite Eqts. set_solver-.
        - rewrite SoG'. set_solver-. }
      have deqIdUN: ¬ unmatched_enq_2 G' deqId.
      { intros [[v' Eqv] _]; by rewrite EqDm' in Eqv. }
      set (dVenq := mkGraphEvent (Enq v1) Venq Menq) in *.
      have enqIdInG: enqId ∈ (to_set G.(Es)). { set_solver+FGG'. }
      apply iLog in enqIdInG as (x & H & _ & jInLog).
      rewrite EqEId in H; inversion H; subst x; clear H.
      (* prove enqId is the smallest element of the list *)
      have enqId_sml: Forall (λ i : event_id, ¬ i < enqId)%nat
                             (elem_filter G G).
      { apply Forall_Exists_neg.
        rewrite Exists_exists.
        intros (x & xInG & xLTenq).
        have xNEenq: x ≠ enqId by lia.
        apply jInLog in xLTenq.
        apply elem_of_elements in xInG.
        have xInG' := xInG.
        apply elem_of_filter in xInG' as [[[t xUM1] xUM2] _].
        apply list_lookup_fmap_inv' in xUM1  as (dVenqt & xUM1 & EsGx).
        have ?: x ≠ deqId. { intros ?; apply lookup_lt_Some in EsGx. lia. }
        have eIdxEm' : G'.(Es) !! x = Some dVenqt.
        { rewrite EsG' lookup_app_1_ne; [done|by rewrite -Eqdeq]. }
        have EdCom': (enqId, deqId) ∈ G'.(com). { set_solver+ComG'. }
        symmetry in xUM1.
        destruct (HBb _ _ _ _ _ _ eIdxEm' xUM1 EdCom' EqEm' xLTenq)
          as [d1 (eidCom' & ?)].
        assert (unmatched_enq_2 G' x) as [_ eidxUN%set_Forall_elements].
        { move : xInG. rewrite FGG' elem_of_union elem_of_singleton.
          clear -xNEenq. by intros [?|[]%elem_of_filter]. }
        rewrite -> Forall_forall in eidxUN.
        apply (eidxUN d1); [|by rewrite HSoCom].
        apply Hcom in eidCom'  as (_ & ? & ? & ? & _ & ?%lookup_lt_Some & _).
        by apply elem_of_elements, set_to_Lt.
      }  (*finish proving enqId is the smallest element of the list*)
      rewrite FGG' in enqId_sml. apply enqId_elem in enqId_sml.
      have enqIdNUM' := enqIdNUM.
      apply disjoint_singleton_l in enqIdNUM.
      have enqIdNUM1: enqId ∉ elem_filter G' G'. { set_solver+ enqIdNUM. }
      apply not_in_set in enqIdNUM1.
      have LT: ∀ (x: event_id), (¬ x < enqId)%nat ∧ x ≠ enqId → (x > enqId)%nat.
      { lia. }
      specialize (List.Forall_and enqId_sml enqIdNUM1) as HLT.
      simpl in HLT.
      eapply (Forall_impl _ (λ x : event_id, x > enqId)%nat) in LT; eauto.
      clear HLT enqId_sml enqIdNUM1.
      unfold queue_list, run_queue in eList; rewrite -eList.
        (*Prove Some v1 = last l ∧
            queue_list (event_list_graph (G'.(Es)) (run_queue G')) (removelast l)*)
      iSplit.
      * (*LAST*)
        iPureIntro; rewrite FGG' merge_elem_2; [|done..].
        rewrite list_add_levent.
        simpl; by rewrite EqEId last_snoc.
      * (* REMOVE LAST *)
        iExists _, _; iFrame.
        iSplit; last by iDestruct (view_at_elim with "sV' Local") as "$".
        iPureIntro.
        split; last eapply extend_LogView; subst; eauto.
        rewrite FGG' merge_elem_2; auto.
        rewrite list_add_levent; simpl.
        rewrite EqEId removelast_last.
        unfold run_queue, queue_list.
        rewrite{1} EsG' list_add_G; auto.
        rewrite Eqts filter_union_L filter_singleton_not_L; last first; auto.
        rewrite left_id_L.
        by eapply merge_len_Lt.
  Qed.
End SequentialQueue.
