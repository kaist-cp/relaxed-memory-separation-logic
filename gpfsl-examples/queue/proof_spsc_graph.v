From stdpp Require Import namespaces.

From iris.algebra Require Import excl_auth.
From gpfsl.logic Require Import logatom invariants proofmode.
From gpfsl.examples.graph Require Export spec.
From gpfsl.examples.queue Require Export event spec_graph spec_spsc.

Require Import iris.prelude.options.

(** Simplified/strengthened queue specification for SPSC (single-producer,
  single-consumer) case, based on the graph-based LAT spec for queue. *)

Local Notation graph := (graph qevent).
Implicit Type
  (G : graph) (M : logView)
  (es ds xs : list event_id).

Local Hint Constructors Produced Consumed EmpDeqs : core.

Section proof.
Context `{!noprolG Σ,
          !inG Σ (graphR qevent),
          !inG Σ (prodR (excl_authR (leibnizO (list event_id)))
                        (excl_authR (leibnizO (list event_id))))}.
Context (wq : weak_queue_spec Σ).
Local Existing Instances QueueInv_Timeless QueueInv_Objective QueueLocal_Persistent.

Local Notation iProp := (iProp Σ).
Local Notation vProp := (vProp Σ).

Local Open Scope nat_scope.

Definition QEAuth γed es ds : vProp :=
  ⎡ own γed (●E (es : leibnizO (list event_id)),
             ●E (ds : leibnizO (list event_id))) ⎤.
Definition QEes γed es : vProp :=
  ⎡ own γed (◯E (es : leibnizO (list event_id)), ◯ None) ⎤.
Definition QEds γed ds : vProp :=
  ⎡ own γed (◯ None, ◯E (ds : leibnizO (list event_id))) ⎤.

#[local] Lemma QE_alloc :
  ⊢ |==> ∃ γed, QEAuth γed [] [] ∗ QEes γed [] ∗ QEds γed [].
Proof.
  rewrite /QEAuth /QEes /QEds.
  do 2 setoid_rewrite <- embed_sep. do 2 setoid_rewrite <- own_op.
  rewrite -embed_exist -embed_bupd -own_alloc; first eauto.
  rewrite /excl_auth_auth /excl_auth_frag.
  rewrite -pair_op -!auth_frag_op left_id right_id.
  split; by apply auth_both_valid_2.
Qed.

#[local] Lemma QEes_update {γed es ds} es' :
  QEAuth γed es ds -∗ QEes γed es ==∗ QEAuth γed es' ds ∗ QEes γed es'.
Proof.
  iIntros "E1 E2". iCombine "E1 E2" as "E".
  setoid_rewrite <- embed_sep. setoid_rewrite <- own_op.
  iMod (own_update with "E") as "$"; last done.
  apply prod_update; simpl; [|done]. apply excl_auth_update.
Qed.

#[local] Lemma QEds_update {γed es ds} ds' :
  QEAuth γed es ds -∗ QEds γed ds ==∗ QEAuth γed es ds' ∗ QEds γed ds'.
Proof.
  iIntros "E1 E2". iCombine "E1 E2" as "E".
  setoid_rewrite <- embed_sep. setoid_rewrite <- own_op.
  iMod (own_update with "E") as "$"; last done.
  apply prod_update; simpl; [done|]. apply excl_auth_update.
Qed.

Definition SPSCInv γg γed q G es ds : vProp := ∃ xs,
  wq.(QueueInv) γg q G ∗
  QEAuth γed es ds ∗
  (* Thanks to SPSC, we can easily have an inductive invariant that matches up
    enqueue events by the producer and dequeue events by the consumer at every
    (dequeue) step, instead of having to look into the whole history and prove
    that only one certain permutation is possible. *)
  ⌜ seq 0 (length G.(Es)) ≡ₚ es ++ ds ++ xs ∧
    Produced G es ∧
    Consumed G ds ∧
    matches G es ds ∧
    EmpDeqs G xs ⌝
  .

Definition Producer N γg γed q G M es : vProp :=
  wq.(QueueLocal) N γg q G M ∗
  QEes γed es ∗
  ⌜ Produced G es ∧ Forall (λ e, e ∈ M) es ⌝.

Definition Consumer N γg γed q G M ds : vProp :=
  wq.(QueueLocal) N γg q G M ∗
  QEds γed ds ∗
  ⌜ Consumed G ds ∧ Forall (λ e, e ∈ M) ds ⌝.

Instance SPSCInv_Timeless γg γed q G es ds :
  Timeless (SPSCInv γg γed q G es ds) := _.
Instance SPSCInv_Objective γg γed q G es ds :
  Objective (SPSCInv γg γed q G es ds) := _.
Lemma SPSCInv_matches γg γed q G es ds :
  SPSCInv γg γed q G es ds ⊢ ⌜ matches G es ds ⌝.
Proof.
  by iDestruct 1 as "[%xs [QI (●ed & %PERM & %PROD & %CONS & %MATCH & %EMP)]]".
Qed.
Lemma SPSCInv_QueueInv_acc  γg γed q G es ds :
  SPSCInv γg γed q G es ds ⊢
  wq.(QueueInv) γg q G ∗
  (wq.(QueueInv) γg q G -∗ SPSCInv γg γed q G es ds).
Proof.
  iDestruct 1 as "[%xs [QI (●e●d & %PERM & %PROD & %CONS & %MATCH & %EMP)]]".
  iFrame "QI". iIntros "QI". iExists _. by iFrame.
Qed.

Lemma Producer_exclusive N γg γed q G1 G2 M1 M2 es1 es2 :
  Producer N γg γed q G1 M1 es1 -∗ Producer N γg γed q G2 M2 es2 -∗ False.
Proof.
  iDestruct 1 as "(_ & ◯e1 & _)". iDestruct 1 as "(_ & ◯e2 & _)".
  by iCombine "◯e1 ◯e2" gives %[?%excl_auth_frag_op_valid ?].
Qed.
Lemma Producer_QueueLocal N γg γed q G M es :
  Producer N γg γed q G M es ⊢ wq.(QueueLocal) N γg q G M.
Proof. iDestruct 1 as "[$ _]". Qed.
Lemma Producer_Produced N γg γed q G M es :
  Producer N γg γed q G M es ⊢ ⌜ Produced G es ⌝.
Proof. iDestruct 1 as "(_ & _ & $ & _)". Qed.
Lemma Producer_agree N γg γed q G G' M es es' ds :
  SPSCInv γg γed q G es ds -∗ Producer N γg γed q G' M es' -∗ ⌜ es = es' ⌝.
Proof.
  iDestruct 1 as "[%xs [QI (●ed & %PERM & %PROD & %CONS & %MATCH & %EMP)]]".
  iDestruct 1 as "(_ & ◯e & _ & _)".
  by iCombine "●ed ◯e" gives %[<-%excl_auth_agree_L ?].
Qed.

Lemma Consumer_exclusive N γg γed q G1 G2 M1 M2 ds1 ds2 :
  Consumer N γg γed q G1 M1 ds1 -∗ Consumer N γg γed q G2 M2 ds2 -∗ False.
Proof.
  iDestruct 1 as "(_ & ◯d1 & _)". iDestruct 1 as "(_ & ◯d2 & _)".
  by iCombine "◯d1 ◯d2" gives %[? ?%excl_auth_frag_op_valid].
Qed.
Lemma Consumer_QueueLocal N γg γed q G M ds :
  Consumer N γg γed q G M ds ⊢ wq.(QueueLocal) N γg q G M.
Proof. iDestruct 1 as "[$ _]". Qed.
Lemma Consumer_Consumed N γg γed q G M ds :
  Consumer N γg γed q G M ds ⊢ ⌜ Consumed G ds ⌝.
Proof. iDestruct 1 as "(_ & _ & $ & _)". Qed.
Lemma Consumer_agree N γg γed q G G' M es ds ds' :
  SPSCInv γg γed q G es ds -∗ Consumer N γg γed q G' M ds' -∗ ⌜ ds = ds' ⌝.
Proof.
  iDestruct 1 as "[%xs [QI (●ed & %PERM & %PROD & %CONS & %MATCH & %EMP)]]".
  iDestruct 1 as "(_ & ◯d & _ & _)".
  by iCombine "●ed ◯d" gives %[? <-%excl_auth_agree_L].
Qed.


Lemma new_queue_spsc_spec :
  new_queue_spsc_spec' wq.(new_queue) Producer Consumer SPSCInv.
Proof.
  intros ??.
  iIntros (Φ) "_ Post".
  iMod QE_alloc as (γed) "(●ed & ◯e & ◯d)".
  iApply (wq.(new_queue_spec) with "[%//]").
  iIntros "!> * [#QL QI]". iApply "Post".
  iFrame "#∗". iPureIntro. split_and!; [done..|].
  exists []. split_and!; [done|done|done| |done..].
  split; [done|]. intros (?&?&?). done.
Qed.

Lemma enqueue_spsc_spec :
  enqueue_spsc_spec' wq.(enqueue) Producer SPSCInv.
Proof.
  intros ????????????.
  iIntros "#⊒V P" (Φ) "AU".
  iDestruct "P" as "(#QL & ◯e & _ & %SEEN_ENQ)".

  awp_apply (wq.(enqueue_spec) with "⊒V QL"); [done..|].
  iApply (aacc_aupd_commit with "AU"); [done|].
  iIntros (G es ds) "[%xs [QI >(●ed & %PERM & %PROD & %CONS & %MATCH & %EMP)]]".
  iCombine "●ed ◯e" gives %[<-%excl_auth_agree_L _].
  iDestruct (QueueInv_QueueConsistent with "QI") as "#>%QC".
  rewrite QueueInv_graph_master_acc. iDestruct "QI" as "[>Gm QI]".
  iDestruct (graph_master_consistent with "Gm") as %EGC.
  iSpecialize ("QI" with "[$Gm]").

  iAaccIntro with "QI".
  { iFrame. iIntros "QI !>". iSplitL "QI"; [|by auto].
    iNext. iExists _. iFrame "QI". done. }
  iIntros (V' G' enqId enq Venq M') "(QI & #⊒V' & #QL' & %F)".
  iDestruct (QueueInv_QueueConsistent with "QI") as "#>%QC'".
  rewrite /is_enqueue in F.
  destruct F as (SubGG' & SubMM' & ? & ? & -> & HenqId & EsG' & SoG' & ComG' & ? & ?).
  set (eV := mkGraphEvent (Enq v) Venq M') in *.
  specialize (Produced_mono _ G' _ SubGG' PROD) as PROD'.
  specialize (Consumed_mono _ G' _ SubGG' CONS) as CONS'.
  specialize (matches_stable _ G' _ _ SubGG' ComG' MATCH) as MATCH'.
  specialize (EmpDeqs_mono _ G' _ SubGG' EMP) as EMP'.

  rewrite QueueInv_graph_master_acc. iDestruct "QI" as "[>Gm QI]".
  iDestruct (graph_master_consistent with "Gm") as %EGC'.
  iSpecialize ("QI" with "[$Gm]").

  have PROD'' : Produced G' (es ++ [enqId]).
  { constructor.
    - intros ?? [Ei0|[-> <-]]%lookup_app_1.
      + destruct PROD'. apply (ENQS _ _ Ei0).
      + exists eV, v. rewrite EsG' HenqId. split; [by apply lookup_app_1_eq|done].
    - destruct PROD'.
      intros ????? [Ei1|[-> <-]]%lookup_app_1 [Ei2|[-> <-]]%lookup_app_1 ? ?.
      + by eapply (ENQ_SEQ i1 i2).
      + rewrite HenqId EsG' in EV2. apply lookup_last_Some_2 in EV2 as ->.
        subst eV. simpl.
        specialize (ENQS _ _ Ei1) as (eV1 & EV1 & _).
        rewrite ->Forall_lookup in SEEN_ENQ. specialize (SEEN_ENQ _ _ Ei1).
        set_solver +SEEN_ENQ SubMM'.
      + exfalso. apply lookup_lt_Some in Ei2. lia.
      + by apply (egcons_logview_event _ EGC' _ _ EV2). }

  have SEEN_ENQ' : Forall (λ e, e ∈ M') (es ++ [enqId]).
  { rewrite ->Forall_lookup in SEEN_ENQ |- *.
    intros ? e0 [Ei0|[-> <-]]%lookup_app_1; [|done].
    specialize (SEEN_ENQ _ _ Ei0). set_solver +SEEN_ENQ SubMM'. }

  iMod (QEes_update (es ++ [enqId]) with "●ed ◯e") as "[●ed ◯e]".

  iIntros "!>". iExists V',_,(es ++ [enqId]),_,_,_,_. iSplitL; [|by auto].
  iSplitR "◯e"; last iSplit; last iSplit; [|done| |done].
  { (* SPSCInv *)
    iNext. iExists _. iFrame. iPureIntro. split_and!; [|done|done| |done].
    - subst enqId. rewrite EsG' app_length /= seq_app /=.
      rewrite -(assoc app es) (comm app _ (ds ++ xs)).
      rewrite (assoc app es). by f_equiv.
    - intros i' d'. specialize (MATCH' i' d'). split.
      + intros (e' & Ei' & Com')%MATCH'. exists e'.
        split; [|done]. eapply prefix_lookup_Some; [done|by eexists].
      + intros (e' & [Ei'|[-> <-]]%lookup_app_1 & Com').
        { apply MATCH'. by exists e'. }
        exfalso. rewrite ComG' -(bsq_cons_so_com _ QC) in Com'.
        specialize (egcons_so _ EGC _ _ Com') as (eV' & _ & HeV' & _).
        subst enqId. by apply lookup_length_not_Some in HeV'. }
  (* Producer *)
  iFrame "QL' ◯e". done.
Qed.

Lemma dequeue_spsc_spec :
  dequeue_spsc_spec' wq.(dequeue) Consumer SPSCInv.
Proof.
  intros ???????????.
  iIntros "#⊒V C" (Φ) "AU".
  iDestruct "C" as "(#QL & ◯d & _ & %SEEN_DEQ)".

  awp_apply (wq.(dequeue_spec) with "⊒V QL"); [done..|].
  iApply (aacc_aupd_commit with "AU"); [done|].
  iIntros (G es ds) "[%xs [QI >(●ed & %PERM & %PROD & %CONS & %MATCH & %EMP)]]".
  iCombine "●ed ◯d" gives %[_ <-%excl_auth_agree_L].
  iDestruct (QueueInv_QueueConsistent with "QI") as "#>%QC".
  have [NODUPes [NODUPds NODUPxs]] : NoDup es ∧ NoDup ds ∧ NoDup xs.
  { symmetry in PERM. move: PERM => /ord_nodup.
    move=> /NoDup_app [?][_] /NoDup_app [?][_]? //. }

  iAaccIntro with "QI".
  { iFrame. iIntros "QI !>". iSplitL "QI"; [|by auto].
    iNext. iExists _. iFrame "QI". done. }
  iIntros (v V' G' enqId deqId enq deq Vdeq M') "(QI & #⊒V' & #QL' & %F)".
  set (dV := mkGraphEvent deq Vdeq M') in *.
  iDestruct (QueueInv_QueueConsistent with "QI") as "#>%QC'".
  destruct F as (SubGG' & SubMM' & ? & ? & CASE).
  specialize (Produced_mono _ G' _ SubGG' PROD) as PROD'.
  specialize (Consumed_mono _ G' _ SubGG' CONS) as CONS'.
  specialize (EmpDeqs_mono _ G' _ SubGG' EMP) as EMP'.
  rewrite QueueInv_graph_master_acc. iDestruct "QI" as "[>Gm QI]".
  iDestruct (graph_master_consistent with "Gm") as %EGC'.
  iSpecialize ("QI" with "[$Gm]").

  have HdV : Es G' !! deqId = Some dV.
  { destruct_or! CASE; destruct_and! CASE; subst deqId;
      match goal with H : Es G' = _ |- _ => rewrite H end; apply lookup_app_1_eq. }
  have SEEN_DEQ' : Forall (λ e, e ∈ M') ds.
  { rewrite ->Forall_lookup in SEEN_DEQ |- *.
    intros ? d0 Di0. specialize (SEEN_DEQ _ _ Di0). set_solver +SEEN_DEQ SubMM'. }

  destruct CASE as [CASE|CASE].
  { destruct CASE as (-> & -> & ? & EsG' & ? & ComG' & ? & ?).
    iIntros "!>". iExists _,V',_,ds,dummy_eid,_,dummy_qevt,_. iExists _,_.
    iSplitL; [|by auto]. iSplitR "◯d"; last iSplit; last iSplit; [|done| | ].
    { (* SPSCInv *)
      iNext. iExists (xs ++ [deqId]). iFrame.
      iPureIntro. split_and!; [|done|done| | ].
      - subst deqId. rewrite EsG' app_length /= seq_app /=.
        rewrite (assoc app ds) (assoc app es). by f_equiv.
      - apply (matches_stable _ G' _ _ SubGG' ComG' MATCH).
      - constructor. intros ?? [Xi0|[-> <-]]%lookup_app_1.
        + destruct EMP'. apply (EMPS _ _ Xi0).
        + by eexists. }
    { (* Consumer *) iFrame "∗#". iPureIntro. done. }
    iPureIntro. do 5 (split; [done|]). left. split_and!; [done..|].
    (* I must've dequeued all enqueues that I have seen. *)
    intros ?? Ei' SEEN.
    destruct PROD'. specialize (ENQS _ _ Ei') as (eV' & v' & HeV' & Henq').
    specialize (bsq_cons_non_empty _ QC' _ _ HdV ltac:(done) _ _ _ HeV' ltac:(done) SEEN) as (deqId' & Com' & _).
    exists deqId'. apply (MATCH i' deqId').
    exists enqId'. split; [done|]. rewrite -ComG' //. }

  rewrite /is_enqueue /is_dequeue in CASE.
  destruct CASE as (? & -> & -> & HdeqId & ? & EsG' & SoG' & ComG' & ? & ? & ? & eV & HeV & ? & ?).
  have Com_imi : (enqId, deqId) ∈ com G' by set_solver +ComG'.
  have LTall : Forall (λ e, e < length (Es G)) (seq 0 (length (Es G))).
  { apply Forall_seq. lia. }

  (* find the matching enqueue in [es] ([im]-th) *)
  have [im Eim] : ∃ im, es !! im = Some enqId.
  { apply lookup_lt_Some in HeV as LTenqId.
    move: (lookup_xo _ _ LTenqId) => /(elem_of_list_lookup_2 _ _ _).
    rewrite PERM => /elem_of_app [|/elem_of_app [|]] /(elem_of_list_lookup_1 _ _) [im Eim].
    - by exists im.
    - destruct CONS. specialize (DEQS _ _ Eim) as (?&?&?&?). congruence.
    - destruct EMP. specialize (EMPS _ _ Eim) as (?&?&?). congruence. }

  (* the matching enqueue is not matched with earlier dequeue *)
  have LEiim : i ≤ im.
  { apply not_gt => GTiim. case Eqi: i => [|i']; [lia|].
    have [d_im Dim] : is_Some (ds !! im).
    { apply lookup_lt_is_Some. lia. }
    have ? : d_im ≠ deqId.
    { suff ? : d_im < deqId by lia.
      have ? : d_im ∈ seq 0 (length (Es G)).
      { rewrite PERM. apply elem_of_app. right. apply elem_of_app. left.
        by eapply elem_of_list_lookup_2. }
      rewrite ->Forall_forall in LTall. subst deqId. by apply LTall. }
    (* matches ⇒ (enqId, d_im). Contradicts [bsq_cons_com_functional] *)
    have Com_imim : (enqId, d_im) ∈ com G'.
    { move: Dim=> /(MATCH im d_im) [?]. rewrite Eim.
      intros [[= ->] Com]. set_solver +ComG' Com. }
    specialize (bsq_cons_com_functional _ QC') as [FUNC _].
    specialize (FUNC _ _ Com_imi Com_imim eq_refl). done. }

  have [e_i Ei] : is_Some (es !! i).
  { apply lookup_lt_Some in Eim. apply lookup_lt_is_Some. lia. }

  (* i-th dequeue matches exactly i-th enqueue *)
  have {LEiim}? : im = i.
  { (* suppose i < im *)
    suff ? : ¬ i < im by lia. clear LEiim. intros LTiim.

    (* info about i-th enqueue *)
    have [e_iV He_iV] : is_Some (Es G' !! e_i).
    { apply lookup_lt_is_Some.
      have ? : e_i ∈ seq 0 (length (Es G)).
      { rewrite PERM. apply elem_of_app. left. by eapply elem_of_list_lookup_2. }
      rewrite ->Forall_forall in LTall. trans (length (Es G)).
      - by apply LTall.
      - rewrite EsG' app_length /=. lia. }
    have [v_e_i ENQ_e_i] : ∃ v_e_i, e_iV.(ge_event) = Enq v_e_i.
    { destruct PROD'. specialize (ENQS _ _ Ei) as (?&?& He_iV' &?).
      rewrite He_iV in He_iV'. injection He_iV' as <-. by eexists. }
    case (decide (e_i = enqId)) as [->|NE].
    { destruct PROD. specialize (NoDup_lookup _ _ _ _ NODUPes Eim Ei). lia. }

    (* by FIFO, ∃ d_j,
           e_i -> e_im
          /      /
       d_j </- d_i *)
    refine (_ (bsq_cons_FIFO_b _ QC' e_i e_iV v_e_i enqId deqId eV ltac:(done) ltac:(done) ltac:(done) _ _)); cycle 1.
    { eapply prefix_lookup_Some; [done|by eexists]. }
    { (* (e_i, enqId) ∈ eco *) destruct PROD. by eapply (ENQ_SEQ i im). }
    intros (d_j & Com_ij & NOeco_ij).
    move: (gcons_com_included _ _ Com_ij) => /= [_] /lookup_lt_is_Some [d_jV Hd_jV].
    specialize (NOeco_ij _ Hd_jV NE).
    have [v_d_j DEQ_d_j] : ∃ v_d_j, d_jV.(ge_event) = Deq v_d_j.
    { specialize (bsq_cons_matches _ QC' _ _ Com_ij) as (?&?&?&?&?& Hd_jV' &?&?&?).
      rewrite Hd_jV in Hd_jV'. injection Hd_jV' as <-. by eexists. }
    have {}Hd_jV : Es G !! d_j = Some d_jV.
    { rewrite EsG' in Hd_jV. apply lookup_app_1 in Hd_jV as [|[-> <-]]; [done|].
      exfalso. by specialize (egcons_logview_event _ EGC' _ _ HdV). }
    have [j Dj] : ∃ j, ds !! j = Some d_j.
    { apply lookup_lt_Some in Hd_jV as LTd_j.
      move: (lookup_xo _ _ LTd_j) => /(elem_of_list_lookup_2 _ _ _).
      rewrite PERM => /elem_of_app [|/elem_of_app [|]] /(elem_of_list_lookup_1 _ _) [j Dj].
      - destruct PROD. specialize (ENQS _ _ Dj) as (?&?&?&?). congruence.
      - by exists j.
      - destruct EMP. specialize (EMPS _ _ Dj) as (?&?&?). congruence. }

    (* ∃ e_j, es !! j = Some e_j ∧ (e_j, d_j) ∈ com ∵ matches *)
    move: (MATCH j d_j) => /iffLR /(_ Dj) [e_j][Ej Com_jj].

    have ? : j ≠ i.
    { suff ? : j < i by lia. subst i. by apply lookup_lt_Some in Dj. }

    (* (e_i, d_j), (e_j, d_j) ∈ com. Contradiction. *)
    specialize (bsq_cons_com_functional _ QC') as [_ FUNC].
    refine (_ (FUNC _ (e_j, d_j) Com_ij _)); cycle 1.
    { set_solver +Com_jj ComG'. }
    simpl. intros EQ_ix. specialize (EQ_ix eq_refl). rewrite EQ_ix in Ei.
    destruct PROD. specialize (NoDup_lookup _ _ _ _ NODUPes Ej Ei). lia. }

  subst im. rewrite Eim in Ei. injection Ei as <-. rename Eim into Ei.

  have CONS'' : Consumed G' (ds ++ [deqId]).
  { constructor.
    - intros ?? [Di0|[-> <-]]%lookup_app_1.
      + destruct CONS'. apply (DEQS _ _ Di0).
      + eexists _,v. rewrite EsG'. subst deqId dV i.
        split; [apply lookup_app_1_eq|done].
    - destruct CONS'.
      intros ????? [Ei1|[-> <-]]%lookup_app_1 [Ei2|[-> <-]]%lookup_app_1 ? ?.
      + by eapply (DEQ_SEQ i1 i2).
      + rewrite HdeqId EsG' in EV2. apply lookup_last_Some_2 in EV2 as ->.
        subst dV. simpl.
        specialize (DEQS _ _ Ei1) as (eV1 & EV1 & _).
        rewrite ->Forall_lookup in SEEN_DEQ. specialize (SEEN_DEQ _ _ Ei1).
        set_solver +SEEN_DEQ SubMM'.
      + exfalso. apply lookup_lt_Some in Ei2. lia.
      + by apply (egcons_logview_event _ EGC' _ _ EV2). }

  have SEEN_DEQ'' : Forall (λ e, e ∈ M') (ds ++ [deqId]).
  { rewrite ->Forall_lookup in SEEN_DEQ' |- *.
    intros ? d0 [Di0|[-> <-]]%lookup_app_1; [|done].
    apply (SEEN_DEQ' _ _ Di0). }

  iMod (QEds_update (ds ++ [deqId]) with "●ed ◯d") as "[●ed ◯d]".
  iIntros "!>". iExists _,V',_,(ds ++ [deqId]),_,_,_,_. iExists _,_. iSplitL; [|by auto].
  iSplitR "◯d"; last iSplit; last iSplit; [|done| |].
  { (* SPSCInv *)
    iNext. iExists _. iFrame. iPureIntro. split_and!; [|done|done| |done].
    - subst deqId. rewrite EsG' app_length /= seq_app /=.
      rewrite -(assoc app ds) -(comm app xs).
      rewrite (assoc app ds) (assoc app es). by f_equiv.
    - intros i' d'. specialize (MATCH i' d'). split.
      + intros [(e'&?&Com)%MATCH|[-> <-]]%lookup_app_1.
        * exists e'. split; [done|]. set_solver +ComG' Com.
        * exists enqId. split; [done|]. set_solver +ComG'.
      + rewrite ComG'. intros (e' & Ei' & [[= -> ->]%elem_of_singleton|Com]%elem_of_union).
        * specialize (NoDup_lookup _ _ _ _ NODUPes Ei' Ei) as ->.
          apply lookup_app_1_eq.
        * destruct MATCH as [_ MATCH]. specialize (MATCH ltac:(by exists e')).
          eapply prefix_lookup_Some; [done|by eexists]. }
  { (* Consumer *) iFrame "QL' ◯d". done. }
  iPureIntro. do 5 (split; [done|]). right. split_and!; [done..|]. by exists eV.
Qed.
End proof.

Definition weak_queue_spsc_spec
  Σ `{!noprolG Σ,
      !inG Σ (graphR qevent),
      !inG Σ (prodR (excl_authR (leibnizO (list event_id)))
                    (excl_authR (leibnizO (list event_id))))}
  (wq : weak_queue_spec Σ)
  : spsc_spec Σ WeakQueueConsistent := {|
    spsc_core_spec := wq;

    spec_spsc.SPSCInv_Timeless := SPSCInv_Timeless wq;
    spec_spsc.SPSCInv_Objective := SPSCInv_Objective wq;
    spec_spsc.SPSCInv_matches := SPSCInv_matches wq;
    spec_spsc.SPSCInv_QueueInv_acc := SPSCInv_QueueInv_acc wq;

    spec_spsc.Producer_exclusive := Producer_exclusive wq ;
    spec_spsc.Producer_QueueLocal := Producer_QueueLocal wq ;
    spec_spsc.Producer_Produced := Producer_Produced wq ;
    spec_spsc.Producer_agree := Producer_agree wq ;

    spec_spsc.Consumer_exclusive := Consumer_exclusive wq ;
    spec_spsc.Consumer_QueueLocal := Consumer_QueueLocal wq ;
    spec_spsc.Consumer_Consumed := Consumer_Consumed wq ;
    spec_spsc.Consumer_agree := Consumer_agree wq ;

    spec_spsc.new_queue_spsc_spec := new_queue_spsc_spec wq;
    spec_spsc.enqueue_spsc_spec := enqueue_spsc_spec wq;
    spec_spsc.dequeue_spsc_spec := dequeue_spsc_spec wq;
  |}%I.
