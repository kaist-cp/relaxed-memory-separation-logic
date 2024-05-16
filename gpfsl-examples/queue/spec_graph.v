From stdpp Require Import namespaces.

From gpfsl.logic Require Import logatom.
From gpfsl.examples Require Export set_helper.
From gpfsl.examples.graph Require Export spec.
From gpfsl.examples.queue Require Export event.

Require Import iris.prelude.options.

Local Open Scope Z_scope.

Local Notation graph := (graph qevent).
Implicit Type (G : graph) (M : logView).

(** * Specs using Event Graphs *)

Definition unmatched_enq G eid : Prop :=
  (∃ v : Z, ge_event <$> (G.(Es) !! eid) = Some (Enq v)) ∧
    (∀ id, (eid, id) ∉ G.(so)).

Definition unmatched_enq_2 G eid : Prop :=
  (∃ v : Z, ge_event <$> (G.(Es) !! eid) = Some (Enq v)) ∧
  set_Forall (λ id', (eid, id') ∉ G.(so)) (to_set G.(Es)).

Global Instance umatched_enq_dec G eid : Decision (unmatched_enq_2 G eid).
Proof.
  apply and_dec; last apply _.
  case (G.(Es) !! eid) as [[e V]|].
  - destruct e; [left | right | right]; eauto; intros []; discriminate.
  - right. intros []; discriminate.
Qed.

(** Queue predicates *)
Definition QueueLocalT Σ : Type :=
  namespace → gname → loc → graph → logView → vProp Σ.
Definition QueueInvT Σ : Type :=
  gname → loc → graph → vProp Σ.


(** Operation specs *)
Definition new_queue_spec' {Σ} `{!noprolG Σ, !inG Σ (graphR qevent)}
  (new_queue : val) (QueueLocal : QueueLocalT Σ) (QueueInv : QueueInvT Σ) : Prop :=
  ∀ N tid,
  {{{ True }}}
    new_queue [] @ tid; ⊤
  {{{ γg (q: loc), RET #q; QueueLocal N γg q ∅ ∅ ∗ QueueInv γg q ∅ }}}.

Definition enqueue_spec' {Σ} `{!noprolG Σ, !inG Σ (graphR qevent)}
  (enqueue : val) (QueueLocal : QueueLocalT Σ) (QueueInv : QueueInvT Σ) : Prop :=
  ∀ N (DISJ: N ## histN) (q : loc) tid γg G1 M (V : view) (v : Z) (Posx: 0 < v),
  (* PRIVATE PRE *)
  ⊒V -∗ QueueLocal N γg q G1 M -∗ (* G1 is a snapshot of the graph, locally observed by M *)
  (* PUBLIC PRE *)
  <<< ∀ G, ▷ QueueInv γg q G >>>
    enqueue [ #q ; #v] @ tid; ↑N
  <<< ∃ V' G' (enqId : event_id) enq Venq M',
      (* PUBLIC POST *)
      ▷ QueueInv γg q G' ∗
      ⊒V' ∗ @{V'} QueueLocal N γg q G' M' ∗
      ⌜ G ⊑ G' ∧ M ⊑ M' ∧
        V ⊑ Venq.(dv_in) ∧ Venq.(dv_wrt) = V' ∧
        (* enq is a new enqueue event with which G' strictly extends G *)
        is_enqueue enq v ∧
        enqId = length G.(Es) ∧
        G'.(Es) = G.(Es) ++ [mkGraphEvent enq Venq M'] ∧
        G'.(so) = G.(so) ∧ G'.(com) = G.(com) ∧
        enqId ∈ M' (* << M' may also acquire more events that
          come with the Enqueue (acquired by reading the Head pointer). *) ∧
        enqId ∉ M ⌝,
      (* RETURN VALUE AT COMMITTING POINT *)
      RET #☠, emp >>>
  .

Definition dequeue_spec' {Σ} `{!noprolG Σ, !inG Σ (graphR qevent)}
  (dequeue : val) (QueueLocal : QueueLocalT Σ) (QueueInv : QueueInvT Σ) : Prop :=
  ∀ N (DISJ: N ## histN) (q : loc) tid γg G1 M V,
  (* PRIVATE PRE *)
  ⊒V -∗ QueueLocal N γg q G1 M -∗
  (* PUBLIC PRE *)
  <<< ∀ G, ▷ QueueInv γg q G >>>
    dequeue [ #q] @ tid; ↑N
  <<< ∃ (v: Z) V' G' enqId deqId enq deq Vdeq M',
      (* PUBLIC POST *)
      ▷ QueueInv γg q G' ∗
      ⊒V' ∗ @{V'} QueueLocal N γg q G' M' ∗
      ⌜ G ⊑ G' ∧ M ⊑ M' ∧
        V ⊑ Vdeq.(dv_in) ∧ Vdeq.(dv_comm) = V' ∧
        ( (* EMPTY case *)
          (v = 0 ∧ deq = EmpDeq ∧
            deqId = length G.(Es) ∧
            G'.(Es) = G.(Es) ++ [mkGraphEvent deq Vdeq M'] ∧
            G'.(so) = G.(so) ∧ G'.(com) = G.(com) ∧
            {[deqId]} ∪ M ⊆ M' ∧ deqId ∉ M)
        ∨ (* successful case *)
          (0 < v ∧ is_enqueue enq v ∧ is_dequeue deq v ∧
          deqId = length G.(Es) ∧
          (∀ id, (enqId, id) ∉ G.(so)) ∧
          G'.(Es) = G.(Es) ++ [mkGraphEvent deq Vdeq M'] ∧
          G'.(so) = {[(enqId, deqId)]} ∪ G.(so) ∧
          G'.(com) = {[(enqId, deqId)]} ∪ G.(com) ∧
          enqId ∈ M' ∧ deqId ∈ M' ∧ deqId ∉ M ∧
          ∃ eV, G.(Es) !! enqId = Some eV ∧ eV.(ge_event) = enq ∧ eV.(ge_lview) ⊆ M') ) ⌝,
      (* RETURN VALUE AT COMMITTING POINT *)
      RET #v, emp >>>
  .


Definition try_enq_spec' {Σ} `{!noprolG Σ, !inG Σ (graphR qevent)}
  (try_enq : val) (QueueLocal : QueueLocalT Σ) (QueueInv : QueueInvT Σ) : Prop :=
  ∀ N (DISJ: N ## histN) (q : loc) tid γg G1 M (V : view) (v : Z) (Posx: 0 < v),
  (* PRIVATE PRE *)
  ⊒V -∗ QueueLocal N γg q G1 M -∗
  (* PUBLIC PRE *)
  <<< ∀ G, ▷ QueueInv γg q G >>>
    try_enq [ #q ; #v] @ tid; ↑N
  <<< ∃ (b: bool) V' G' (enqId : event_id) enq Venq M',
      (* PUBLIC POST *)
      ▷ (QueueInv γg q G') ∗
      ⊒V' ∗ @{V'} QueueLocal N γg q G' M' ∗
      ⌜ G ⊑ G' ∧ M ⊑ M' ∧
        V ⊑ Venq.(dv_in) ∧ Venq.(dv_wrt) = V' ∧
          if b is false then
            G' = G
          else
            (* enq is a new enqueue event with which G' strictly extends G *)
            is_enqueue enq v ∧
            enqId = length G.(Es) ∧
            G'.(Es) = G.(Es) ++ [mkGraphEvent enq Venq M'] ∧
            G'.(so) = G.(so) ∧ G'.(com) = G.(com) ∧
            enqId ∈ M' ∧ enqId ∉ M ⌝,
      (* RETURN VALUE AT COMMITTING POINT *)
      RET #b, emp >>>
  .

Definition try_deq_spec' {Σ} `{!noprolG Σ, !inG Σ (graphR qevent)}
  (try_deq : val) (QueueLocal : QueueLocalT Σ) (QueueInv : QueueInvT Σ) : Prop :=
  ∀ N (DISJ: N ## histN) (q : loc) tid γg G1 M V,
  (* PRIVATE PRE *)
  ⊒V -∗ QueueLocal N γg q G1 M -∗
  <<< (* PUBLIC PRE *)
      ∀ G, ▷ (QueueInv γg q G) >>>
    try_deq [ #q] @ tid; ↑N
  <<< ∃ (v: Z) V' G' enqId deqId enq deq Vdeq M',
      (* PUBLIC POST *)
      ▷ (QueueInv γg q G') ∗
      ⊒V' ∗ @{V'} QueueLocal N γg q G' M' ∗
      ⌜ G ⊑ G' ∧ M ⊑ M' ∧
        V ⊑ Vdeq.(dv_in) ∧ Vdeq.(dv_comm) = V' ∧
          (* FAIL case *)
        ((v < 0 ∧ G' = G)
        ∨ (* EMPTY case *)
          (v = 0 ∧ deq = EmpDeq ∧
            deqId = length G.(Es) ∧
            G'.(Es) = G.(Es) ++ [mkGraphEvent deq Vdeq M'] ∧
            G'.(so) = G.(so) ∧ G'.(com) = G.(com) ∧
            {[deqId]} ∪ M ⊆ M' ∧ deqId ∉ M)
        ∨ (* successful case *)
          (0 < v ∧ is_enqueue enq v ∧ is_dequeue deq v ∧
          deqId = length G.(Es) ∧
          (∀ id, (enqId, id) ∉ G.(so)) ∧
          G'.(Es) = G.(Es) ++ [mkGraphEvent deq Vdeq M'] ∧
          G'.(so) = {[(enqId, deqId)]} ∪ G.(so) ∧
          G'.(com) = {[(enqId, deqId)]} ∪ G.(com) ∧
          enqId ∈ M' ∧ deqId ∈ M' ∧ deqId ∉ M ∧
          ∃ eV, G.(Es) !! enqId = Some eV ∧ eV.(ge_event) = enq ∧ eV.(ge_lview) ⊆ M') ) ⌝,
      (* RETURN VALUE AT COMMITTING POINT *)
      RET #v, emp >>>
  .

(** Bundling of specs *)
Record core_queue_spec {Σ} `{!noprolG Σ, !inG Σ (graphR qevent)}
  {QueueConsistent : graph → Prop} := QueueSpec {
  (* operations *)
  new_queue : val;
  enqueue : val;
  dequeue : val;
  (* predicates *)
  QueueLocal : QueueLocalT Σ;
  QueueInv : QueueInvT Σ;
  (** predicates properties *)
  QueueInv_Timeless : ∀ γg q G, Timeless (QueueInv γg q G);
  QueueInv_Objective : ∀ γg q G, Objective (QueueInv γg q G);
  QueueInv_QueueConsistent : ∀ γg q G, QueueInv γg q G ⊢ ⌜ QueueConsistent G ⌝;
  QueueInv_graph_master_acc :
    ∀ γg q G, QueueInv γg q G ⊢ graph_master γg (1/2) G ∗
                                (graph_master γg (1/2) G -∗ QueueInv γg q G);

  QueueLocal_graph_snap :
    ∀ N γg q G M, QueueLocal N γg q G M ⊢ graph_snap γg G M;
  QueueLocal_Persistent :
    ∀ N γg q G M, Persistent (QueueLocal N γg q G M);

  (* operations specs *)
  new_queue_spec : new_queue_spec' new_queue QueueLocal QueueInv;
  enqueue_spec : enqueue_spec' enqueue QueueLocal QueueInv;
  dequeue_spec : dequeue_spec' dequeue QueueLocal QueueInv;
}.

Arguments core_queue_spec _ {_ _} _.

Record extended_queue_spec {Σ} `{!noprolG Σ, !inG Σ (graphR qevent)}
  {QueueConsistent : graph → Prop} := ExtendedQueueSpec {
  extended_core_spec :> core_queue_spec Σ QueueConsistent ;
  (* extra operations *)
  try_enq : val;
  try_deq : val;
  (* operations specs *)
  try_enq_spec :
    try_enq_spec' try_enq extended_core_spec.(QueueLocal) extended_core_spec.(QueueInv);
  try_deq_spec :
    try_deq_spec' try_deq extended_core_spec.(QueueLocal) extended_core_spec.(QueueInv);
}.
Arguments extended_queue_spec _ {_ _} _.

(* only enqueue positive values *)
Definition queue_positive_value G : Prop :=
  ∀ e eV (v: Z), G.(Es) !! e = Some eV → eV.(ge_event) = Enq v → 0 < v.

(** (2) com relates matching enqueue and dequeue events *)
Definition queue_matches_value G : Prop :=
  ∀ e d, (e, d) ∈ G.(com) → (e < d)%nat ∧
    ∃ eV dV (v : Z), G.(Es) !! e = Some eV ∧ G.(Es) !! d = Some dV ∧
      eV.(ge_event) = Enq v ∧ dV.(ge_event) = Deq v ∧
      (* so is synchronizing at commit points *)
      eV.(ge_view).(dv_comm) ⊑ dV.(ge_view).(dv_comm).

(** (4) every unmatched dequeue returns empty *)
Definition queue_unmatched_deq_empty G : Prop :=
  ∀ e eV, G.(Es) !! e = Some eV →
    is_maybe_dequeue eV.(ge_event) →
    e ∉ (elements G.(com)).*2 →
    eV.(ge_event) = EmpDeq.

(** (5) a dequeue with a previous unmatched enqueue cannot return empty. *)
Definition queue_empty_unmatched_enq G : Prop :=
  ∀ d dV, G.(Es) !! d = Some dV → dV.(ge_event) = EmpDeq →
    ∀ e, e ∈ dV.(ge_lview) → ¬ unmatched_enq G e.
(* A stronger version *)
Definition queue_empty_unmatched_enq_strong G : Prop :=
  ∀ d dV, G.(Es) !! d = Some dV → dV.(ge_event) = EmpDeq →
    ∀ e v eV, G.(Es) !! e = Some eV → eV.(ge_event) = Enq v →
      e ∈ dV.(ge_lview) → ∃ de, (e, de) ∈ G.(com) ∧ de ∈ dV.(ge_lview).

(* This encodes enough properties for xo so that we can show xo
  to be the total (linearization) order similar to that of Yacovet's (7ii).
  This task can be done in the linearizability step.

  This is a strong property. We can also weaken it to just require (e1,e2) ∈ hb,
  instead of (e1,e2) ∈ xo.
  See more weakenings below.

  On the other hand, we can also strengthen it further by changing the
  conclusion from [(d1,d2) ∈ xo] to [(d1,d2) ∈ eco]. *)
Definition queue_FIFO_strong G : Prop :=
  ∀ e1 v1 eV1 e2 d2,
    G.(Es) !! e1 = Some eV1 → eV1.(ge_event) = Enq v1 →
    (e2, d2) ∈ G.(com) → (* if e2 is already dequeued *)
    (e1 ≤ e2)%nat → (* and e1 is before e2 in xo--- (e1,e2) ∈ xo *)
    (* then e1 must also have been dequeued with d1, which,
    by [queue_matches_value], should also come before d2 in xo. *)
    ∃ d1, (d1 ≤ d2)%nat ∧ (e1, d1) ∈ G.(com). (* (d1, d2) ∈ xo ∧ (e1, d1) ∈ com *)

(* A weakening that is not so weak *)
Definition queue_FIFO G : Prop :=
  ∀ e1 eV1 v1 e2 d2 eV2,
    G.(Es) !! e1 = Some eV1 → eV1.(ge_event) = Enq v1 →
    (e2, d2) ∈ G.(com) →  (* (e2, d2) ∈ com *)
    G.(Es) !! e2 = Some eV2 →
    e1 ∈ eV2.(ge_lview) → (* (e1,e2) ∈ eco *)
    ∃ d1, (e1,d1) ∈ G.(com) ∧ (* (e1, d1) ∈ com *)
    ∀ dV1, G.(Es) !! d1 = Some dV1 →
    e1 ≠ e2 → d2 ∉ dV1.(ge_lview) (* (d2, d1) ∉ eco *)
  .

(* Alternatively, if e2 as an enqueue that has been dequeued but also observed
  an enqueue e1, then e1 must also have been dequeued.
  This encodes the Yacovet's condition [com^-1; lhb; com; lhb is irreflexive]. *)
Definition queue_FIFO_weak G :=
  ∀ e1 d1 dV1 e2 d2 eV2,
    (e1, d1) ∈ G.(com) → (e2, d2) ∈ G.(com) →
    e1 ≠ e2 → (* e1 and e2 are distinct *)
    G.(Es) !! d1 = Some dV1 → G.(Es) !! e2 = Some eV2 →
    e1 ∈ eV2.(ge_lview) → (* (e1, e2) ∈ eco *)
    d2 ∉ dV1.(ge_lview)   (* (d2,d1) ∉ eco *)
  .

(** * Basic Queue Consistency *)
Record BasicQueueConsistent G : Prop := mkBasicQueueConsistent {
  bsq_cons_enq_non_zero : (* 0 is used for Empty Dequeue *)
    queue_positive_value G ;
  (* (1)-(7) Weak queue spec from POPL'19 Library Correctness paper *)
    (* (1) at most 1 Constructor event: we currently don't have initialization events *)
  bsq_cons_matches :
    (* (2) There can only be so edges between matching enqueues and dequeues *)
    queue_matches_value G ;
  bsq_cons_com_functional :
    (* (3) com and com^-1 are functional: *)
    functional_pair G.(com) ;
  bsq_cons_unmatched_dequeue_empty :
    (* (4) every unmatched dequeue returns empty  *)
      queue_unmatched_deq_empty G ;
  bsq_cons_non_empty :
    (* (5) a dequeue with a previous unmatched enqueue cannot return empty.
    But we can prove a stronger property: *)
    queue_empty_unmatched_enq_strong G ;
  bsq_cons_so_com :
    (* (6) so and com agree *)
    G.(so) = G.(com) ;
  bsq_cons_FIFO_a :
    (* xo must agree with logview-inclusion. *)
    graph_xo_eco G.(Es) ;
  bsq_cons_FIFO_b :
    (* (7b) "If we know that e1 happens before e2, then it is impossible that d2
            happens before d1."
      Here, e1 happens-before e2 would mean that e2 has seen e1, i.e.
      (e1,e2) ∈ eco ∧ e1 ≠ e2. *)
    queue_FIFO G ;
}.

(** * Weak Consistency *)
Record WeakQueueConsistent G : Prop := mkWeakQueueConsistent {
  wkq_cons_write : (* all non-empty events are writes *)
    graph_event_is_writing G.(Es) (.≠ EmpDeq) ;
  wkq_cons_enqueue_release : (* enqueue is releasing *)
    graph_event_is_releasing G.(Es) (λ eg, ∃ v, eg = Enq v) ;
  wkq_cons_dequeue_acquire : (* dequeue is acquiring *)
    graph_event_is_acquiring G.(Es) (λ eg, ∃ v, eg = Deq v) ;

  wkq_bsq_cons :> BasicQueueConsistent G;
}.

(** * Strong Consistency *)
Record StrongQueueConsistent G : Prop := mkStrongQueueConsistent {
  strq_cons_relacq : (* the message view is the same as the commiter's view *)
    graph_event_is_relacq G.(Es) (λ _, True) ;

  strq_wkq_cons :> WeakQueueConsistent G ;

  strq_cons_FIFO_b :
  (* (7b) stronger FIFO *)
    queue_FIFO_strong G ;
}.

(** A Strong queue spec, with 5 operations with Strong Consistency *)
Definition strong_queue_spec Σ `{!noprolG Σ, !inG Σ (graphR qevent)}
  := extended_queue_spec Σ StrongQueueConsistent.

(** A Weak queue spec, with 3 operations and Weak Consistency *)
Definition weak_queue_spec Σ `{!noprolG Σ, !inG Σ (graphR qevent)}
  := core_queue_spec Σ WeakQueueConsistent.

(** Basic queue spec, with 3 operations and Basic Consistency *)
Definition basic_queue_spec Σ `{!noprolG Σ, !inG Σ (graphR qevent)}
  := core_queue_spec Σ BasicQueueConsistent.

(** Strong implies Weak *)
Program Definition strong_weak_queue_spec
  Σ `{!noprolG Σ, !inG Σ (graphR qevent)}
  (sq : strong_queue_spec Σ) : weak_queue_spec Σ :=
  {|
    QueueInv_Timeless         := sq.(QueueInv_Timeless);
    QueueInv_Objective        := sq.(QueueInv_Objective);
    QueueInv_graph_master_acc := sq.(QueueInv_graph_master_acc);
    QueueLocal_graph_snap     := sq.(QueueLocal_graph_snap) ;
    QueueLocal_Persistent     := sq.(QueueLocal_Persistent) ;
    new_queue_spec            := sq.(new_queue_spec) ;
    enqueue_spec              := sq.(enqueue_spec) ;
    dequeue_spec              := sq.(dequeue_spec) ;
  |}.
Next Obligation.
  iIntros "* QI".
  by iDestruct (sq.(QueueInv_QueueConsistent) with "QI") as %SC%strq_wkq_cons.
Qed.

(** Weak implies Basic *)
Program Definition weak_basic_queue_spec
  Σ `{!noprolG Σ, !inG Σ (graphR qevent)}
  (wq : weak_queue_spec Σ) : basic_queue_spec Σ :=
  {|
    QueueInv_Timeless         := wq.(QueueInv_Timeless);
    QueueInv_Objective        := wq.(QueueInv_Objective);
    QueueInv_graph_master_acc := wq.(QueueInv_graph_master_acc);
    QueueLocal_graph_snap     := wq.(QueueLocal_graph_snap) ;
    QueueLocal_Persistent     := wq.(QueueLocal_Persistent) ;
    new_queue_spec            := wq.(new_queue_spec) ;
    enqueue_spec              := wq.(enqueue_spec) ;
    dequeue_spec              := wq.(dequeue_spec) ;
  |}.
Next Obligation.
  iIntros "* QI".
  by iDestruct (wq.(QueueInv_QueueConsistent) with "QI") as %SC%wkq_bsq_cons.
Qed.

(** Some properties *)
Lemma BasicQueueConsistent_empty : BasicQueueConsistent ∅.
Proof. done. Qed.

Lemma WeakQueueConsistent_empty : WeakQueueConsistent ∅.
Proof. constructor; [done..|apply BasicQueueConsistent_empty]. Qed.

Lemma StrongQueueConsistent_empty : StrongQueueConsistent ∅.
Proof. constructor; [done|apply WeakQueueConsistent_empty|done]. Qed.

Lemma BasicQueueConsistent_queue_empty_unmatched_enq G
    (EGC : eventgraph_consistent G) :
  BasicQueueConsistent G → queue_empty_unmatched_enq G.
Proof.
  intros QC d dV HdV Emp ? In UE.
  specialize (egcons_logview_closed _ EGC _ _ HdV _ In) as [eV HeV].
  destruct UE as [[v Henq] UNMATCHED].
  rewrite HeV in Henq. injection Henq as Henq.
  rewrite (bsq_cons_so_com _ QC) in UNMATCHED.
  specialize (bsq_cons_non_empty _ QC _ _ HdV Emp _ _ _ HeV Henq In) as [? [MATCH _]].
  apply (UNMATCHED _ MATCH).
Qed.

Lemma queue_FIFO_strong_FIFO G :
  graph_xo_eco G.(Es) → functional_pair G.(com) →
  queue_FIFO_strong G → queue_FIFO G.
Proof.
  intros EC FP F e1 eV1 v1 e2 d2 eV2 Eqe1 Eqv1 InCo Eqe2 Ine2.
  specialize (F _ _ _ _ _ Eqe1 Eqv1 InCo (EC _ _ _ Eqe2 Ine2))
    as (d1 & Le12 & InCo1).
  exists d1. split; [done|].
  intros dV1 Eqd1 NEq Ind1. apply NEq.
  assert (d2 = d1) as ->.
  { apply (anti_symm le); [|done]. apply (EC _ _ _ Eqd1 Ind1). }
  destruct FP as [_ F2]. by apply (F2 _ _ InCo1 InCo eq_refl).
Qed.

Lemma BasicQueueConsistent_FIFO_weak G :
  BasicQueueConsistent G → queue_FIFO_weak G.
Proof.
  destruct 1 as [_ CON2 [CON3a CON3b] CON4 CON5 CON6 CON7a CON7b].
  intros e1 d1 dV1 e2 d2 eV2 InG1 InG2 NEq Eqd1 Eq2 Ine1 Ind2.
  destruct (CON2 _ _ InG1) as [Lt1 (eV1 & dV1' & v1 & Eqe1 & Eqd1' & Eqv1 & ?)].
  rewrite Eqd1 in Eqd1'; inversion Eqd1'; clear Eqd1'; subst dV1'.
  specialize (CON7b _ _ _ _ _ _ Eqe1 Eqv1 InG2 Eq2 Ine1) as (d1' & Ind1' & CASE).
  assert (Eqd := CON3a _ _ InG1 Ind1' eq_refl). simpl in Eqd. subst d1'.
  destruct (CON2 _ _ InG2) as [Lt2 (eV2' & dV2 & v2 & Eqe2 & Eqd2 & ?)].
  rewrite Eq2 in Eqe2; inversion Eqe2; clear Eqe2; subst eV2'.
  assert (LE1 := CON7a _ _ _ Eq2 Ine1).
  assert (LE2 := CON7a _ _ _ Eqd1 Ind2).
  by apply (CASE _ Eqd1 NEq).
Qed.

Lemma unmatched_enq_mono G G' eid :
  G ⊑ G' → is_Some (G.(Es) !! eid) →
  unmatched_enq G' eid → unmatched_enq G eid.
Proof.
  intros LeG' [? Eq] [[v Eq'] FA].
  destruct (G'.(Es) !! eid) as [[? V]|] eqn:Eq''; [|done]. simpl in Eq'.
  rewrite (prefix_lookup_Some _ _ _ _ Eq) in Eq''; [|apply LeG']. simplify_eq.
  split.
  - exists v. by rewrite Eq.
  - intros e' ?. apply (FA e'); by apply LeG'.
Qed.
