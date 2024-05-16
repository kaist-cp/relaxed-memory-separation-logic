From stdpp Require Import namespaces.

From gpfsl.logic Require Import logatom.
From gpfsl.examples.graph Require Export spec.
From gpfsl.examples.queue Require Export event spec_graph.

Require Import iris.prelude.options.

Local Open Scope Z_scope.

Local Notation graph := (graph qevent).
Implicit Type (Q : queue) (G : graph) (M : logView).

(** * Hybrid Specs with both Abstract State and Partial Orders (Event Graph) *)
(** Queue predicate with abstract state *)
Definition QueueInvT Σ : Type :=
  gname → loc → queue → graph → vProp Σ.

(** Operation specs *)
Definition new_queue_spec' {Σ} `{!noprolG Σ, !inG Σ (graphR qevent)}
  (new_queue : val) (QueueLocal : QueueLocalT Σ) (QueueInv : QueueInvT Σ) : Prop :=
  ∀ N tid,
  {{{ True }}}
    new_queue [] @ tid; ⊤
  {{{ γg (q: loc), RET #q; QueueLocal N γg q ∅ ∅ ∗ QueueInv γg q [] ∅ }}}.

Definition enqueue_spec' {Σ} `{!noprolG Σ, !inG Σ (graphR qevent)}
  (enqueue : val) (QueueLocal : QueueLocalT Σ) (QueueInv : QueueInvT Σ) : Prop :=
  ∀ N (DISJ: N ## histN) (q : loc) tid γg G1 M (V : view) (v : Z) (Posx: 0 < v),
  (* PRIVATE PRE *)
  ⊒V -∗ QueueLocal N γg q G1 M -∗ (* G1 is a snapshot of the graph, locally observed by M *)
  (* PUBLIC PRE *)
  <<< ∀ Q G, ▷ QueueInv γg q Q G >>>
    enqueue [ #q ; #v] @ tid; ↑N
  <<< ∃ V' Q' G' (enqId : event_id) enq Venq M',
      (* PUBLIC POST *)
      ▷ QueueInv γg q Q' G' ∗
      ⊒V' ∗ @{V'} QueueLocal N γg q G' M' ∗
      ⌜ G ⊑ G' ∧ M ⊑ M' ∧
        V ⊑ Venq.(dv_in) ∧ Venq.(dv_wrt) = V' ∧
        Q' = Q ++ [(v, Venq.(dv_comm))] ∧
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
  <<< ∀ Q G, ▷ QueueInv γg q Q G >>>
    dequeue [ #q] @ tid; ↑N
  <<< ∃ (v: Z) V' Q' G' enqId deqId enq deq Venq Vdeq M',
      (* PUBLIC POST *)
      ▷ QueueInv γg q Q' G' ∗
      ⊒V' ∗ @{V'} QueueLocal N γg q G' M' ∗
      ⌜ G ⊑ G' ∧ M ⊑ M' ∧
        V ⊑ Vdeq.(dv_in) ∧ Vdeq.(dv_comm) = V' ∧
        ( (* EMPTY case *)
          ( Q' = Q ∧
            v = 0 ∧ deq = EmpDeq ∧
            deqId = length G.(Es) ∧
            G'.(Es) = G.(Es) ++ [mkGraphEvent deq Vdeq M'] ∧
            G'.(so) = G.(so) ∧ G'.(com) = G.(com) ∧
            {[deqId]} ∪ M ⊆ M' ∧ deqId ∉ M)
        ∨ (* successful case *)
          (Q = (v, Venq.(dv_comm)) :: Q' ∧
          0 < v ∧ is_enqueue enq v ∧ is_dequeue deq v ∧
          deqId = length G.(Es) ∧
          (∀ id, (enqId, id) ∉ G.(so)) ∧
          G'.(Es) = G.(Es) ++ [mkGraphEvent deq Vdeq M'] ∧
          G'.(so) = {[(enqId, deqId)]} ∪ G.(so) ∧
          G'.(com) = {[(enqId, deqId)]} ∪ G.(com) ∧
          enqId ∈ M' ∧ deqId ∈ M' ∧ deqId ∉ M ∧
          ∃ eV, G.(Es) !! enqId = Some eV ∧ eV.(ge_event) = enq ∧
                eV.(ge_view) = Venq ∧ eV.(ge_lview) ⊆ M') ) ⌝,
      (* RETURN VALUE AT COMMITTING POINT *)
      RET #v, emp >>>
  .


Definition try_enq_spec' {Σ} `{!noprolG Σ, !inG Σ (graphR qevent)}
  (try_enq : val) (QueueLocal : QueueLocalT Σ) (QueueInv : QueueInvT Σ) : Prop :=
  ∀ N (DISJ: N ## histN) (q : loc) tid γg G1 M (V : view) (v : Z) (Posx: 0 < v),
  (* PRIVATE PRE *)
  ⊒V -∗ QueueLocal N γg q G1 M -∗
  (* PUBLIC PRE *)
  <<< ∀ Q G, ▷ QueueInv γg q Q G >>>
    try_enq [ #q ; #v] @ tid; ↑N
  <<< ∃ (b: bool) V' Q' G' (enqId : event_id) enq Venq M',
      (* PUBLIC POST *)
      ▷ (QueueInv γg q Q' G') ∗
      ⊒V' ∗ @{V'} QueueLocal N γg q G' M' ∗
      ⌜ G ⊑ G' ∧ M ⊑ M' ∧
        V ⊑ Venq.(dv_in) ∧ Venq.(dv_wrt) = V' ∧
          if b is false then
            Q' = Q ∧ G' = G
          else
            (* enq is a new enqueue event with which G' strictly extends G *)
            Q' = Q ++ [(v, Venq.(dv_comm))] ∧
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
      ∀ Q G, ▷ (QueueInv γg q Q G) >>>
    try_deq [ #q] @ tid; ↑N
  <<< ∃ (v: Z) V' Q' G' enqId deqId enq deq Venq Vdeq M',
      (* PUBLIC POST *)
      ▷ (QueueInv γg q Q' G') ∗
      ⊒V' ∗ @{V'} QueueLocal N γg q G' M' ∗
      ⌜ G ⊑ G' ∧ M ⊑ M' ∧
        V ⊑ Vdeq.(dv_in) ∧ Vdeq.(dv_comm) = V' ∧
          (* FAIL case *)
        ((Q' = Q ∧ v < 0 ∧ G' = G)
        ∨ (* EMPTY case *)
          ( Q' = Q ∧
            v = 0 ∧ deq = EmpDeq ∧
            deqId = length G.(Es) ∧
            G'.(Es) = G.(Es) ++ [mkGraphEvent deq Vdeq M'] ∧
            G'.(so) = G.(so) ∧ G'.(com) = G.(com) ∧
            {[deqId]} ∪ M ⊆ M' ∧ deqId ∉ M)
        ∨ (* successful case *)
          (Q = (v, Venq.(dv_comm)) :: Q' ∧
          0 < v ∧ is_enqueue enq v ∧ is_dequeue deq v ∧
          deqId = length G.(Es) ∧
          (∀ id, (enqId, id) ∉ G.(so)) ∧
          G'.(Es) = G.(Es) ++ [mkGraphEvent deq Vdeq M'] ∧
          G'.(so) = {[(enqId, deqId)]} ∪ G.(so) ∧
          G'.(com) = {[(enqId, deqId)]} ∪ G.(com) ∧
          enqId ∈ M' ∧ deqId ∈ M' ∧ deqId ∉ M ∧
          ∃ eV, G.(Es) !! enqId = Some eV ∧ eV.(ge_event) = enq ∧
                eV.(ge_view) = Venq ∧ eV.(ge_lview) ⊆ M') ) ⌝,
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
  QueueInv_Timeless : ∀ γg q Q G, Timeless (QueueInv γg q Q G);
  QueueInv_Objective : ∀ γg q Q G, Objective (QueueInv γg q Q G);
  QueueInv_QueueConsistent : ∀ γg q Q G, QueueInv γg q Q G ⊢ ⌜ QueueConsistent G ⌝;
  QueueInv_graph_master_acc :
    ∀ γg q Q G, QueueInv γg q Q G ⊢ graph_master γg (1/2) G ∗
                                (graph_master γg (1/2) G -∗ QueueInv γg q Q G);

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
Program Definition extended_strong_weak_queue_spec
  Σ `{!noprolG Σ, !inG Σ (graphR qevent)}
  (sq : strong_queue_spec Σ) : extended_queue_spec Σ WeakQueueConsistent :=
  {|
    extended_core_spec := {|
      QueueInv_Timeless         := sq.(QueueInv_Timeless);
      QueueInv_Objective        := sq.(QueueInv_Objective);
      QueueInv_graph_master_acc := sq.(QueueInv_graph_master_acc);
      QueueLocal_graph_snap     := sq.(QueueLocal_graph_snap) ;
      QueueLocal_Persistent     := sq.(QueueLocal_Persistent) ;
      new_queue_spec            := sq.(new_queue_spec) ;
      enqueue_spec              := sq.(enqueue_spec) ;
      dequeue_spec              := sq.(dequeue_spec);
    |} ;
    try_enq_spec                := sq.(try_enq_spec) ;
    try_deq_spec                := sq.(try_deq_spec) ;
  |}.
Next Obligation.
  iIntros "* QI".
  by iDestruct (sq.(QueueInv_QueueConsistent) with "QI") as %SC%strq_wkq_cons.
Qed.

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
