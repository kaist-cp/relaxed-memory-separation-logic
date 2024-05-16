From stdpp Require Import namespaces.

From gpfsl.logic Require Import logatom.
From gpfsl.examples.queue Require Export event spec_abs_graph.

Require Import iris.prelude.options.

Local Open Scope Z_scope.

Implicit Type (Q : queue) (N : namespace).

(** * Abstract State Specs, similar to Cosmo style. *)
(** Queue predicates *)
Definition isQueueT Σ : Type := namespace → gname → loc → vProp Σ.
Definition QueueT Σ : Type := gname → loc → queue → vProp Σ.

(** Operation specs *)
Definition new_queue_spec' {Σ} `{!noprolG Σ}
  (new_queue : val) (isQueue : isQueueT Σ) (Queue : QueueT Σ) : Prop :=
  ∀ N tid,
  {{{ True }}}
    new_queue [] @ tid; ⊤
  {{{ γq (q: loc), RET #q; isQueue N γq q ∗ Queue γq q [] }}}.

Definition enqueue_spec' {Σ} `{!noprolG Σ}
  (enqueue : val) (isQueue : isQueueT Σ) (Queue : QueueT Σ) : Prop :=
  ∀ N (DISJ: N ## histN) (q : loc) tid γq (V : view) (v : Z) (Posx: 0 < v),
  (* PRIVATE PRE *)
  ⊒V -∗ isQueue N γq q -∗
  (* PUBLIC PRE *)
  <<< ∀ Q, ▷ Queue γq q Q >>>
    enqueue [ #q ; #v] @ tid; ↑N
  <<< ∃ V' Q',
      (* PUBLIC POST *)
      ▷ Queue γq q Q' ∗
      ⊒V' ∗
      ⌜ V ⊑ V' ∧ Q' = Q ++ [(v, V')] ⌝,
      (* RETURN VALUE AT COMMITTING POINT *)
      RET #☠, emp >>>
  .

Definition dequeue_spec' {Σ} `{!noprolG Σ}
  (dequeue : val) (isQueue : isQueueT Σ) (Queue : QueueT Σ) : Prop :=
  ∀ N (DISJ: N ## histN) (q : loc) tid γq V,
  (* PRIVATE PRE *)
  ⊒V -∗ isQueue N γq q -∗
  (* PUBLIC PRE *)
  <<< ∀ Q, ▷ Queue γq q Q >>>
    dequeue [ #q] @ tid; ↑N
  <<< ∃ (v: Z) V' Q',
      (* PUBLIC POST *)
      ▷ Queue γq q Q' ∗
      ⊒V' ∗
      ⌜ ( (* EMPTY case *)
          ( Q' = Q ∧ v = 0 )
        ∨ (* successful case *)
          ( Q = (v, V') :: Q' ∧ 0 < v ) ) ⌝,
      (* RETURN VALUE AT COMMITTING POINT *)
      RET #v, emp >>>
  .


Definition try_enq_spec' {Σ} `{!noprolG Σ}
  (try_enq : val) (isQueue : isQueueT Σ) (Queue : QueueT Σ) : Prop :=
  ∀ N (DISJ: N ## histN) (q : loc) tid γq (V : view) (v : Z) (Posx: 0 < v),
  (* PRIVATE PRE *)
  ⊒V -∗ isQueue N γq q -∗
  (* PUBLIC PRE *)
  <<< ∀ Q, ▷ Queue γq q Q >>>
    try_enq [ #q ; #v] @ tid; ↑N
  <<< ∃ (b: bool) V' Q',
      (* PUBLIC POST *)
      ▷ (Queue γq q Q') ∗
      ⊒V' ∗
      ⌜ V ⊑ V' ∧
          if b is false then
            Q' = Q
          else
            Q' = Q ++ [(v, V')] ⌝,
      (* RETURN VALUE AT COMMITTING POINT *)
      RET #b, emp >>>
  .

Definition try_deq_spec' {Σ} `{!noprolG Σ}
  (try_deq : val) (isQueue : isQueueT Σ) (Queue : QueueT Σ) : Prop :=
  ∀ N (DISJ: N ## histN) (q : loc) tid γq V,
  (* PRIVATE PRE *)
  ⊒V -∗ isQueue N γq q -∗
  <<< (* PUBLIC PRE *)
      ∀ Q, ▷ (Queue γq q Q) >>>
    try_deq [ #q] @ tid; ↑N
  <<< ∃ (v: Z) V' Q',
      (* PUBLIC POST *)
      ▷ (Queue γq q Q') ∗
      ⊒V' ∗
      ⌜ (* FAIL case *)
        ( ( Q' = Q ∧ v < 0 )
        ∨ (* EMPTY case *)
          ( Q' = Q ∧ v = 0 )
        ∨ (* successful case *)
          ( Q = (v, V') :: Q' ∧ 0 < v ) ) ⌝,
      (* RETURN VALUE AT COMMITTING POINT *)
      RET #v, emp >>>
  .

Record queue_spec {Σ} `{!noprolG Σ} := QueueSpec {
  (* operations *)
  new_queue : val;
  enqueue : val;
  dequeue : val;
  try_enq : val;
  try_deq : val;

  (* predicates *)
  isQueue : isQueueT Σ;
  Queue : QueueT Σ;

  (** predicates properties *)
  Queue_Timeless : ∀ γq q Q, Timeless (Queue γq q Q);
  Queue_Objective : ∀ γq q Q, Objective (Queue γq q Q);
  isQueue_Persistent :
    ∀ N γq q, Persistent (isQueue N γq q);

  (* operations specs *)
  new_queue_spec : new_queue_spec' new_queue isQueue Queue;
  enqueue_spec : enqueue_spec' enqueue isQueue Queue;
  dequeue_spec : dequeue_spec' dequeue isQueue Queue;
  try_enq_spec : try_enq_spec' try_enq isQueue Queue;
  try_deq_spec : try_deq_spec' try_deq isQueue Queue;
}.

Arguments queue_spec _ {_}.
