From gpfsl.examples Require Import sflib.

From stdpp Require Import namespaces.

From gpfsl.logic Require Import logatom.

From gpfsl.examples.queue Require Export event.
From gpfsl.examples.omo Require Export omo omo_preds append_only_loc.

Require Import iris.prelude.options.

Local Open Scope Z_scope.

Definition queue_state := list (event_id * Z * view * eView).

Local Notation history := (history qevent).
Implicit Types (E : history) (qu : queue_state).

(* Build queue state with the events in the given order *)
Inductive queue_step : ∀ (e : event_id) (eV : omo_event qevent) qu qu', Prop :=
  | queue_step_Enq u uV v qu
      (ENQ : uV.(type) = Enq v)
      (NZ : 0 < v)
      (LVIEW : u ∈ uV.(eview))
      : queue_step u uV qu (qu ++ [(u, v, uV.(sync), uV.(eview))])
  | queue_step_Deq u o oV v V lV qu
      (DEQ : oV.(type) = Deq v)
      (NZ : 0 < v)
      (SYNC : V ⊑ oV.(sync))
      (LVIEW : {[o; u]} ∪ lV ⊆ oV.(eview))
      : queue_step o oV ((u, v, V, lV) :: qu) qu
  | queue_step_EmpDeq o oV
      (EMPDEQ : oV.(type) = EmpDeq)
      (LVIEW : o ∈ oV.(eview))
      : queue_step o oV [] []
  .

Global Instance queue_interpretable : Interpretable qevent queue_state :=
  {
    init := [];
    step := queue_step
  }.

Local Notation EMPTY := 0 (only parsing).
Local Notation FAIL_RACE := (-1) (only parsing).

Definition QueueLocalT Σ : Type :=
  ∀ (N : namespace) (γg : gname) (q : loc) (E : history) (M : eView), vProp Σ.
Definition QueueInvT Σ : Type :=
  ∀ (γg : gname) (q : loc) (E : history), vProp Σ.

Definition new_queue_spec' {Σ} `{!noprolG Σ}
  (new_queue : val) (QueueLocal : QueueLocalT Σ) (QueueInv : QueueInvT Σ) : Prop :=
  ∀ N tid,
  {{{ True }}}
    new_queue [] @ tid; ⊤
  {{{ γg (q: loc) V V' E Menq Mdeq, RET #q;
       ⊒V' ∗ @{V'} QueueLocal N γg q E Mdeq ∗ QueueInv γg q E ∗
      ⌜ E = [mkOmoEvent (Enq 1) V Menq; mkOmoEvent (Deq 1) V' Mdeq] ∧
        V ⊑ V' ⌝}}}.

Definition enqueue_spec' {Σ} `{!noprolG Σ}
  (enqueue : val) (QueueLocal : QueueLocalT Σ) (QueueInv : QueueInvT Σ) : Prop :=
  ∀ N (DISJ: N ## histN) (q: loc) tid γg E1 M (V : view) (v : Z) (Posx: 0 < v),
  (* PRIVATE PRE *)
  (* E1 is a snapshot of the history, locally observed by M *)
  ⊒V -∗ QueueLocal N γg q E1 M -∗
  (* PUBLIC PRE *)
  <<< ∀ E, ▷ QueueInv γg q E >>>
    enqueue [ #q ; #v] @ tid; ↑N
  <<< ∃ V' E' M',
      (* PUBLIC POST *)
      ▷ QueueInv γg q E' ∗
      ⊒V' ∗ @{V'} QueueLocal N γg q E' M' ∗
      ⌜ V ⊑ V' ∧
        E' = E ++ [mkOmoEvent (Enq v) V' M'] ∧ M ⊆ M' ⌝,
      RET #☠, emp >>>
  .

Definition dequeue_spec' {Σ} `{!noprolG Σ}
  (dequeue : val) (QueueLocal : QueueLocalT Σ) (QueueInv : QueueInvT Σ) : Prop :=
  ∀ N (DISJ: N ## histN) (q: loc) tid γg E1 M V,
  (* PRIVATE PRE *)
  ⊒V -∗ QueueLocal N γg q E1 M -∗
  (* PUBLIC PRE *)
  <<< ∀ E, ▷ QueueInv γg q E >>>
    dequeue [ #q] @ tid; ↑N
  <<< ∃ (v: Z) V' E' deq M',
      (* PUBLIC POST *)
      ▷ QueueInv γg q E' ∗
      ⊒V' ∗ @{V'} QueueLocal N γg q E' M' ∗
      ⌜ V ⊑ V' ∧
        E' = E ++ [mkOmoEvent deq V' M'] ∧ M ⊆ M' ∧
        if decide (v = 0) then deq = EmpDeq (* EMPTY case *)
        else 0 < v ∧ is_dequeue deq v (* successful case *) ⌝,
      RET #v, emp >>>
  .

Definition try_enq_spec' {Σ} `{!noprolG Σ}
  (try_enq : val) (QueueLocal : QueueLocalT Σ) (QueueInv : QueueInvT Σ) : Prop :=
  ∀ N (DISJ: N ## histN) (q: loc) tid γg E1 M (V : view) (v : Z) (Posx: 0 < v),
  (* PRIVATE PRE *)
  (* E1 is a snapshot of the history, locally observed by M *)
  ⊒V -∗ QueueLocal N γg q E1 M -∗
  (* PUBLIC PRE *)
  <<< ∀ E, ▷ QueueInv γg q E >>>
    try_enq [ #q ; #v] @ tid; ↑N
  <<< ∃ (b: bool) V' E' M',
      (* PUBLIC POST *)
      ▷ QueueInv γg q E' ∗
      ⊒V' ∗ @{V'} QueueLocal N γg q E' M' ∗
      ⌜ if b then (
          (* successful case *)
          V ⊑ V' ∧
          E' = E ++ [mkOmoEvent (Enq v) V' M'] ∧ M ⊆ M'
        ) else (
          (* FAIL_RACE case *)
          E' = E ∧ M' = M
        ) ⌝,
      RET #b, emp >>>
  .

Definition try_deq_spec' {Σ} `{!noprolG Σ}
  (try_deq : val) (QueueLocal : QueueLocalT Σ) (QueueInv : QueueInvT Σ) : Prop :=
  ∀ N (DISJ: N ## histN) (q: loc) tid γg E1 M V,
  (* PRIVATE PRE *)
  ⊒V -∗ QueueLocal N γg q E1 M -∗
  (* PUBLIC PRE *)
  <<< ∀ E, ▷ QueueInv γg q E >>>
    try_deq [ #q] @ tid; ↑N
  <<< ∃ (v: Z) V' E' deq M',
      (* PUBLIC POST *)
      ▷ QueueInv γg q E' ∗
      ⊒V' ∗ @{V'} QueueLocal N γg q E' M' ∗
      ⌜ V ⊑ V' ∧
        if decide (v = FAIL_RACE) then (
          (* FAIL_RACE case *)
          E' = E ∧ M' = M
        ) else (
          E' = E ++ [mkOmoEvent deq V' M'] ∧ M ⊆ M' ∧
          if decide (v = EMPTY) then deq = EmpDeq (* EMPTY case *)
          else 0 < v ∧ is_dequeue deq v (* successful case *)
        ) ⌝,
      RET #v , emp >>>
  .

Record queue_spec {Σ} `{!noprolG Σ} := QueueSpec {
  (** operations *)
  new_queue : val;
  try_enq : val;
  enqueue : val;
  try_deq : val;
  dequeue : val;

  (** predicates *)
  QueueLocal : QueueLocalT Σ;
  QueueInv : QueueInvT Σ;

  (** predicates properties *)
  QueueInv_Objective : ∀ γg s E, Objective (QueueInv γg s E);
  QueueInv_Timeless : ∀ γg s E, Timeless (QueueInv γg s E);
  QueueInv_Linearizable : ∀ γg s E, QueueInv γg s E ⊢ ⌜ Linearizability E ⌝;
  QueueInv_history_wf :
    ∀ γg s E, QueueInv γg s E ⊢ ⌜ history_wf E ⌝;

  QueueInv_QueueLocal :
    ∀ N γg q E E' M',
      QueueInv γg q E -∗ QueueLocal N γg q E' M' -∗ ⌜ E' ⊑ E ⌝;
  QueueLocal_lookup :
    ∀ N γg q E M e V,
      sync <$> E !! e = Some V → e ∈ M → QueueLocal N γg q E M -∗ ⊒V;
  QueueLocal_Persistent :
    ∀ N γg q E M, Persistent (QueueLocal N γg q E M);

  (* operations specs *)
  new_queue_spec : new_queue_spec' new_queue QueueLocal QueueInv;
  try_enq_spec : try_enq_spec' try_enq QueueLocal QueueInv;
  enqueue_spec : enqueue_spec' enqueue QueueLocal QueueInv;
  try_deq_spec : try_deq_spec' try_deq QueueLocal QueueInv;
  dequeue_spec : dequeue_spec' dequeue QueueLocal QueueInv;
}.

Arguments queue_spec _ {_}.
Global Existing Instances QueueInv_Objective QueueInv_Timeless QueueLocal_Persistent.
