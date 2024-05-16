From gpfsl.examples Require Import sflib.

From stdpp Require Import namespaces.

From gpfsl.logic Require Import logatom.

From gpfsl.examples.omo Require Export omo omo_preds append_only_loc.

Require Import iris.prelude.options.

Local Open Scope Z_scope.

Inductive qevent := Init | Enq (v : Z) | Deq (v : Z). (* No EmpDeq in Folly queue *)
Definition queue_state := list (event_id * Z * view * eView).
Global Instance qevent_inhabited : Inhabited qevent := populate Init.

Local Notation history := (history qevent).
Implicit Types (E : history) (qu : queue_state).

(* Build queue state with the events in the given order *)
Inductive queue_step : ∀ (e : event_id) (eV : omo_event qevent) qu qu', Prop :=
  | queue_step_Enq u uV v qu
      (ENQ : uV.(type) = Enq v)
      (NZ : 0 < v)
      (EVIEW : u ∈ uV.(eview))
      : queue_step u uV qu (qu ++ [(u, v, uV.(sync), uV.(eview))])
  | queue_step_Deq u o oV v V lV qu
      (DEQ : oV.(type) = Deq v)
      (NZ : 0 < v)
      (SYNC : V ⊑ oV.(sync))
      (EVIEW : {[o; u]} ∪ lV ⊆ oV.(eview))
      : queue_step o oV ((u, v, V, lV) :: qu) qu
  | queue_step_Init eV
      (INIT : eV.(type) = Init)
      (EVIEW : eV.(eview) = {[0%nat]})
      : queue_step 0%nat eV [] []
  .

Global Instance queue_interpretable : Interpretable qevent queue_state :=
  {
    init := [];
    step := queue_step
  }.

Definition QueueLocalT Σ : Type :=
  ∀ (N : namespace) (γg : gname) (q : loc) (M : eView), vProp Σ.
Definition QueueInvT Σ : Type :=
  ∀ (γg γs : gname) (q : loc) (E : history) (omo : omoT) (stlist : list queue_state), vProp Σ.

Definition new_queue_spec' {Σ} `{!noprolG Σ, !omoGeneralG Σ}
  (newQueue : val) (QueueLocal : QueueLocalT Σ) (QueueInv : QueueInvT Σ) : Prop :=
  ∀ N tid (sz : nat) V,
  (0 < sz)%nat →
  {{{ ⊒V }}}
    newQueue [ #sz] @ tid; ⊤
  {{{ γg γs (q: loc) V' M, RET #q;
      let eVinit := mkOmoEvent Init V' M in
      let E := [eVinit] in
      let omo := omo_append_w [] 0%nat [] in
      let st : queue_state := [] in
      ⊒V' ∗ QueueInv γg γs q E omo [st] ∗ @{V'} QueueLocal N γg q M ∗
      OmoTokenW γg 0%nat ∗
      ⌜ V ⊑ V' ⌝}}}.

Definition enqueue_spec' {Σ} `{!noprolG Σ, !omoGeneralG Σ}
  (enqueue : val) (QueueLocal : QueueLocalT Σ) (QueueInv : QueueInvT Σ) : Prop :=
  ∀ N (DISJ: N ## histN) (q: loc) tid γg M (V : view) (v : Z) (Posx: 0 < v),
  (* PRIVATE PRE *)
  ⊒V -∗ QueueLocal N γg q M -∗
  (* PUBLIC PRE *)
  <<< ∀ γs E omo stlist, ▷ QueueInv γg γs q E omo stlist >>>
    enqueue [ #q ; #v] @ tid; ↑N
  <<< ∃ V' st M',
      let eVenq := mkOmoEvent (Enq v) V' M' in
      let E' := E ++ [eVenq] in
      let omo' := omo_append_w omo (length E) [] in
      (* PUBLIC POST *)
      ⊒V' ∗ ▷ QueueInv γg γs q E' omo' (stlist ++ [st]) ∗ @{V'} QueueLocal N γg q M' ∗
      OmoTokenW γg (length E) ∗ OmoUB γg M (length E) ∗
      ⌜ V ⊑ V' ∧ M ⊑ M' ⌝,
      RET #☠, emp >>>
  .

Definition dequeue_spec' {Σ} `{!noprolG Σ, !omoGeneralG Σ}
  (dequeue : val) (QueueLocal : QueueLocalT Σ) (QueueInv : QueueInvT Σ) : Prop :=
  ∀ N (DISJ: N ## histN) (q: loc) tid γg M V,
  (* PRIVATE PRE *)
  ⊒V -∗ QueueLocal N γg q M -∗
  (* PUBLIC PRE *)
  <<< ∀ γs E omo stlist, ▷ QueueInv γg γs q E omo stlist >>>
    dequeue [ #q] @ tid; ↑N
  <<< ∃ (v: Z) V' st M',
      let eVdeq := mkOmoEvent (Deq v) V' M' in
      let E' := E ++ [eVdeq] in
      let omo' := omo_append_w omo (length E) [] in
      (* PUBLIC POST *)
      ⊒V' ∗ ▷ QueueInv γg γs q E' omo' (stlist ++ [st]) ∗ @{V'} QueueLocal N γg q M' ∗
      OmoTokenW γg (length E) ∗ OmoUB γg M (length E) ∗
      ⌜ V ⊑ V' ∧ M ⊆ M' ∧ 0 < v ⌝,
      RET #v, emp >>>
  .

Record mpmcqueue_spec {Σ} `{!noprolG Σ, !omoGeneralG Σ, !omoSpecificG Σ qevent queue_state} := MpmcQueueSpec {
  (** operations *)
  newQueue : val;
  enqueue : val;
  dequeue : val;

  (** predicates *)
  QueueLocal : QueueLocalT Σ;
  QueueInv : QueueInvT Σ;

  (** predicates properties *)
  QueueInv_Objective : ∀ γg γs q E omo stlist, Objective (QueueInv γg γs q E omo stlist);
  QueueInv_Timeless : ∀ γg γs q E omo stlist, Timeless (QueueInv γg γs q E omo stlist);
  QueueInv_Linearizable : ∀ γg γs q E omo stlist, QueueInv γg γs q E omo stlist ⊢ ⌜ Linearizability_omo E omo stlist ⌝;
  QueueInv_OmoAuth_acc : ∀ γg γs q E omo stlist,
    QueueInv γg γs q E omo stlist ⊢ OmoAuth γg γs (1/2)%Qp E omo stlist _ ∗ (OmoAuth γg γs (1/2)%Qp E omo stlist _ -∗ QueueInv γg γs q E omo stlist);
  QueueLocal_OmoEview : ∀ N γg l M, QueueLocal N γg l M ⊢ OmoEview γg M;
  QueueLocal_Persistent :
    ∀ N γg q M, Persistent (QueueLocal N γg q M);

  (* operations specs *)
  new_queue_spec : new_queue_spec' newQueue QueueLocal QueueInv;
  enqueue_spec : enqueue_spec' enqueue QueueLocal QueueInv;
  dequeue_spec : dequeue_spec' dequeue QueueLocal QueueInv;
}.

Arguments mpmcqueue_spec _ {_ _ _}.
Global Existing Instances QueueInv_Objective QueueInv_Timeless QueueLocal_Persistent.
