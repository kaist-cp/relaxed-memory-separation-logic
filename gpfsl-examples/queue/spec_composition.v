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
  ∀ (N : namespace) (γg : gname) (q : loc) (M : eView), vProp Σ.
Definition QueueInvT Σ : Type :=
  ∀ (γg γs : gname) (q : loc) (E : history) (omo : omoT) (stlist : list queue_state), vProp Σ.

Definition new_queue_spec' {Σ} `{!noprolG Σ, !omoGeneralG Σ}
  (new_queue : val) (QueueLocal : QueueLocalT Σ) (QueueInv : QueueInvT Σ) : Prop :=
  ∀ N tid V,
  {{{ ⊒V }}}
    new_queue [] @ tid; ⊤
  {{{ γg γs (q: loc) V' V'' Menq Mdeq, RET #q;
      let eVenq := mkOmoEvent (Enq 1) V' Menq in
      let eVdeq := mkOmoEvent (Deq 1) V'' Mdeq in
      let E := [eVenq; eVdeq] in
      let omo := omo_append_w (omo_append_w [] 0%nat []) 1%nat [] in
      let stenq := [(0%nat, 1, V', Menq)] in
      let stdeq := [] in
      let stlist := [stenq; stdeq] in
      ⊒V'' ∗ QueueInv γg γs q E omo stlist ∗ @{V''} QueueLocal N γg q Mdeq ∗
      OmoTokenW γg 0%nat ∗ OmoTokenW γg 1%nat ∗
      ⌜ V ⊑ V' ∧ V' ⊑ V'' ⌝}}}.

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
      ⌜ V ⊑ V' ∧ M ⊆ M' ⌝,
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
  <<< ∃ (v: Z) V' deq γs' omo' stlist' M',
      let eVdeq := mkOmoEvent deq V' M' in
      let E' := E ++ [eVdeq] in
      (* PUBLIC POST *)
      ⊒V' ∗ ▷ QueueInv γg γs' q E' omo' stlist' ∗ @{V'} QueueLocal N γg q M' ∗ OmoUB γg M (length E) ∗
      ⌜ V ⊑ V' ∧ M ⊑ M' ⌝ ∗
      if decide (v = 0) then ( (* EMPTY case *)
        ⌜ deq = EmpDeq ∧ γs' = γs ∧ (∃ gen, omo' = omo_insert_r omo gen (length E)) ∧ stlist' = stlist ⌝ ∗
        OmoTokenR γg (length E)
      ) else ( (* successful case *)
        ⌜ 0 < v ∧ deq = Deq v ∧ (∃ gen, omo' = omo_insert_w omo gen (length E) []) ⌝ ∗ OmoTokenW γg (length E)
      ),
      RET #v, emp >>>
  .

Definition try_enq_spec' {Σ} `{!noprolG Σ, !omoGeneralG Σ}
  (try_enq : val) (QueueLocal : QueueLocalT Σ) (QueueInv : QueueInvT Σ) : Prop :=
  ∀ N (DISJ: N ## histN) (q: loc) tid γg M (V : view) (v : Z) (Posx: 0 < v),
  (* PRIVATE PRE *)
  ⊒V -∗ QueueLocal N γg q M -∗
  (* PUBLIC PRE *)
  <<< ∀ γs E omo stlist, ▷ QueueInv γg γs q E omo stlist >>>
    try_enq [ #q ; #v] @ tid; ↑N
  <<< ∃ (b: bool) V' E' omo' stlist' M',
      (* PUBLIC POST *)
      ⊒V' ∗ ▷ QueueInv γg γs q E' omo' stlist' ∗ @{V'} QueueLocal N γg q M' ∗
      if b then ( (* successful case *)
        ⌜ E' = E ++ [mkOmoEvent (Enq v) V' M'] ∧ omo' = omo_append_w omo (length E) []
        ∧ (∃ st, stlist' = stlist ++ [st])
        ∧ V ⊑ V' ∧ M ⊆ M' ⌝ ∗
        OmoTokenW γg (length E) ∗ OmoUB γg M (length E)
      ) else ( (* FAIL_RACE case *)
        ⌜ E' = E ∧ omo' = omo ∧ stlist' = stlist ∧ M' = M ⌝
      ),
      RET #b, emp >>>
  .

Definition try_deq_spec' {Σ} `{!noprolG Σ, !omoGeneralG Σ}
  (try_deq : val) (QueueLocal : QueueLocalT Σ) (QueueInv : QueueInvT Σ) : Prop :=
  ∀ N (DISJ: N ## histN) (q: loc) tid γg M V,
  (* PRIVATE PRE *)
  ⊒V -∗ QueueLocal N γg q M -∗
  (* PUBLIC PRE *)
  <<< ∀ γs E omo stlist, ▷ QueueInv γg γs q E omo stlist >>>
    try_deq [ #q] @ tid; ↑N
  <<< ∃ (v: Z) V' deq γs' E' omo' stlist' M',
      (* PUBLIC POST *)
      ⊒V' ∗ ▷ QueueInv γg γs' q E' omo' stlist' ∗ @{V'} QueueLocal N γg q M' ∗
      if decide (v = FAIL_RACE) then ( (* FAIL_RACE case *)
        ⌜ γs' = γs ∧ E' = E ∧ omo' = omo ∧ stlist' = stlist ∧ M' = M ⌝
      ) else (
        ⌜ E' = E ++ [mkOmoEvent deq V' M']
        ∧ V ⊑ V' ∧ M ⊆ M' ⌝ ∗
        OmoUB γg M (length E) ∗
        if decide (v = EMPTY) then ( (* EMPTY case *)
          ⌜ deq = EmpDeq ∧ γs' = γs ∧ (∃ gen, omo' = omo_insert_r omo gen (length E)) ∧ stlist' = stlist ⌝ ∗
          OmoTokenR γg (length E)
        ) else ( (* successful case *)
          ⌜ 0 < v ∧ deq = Deq v ∧ (∃ gen, omo' = omo_insert_w omo gen (length E) []) ⌝ ∗
          OmoTokenW γg (length E)
        )
      ),
      RET #v , emp >>>
  .

Record queue_spec {Σ} `{!noprolG Σ, !omoGeneralG Σ, !omoSpecificG Σ qevent queue_state} := QueueSpec {
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
  QueueInv_Objective : ∀ γg γs q E omo stlist, Objective (QueueInv γg γs q E omo stlist);
  QueueInv_Timeless : ∀ γg γs q E omo stlist, Timeless (QueueInv γg γs q E omo stlist);
  QueueInv_Linearizable : ∀ γg γs q E omo stlist, QueueInv γg γs q E omo stlist ⊢ ⌜ Linearizability_omo E omo stlist ⌝;
  QueueInv_OmoAuth_acc : ∀ γg γs q E omo stlist,
    QueueInv γg γs q E omo stlist ⊢ OmoAuth γg γs (1/2)%Qp E omo stlist _ ∗ (OmoAuth γg γs (1/2)%Qp E omo stlist _ -∗ QueueInv γg γs q E omo stlist);
  QueueLocal_OmoEview : ∀ N γg q M, QueueLocal N γg q M ⊢ OmoEview γg M;
  QueueLocal_Persistent : ∀ N γg q M, Persistent (QueueLocal N γg q M);

  (* operations specs *)
  new_queue_spec : new_queue_spec' new_queue QueueLocal QueueInv;
  try_enq_spec : try_enq_spec' try_enq QueueLocal QueueInv;
  enqueue_spec : enqueue_spec' enqueue QueueLocal QueueInv;
  try_deq_spec : try_deq_spec' try_deq QueueLocal QueueInv;
  dequeue_spec : dequeue_spec' dequeue QueueLocal QueueInv;
}.

Arguments queue_spec _ {_ _ _}.
Global Existing Instances QueueInv_Objective QueueInv_Timeless QueueLocal_Persistent.
