From gpfsl.examples Require Import sflib.

From stdpp Require Import namespaces.

From gpfsl.logic Require Import logatom.

From gpfsl.examples.omo Require Export omo omo_preds append_only_loc.

Require Import iris.prelude.options.

Local Open Scope Z_scope.

Inductive seq_event := Init | Enq (v : Z) (n : nat) | Deq (v : Z) (n : nat).
Definition seq_state := list (event_id * Z * nat * view * eView).
Global Instance seq_event_inhabited : Inhabited seq_event := populate Init.

Local Notation history := (history seq_event).
Local Notation empty := 0 (only parsing).
Implicit Types (E : history) (st : seq_state).

Inductive seq_step : ∀ (e : event_id) (eV : omo_event seq_event) st st', Prop :=
  | seq_step_Enq e eV v n
    (ENQ : eV.(type) = Enq v n)
    (GT : 0 < v)
    (EVIEW : e ∈ eV.(eview))
    : seq_step e eV [] [(e, v, n, eV.(sync), eV.(eview))]
  | seq_step_Deq e eV e' v n V lV
    (DEQ : eV.(type) = Deq v n)
    (GT : 0 < v)
    (SYNC : V ⊑ eV.(sync))
    (EVIEW : {[e; e']} ∪ lV ⊆ eV.(eview))
    : seq_step e eV [(e', v, n, V, lV)] []
  | seq_step_Init eV
    (INIT : eV.(type) = Init)
    (EVIEW : eV.(eview) = {[0%nat]})
    : seq_step 0%nat eV [] []
  .

Global Instance seq_interpretable : Interpretable seq_event seq_state :=
  {
    init := [];
    step := seq_step
  }.

Inductive seq_perm_type := EnqP | DeqP.
Global Instance seq_perm_type_inhabited : Inhabited seq_perm_type := populate EnqP.

Definition SeqLocalT Σ : Type :=
  ∀ (γg : gname) (q : loc) (M : eView), vProp Σ.
Definition SeqLocalNT Σ : Type :=
  ∀ (N : namespace), SeqLocalT Σ.
Definition SeqInvT Σ : Type :=
  ∀ (γg γs : gname) (q : loc) (E : history) (omo : omoT) (stlist : list seq_state), vProp Σ.
Definition SeqPermT Σ : Type :=
  ∀ (γg : gname) (q : loc) (ty : seq_perm_type) (P : nat → bool), vProp Σ.

Definition new_seq_spec' {Σ} `{!noprolG Σ, !omoGeneralG Σ}
  (newSEQ : val) (SeqLocal : SeqLocalNT Σ) (SeqInv : SeqInvT Σ) (SeqPerm : SeqPermT Σ) : Prop :=
  ∀ N tid V,
  {{{ ⊒V }}}
    newSEQ [] @ tid; ⊤
  {{{ γg γs (q: loc) M V', RET #q;
      let eVinit := mkOmoEvent Init V' M in
      let E := [eVinit] in
      let stinit : seq_state := [] in
      ⊒V' ∗ @{V'} SeqLocal N γg q M ∗ SeqInv γg γs q E (omo_append_w [] 0%nat []) [stinit] ∗
      OmoTokenW γg 0%nat ∗
      SeqPerm γg q EnqP (λ _, true) ∗ SeqPerm γg q DeqP (λ _, true) ∗
      ⌜ V ⊑ V' ⌝ }}}.

Definition enqueueWithTicket_spec' {Σ} `{!noprolG Σ, !omoGeneralG Σ}
  (enqueueWithTicket : val) (SeqLocal : SeqLocalNT Σ) (SeqInv : SeqInvT Σ) (SeqPerm : SeqPermT Σ) : Prop :=
  ∀ N (DISJ: N ## histN) (q: loc) tid γg γs M (V : view) (v : Z) (n : nat),
  (* PRIVATE PRE *)
  0 < v →
  ⊒V -∗ SeqLocal N γg q M -∗ SeqPerm γg q EnqP (λ m, m =? n)%nat -∗
  (* PUBLIC PRE *)
  <<< ∀ E omo stlist, ▷ SeqInv γg γs q E omo stlist >>>
    enqueueWithTicket [ #q; #n; #v] @ tid; ↑N
  <<< ∃ V' M',
      (* PUBLIC POST *)
      let eVenq := mkOmoEvent (Enq v n) V' M' in
      let E' := E ++ [eVenq] in
      let enqId := length E in
      let omo' := omo_append_w omo enqId [] in
      let st := [(enqId, v, n, eVenq.(sync), eVenq.(eview))] in
      ▷ SeqInv γg γs q E' omo' (stlist ++ [st]) ∗ OmoTokenW γg enqId ∗
      ⊒V' ∗ @{V'} SeqLocal N γg q M' ∗
      ⌜ V ⊑ V' ∧ M ⊆ M' ⌝,
      RET #☠, emp >>>
  .

Definition dequeueWithTicket_spec' {Σ} `{!noprolG Σ, !omoGeneralG Σ}
  (dequeueWithTicket : val) (SeqLocal : SeqLocalNT Σ) (SeqInv : SeqInvT Σ) (SeqPerm : SeqPermT Σ) : Prop :=
  ∀ N (DISJ: N ## histN) (q: loc) tid γg γs M (V : view) (n : nat),
  (* PRIVATE PRE *)
  ⊒V -∗ SeqLocal N γg q M -∗ SeqPerm γg q DeqP (λ m, m =? n)%nat -∗
  (* PUBLIC PRE *)
  <<< ∀ E omo stlist, ▷ SeqInv γg γs q E omo stlist >>>
    dequeueWithTicket [ #q; #n] @ tid; ↑N
  <<< ∃ V' M' (v : Z),
      (* PUBLIC POST *)
      let eVdeq := mkOmoEvent (Deq v n) V' M' in
      let E' := E ++ [eVdeq] in
      let deqId := length E in
      let omo' := omo_append_w omo deqId [] in
      let st : seq_state := [] in
      ▷ SeqInv γg γs q E' omo' (stlist ++ [st]) ∗ OmoTokenW γg deqId ∗
      ⊒V' ∗ @{V'} SeqLocal N γg q M' ∗
      ⌜ V ⊑ V' ∧ M ⊆ M' ∧ 0 < v⌝,
      RET #v, emp >>>
  .

Record seq_composition_spec {Σ} `{!noprolG Σ, !omoGeneralG Σ, !omoSpecificG Σ seq_event seq_state} := SeqCompositionSpec {
  (** operations *)
  newSEQ : val;
  enqueueWithTicket : val;
  dequeueWithTicket : val;

  (** These are common elements in arbitrary composable linearizability spec *)
  (** predicates *)
  SeqLocal : SeqLocalNT Σ;
  SeqInv : SeqInvT Σ;
  SeqPerm : SeqPermT Σ;

  (** predicates properties *)
  SeqInv_Objective : ∀ γg γs q E omo stlist, Objective (SeqInv γg γs q E omo stlist);
  SeqInv_Linearizable : ∀ γg γs q E omo stlist, SeqInv γg γs q E omo stlist ⊢ ⌜ Linearizability_omo E omo stlist ⌝;
  SeqInv_OmoAuth_acc : ∀ γg γs q E omo stlist,
    SeqInv γg γs q E omo stlist ⊢ ∃ qp, OmoAuth γg γs qp E omo stlist _ ∗ (OmoAuth γg γs qp E omo stlist _ -∗ SeqInv γg γs q E omo stlist);
  SeqLocal_OmoEview : ∀ N γg l M, SeqLocal N γg l M ⊢ OmoEview γg M;
  SeqLocal_Persistent :
    ∀ N γg q M, Persistent (SeqLocal N γg q M);

  SeqPerm_Objective : ∀ γg q ty P, Objective (SeqPerm γg q ty P);
  SeqPerm_Equiv : ∀ γg q ty P1 P2, (∀ n, P1 n = P2 n) → SeqPerm γg q ty P1 -∗ SeqPerm γg q ty P2;
  SeqPerm_Split : ∀ γg q ty P1 P2, SeqPerm γg q ty P1 -∗ SeqPerm γg q ty (λ n, P1 n && P2 n) ∗ SeqPerm γg q ty (λ n, P1 n && negb (P2 n));
  SeqPerm_Combine : ∀ γg q ty P1 P2, SeqPerm γg q ty P1 -∗ SeqPerm γg q ty P2 -∗ SeqPerm γg q ty (λ n, P1 n || P2 n);
  SeqPerm_Excl : ∀ γg q ty P1 P2 n, P1 n = true → P2 n = true → SeqPerm γg q ty P1 -∗ SeqPerm γg q ty P2 -∗ False;
  (**************************************************************)

  (* operations specs *)
  new_seq_spec : new_seq_spec' newSEQ SeqLocal SeqInv SeqPerm;
  enqueueWithTicket_spec : enqueueWithTicket_spec' enqueueWithTicket SeqLocal SeqInv SeqPerm;
  dequeueWithTicket_spec : dequeueWithTicket_spec' dequeueWithTicket SeqLocal SeqInv SeqPerm;
}.

Arguments seq_composition_spec _ {_ _ _}.
Global Existing Instances SeqInv_Objective SeqLocal_Persistent SeqPerm_Objective.
