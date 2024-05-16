From gpfsl.examples Require Import sflib.

From stdpp Require Import namespaces.

From gpfsl.logic Require Import logatom.

From gpfsl.examples.stack Require Export event.
From gpfsl.examples.omo Require Export omo omo_preds append_only_loc.

Require Import iris.prelude.options.

Local Open Scope nat_scope.

Inductive tseq_event := Init | Take (n : nat) | Complete (n : nat).
Definition tseq_state := (event_id * nat * view * eView)%type.
Global Instance tseq_event_inhabited : Inhabited tseq_event := populate Init.

Local Notation history := (history tseq_event).
Implicit Types (E : history) (st : tseq_state).

Inductive tseq_step : ∀ (e : event_id) (eV : omo_event tseq_event) st st', Prop :=
  | tseq_step_Take e eV v e' V' lV'
    (TAKE : eV.(type) = Take v)
    (LEQ : 0 ≤ v)
    (SYNC : V' ⊑ eV.(sync))
    (EVIEW : {[e; e']} ∪ lV' ⊆ eV.(eview))
    : tseq_step e eV (e', v, V', lV') (e', v, V', lV')
  | tseq_step_Complete e eV v e' V' lV'
    (COMPLETE : eV.(type) = Complete v)
    (LEQ : 0 ≤ v)
    (SYNC : V' ⊑ eV.(sync))
    (EVIEW : {[e; e']} ∪ lV' ⊆ eV.(eview))
    : tseq_step e eV (e', v, V', lV') (e, v + 1, eV.(sync), eV.(eview))
  | tseq_step_Init eV
    (INIT : eV.(type) = Init)
    (EVIEW : eV.(eview) = {[0%nat]})
    : tseq_step 0%nat eV (0%nat, 0, ∅, ∅) (0%nat, 0, eV.(sync), eV.(eview))
  .

Global Instance tseq_interpretable : Interpretable tseq_event tseq_state :=
  {
    init := (0%nat, 0, ∅, ∅);
    step := tseq_step
  }.

Definition TSeqLocalT Σ : Type :=
  ∀ (γg : gname) (l : loc) (E : history) (M : eView), vProp Σ.
Definition TSeqLocalNT Σ : Type :=
  ∀ (N : namespace), TSeqLocalT Σ.
Definition TSeqInvT Σ : Type :=
  ∀ (γg : gname) (l : loc) (E : history) (R : nat → vProp Σ), vProp Σ.
Definition TSeqPermT Σ : Type :=
  ∀ (γg : gname) (l : loc) (P : nat → bool), vProp Σ.
Definition TSeqCompleteT Σ : Type :=
  ∀ (γg : gname) (l : loc) (n : nat), vProp Σ.

Definition new_tseq_spec' {Σ} `{!noprolG Σ}
  (newTS : val) (TSeqLocal : TSeqLocalNT Σ) (TSeqInv : TSeqInvT Σ) (TSeqPerm : TSeqPermT Σ) : Prop :=
  ∀ N tid V R,
  {{{ ⊒V ∗ ▷ (R 0%nat) }}}
    newTS [] @ tid; ⊤
  {{{ γg (l: loc) E M V', RET #l;
      ⊒V' ∗ @{V'} TSeqLocal N γg l E M ∗ TSeqInv γg l E R ∗ TSeqPerm γg l (λ _, true) ∗
      ⌜ E = [mkOmoEvent Init V' M] ∧ V ⊑ V' ⌝ }}}.

Definition wait_spec' {Σ} `{!noprolG Σ}
  (waitForTurn : val) (TSeqLocal : TSeqLocalNT Σ) (TSeqInv : TSeqInvT Σ) (TSeqPerm : TSeqPermT Σ) (TSeqComplete : TSeqCompleteT Σ) : Prop :=
  ∀ N (DISJ: N ## histN) (l: loc) tid γg E1 M (V : view) (n : nat) (R : nat → vProp Σ),
  (* PRIVATE PRE *)
  (* E1 is a snapshot of the history, locally observed by M *)
  ⊒V -∗ TSeqLocal N γg l E1 M -∗ TSeqPerm γg l (λ m, m =? n) -∗
  (* PUBLIC PRE *)
  <<< ∀ E, ▷ TSeqInv γg l E R >>>
    waitForTurn [ #l; #n] @ tid; ↑N
  <<< ∃ V' E' M',
      (* PUBLIC POST *)
      ▷ TSeqInv γg l E' R ∗
      ⊒V' ∗ @{V'} TSeqLocal N γg l E' M' ∗
      ⌜ V ⊑ V' ∧
        E' = E ++ [mkOmoEvent (Take n) V' M'] ∧ M ⊆ M' ⌝,
      RET #☠, R n ∗ TSeqComplete γg l n >>>
  .

Definition complete_spec' {Σ} `{!noprolG Σ}
  (completeTurn : val) (TSeqLocal : TSeqLocalNT Σ) (TSeqInv : TSeqInvT Σ) (TSeqComplete : TSeqCompleteT Σ) : Prop :=
  ∀ N (DISJ: N ## histN) (l: loc) tid γg E1 M (V : view) (n : nat) (R : nat → vProp Σ),
  (* PRIVATE PRE *)
  (* E1 is a snapshot of the history, locally observed by M *)
  ⊒V -∗ TSeqLocal N γg l E1 M -∗ R (n + 1)%nat -∗ TSeqComplete γg l n -∗
  (* PUBLIC PRE *)
  <<< ∀ E, ▷ TSeqInv γg l E R >>>
    completeTurn [ #l; #n] @ tid; ↑N
  <<< ∃ V' E' M',
      (* PUBLIC POST *)
      ▷ TSeqInv γg l E' R ∗
      ⊒V' ∗ @{V'} TSeqLocal N γg l E' M' ∗
      ⌜ V ⊑ V' ∧
        E' = E ++ [mkOmoEvent (Complete n) V' M'] ∧ M ⊆ M' ⌝,
      RET #☠, emp >>>
  .

Record tseq_spec {Σ} `{!noprolG Σ} := TSeqSpec {
  (** operations *)
  newTS : val;
  waitForTurn : val;
  completeTurn : val;

  (** These are common elements in arbitrary history-style spec *)
  (** predicates *)
  TSeqLocal : TSeqLocalNT Σ;
  TSeqInv : TSeqInvT Σ;
  TSeqPerm : TSeqPermT Σ;
  TSeqComplete : TSeqCompleteT Σ;

  (** predicates properties *)
  TSeqInv_Objective : ∀ γg l E R, Objective (TSeqInv γg l E R);
  TSeqInv_Linearizable : ∀ γg l E R, TSeqInv γg l E R ⊢ ⌜ Linearizability E ⌝;
  TSeqInv_history_wf :
    ∀ γg l E R, TSeqInv γg l E R ⊢ ⌜ history_wf E ⌝;

  TSeqInv_TSeqLocal :
    ∀ N γg l E E' M' R,
      TSeqInv γg l E R -∗ TSeqLocal N γg l E' M' -∗ ⌜ E' ⊑ E ⌝;
  TSeqLocal_lookup :
    ∀ N γg l E M e V,
      sync <$> E !! e = Some V → e ∈ M → TSeqLocal N γg l E M -∗ ⊒V;
  TSeqLocal_Persistent :
    ∀ N γg l E M, Persistent (TSeqLocal N γg l E M);

  TSeqPerm_Objective : ∀ γg l P, Objective (TSeqPerm γg l P);
  TSeqPerm_Equiv : ∀ γg l P1 P2, (∀ n, P1 n = P2 n) → TSeqPerm γg l P1 -∗ TSeqPerm γg l P2;
  TSeqPerm_Split : ∀ γg l P1 P2, TSeqPerm γg l P1 -∗ TSeqPerm γg l (λ n, P1 n && P2 n) ∗ TSeqPerm γg l (λ n, P1 n && negb (P2 n));
  TSeqPerm_Combine : ∀ γg l P1 P2, TSeqPerm γg l P1 -∗ TSeqPerm γg l P2 -∗ TSeqPerm γg l (λ n, P1 n || P2 n);
  TSeqPerm_Excl : ∀ γg l P1 P2 n, P1 n = true → P2 n = true → TSeqPerm γg l P1 -∗ TSeqPerm γg l P2 -∗ False;
  (**************************************************************)

  (* operations specs *)
  new_tseq_spec : new_tseq_spec' newTS TSeqLocal TSeqInv TSeqPerm;
  wait_spec : wait_spec' waitForTurn TSeqLocal TSeqInv TSeqPerm TSeqComplete;
  complete_spec : complete_spec' completeTurn TSeqLocal TSeqInv TSeqComplete;
}.

Arguments tseq_spec _ {_}.
Global Existing Instances TSeqInv_Objective TSeqLocal_Persistent TSeqPerm_Objective.
