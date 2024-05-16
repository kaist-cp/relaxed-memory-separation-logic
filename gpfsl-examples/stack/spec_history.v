From gpfsl.examples Require Import sflib.

From stdpp Require Import namespaces.

From gpfsl.logic Require Import logatom.

From gpfsl.examples.stack Require Export stack_event_omo.
From gpfsl.examples.omo Require Export omo omo_preds append_only_loc.

Require Import iris.prelude.options.

Local Open Scope Z_scope.

Local Notation history := (history sevent_hist).
Implicit Types (E : history) (stk : stack_state).

Local Notation EMPTY := 0 (only parsing).
Local Notation FAIL_RACE := (-1) (only parsing).

Definition StackLocalT Σ : Type :=
  ∀ (γg : gname) (s : loc) (E : history) (M : eView), vProp Σ.
Definition StackLocalNT Σ : Type :=
  ∀ (N : namespace), StackLocalT Σ.
Definition StackInvT Σ : Type :=
  ∀ (γg : gname) (s : loc) (E : history), vProp Σ.

Definition new_stack_spec' {Σ} `{!noprolG Σ}
  (new_stack : val) (StackLocal : StackLocalNT Σ) (StackInv : StackInvT Σ) : Prop :=
  ∀ N tid,
  {{{ True }}}
    new_stack [] @ tid; ⊤
  {{{ γg (s: loc) V E M, RET #s;
      ⊒V ∗ StackInv γg s E ∗
      ⌜ E = [mkOmoEvent Init V M] ⌝ ∗ @{V} StackLocal N γg s E M }}}.

Definition try_push_spec' {Σ} `{!noprolG Σ}
  (try_push : val) (StackLocal : StackLocalNT Σ) (StackInv : StackInvT Σ) : Prop :=
  ∀ N (DISJ: N ## histN) (s: loc) tid γg E1 M (V : view) (v : Z) (Posx: 0 < v),
  (* PRIVATE PRE *)
  (* E1 is a snapshot of the history, locally observed by M *)
  ⊒V -∗ StackLocal N γg s E1 M -∗
  (* PUBLIC PRE *)
  <<< ∀ E, ▷ StackInv γg s E >>>
    try_push [ #s ; #v] @ tid; ↑N
  <<< ∃ (b: bool) V' E' ps M',
      (* PUBLIC POST *)
      ▷ StackInv γg s E' ∗
      ⌜ if b then (
        (* successful case *)
        E' = E ++ [mkOmoEvent ps V' M'] ∧
        is_push ps v ∧ V ⊑ V' ∧
        M ⊆ M')
        else (
          (* FAIL_RACE case *)
          E' = E ∧ M' = M
        ) ⌝ ∗
        ⊒V' ∗ @{V'} StackLocal N γg s E' M',
      RET #b, emp >>>
  .

Definition push_spec' {Σ} `{!noprolG Σ}
  (push : val) (StackLocal : StackLocalNT Σ) (StackInv : StackInvT Σ) : Prop :=
  ∀ N (DISJ: N ## histN) (s: loc) tid γg E1 M (V : view) (v : Z) (Posx: 0 < v),
  (* PRIVATE PRE *)
  (* E1 is a snapshot of the history, locally observed by M *)
  ⊒V -∗ StackLocal N γg s E1 M -∗
  (* PUBLIC PRE *)
  <<< ∀ E, ▷ StackInv γg s E >>>
    push [ #s ; #v] @ tid; ↑N
  <<< ∃ V' E' ps M',
      (* PUBLIC POST *)
      ▷ StackInv γg s E' ∗
      ⊒V' ∗ @{V'} StackLocal N γg s E' M' ∗
      ⌜ V ⊑ V'
      ∧ is_push ps v
      ∧ E' = E ++ [mkOmoEvent ps V' M'] ∧ M ⊆ M' ⌝,
      RET #☠, emp >>>
  .

Definition try_pop_spec' {Σ} `{!noprolG Σ}
  (try_pop : val) (StackLocal : StackLocalNT Σ) (StackInv : StackInvT Σ) : Prop :=
  ∀ N (DISJ: N ## histN) (s: loc) tid γg E1 M V,
  (* PRIVATE PRE *)
  ⊒V -∗ StackLocal N γg s E1 M -∗
  (* PUBLIC PRE *)
  <<< ∀ E, ▷ StackInv γg s E >>>
    try_pop [ #s] @ tid; ↑N
  <<< ∃ (v: Z) V' E' pp M',
      (* PUBLIC POST *)
      ▷ StackInv γg s E' ∗
      ⊒V' ∗ @{V'} StackLocal N γg s E' M' ∗
      ⌜ V ⊑ V' ⌝ ∗
      ⌜ if (decide (v = FAIL_RACE)) then (
          (* FAIL_RACE case *)
          E' = E ∧ M' = M
        ) else (
          E' = E ++ [mkOmoEvent pp V' M'] ∧ M ⊆ M' ∧
          if (decide (v = EMPTY)) then pp = EmpPop  (* EMPTY case *)
          else 0 < v ∧ is_pop pp v (* successful case *)
        ) ⌝,
      RET #v , emp >>>
  .

Definition pop_spec' {Σ} `{!noprolG Σ}
  (pop : val) (StackLocal : StackLocalNT Σ) (StackInv : StackInvT Σ) : Prop :=
  ∀ N (DISJ: N ## histN) (s: loc) tid γg E1 M V,
  (* PRIVATE PRE *)
  ⊒V -∗ StackLocal N γg s E1 M -∗
  (* PUBLIC PRE *)
  <<< ∀ E, ▷ StackInv γg s E >>>
    pop [ #s] @ tid; ↑N
  <<< ∃ (v: Z) V' E' pp M',
      (* PUBLIC POST *)
      ▷ StackInv γg s E' ∗
      ⊒V' ∗ @{V'} StackLocal N γg s E' M' ∗
      ⌜ V ⊑ V'
      ∧ E' = E ++ [mkOmoEvent pp V' M'] ∧ M ⊆ M'
      ∧ if (decide (v = EMPTY)) then pp = EmpPop (* EMPTY case *)
        else 0 < v ∧ is_pop pp v ⌝, (* successful case *)
      RET #v, emp >>>
  .

Record stack_spec {Σ} `{!noprolG Σ} := StackSpec {
  (** operations *)
  new_stack : val;
  try_push : val;
  push : val;
  try_pop : val;
  pop : val;

  (** These are common elements in arbitrary history-style spec *)
  (** predicates *)
  StackLocal : StackLocalNT Σ;
  StackInv : StackInvT Σ;

  (** predicates properties *)
  StackInv_Objective : ∀ γg s E, Objective (StackInv γg s E);
  StackInv_Timeless : ∀ γg s E, Timeless (StackInv γg s E);
  StackInv_Linearizable : ∀ γg s E, StackInv γg s E ⊢ ⌜ Linearizability E ⌝;
  StackInv_history_wf :
    ∀ γg s E, StackInv γg s E ⊢ ⌜ history_wf E ⌝;

  StackInv_StackLocal :
    ∀ N γg s E E' M',
      StackInv γg s E -∗ StackLocal N γg s E' M' -∗ ⌜ E' ⊑ E ⌝;
  StackLocal_lookup :
    ∀ N γg s E M e V,
      sync <$> E !! e = Some V → e ∈ M → StackLocal N γg s E M -∗ ⊒V;
  StackLocal_Persistent :
    ∀ N γg s E M, Persistent (StackLocal N γg s E M);
  (**************************************************************)

  (* operations specs *)
  new_stack_spec : new_stack_spec' new_stack StackLocal StackInv;
  try_push_spec : try_push_spec' try_push StackLocal StackInv;
  push_spec : push_spec' push StackLocal StackInv;
  try_pop_spec : try_pop_spec' try_pop StackLocal StackInv;
  pop_spec : pop_spec' pop StackLocal StackInv;
}.

Arguments stack_spec _ {_}.
Global Existing Instances StackInv_Objective StackInv_Timeless StackLocal_Persistent.
