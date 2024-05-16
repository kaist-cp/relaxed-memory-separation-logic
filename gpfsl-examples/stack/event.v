From stdpp Require Import countable.

Require Import iris.prelude.options.

(** Stack events *)
Inductive sevent := Push (v : Z) | Pop (v : Z) | EmpPop (* | FAIL_DEQ *).
Notation dummy_sevt := (Push 0).

Local Open Scope Z_scope.

Global Instance sevent_eq_dec : EqDecision sevent.
Proof. solve_decision. Defined.
Global Instance sevent_countable : Countable sevent.
Proof.
  refine (
    inj_countable'
      (λ e, match e with
            | Push v => (1, v)
            | Pop v => (2, v)
            | EmpPop => (3, 0) end)
      (λ x, match x with
            | (1, v) => Push v
            | (2, v) => Pop v
            | _ => EmpPop end) _);
    by intros [].
Qed.

Definition is_push e v : Prop := e = Push v.
Definition is_pop e v : Prop := e = Pop v.
Definition is_maybe_pop e : Prop :=
  match e with | Push _ => False | _ => True end.
