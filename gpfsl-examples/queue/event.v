From stdpp Require Import countable.

From gpfsl.lang Require Import lang.

Require Import iris.prelude.options.

(** Abstract state of queue *)
Definition queue := list (Z * view).

(** Queue events *)
Inductive qevent := Enq (v : Z) | Deq (v : Z) | EmpDeq (* | FAIL_DEQ *).
Notation dummy_qevt := (Enq 0).
#[global] Instance qevent_inhabited : (Inhabited qevent) := populate dummy_qevt. 

Local Open Scope Z_scope.

Global Instance qevent_eq_dec : EqDecision qevent.
Proof. solve_decision. Defined.
Global Instance qevent_countable : Countable qevent.
Proof.
  refine (
    inj_countable'
      (λ e, match e with
            | Enq v => (1, v)
            | Deq v => (2, v)
            | EmpDeq => (3, 0) end)
      (λ x, match x with
            | (1, v) => Enq v
            | (2, v) => Deq v
            | _ => EmpDeq end) _);
    by intros [].
Qed.

Definition is_enqueue e v : Prop := e = Enq v.
Definition is_dequeue e v : Prop := e = Deq v.
Definition is_maybe_dequeue e : Prop :=
  match e with | Enq _ => False | _ => True end.
