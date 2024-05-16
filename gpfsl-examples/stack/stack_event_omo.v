From gpfsl.examples Require Import sflib.

From stdpp Require Import namespaces.

From gpfsl.logic Require Import logatom.

From gpfsl.examples.stack Require Export event.
From gpfsl.examples.omo Require Export omo omo_preds append_only_loc.

Require Import iris.prelude.options.

Local Open Scope Z_scope.

Inductive sevent_hist := Init | Push (v : Z) | Pop (v : Z) | EmpPop.
Definition is_push ev v := ev = Push v.
Definition is_pop ev v := ev = Pop v.
Definition dummy_sevt_hist := Push 0.

Definition stack_state := list (event_id * Z * view * eView).

Implicit Types (stk : stack_state).

(* Build stack state with the events in the given order *)
Inductive stack_step : ∀ (e : event_id) (eV : omo_event sevent_hist) stk stk', Prop :=
  | stack_step_Push u uV v stk
      (PUSH : uV.(type) = Push v)
      (NZ : 0 < v)
      (LVIEW : u ∈ uV.(eview))
      : stack_step u uV
          stk
          ((u, v, uV.(sync), uV.(eview)) :: stk)
  | stack_step_Pop u o oV v V lV stk
      (POP : oV.(type) = Pop v)
      (NZ : 0 < v)
      (SYNC : V ⊑ oV.(sync))
      (LVIEW : ({[o; u]} ∪ lV) ⊆ oV.(eview))
      : stack_step o oV
          ((u, v, V, lV) :: stk)
          stk
  | stack_step_EmpPop o oV
      (EMPPOP : oV.(type) = EmpPop)
      (LVIEW : o ∈ oV.(eview))
      : stack_step o oV [] []
  | stack_step_Init eV
      (INIT : eV.(type) = Init)
      (LVIEW : eV.(eview) = {[0%nat]})
      : stack_step 0%nat eV [] []
  .

Global Instance stack_interpretable : Interpretable sevent_hist stack_state :=
  {
    init := [];
    step := stack_step
  }.
