From gpfsl.logic Require Import lifting.

Require Import iris.prelude.options.

Record na_stack_spec {Σ} `{!noprolG Σ} := NAStackSpec {
  (* -- operations -- *)
  new_stack: val;
  push: val;
  pop: val;
  (* -- predicates -- *)
  NAStack (P: lit → vProp Σ) (s : loc) (A : list lit) : vProp Σ;
  (* -- predicate properties -- *)
  (* NAStack is unique w.r.t. s? *)
  (* -- operation specs -- *)
  new_stack_spec P tid :
    {{{ True }}}
        new_stack [] @ tid; ⊤
    {{{ (s: loc), RET #s; NAStack P s nil }}} ;
  push_spec P s A v tid :
    {{{ NAStack P s A ∗ P v }}}
        push [ #s; #v] @ tid; ⊤
    {{{ RET #☠; NAStack P s (v :: A) }}} ;
  pop_spec P s A tid :
    {{{ NAStack P s A }}}
     pop [ #s] @ tid; ⊤
    {{{ (v: lit), RET #v;  match A with
                           | nil => ⌜v = 0⌝ ∗ NAStack P s A
                           | v' :: A' =>  ⌜v = v'⌝ ∗ NAStack P s A' ∗ P v
                           end }}} ;
}.

Global Arguments na_stack_spec _ {_}.
