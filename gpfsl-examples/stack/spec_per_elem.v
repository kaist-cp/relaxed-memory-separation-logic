From gpfsl.logic Require Import lifting.

Require Import iris.prelude.options.

Local Notation EMPTY := 0%Z (only parsing).
Local Notation FAIL := (-1)%Z (only parsing).

Record stack_per_elem_spec {Σ} `{!noprolG Σ} := StackPerElemSpec {
  (* -- operations -- *)
  new_stack : val;
  push : val;
  pop : val;
  try_push : val;
  try_pop : val;
  (* -- predicates -- *)
  Stack (P: Z → vProp Σ) (s : loc) : vProp Σ;
  (* -- predicate properties -- *)
  stack_persistent : ∀ P s, Persistent (Stack P s);
  (* Stack is unique w.r.t. s? *)
  (* -- operation specs -- *)
  new_stack_spec P tid :
    {{{ True }}}
      new_stack [] @ tid; ⊤
    {{{ (s: loc), RET #s; Stack P s }}} ;
  push_spec P s v tid :
    {{{ Stack P s ∗ P v }}}
      push [ #s; #v] @ tid; ⊤
    {{{ RET #☠; True }}} ;
  pop_spec P s tid :
    {{{ Stack P s }}}
      pop [ #s] @ tid; ⊤
    {{{ v, RET #v; if decide (v = EMPTY) then True else P v }}} ;
  try_push_spec P s v tid :
    {{{ Stack P s ∗ P v }}}
      try_push [ #s; #v] @ tid; ⊤
    {{{ (b : bool), RET #b; if b then True else P v }}} ;
  try_pop_spec P s tid :
    {{{ Stack P s }}}
      try_pop [ #s] @ tid; ⊤
    {{{ v, RET #v; ⌜v = EMPTY⌝ ∨ ⌜v = FAIL⌝ ∨ P v }}} ;
}.

Global Arguments stack_per_elem_spec _ {_}.
