From gpfsl.logic Require Import lifting.

Require Import iris.prelude.options.

Local Notation EMPTY := 0%Z (only parsing).
Local Notation FAIL := (-1)%Z (only parsing).

Record queue_per_elem_spec {Σ} `{!noprolG Σ} := QueuePerElemSpec {
  (* -- operations -- *)
  new_queue : val;
  enqueue : val;
  dequeue : val;
  try_enq : val;
  try_deq : val;
  (* -- predicates -- *)
  Queue (P : Z → vProp Σ) (q : loc) : vProp Σ;
  (* -- predicate properties -- *)
  queue_persistent : ∀ P q, Persistent (Queue P q);
  (* Queue is unique w.r.t. s? *)
  (* -- operation specs -- *)
  new_queue_spec P tid :
    {{{ True }}}
      new_queue [] @ tid; ⊤
    {{{ (q : loc), RET #q; Queue P q }}} ;
  enqueue_spec P q v tid :
    {{{ Queue P q ∗ P v }}}
      enqueue [ #q; #v] @ tid; ⊤
    {{{ RET #☠; True }}} ;
  dequeue_spec P q tid :
    {{{ Queue P q }}}
      dequeue [ #q] @ tid; ⊤
    {{{ v, RET #v; if decide (v = EMPTY) then True else P v }}} ;
  try_enq_spec P q v tid :
    {{{ Queue P q ∗ P v }}}
      try_enq [ #q; #v] @ tid; ⊤
    {{{ (b : bool), RET #b; if b then True else P v }}} ;
  try_deq_spec P q tid :
    {{{ Queue P q }}}
      try_deq [ #q] @ tid; ⊤
    {{{ v, RET #v; ⌜v = EMPTY⌝ ∨ ⌜v = FAIL⌝ ∨ P v }}} ;
}.

Global Arguments queue_per_elem_spec _ {_}.
