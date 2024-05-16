From orc11 Require Export value mem_order.

Require Import stdpp.options.

Record sysEvent := mkSysEvent {
    output: Z;
    inputs: list Z;
  }.

Section Event.
  Context {loc: Type} `{Countable VAL}.

  Inductive event :=
    | Silent
    | Alloc (l : loc) (n: positive)
    | Dealloc (l : loc) (n : positive)
    | Read (l: loc) (v: val (VAL:=VAL)) (o: memOrder)
    | Write (l: loc) (v: VAL) (o: memOrder)
    | Update (l: loc) (vr vw: VAL) (or ow: memOrder)
    | Fence (or ow: memOrder)
    | SysCall (sevt: sysEvent)
    .

End Event.

Arguments event loc VAL : clear implicits.
