From stdpp Require Import namespaces.
From gpfsl.logic Require Import lifting.

Definition mp_spec Σ `{!noprolG Σ} (mp: expr) :=
  ∀ tid, {{{ True }}} mp @ tid; ⊤ {{{ v, RET #v; ⌜v = 42⌝ }}}.

(* namespace for MP *)
Definition mpN (n: loc) := nroot .@ "mpN" .@ n.
