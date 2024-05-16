From gpfsl.lang Require Import lang.

Definition oloc_to_lit (on : option loc) : lit :=
  if on is Some n then LitLoc n else LitInt 0.

Global Instance oloc_to_lit_inj : Inj (=) (=) oloc_to_lit.
Proof. intros [] []; simpl; naive_solver. Qed.
