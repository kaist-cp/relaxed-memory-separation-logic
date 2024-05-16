From gpfsl.lang Require Export notation.
From gpfsl.logic Require Import new_delete.

Notation stack := 0 (only parsing).
Notation offer := 1 (only parsing).
Notation CANCELLED := (-1) (only parsing).
Notation DUMMY_XCHG := 0 (only parsing).
Notation EMPTY := 0 (only parsing).
Notation FAIL_RACE := (-1) (only parsing).

Section elim_stack.
  Variables (new_stack try_push' try_pop' : val).
  Variables (new_exchanger exchange : val).

  Definition new_estack : val :=
    λ: [],
      let: "es" := new [ #2] in
      "es" +ₗ #stack <- new_stack [];;
      "es" +ₗ #offer <- new_exchanger [];;
      "es".

  Definition try_push : val :=
    λ: ["es"; "v"],
      let: "s" := !("es" +ₗ #stack) in
      if: try_push' ["s"; "v"]
      then #true
      else
        let: "ex" := !("es" +ₗ #offer) in
        (* exchange with pop, only succeeds if we get DUMMY_XCHG.
          Otherwise, we can fail because the exchange fails, or because
          we accidentally exchanged with another push. *)
        exchange ["ex"; "v"] = #DUMMY_XCHG
    .

  (** Similar to Treiber stack's [push_internal] or [push_slow] *)
  Definition push : val :=
    rec: "try" ["es"; "v"] :=
      if: try_push ["es"; "v"]
      then #☠
      else "try" ["es"; "v"]
    .

  Definition try_pop : val :=
    λ: ["es"],
      let: "s" := !("es" +ₗ #stack) in
      let: "v" := try_pop' ["s"] in
      if: "v" = #FAIL_RACE
      then (* only try to exchange if we fail due to a race *)
        let: "ex" := !("es" +ₗ #offer) in
        (* can return CANCELLED (= FAIL_RACE) or a real element *)
        let: "e" := exchange ["ex"; #DUMMY_XCHG] in
        if: #0 < "e"
        then "e" (* only succeeds with a 0 < return *)
        else (* exchange fails, or we accidentally exchanged with another pop *)
          #FAIL_RACE
      else "v" (* can return EMPTY or a real element *)
    .

  (** Similar to Treiber stack's [pop] *)
  Definition pop : val :=
    rec: "try" ["es"] :=
      let: "v" := try_pop ["es"] in
      if: "v" = #FAIL_RACE
      then "try" ["es"] (* retry if FAIL_RACE *)
      else "v" (* can return EMPTY or a real element *)
    .
End elim_stack.
