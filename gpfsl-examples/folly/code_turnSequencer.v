From gpfsl.lang Require Export notation.
From gpfsl.logic Require Import repeat_loop new_delete.

Notation errorE := (-1) (only parsing).

Definition newTS : val :=
  λ: [],
    let: "x" := new [ #1] in
    "x" <- #0;;
    "x".

Definition completeTurn : val :=
  λ: ["state_"; "turn"],
    let: "state" := !ʳˡˣ "state_" in
    if: "state" = "turn"
    then "state_" <-ʳᵉˡ ("turn" + #1)
    else #errorE.

Definition waitForTurn : val :=
  rec: "wait" ["state_"; "turn"] :=
    let: "state" := !ᵃᶜ "state_" in
    if: "state" = "turn" then #☠
    else if: "turn" < "state" then #errorE
         else "wait" ["state_"; "turn"].
