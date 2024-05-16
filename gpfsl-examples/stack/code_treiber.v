From gpfsl.lang Require Export notation.
From gpfsl.logic Require Import new_delete.

Notation next := 0 (only parsing).
Notation data := 1 (only parsing).

Notation null := 0 (only parsing).
Notation EMPTY := 0 (only parsing).
Notation FAIL_RACE := (-1) (only parsing).

Definition new_tstack : val :=
  λ: [], let: "s" := new [ #1] in "s" <- #null ;; "s".

Definition try_push_internal : val :=
  λ: ["s"; "n"],
    let: "h" := !ʳˡˣ "s" in
    "n" +ₗ #next <- "h";;
    (* release CAS, i.e. relaxed fail read, relaxed success read, release write *)
    casʳᵉˡ("s","h","n")
  .

Definition try_push : val :=
  λ: ["s"; "x"],
    let: "n" := new [ #2] in
    "n" +ₗ #data <- "x" ;;
    if: try_push_internal ["s"; "n"]
    then #true
    else delete [ #2; "n"] ;; #false
  .

Definition try_pop : val :=
  λ: ["s"],
    let: "h" := !ᵃᶜ "s" in
    if: "h" = #null
    then #EMPTY
    else
      (* This non-atomic read suffices, because the nodes in the stack are
        one-shots: once set, they are never written to again. *)
      let: "n" := !("h" +ₗ #next) in
      (* acquire CAS, i.e. relaxed fail read, acquire success read, relaxed write *)
      (* TODO: this CAS can be made relaxed completely. The acquire read is not
        needed, because we have read acquire from "s" above, which should already
        include the write to data. Certainly this will complicate the proof. *)
      if: casᵃᶜ("s","h","n")
      then !("h" +ₗ #data)
      else #FAIL_RACE
  .

(* keep retrying to push *)
Definition push_internal : val :=
  rec: "try" ["s"; "n"] :=
    if: try_push_internal ["s"; "n"]
    then #☠
    else "try" ["s"; "n"]
  .

(* set up the node with data then try to push *)
Definition push : val :=
  λ: ["s"; "x"],
    let: "n" := new [ #2] in
    "n" +ₗ #data <- "x" ;;
    push_internal ["s";"n"]
  .

Definition push_slow : val :=
  rec: "try" ["s"; "x"] :=
    if: try_push ["s"; "x"]
    then #☠
    else "try" ["s"; "x"]
  .

Definition pop : val :=
  rec: "try" ["s"] :=
    let: "v" := try_pop ["s"] in
    if: "v" = #FAIL_RACE
    then "try" ["s"]
    else "v"
  .
