From gpfsl.lang Require Export notation.
From gpfsl.logic Require Import repeat_loop new_delete.

Require Import iris.prelude.options.

Notation link := 0 (only parsing).
Notation data := 1 (only parsing).
Notation head := 0 (only parsing).
Notation tail := 1 (only parsing).

Notation null := 0 (only parsing).
Notation EMPTY := 0 (only parsing).
Notation FAIL_RACE := (-1) (only parsing).

Definition new_queue : val :=
  λ: [],
    let: "s" := new [ #1] in
    "s" +ₗ #link <- #null ;;
    let: "q" := new [ #2] in
    "q" +ₗ #head <- "s" ;;
    "q" +ₗ #tail <- "s" ;;
    "q"
  .

Definition find_tail : val :=
  λ: ["q"],
    let: "n"  := !ᵃᶜ ("q" +ₗ #tail) in
    let: "n'" := !ᵃᶜ ("n" +ₗ #link) in
      if: "n'" = #null
      then "n"
      else
        casʳᵉˡ("q" +ₗ #tail, "n", "n'");;
        #false
  .

Definition try_enq : val :=
  λ: ["q"; "x"],
    let: "n" := new [ #2] in
    "n" +ₗ #data <- "x" ;;
    "n" +ₗ #link <- #null ;;
    let: "t" := (repeat: (find_tail ["q"])) in
    if: casʳᵃ("t" +ₗ #link, #null, "n")
    then casʳᵉˡ("q" +ₗ #tail, "t", "n");; #true
    else delete [ #2; "n"] ;; #false
  .

Definition enqueue : val :=
  rec: "try" ["q"; "x"] :=
    if: try_enq ["q"; "x"]
    then #☠
    else "try" ["q"; "x"]
  .

Definition try_deq : val :=
  λ: ["q"],
    let: "s" := !ᵃᶜ ("q" +ₗ #head) in
    let: "n" := !ᵃᶜ ("s" +ₗ #link) in
    if: "n" = #null
    then #EMPTY
    else
      if: casʳᵃ("q" +ₗ #head, "s", "n")
      then ! ("n" +ₗ #data)
      else #FAIL_RACE
  .

(* Keep retrying if FAIL_RACE *)
Definition dequeue : val :=
  rec: "try" ["q"] :=
    let: "n" := try_deq ["q"] in
      (* FIXME: our language doesn't have comparison for arbitrary literals, so
        the next line is limited to integer comparison, which means that
        the queue is only intended for use with integers. *)
      if: #EMPTY ≤ "n"
      then "n"
      else "try" ["q"]
  .
