From gpfsl.lang Require Export notation.
From gpfsl.logic Require Import new_delete.

(* A circular array that is non-atomic, and its bounds (top + bottom) are to be
  managed externally *)

Notation sz := 0 (only parsing).
Notation b := 1 (only parsing).

(* Allocate a buffer with size s *)
Definition ca_new : val :=
  λ: ["s"],
    let: "q" := new [ #2] in
      "q" +ₗ #sz <- "s" ;;
      let: "d" := new [ "s"] in
      "q" +ₗ #b <- "d" ;;
      "q"
  .

(* get the ith element in q *)
Definition ca_get : val :=
  λ: ["q"; "i"],
    let: "s" := !("q" +ₗ #sz) in
    let: "d" := !("q" +ₗ #b) in
    let: "n" := "i" `mod` "s" in
      ! ("d" +ₗ "n")
  .

(* set the ith element in q with v *)
Definition ca_set : val :=
  λ: ["q"; "i" ; "v"],
    let: "s" := !("q" +ₗ #sz) in
    let: "d" := !("q" +ₗ #b) in
    let: "n" := "i" `mod` "s" in
      ("d" +ₗ "n") <- "v"
  .
