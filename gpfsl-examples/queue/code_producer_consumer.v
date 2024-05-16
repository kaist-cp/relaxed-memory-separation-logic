From gpfsl.lang Require Export notation.
From gpfsl.lang Require Import tactics.

Require Import iris.prelude.options.

Section code.
Variables (enqueue dequeue : val).

(** Iterate the array "a" from "i" up to (but not including) "n" and enqueue
  the elements in "q" in the array index order. *)
Definition produce_loop : val :=
  λ: ["q"; "a"; "n"],
    rec: "loop" ["i"] :=
      if: "i" = "n"
      then #☠
      else
        let: "e":= !("a" +ₗ "i") in
        enqueue ["q"; "e"];;
        "loop" ["i" + #1%nat]
  .

(** Enqueue the elements of array "a" with size "n" into "q" *)
Definition produce : val :=
  λ: ["q"; "a"; "n"], produce_loop ["q"; "a"; "n"] [ #0%nat].

(** Dequeue elements from "q" into array "a" from index "i" to "n". *)
Definition consume_loop : val :=
  λ: ["q"; "a"; "n"],
    rec: "loop" ["i"] :=
      if: "i" = "n"
      then #☠
      else
        let: "e" := dequeue ["q"] in
        if: #0%nat < "e"
        then
          ("a" +ₗ "i") <- "e";;
          "loop" ["i" + #1%nat]
        else
          "loop" ["i"]
  .

(** Dequeue "n" elements from "q" and put them in "a" using the dequeue order. *)
Definition consume : val :=
  λ: ["q"; "a"; "n"], consume_loop ["q"; "a"; "n"] [ #0%nat].

(** Concurrently produce in one thread and consume in the other.
  We don't need to join because the consumer thread does wait for enough "n"
  elements to be consumed. *)
Definition produce_consume : val :=
  λ: ["q"; "pa"; "ca"; "n"],
    Fork
    ( produce ["q" ; "pa"; "n"] );; (* || *) consume ["q" ; "ca"; "n"]
  .

(* The consumer tries to consume half (n) elements of the 2n elements that the
  producer produces. In case of SPSC, the consumer gets the first half. *)
Definition produce_consume_first_half : val :=
  λ: ["q"; "pa"; "ca"; "n"],
    Fork
    ( produce ["q" ; "pa"; "n" + "n"] );; (* || *) consume ["q" ; "ca"; "n"]
  .

(** Sequential produce-consume. *)
Definition produce_consume_seq : val :=
  λ: ["q"; "pa"; "ca"; "n"],
    produce ["q" ; "pa"; "n"] ;; consume ["q" ; "ca"; "n"]
  .
End code.
