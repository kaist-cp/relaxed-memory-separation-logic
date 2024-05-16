From gpfsl.lang Require Export notation.
From gpfsl.logic Require Import
  repeat_loop new_delete atomic_exchange diverge arith.

Notation back := 0 (only parsing).
Notation buff := 1 (only parsing).

(* Herlihy-Wing queue *)
(* We assume a finite buffer. *)
Section HW_queue.
  Context (N : positive). (* Assuming a syntactic, fixed length of the buffer. *)

  Definition new_queue : val :=
    λ: [],
      (* allocate a buffer of max length N, with the current length store in
        the back fill *)
      let: "q" := new [ #(Z.pos N) + #1] in
      (* loop to initialize everything to 0, conveniently use the back field as
        the counter *)
      "q" +ₗ #back <- #0 ;;
      (repeat: (* repeat ... *)
        let: "c" := !("q" +ₗ #back) in
        "q" +ₗ (#buff + "c") <- #0 ;; (* initialize the buffer's index "c" to 0 *)
        "q" +ₗ #back <- "c" + #1 ;; (* increment the counter *)
        "c" + #1 = #(Z.pos N) (* until the counter is equal to N *)
      ) ;;
      "q" +ₗ #back <- #0 ;; (* reset back field *)
      (* end loop *)
      "q"
    .

  (* Enqueue can fail, but only when the buffer is full, and there's no way to
    clear the buffer, so all subsequent enqueues will fail.
    Here, we make the function diverge in the failure case, so no proof obligation. *)
  Definition enqueue : val :=
    λ: ["q"; "v"],
      let: "i" := FAAʳᵉˡ("q" +ₗ #back, #1) in (* a release FAA *)
      if: "i" < #(Z.pos N) (* check if the buffer is full *)
      then "q" +ₗ (#buff + "i") <-ʳᵉˡ "v" (* if not full, release the value *)
      else diverge [ #☠ ]
    .

  Definition dequeue_loop (weakHW : bool) : val :=
    λ: ["dequeue"; "q"; "range"],
      rec: "loop" ["i"] :=
        (* internal loop, encoded as the recursion of "loop",
          with i decreasing from "range" to 0, but doesn't include 0, i.e.
          0 < i ≤ range *)
        if: "i" = #0
        then "dequeue" ["q"] (* when "i" is 0, go back to the external loop *)
        else
          (* so the actual index is "j", which is 0 ≤ j < range *)
          let: "j" := "range" - "i" in
          (* weak HW queue uses an acq XCHG, strong one uses a rel-acq XCHG *)
          let: "x" := XCHG AcqRel (if weakHW then Relaxed else AcqRel)
                           ["q" +ₗ (#buff + "j"); #0] in
          if: "x" = #0
          then "loop" ["i" - #1]
          else "x"
    .

  (* Dequeue also only fails when the buffer is full.
    Here, we make the function diverge in the failure case, so no proof obligation. *)
  Definition dequeue (weakHW : bool) : val :=
    rec: "dequeue" ["q" ] :=
      (* external loop, encoded as the recursion of "dequeue" *)
      let: "range" := minimum [ !ᵃᶜ ("q" +ₗ #back) ; #(Z.pos N)] in
      (* we know that 0 ≤ range ≤ N, so there can't be out-of-bound access *)
      dequeue_loop weakHW ["dequeue"; "q" ; "range"] ["range"]
    .
End HW_queue.
