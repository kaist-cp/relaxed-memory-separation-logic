From gpfsl.lang Require Export notation.
From gpfsl.logic Require Import repeat_loop new_delete atomic_exchange.

Notation enq := 0 (only parsing).
Notation deq := 1 (only parsing).
Notation size := 2 (only parsing).
Notation slot := 3 (only parsing).

Section MpmcQueue.

Variables (newSEQ enqueueWithTicket dequeueWithTicket : val).

Definition initSlot : val :=
  rec: "next" ["q"; "idx"; "size"] :=
    if: "idx" = "size" then #☠
    else "q" +ₗ "idx" <- newSEQ [];;
         "next" ["q"; "idx" + #1; "size"].

Definition newQueue : val :=
  λ: ["size"],
    let: "q" := new [ "size" + #3] in
    "q" +ₗ #enq <- #0;; (* Initialize field for [enqTicket] *)
    "q" +ₗ #deq <- #0;; (* Initialize field for [deqTicket] *)
    "q" +ₗ #size <- "size";;
    initSlot ["q" +ₗ #slot; #0; "size"];; (* Initialize each slot *)
    "q".

Definition enqueue : val :=
  λ: ["q"; "v"],
    let: "ticket" := FAAʳˡˣ("q" +ₗ #enq, #1) in
    let: "size" := ! ("q" +ₗ #size) in
    let: "turn" := "ticket" `quot` "size" in
    let: "idx" := "ticket" `rem` "size" in
    let: "slot" := "q" +ₗ #slot in
    enqueueWithTicket [! ("slot" +ₗ "idx"); "turn"; "v"].

Definition dequeue : val :=
  λ: ["q"],
    let: "ticket" := FAAʳˡˣ("q" +ₗ #deq, #1) in
    let: "size" := ! ("q" +ₗ #size) in
    let: "turn" := "ticket" `quot` "size" in
    let: "idx" := "ticket" `rem` "size" in
    let: "slot" := "q" +ₗ #slot in
    (** Instead of just `dequeueWithTicket`, we temporarilty store its return value
        This is a little trick for taking one more step to remove later ▷ modality *)
    let: "ret" := dequeueWithTicket [! ("slot" +ₗ "idx"); "turn"] in
    "ret".

End MpmcQueue.
