From gpfsl.lang Require Export notation.
From gpfsl.logic Require Import repeat_loop new_delete.

Notation empty := 0 (only parsing).
Notation tseq := 0 (only parsing).
Notation data := 1 (only parsing).

Section singleElementQueue.
Variables (newTS waitForTurn completeTurn : val).

Definition newSEQ : val :=
  λ: [],
    let: "q" := new [ #2] in
    "q" +ₗ #data <- #empty;;
    "q" +ₗ #tseq <- newTS [];;
    "q".

Definition enqueueWithTicket : val :=
  λ: ["this"; "ticket"; "v"],
    let: "t" := ! ("this" +ₗ #tseq) in
    let: "r" := "this" +ₗ #data in
    let: "turn" := "ticket" * #2 in
    waitForTurn ["t"; "turn"];;
    "r" <- "v";;
    completeTurn ["t"; "turn"].

Definition dequeueWithTicket : val :=
  λ: ["this"; "ticket"],
    let: "t" := ! ("this" +ₗ #tseq) in
    let: "r" := "this" +ₗ #data in
    let: "turn" := "ticket" * #2 + #1 in
    waitForTurn ["t"; "turn"];;
    let: "v" := ! "r" in
    "r" <- #empty;;
    completeTurn ["t"; "turn"];;
    "v".

End singleElementQueue.
