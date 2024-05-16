From gpfsl.lang Require Export notation.
From gpfsl.logic Require Import new_delete.

(** Chase-Lev work-stealing queue: A simplified version. *)

(** See the original paper:
  [1] Dynamic Circular Work-Stealing Deque, David Chase and Yossi Lev, SPAA'05.
  https://dl.acm.org/doi/10.1145/1073970.1073974
  Also, the weak-memory (C11 and ARMv7) version:
  [2] Correct and Efficient Work-Stealing for Weak Memory Models, Lê et al.,
  PPoPP'13. https://dl.acm.org/doi/10.1145/2442516.2442524 *)

(* The original version uses dynamic array a circular array as the underlying
  storage for the queue. Once a position in the array has been stolen, it can be
  reused for the coming push's.
  Furthemore, the array can grow and shrink dynamically---only when the array is
  completely full, it will be resized by reallocation. *)

(** In this implementation, we make a drastic simplification:
  - the array is fixed-size
  - the array is non circular
  Therefore, once the last position of the array is used, further push's will
  fail.
  This simplification can be lifted by building an abstract circular array that
  can grow:
  - the circular array provides abstract indexes will always be modulo-ed the
    size s of the underlying buffer to get the correct physical indexes.
  - the circular array offers a "grow" function that allocates a bigger array
    and then copies the elements to that new array, while maintaining the
    abstract indexes (but not physical indexes).
  - the circular array my offer also a "shrink" function.
  - this array can be implemented with non-atomics: the synchronizations by the
    Chase-Lev queue itself should be enough to eliminate any possible UB
    non-atomic) races.
    -->> actually, it may not be so easy to allow concurrent reads of the
    underlying array while we want to grow and also to reclaim it. This is also
    discussed in Section 4 of [1], which may give some solution.
  *)

Notation bot := 0 (only parsing).
Notation top := 1 (only parsing).
Notation b := 2 (only parsing).
Notation NONE := (-1)%Z (only parsing).

Section Code.
Context (Ns: Z) (* size of the buffer *).

Definition cl_new : val :=
  λ: [],
    (* Ns + 2 cells: first the bot counter, then top counter, then the buffer
      of size Ns *)
    let: "q" := new [ #Ns + #b] in
      "q" +ₗ #bot <- #0 ;;
      "q" +ₗ #top <- #0 ;;
      "q".

Definition cl_push : val :=
  λ: ["q"; "x"],
    let: "b" := !ʳˡˣ ("q" +ₗ #bot) in
    "q" +ₗ (#b + "b") <- "x" ;;
    "q" +ₗ ("q" +ₗ #bot) <-ʳᵉˡ ("b" + #1)
    .

Definition cl_steal : val :=
  λ: ["q"],
    let: "t" := !ʳˡˣ ("q" +ₗ #top) in
    FenceSC ;;
    let: "b" := !ᵃᶜ ("q" +ₗ #bot) in
    if: ("b" - "t") ≤ #0
    then #NONE
    else
      (* Relaxed CAS is good enough because we already synchronized using the
        acquire read of b above. *)
      if: casʳˡˣ("q" +ₗ #top, "t", "t" + #1)
      then ! ("q" +ₗ (#b + "t"))
      else #NONE
    .

Definition cl_try_pop : val :=
  λ: ["q"],
    let: "b" := !ʳˡˣ ("q" +ₗ #bot) in
    ("q" +ₗ #bot) <-ʳˡˣ ("b" - #1) ;;
    FenceSC ;;
    let: "t" := !ᵃᶜ ("q" +ₗ #top) in
    if: ("b" - "t") ≤ #0
    then ("q" +ₗ #bot) <-ʳˡˣ "b" ;; #NONE
    else
      if: #2 ≤ ("b" - "t")
      then ! ("q" +ₗ (#b + ("b" - #1)))
      else (* b - t = 1 *)
        let: "s" := casʳˡˣ("q" +ₗ #top, "t", "t" + #1) in
        ("q" +ₗ #bot) <-ʳˡˣ "b" ;;
        if: "s"
        then ! ("q" +ₗ (#b + "t"))
        else #NONE
    .
End Code.
