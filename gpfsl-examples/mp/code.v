From gpfsl.lang Require Export notation.
From gpfsl.logic Require Import repeat_loop new_delete.

(** Message-Passing example with Release-Acquire *)

Notation flag := 0 (only parsing).
Notation data := 1 (only parsing).

Definition mp : expr :=
  let: "m" := new [ #2] in
  "m" +ₗ #flag <- #0 ;;
  "m" +ₗ #data <- #0 ;;
  Fork                              ("m" +ₗ #data <- #42 ;;
                                     "m" +ₗ #flag <-ʳᵉˡ #1)
  ;;
  (repeat: !ᵃᶜ("m" +ₗ #flag)) ;;
  !("m" +ₗ #data).

Definition mp_reclaim : expr :=
  let: "m" := new [ #2] in
  "m" +ₗ #flag <- #0 ;;
  "m" +ₗ #data <- #0 ;;
  Fork                              ("m" +ₗ #data <- #42 ;;
                                     "m" +ₗ #flag <-ʳᵉˡ #1)
  ;;
  (repeat: !ᵃᶜ("m" +ₗ #flag)) ;;
  let: "v" := !("m" +ₗ #data) in
  (* reclaim *)
  delete [ #2; "m"] ;;
  "v".
