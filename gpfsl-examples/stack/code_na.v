From gpfsl.lang Require Export notation.
From gpfsl.logic Require Import new_delete.

Notation next := 0 (only parsing).
Notation data := 1 (only parsing).

Definition new_stack : val :=
  λ: [], let: "s" := new [ #1] in "s" <- #0 ;; "s".

Definition push : val :=
  λ: ["s" ; "x"],
    let: "n" := new [ #2] in
    "n" +ₗ #data <- "x" ;;
    let: "h" := !"s" in
    "n" +ₗ #next <- "h";;
    "s" <- "n"
  .

Definition pop : val :=
  λ: ["s"],
    let: "h" := !"s" in
    if: "h" = #0
    then #0
    else
      let: "v"  := !("h" +ₗ #data) in
      let: "h'" := !("h" +ₗ #next) in
      "s" <- "h'" ;;
      delete [ #2; "h"] ;;
      "v"
  .
