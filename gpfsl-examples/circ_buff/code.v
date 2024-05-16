From gpfsl.lang Require Export notation.
From gpfsl.logic Require Import new_delete.

Notation wi := 0 (only parsing).
Notation ri := 1 (only parsing).
Notation b := 2 (only parsing).

Section Code.
Context (Ns: nat) (* size of the buffer *).

Definition new_buffer : val :=
  λ: [],
    let: "q" := new [ #Ns + #b] in
      "q" +ₗ #ri <- #0 ;;
      "q" +ₗ #wi <- #0 ;;
      "q"
  .

Definition try_prod : val :=
  λ: ["q"; "x"],
    let: "w" := !ᵃᶜ ("q" +ₗ #wi) in
    let: "r" := !ᵃᶜ ("q" +ₗ #ri) in
    let: "w'" := ("w" + #1) `mod` #Ns in
      if: "w'" = "r"
      then #0
      else
        "q" +ₗ (#b + "w") <- "x" ;;
        "q" +ₗ #wi <-ʳᵉˡ "w'" ;;
        #1
  .

Definition try_cons : val :=
  λ: ["q"],
    let: "w" := !ᵃᶜ ("q" +ₗ #wi) in
    let: "r" := !ᵃᶜ ("q" +ₗ #ri) in
      if: "w" = "r"
      then #0
      else
        let: "x" := ! ("q" +ₗ (#b + "r")) in
          "q" +ₗ #ri <-ʳᵉˡ  (("r" + #1) `mod` #Ns) ;;
          "x"
  .
End Code.
