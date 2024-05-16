From gpfsl.lang Require Export notation.
From gpfsl.logic Require Import repeat_loop new_delete.

Notation ns := 0 (only parsing).
Notation tc := 1 (only parsing).

Section code.
  Context (C: positive).
  Definition new_lock : val :=
    λ: [],
      let: "x" := new [ #2] in
        "x" +ₗ #ns <- #0 ;;
        "x" +ₗ #tc <- #0 ;;
        "x"
    .

  Definition FAIm : val :=
    rec: "FAI" ["x"] :=
      let: "i"  := !ʳˡˣ "x" in
      let: "i'" := ("i" + #1) `mod` #(Z.pos C) in
        if: casʳᵃ("x", "i", "i'")
        then "i"
        else "FAI" ["x"]
    .

  Definition lock : val :=
    λ: ["x"],
      let: "y" := FAIm [ ("x" +ₗ #tc)] in
      (repeat: (let: "z" := !ᵃᶜ ("x" +ₗ #ns) in "y" = "z"))
    .

  Definition unlock : val :=
    λ: ["x"],
      let: "z" := !ʳˡˣ ("x" +ₗ #ns) in
      "x" +ₗ #ns <-ʳᵉˡ ("z" + #1) `mod` #(Z.pos C)
    .
End code.
