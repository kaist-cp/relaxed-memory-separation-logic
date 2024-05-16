From gpfsl.lang Require Export notation.
From gpfsl.logic Require Import repeat_loop new_delete.


Section code.

  Definition new_lock : val :=
    λ: [],
      let: "x" := new [ #1] in
        "x" <- #0 ;;
        "x"
    .

  Definition do_lock : val :=
    λ: ["x"],
      (repeat: casᵃᶜ("x", #0, #1));; #☠ .

  Definition try_lock : val :=
    λ: ["x"],
      casᵃᶜ("x", #0, #1).

  Definition unlock: val :=
    λ: ["x"], "x" <-ʳᵉˡ #0;; #☠.

End code.