From gpfsl.lang Require Import notation.
From gpfsl.logic Require Import new_delete.

Notation hole := 0 (only parsing).
Notation data := 1 (only parsing).
Notation NULL := 0 (only parsing).
Notation MATCHING := (-1) (only parsing).
Notation CANCELLED := (-1) (only parsing).
Notation CANCELLEDval := (-2) (only parsing).

(* Fine-grained version of exchanger in [gpfsl-examples/exchanger/code.v] that splits [exchange] function into three parts *)

Definition new_exchanger : val :=
  λ: [],
    let: "ex" := new [ #1] in
    "ex" <- #NULL ;; (* published offer, initially Null *)
    "ex".

(* Registers a new offer in the exchanger *)
Definition new_offer : val :=
  λ: ["ex"; "x"],
    (* prepare an offer called mine *)
    let: "mine" := new [ #2] in
    "mine" +ₗ #hole <- #MATCHING;;  (* hole *)
    "mine" +ₗ #data <- "x";;        (* data *)
    (* try publishing mine as the main offer *)
    if: casʳᵉˡ("ex", #NULL, "mine")
    then "mine" (* successfully published mine as the main offer *)
    else (
      delete [ #2; "mine"] ;;
      #NULL
    ).

(* After registering an offer, check whether the offer is taken by other thread *)
Definition check_offer : val :=
  λ: ["ex"; "mine"],
    if: casʳˡˣ("mine" +ₗ #hole, #MATCHING, #CANCELLEDval)
    then (* no matched! Failed. We can reclaim data. But what about the hole? *)
      #CANCELLED
    else (
      (* read the matched sub offer with acquire *)
      !ᵃᶜ("mine" +ₗ #hole)
    ).

(* Try exchanging with existing offer *)
Definition take_offer : val :=
  λ: ["ex"; "x"],
    let: "other" := !ᵃᶜ"ex" in
    if: "other" = #NULL
    then ( (* something racy is going on, failed. *)
      #CANCELLED
    )
    else (
      (* try to match the main offer (other) with my offer [x] as the sub offer *)
      let: "ok" := casʳᵉˡ("other" +ₗ #hole, #MATCHING, "x") in
      (* clean up regardless of the result. If we fail here nothing wrong can happen. *)
      casʳˡˣ("ex", "other", #NULL) ;;
      if: "ok"
      (* managed to match, can read the main offer (other) *)
      then !("other" +ₗ #data) (* we can safely read because we used an acq
                                 read on `"ex"` previously. *)
      else (
      (* fail to match *)
        #CANCELLED
      )
    ).
