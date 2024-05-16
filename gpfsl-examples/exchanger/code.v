From gpfsl.lang Require Import notation.
From gpfsl.logic Require Import new_delete.

Notation hole := 0 (only parsing).
Notation data := 1 (only parsing).
Notation NULL := 0 (only parsing).
Notation MATCHING := 0 (only parsing).
Notation CANCELLED := (-1) (only parsing).

(* exchanges non-negative integers; return #-1 if cancelled *)
(* The state of the exchanger is NULL <-> OFFER (l : loc). *)
Definition new_exchanger : val :=
  λ: [],
    let: "ex" := new [ #1] in
    "ex" <- #NULL ;; (* published offer, initially Null *)
    "ex".

(* The state of a hole is
  Inductive HoleState :=
    | MATCHING | CANCELLED | ACCEPTED (other : loc) | ACKED (other : loc) .
  State transition:
    MATCHING -> CANCELLED      : self action to cancel
    MATCHING -> ACCEPTED other : other action to match
    ACCEPTED other -> ACKED other : self action to acknowledge the offer *)
Definition exchange : val :=
  λ: ["ex"; "x"],
    (* prepare an offer called mine *)
    let: "mine" := new [ #2] in
    "mine" +ₗ #hole <- #MATCHING;;  (* hole *)
    "mine" +ₗ #data <- "x";;        (* data *)
    (* try publishing mine as the main offer *)
    if: casʳᵉˡ("ex", #NULL, "mine")
    then ( (* successfully published mine as the main offer *)
      (* *sleep* *)
      (* check if there's any matched sub offer *)
      if: casʳˡˣ("mine" +ₗ #hole, #MATCHING, #CANCELLED)
      then (* no matched! Failed. We can reclaim data. But what about the hole? *)
        #CANCELLED (* CANCEL_CASE 1 *)
      else (
        (* read the matched sub offer with acquire, name it other *)
        let: "other" := !ᵃᶜ("mine" +ₗ #hole) in
        !("other" +ₗ #data)
      )
    )
    else ( (* failed. there is already a main offer, try to accept it *)
      (* try accepting the main offer as other *)
      let: "other" := !ᵃᶜ"ex" in
      if: "other" = #NULL
      then ( (* something racy is going on, failed. *)
        delete [ #2; "mine"] ;; (* we can actually reclaim, because we fail to publish anything *)
        #CANCELLED (* CANCEL_CASE 2 *)
      )
      else (
        (* try to match the main offer (other) with my offer (mine) as the sub offer *)
        let: "ok" := casʳᵉˡ("other" +ₗ #hole, #MATCHING, "mine") in
        (* clean up regardless of the result. If we fail here nothing wrong can happen. *)
        casʳˡˣ("ex", "other", #NULL) ;;
        if: "ok"
        (* managed to match, can read the main offer (other) *)
        then !("other" +ₗ #data) (* we can safely read because we used an acq
                                    read on `"ex"` previously. *)
        else (
        (* fail to match *)
          delete [ #2; "mine"] ;; (* we can actually reclaim, because we fail to publish anything *)
          #CANCELLED (* CANCEL_CASE 3 *)
        )
      )
    )
  .
