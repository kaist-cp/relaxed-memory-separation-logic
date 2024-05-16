From iris.algebra Require Import gmap.

From gpfsl.lang Require Import lang.
From gpfsl.examples Require Export list_helper.

Require Import iris.prelude.options.

Definition event_id := nat.
Definition dummy_eid : event_id := O.

(** * An event view *)
Definition eView := gset event_id.

Definition set_in_bound {A} (M: eView) (E : list A)  :=
  set_Forall (λ e, is_Some (E !! e)) M.

(** * An omo event *)
Record omo_event (eventT : Type) :=
  mkOmoEvent {
    type : eventT;
    sync : view;
    eview : eView;
  }.
Arguments mkOmoEvent {_} _ _ _.
Arguments type {_} _.
Arguments sync {_} _.
Arguments eview {_} _.

Global Instance omo_event_Inhabited eventT (H : Inhabited eventT) : Inhabited (omo_event eventT) :=
  match H with
  | populate x => populate (mkOmoEvent x empty ∅)
  end.

Notation event_list eventT := (list (omo_event eventT))%type.
