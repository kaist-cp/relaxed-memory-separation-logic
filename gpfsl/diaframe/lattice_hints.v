From diaframe Require Import proofmode_base.
From gpfsl.logic Require Import proofmode atomics.
From orc11 Require Export weak_lat_solver.

From gpfsl.lang Require Import notation.


#[global] Arguments sqsubseteq {_} {_} _ _ : simpl never.
#[global] Typeclasses Opaque sqsubseteq.
#[global] Hint Extern 500 (@sqsubseteq ?A _ _ _) =>
  repeat (
    match goal with
    | |- context [@union ?B] =>
      change (@union B _) with (@join A _)
    end
  ); (* weak_lat_solver is very syntactic *)
  weak_lat_solver : solve_pure_add.
  (* above used to be just a call to [solve_lat].
    We [change] the syntax of the goal a bit,
    so that a call to [weak_lat_solver] should be enough *)
