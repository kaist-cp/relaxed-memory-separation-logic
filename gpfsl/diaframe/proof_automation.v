From iris.prelude Require Import options.

From iris.proofmode Require Export proofmode.
From diaframe Require Export proofmode_base.
From gpfsl.diaframe Require Export view_hints base_hints base_specs inv_hints.
From diaframe Require Export steps.verify_tac.

From iris.bi Require Export bi telescopes derived_laws.
From gpfsl.logic Require Export proofmode new_delete atomics invariants repeat_loop.

From gpfsl.lang Require Export notation.



(* Importing this file should give you access to Diaframe's automation,
   including required hints to automatically verify programs written in
   orc11. *)