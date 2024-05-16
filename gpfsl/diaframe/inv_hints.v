From iris.proofmode Require Import proofmode.
From diaframe Require Import proofmode_base.

(* From iris.base_logic Require Import invariants. *)
From gpfsl.logic Require Import invariants.
From diaframe.lib Require Import except_zero.


(* This file is the gpfsl version of diaframe's 'iris_hints.v' *)


Section biabd_gpfsl_instances.
  Context `{!invGS Σ}.

  (* TODO: LaterToExcept0 is slow! Sometimes takes about 0.1-0.07 seconds to find an instance.
      This is because it recurses inside P. This is annoying, since this cost is also incurred if
      we later detect that we could not open the invariant anyway *)
  Global Instance inv_objective_into_wand P N E P' :
    Objective P →
    LaterToExcept0 P P' →
    IntoWand2 true (inv N P) (* (cfupd (↑ N) E E)*)
                              (* the diamond below prevents automation from recursing into the wand *)
      (⌜↑N ⊆ E⌝) (* -∗ *) (cfupd (↑ N) E (E ∖ ↑ N) (*|={E, E ∖ ↑ N}=> *) (P' ∗ ◇ (▷ P ={E ∖ ↑N, E}=∗ χ)))%I.
  (* if laterToExcept0 was stronger (▷ P ⊣⊢ ⋄P') we would have also been able to replace
      ▷ P in (▷P ={...}=∗ ..) with P'. But that makes things harder to prove, while replacing the
    first occurence makes our system stronger. *)
    (* we should, but cant use AtomIntoWand, since it requires a coPset argument which we actually do not need *)
    (* This used to be an IntoWand2 instance, but the prefixed fancy update enforces unification of E at the correct moment. *)
    (* TODO: Is AtomIntoModal missing? *)
  Proof.
    rewrite /IntoWand2 /IntoModal bi.intuitionistically_if_elim /LaterToExcept0 => obj_p HP.
    iSteps as (HNE) "HN".
    rewrite cfupd_eq. (* iStep.*)
    rewrite inv_acc // {1}HP.
    iMod "HN" as "[>HP HPacc]".
    iSteps. rewrite empty_goal_eq.
    iIntros "!> !> HP". by iMod ("HPacc" with "HP").
  Qed.

  Global Instance inv_atom_and_connective p P N : AtomAndConnective p (inv N P).
  Proof. by split. Qed.

  (* abduction hints rely on above, for biabd we need below *)
  Global Instance inv_into_connective P N P' :
    Objective P →
    LaterToExcept0 P P' →
    AtomIntoConnective (inv N P) (* (cfupd (↑ N) E E)*)
                              (* the diamond below prevents automation from recursing into the wand *)
      (∀ E, ⌜↑N ⊆ E⌝ -∗ (cfupd (↑ N) E (E ∖ ↑ N) (*|={E, E ∖ ↑ N}=> *) (P' ∗ ◇ (▷ P ={E ∖ ↑N, E}=∗ χ)))%I).
  Proof.
    rewrite /AtomIntoConnective /LaterToExcept0 => HP HP2.
    rewrite cfupd_eq. iStep 3 as (E HNE) "HI".
    iMod (inv_acc with "HI") as "HI'"; first done.
    rewrite {1}HP2.
    iDestruct "HI'" as "[>HP HPacc]".
    iSteps. iIntros "!> !> HP". rewrite empty_goal_eq.
    by iMod ("HPacc" with "HP").
  Qed.

  Global Arguments difference : simpl never.

  Global Instance bi_abduct_inv_objective P N E :
    Objective P →
    HINT ε₁ ✱ [- ; ▷ P] ⊫ [fupd E E]; inv N P ✱ [inv N P].
  Proof.
    intros. iStep. rewrite inv_alloc. iSteps.
  Qed.
End biabd_gpfsl_instances.


Global Hint Extern 10 (BehindModal (fupd ?El ?Er) (↑?N ⊆ ?Er)) =>
  unify El Er; unfold BehindModal; pure_solver.trySolvePure : solve_pure_add.


