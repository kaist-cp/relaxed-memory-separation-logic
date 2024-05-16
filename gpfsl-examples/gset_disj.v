From iris.algebra Require Import excl gset auth.
From iris.base_logic Require Import lib.own.
From iris.proofmode Require Import tactics.

From gpfsl.base_logic Require Import vprop.

Require Import iris.prelude.options.

Definition gset_disjAR A `{Countable A} := authR $ gset_disjUR A.

Class gset_disjARG Σ A `{Countable A} := GsetDisjAG {
  gset_disjRG : inG Σ (gset_disjAR A);
}.
Local Existing Instance gset_disjRG.
Definition gset_disjARΣ A `{Countable A} : gFunctors := #[GFunctor (constRF (gset_disjAR A))].

Global Instance subG_gset_disjARΣ {Σ A} `{Countable A} :
  subG (gset_disjARΣ A) Σ → gset_disjARG Σ A.
Proof. solve_inG. Qed.

Section gset_disj.
Context {Σ A} `{Countable A} `{gset_disjARG Σ A}.
Notation vProp := (vProp Σ).

Implicit Type (γ : gname) (a b : A) (X : gset A).

Definition GsetDisjAuth γ q X : vProp := ⎡ own γ (●{#q} (GSet X)) ⎤.
Definition GsetDisjFrag γ a : vProp := ⎡ own γ (◯ (GSet {[a]})) ⎤.

#[global] Instance GsetDisjAuth_timeless γ q X : Timeless (GsetDisjAuth γ q X) := _.
(* Proof. rewrite GsetDisjAuth_eq. apply _. Qed. *)

#[global] Instance GsetDisjAuth_affine γ q X : Affine (GsetDisjAuth γ q X) := _.
(* Proof. rewrite GsetDisjAuth_eq. apply _. Qed. *)

#[global] Instance GsetDisjAuth_objective γ q X  : Objective (GsetDisjAuth γ q X) := _.
(* Proof. rewrite GsetDisjAuth_eq. apply _. Qed. *)

#[global] Instance GsetDisjFrag_timeless γ a : Timeless (GsetDisjFrag γ a) := _.
(* Proof. rewrite GsetDisjFrag_eq. apply _. Qed. *)

#[global] Instance GsetDisjFrag_affine γ a : Affine (GsetDisjFrag γ a) := _.
(* Proof. rewrite GsetDisjFrag_eq. apply _. Qed. *)

#[global] Instance GsetDisjFrag_objective γ a : Objective (GsetDisjFrag γ a) := _.
(* Proof. rewrite GsetDisjFrag_eq. apply _. Qed. *)

Lemma GsetDisjAuth_alloc : ⊢ |==> ∃ γ, GsetDisjAuth γ 1 ∅.
Proof.
  iMod own_alloc as (γ) "GA"; last first.
  { iExists γ. by iFrame "GA". }
  by apply auth_auth_valid.
Qed.

Lemma GsetDisjAuth_frag_include γ q X a :
  GsetDisjAuth γ q X -∗ GsetDisjFrag γ a -∗ ⌜ a ∈ X ⌝.
Proof.
  iIntros "o1 o2".
  iCombine "o1 o2" gives
    %[? [INCL%gset_disj_included%elem_of_subseteq_singleton ?]]%auth_both_dfrac_valid_discrete.
  done.
Qed.

Lemma GsetDisjAuth_insert γ X a :
  a ∉ X →
  GsetDisjAuth γ 1 X ==∗ GsetDisjAuth γ 1 ({[a]} ∪ X) ∗ GsetDisjFrag γ a.
Proof.
  intros NI. rewrite -embed_sep -own_op.
  iIntros "o". iMod (own_update with "o") as "$"; [|done].
  apply auth_update_alloc, gset_disj_alloc_empty_local_update.
  set_solver.
Qed.

Lemma GsetDisjAuth_insert2 γ X a b :
  a ∉ X → b ∉ X → a ≠ b →
  GsetDisjAuth γ 1 X ==∗ GsetDisjAuth γ 1 ({[a; b]} ∪ X) ∗ GsetDisjFrag γ a ∗ GsetDisjFrag γ b.
Proof.
  intros NI1 NI2 NEq.
  rewrite -2!embed_sep -2!own_op -auth_frag_op gset_disj_union; [|set_solver+NEq].
  iIntros "o". iMod (own_update with "o") as "$"; [|done].
  apply auth_update_alloc, gset_disj_alloc_empty_local_update.
  set_solver.
Qed.

Lemma GsetDisjFrag_disj γ a b :
  GsetDisjFrag γ a -∗ GsetDisjFrag γ b -∗ ⌜ a ≠ b ⌝.
Proof.
  iIntros "o1 o2".
  iCombine "o1 o2" gives %VALID%auth_frag_valid_1%gset_disj_valid_op.
  iPureIntro. set_solver.
Qed.
End gset_disj.
