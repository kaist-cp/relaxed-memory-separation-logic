From iris.algebra Require Import excl.
From iris.base_logic Require Import lib.own.
From iris.proofmode Require Import proofmode monpred.

From gpfsl.base_logic Require Import vprop.

Require Import iris.prelude.options.

Class uniqTokG Σ := UniqTokG {
  uniq_tokG : inG Σ (exclR unitO);
}.
Local Existing Instances uniq_tokG.

Definition uniqTokΣ : gFunctors := #[GFunctor (constRF (exclR unitO))].

Global Instance subG_uniqTokΣ {Σ} : subG uniqTokΣ Σ → uniqTokG Σ.
Proof. solve_inG. Qed.

Section Tok.
Context `{!uniqTokG Σ}.
Notation vProp := (vProp Σ).

Implicit Type (γ : gname).

Definition UTok_def γ : vProp := ⎡ own γ (Excl ()) ⎤%I.
Definition UTok_aux : seal (@UTok_def). Proof. by eexists. Qed.
Definition UTok := unseal (@UTok_aux).
Definition UTok_eq : @UTok = _ := seal_eq _.

#[global] Instance UTok_timeless γ : Timeless (UTok γ).
Proof. rewrite UTok_eq. apply _. Qed.

#[global] Instance UTok_affine γ : Affine (UTok γ).
Proof. rewrite UTok_eq. apply _. Qed.

#[global] Instance UTok_objective γ : Objective (UTok γ).
Proof. rewrite UTok_eq. apply _. Qed.

Lemma UTok_alloc_cofinite (G : gset gname) : ⊢ (|==> ∃ γ, ⌜γ ∉ G⌝ ∧ UTok γ : vProp)%I.
Proof.
  iStartProof.
  iMod (own_alloc_cofinite (Excl ()) G) as (γ) "[% U]"; [done|].
  iIntros "!>". iExists γ. rewrite UTok_eq. by iFrame "%∗".
Qed.

Lemma UTok_alloc : ⊢ (|==> ∃ γ, UTok γ : vProp)%I.
Proof.
  iStartProof. iMod (UTok_alloc_cofinite ∅) as (γ) "[_ U]".
  iIntros "!>". by iExists _.
Qed.

Lemma UTok_unique γ : UTok γ -∗ UTok γ -∗ False.
Proof.
  rewrite UTok_eq. iIntros "U1 U2".
  by iCombine "U1 U2" gives %?.
Qed.
End Tok.
