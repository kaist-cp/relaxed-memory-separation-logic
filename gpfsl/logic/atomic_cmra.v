From iris.algebra Require Export auth gmap agree lib.frac_auth.

From gpfsl.algebra Require Import to_agree.
From gpfsl.lang Require Import notation.
From gpfsl.base_logic Require Import history.

Require Import iris.prelude.options.

Definition absHist := gmap time (val * view).

(* Master-snapshot-style CMRA for histories *)
Definition histBaseUR : ucmra := agreeMR time (val * view).
Definition histMSR    :  cmra := authUR $ histBaseUR.
(* CMRA for the exclusive write *)
Definition exWriteR : cmra := frac_authR $ (agreeR positiveO).
(* cmra for the last non-atomic write *)
Definition naWriteR : cmra := optionR $ agreeR $ leibnizO view.
(* the real one *)
Definition atomicR  : cmra := prodR histMSR (prodR exWriteR naWriteR).

Class atomicG Σ := { atomic_inG : inG Σ atomicR; }.
Local Existing Instance atomic_inG.
Definition atomicΣ : gFunctors := #[ GFunctor (constRF atomicR) ].
Global Instance subG_atomicΣ {Σ} : subG atomicΣ Σ → atomicG Σ.
Proof. solve_inG. Qed.

Definition toHistBaseUR : absHist → histBaseUR := to_agreeM.

Lemma toHistBase_included ζ1 ζ2 : ζ1 ⊆ ζ2 ↔ toHistBaseUR ζ1 ≼ toHistBaseUR ζ2.
Proof. symmetry. apply to_agreeM_included. Qed.

Lemma toHistBase_inj ζ1 ζ2 : toHistBaseUR ζ1 ≡ toHistBaseUR ζ2 → ζ1 = ζ2.
Proof. apply to_agreeM_agree. Qed.

Lemma histBase_idemp (ζ : histBaseUR) : ζ ⋅ ζ ≡ ζ.
Proof. by apply agreeM_idemp. Qed.

(* the side condition is needed to guarantee that ζ1 ∪ ζ2 = ζ2 ∪ ζ1. *)
Lemma toHistBase_op_valid ζ1 ζ2 :
  ✓ (toHistBaseUR ζ1 ⋅ toHistBaseUR ζ2) →
  toHistBaseUR ζ1 ⋅ toHistBaseUR ζ2 ≡ toHistBaseUR (ζ1 ∪ ζ2).
Proof. apply to_agreeM_op_valid. Qed.

Lemma toHistBase_valid ζ: ✓ toHistBaseUR ζ.
Proof. apply to_agreeM_valid. Qed.

Lemma toHistBase_valid_union ζ1 ζ2 :
  ✓ (toHistBaseUR ζ1 ⋅ toHistBaseUR ζ2) → ζ1 ∪ ζ2 = ζ2 ∪ ζ1.
Proof. apply to_agreeM_valid_union. Qed.

Lemma toHistBase_local_update ζ ζ' (ζ0: histBaseUR) :
  ζ ⊆ ζ' → (toHistBaseUR ζ, ζ0) ~l~> (toHistBaseUR ζ', toHistBaseUR ζ').
Proof. by apply to_agreeM_local_update. Qed.

Lemma toHistBase_local_update_insert ζ ζ' t vV :
  ζ !! t = None →
  (toHistBaseUR ζ, toHistBaseUR ζ') ~l~>
  (toHistBaseUR (<[t := vV]>ζ), toHistBaseUR (<[t := vV]>ζ')).
Proof. apply to_agreeM_local_update_insert. Qed.

Lemma toHistBase_local_update_fork ζ ζ' ζ0 :
  ζ0 ⊆ ζ' → ζ' ⊆ ζ →
  (toHistBaseUR ζ, toHistBaseUR ζ0) ~l~> (toHistBaseUR ζ, toHistBaseUR ζ').
Proof. apply to_agreeM_local_update_fork. Qed.
