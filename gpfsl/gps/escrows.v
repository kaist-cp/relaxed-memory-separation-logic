From iris.base_logic.lib Require Import own invariants.
From iris.proofmode Require Import proofmode.

From gpfsl.base_logic Require Import vprop.

Require Import iris.prelude.options.

Definition escrowN : namespace := nroot .@ "gps" .@ "escrow".

Section Escrows.
  Context `{invGS Σ}.
  Local Notation vProp := (vProp Σ).

  Program Definition escrow_def (P Q: vProp) : vProp :=
    MonPred (λ V, ∃ V0, ⌜V0 ⊑ V⌝ ∗ inv escrowN ((∃ V1, P V1) ∨ Q V0))%I _.
  Next Obligation. solve_proper. Qed.
  Definition escrow_aux : seal (@escrow_def). Proof. by eexists. Qed.
  Definition escrow := unseal (@escrow_aux).
  Definition escrow_eq : @escrow = _ := seal_eq _.

End Escrows.

Notation "[es P ⇝ Q ]" := (escrow P Q)
  (at level 99, format "[es  P  ⇝  Q ]"): bi_scope.

Section proof.
  Context `{invGS Σ}.
  Global Instance escrow_persistent P Q : Persistent ([es P ⇝ Q]).
  Proof. rewrite /Persistent escrow_eq. iStartProof (iProp _). by iIntros (?) "#?". Qed.

  Global Instance escrow_proper :
    Proper ((≡) ==> (≡) ==> (≡)) (escrow).
  Proof. rewrite escrow_eq. constructor. solve_proper. Qed.
  Global Instance escrow_contractive n :
    Proper (dist_later n ==> dist_later n ==> dist n) escrow.
  Proof. move => ??????. rewrite escrow_eq. constructor => ?. solve_contractive. Qed.
  Global Instance escrow_ne n :
    Proper (dist n ==> dist n ==> dist n) escrow.
  Proof. intros ??????. rewrite escrow_eq. constructor => ?. solve_proper. Qed.

  Lemma escrow_alloc P Q E:
    ↑escrowN ⊆ E → ▷ Q ={E}=∗ [es P ⇝ Q].
  Proof.
    iIntros (?). rewrite escrow_eq. iStartProof (iProp _).
    iIntros (V) "Q". iExists V. iSplitL ""; [done|].
    iApply inv_alloc. iNext. by iRight.
  Qed.

  Lemma escrow_elim P Q E:
    ↑escrowN ⊆ E → (P ∗ P → False) ⊢ [es P ⇝ Q] -∗ ▷ P ={E}=∗ ▷ Q.
  Proof.
    iIntros (?). rewrite escrow_eq. iStartProof (iProp _).
    iIntros (?) "ND". iIntros (? ->) "Es". iIntros (V ->) "P".
    iDestruct "Es" as (V0) "[%Ext Inv]".
    iInv escrowN as "inv" "HClose".
    iAssert (▷ (Q V0 ∗ ((∃ V1, P V1) ∨ Q V0)))%I with "[ND P inv]" as "[Q inv]".
    { iNext. iDestruct "inv" as "[inv|$]".
      - iExFalso. iDestruct "inv" as (V1) "P1".
        rewrite {1}(monPred_mono _ _ _ (lat_join_sqsubseteq_l V V1)).
        by iApply ("ND" with "[$P $P1]").
      - iLeft. by iExists _. }
    iMod ("HClose" with "inv") as "_". by iFrame "Q".
  Qed.

End proof.
