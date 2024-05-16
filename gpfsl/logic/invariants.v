From iris.base_logic.lib Require Export invariants.
From iris.proofmode Require Import proofmode monpred.

From gpfsl.base_logic Require Export vprop.

Require Import iris.prelude.options.

(** Lifting of Iris invariants to vProp *)
(* TODO: at least lift to monPred of iProp *)
(* TODO: define general invariants.
  See https://gitlab.mpi-sws.org/iris/iris/-/issues/420 *)
Section defs.
Context `{invGS Σ}.
Notation vProp := (vProp Σ).
Implicit Types (N: namespace) (P Q : vProp).

Definition inv_def N P : vProp := ⎡ invariants.inv N (∀ V, P V) ⎤%I.
Definition inv_aux : seal (@inv_def). Proof. by eexists. Qed.
Definition inv := unseal (@inv_aux).
Definition inv_eq : @inv = _ := seal_eq _.

End defs.

#[global] Instance: Params (@inv) 3 := {}.
#[global] Typeclasses Opaque inv.

Section props.
Context `{invGS Σ}.
Notation vProp := (vProp Σ).
Implicit Types (N: namespace) (E: coPset) (P Q : vProp).

#[global] Instance inv_contractive N : Contractive (inv N).
Proof. rewrite inv_eq. solve_contractive. Qed.
#[global] Instance inv_ne N : NonExpansive (inv N) := _.
#[global] Instance inv_proper N : Proper ((≡) ==> (≡)) (inv N) := _.
#[global] Instance inv_persistent N P : Persistent (inv N P).
Proof. rewrite inv_eq; apply _. Qed.
#[global] Instance inv_objective N P : Objective (inv N P).
Proof. rewrite inv_eq; apply _. Qed.

Lemma inv_alloc' N E P : ▷ <obj> P ={E}=∗ inv N P.
Proof.
  iStartProof (iProp _). iIntros (V) "P".
  rewrite inv_eq monPred_objectively_unfold monPred_at_embed.
  by iMod (invariants.inv_alloc with "P") as "$".
Qed.

Lemma inv_alloc_open' N E P :
  ↑N ⊆ E → ⊢ |={E, E∖↑N}=> inv N P ∗ (▷ <obj> P ={E∖↑N, E}=∗ True).
Proof.
  intros SUB. iStartProof (iProp _). iIntros (V).
  rewrite inv_eq monPred_objectively_unfold monPred_at_embed.
  iMod (invariants.inv_alloc_open _ _ _ SUB) as "[$ Close]".
  iIntros "!>" (??). by iFrame.
Qed.

Lemma inv_acc' E N P :
  ↑N ⊆ E → inv N P ={E, E∖↑N}=∗ ▷ <obj> P ∗ (▷ <obj> P ={E∖↑N, E}=∗ True).
Proof.
  intros SUB. iStartProof (iProp _). iIntros (V) "Inv".
  rewrite inv_eq /inv_def monPred_objectively_unfold !monPred_at_embed.
  iMod (invariants.inv_acc with "Inv") as "[$ Close]"; first done.
  iIntros "!>" (??). by iFrame.
Qed.

Lemma inv_acc_strong' E N P :
  ↑N ⊆ E → inv N P ={E,E∖↑N}=∗ ▷ <obj> P ∗ ∀ E', ▷ <obj> P ={E',↑N ∪ E'}=∗ True.
Proof.
  intros SUB. iStartProof (iProp _). iIntros (V) "Inv".
  rewrite inv_eq /inv_def monPred_objectively_unfold !monPred_at_embed.
  iMod (invariants.inv_acc_strong with "Inv") as "[$ Close]"; first done.
  iIntros "!>" (???). by iFrame.
Qed.

Lemma inv_acc_timeless' E N P `{!Timeless P} :
  ↑N ⊆ E → inv N P ={E,E∖↑N}=∗ <obj> P ∗ (<obj> P ={E∖↑N,E}=∗ True).
Proof.
  intros SUB. iStartProof (iProp _). iIntros (V) "Inv".
  rewrite inv_eq /inv_def monPred_objectively_unfold !monPred_at_embed.
  iMod (invariants.inv_acc_timeless with "Inv") as "[$ Close]"; first done.
  iIntros "!>" (??). by iFrame.
Qed.

Lemma inv_alloc N E P `{!Objective P} : ▷ P ={E}=∗ inv N P.
Proof. by rewrite -inv_alloc' -objective_objectively. Qed.

Lemma inv_alloc_open N E P `{!Objective P} :
  ↑N ⊆ E → ⊢ |={E, E∖↑N}=> inv N P ∗ (▷ P ={E∖↑N, E}=∗ True).
Proof. rewrite {2}(objective_objectively P). by apply inv_alloc_open'. Qed.

Lemma inv_acc E N P `{!Objective P} :
  ↑N ⊆ E → inv N P ={E, E∖↑N}=∗ ▷ P ∗ (▷ P ={E∖↑N, E}=∗ True).
Proof.
  rewrite -{2}(monPred_objectively_elim P) {3}(objective_objectively P).
  by apply inv_acc'.
Qed.

Lemma inv_acc_strong E N P `{!Objective P} :
  ↑N ⊆ E → inv N P ={E,E∖↑N}=∗ ▷ P ∗ ∀ E', ▷ P ={E',↑N ∪ E'}=∗ True.
Proof.
  rewrite -{2}(monPred_objectively_elim P).
  setoid_rewrite (objective_objectively P) at 3. by apply inv_acc_strong'.
Qed.

Lemma inv_acc_timeless E N P `{!Objective P} `{!Timeless P} :
  ↑N ⊆ E → inv N P ={E,E∖↑N}=∗ P ∗ (P ={E∖↑N,E}=∗ True).
Proof.
  rewrite -{2}(monPred_objectively_elim P) {3}(objective_objectively P).
  by apply inv_acc_timeless'.
Qed.

#[global] Instance into_inv_inv N P : IntoInv (inv N P) N := {}.

#[global] Instance into_acc_inv' N P E:
  IntoAcc (X := unit) (inv N P)
          (↑N ⊆ E) True (fupd E (E ∖ ↑N)) (fupd (E ∖ ↑N) E)
          (λ _ : (), (▷ <obj> P)%I) (λ _ : (), (▷ <obj> P)%I) (λ _ : (), None).
Proof.
  rewrite /IntoAcc /accessor bi.exist_unit.
  iIntros (?) "#Hinv _".
  iMod (inv_acc' E with "Hinv") as "[$ Close]"; first done.
  iIntros "!> P". by iMod ("Close" with "P").
Qed.

#[global] Instance into_acc_inv N P E `{!Objective P}:
  IntoAcc (X := unit) (inv N P)
          (↑N ⊆ E) True (fupd E (E ∖ ↑N)) (fupd (E ∖ ↑N) E)
          (λ _ : (), (▷ P)%I) (λ _ : (), (▷ P)%I) (λ _ : (), None) | 0.
Proof.
  rewrite /IntoAcc /accessor bi.exist_unit.
  iIntros (?) "#Hinv _".
  iMod (inv_acc E with "Hinv") as "[$ Close]"; first done.
  iIntros "!> P". by iMod ("Close" with "P").
Qed.
End props.
