From iris.base_logic Require Import lib.invariants.
From iris.proofmode Require Import proofmode.
From gpfsl.base_logic Require Import vprop.

Require Import iris.prelude.options.

Section subj_inv.
Context `{!invGS Σ}.
Local Notation vProp := (vProp Σ).
Implicit Types (N: namespace) (E: coPset) (P: vProp).

Definition subj_inv_def N P : vProp := ⎡ inv N (∃ V, P V) ⎤%I.
Definition subj_inv_aux : seal (@subj_inv_def). Proof. by eexists. Qed.
Definition subj_inv := unseal (@subj_inv_aux).
Definition subj_inv_eq : @subj_inv = _ := seal_eq _.

Global Instance subj_inv_objective N P : Objective (subj_inv N P).
Proof. rewrite subj_inv_eq. apply _. Qed.

Lemma subj_inv_alloc N E P : ▷ P ={E}=∗ subj_inv N P.
Proof.
  iStartProof (iProp _). rewrite subj_inv_eq. iIntros (V) "P".
  rewrite monPred_at_embed.
  iApply inv_alloc. by iExists _.
Qed.

Lemma subj_inv_alloc_open N E P :
  ↑N ⊆ E → ⊢ |={E, E∖↑N}=> subj_inv N P ∗ (▷P ={E∖↑N, E}=∗ True).
Proof.
  intros. iStartProof (iProp _). rewrite subj_inv_eq. iIntros (V).
  rewrite monPred_at_embed.
  iMod (inv_alloc_open) as "[$ Closed]"; [done|].
  iIntros "!>" (??) "P". iMod ("Closed" with "[P]"); [|done].
  by iExists _.
Qed.

Lemma subj_inv_acc N P E :
  ↑N ⊆ E → subj_inv N P ={E,E∖↑N}=∗
    ∃ Vb, (⊒Vb → ▷ P) ∗ ((⊒Vb → ▷ P) ={E∖↑N,E}=∗ True).
Proof.
  intros. iStartProof (iProp _). rewrite subj_inv_eq. iIntros (V) "#INV".
  iMod (inv_acc with "INV") as "[VI Closed]"; [done|].
  iDestruct "VI" as (Vb) "P".
  iIntros "!>". iExists Vb. iSplitL "P".
  { iIntros (???). by iFrame "P". }
  iIntros (V' ?) "P". rewrite monPred_at_impl.
  iDestruct ("P" $! (V' ⊔ Vb) with "[%] [%]") as "P"; [solve_lat..|].
  iMod ("Closed" with "[P]"); [|done]. iExists _.
  rewrite monPred_at_later. by iFrame "P".
Qed.

Global Instance subj_inv_contractive N : Contractive (subj_inv N).
Proof. rewrite subj_inv_eq. solve_contractive. Qed.
Global Instance subj_inv_ne N : NonExpansive (subj_inv N).
Proof. rewrite subj_inv_eq. solve_proper. Qed.
Global Instance subj_inv_proper N : Proper ((≡) ==> (≡)) (subj_inv N).
Proof. apply (ne_proper _). Qed.
Global Instance subj_inv_persistent N P :
  Persistent (subj_inv N P).
Proof. rewrite subj_inv_eq; apply _. Qed.

Global Instance into_inv_subj_inv N P : IntoInv (subj_inv N P) N := {}.

Global Instance into_acc_subj_inv E N P :
  IntoAcc (X:=view) (subj_inv N P)
          (↑N ⊆ E) True (fupd E (E∖↑N)) (fupd (E∖↑N) E)
          (λ Vb, (⊒Vb → ▷ P))%I (λ Vb, (⊒Vb → ▷ P))%I (λ _, None)%I.
Proof.
  rewrite /IntoAcc /accessor.
  iIntros (?) "#Hinv _". simpl. setoid_rewrite <- bi.True_emp.
  by iApply subj_inv_acc.
Qed.

End subj_inv.

#[global] Instance: Params (@subj_inv) 3 := {}.
#[global] Typeclasses Opaque subj_inv.
