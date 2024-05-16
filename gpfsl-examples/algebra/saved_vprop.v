From gpfsl.examples Require Import sflib.

From iris.algebra Require Import auth gset gmap agree.
From iris.algebra Require Import lib.mono_list.
From iris.proofmode Require Import tactics.
From iris.base_logic.lib Require Import ghost_var ghost_map saved_prop.

From gpfsl.base_logic Require Import meta_data.
From gpfsl.examples.algebra Require Import mono_list_list.
From gpfsl.logic Require Import logatom atomics invariants.

From gpfsl.logic Require Import repeat_loop new_delete.

Require Import iris.prelude.options.

Class savedvPropG Σ := SavedvPropG {
  savediPredG :> savedPredG Σ view;
}.

Definition savedvPropΣ : gFunctors := #[savedPredΣ view].

Global Instance subG_savedvPropΣ {Σ} : subG savedvPropΣ Σ → savedvPropG Σ.
Proof. solve_inG. Qed.

Section saved_vProp.
Context `{!savedvPropG Σ}.
Local Notation vProp := (vProp Σ).

Definition saved_vProp_own (γ : gname) dq (P : vProp) : vProp :=
  ⎡saved_pred_own γ dq P⎤.

Lemma saved_vProp_alloc dq (P : vProp) :
  ✓ dq →
  ⊢ |==> ∃ γ, saved_vProp_own γ dq P.
Proof. iIntros. iMod saved_pred_alloc as (γ) "H"; [done|]. iModIntro. iExists _. iFrame "H". Qed.

Lemma saved_vProp_valid γ dq P :
  saved_vProp_own γ dq P -∗ ⌜ ✓ dq ⌝.
Proof. iIntros "H". by iDestruct (saved_pred_valid with "H") as %?. Qed.

Lemma saved_vProp_valid_2 γ dq1 dq2 P1 P2 :
  saved_vProp_own γ dq1 P1 -∗ saved_vProp_own γ dq2 P2 -∗ ⌜ ✓ (dq1 ⋅ dq2) ⌝ ∗ ▷ (P1 ≡ P2).
Proof.
  iIntros "H1 H2". iDestruct (saved_pred_valid_2 _ _ _ _ _ ∅ with "H1 H2") as "#H". iDestruct "H" as "[% _]". iSplit; [done|].
  rewrite -{2}(sig_monPred_sig P1) -{2}(sig_monPred_sig P2) -f_equivI -sig_equivI discrete_fun_equivI /=.
  iIntros "%x". iDestruct (saved_pred_agree _ _ _ _ _ x with "H1 H2") as "H".
  iModIntro. by rewrite embed_internal_eq.
Qed.

Lemma saved_vProp_agree γ dq1 dq2 P1 P2 :
  saved_vProp_own γ dq1 P1 -∗ saved_vProp_own γ dq2 P2 -∗ ▷ (P1 ≡ P2).
Proof.
  iIntros "H1 H2". iDestruct (saved_vProp_valid_2 with "H1 H2") as "[_ ?]". done.
Qed.

Lemma saved_vProp_persist γ dq P :
  saved_vProp_own γ dq P ==∗ saved_vProp_own γ DfracDiscarded P.
Proof.
  iIntros "H". iMod (saved_pred_persist with "H") as "H". iModIntro. done.
Qed.

Lemma saved_vProp_update P' γ P :
  saved_vProp_own γ (DfracOwn 1) P ==∗ saved_vProp_own γ (DfracOwn 1) P'.
Proof.
  iIntros "H". iMod (saved_pred_update with "H") as "H". iModIntro. done.
Qed.

Lemma saved_vProp_update_2 P' γ q1 q2 P1 P2 :
  (q1 + q2 = 1)%Qp →
  saved_vProp_own γ (DfracOwn q1) P1 -∗ saved_vProp_own γ (DfracOwn q2) P2 ==∗ saved_vProp_own γ (DfracOwn q1) P' ∗ saved_vProp_own γ (DfracOwn q2) P'.
Proof.
  iIntros (?) "H1 H2". iMod (saved_pred_update_2 P' with "H1 H2") as "[H1 H2]"; [done|]. iModIntro. iFrame "H1 H2".
Qed.

Lemma saved_vProp_update_halves P' γ P1 P2 :
  saved_vProp_own γ (DfracOwn (1/2)) P1 -∗ saved_vProp_own γ (DfracOwn (1/2)) P2 ==∗ saved_vProp_own γ (DfracOwn (1/2)) P' ∗ saved_vProp_own γ (DfracOwn (1/2)) P'.
Proof.
  iIntros "H1 H2". iMod (saved_pred_update_halves P' with "H1 H2") as "[H1 H2]". iModIntro. iFrame "H1 H2".
Qed.

End saved_vProp.
