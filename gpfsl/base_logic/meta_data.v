From iris.base_logic.lib Require Import gen_heap.
From iris.proofmode Require Import proofmode.

From gpfsl.base_logic Require Import history vprop.

Require Import iris.prelude.options.

(** Lifts meta into vProp *)

Local Existing Instances
  histGpreS_hist hist_inG
  .

Section meta_vprop_def.
  Context `{!noprolG Σ}.
  Definition meta_token_def l (E : coPset) : vProp Σ := ⎡ meta_token l E ⎤.
  Definition meta_token_aux : seal (@meta_token_def). Proof. by eexists. Qed.
  Definition meta_token := meta_token_aux.(unseal).
  Definition meta_token_eq : @meta_token = @meta_token_def := meta_token_aux.(seal_eq).

  Definition meta_def `{Countable A} l (N : namespace) (x : A) : vProp Σ :=
    ⎡ meta l N x ⎤.
  Definition meta_aux : seal (@meta_def). Proof. by eexists. Qed.
  Definition meta := meta_aux.(unseal).
  Definition meta_eq : @meta = @meta_def := meta_aux.(seal_eq).
End meta_vprop_def.
Global Arguments meta {Σ _ A _ _} l N x.

Section meta_vprop.
  Context `{!noprolG Σ}.
  (** General properties of [meta] and [meta_token] *)
  Global Instance meta_token_timeless l N : Timeless (meta_token l N).
  Proof. rewrite meta_token_eq. apply _. Qed.
  Global Instance meta_token_objective l N : Objective (meta_token l N).
  Proof. rewrite meta_token_eq. apply _. Qed.
  Global Instance meta_timeless `{Countable A} l N (x : A) : Timeless (meta l N x).
  Proof. rewrite meta_eq. apply _. Qed.
  Global Instance meta_persistent `{Countable A} l N (x : A) : Persistent (meta l N x).
  Proof. rewrite meta_eq. apply _. Qed.
  Global Instance meta_objective `{Countable A} l N (x : A) : Objective (meta l N x).
  Proof. rewrite meta_eq. apply _. Qed.

  Lemma meta_token_union_1 l E1 E2 :
    E1 ## E2 → meta_token l (E1 ∪ E2) -∗ meta_token l E1 ∗ meta_token l E2.
  Proof.
    rewrite meta_token_eq /meta_token_def. iIntros (?) "HE12".
    by iDestruct (gen_heap.meta_token_union_1 with "HE12") as "[$ $]".
  Qed.
  Lemma meta_token_union_2 l E1 E2 :
    meta_token l E1 -∗ meta_token l E2 -∗ meta_token l (E1 ∪ E2).
  Proof.
    rewrite meta_token_eq /meta_token_def. iIntros "H1 H2".
    iApply (gen_heap.meta_token_union_2 with "H1 H2").
  Qed.
  Lemma meta_token_union l E1 E2 :
    E1 ## E2 → meta_token l (E1 ∪ E2) ⊣⊢ meta_token l E1 ∗ meta_token l E2.
  Proof.
    intros. rewrite meta_token_eq /meta_token_def -embed_sep. apply embed_proper.
    by apply gen_heap.meta_token_union.
  Qed.

  Lemma meta_token_difference l E1 E2 :
    E1 ⊆ E2 → meta_token l E2 ⊣⊢ meta_token l E1 ∗ meta_token l (E2 ∖ E1).
  Proof.
    intros. rewrite meta_token_eq /meta_token_def -embed_sep. apply embed_proper.
    by apply gen_heap.meta_token_difference.
  Qed.

  Lemma meta_agree `{Countable A} l i (x1 x2 : A) :
    meta l i x1 -∗ meta l i x2 -∗ ⌜x1 = x2⌝.
  Proof.
    rewrite meta_eq /meta_def. iIntros "H1 H2".
    by iDestruct (gen_heap.meta_agree with "H1 H2") as %?.
  Qed.
  Lemma meta_set `{Countable A} E l (x : A) N :
    ↑ N ⊆ E → meta_token l E ==∗ meta l N x.
  Proof.
    intros.
    rewrite meta_token_eq meta_eq /meta_token_def /meta_def -embed_bupd.
    by apply embed_mono, gen_heap.meta_set.
  Qed.
End meta_vprop.
