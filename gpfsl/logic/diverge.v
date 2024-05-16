(** This library is copied from
  https://gitlab.mpi-sws.org/iris/iris/-/blob/32b4b0ccf9f91e19b37486a6a280afe129d107ca/iris_heap_lang/lib/diverge.v
  It provides a [diverge] function that goes into an infinite loop when provided
  with an (arbitrary) argument value. This function can be used to let the
  program diverge in corner cases that one wants to omit in proofs. *)
From gpfsl.lang Require Export notation.
From gpfsl.logic Require Export lifting proofmode.

Require Import iris.prelude.options.

Definition diverge : val :=
  rec: "diverge" ["v"] := "diverge" ["v"].

Lemma wp_diverge `{!noprolG Σ} tid E (Φ : val → vProp Σ) (v : val) :
  ⊢ WP diverge [v] @ tid; E {{ Φ }}.
Proof.
  iLöb as "IH". wp_lam. iApply "IH".
Qed.
