(** This library is copied from
  https://gitlab.mpi-sws.org/iris/iris/-/blob/32b4b0ccf9f91e19b37486a6a280afe129d107ca/iris_heap_lang/lib/arith.v *)
From gpfsl.lang Require Export notation.
From gpfsl.logic Require Export lifting proofmode.

Require Import iris.prelude.options.

Definition minimum : val :=
  λ: ["m"; "n"], if: "m" < "n" then "m" else "n".

Definition maximum : val :=
  λ: ["m"; "n"], if: "m" < "n" then "n" else "m".

Section spec_proof.
Context `{!noprolG Σ}.

Lemma minimum_spec tid E (Φ : val → vProp Σ) (m n : Z) :
  ▷ Φ #(m `min` n) -∗
  WP minimum [ #m; #n] @ tid; E {{ Φ }}.
Proof.
  iIntros "HΦ". wp_lam. wp_op. case_bool_decide; wp_if.
  - rewrite Z.min_l; [ done | by lia ].
  - rewrite Z.min_r; [ done | by lia ].
Qed.

Lemma minimum_spec_nat tid E (Φ : val → vProp Σ) (m n : nat) :
  ▷ Φ #(m `min` n)%nat -∗
  WP minimum [ #m; #n] @ tid; E {{ Φ }}.
Proof. iIntros "HΦ". iApply minimum_spec. by rewrite Nat2Z.inj_min. Qed.

Lemma maximum_spec tid E (Φ : val → vProp Σ) (m n : Z) :
  ▷ Φ #(m `max` n) -∗
  WP maximum [ #m; #n] @ tid; E {{ Φ }}.
Proof.
  iIntros "HΦ". wp_lam. wp_op. case_bool_decide; wp_if.
  - rewrite Z.max_r; [ done | by lia ].
  - rewrite Z.max_l; [ done | by lia ].
Qed.

Lemma maximum_spec_nat tid E (Φ : val → vProp Σ) (m n : nat) :
  ▷ Φ #(m `max` n)%nat -∗
  WP maximum [ #m; #n] @ tid; E {{ Φ }}.
Proof. iIntros "HΦ". iApply maximum_spec. by rewrite Nat2Z.inj_max. Qed.
End spec_proof.
