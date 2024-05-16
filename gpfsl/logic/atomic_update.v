From stdpp Require Import coPset namespaces.
From iris.bi Require Import lib.atomic.
From iris.proofmode Require Import proofmode classes.

Require Import iris.prelude.options.

Section derived.
  Context `{BiFUpd PROP} {TA TB : tele}.
  Implicit Types
  (Eo Ei : coPset) (* outer/inner masks *)
  (α : TA → PROP) (* atomic pre-condition *)
  (P : PROP) (* abortion condition *)
  (β : TA → TB → PROP) (* atomic post-condition *)
  (Φ : TA → TB → PROP) (* post-condition *)
  .

  Lemma atomic_update_mask_frame Eo Ei Ef α β Φ :
    Eo ## Ef →
    atomic_update Eo Ei α β Φ ⊢ atomic_update (Eo ∪ Ef) (Ei ∪ Ef) α β Φ.
  Proof.
    iIntros (Do) "AU". iAuIntro.
    iPoseProof (aupd_aacc with "AU") as "AU".
    rewrite /atomic_acc.
    iApply fupd_mask_frame_r'; [done|].
    iMod "AU" as (x) "[Hα HClose]".
    iIntros "!>" (?). iExists x. iFrame "Hα".
    iApply (bi.and_parallel with "HClose"). iSplit.
    - rewrite -fupd_mask_frame_r //. iIntros "$".
    - iIntros "HP" (y) "Hβ". rewrite -fupd_mask_frame_r //. by iApply "HP".
  Qed.

  Lemma atomic_update_mask_frame_top_empty E α β Φ :
    atomic_update (⊤ ∖ E) ∅ α β Φ ⊢ atomic_update ⊤ E α β Φ.
  Proof.
    rewrite -{2}(left_id_L ∅ union E).
    rewrite {2}(union_difference_L E top) // union_comm_L.
    apply atomic_update_mask_frame; set_solver.
  Qed.
End derived.
