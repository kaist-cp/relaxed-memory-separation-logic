(* From iris.algebra Require Import gmap. *)
From iris.base_logic.lib Require Import ghost_var ghost_map.
From diaframe Require Import proofmode_base own_hints.
From gpfsl.logic Require Import proofmode.
From Hammer Require Import Tactics.



Section ghost_map_hints.
  Context `{!noprolG Σ, ghost_mapG Σ K V}.
  Implicit Types (k : K) (v : V) (m : gmap K V).
  #[local] Notation vProp := (vProp Σ).

  #[global] Instance biabd_ghost_map_insert Mk γ m k v :
    HINT @embed _ vProp _ (ghost_map_auth γ 1 m) ✱ [-; ⌜ m !! k = None ⌝ ]
    ⊫ [fupd Mk Mk]
    ; ⎡ ghost_map_auth γ 1 (<[k := v]> m)⎤ ✱ [ ⎡ k ↪[γ] v ⎤ ] | 100.
  Proof. iStep as (?) "A". iMod (ghost_map_insert with "A") as "[$ $]"; done. Qed.

  #[global] Instance biabd_ghost_map_elem_persist Mk γ k v :
    HINT @embed _ vProp _ (k ↪[γ] v) ✱ [-; emp ]
    ⊫ [fupd Mk Mk]
    ; ⎡ k ↪[γ]□ v ⎤ ✱ [ ⎡ k ↪[γ]□ v ⎤ ] | 100.
  Proof. iStep as "A". iMod (ghost_map_elem_persist with "A") as "#A". auto. Qed.

  #[global] Instance mergable_persist_ghost_map_lookup γ k v dq q' m :
  MergablePersist (PROP := vProp) (⎡k ↪[γ]{dq} v⎤) (λ p Pin Pout,
  TCAnd (TCEq Pin (⎡ghost_map_auth γ q' m⎤)) $
        TCEq Pout (⌜m !! k = Some v⌝)%I)%I.
  Proof.
    intros p Pin Pout [-> ->]. rewrite bi.intuitionistically_if_elim.
    iIntros "[A B]". iDestruct (ghost_map_lookup with "B A") as "%". auto.
  Qed.

  #[global] Instance biabd_ghost_map_delete Mk γ m k :
    HINT @embed _ vProp _ (ghost_map_auth γ 1 m) ✱[v; ⎡ k ↪[γ] v ⎤ ]
    ⊫ [fupd Mk Mk]
    ; ⎡ ghost_map_auth γ 1 (delete k m)⎤ ✱ [ emp ] | 100.
  Proof. iStep 2 as (??) "_ A B". iMod (ghost_map_delete with "A B") as "$". done. Qed.

  #[global] Instance biabd_ghost_map_elem_merge γ k dq dq1 dq2 v1 v2 :
    MergableConsume (PROP := vProp) (⎡ k ↪[γ]{dq1} v1 ⎤) true (λ p Pin Pout,
      TCAnd (TCEq Pin (⎡ k ↪[γ]{dq2} v2 ⎤)) $
      TCAnd (proofmode_classes.IsOp dq dq1 dq2) $
          TCEq Pout (⌜ v1 = v2 ⌝ ∗ ⎡ k ↪[γ]{dq} v2 ⎤))%I.
  Proof. 
    intros p Pin Pout (->&->&->). rewrite bi.intuitionistically_if_elim.
    iIntros "[A B]". iDestruct (ghost_map_elem_agree with "A B") as %->.
    iCombine "A B" as "$". done.
  Qed.

End ghost_map_hints.