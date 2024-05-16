From stdpp Require Import namespaces.
From iris.proofmode Require Import proofmode.

From gpfsl.logic Require Import proofmode.
From gpfsl.logic Require Import repeat_loop new_delete.
From gpfsl.gps Require Import surface_iSP protocols escrows.

From gpfsl.examples Require Import uniq_token.
From gpfsl.examples.mp Require Import code spec.

Require Import iris.prelude.options.

(** Message-Passing example with Release-Acquire *)

Implicit Types (x : loc) (γ: gname) (s: pr_stateT boolProtocol).

Section defs.
Context `{!noprolG Σ, !uniqTokG Σ, gpG: !gpsG Σ boolProtocol}.
Local Notation vProp := (vProp Σ).

Definition XE x γ : vProp := [es UTok γ ⇝ x ↦ #42 ]%I.
Definition YP x γ s (v: val) : vProp :=
  (match s with
  | false => ⌜v = #0⌝
  | true => ⌜v = #1⌝ ∗ XE x γ
  end)%I.

Definition mpInt x γ : interpO Σ boolProtocol
  := (λ _ _ _ _, YP x γ)%I.

Global Instance YP_persistent x γ s v: Persistent (YP x γ s v).
Proof. rewrite /Persistent. destruct s; by iIntros "#YP". Qed.
Global Instance interp_persistent x γ b l γl t s v V : Persistent (mpInt x γ b l γl t s v V).
Proof. destruct b; apply _. Qed.
End defs.

Section proof.
Local Set Default Proof Using "All".
Context `{!noprolG Σ, !uniqTokG Σ, gpG: !gpsG Σ boolProtocol, !atomicG Σ}.

Lemma mp_instance_gps : mp_spec Σ mp.
Proof.
  iIntros (tid Φ) "_ Post". rewrite /mp.
  (* allocation *)
  wp_apply wp_new; [done..|].
  iIntros (m) "(DEL & m & Hm)". rewrite own_loc_na_vec_cons own_loc_na_vec_singleton.
  iDestruct "m" as "[m0 m1]".
  (* initializing *)
  wp_pures. rewrite shift_0. wp_write. wp_op. wp_write.

  (* constructing protocol for m1 *)
  iMod UTok_alloc as (γ) "Tok".
  iMod (GPS_iSP_Init (mpN m) (mpInt (m >> 1) γ) (mpInt (m >> 1) γ false) m false with "m0 []")
    as (γm tm) "W"; [done|].
  iDestruct (GPS_iSP_SWWriter_Reader with "W") as "#R".
  (* forking *)
  wp_apply (wp_fork with "[W m1]"); [done|..].
  - iIntros "!>" (tid').
    (* write message *)
    wp_op. wp_write.
    (* wrap the message in an escrow *)
    iMod (escrow_alloc (UTok γ) ((m >> 1) ↦ #42)%I with "[$m1]") as "#XE"; [done|].
    (* send the escrow *)
    wp_op. rewrite shift_0.
    iApply (GPS_iSP_SWWrite (mpN m) (mpInt (m >> 1) γ) (mpInt (m >> 1) γ false)
              True%I _ AcqRel _ _ true _ #1 with "[$W]");
          [solve_ndisj|done|done|by right|done|..].
    { iSplitL "". - iIntros "!>"; by iFrame "XE". - by iIntros "!> !> _". }
    by iIntros "!>" (?) "W".
  - iIntros "_". wp_seq. wp_bind (repeat: _)%E.
    (* repeat loop *)
    iLöb as "IH". iApply wp_repeat; [done|].
    wp_op. rewrite shift_0.
    iApply (GPS_iSP_Read (mpN m) (mpInt (m >> 1) γ) (mpInt (m >> 1) γ false)
                          (mpInt (m >> 1) γ false m γ) with "[$R]");
        [solve_ndisj|done|done|by right| ..].
    { iIntros "!>" (????) "!>". iSplit; last iSplit; by iIntros "#$". }
    iIntros "!>" (? s' v'). simpl.
    iDestruct 1 as "[% [R' Int]]". destruct s'; simpl; last first.
    { (* keep looping *)
      iDestruct "Int" as %?. subst v'.
      iExists 0. iSplit; [done|]. simpl.
      by iApply ("IH" with "Post DEL Hm Tok"). }
    (* done looping *)
    iDestruct "Int" as "[% XE]". subst v'.
    iExists 1. iSplit; [done|]. simpl. iIntros "!> !>". wp_seq.
    (* read message *)
    iMod (escrow_elim with "[] XE Tok") as "m1"; [done|..].
    { iIntros "[e1 e2]". by iApply (UTok_unique with "e1 e2"). }
    wp_op. wp_read. by iApply ("Post" $! 42).
Qed.
End proof.
