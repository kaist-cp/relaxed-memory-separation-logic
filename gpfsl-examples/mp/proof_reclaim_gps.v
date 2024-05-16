From iris.proofmode Require Import proofmode.

From gpfsl.logic Require Import proofmode.
From gpfsl.logic Require Import view_invariants.
From gpfsl.logic Require Import repeat_loop new_delete.
From gpfsl.gps Require Import surface_vSP protocols escrows.

From gpfsl.examples Require Import uniq_token.
From gpfsl.examples.mp Require Import code spec.

Require Import iris.prelude.options.

(** Message-Passing example with Release-Acquire *)

Implicit Types (x : loc) (γ: gname) (s: pr_stateT boolProtocol).

Section defs.
Context `{!noprolG Σ, !view_invG Σ, !uniqTokG Σ, !gpsG Σ boolProtocol}.
Local Notation vProp := (vProp Σ).

Definition XE x γ γi : vProp := [es UTok γ ⇝ x ↦ #42 ∗ view_tok γi (1/2)]%I.
Definition YP x γ γi s (v: val) : vProp :=
  (match s with
  | false => ⌜v = #0⌝
  | true => ⌜v = #1⌝ ∗ XE x γ γi
  end)%I.

Definition mpInt x γ γi : interpO Σ boolProtocol
  := (λ _ _ _ _, YP x γ γi)%I.

Global Instance YP_persistent x γ γi s v: Persistent (YP x γ γi s v).
Proof. rewrite /Persistent. destruct s; by iIntros "#YP". Qed.
Global Instance interp_persistent x γ γi b l γl t s v V : Persistent (mpInt x γ γi b l γl t s v V).
Proof. destruct b; apply _. Qed.
End defs.

Section proof.
Context `{!noprolG Σ, !view_invG Σ, !uniqTokG Σ, !gpsG Σ boolProtocol, !atomicG Σ}.

Lemma mp_instance_reclaim_gps : mp_spec Σ mp_reclaim.
Proof using All.
  iIntros (tid Φ) "_ Post". rewrite /mp_reclaim.
  (* allocation *)
  wp_apply wp_new; [done..|].
  iIntros (m) "([DEL|%] & m & Hm)"; [|done].
  rewrite own_loc_na_vec_cons own_loc_na_vec_singleton.
  iDestruct "m" as "[m0 m1]".
  (* initializing *)
  wp_pures. rewrite shift_0. wp_write.
  wp_op. wp_write.

  (* constructing protocol for m1 *)
  iMod UTok_alloc as (γ) "Tok".
  iMod (GPS_vSP_Init (mpN m) (mpInt (m >> 1) γ) (λ γi, mpInt (m >> 1) γ γi false)
          m false with "m0 []") as (γi γm tm) "[[Htok1 Htok2] W]"; [done|].
  iDestruct (GPS_vSP_SWWriter_Reader with "W") as "#R".
  (* forking *)
  wp_apply (wp_fork with "[W m1 Htok1]"); [done|..].
  - iIntros "!>" (tid').
    (* write message *)
    wp_op. wp_write.
    wp_op. rewrite shift_0.
    (* send the message *)
    iApply (GPS_vSP_SWWrite_rel (mpN m) (mpInt (m >> 1) γ γi)
            (mpInt (m >> 1) γ γi false) _ (1/2) (λ _, True)%I True%I True%I _
            _ true _ #1 with "[$Htok1 $W m1]"); [done|solve_ndisj|done|done|..].
    { iSplitR ""; last by iIntros "!> !>".
      iIntros "!>" (??) "W _ Htok1 !>". iSplitL ""; first by iIntros "!> _ !>".
      (* wrap the message in an escrow *)
      iMod (escrow_alloc (UTok γ) ((m >> 1) ↦ #42 ∗ view_tok γi (1/2))%I
            with "[$m1 $Htok1]") as "#XE"; [solve_ndisj|].
      iIntros "!>". by iFrame "XE". }
    by iIntros "!>" (?) "_".
  - iIntros "_". wp_seq. wp_bind (repeat: _)%E.
    (* repeat loop *)
    iLöb as "IH". iApply wp_repeat; [done|].
    wp_op. rewrite shift_0.
    iApply (GPS_vSP_Read (mpN m) (mpInt (m >> 1) γ γi) (mpInt (m >> 1) γ γi false)
                         (mpInt (m >> 1) γ γi false m γm)%I
              with "[$R $Htok2]");
        [solve_ndisj|done|done|by right| ..].
    { iIntros "!>" (? s' v' ?) "!>". iSplit; last iSplit; by iIntros "#$". }

    iIntros "!>" (? s' v'). simpl.
    iDestruct 1 as "[% [Htok2 [R' Int]]]". destruct s'; simpl; last first.
    { (* keep looping *)
      iDestruct "Int" as %?. subst v'.
      iExists 0. iSplit; [done|]. simpl.
      by iApply ("IH" with "Post DEL Hm Tok Htok2"). }
    (* done looping *)
    iDestruct "Int" as "[% XE]". subst v'.
    iExists 1. iSplit; [done|]. simpl. iIntros "!> !>". wp_seq.
    (* read message *)
    iMod (escrow_elim with "[] XE Tok") as "[m1 Htok1]"; [done|..].
    { iIntros "[e1 e2]". by iApply (UTok_unique with "e1 e2"). }

    wp_op. wp_read. wp_let.

    (* dealloc protocol *)
    iCombine "Htok1" "Htok2" as "Htok".
    iApply wp_hist_inv; [done|]. iIntros "HINV".
    iMod (GPS_vSP_dealloc with "HINV Htok R'") as (?? v') "[Hl ?]"; [done..|].
    (* dealloc the locations *)
    wp_apply (wp_delete _ tid 2 m [v'; #42] with "[m1 Hl $DEL]"); [done|done|..].
    { rewrite own_loc_na_vec_cons own_loc_na_vec_singleton. by iFrame. }
    iIntros "_". wp_seq. by iApply ("Post" $! 42).
Qed.
End proof.
