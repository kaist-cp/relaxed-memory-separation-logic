From gpfsl.logic Require Import view_invariants.
From gpfsl.logic Require Import atomics.

From gpfsl.logic Require Import proofmode.
From gpfsl.logic Require Import repeat_loop new_delete.

From gpfsl.examples Require Import uniq_token.
From gpfsl.examples.mp Require Import code spec.

Require Import iris.prelude.options.

(** Message-Passing example with Release-Acquire *)

Implicit Types (x : loc) (γ: gname) (ζ : absHist) (t : time) (V: view).

Local Notation flag := 0%nat (only parsing).
Local Notation data := 1%nat (only parsing).

Section inv.
Context `{!noprolG Σ, !atomicG Σ, !uniqTokG Σ}.
#[local] Notation vProp := (vProp Σ).

Definition mp_inv'_def (x y : loc) γ γx : vProp :=
  (∃ ζ (b : bool) t0 V0 Vx,
    @{Vx} (x sw↦{γx} ζ) ∗
    let ζ0 : absHist := {[t0 := (#0, V0)]} in
    match b with
    | false => ⌜ζ = ζ0⌝
    | true => ∃ t1 V1, ⌜(t0 < t1)%positive ∧ ζ = <[t1 := (#1, V1)]>ζ0⌝ ∗
              (UTok γ ∨ @{V1} (y ↦ #42))
    end
  )%I.
Definition mp_inv'_aux : seal (@mp_inv'_def). Proof. by eexists. Qed.
Definition mp_inv' := unseal (@mp_inv'_aux).
Definition mp_inv'_eq : @mp_inv' = _ := seal_eq _.

#[global] Instance mp_inv'_objective x y γ γx : Objective (mp_inv' x y γ γx).
Proof.
  rewrite mp_inv'_eq.
  apply exists_objective=>?. apply exists_objective=>[[|]]; by apply _.
Qed.

Definition mp_inv N x y γ γx := inv N (mp_inv' x y γ γx).
End inv.

Lemma mp_instance_gen_inv `{!noprolG Σ, !atomicG Σ, !uniqTokG Σ} :
  mp_spec Σ mp.
Proof.
  iIntros (tid Φ) "_ Post". rewrite /mp.
  (* allocation *)
  wp_apply wp_new; [done..|].
  iIntros (m) "(DEL & m & Hm)". rewrite own_loc_na_vec_cons own_loc_na_vec_singleton.
  iDestruct "m" as "[m0 m1]".
  (* initializing *)
  wp_pures. rewrite shift_0. wp_write. wp_op. wp_write.

  (* constructing the invariant *)
  iMod UTok_alloc as (γ) "Tok".
  iMod (AtomicPtsTo_from_na with "m0") as (γx t V) "(#SeenV & SW & Pts)".
  iDestruct (AtomicSWriter_AtomicSync with "SW") as "#S".
  iDestruct (view_at_intro with "Pts") as (Vx) "[SeenVx Pts]".
  iMod (inv_alloc (mpN m) _ (mp_inv' (m >> flag) (m >> data) γ γx)
          with "[Pts]") as "#Inv".
  { rewrite mp_inv'_eq. iIntros "!>".
    iExists _, false, t, V, Vx. rewrite shift_0. by iFrame "Pts". }
  (* forking *)
  wp_apply (wp_fork with "[SW m1]"); [done|..].
  - iIntros "!>" (tid').
    (* write message *)
    wp_op. wp_write. wp_op. rewrite shift_0.
    (* open shared invariant *)
    iInv (mpN m) as "INV" "Close". rewrite mp_inv'_eq.
    iDestruct "INV" as (ζ' b t0 V0 Vx0) "[>Pts _]".
    iDestruct (AtomicPtsTo_AtomicSWriter_agree_1 with "Pts SW") as %->.
    (* actualy write of flag *)
    iApply (AtomicSWriter_release_write _ _ _ _ V Vx0 #1 ((m >> 1) ↦{1} #42)%I
              with "[$SW $Pts $m1 $SeenV]"); [solve_ndisj|..].
    iIntros "!>" (t1 V1) "(%MAX & SeenV' & [m1 SW'] & Pts')".
    (* reestablishing the invariant *)
    iMod ("Close" with "[-]"); last done.
    iIntros "!>". iExists _, true, t, V, _. iFrame "Pts'".
    iExists t1, V1. iSplit.
    { iPureIntro. split; [|done]. apply MAX. rewrite lookup_insert. by eexists. }
    iRight. by iFrame "m1".

  - iIntros "_". wp_seq. wp_bind (repeat: _)%E.
    (* repeat loop *)
    iLöb as "IH". iApply wp_repeat; [done|].
    wp_op. rewrite shift_0.

    (* open shared invariant *)
    iInv (mpN m) as "INV" "Close". rewrite mp_inv'_eq.
    iDestruct "INV" as (ζ' b t0 V0 Vx0) "[>Pts Own]".

    (* actual read *)
    iApply (AtomicSeen_acquire_read with "[$Pts $SeenV]"); [solve_ndisj|..].
    { by iApply (AtomicSync_AtomicSeen with "S"). }
    iIntros "!>" (t' v' V' V'' ζ'') "(HF & SV' & SN' & Pts)".
    iDestruct "HF" as %([Sub1 Sub2] & Eqt' & MAX' & LeV'').

    case (decide (t' = t0)) => [?|NEqt'].
    + subst t'.
      (* we must have read the flag to be 0 (i.e. z = 0). *)
      iAssert (⌜v' = #0⌝)%I as %Eq0.
      { destruct b.
        - iDestruct "Own" as (t1 V1 [Lt1 Eqζ']) "_".
          iPureIntro.
          rewrite Eqζ' in Sub2. apply (lookup_weaken _ _ _ _ Eqt') in Sub2.
          rewrite lookup_insert_ne in Sub2.
          + rewrite lookup_insert in Sub2. by inversion Sub2.
          + clear -Lt1. intros ?. subst. lia.
        - iDestruct "Own" as %Eqζ'. iPureIntro.
          rewrite Eqζ' in Sub2. apply (lookup_weaken _ _ _ _ Eqt') in Sub2.
          rewrite lookup_insert in Sub2. by inversion Sub2. }
      (* then simply keep looping *)
      (* first close the invariant *)
      iMod ("Close" with "[Pts Own]").
      { iIntros "!>". iExists ζ', b, t0, V0, _. by iFrame. }
      iIntros "!>". iExists 0. iSplit; [done|].
      (* then apply the Löb IH *)
      iIntros "!> !>". by iApply ("IH" with "Post DEL Hm Tok SeenVx").

    + destruct b; last first.
      { (* b cannot be false *)
        iDestruct "Own" as %Eqζ'. exfalso.
        rewrite Eqζ' in Sub2.
        apply (lookup_weaken _ _ _ _ Eqt'), lookup_singleton_Some in Sub2 as [].
        by apply NEqt'. }
      iClear "IH".
      (* we read 1, the destruct Own to get data. *)
      iDestruct "Own" as (t1 V1 [Lt1 Eqζ']) "Own".
      rewrite Eqζ' in Sub2. apply (lookup_weaken _ _ _ _ Eqt') in Sub2.
      have ? : t' = t1.
      { case (decide (t' = t1)) => [//|NEqt1].
        exfalso. by rewrite !lookup_insert_ne // in Sub2. }
      subst t'. rewrite lookup_insert in Sub2. inversion Sub2. subst v' V'.

      iDestruct "Own" as "[Own|Data]".
      { iExFalso. by iDestruct (UTok_unique with "Tok Own") as "$". }
      iDestruct (view_at_elim with "[SV'] Data") as "Data".
      { iApply (monPred_in_mono with "SV'"). simpl. solve_lat. }

      (* close the invariant *)
      iMod ("Close" with "[Pts Tok]").
      { iIntros "!>". iExists ζ', true, t0, V0, _. iFrame "Pts".
        iExists t1, V1. iSplit; [done|]. by iLeft. }
      iIntros "!>". iExists 1. iSplit; [done|].
      iIntros "!> !>".

      wp_pures. wp_read. by iApply "Post".
Qed.


Section reclaim.
Context `{!noprolG Σ, !atomicG Σ, !view_invG Σ}.
#[local] Notation vProp := (vProp Σ).

(* Notice how we don't need UTok here: we can just use view_tok to immediately
  cancel the invariant after acquiring y. *)
Definition mp_inv_reclaim'_def (x y : loc) γx γi : vProp :=
  (∃ ζ (b : bool) t0 V0,
    x sw↦{γx} ζ ∗
    let ζ0 : absHist := {[t0 := (#0, V0)]} in
    match b with
    | false => ⌜ζ = ζ0⌝
    | true => ∃ t1 V1, ⌜(t0 < t1)%positive ∧ ζ = <[t1 := (#1, V1)]>ζ0⌝ ∗
              @{V1} (y ↦ #42 ∗ view_tok γi (1/2))
    end
  )%I.
Definition mp_inv_reclaim'_aux : seal (@mp_inv_reclaim'_def). Proof. by eexists. Qed.
Definition mp_inv_reclaim' := unseal (@mp_inv_reclaim'_aux).
Definition mp_inv_reclaim'_eq : @mp_inv_reclaim' = _ := seal_eq _.

(* we don't care about objectivity when using view_inv *)
Definition mp_inv_reclaim N x y γx γi :=
  view_inv γi N (mp_inv_reclaim' x y γx γi).
End reclaim.

Lemma mp_instance_reclaim_gen_inv `{!noprolG Σ, !view_invG Σ, !atomicG Σ} :
  mp_spec Σ mp_reclaim.
Proof.
  iIntros (tid Φ) "_ Post". rewrite /mp_reclaim.
  (* allocation *)
  wp_apply wp_new; [done..|].
  iIntros (m) "(DEL & m & Hm)". rewrite own_loc_na_vec_cons own_loc_na_vec_singleton.
  iDestruct "m" as "[m0 m1]".
  (* initializing *)
  wp_pures. rewrite shift_0. wp_write. wp_op. wp_write.

  (* constructing the invariant *)
  iMod (AtomicPtsTo_from_na with "m0") as (γx t V) "(#SeenV & SW & Pts)".
  iDestruct (AtomicSWriter_AtomicSync with "SW") as "#S".
  iMod (view_inv_alloc (mpN m) _) as (γi) "Inv".
  iMod ("Inv" $! (mp_inv_reclaim' (m >> flag) (m >> data) γx γi) with "[Pts]")
    as "(#Inv & vTok1 & vTok2)".
  { rewrite mp_inv_reclaim'_eq. iIntros "!>".
    iExists _, false, t, V. rewrite shift_0. by iFrame "Pts". }
  (* forking *)
  wp_apply (wp_fork with "[SW m1 vTok1]"); [done|..].
  - iIntros "!>" (tid').
    (* write message *)
    wp_op. wp_write.

    wp_op. rewrite shift_0.
    (* open shared invariant *)
    iMod (view_inv_acc_base' with "[$Inv $vTok1]") as "(vTok1 & INV) {Inv}"; [done|].
    iDestruct "INV" as (Vb) "[INV Close]".
    rewrite {1}mp_inv_reclaim'_eq.
    iDestruct "INV" as (ζ' b t0 V0) "[Pts _]".
    rewrite view_join_later. iDestruct "Pts" as ">Pts".
    iDestruct (view_join_elim' with "Pts SeenV") as (V') "(#SeenV' & % & Pts)".
    iDestruct (AtomicPtsTo_AtomicSWriter_agree_1 with "Pts SW") as %->.
    (* actualy write of flag *)
    iApply (AtomicSWriter_release_write _ _ _ _ V' _ #1
              ((m >> 1) ↦{1} #42 ∗ view_tok γi (1 / 2))%I
              with "[$SW $Pts $m1 $vTok1 $SeenV']"); [solve_ndisj|..].
    iIntros "!>" (t1 V1) "((%MAX & %LeV1 & _) & SeenV1 & [[m1 vTok1] SW'] & Pts')".
    (* reestablishing the invariant *)
    rewrite bi.and_elim_r bi.and_elim_l.
    iMod ("Close" $! V1 True%I with "vTok1 [-]"); last done.
    iIntros "vTok1 !>". iSplit; [|done].
    rewrite view_at_view_join. iNext. rewrite mp_inv_reclaim'_eq.
    iExists _, true, t, V. iSplitL "Pts'"; first by iFrame.
    iExists t1, V1. iSplit.
    { iPureIntro. split; [|done]. apply MAX. rewrite lookup_insert. by eexists. }
    by iFrame.

  - iIntros "_". wp_seq. wp_bind (repeat: _)%E.
    (* repeat loop *)
    iLöb as "IH". iApply wp_repeat; [done|].
    wp_op. rewrite shift_0.

    (* open shared invariant *)
    iMod (view_inv_acc_base' with "[$Inv $vTok2]") as "(vTok2 & INV) {Inv}"; [done|].
    iDestruct "INV" as (Vb) "[INV Close]".
    rewrite {1}mp_inv_reclaim'_eq.
    iDestruct "INV" as (ζ' b t0 V0) "[Pts Own]".
    (* TODO: IntoLater for view join *)
    rewrite view_join_later. iDestruct "Pts" as ">Pts".

    (* actual read *)
    iApply (AtomicSeen_acquire_read_vj with "[$Pts $SeenV]"); [solve_ndisj|..].
    { by iApply (AtomicSync_AtomicSeen with "S"). }
    iIntros "!>" (t' v' V' V'' ζ'') "(HF & #SV' & SN' & Pts)".
    iDestruct "HF" as %([Sub1 Sub2] & Eqt' & MAX' & LeV'').

    case (decide (t' = t0)) => [?|NEqt'].
    + subst t'.
      (* we must have read the flag to be 0 (i.e. z = 0). *)
      iAssert (⌜v' = #0⌝)%I as %Eq0.
      { destruct b.
        - iDestruct "Own" as (t1 V1 [Lt1 Eqζ']) "_".
          iPureIntro.
          rewrite Eqζ' in Sub2. apply (lookup_weaken _ _ _ _ Eqt') in Sub2.
          rewrite lookup_insert_ne in Sub2.
          + rewrite lookup_insert in Sub2. by inversion Sub2.
          + clear -Lt1. intros ?. subst. lia.
        - iDestruct "Own" as %Eqζ'. iPureIntro.
          rewrite Eqζ' in Sub2. apply (lookup_weaken _ _ _ _ Eqt') in Sub2.
          rewrite lookup_insert in Sub2. by inversion Sub2. }
      (* then simply keep looping *)

      (* first close the invariant *)
      rewrite bi.and_elim_l.
      iMod ("Close" with "vTok2 [Pts Own]") as "vTok2".
      { iClear "IH". iNext. rewrite mp_inv_reclaim'_eq.
        iExists ζ', b, t0, V0. iSplitL "Pts"; by iFrame. }
      iIntros "!>". iExists 0. iSplit; [done|].
      (* then apply the Löb IH *)
      iIntros "!> !>". by iApply ("IH" with "Post DEL Hm vTok2").

    + destruct b; last first.
      { (* b cannot be false *)
        iDestruct "Own" as %Eqζ'. exfalso.
        rewrite Eqζ' in Sub2.
        apply (lookup_weaken _ _ _ _ Eqt'), lookup_singleton_Some in Sub2 as [].
        by apply NEqt'. }
      iClear "IH".
      (* we read 1, the destruct Own to get data. *)
      iDestruct "Own" as (t1 V1 [Lt1 Eqζ']) "Own".
      rewrite Eqζ' in Sub2. apply (lookup_weaken _ _ _ _ Eqt') in Sub2.
      have ? : t' = t1.
      { case (decide (t' = t1)) => [//|NEqt1].
        exfalso. by rewrite !lookup_insert_ne // in Sub2. }
      subst t'. rewrite lookup_insert in Sub2. inversion Sub2. subst v' V'.

      rewrite view_join_view_at.
      iDestruct (view_at_elim with "[SV'] Own") as "[m1 vTok1]".
      { iApply (monPred_in_mono with "SV'"). simpl. solve_lat. }

      (* cancel the invariant *)
      iCombine "vTok1" "vTok2" as "vTok".
      rewrite 2!bi.and_elim_r.
      iDestruct ("Close" with "vTok") as "[#LeVb >_]".
      iDestruct (view_join_elim with "Pts LeVb") as "Pts".
      iIntros "!>". iExists 1. iSplit; [done|]. simpl.
      iIntros "!> !>".

      wp_pures. wp_read. wp_let.

      iApply wp_hist_inv; [done|]. iIntros "HINV".
      iMod (AtomicPtsTo_to_na with "HINV Pts") as (t' v') "[m2 ?]"; [done|].
      (* dealloc the locations *)
      wp_apply (wp_delete _ tid 2 m [v'; #42] with "[m1 m2 $DEL]"); [done|done|..].
      { rewrite own_loc_na_vec_cons own_loc_na_vec_singleton. by iFrame. }
      iIntros "_". wp_seq. by iApply ("Post" $! 42).
Qed.
