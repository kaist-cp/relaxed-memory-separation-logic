From iris.proofmode Require Import proofmode.

From gpfsl.logic Require Import lifting.
From gpfsl.logic Require Import atomic_preds.
From gpfsl.gps Require Import cbends.
From gpfsl.gps Require Export model_defs.

Require Import iris.prelude.options.

Implicit Types (t : time) (v : val) (V : view) (ζ : absHist) (γ : gname).

Section Dealloc.
  Context `{!noprolG Σ, !gpsG Σ Prtcl, !atomicG Σ}
          (IP : interpO Σ Prtcl) (l : loc).
  Local Notation iProp := (iProp Σ).
  Local Notation vProp := (vProp Σ).
  Implicit Types
    (s : pr_stateT Prtcl) (χ : stateT Prtcl) (μ : time → pr_stateT Prtcl).

  Notation F := (IP true l).
  Notation F_read := (IP false l).

  (** DEALLOC *)
  Lemma GPSRaw_dealloc IW b γ bs E (SUB: ↑histN ⊆ E) :
    ⎡ hist_inv ⎤ -∗
    ▷?b gps_inv IP IW l γ bs ={E}=∗
    ∃ t s v, l ↦ v ∗ ▷?b F γ t s v.
  Proof.
    iIntros "#Inv".
    iDestruct 1 as (μ γs γl ζ tx) "(>%ENC & _ & >Pts & rB & _)".
    iMod (AtomicPtsToX_to_na with "Inv Pts") as (t v V) "(Pts & sV & F')"; [done|].
    iDestruct "F'" as %(Eqt & Letx & MAX).
    set s := μ t.
    have Eqs : toState μ ζ !! t = Some s by rewrite map_lookup_imap Eqt.
    iIntros "!>".
    iExists t, s, v. iFrame "Pts".
    iIntros "!>".
    have HLa : cbends ζ !! t = Some (v, V).
    { apply (top_write_block_end μ); [|done].
      intros t' InD. apply MAX, elem_of_dom.
      revert InD. apply dom_imap_subseteq. }
    rewrite /resBE /gps_res (big_sepM_lookup _ _ _ _ HLa) /= decide_True //.
    iApply (view_at_elim with "sV rB").
  Qed.

  Lemma GPSRaw_SW_dealloc IW b ζ t s v V γ γs γl bs E
    (SUB: ↑histN ⊆ E) (MAX: no_earlier_time ζ t) :
    γ = encode (γs, γl) →
    ⎡ hist_inv ⎤ -∗
    gps_snap γs {[t := s]} -∗
    l sy⊒{γl} {[t := (v, V)]} -∗
    l sw⊒{γl} ζ -∗
    ▷?b gps_inv IP IW l γ bs ={E}=∗
    l ↦ v ∗ ▷?b F γ t s v.
  Proof.
    iIntros (ENC) "#Inv SS SY W".
    iDestruct 1 as (μ γs' γl' ζ' tx) "(>%ENC' & >O & >Pts & rB & _)".
    rewrite ENC in ENC'. apply encode_inj, pair_inj in ENC' as [<- <-].
    iDestruct (AtomicPtsToX_AtomicSWriter_agree_2 with "Pts W") as %->.
    iMod (AtomicPtsToX_to_na with "Inv Pts") as (t' v' V') "(Pts & sV & F')";
      [done|].
    iDestruct "F'" as %(Eqt & Letx & MAX').
    iDestruct (AtomicSWriter_latest with "W [SY]") as %Sub%map_singleton_subseteq_l.
    { by iApply AtomicSync_AtomicSeen. }
    assert (t' = t) as ->.
    { apply : (anti_symm (⊑)); [apply MAX|apply MAX']; by eexists. }
    rewrite Eqt in Sub. simplify_eq.
    iFrame "Pts".
    iDestruct (gps_own_snap_singleton_sub with "O SS") as %Eqs.
    iIntros "!> !>".
    have HLa : cbends ζ !! t = Some (v, V).
    { apply (top_write_block_end μ); [|done].
      intros t' InD. apply MAX, elem_of_dom.
      revert InD. apply dom_imap_subseteq. }
    rewrite /resBE /gps_res (big_sepM_lookup _ _ _ _ HLa) /= decide_True //.
    assert (s = μ t) as ->.
    { rewrite map_lookup_imap Eqt /= in Eqs. by inversion Eqs. }
    iApply (view_at_elim with "sV rB").
  Qed.
End Dealloc.
