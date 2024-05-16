From iris.proofmode Require Import proofmode.

From gpfsl.base_logic Require Import iwp.
From gpfsl.base_logic Require Import vprop history.
From gpfsl.base_logic Require Import weakestpre base_lifting na.
From gpfsl.logic Require Import relacq.
From gpfsl.logic Require Import atomic_cmra atomic_ghost atomic_preds.

From gpfsl.lang Require Import notation.

Require Import iris.prelude.options.

Implicit Types (ζ : absHist) (l : loc) (t : time) (v : val) (V : view) (q : frac).

Section ops_rules.
Context `{!noprolG Σ, !atomicG Σ}.
#[local] Notation iProp := (iProp Σ).
#[local] Notation vProp := (vProp Σ).

(** * AtomicSeen read *)
Lemma AtomicSeen_readX l γ tx ζ ζ' mode o tid V Vb E :
  Relaxed ⊑ o → ↑histN ⊆ E →
  {{{ l sn⊒{γ} ζ' ∗ @{Vb} AtomicPtsToX l γ tx ζ mode ∗ ⊒V }}}
    Read o #l @ tid; E
  {{{ t' v' V' V'' ζ'', RET v';
      ⌜ζ' ⊆ ζ'' ⊆ ζ
        ∧ ζ'' !! t' = Some (v', V')
        ∧ no_earlier_time ζ' t'
        ∧ V ⊑ V''⌝
      ∗ ⊒V''
      ∗ (if decide (AcqRel ⊑ o) then ⌜V' ⊑ V''⌝ else ▽{tid} ⊒V')
      ∗ @{V''} l sn⊒{γ} ζ''
      ∗ @{Vb ⊔ V''} AtomicPtsToX l γ tx ζ mode }}}.
Proof.
  intros RLX SUB Φ. iStartProof iProp. iIntros (V0) "(SR & Pts & sV)".
  iIntros (V1 ->) "Post". iDestruct "sV" as %LeV1.
  rewrite wp_eq /wp_def /=.
  iIntros (𝓥 Le𝓥) "oL sV".
  rewrite AtomicPtsToX_eq /AtomicPtsToX_def AtomicSeen_eq /AtomicSeen_def.
  rewrite !view_at_unfold_2.
  iDestruct "Pts" as (C Va rsa rns ws (GH & Eqζ & IS & ND))
                    "((SL & ARL & AWL & NAL) & HC & (AR & AW & NA) & [SA SW])".
  iDestruct "SR" as "(SL' & SR & #NA')".
  iDestruct "NA'" as (? [(t'&m'&IS')%map_choose [C' [Eqζ' ND']]] LE) "NA'".
  iDestruct (at_auth_at_last_na_agree with "SA NA'") as %<-.
  iDestruct (at_auth_reader_latest with "SA SR") as "%INCL {SR}".
  iDestruct (SeenLocal_alloc_local l C' _ _ Va with "[SL']") as %AL'.
  { rewrite -Eqζ'. by exists m'. } { by rewrite -Eqζ'. }
  iAssert (⌜atr_local l rsa Vb⌝)%I as %?. { by iDestruct "ARL" as %?. }

  iApply iwp_fupd.
  iApply (iwp_read_atomic with "[$sV $HC $AR]"); [done| |done..|].
  { apply (absHist_alloc_local_mono _ _ C' C ζ' ζ Va); [done..|].
    by eapply alloc_local_mono. }

  iNext. iIntros (𝓥' v' ?) "(s' & hist & at & Ext)".
  iDestruct "Ext" as %(Le𝓥' & _ & t & m & HL & ISV & RH & AT').
  iMod (own_lat_auth_update with "oL") as "[$ oTV]"; [done|].
  iDestruct (at_auth_fork_at_reader with "SA") as "#SR".
  specialize (toAbsHist_lookup_state_inv C Va t m v' ISV HL) as AHL.

  set V' := default ∅ m.(mrel) ⊔ Va.
  set ζ'' := <[t := (v', V')]> ζ'.
  set V'' := 𝓥'.(cur).
  have INCL' : ζ' ⊆ ζ''.
  { destruct (ζ' !! t) as [vV'|] eqn:Eqt; last by apply insert_subseteq.
    rewrite -(insert_id _ _ _ Eqt) (_: vV' = (v', V')).
    + by apply insert_mono.
    + move : (INCL t). by rewrite Eqt Eqζ AHL /=. }
  have INCL'' : ζ'' ⊆ ζ.
  { subst ζ'' ζ. rewrite insert_union_singleton_l.
    eapply map_union_least; [by apply map_singleton_subseteq_l|done]. }
  have LEV1 : V1 ⊑ 𝓥'.(cur) by rewrite Le𝓥 Le𝓥'.
  iAssert (⌜ Va ⊑ 𝓥.(cur) ⌝)%I as %LeVa. { iPureIntro. by rewrite LE. }
  have LEV2: V' ⊑ if decide (AcqRel ⊑ o) then 𝓥'.(cur) else 𝓥'.(acq).
  { apply lat_join_lub; first by eapply read_helper_view_at.
    rewrite LeVa Le𝓥'; case decide => ?; [done|by apply cur_acq]. }

  iApply ("Post" $! t v' V' V'' ζ''). iModIntro.
  iAssert (⌜∀ t, is_Some (ζ' !! t) → seen_local l t 𝓥.(cur)⌝)%I with "[SL']" as %SL.
  { iApply SeenLocal_unfold. by iFrame. }
  iSplitR.
  { iPureIntro; split; [done|split]; [..|split].
    - by rewrite lookup_insert.
    - intros t0 IS0. change (Some t0 ⊑ Some t).
      etrans; [by apply SL|by inversion RH].
    - solve_lat. }
  iSplit; [done|].
  iSplitL "oTV".
  { rewrite /V'. case decide => ?; first by rewrite decide_True in LEV2.
    rewrite decide_False // in LEV2.
    rewrite acq_mod_eq /acq_mod_def /=. iExists _. by iFrame. }
  iSplitL "SL' SR".
  { rewrite view_at_unfold_2. iSplit; last iSplitR "".
    - iApply (SeenLocal_insert with "[] [SL']").
      + iPureIntro. by eapply read_helper_seen_local.
      + by iFrame "SL'".
    - by iApply (at_reader_extract _ _ _ INCL'' with "SR").
    - iExists Va. iFrame "#". iPureIntro.
      split; last first. { by rewrite LE LEV1. }
      eapply good_absHist_mono; eauto.
      + by apply insert_non_empty.
      + by eapply good_hist_good_absHist. }
  iExists _, _, _, _, _.
  iSplit; [done|]. rewrite view_at_unfold_2. by iFrame "∗%".
Qed.

Lemma AtomicSeen_read l γ ζ ζ' mode o tid V Vb E :
  Relaxed ⊑ o → ↑histN ⊆ E →
  {{{ l sn⊒{γ} ζ' ∗ @{Vb} AtomicPtsTo l γ ζ mode ∗ ⊒V }}}
    Read o #l @ tid; E
  {{{ t' v' V' V'' ζ'', RET v';
      ⌜ζ' ⊆ ζ'' ⊆ ζ
        ∧ ζ'' !! t' = Some (v', V')
        ∧ no_earlier_time ζ' t'
        ∧ V ⊑ V''⌝
      ∗ ⊒V''
      ∗ (if decide (AcqRel ⊑ o) then ⌜V' ⊑ V''⌝ else ▽{tid} ⊒V')
      ∗ @{V''} l sn⊒{γ} ζ''
      ∗ @{Vb ⊔ V''} AtomicPtsTo l γ ζ mode }}}.
Proof.
  intros RLX SUB Φ. rewrite AtomicPtsTo_eq. iIntros "(SR & [%tx Pts] & sV) Post".
  iApply (AtomicSeen_readX with "[$SR $Pts $sV]"); [done..|].
  iIntros "!>" (t' v' V' V'' ζ'') "(F & sV'' & sV' & Pts)".
  iApply "Post". iFrame. iDestruct "Pts" as "[$ Pts]". by iExists _.
Qed.

Lemma AtomicSeen_acquire_read l γ ζ ζ' mode tid V Vb E :
  ↑histN ⊆ E →
  {{{ l sn⊒{γ} ζ' ∗ @{Vb} AtomicPtsTo l γ ζ mode ∗ ⊒V }}}
    !ᵃᶜ#l @ tid; E
  {{{ t' v' V' V'' ζ'', RET v';
      ⌜ζ' ⊆ ζ'' ⊆ ζ
        ∧ ζ'' !! t' = Some (v', V')
        ∧ no_earlier_time ζ' t'
        ∧ V ⊔ V' ⊑ V''⌝
      ∗ ⊒V'' ∗ @{V''} l sn⊒{γ} ζ''
      ∗ @{Vb ⊔ V''} AtomicPtsTo l γ ζ mode }}}.
Proof.
  iIntros (SUB Φ) "Pre Post".
  iApply (AtomicSeen_read with "Pre"); [done|done|].
  simpl. iIntros "!>" (t' v' V' V'' ζ'') "(F & S'' & % & SN & P)".
  iApply "Post". iFrame "S'' SN P".
  iDestruct "F" as %(?&?&?&?). iPureIntro. do 3 (split; [done|]). solve_lat.
Qed.

Lemma AtomicSeen_relaxed_read l γ ζ ζ' mode tid V Vb E :
  ↑histN ⊆ E →
  {{{ l sn⊒{γ} ζ' ∗ @{Vb} AtomicPtsTo l γ ζ mode ∗ ⊒V }}}
    !ʳˡˣ#l @ tid; E
  {{{ t' v' V' V'' ζ'', RET v';
      ⌜ζ' ⊆ ζ'' ⊆ ζ
        ∧ ζ'' !! t' = Some (v', V')
        ∧ no_earlier_time ζ' t'
        ∧ V ⊑ V''⌝
      ∗ ⊒V'' ∗ ▽{tid}(⊒V') ∗ @{V''} l sn⊒{γ} ζ''
      ∗ @{Vb ⊔ V''} AtomicPtsTo l γ ζ mode }}}.
Proof.
  iIntros (? Φ) "Pre Post".
  iApply (AtomicSeen_read with "Pre"); [done|done|simpl; by iFrame].
Qed.


Lemma AtomicSync_readX l γ t ζ mode o tid V Vb E :
  Relaxed ⊑ o → ↑histN ⊆ E →
  {{{ l sy⊒{γ} ζ ∗ @{Vb} AtomicPtsToX l γ t ζ mode ∗ ⊒V }}}
    Read o #l @ tid; E
  {{{ t' v' V' V'', RET v';
      ⌜ζ !! t' = Some (v', V')
        ∧ no_earlier_time ζ t'
        ∧ V ⊔ V' ⊑ V''⌝
      ∗ ⊒V''
      ∗ @{Vb ⊔ V''} AtomicPtsToX l γ t ζ mode }}}.
Proof.
  iIntros (RLX SUB Φ) "(#SY & P & sV) Post".
  iDestruct (AtomicSync_AtomicSeen with "SY") as "#SS".
  iApply (AtomicSeen_readX with "[$SS $P $sV]"); [done..|].
  iIntros "!>" (t' v' V' V'' ζ'') "(F & Seen & _ & _ & P)".
  iApply ("Post" $! t' v' V' (V'' ⊔ V')). iFrame.
  iDestruct "F" as %([Le1 Le2] & Ht' & MAX & LeV'').
  have ?: ζ !! t' = Some (v', V') by eapply lookup_weaken.
  iSplit.
  - iPureIntro. do 2 (split; [done|]). solve_lat.
  - iApply monPred_in_view_op. iFrame. by iApply (AtomicSync_lookup with "SY").
Qed.

Lemma AtomicSync_read l γ ζ mode o tid V Vb E :
  Relaxed ⊑ o → ↑histN ⊆ E →
  {{{ l sy⊒{γ} ζ ∗ @{Vb} AtomicPtsTo l γ ζ mode ∗ ⊒V }}}
    Read o #l @ tid; E
  {{{ t' v' V' V'', RET v';
      ⌜ζ !! t' = Some (v', V')
        ∧ no_earlier_time ζ t'
        ∧ V ⊔ V' ⊑ V''⌝
      ∗ ⊒V''
      ∗ @{Vb ⊔ V''} AtomicPtsTo l γ ζ mode }}}.
Proof.
  intros RLX SUB Φ. rewrite AtomicPtsTo_eq. iIntros "(SR & [%tx Pts] & sV) Post".
  iApply (AtomicSync_readX with "[$SR $Pts $sV]"); [done..|].
  iIntros "!>" (t' v' V' V'') "(F & sV'' & Pts)".
  iApply "Post". iFrame "F sV''". by iExists _.
Qed.


Lemma AtomicSWriter_readX l γ t ζ mode o tid V Vb E :
  Relaxed ⊑ o → ↑histN ⊆ E →
  {{{ l sw⊒{γ} ζ ∗ @{Vb} AtomicPtsToX l γ t ζ mode ∗ ⊒V }}}
    Read o #l @ tid; E
  {{{ t' v' V' V'', RET v';
      ⌜ζ !! t' = Some (v', V')
        ∧ no_earlier_time ζ t'
        ∧ V ⊔ V' ⊑ V''⌝
      ∗ ⊒V'' ∗ l sw⊒{γ} ζ
      ∗ @{Vb ⊔ V''} AtomicPtsToX l γ t ζ mode }}}.
Proof.
  iIntros (RLX SUB Φ) "(SW & P & sV) Post".
  iDestruct (AtomicSWriter_AtomicSync with "SW") as "#SY".
  iApply (AtomicSync_readX with "[$SY $P $sV]"); [done..|].
  iIntros "!>" (t' v' V' V'') "(F & Seen & P)".
  iApply ("Post" $! t' v' V' V''). iFrame.
Qed.

Lemma AtomicSWriter_read l γ ζ mode o tid V Vb E :
  Relaxed ⊑ o → ↑histN ⊆ E →
  {{{ l sw⊒{γ} ζ ∗ @{Vb} AtomicPtsTo l γ ζ mode ∗ ⊒V }}}
    Read o #l @ tid; E
  {{{ t' v' V' V'', RET v';
      ⌜ζ !! t' = Some (v', V')
        ∧ no_earlier_time ζ t'
        ∧ V ⊔ V' ⊑ V''⌝
      ∗ ⊒V'' ∗ l sw⊒{γ} ζ
      ∗ @{Vb ⊔ V''} AtomicPtsTo l γ ζ mode }}}.
Proof.
  intros RLX SUB Φ. rewrite AtomicPtsTo_eq. iIntros "(SR & [%tx Pts] & sV) Post".
  iApply (AtomicSWriter_readX with "[$SR $Pts $sV]"); [done..|].
  iIntros "!>" (t' v' V' V'') "(F & sV'' & W & Pts)".
  iApply "Post". iFrame "F sV'' W". by iExists _.
Qed.

Lemma AtomicCASer_read l γ ζ ζ' q mode o tid V Vb E :
  Relaxed ⊑ o → ↑histN ⊆ E →
  {{{ l cas⊒{γ,q} ζ' ∗ @{Vb} AtomicPtsTo l γ ζ mode ∗ ⊒V }}}
    Read o #l @ tid; E
  {{{ t' v' V' V'' ζ'', RET v';
      ⌜ζ' ⊆ ζ'' ⊆ ζ
        ∧ ζ'' !! t' = Some (v', V')
        ∧ no_earlier_time ζ' t'
        ∧ V ⊑ V''⌝
      ∗ ⊒V''
      ∗ (if decide (AcqRel ⊑ o) then ⌜V' ⊑ V''⌝ else ▽{tid} ⊒V')
      ∗ @{V''} l cas⊒{γ,q} ζ''
      ∗ @{Vb ⊔ V''} AtomicPtsTo l γ ζ mode }}}.
Proof.
  iIntros (RLX SUB Φ) "(C & P & sV) Post".
  iDestruct (AtomicCASer_AtomicSeen with "C") as "#SS".
  iApply wp_fupd.
  iDestruct (view_at_intro_incl with "C sV ") as (V0) "(sV0 & %LeV & C0)".
  iApply (AtomicSeen_read with "[$SS $P $sV0]"); [done..|].
  iIntros "!>" (t' v' V' V'' ζ'') "(F & sV'' & sV' & SS' & P)".
  iDestruct "F" as %([Le1 Le2] & Eqt' & MAX & LeV0).
  assert (V ⊑ V'') by solve_lat.
  iDestruct (view_at_mono_2 _ _ _ LeV0 with "C0") as "C".
  rewrite AtomicCASer_AtomicSeen_update_join. iDestruct ("C" with "SS'") as "C".
  rewrite (map_subseteq_union _ _ Le1).
  iIntros "!>". iApply "Post". by iFrame.
Qed.

#[local] Definition own_writer γ (m : AtomicMode) (q : frac) ζ tx : iProp :=
  match m with
    | SingleWriter => at_writer γ ζ ∗ at_exclusive_write γ tx 1%Qp
    | CASOnly => at_exclusive_write γ tx q
    | ConcurrentWriter => True
    end.

(** * AtomicSeen write *)
Lemma AtomicSeen_writeX
  l γ ζ' ζ (m : AtomicMode) q (tx tx' : time) o tid (Vrel : view) V Vb v' E :
  Relaxed ⊑ o →
  ↑histN ⊆ E →
  {{{ l sn⊒{γ} ζ' ∗ ⎡ own_writer γ m q ζ' tx' ⎤ ∗
      @{Vb} AtomicPtsToX l γ tx ζ m ∗ ⊒V ∗
      (if decide (AcqRel ⊑ o) then True else △{tid} ⊒Vrel) }}}
    Write o #l v' @ tid; E
  {{{ (t' : time) V' V'', RET #☠;
      ⌜ fresh_max_time ζ' t'
        ∧ ζ !! t' = None
        ∧ V ⊑ V'' ∧ V ≠ V'' ∧ (¬ V' ⊑ V)
        ∧ if decide (AcqRel ⊑ o) then V'' = V' else Vrel ⊑ V' ∧ V' ⊑ V''⌝ ∗
      ⊒V'' ∗
      let ζ'' : absHist := <[t' := (v',V')]>ζ' in
      @{V''} l sn⊒{γ} ζ'' ∗
      ⎡ own_writer γ m q ζ'' (if m is SingleWriter then t' else tx') ⎤ ∗
      @{V''} l sy⊒{γ} {[t' := (v', V')]} ∗
      @{V'} l sn⊒{γ} {[t' := (v', V')]} ∗
      let ζn : absHist := <[t' := (v',V')]>ζ in
      @{Vb ⊔ V''} AtomicPtsToX l γ (if m is SingleWriter then t' else tx) ζn m }}}.
Proof.
  intros RLX SUB Φ. iStartProof iProp. iIntros (V0) "(#SR & W & Pts & sV & HV)".
  iIntros (V1 ->) "Post". iDestruct "sV" as %LeV1.
  rewrite wp_eq /wp_def /=.
  iIntros (𝓥 Le𝓥) "oL sV".
  rewrite AtomicPtsToX_eq /AtomicPtsToX_def.
  rewrite !view_at_unfold_2.
  iDestruct "Pts" as (C Va rsa rns ws (GH & Eqζ & IS & ND))
                    "((SL & ARL & AWL & NAL) & HC & (AR & AW & NA) & [SA SW])".
  rewrite AtomicSeen_eq /AtomicSeen_def.
  iDestruct "SR" as "(SL' & SR & NA')".
  iDestruct "NA'" as (? [(t'&m'&IS')%map_choose [C' [Eqζ' ND']]] LeVa) "NA'".
  iDestruct (at_auth_at_last_na_agree with "SA NA'") as %<-.
  iAssert (⌜ na_local l rns Va ⌝)%I with "[NAL]" as %NAL.
  { iDestruct "NAL" as "[$ ?]". }

  iDestruct (at_auth_reader_latest with "SA SR") as %INCL.
  iDestruct (SeenLocal_alloc_local l C' _ _ Va with "[SL']") as %AL'.
  { rewrite -Eqζ'. by exists m'. } { by rewrite -Eqζ'. }
  iAssert (⌜atw_local l ws Vb⌝)%I as %?. { by iDestruct "AWL" as %?. }

  iApply iwp_fupd.
  iApply (base_lifting.iwp_write_atomic with "[$sV $HC $NA $AW]");
    [done| | |done|done|..].
  { apply (absHist_alloc_local_mono _ _ C' C ζ' ζ Va); [done..|].
    by eapply alloc_local_mono. }
  { eapply na_local_mono; [..|eauto]; [done|solve_lat]. }

  iIntros "!>" (𝓥' Cn tn) "(sV' & HC' & NA & AT' & %F)".
  destruct F as (Le𝓥' & _ & GH' & AW' & mn & -> & Eqt' & Eqv' & ADD & NEQV & NLEV & WH).

  have Ext': 𝓥.(cur) !!w l ⊏ Some tn by inversion WH.

  have HN: toAbsHist C Va !! tn = None by rewrite /toAbsHist map_lookup_imap Eqt'.
  set V' := default ∅ mn.(mrel) ⊔ Va.
  set ζ'' : absHist := <[tn:=(v', V')]> ζ'.
  set ζn : absHist := <[tn:=(v', V')]> ζ.
  set txn := (if m is SingleWriter then tn else tx).
  set txn' := (if m is SingleWriter then tn else tx').

  have HN' : ζ' !! tn = None.
  { eapply lookup_weaken_None; eauto. by rewrite -Eqζ. }
  have SUBn : ζ'' ⊆ ζn by apply insert_mono.

  iAssert (⌜if decide (AcqRel ⊑ o) then V1 ⊑ V' else Vrel ⊑ V'⌝)%I
    with "[HV oL]" as %LeV.
  { case (decide (AcqRel ⊑ o)) => Ho.
    - iPureIntro. rewrite Le𝓥 /V'; etrans; last apply lat_join_sqsubseteq_l.
      clear -WH Ho. apply write_helper_release_seqcst_mrel in WH; [|done].
      destruct mn.(mrel); [|done]. simpl. cbn in WH. solve_lat.
    - iDestruct (rel_at_unfold with "HV oL") as "[%LeVrel _]". iPureIntro.
      rewrite LeVrel /V'; etrans; last apply lat_join_sqsubseteq_l.
      have ? : o = Relaxed by destruct o. subst o.
      clear -WH. apply write_helper_relaxed_mrel in WH.
      destruct mn.(mrel) ; [|done]. simpl. cbn in WH. solve_lat. }

  iAssert (⌜ fresh_max_time ζ' tn ⌝)%I with "[]" as %FMAX'.
  { rewrite SeenLocal_unfold. iDestruct "SL'" as %SL.
    iPureIntro. intros t IS1.
    have Ext2: t ⊏ tn.
    { change (Some t ⊏ Some tn). eapply strict_transitive_r; [|apply Ext'].
      etrans; [by apply SL|by apply view_sqsubseteq]. }
    by apply Pos.lt_nle, Ext2. }
  have MAX' : no_earlier_time ζ' tn.
  { clear -FMAX'. intros t IS1. by apply Pos.lt_le_incl, FMAX'. }

  iAssert (|==> at_auth γ ζn txn Va ∗
            match m with
            | SingleWriter => True
            | CASOnly => at_writer γ ζn
            | ConcurrentWriter => at_writer γ ζn ∗ at_exclusive_write γ txn 1
            end ∗
            own_writer γ m q ζ'' txn' ∗ at_reader γ ζ'')%I
            with "[SA SW W]" as ">(SA' & SW' & W' & #SR')".
  { iDestruct "SA" as "(SAW & SAE & $)".
    rewrite /own_writer. rewrite -Eqζ in HN. destruct m.
    - iDestruct "W" as "[W SE]".
      iDestruct (at_auth_writer_exact with "SAW W") as %<-.
      iMod (at_writer_update_insert_at_reader _ _ _ _ _ HN' with "SAW W")
        as "($ & SW' & _)".
      iDestruct (at_writer_fork_at_reader with "SW'") as "#$".
      iDestruct (at_auth_exclusive_write_agree with "SAE SE") as %<-.
      iMod (at_exclusive_write_update _ _ txn with "SAE SE") as "[$ $]".
      iIntros "!>". iFrame "SW'".
    - iDestruct (at_auth_exclusive_write_agree with "SAE W") as %<-.
      iMod (at_writer_update_insert_at_reader _ _ _ _ _ HN with "SAW SW")
        as "($ & SW' & _)".
      iDestruct (at_writer_fork_at_reader_sub with "SW'") as "#$"; [done|by iFrame].
    - iDestruct "SW" as "[SW SE]".
      iMod (at_writer_update_insert_at_reader _ _ _ _ _ HN with "SAW SW")
        as "($ & SW' & _)".
      iMod (at_exclusive_write_update _ _ txn with "SAE SE") as "[$ $]".
      iDestruct (at_writer_fork_at_reader_sub with "SW'") as "#$"; done. }

  iMod (own_lat_auth_update with "oL") as "[$ oL']"; [done|].

  have LEV1 : V1 ⊑ 𝓥'.(cur). { etrans; [by apply Le𝓥|by apply Le𝓥']. }
  have Lem2: V' ⊑  𝓥'.(cur). {
    apply lat_join_lub; [|solve_lat].
    assert (LE:= write_helper_cur_tview_include WH ltac:(done)). clear -LE.
    by destruct mn.(mrel). }
  have SL' : seen_local l tn V'.
  { eapply seen_local_mono; last by eapply write_helper_seen_local_write.
    rewrite /V'. clear; solve_lat. }
  have Gζn : good_absHist ζn Va.
  { eapply good_hist_good_absHist; eauto.
    rewrite /ζn Eqζ -toAbsHist_insert // Eqv'. by constructor. }

  iApply ("Post" $! tn V' 𝓥'.(cur)). iIntros "!>".
  rewrite !view_at_unfold_2.
  have Sub'': {[tn := (v', V')]} ⊆ ζ'' by apply insert_mono, gmap_subseteq_empty.
  iDestruct (at_reader_extract _ _ _ Sub'' with "SR'") as "SR''".
  have GH'' : good_absHist {[tn := (v', V')]} Va.
  { eapply good_absHist_mono; [apply insert_non_empty| |exact Gζn]. by etrans. }

  have LeVa' : Va ⊑ 𝓥'.(cur). { by rewrite LeVa LEV1. }
  iSplit; last iSplit; last iSplitR; last iSplitL "W'"; last iSplitR;
    last iSplitR; [|done|..].
  - iPureIntro. split; [done|]. split; last split; last split; last split.
    + by rewrite Eqζ.
    + solve_lat.
    + clear -LeV1 Le𝓥 NEQV Le𝓥'. intros ->. apply NEQV.
      apply : (anti_symm (⊑)); [by apply cur_mono|solve_lat].
    + clear -LeV1 Le𝓥 NLEV. subst V'. intros LE. apply NLEV. solve_lat.
    + case decide => Ho.
      * apply : anti_symm; simpl; [done|].
        rewrite /V'. etrans; last apply lat_join_sqsubseteq_l.
        change (Some 𝓥'.(cur) ⊑ Some (default ∅ mn.(mrel))).
        clear -WH Ho. apply write_helper_release_seqcst_mrel_cur in WH; [|done].
        by destruct mn.(mrel).
      * by rewrite decide_False // in LeV.
  - iFrame "SR'". iSplit.
    + iApply (SeenLocal_insert with "[] []"); last by iFrame "SL'".
      iPureIntro. clear LeVa'. by eapply seen_local_mono.
    + iExists Va. iFrame "NA'". iPureIntro. split; [|done].
      eapply good_absHist_mono; [apply insert_non_empty|exact SUBn|exact Gζn].
  - by iFrame "W'".
  - rewrite AtomicSync_eq /AtomicSync_def. iFrame "SR''". iSplit.
    + iApply SeenLocal_SyncLocal_singleton; first done.
      rewrite SeenLocal_unfold_singleton. iPureIntro.
      clear LeVa'. by eapply seen_local_mono.
    + iExists Va. by iFrame "NA'".
  - iFrame "SR''". iSplit.
    + rewrite SeenLocal_unfold_singleton. by iPureIntro.
    + iExists Va. iSplit; [done|]. iFrame "NA'".
      iPureIntro. clear; rewrite /V'; solve_lat.
  - iExists (<[tn:=mn]> C), Va, rsa, rns, _. iFrame.
    iSplit; last iSplit.
    + iPureIntro. split; [done|]. repeat split.
      * rewrite Eqζ. symmetry. apply toAbsHist_insert.
        rewrite Eqv'. by constructor.
      * have ? : tn ≠ tx.
        { intros ?. subst tx. rewrite Eqζ HN in IS. by destruct IS. }
        destruct m; [|by rewrite lookup_insert_ne..].
        rewrite lookup_insert. by eexists.
      * intros t0 m0. case (decide (t0 = tn)) => [->|?].
        { rewrite lookup_insert => [[<-]]. by rewrite Eqv'. }
        { rewrite lookup_insert_ne //. by apply ND. }
    + iApply (SyncLocal_insert with "[] [SL]"); last by iFrame "SL".
      iPureIntro. split; [|solve_lat].
      eapply seen_local_mono; last eauto. solve_lat.
    + by iFrame (AW').
Qed.

Lemma AtomicSeen_write
  l γ ζ' ζ (m : AtomicMode) q (tx' : time) o tid (Vrel : view) V Vb v' E :
  Relaxed ⊑ o →
  ↑histN ⊆ E →
  {{{ l sn⊒{γ} ζ' ∗ ⎡ own_writer γ m q ζ' tx' ⎤ ∗
      @{Vb} AtomicPtsTo l γ ζ m ∗ ⊒V ∗
      (if decide (AcqRel ⊑ o) then True else △{tid} ⊒Vrel) }}}
    Write o #l v' @ tid; E
  {{{ (t' : time) V' V'', RET #☠;
      ⌜ fresh_max_time ζ' t'
        ∧ ζ !! t' = None
        ∧ V ⊑ V'' ∧ V ≠ V'' ∧ (¬ V' ⊑ V)
        ∧ if decide (AcqRel ⊑ o) then V'' = V' else Vrel ⊑ V' ∧ V' ⊑ V''⌝ ∗
      ⊒V'' ∗
      let ζ'' : absHist := <[t' := (v',V')]>ζ' in
      @{V''} l sn⊒{γ} ζ'' ∗
      ⎡ own_writer γ m q ζ'' (if m is SingleWriter then t' else tx') ⎤ ∗
      @{V''} l sy⊒{γ} {[t' := (v', V')]} ∗
      let ζn : absHist := <[t' := (v',V')]>ζ in
      @{Vb ⊔ V''} AtomicPtsTo l γ ζn m }}}.
Proof.
  rewrite AtomicPtsTo_eq.
  iIntros (RLX SUB Φ) "(SR & W & [%tx Pts] & HV) Post".
  iApply (AtomicSeen_writeX with "[$SR $W $Pts $HV]"); [done..|].
  iIntros "!>" (t' V' V'') "(F & sV' & SS' & W & SY & ? & P)".
  iApply "Post". iFrame "F sV' SS' W SY". iExists _. iFrame.
Qed.

Lemma AtomicSeen_write_vj
  l γ ζ' ζ (m : AtomicMode) q (tx' : time) o tid (Vrel : view) V Vb v' E :
  Relaxed ⊑ o →
  ↑histN ⊆ E →
  {{{ l sn⊒{γ} ζ' ∗ ⎡ own_writer γ m q ζ' tx' ⎤ ∗
      ⊔{Vb} AtomicPtsTo l γ ζ m ∗ ⊒V ∗
      (if decide (AcqRel ⊑ o) then True else △{tid} ⊒Vrel) }}}
    Write o #l v' @ tid; E
  {{{ (t' : time) V' V'', RET #☠;
      ⌜ fresh_max_time ζ' t'
        ∧ ζ !! t' = None
        ∧ V ⊑ V'' ∧ V ≠ V'' ∧ (¬ V' ⊑ V)
        ∧ if decide (AcqRel ⊑ o) then V'' = V' else Vrel ⊑ V' ∧ V' ⊑ V''⌝ ∗
      ⊒V'' ∗
      let ζ'' : absHist := <[t' := (v',V')]>ζ' in
      @{V''} l sn⊒{γ} ζ'' ∗
      ⎡ own_writer γ m q ζ'' (if m is SingleWriter then t' else tx') ⎤ ∗
      @{V''} l sy⊒{γ} {[t' := (v', V')]} ∗
      let ζn : absHist := <[t' := (v',V')]>ζ in
      ⊔{Vb} AtomicPtsTo l γ ζn m }}}.
Proof.
  iIntros (RLX HN Φ) "(SN & oW & Pts & sV & HRel) Post".
  iDestruct (view_join_elim' with "Pts sV") as (V') "(#sV' & % & P)".
  iApply (AtomicSeen_write with "[$SN $oW $P $sV' $HRel]"); [done..|].
  iIntros "!>" (t' V2 V3) "(F & #sV3 & SN' & oW & SY & P)".
  rewrite -lat_join_assoc_L lat_join_comm_L.
  iDestruct (view_join_intro_at with "P []") as "P".
  { rewrite -monPred_in_view_op. by iFrame "#". }
  iApply ("Post" $! t' V2 V3). iFrame "# ∗".
  iDestruct "F" as %(?&?&? & NEQV & NLEV & ?). iPureIntro.
  do 2 (split; [done|]). split; [solve_lat|].
  split; last split; last done.
  - intros ->. apply NEQV. by apply : (anti_symm (⊑)).
  - intros NLEV'. apply NLEV. solve_lat.
Qed.

(** AtomicSeen write concurrent *)
Lemma AtomicSeen_concurrent_writeX l γ ζ' t ζ o tid (Vrel : view) V Vb v' E :
  Relaxed ⊑ o →
  ↑histN ⊆ E →
  {{{ l sn⊒{γ} ζ' ∗ @{Vb} l atX↦{γ,t} ζ ∗ ⊒V ∗
      (if decide (AcqRel ⊑ o) then True else △{tid} ⊒Vrel) }}}
    Write o #l v' @ tid; E
  {{{ t' V' V'', RET #☠;
      ⌜ fresh_max_time ζ' t'
        ∧ ζ !! t' = None
        ∧ V ⊑ V'' ∧ V ≠ V'' ∧ (¬ V' ⊑ V)
        ∧ if decide (AcqRel ⊑ o) then V'' = V' else Vrel ⊑ V' ∧ V' ⊑ V''⌝ ∗
      ⊒V'' ∗
      @{V'} l sn⊒{γ} {[t' := (v', V')]} ∗
      let ζ'' := <[t' := (v',V')]>ζ' in let ζn := <[t' := (v',V')]>ζ in
      @{V''} l sn⊒{γ} ζ'' ∗
      @{Vb ⊔ V''} l atX↦{γ,t} ζn }}}.
Proof.
  iIntros (RLX SUB Φ) "(SS & Pts & sV & HV) Post".
  iApply (AtomicSeen_writeX _ _ _ _ _ 1 t t with "[$SS $Pts $sV $HV]"); [done..|].
  iIntros "!>" (t' V' V'') "(F & #sV'' & SN' & SN'' & _ & SY' & Pts)".
  iApply ("Post" $! t' V' V''). by iFrame "∗#".
Qed.

Lemma AtomicSeen_concurrent_write l γ ζ' ζ o tid (Vrel : view) V Vb v' E :
  Relaxed ⊑ o →
  ↑histN ⊆ E →
  {{{ l sn⊒{γ} ζ' ∗ @{Vb} l at↦{γ} ζ ∗ ⊒V ∗
      (if decide (AcqRel ⊑ o) then True else △{tid} ⊒Vrel) }}}
    Write o #l v' @ tid; E
  {{{ t' V' V'', RET #☠;
      ⌜ fresh_max_time ζ' t'
        ∧ ζ !! t' = None
        ∧ V ⊑ V'' ∧ V ≠ V'' ∧ (¬ V' ⊑ V)
        ∧ if decide (AcqRel ⊑ o) then V'' = V' else Vrel ⊑ V' ∧ V' ⊑ V''⌝ ∗
      ⊒V'' ∗
      let ζ'' := <[t' := (v',V')]>ζ' in let ζn := <[t' := (v',V')]>ζ in
      @{V''} l sn⊒{γ} ζ'' ∗ @{Vb ⊔ V''} l at↦{γ} ζn }}}.
Proof.
  iIntros (RLX SUB Φ) "(SS & Pts & sV & HV) Post".
  iApply (AtomicSeen_write _ _ _ _ _ 1 1 with "[$SS $Pts $sV $HV]"); [done..|].

  iIntros "!>" (t' V' V'') "(F & #sV'' & SN' & _ & SY' & Pts)".
  iApply ("Post" $! t' V' V''). by iFrame "∗#".
Qed.

(** AtomicCASer concurrent write *)
Lemma AtomicCASer_write l γ q ζ' ζ o tid (Vrel : view) V Vb v' E :
  Relaxed ⊑ o →
  ↑histN ⊆ E →
  {{{ l cas⊒{γ,q} ζ' ∗ @{Vb} l cas↦{γ} ζ ∗ ⊒V ∗
      (if decide (AcqRel ⊑ o) then True else △{tid} ⊒Vrel) }}}
    Write o #l v' @ tid; E
  {{{ t' V' V'', RET #☠;
      ⌜ fresh_max_time ζ' t'
        ∧ ζ !! t' = None
        ∧ V ⊑ V'' ∧ V ≠ V'' ∧ (¬ V' ⊑ V)
        ∧ if decide (AcqRel ⊑ o) then V'' = V' else Vrel ⊑ V' ∧ V' ⊑ V''⌝ ∗
      ⊒V'' ∗
      let ζ'' := <[t' := (v',V')]>ζ' in let ζn := <[t' := (v',V')]>ζ in
      @{V''} l cas⊒{γ,q} ζ'' ∗ @{Vb ⊔ V''} l cas↦{γ} ζn }}}.
Proof.
  iIntros (RLX SUB Φ) "(C & Pts & sV & HV) Post".
  rewrite AtomicCASer_eq /AtomicCASer_def AtomicCASerX_eq.
  iDestruct "C" as (tx') "[SS [SE %IS]]".

  iApply (AtomicSeen_write _ _ _ _ _ q tx' with "[$SS $Pts SE $sV $HV]");
    [done..|].
  iIntros "!>" (t' V' V'') "(F & sV'' & SN' & SE & SY & Pts)".
  iApply ("Post" $! t' V' V''). iFrame.
  iExists tx'. iFrame "SE". iPureIntro.
  case (decide (tx' = t')) => [->|?].
  - rewrite lookup_insert. by eexists.
  - by rewrite lookup_insert_ne.
Qed.

(* SW writes *)
Lemma AtomicSWriter_writeX l γ tx ζ o tid (Vrel : view) V Vb v' E :
  Relaxed ⊑ o →
  ↑histN ⊆ E →
  {{{ l sw⊒{γ} ζ ∗ @{Vb} l swX↦{γ,tx} ζ ∗ ⊒V ∗
      (if decide (AcqRel ⊑ o) then True else △{tid} ⊒Vrel) }}}
    Write o #l v' @ tid; E
  {{{ t' V' V'', RET #☠;
      ⌜ fresh_max_time ζ t'
        ∧ ζ !! t' = None
        ∧ V ⊑ V'' ∧ V ≠ V'' ∧ (¬ V' ⊑ V)
        ∧ if decide (AcqRel ⊑ o) then V'' = V' else Vrel ⊑ V' ∧ V' ⊑ V''⌝ ∗
      ⊒V'' ∗
      let ζ' := <[t' := (v',V')]>ζ in
      @{V''} l sw⊒{γ} ζ' ∗ @{Vb ⊔ V''} l swX↦{γ,t'} ζ' }}}.
Proof.
  iIntros (RLX SUB Φ) "(SW & Pts & sV & HV) Post".
  rewrite AtomicSWriter_eq.
  iDestruct "SW" as "[[SS SW] S]". iDestruct "S" as (tx') "[SE %MAX]".

  iDestruct (AtomicSync_AtomicSeen with "SS") as "#SN".
  iDestruct (view_at_intro_incl with "SS sV") as (V0) "(sV0 & % & SS)".
  iApply (AtomicSeen_writeX _ _ _ _ _ 1 with "[$SN SW SE $Pts $sV0 $HV]");
    [done..|by iFrame|].

  iIntros "!>" (t' V' V'') "(F & #sV'' & SN' & [SW SE] & SY' & SN'' & Pts)".
  iDestruct "F" as %(MAX' & HN & LeV'' & NEQV & NLEV & LeV').
  iApply ("Post" $! t' V' V''). iSplit.
  { iPureIntro. do 2 (split; [done|]). split; [solve_lat|].
    split; last split; last done.
    - intros ->. apply NEQV. by apply : (anti_symm (⊑)).
    - intros NLEV'. apply NLEV. solve_lat. }
  iFrame "sV'' Pts SW". iSplit.
  - iClear "SN' SE SN". rewrite insert_union_singleton_l LeV''.
    iCombine "SS SY'" as "SY".
    iApply (view_at_wand with "[] SY"). iApply view_at_at.
    iIntros "[SS SY]". by iApply (AtomicSync_join with "SY SS").
  - iExists t'. iFrame. iPureIntro.
    split. { eexists. by rewrite lookup_insert. }
    intros t0 [vV0 Eq0]. case (decide (t0 = t')) => [->//|?].
    rewrite lookup_insert_ne // in Eq0. apply Pos.lt_le_incl, MAX'. by eexists.
Qed.
Lemma AtomicSWriter_write l γ ζ o tid (Vrel : view) V Vb v' E :
  Relaxed ⊑ o →
  ↑histN ⊆ E →
  {{{ l sw⊒{γ} ζ ∗ @{Vb} l sw↦{γ} ζ ∗ ⊒V ∗
      (if decide (AcqRel ⊑ o) then True else △{tid} ⊒Vrel) }}}
    Write o #l v' @ tid; E
  {{{ t' V' V'', RET #☠;
      ⌜ fresh_max_time ζ t'
        ∧ V ⊑ V'' ∧ V ≠ V'' ∧ (¬ V' ⊑ V)
        ∧ if decide (AcqRel ⊑ o) then V'' = V' else Vrel ⊑ V' ∧ V' ⊑ V''⌝ ∗
      ⊒V'' ∗
      let ζ' := <[t' := (v',V')]>ζ in
      @{V''} l sw⊒{γ} ζ' ∗ @{Vb ⊔ V''} l sw↦{γ} ζ' }}}.
Proof.
  rewrite AtomicPtsTo_eq.
  iIntros (RLX SUB Φ) "(SW & [%tx Pts] & sV & HV) Post".
  iApply (AtomicSWriter_writeX with "[$SW $Pts $HV $sV]"); [done..|].
  iIntros "!>" (t' V' V'') "(F & sV' & SS' & W)".
  iApply "Post". iDestruct "F" as %(?&?&?). iSplit; [done|].
  iFrame "sV' SS'". iExists _. iFrame.
Qed.

Lemma AtomicSWriter_write_resource l γ ζ o tid (Vrel : view) V Vb v' P E :
  Relaxed ⊑ o →
  ↑histN ⊆ E →
  {{{ l sw⊒{γ} ζ ∗ @{Vb} l sw↦{γ} ζ ∗ ⊒V ∗
    (if decide (AcqRel ⊑ o) then P else @{Vrel} P ∗ △{tid} ⊒Vrel) }}}
    Write o #l v' @ tid; E
  {{{ t' V' V'', RET #☠;
      ⌜ fresh_max_time ζ t'
        ∧ V ⊑ V'' ∧ V ≠ V'' ∧ (¬ V' ⊑ V)
        ∧ if decide (AcqRel ⊑ o) then V'' = V' else Vrel ⊑ V' ∧ V' ⊑ V''⌝ ∗
      ⊒V'' ∗ @{V'} P ∗
      let ζ' := <[t' := (v',V')]>ζ in
      @{V''} l sw⊒{γ} ζ' ∗ @{Vb ⊔ V''} l sw↦{γ} ζ' }}}.
Proof.
  iIntros (RLX SUB Φ) "(SW & Pts & #sV & P) Post".
  set Hrel : vProp := (if decide (AcqRel ⊑ o) then True else △{tid} (⊒Vrel))%I.
  iAssert (Hrel ∗ ∃ V0, ⊒V0 ∧ ⌜V ⊑ V0⌝ ∧
          if decide (AcqRel ⊑ o) then @{V0} P else @{Vrel} P)%I
          with "[P]" as "[sVrel P]".
  { rewrite /Hrel.
    case decide => ?.
    - iSplit; [done|]. by iApply (view_at_intro_incl with "P sV").
    - iDestruct "P" as "[P $]". iExists V. by iFrame "sV P". }
  iDestruct "P" as (V0) "(sV0 & %LeV0 & P)".
  iApply (AtomicSWriter_write with "[$SW $Pts $sV0 $sVrel]"); [done..|].
  iIntros "!>" (t' V' V'') "(F & sV'' & SW & Pts)".
  iDestruct "F" as %(MAX & LeV'' & NEQV & NLEV & HV'').
  iApply ("Post" $! _ V' V''). iFrame. iSplit.
  { iPureIntro. split; [done|]. split; [solve_lat|].
    split; last split; last done.
    - intros ->. apply NEQV. by apply : (anti_symm (⊑)).
    - intros NLEV'. apply NLEV. solve_lat. }
  case decide => ?.
  - rewrite decide_True // in HV''. subst V'. by iFrame.
  - rewrite decide_False // in HV''. destruct HV''. by iFrame.
Qed.

Lemma AtomicSWriter_release_write l γ ζ tid V Vb v' P E :
  ↑histN ⊆ E →
  {{{ l sw⊒{γ} ζ ∗ @{Vb} l sw↦{γ} ζ ∗ P ∗ ⊒V }}}
    #l <-ʳᵉˡ v' @ tid; E
  {{{ t' V', RET #☠;
      ⌜ fresh_max_time ζ t' ∧ V ⊑ V' ∧ V ≠ V' ⌝ ∗ ⊒V' ∗
      let ζ' := <[t' := (v',V')]>ζ in
      @{V'} (P ∗ l sw⊒{γ} ζ') ∗ @{Vb ⊔ V'} l sw↦{γ} ζ' }}}.
Proof.
  iIntros (SUB Φ) "(SW & Pts & P & LeV) Post".
  iApply (AtomicSWriter_write_resource _ _ _ _ _ ∅ with "[$SW $Pts P $LeV]");
    [done|done|iExact "P"|..].
  iIntros "!>" (t' V' V'') "(F & SV' & P & SW & Pts)".
  iApply ("Post" $! t' V''). simpl.
  iDestruct "F" as %(F1 & F2 & ? & ? & <-). by iFrame.
Qed.

Corollary AtomicSWriter_release_write_cur l γ ζ tid v' P E :
  ↑histN ⊆ E →
  {{{ l sw⊒{γ} ζ ∗ l sw↦{γ} ζ ∗ P }}}
    #l <-ʳᵉˡ v' @ tid; E
  {{{ t' V', RET #☠;
      ⌜ fresh_max_time ζ t' ⌝ ∗ ⊒V' ∗
      let ζ' := <[t' := (v',V')]>ζ in
      @{V'} P ∗ l sw⊒{γ} ζ' ∗ l sw↦{γ} ζ' }}}.
Proof.
  iIntros (SUB Φ) "(SW & Pt & P) Post".
  iDestruct (view_at_intro with "Pt") as (V) "[#SeenV Pt]".
  iApply (AtomicSWriter_release_write _ _ _ _ _ _ _ P with "[-Post]");
    [done|by iFrame|].
  iIntros "!>" (t' V') "(%MAX & #SeenV' & [P SW'] & Pt)".
  iApply ("Post" $! t' V'). iFrame "SeenV' P".
  iSplit. { iPureIntro. intros. by apply MAX. }
  iDestruct (view_at_elim with "SeenV' SW'") as "$".
  iDestruct (view_at_elim with "[] Pt") as "$".
  iApply monPred_in_view_op. by iFrame "#".
Qed.

Lemma AtomicSWriter_relaxed_write l γ ζ tid (Vrel : view) V Vb v' P E :
  ↑histN ⊆ E →
  {{{ l sw⊒{γ} ζ ∗ @{Vb} l sw↦{γ} ζ ∗ ⊒V ∗ @{Vrel} P ∗ △{tid} ⊒Vrel }}}
    #l <-ʳˡˣ v' @ tid; E
  {{{ t' V' V'', RET #☠;
      ⌜ fresh_max_time ζ t'
        ∧ V ⊑ V'' ∧ V ≠ V'' ∧ (¬ V' ⊑ V)
        ∧ Vrel ⊑ V' ∧ V' ⊑ V''⌝ ∗ ⊒V'' ∗ @{V'} P ∗
      let ζ' := <[t' := (v',V')]>ζ in
      @{V''} l sw⊒{γ} ζ' ∗ @{Vb ⊔ V''} l sw↦{γ} ζ' }}}.
Proof.
  iIntros (SUB Φ) "(SW & Pts & LeV & Prel) Post".
  iApply (AtomicSWriter_write_resource with "[$SW $Pts Prel $LeV]");
    [done|done|iExact "Prel"|..]. simpl. by iFrame.
Qed.

(** * AtomicSeen CAS *)
Lemma AtomicSeen_CASX_later
  l γ ζ' ζ tx orf or ow (vr : lit) (vw : val) (Vrel : view) (bl : bool) V Vb mo
  tid E E' (El: loc → coPset) (Φ : val → vProp) :
  Relaxed ⊑ orf → Relaxed ⊑ or → Relaxed ⊑ ow →
  ↑histN ⊆ E → (∀ l', ↑histN ⊆ El l') →
  (∀ t v, no_earlier_time ζ' t → fst <$> ζ !! t = Some v →
          ∃ vl : lit, v = #vl ∧ lit_comparable vr vl) →
  let Wv ζ : vProp := (if mo is SingleWriter then ⎡ at_writer γ ζ ⎤ else True)%I in
  l sn⊒{γ} ζ' -∗
  @{Vb} AtomicPtsToX l γ tx ζ mo -∗
  ⊒V -∗
  (if decide (AcqRel ⊑ ow) then True else △{tid} ⊒Vrel) -∗
  (∀ (b : bool) t' (v' : lit) (Vr Vw V'' : view) (ζ'' ζn : absHist),
    let tn := (t'+1)%positive in
    ⌜ ζ' ⊆ ζ'' ⊆ ζn
      ∧ (* read message (t', #v', Vr) *) ζ'' !! t' = Some (#v', Vr)
      ∧ no_earlier_time ζ' t'
      ∧ (* pre-view ⊑ post-view *) V ⊑ V''
      ∧ ( b = false ∧ lit_neq vr v' ∧ ζn = ζ
        ∨ b = true (* tn is fresh *)
          ∧ ζ !! tn = None ∧ ζn = <[tn := (vw, Vw)]>ζ
          ∧ ζ'' !! tn = Some (vw, Vw)
          (* release sequence: Vwrite includes Vread *)
          ∧ Vr ⊑ Vw ∧ Vr ≠ Vw ∧ (¬ V'' ⊑ Vr) ∧ V ≠ V''
          ∧ ( if decide (AcqRel ⊑ ow) then
                ( if decide (AcqRel ⊑ or) then
                    (* release-acquire CAS *) Vw = V''
                  else (* release CAS: *) V'' ⊑ Vw )
              else (* relaxed write CAS *) Vrel ⊑ Vw ) ) ⌝ -∗
    ( ⌜if b then v' = vr else true⌝ -∗
      @{V''} l sn⊒{γ} {[t' := (#v', Vr)]} ={E}=∗
      ∃ ζs1, (if b && bl then Wv ζs1 else emp) ∗
      ((if b && bl then
          ⌜ if mo is SingleWriter then ζs1 = ζ else True ⌝
          ∗ Wv ζn ∗ @{Vw} l sy⊒{γ} {[tn := (vw, Vw)]}
        else emp) -∗
        ⊒V'' -∗
        ( if b then
            (∀ ζs2,
              (if bl then emp else Wv ζs2) ==∗
              (if bl then emp else
                ⌜ if mo is SingleWriter then ζs2 = ζ else True ⌝
                ∗ Wv ζn ∗ @{Vw} l sy⊒{γ} {[tn := (vw, Vw)]})
              ∗ @{V''} l sn⊒{γ} ζ''
              ∗ @{Vb ⊔ V''} AtomicPtsToX l γ tx ζn mo
              ∗ (if decide (AcqRel ⊑ ow) then @{Vw} l sn⊒{γ} ζ'' else emp))
            ∗ (if decide (AcqRel ⊑ or) then ⌜Vw ⊑ V''⌝ else ▽{tid} ⊒Vw)
          else
            @{V''} l sn⊒{γ} ζ''
            ∗ @{Vb ⊔ V''} AtomicPtsToX l γ tx ζn mo
            ∗ (if decide (AcqRel ⊑ orf) then ⌜Vr ⊑ V''⌝ else ▽{tid} ⊒Vr) )
        ={E}[E']▷=∗ Φ #b))) -∗
  WP CAS #l #vr vw orf or ow @ tid; E {{ Φ }}.
Proof.
  intros ORF OR OW SUB SubEl COMP Wv.
  iIntros "SN P sV sR Post". iStopProof. iStartProof iProp.
  iIntros (V1) "(SR & Pts & %LeV1 & HRel & Post)".
  rewrite wp_eq /wp_def /=.
  iIntros (𝓥 Le𝓥) "oL sV".
  rewrite AtomicPtsToX_eq /AtomicPtsToX_def AtomicSeen_eq /AtomicSeen_def.
  rewrite view_at_unfold_2.
  iDestruct "Pts" as (C Va rsa rns ws (GH & Eqζ & IS & ND))
                    "((SL & ARL & AWL & NAL) & HC & (AR & AW & NA) & [SA SW])".
  iDestruct "SR" as "(SL' & SR0 & NA')".
  iDestruct (at_auth_reader_latest with "SA SR0") as %INCL.
  iDestruct "NA'" as (? [(t'&m'&IS')%map_choose [C' [Eqζ' ND']]] LeVa) "#NA'".
  iDestruct (at_auth_at_last_na_agree with "SA NA'") as %<-.
  iDestruct (bi.persistent_sep_dup with "ARL") as "[#ARL' %ARL]".
  iDestruct (bi.persistent_sep_dup with "AWL") as "[#AWL' %AWL]".
  iAssert (⌜ na_local l rns 𝓥.(cur) ⌝)%I with "[NAL]" as %NAL.
  { iDestruct "NAL" as %[NAL _]. iPureIntro.
    by eapply na_local_mono; [done| |eauto]; solve_lat. }

  iDestruct (SeenLocal_alloc_local l C' _ _ Va with "[SL']") as %AL'.
  { rewrite -Eqζ'. by exists m'. } { by rewrite -Eqζ'. }
  have ALL: alloc_local l C 𝓥.(cur).
  { apply (absHist_alloc_local_mono _ _ C' C ζ' ζ Va); [done..|].
    by eapply alloc_local_mono. }
  iDestruct (SeenLocal_unfold with "SL'") as %SL'.

  iApply (base_lifting.iwp_cas _ _ _ _ _ _ _ _ _ _ _ _ _ _ E' El
            with "sV HC AR NA AW"); [done..| |done|done|].
  { intros t ? v Eqt Lev VALv.
    eapply (COMP t); last first.
    - rewrite Eqζ (toAbsHist_lookup_state_inv _ _ _ _ _ VALv Eqt) //.
    - intros t0 Eqt0. change (Some t0 ⊑ Some t).
      etrans; last apply Lev. etrans; last apply view_sqsubseteq, Le𝓥.
      by apply SL'. }

  iIntros (b tr v0 𝓥' C0 t0 (WFC&m0&𝓥x&Eqt0&Eqv0&Ext1&Ext2&AT'&CCase)).

  have Ext3: 𝓥 ⊑ 𝓥' by etrans.
  have VAL0 : memval_val_rel m0.(mval) #v0 by rewrite Eqv0; constructor.
  have Eq0 := toAbsHist_lookup_state_inv _ Va _ _ _ VAL0 Eqt0.
  have LEV1 : V1 ⊑ 𝓥'.(cur) by rewrite Le𝓥 Ext3.

  set Vr := default ∅ m0.(mrel) ⊔ Va.
  set ζ0 := <[t0 := (#v0, Vr)]> ζ'.

  have INCL' : ζ' ⊆ ζ0.
  { destruct (ζ' !! t0) as [vV'|] eqn:Eqt; last by apply insert_subseteq.
    rewrite -(insert_id _ _ _ Eqt) (_: vV' = (#v0, Vr)).
    + by apply insert_mono.
    + move : (INCL t0). by rewrite Eqt Eqζ Eq0 /=. }
  have INCL0 : ζ0 ⊆ ζ.
  { rewrite /ζ0. rewrite insert_union_singleton_l.
    eapply map_union_least; [rewrite Eqζ; by apply map_singleton_subseteq_l|done]. }
  iAssert (⌜∀ t, is_Some (ζ' !! t) → seen_local l t 𝓥.(cur)⌝)%I
              with "[SL']" as %SL. { iApply SeenLocal_unfold. by iFrame. }
  have MAXt0 : no_earlier_time ζ' t0.
  { intros t1 IS1. change (Some t1 ⊑ Some t0).
    etrans; [by apply SL|].
    destruct CCase as [(_&_&_&_&RH)|(_&RH&_)]; by inversion RH. }

  have LeVa1: Va ⊑ 𝓥.(cur) by solve_lat.
  have LeVa': Va ⊑ 𝓥'.(cur) by solve_lat.

  iAssert (SeenLocal l ζ0 (cur 𝓥'))%I as "#SL0".
  { iApply (SeenLocal_insert with "[] [SL']"); last by iFrame "SL'".
    iPureIntro. eapply seen_local_mono; first apply Ext2.
    destruct CCase as [(_&_&_&_&RH)|(_&RH&_)];
      (eapply read_helper_seen_local; last exact RH; done). }
  iDestruct (at_auth_fork_at_reader with "SA") as "#SR".

  have GAB: good_absHist ζ Va by eapply good_hist_good_absHist; eauto.

  iSpecialize ("Post" $! b t0 v0 Vr).

  destruct CCase as [(-> & -> & ? & ATW' & RH)
    |(-> & RH & m & EqC' & Eqt & Eqv
      & LeRel & Let1 & Let2 & Let3 & NLet & ADD & HACQ & CUR & ATW' & WH)].
  (* CAS fail *)
  - iDestruct ("Post" $! ∅ 𝓥'.(cur) ζ0 ζ with "[%]") as "Post".
    { split; [done|]. split; [by rewrite lookup_insert|]. split; [done|].
      split; [solve_lat|]. by left. }
    (* iExists (Pr _). iFrame "Pr". iSplitL "HPr". { by destruct vr. } *)
    (* iIntros "_ Pr". *)
    iMod ("Post" with "[//] []") as (ζs1) "[_ Post]".
    { rewrite view_at_unfold_2. iSplit; last iSplit.
      - rewrite SeenLocal_unfold_singleton. iPureIntro.
        eapply seen_local_mono;
          [apply Ext2|apply (read_helper_seen_local _ _ _ _ _ _ _ ORF RH)].
      - iApply (at_reader_extract with "SR"). apply map_singleton_subseteq_l.
        clear -Eq0 Eqζ. by subst ζ.
      - iExists Va. iFrame "NA'". iPureIntro. split; [|done].
        eapply good_absHist_mono; [apply map_non_empty_singleton|..].
        + by apply map_singleton_subseteq_l. + by rewrite -Eqζ. }

    iIntros "_ sV' HC' AR NA AW" (GH0).
    iMod (own_lat_auth_update with "oL") as "[$ oTV]"; [done|].
    rewrite (monPred_at_mono (_ -∗ _)%I _ _ V1 𝓥'.(cur)); [|reflexivity|done].
    iDestruct ("Post" with "[//] [%//] [-]") as "$".
    rewrite 2!view_at_unfold_2.
    iSplitR; last iSplitR "oTV NA'".
    { iFrame "SL0". iDestruct (at_reader_extract _ _ _ INCL0 with "SR") as "$".
      iExists Va. iFrame "NA'". iPureIntro. split; [|done].
      eapply (good_absHist_mono Va ζ); eauto. apply insert_non_empty. }
    { iExists C, Va, _, _, _. iFrame. iSplit; [done|]. iFrame (AT') "#". }
    have LEV2: Vr ⊑ if decide (AcqRel ⊑ orf) then 𝓥'.(cur) else 𝓥'.(acq).
    { apply lat_join_lub.
      - etrans; first (by eapply read_helper_view_at);
          case decide => _; by apply Ext2.
      - case decide => _; [done| by rewrite -cur_acq]. }
    case decide => ?.
    + rewrite decide_True // in LEV2. by iPureIntro.
    + rewrite decide_False // in LEV2.
      rewrite acq_mod_eq /acq_mod_def /=. iExists _. by iFrame.

  (* CAS succeeds *)
  - set tn := (t0 + 1)%positive.
    set Vw := default ∅ m.(mrel) ⊔ Va.
    set ζn := <[tn := (vw, Vw)]> ζ.
    set ζ'' := <[tn := (vw, Vw)]> ζ0.

    iDestruct (bi.persistent_sep_dup with "SL") as "[SL SL1]".
    iDestruct (SyncLocal_unfold with "SL1") as %Seenζ.
    have LeVrb : Vr ⊑ Vb. { apply (Seenζ t0). by rewrite Eqζ Eq0. }
    have SLn : seen_local l tn Vw.
    { eapply seen_local_mono; last by eapply write_helper_seen_local_write.
      rewrite /Vw. clear; solve_lat. }
    have SL0 : seen_local l t0 Vw.
    { move : SLn. clear. rewrite /seen_local. intros SLn. etrans; last exact SLn.
      change (t0 ≤ tn)%positive. by lia. }
    have LeVr: Vr ⊑ Vw.
    { apply lat_join_mono; [|done]. by eapply write_helper_read_write_relaxed. }
    have Leta: Va !!w l ⊏ Some tn.
    { eapply strict_transitive_r; [|exact Let1]. apply view_sqsubseteq, LeVa1. }
    have LetVr: Vr !!w l ⊏ Some tn.
    { clear -Let3 Leta. rewrite /Vr view_lookup_w_join.
      move : Let3 Leta.
      destruct (default ∅ (mrel m0) !!w l) as [t1|]; [|by rewrite left_id_L].
      destruct (Va !!w l) as [t2|]; [|by rewrite right_id_L].
      rewrite !strict_spec_alt. intros [? NEq1] [? NEq2].
      split; [solve_lat|].
      do 2 rewrite /join /lat_join /=. case decide; done. }
    have LtVr: Vr ≠ Vw.
    { clear -SLn LetVr. intros ->.
      apply : (irreflexivity (⊏) (_ !!w _)). eapply strict_transitive_l; eauto. }
    have NLeVr:  ¬ 𝓥'.(cur) ⊑ Vr.
    { clear -LetVr Let2. intros LeVr. apply : (irreflexivity (⊏) (_ !!w _)).
      eapply strict_transitive_l; [|exact Let2]. eapply strict_transitive_r; [|exact LetVr].
      by apply view_sqsubseteq, LeVr. }
    have LeVw : Vw ⊑ Vb ⊔ 𝓥'.(cur).
    { apply lat_join_lub; [|by solve_lat].
       etrans; first by eapply write_helper_read_write_relaxed_inv. solve_lat. }
    iAssert (⌜if decide (AcqRel ⊑ ow) then
                if decide (AcqRel ⊑ or) then Vw = 𝓥'.(cur) else 𝓥'.(cur) ⊑ Vw
              else Vrel ⊑ Vw⌝)%I with "[HRel oL]" as %LeVw'.
    { case decide => HOW.
      - iPureIntro.
        have LeVw': 𝓥'.(cur) ⊑ Vw.
        { rewrite /Vw. etrans; last apply lat_join_sqsubseteq_l.
          change (Some 𝓥'.(cur) ⊑ Some (default ∅ (mrel m))).
          clear -WH HOW. apply write_helper_release_seqcst_mrel_cur in WH; [|done].
          by destruct m.(mrel). }
        case decide => HOR; last by (rewrite -LeVw'; solve_lat).
        apply : anti_symm; simpl; [done|].
        apply lat_join_lub; [|done]. destruct m.(mrel) as [Vw'|] eqn:Eqmr; [|done].
        simpl. change (Some Vw' ⊑ Some 𝓥'.(cur)).
        clear -WH RH OR HOR.
        etrans; last apply (write_helper_cur_tview_include WH); [done|].
        eapply read_helper_view_at in RH; eauto.
        by rewrite decide_True in RH.
      - iDestruct (rel_at_unfold with "HRel oL") as "[%LeVrel _]". iPureIntro.
        etrans; first by apply LeVrel. etrans; first apply Ext1.
        have ? : ow = Relaxed by destruct ow. subst ow.
        clear -WH. apply write_helper_relaxed_mrel in WH.
        rewrite /Vw. etrans; last apply lat_join_sqsubseteq_l.
        destruct m.(mrel) ; [|done]. simpl. cbn in WH. solve_lat. }

    have LEV2: Vw ⊑ if decide (AcqRel ⊑ or) then 𝓥'.(cur) else 𝓥'.(acq).
    { apply lat_join_lub.
      - rewrite write_helper_read_write_relaxed_inv; eauto.
        rewrite read_helper_view_at; eauto. clear -Ext2.
        case decide => _;
          [rewrite (cur_mono _ _ Ext2)|rewrite (acq_mono _ _ Ext2) cur_acq]; solve_lat.
      - case decide => _; [done| by rewrite -cur_acq]. }

    have FRESH : ζ !! tn = None.
    { rewrite Eqζ. by apply toAbsHist_lookup_None. }
    have INCLn' : ζ' ⊆ ζ''.
    { etrans; first apply INCL'. apply insert_subseteq.
      eapply lookup_weaken_None; eauto. }
    have INCLn'' : ζ'' ⊆ ζn by apply insert_mono.
    have Eqζn : ζn = toAbsHist C0 Va.
    { rewrite EqC' /ζn Eqζ. symmetry. apply toAbsHist_insert. rewrite Eqv.
      by constructor. }

    iDestruct ("Post" $! Vw 𝓥'.(cur) ζ'' ζn with "[%]")
      as "Post".
    { rewrite lookup_insert_ne; [|lia]. rewrite lookup_insert.
      do 3 (split; [done|]). split; [solve_lat|]. right.
      rewrite lookup_insert. do 7 (split; [done|]). split; [|done].
      clear- LeV1 Let1 Let2 Le𝓥. intros ->.
      apply : (irreflexivity (⊏) (𝓥'.(cur) !!w _)).
      eapply strict_transitive_l; eauto.
      eapply strict_transitive_r; [|exact Let1]. apply view_sqsubseteq.
      etrans; [apply LeV1|apply Le𝓥]. }

    iIntros "-> sV' HC' AR NA AW" (GH0).
    iMod ("Post" with "[//] []") as (ζs1) "[W1 Post]".
    { rewrite view_at_unfold_2. iSplit; last iSplit.
      - rewrite SeenLocal_unfold_singleton. iPureIntro. rewrite /seen_local.
        etrans; [|exact Let2]. change (t0 ≤ t0 + 1)%positive. lia.
      - iApply (at_reader_extract with "SR"). apply map_singleton_subseteq_l.
        clear -Eq0 Eqζ. by subst ζ.
      - iExists Va. iFrame "NA'". iPureIntro. split; [|done].
        eapply good_absHist_mono; [apply map_non_empty_singleton|..].
        + by apply map_singleton_subseteq_l.
        + rewrite -Eqζ. eapply good_hist_good_absHist; eauto. }

    have GH'' : good_absHist ζ'' Va.
    { eapply good_absHist_mono; eauto.
      - apply insert_non_empty. - eapply good_hist_good_absHist; eauto. }

    iAssert (at_reader γ (<[tn:=(vw, Vw)]> ζ) -∗
              (@{Vw} l sy⊒{γ} {[tn := (vw, Vw)]}) V1)%I as "ESRN".
    { iIntros "SRn". rewrite view_at_unfold_2 AtomicSync_eq /AtomicSync_def.
    iSplit; last iSplit.
    - rewrite SyncLocal_unfold_singleton. iPureIntro. split; [|done].
      eapply seen_local_mono; [apply lat_join_sqsubseteq_l|].
      by eapply write_helper_seen_local_write; last exact WH.
    - iApply (at_reader_extract with "SRn"). apply map_singleton_subseteq_l.
      by rewrite lookup_insert.
    - iExists Va. iFrame "NA'". iPureIntro. split.
      + apply (good_absHist_mono _ ζ''); [apply map_non_empty_singleton| |done].
        apply map_singleton_subseteq_l. by rewrite lookup_insert.
      + clear. solve_lat. }

    iDestruct "SA" as "(SAW & SAE & SNA)".

    set WVo : absHist → view → iProp :=
      (λ ζs Vn, (⌜ if mo is SingleWriter then ζs = ζ else True⌝
        ∗ Wv ζn ∗ @{Vw} l sy⊒{γ} {[tn := (vw, Vw)]}) Vn)%I.
    set WVsRest : iProp :=
      ( at_auth_writer γ ζn ∗ at_reader γ ζn ∗
        match mo with
        | SingleWriter => True
        | CASOnly => at_writer γ ζn
        | ConcurrentWriter => at_writer γ ζn ∗ at_exclusive_write γ tx 1
        end)%I.
    set WVs : iProp := (∀ ζs Vn, Wv ζs V1 ==∗ WVo ζs Vn ∗ WVsRest)%I.
    iAssert WVs with "[SAW SW ESRN]" as "Ws".
    { rewrite /WVs /WVsRest /Wv /WVo. iIntros (ζs Vn) "Wv". destruct mo.
      - iDestruct (at_auth_writer_exact with "SAW Wv") as %<-.
        iMod (at_writer_update_insert_at_reader _ _ _ tn (vw, Vw)
                  with "SAW Wv") as "(SAW' & SW' & _)"; [done|].
        iDestruct (at_writer_fork_at_reader with "SW'") as "#R".
        iFrame "∗ R". iDestruct ("ESRN" with "R") as "SY".
        rewrite 2!view_at_unfold_2. by iFrame "SY".
      - iMod (at_writer_update_insert_at_reader _ _ _ tn (vw, Vw)
                  with "SAW SW") as "(SAW' & SW' & _)"; [done|].
        iDestruct (at_writer_fork_at_reader with "SW'") as "#R".
        iFrame "∗ R". iDestruct ("ESRN" with "R") as "SY".
        iIntros "!>". iSplit; [done|]. rewrite 2!view_at_unfold_2. by iFrame "SY".
      - iDestruct "SW" as "[SW ?]".
        iMod (at_writer_update_insert_at_reader _ _ _ tn (vw, Vw)
                  with "SAW SW") as "(SAW' & SW' & _)"; [done|].
        iDestruct (at_writer_fork_at_reader with "SW'") as "#R".
        iFrame "∗ R". iDestruct ("ESRN" with "R") as "SY".
        iIntros "!>". iSplit; [done|]. rewrite 2!view_at_unfold_2. by iFrame "SY". }

    rewrite andb_true_l.
    iAssert (|==> (if bl then WVo ζs1 V1 else emp) ∗
                  (if bl then WVsRest else WVs))%I with "[W1 Ws]" as ">[Wv Ws]".
    { destruct bl; [|by iFrame]. by iMod ("Ws" with "W1") as "[$ $]". }
    rewrite (monPred_at_mono (_ -∗ _)%I _ _ V1 𝓥'.(cur)); [|reflexivity|done].

    iMod (own_lat_auth_update with "oL") as "[$ oTV]"; [done|].
    iDestruct ("Post" with "[Wv] [//]") as "Post". { by destruct bl. }
    iDestruct ("Post" with "[-]") as "$".
    iSplitR "oTV"; last first.
    { case decide => ?.
      - rewrite decide_True // in LEV2. by iPureIntro.
      - rewrite decide_False // in LEV2.
        rewrite acq_mod_eq /acq_mod_def /=. iExists _. by iFrame. }

    iIntros (ζs2 Vn LeVn) "Wv'".

    iAssert (|==> (if bl then emp else WVo ζs2 Vn) ∗ WVsRest)%I with "[Ws Wv']"
      as ">[Wo (SAW & #SRn & SW)]".
    { destruct bl; [by iFrame|].
      iMod ("Ws" with "[Wv']") as "[$ $]"; [|done]. rewrite /WVo /Wv.
      destruct mo; [rewrite 2!monPred_at_embed; by iFrame|done..]. }
    iIntros "!>". iSplitL "Wo". { by destruct bl. }

    iDestruct (at_reader_extract _ _ _ INCLn'' with "SRn") as "SR''".
    rewrite 3!view_at_unfold_2.
    iSplitL "SR''"; last iSplitL.
    { iDestruct (SeenLocal_insert with "[] [$SL0]") as "$".
      - iPureIntro. by eapply write_helper_seen_local; eauto.
      - iFrame "SR''". iExists Va. by iFrame "NA'". }
    { iExists C0, Va, _, _, _. iFrame. iFrame (AT' ATW'). iSplit.
      - iPureIntro. do 2 (split; [done|]). split.
        + clear -IS FRESH. rewrite lookup_insert_ne //. intros ?. subst tx.
          rewrite FRESH in IS. by destruct IS.
        + intros t1 m1. rewrite EqC'.
          case (decide (t1 = (t0 + 1)%positive)) => [->|?].
          * rewrite lookup_insert => [[<-]]. by rewrite Eqv.
          * rewrite lookup_insert_ne //. by apply ND.
      - iApply (SyncLocal_insert with "[] [SL]"); last iFrame "SL".
        iPureIntro. split; [|done]. by eapply seen_local_mono. }

    case decide => [?/=|//]. rewrite view_at_unfold_2. iSplitL "".
    { iApply (SeenLocal_insert _ _ tn); [done|].
      iApply (SeenLocal_insert _ _ t0); [done|].
      rewrite /SeenLocal. iIntros (t V' SubV' ISt) "!%".
      eapply seen_local_mono; last apply (SL _ ISt).
      etrans; last exact SubV'.
      apply write_helper_release_seqcst_mrel_cur' in WH; [|done].
      clear -WH Ext1. rewrite Ext1. solve_lat. }
    iFrame "SR''". iExists Va. iSplit; [done|]. iFrame "NA'".
    iPureIntro. clear. solve_lat.
Qed.

Lemma AtomicSeen_CASX'
  l γ ζ' ζ tx orf or ow (vr : lit) (vw : val) tid (Vrel : view) V Vb mo E :
  Relaxed ⊑ orf → Relaxed ⊑ or → Relaxed ⊑ ow →
  ↑histN ⊆ E →
  (∀ t v, no_earlier_time ζ' t → fst <$> ζ !! t = Some v →
            ∃ vl : lit, v = #vl ∧ lit_comparable vr vl) →
  let Wv ζ : vProp := (if mo is SingleWriter then ⎡ at_writer γ ζ ⎤ else True)%I in
  {{{ l sn⊒{γ} ζ' ∗ @{Vb} AtomicPtsToX l γ tx ζ mo ∗
      ⊒V ∗ (if decide (AcqRel ⊑ ow) then True else △{tid} ⊒Vrel) }}}
    CAS #l #vr vw orf or ow @ tid; E
  {{{ b t' (v' : lit) Vr V'' ζ'' ζn, RET #b;
      ⌜ ζ' ⊆ ζ'' ⊆ ζn
        ∧ (* read message (t', #v', Vr) *) ζ'' !! t' = Some (#v', Vr)
        ∧ no_earlier_time ζ' t'
        ∧ (* pre-view ⊑ post-view *) V ⊑ V'' ⌝
      ∗ ⊒V''
      ∗ @{V''} l sn⊒{γ} {[t' := (#v', Vr)]}
      ∗ ( (⌜ b = false ∧ lit_neq vr v' ∧ ζn = ζ ⌝
            ∗ @{V''} l sn⊒{γ} ζ'' ∗ @{Vb ⊔ V''} AtomicPtsToX l γ tx ζn mo
            ∗ (if decide (AcqRel ⊑ orf) then ⌜Vr ⊑ V''⌝ else ▽{tid} ⊒Vr))
        ∨ (⌜ b = true ∧ v' = vr ⌝ ∗
            let tn := (t'+1)%positive in ∃ Vw,
            ⌜ (* tn is fresh *)
              ζ !! tn = None ∧ ζn = <[tn := (vw, Vw)]>ζ
              ∧ ζ'' !! tn = Some (vw, Vw)
              (* release sequence: Vwrite includes Vread *)
              ∧ Vr ⊑ Vw ∧ Vr ≠ Vw ∧ (¬ V'' ⊑ Vr) ∧ V ≠ V''
              ∧ ( if decide (AcqRel ⊑ ow) then
                    ( if decide (AcqRel ⊑ or) then
                        (* release-acquire CAS *) Vw = V''
                      else (* release CAS: *) V'' ⊑ Vw )
                  else (* relaxed write CAS *) Vrel ⊑ Vw )⌝
            ∗ (∀ ζ0, Wv ζ0 ==∗
                  ⌜ if mo is SingleWriter then ζ0 = ζ else True ⌝
                  ∗ Wv ζn ∗ @{V''} l sn⊒{γ} ζ''
                  ∗ @{Vb ⊔ V''} AtomicPtsToX l γ tx ζn mo
                  ∗ @{Vw} l sy⊒{γ} {[tn := (vw, Vw)]}
                  ∗ (if decide (AcqRel ⊑ ow) then @{Vw} l sn⊒{γ} ζ'' else emp))
            ∗ (if decide (AcqRel ⊑ or) then ⌜Vw ⊑ V''⌝ else ▽{tid} ⊒Vw)))
  }}}.
Proof.
  iIntros (ORF OR OW SUB COMP Wv Φ) "(SR & Pts & sV & HRel) Post".
  iApply (AtomicSeen_CASX_later _ _ _ _ _ _ _ _ _ _ _ false _ _ _ _ _ E (λ _, E)
              _ ORF OR OW SUB with "SR Pts sV HRel"); [done|done|..].
  iIntros (b t' v' Vr Vw V'' ζ'' ζn F).
  destruct F as (?&?&?&?&CASE). rewrite andb_false_r.
  iIntros (Eqvr) "S1 !>". iExists ∅. iSplit; [done|]. iIntros "_ sV'' VS".
  iApply step_fupd_intro; [done|]. iIntros "!>".
  iApply ("Post" $! b t' v' Vr V'' ζ'' ζn).
  iSplit; [done|]. iFrame "sV'' S1".
  destruct CASE as [(->&?)|(->&?)].
  - iLeft. by iFrame.
  - iRight. subst v'. iSplit; [done|]. iExists Vw. iSplit; [done|].
    iDestruct "VS" as "[VS $]".
    iIntros (ζ0) "W". by iMod ("VS" with "W") as "(($&$&$)&$&$&$)".
Qed.

Lemma AtomicSeen_CASX
  l γ ζ' ζ tx orf or ow (vr : lit) (vw : val) tid (Vrel : view) V Vb E :
  Relaxed ⊑ orf → Relaxed ⊑ or → Relaxed ⊑ ow →
  ↑histN ⊆ E →
  (∀ t v, no_earlier_time ζ' t → fst <$> ζ !! t = Some v →
            ∃ vl : lit, v = #vl ∧ lit_comparable vr vl) →
  {{{ l sn⊒{γ} ζ' ∗ @{Vb} l casX↦{γ,tx} ζ ∗ ⊒V ∗
    (if decide (AcqRel ⊑ ow) then True else △{tid} ⊒Vrel) }}}
    CAS #l #vr vw orf or ow @ tid; E
  {{{ b t' (v' : lit) Vr V'' ζ'' ζn, RET #b;
      ⌜ ζ' ⊆ ζ'' ⊆ ζn
        ∧ (* read message (t', #v', Vr) *) ζ'' !! t' = Some (#v', Vr)
        ∧ no_earlier_time ζ' t'
        ∧ (* pre-view ⊑ post-view *) V ⊑ V'' ⌝
      ∗ ⊒V'' ∗ @{V''} l sn⊒{γ} ζ'' ∗ @{Vb ⊔ V''} l casX↦{γ,tx} ζn
      ∗ ( (⌜b = false ∧ lit_neq vr v' ∧ ζn = ζ⌝
            ∧ (if decide (AcqRel ⊑ orf) then ⌜Vr ⊑ V''⌝ else ▽{tid} ⊒Vr))
        ∨ (⌜b = true ∧ v' = vr⌝
            ∧ let tn := (t'+1)%positive in ∃ Vw,
              ⌜ (* tn is fresh *)
                ζ !! tn = None ∧ ζn = <[tn := (vw, Vw)]>ζ
                ∧ ζ'' !! tn = Some (vw, Vw)
                (* release sequence: Vwrite includes Vread *)
                ∧ Vr ⊑ Vw ∧ Vr ≠ Vw
                ∧ (¬ V'' ⊑ Vr)
                ∧ V ≠ V''
                ∧ ( if decide (AcqRel ⊑ ow) then
                      ( if decide (AcqRel ⊑ or) then
                          (* release-acquire CAS *) Vw = V''
                        else (* release CAS: *) V'' ⊑ Vw )
                    else (* relaxed write CAS *) Vrel ⊑ Vw )⌝
              ∧ (if decide (AcqRel ⊑ ow) then @{Vw} l sn⊒{γ} ζ'' else emp)
              ∗ (if decide (AcqRel ⊑ or) then ⌜Vw ⊑ V''⌝ else ▽{tid} ⊒Vw)))
  }}}.
Proof.
  iIntros (ORF OR OW SUB COMP Φ) "(SR & Pts & sV & HRel) Post".
  iApply wp_fupd.
  iApply (AtomicSeen_CASX' with "[$SR $Pts $sV $HRel]"); [done..|].
  iIntros "!>" (b t' v' Vr V'' ζ'' ζn) "(F & sV'' & S1 & CASE)".
  iApply "Post". iFrame "F sV''".
  iDestruct "CASE" as "[(F & SS & Pts & sVr)|(F & %Vw & F' & Vs & sVw)]".
  - iDestruct "F" as %(?&?&->). iFrame. iLeft. by iFrame.
  - iMod ("Vs" $! ∅ with "[//]") as "(_ & _ & $ & $ & ? & ?)".
    iIntros "!>". iRight. iFrame "F". iExists _. iFrame.
Qed.

Lemma AtomicSeen_CAS
  l γ ζ' ζ orf or ow (vr : lit) (vw : val) tid (Vrel : view) V Vb E :
  Relaxed ⊑ orf → Relaxed ⊑ or → Relaxed ⊑ ow →
  ↑histN ⊆ E →
  (∀ t v, no_earlier_time ζ' t → fst <$> ζ !! t = Some v →
            ∃ vl : lit, v = #vl ∧ lit_comparable vr vl) →
  {{{ l sn⊒{γ} ζ' ∗ @{Vb} l cas↦{γ} ζ ∗ ⊒V ∗
    (if decide (AcqRel ⊑ ow) then True else △{tid} ⊒Vrel) }}}
    CAS #l #vr vw orf or ow @ tid; E
  {{{ b t' (v' : lit) Vr V'' ζ'' ζn, RET #b;
      ⌜ ζ' ⊆ ζ'' ⊆ ζn
        ∧ (* read message (t', #v', Vr) *) ζ'' !! t' = Some (#v', Vr)
        ∧ no_earlier_time ζ' t'
        ∧ (* pre-view ⊑ post-view *) V ⊑ V'' ⌝
      ∗ ⊒V'' ∗ @{V''} l sn⊒{γ} ζ'' ∗ @{Vb ⊔ V''} l cas↦{γ} ζn
      ∗ ( (⌜b = false ∧ lit_neq vr v' ∧ ζn = ζ⌝
            ∧ (if decide (AcqRel ⊑ orf) then ⌜Vr ⊑ V''⌝ else ▽{tid} ⊒Vr))
        ∨ (⌜b = true ∧ v' = vr⌝
            ∧ let tn := (t'+1)%positive in ∃ Vw,
              ⌜ (* tn is fresh *)
                ζ !! tn = None ∧ ζn = <[tn := (vw, Vw)]>ζ
                ∧ ζ'' !! tn = Some (vw, Vw)
                (* release sequence: Vwrite includes Vread *)
                ∧ Vr ⊑ Vw ∧ Vr ≠ Vw
                ∧ (¬ V'' ⊑ Vr)
                ∧ V ≠ V''
                ∧ ( if decide (AcqRel ⊑ ow) then
                      ( if decide (AcqRel ⊑ or) then
                          (* release-acquire CAS *) Vw = V''
                        else (* release CAS: *) V'' ⊑ Vw )
                    else (* relaxed write CAS *) Vrel ⊑ Vw )⌝
              ∧ (if decide (AcqRel ⊑ ow) then @{Vw} l sn⊒{γ} ζ'' else emp)
              ∗ (if decide (AcqRel ⊑ or) then ⌜Vw ⊑ V''⌝ else ▽{tid} ⊒Vw)))
  }}}.
Proof.
  rewrite AtomicPtsTo_eq.
  iIntros (ORF OR OW SUB COMP Φ)
          "(SR & [%tx Pts] & sV & HRel) Post".
  iApply (AtomicSeen_CASX with "[$SR $Pts $sV $HRel]");
    [done..|].
  iIntros "!>" (b t' v' Vr V'' ζ'' ζn) "(F & sV'' & SS & Pts & CASE)".
  iApply "Post". iFrame "F sV'' SS CASE". iExists _. by iFrame.
Qed.

(* AtomicCASer CAS *)
Lemma AtomicCASer_CAS
  l γ q ζ' ζ orf or ow (vr : lit) (vw : val) tid (Vrel : view) V Vb E :
  Relaxed ⊑ orf → Relaxed ⊑ or → Relaxed ⊑ ow →
  ↑histN ⊆ E →
  (∀ t v, no_earlier_time ζ' t → fst <$> ζ !! t = Some v →
            ∃ vl : lit, v = #vl ∧ lit_comparable vr vl) →
  {{{ l cas⊒{γ,q} ζ' ∗ @{Vb} l cas↦{γ} ζ ∗ ⊒V ∗
      (if decide (AcqRel ⊑ ow) then True else △{tid} ⊒Vrel) }}}
    CAS #l #vr vw orf or ow @ tid; E
  {{{ b t' (v' : lit) Vr V'' ζ'' ζn, RET #b;
      ⌜ ζ' ⊆ ζ'' ⊆ ζn ∧ (* read message (t', #v', Vr) *) ζ'' !! t' = Some (#v', Vr)
        ∧ no_earlier_time ζ' t'
        ∧ (* pre-view ⊑ post-view *) V ⊑ V'' ⌝
      ∗ ⊒V'' ∗ @{V''} l cas⊒{γ,q} ζ'' ∗ @{Vb ⊔ V''} l cas↦{γ} ζn
      ∗ ( (⌜b = false ∧ lit_neq vr v' ∧ ζn = ζ⌝
            ∧ (if decide (AcqRel ⊑ orf) then ⌜Vr ⊑ V''⌝ else ▽{tid} ⊒Vr))
        ∨ (⌜b = true ∧ v' = vr⌝
            ∧ let tn := (t'+1)%positive in ∃ Vw,
              ⌜ (* tn is fresh *)
                ζ !! tn = None ∧ ζn = <[tn := (vw, Vw)]>ζ
                ∧ ζ'' !! tn = Some (vw, Vw)
                (* release sequence: Vwrite includes Vread *)
                ∧ Vr ⊑ Vw ∧ Vr ≠ Vw
                ∧ (¬ V'' ⊑ Vr)
                ∧ V ≠ V''
                ∧ ( if decide (AcqRel ⊑ ow) then
                      ( if decide (AcqRel ⊑ or) then
                          (* release-acquire CAS *) Vw = V''
                        else (* release CAS: *) V'' ⊑ Vw )
                    else (* relaxed write CAS *) Vrel ⊑ Vw )⌝
                ∧ (if decide (AcqRel ⊑ ow) then @{Vw} l sn⊒{γ} ζ'' else emp)
                ∗ (if decide (AcqRel ⊑ or) then ⌜Vw ⊑ V''⌝ else ▽{tid} ⊒Vw)))
  }}}.
Proof.
  iIntros (ORF OR OW SUB COMP Φ). iIntros "(S & P & sV & HRel) Post".
  rewrite AtomicCASer_eq /AtomicCASer_def AtomicCASerX_eq.
  iDestruct "S" as (tx) "[#S [Ex %IS]]".
  iApply (AtomicSeen_CAS with "[$S $P $sV $HRel]"); [done..|simpl; eauto|].
  iIntros "!>" (b t' v' Vr V'' ζ'' ζn) "(F & #sV' & S' & P & CASE)".
  iDestruct "F" as %([SUB' SUB''] & Eqt' & MAXt' & LeV).
  iApply ("Post" $! b t' v' Vr V'' ζ'' ζn).
  iFrame "sV' P CASE". iSplit; [done|].
  iFrame "S'". iExists tx. iFrame "Ex". iPureIntro.
  destruct IS as [vV Eq]. exists vV.
  by eapply lookup_weaken; eauto.
Qed.

Lemma AtomicCASer_CAS_int
  l γ q ζ' ζ orf or ow (vr : Z) (vw : val) tid (Vrel : view) V Vb E :
  Relaxed ⊑ orf → Relaxed ⊑ or → Relaxed ⊑ ow →
  ↑histN ⊆ E →
  (∀ t v, no_earlier_time ζ' t → fst <$> ζ !! t = Some v →
            ∃ vl : lit, v = #vl ∧ lit_comparable vr vl) →
  {{{ l cas⊒{γ,q} ζ' ∗ @{Vb} l cas↦{γ} ζ ∗ ⊒V ∗
    (if decide (AcqRel ⊑ ow) then True else △{tid} ⊒Vrel) }}}
    CAS #l #vr vw orf or ow @ tid; E
  {{{ b t' (v' : lit) Vr V'' ζ'' ζn, RET #b;
      ⌜ ζ' ⊆ ζ'' ⊆ ζn ∧ (* read message (t', #v', Vr) *) ζ'' !! t' = Some (#v', Vr)
        ∧ no_earlier_time ζ' t'
        ∧ (* pre-view ⊑ post-view *) V ⊑ V'' ⌝
      ∗ ⊒V'' ∗ @{V''} l cas⊒{γ,q} ζ'' ∗ @{Vb ⊔ V''} l cas↦{γ} ζn
      ∗ ( (⌜b = false ∧ lit_neq vr v' ∧ ζn = ζ⌝
            ∧ (if decide (AcqRel ⊑ orf) then ⌜Vr ⊑ V''⌝ else ▽{tid} ⊒Vr))
        ∨ (⌜b = true ∧ v' = vr⌝
            ∧ let tn := (t'+1)%positive in ∃ Vw,
              ⌜ (* tn is fresh *)
                ζ !! tn = None ∧ ζn = <[tn := (vw, Vw)]>ζ
                ∧ ζ'' !! tn = Some (vw, Vw)
                (* release sequence: Vwrite includes Vread *)
                ∧ Vr ⊑ Vw ∧ Vr ≠ Vw
                ∧ (¬ V'' ⊑ Vr)
                ∧ V ≠ V''
                ∧ ( if decide (AcqRel ⊑ ow) then
                      ( if decide (AcqRel ⊑ or) then
                          (* release-acquire CAS *) Vw = V''
                        else (* release CAS: *) V'' ⊑ Vw )
                    else (* relaxed write CAS *) Vrel ⊑ Vw )⌝
                ∧ (if decide (AcqRel ⊑ ow) then @{Vw} l sn⊒{γ} ζ'' else emp)
                ∗ (if decide (AcqRel ⊑ or) then ⌜Vw ⊑ V''⌝ else ▽{tid} ⊒Vw)))
  }}}.
Proof.
  iIntros (ORF OR OW SUB COMP Φ). iIntros "(S & P & sV & HRel) Post".
  iApply (AtomicCASer_CAS _ _ _ _ _ _ _ _ _ _ with "[$S $P $sV $HRel]");
    [done..|simpl; eauto|].
  iIntros "!>" (b t' v' Vr V'' ζ'' ζn) "(F & sV & S & P & CASE)".
  iApply "Post". by iFrame.
Qed.

Lemma AtomicCASer_CAS_live_loc
  l γ q ζ' ζ orf or ow (lr : loc) (vw : val) tid (Vrel : view) V Vb E :
  Relaxed ⊑ orf → Relaxed ⊑ or → Relaxed ⊑ ow →
  ↑histN ⊆ E →
  (∀ t v, no_earlier_time ζ' t → fst <$> ζ !! t = Some v →
            ∃ vl : lit, v = #vl ∧ lit_comparable lr vl) →
  {{{ l cas⊒{γ,q} ζ' ∗ @{Vb} l cas↦{γ} ζ ∗ ⊒V ∗
      (if decide (AcqRel ⊑ ow) then True else △{tid} ⊒Vrel) }}}
    CAS #l #lr vw orf or ow @ tid; E
  {{{ b t' (v' : lit) Vr V'' ζ'' ζn, RET #b;
      ⌜ ζ' ⊆ ζ'' ⊆ ζn ∧ (* read message (t', #v', Vr) *) ζ'' !! t' = Some (#v', Vr)
        ∧ no_earlier_time ζ' t'
        ∧ (* pre-view ⊑ post-view *) V ⊑ V'' ⌝
      ∗ ⊒V'' ∗ @{V''} l cas⊒{γ,q} ζ'' ∗ @{Vb ⊔ V''} l cas↦{γ} ζn
      ∗ ( (⌜b = false ∧ lit_neq lr v' ∧ ζn = ζ⌝
            ∧ (if decide (AcqRel ⊑ orf) then ⌜Vr ⊑ V''⌝ else ▽{tid} ⊒Vr))
        ∨ (⌜b = true ∧ v' = lr⌝
            ∧ let tn := (t'+1)%positive in ∃ Vw,
              ⌜ (* tn is fresh *)
                ζ !! tn = None ∧ ζn = <[tn := (vw, Vw)]>ζ
                ∧ ζ'' !! tn = Some (vw, Vw)
                (* release sequence: Vwrite includes Vread *)
                ∧ Vr ⊑ Vw ∧ Vr ≠ Vw
                ∧ (¬ V'' ⊑ Vr)
                ∧ V ≠ V''
                ∧ ( if decide (AcqRel ⊑ ow) then
                      ( if decide (AcqRel ⊑ or) then
                          (* release-acquire CAS *) Vw = V''
                        else (* release CAS: *) V'' ⊑ Vw )
                    else (* relaxed write CAS *) Vrel ⊑ Vw )⌝
                ∧ (if decide (AcqRel ⊑ ow) then @{Vw} l sn⊒{γ} ζ'' else emp)
                ∗ (if decide (AcqRel ⊑ or) then ⌜Vw ⊑ V''⌝ else ▽{tid} ⊒Vw)))
  }}}.
Proof.
  iIntros (ORF OR OW SUB COMP Φ). iIntros "(S & P & sV & HRel)".
  iApply (AtomicCASer_CAS with "[$S $P $sV $HRel]"); [done..|simpl; eauto].
Qed.

(* AtomicSeen Concurrent CAS *)
Lemma AtomicSeen_CON_CAS
  l γ ζ' ζ orf or ow (vr : lit) (vw : val) tid (Vrel : view) V Vb E :
  Relaxed ⊑ orf → Relaxed ⊑ or → Relaxed ⊑ ow →
  ↑histN ⊆ E →
  (∀ t v, no_earlier_time ζ' t → fst <$> ζ !! t = Some v →
            ∃ vl : lit, v = #vl ∧ lit_comparable vr vl) →
  {{{ l sn⊒{γ} ζ' ∗ @{Vb} l at↦{γ} ζ ∗ ⊒V ∗
    (if decide (AcqRel ⊑ ow) then True else △{tid} ⊒Vrel) }}}
    CAS #l #vr vw orf or ow @ tid; E
  {{{ b t' (v' : lit) Vr V'' ζ'' ζn, RET #b;
      ⌜ ζ' ⊆ ζ'' ⊆ ζn
        ∧ (* read message (t', #v', Vr) *) ζ'' !! t' = Some (#v', Vr)
        ∧ no_earlier_time ζ' t'
        ∧ (* pre-view ⊑ post-view *) V ⊑ V'' ⌝
      ∗ ⊒V'' ∗ @{V''} l sn⊒{γ} ζ'' ∗ @{Vb ⊔ V''} l at↦{γ} ζn
      ∗ ( (⌜b = false ∧ lit_neq vr v' ∧ ζn = ζ⌝
            ∧ (if decide (AcqRel ⊑ orf) then ⌜Vr ⊑ V''⌝ else ▽{tid} ⊒Vr))
        ∨ (⌜b = true ∧ v' = vr⌝
            ∧ let tn := (t'+1)%positive in ∃ Vw,
              ⌜ (* tn is fresh *)
                ζ !! tn = None ∧ ζn = <[tn := (vw, Vw)]>ζ
                ∧ ζ'' !! tn = Some (vw, Vw)
                (* release sequence: Vwrite includes Vread *)
                ∧ Vr ⊑ Vw ∧ Vr ≠ Vw
                ∧ (¬ V'' ⊑ Vr)
                ∧ V ≠ V''
                ∧ ( if decide (AcqRel ⊑ ow) then
                      ( if decide (AcqRel ⊑ or) then
                          (* release-acquire CAS *) Vw = V''
                        else (* release CAS: *) V'' ⊑ Vw )
                    else (* relaxed write CAS *) Vrel ⊑ Vw )⌝
              ∧ (if decide (AcqRel ⊑ ow) then @{Vw} l sn⊒{γ} ζ'' else emp)
              ∗ (if decide (AcqRel ⊑ or) then ⌜Vw ⊑ V''⌝ else ▽{tid} ⊒Vw)))
  }}}.
Proof.
  iIntros (ORF OR OW SUB COMP Φ) "(S & P & sV & HRel) Post".
  rewrite AtomicPtsTo_CON_CAS. iDestruct "P" as "[P Ex]".
  iDestruct "Ex" as (tx) "Ex".
  iDestruct (AtomicPtsTo_AtomicSeen_latest_1 with "P S") as %SUB'.
  iApply (AtomicSeen_CAS with "[$S $P $sV $HRel]"); [done..|].
  iIntros "!>" (b t' v' Vr V'' ζ'' ζn) "(F & sV'' & S' & P & CASE)".
  iApply "Post". iFrame.
  rewrite AtomicPtsTo_CON_CAS. iFrame. iExists _. by iFrame.
Qed.

Lemma AtomicSeen_CON_CAS_int
  l γ ζ' ζ orf or ow (vr : Z) (vw : val) tid (Vrel : view) V Vb E :
  Relaxed ⊑ orf → Relaxed ⊑ or → Relaxed ⊑ ow →
  ↑histN ⊆ E →
  (∀ t v, no_earlier_time ζ' t → fst <$> ζ !! t = Some v →
            ∃ vl : lit, v = #vl ∧ lit_comparable vr vl) →
  {{{ l sn⊒{γ} ζ' ∗ @{Vb} l at↦{γ} ζ ∗ ⊒V ∗
    (if decide (AcqRel ⊑ ow) then True else △{tid} ⊒Vrel) }}}
    CAS #l #vr vw orf or ow @ tid; E
  {{{ b t' (v' : lit) Vr V'' ζ'' ζn, RET #b;
      ⌜ ζ' ⊆ ζ'' ⊆ ζn
        ∧ (* read message (t', #v', Vr) *) ζ'' !! t' = Some (#v', Vr)
        ∧ no_earlier_time ζ' t'
        ∧ (* pre-view ⊑ post-view *) V ⊑ V'' ⌝
      ∗ ⊒V'' ∗ @{V''} l sn⊒{γ} ζ'' ∗ @{Vb ⊔ V''} l at↦{γ} ζn
      ∗ ( (⌜b = false ∧ lit_neq vr v' ∧ ζn = ζ⌝
            ∧ (if decide (AcqRel ⊑ orf) then ⌜Vr ⊑ V''⌝ else ▽{tid} ⊒Vr))
        ∨ (⌜b = true ∧ v' = vr⌝
            ∧ let tn := (t'+1)%positive in ∃ Vw,
              ⌜ (* tn is fresh *)
                ζ !! tn = None ∧ ζn = <[tn := (vw, Vw)]>ζ
                ∧ ζ'' !! tn = Some (vw, Vw)
                (* release sequence: Vwrite includes Vread *)
                ∧ Vr ⊑ Vw ∧ Vr ≠ Vw
                ∧ (¬ V'' ⊑ Vr)
                ∧ V ≠ V''
                ∧ ( if decide (AcqRel ⊑ ow) then
                      ( if decide (AcqRel ⊑ or) then
                          (* release-acquire CAS *) Vw = V''
                        else (* release CAS: *) V'' ⊑ Vw )
                    else (* relaxed write CAS *) Vrel ⊑ Vw )⌝
                ∧ (if decide (AcqRel ⊑ ow) then @{Vw} l sn⊒{γ} ζ'' else emp)
                ∗ (if decide (AcqRel ⊑ or) then ⌜Vw ⊑ V''⌝ else ▽{tid} ⊒Vw)))
  }}}.
Proof.
  iIntros (ORF OR OW SUB COMP Φ). iIntros "(S & P & sV & HRel) Post".
  iApply (AtomicSeen_CON_CAS _ _ _ _ _ _ _ _ _ _ _
            with "[$S $P $sV $HRel]"); [done..|simpl; eauto|].
  iIntros "!>" (b t' v' Vr V'' ζ'' ζn) "(F & sV & S & P & CASE)".
  iApply "Post". by iFrame.
Qed.

(* CAS on locs values *)
Lemma AtomicSeen_CON_CAS_live_loc
  l γ ζ' ζ orf or ow (lr : loc) (vw : val) tid (Vrel : view) V Vb E :
  Relaxed ⊑ orf → Relaxed ⊑ or → Relaxed ⊑ ow →
  ↑histN ⊆ E →
  (∀ t v, no_earlier_time ζ' t → fst <$> ζ !! t = Some v →
            ∃ vl : lit, v = #vl ∧ lit_comparable lr vl) →
  {{{ l sn⊒{γ} ζ' ∗ @{Vb} l at↦{γ} ζ ∗ ⊒V ∗
      (if decide (AcqRel ⊑ ow) then True else △{tid} ⊒Vrel) }}}
    CAS #l #lr vw orf or ow @ tid; E
  {{{ b t' (v' : lit) Vr V'' ζ'' ζn, RET #b;
      ⌜ ζ' ⊆ ζ'' ⊆ ζn
        ∧ (* read message (t', #v', Vr) *) ζ'' !! t' = Some (#v', Vr)
        ∧ no_earlier_time ζ' t'
        ∧ (* pre-view ⊑ post-view *) V ⊑ V'' ⌝
      ∗ ⊒V'' ∗ @{V''} l sn⊒{γ} ζ'' ∗ @{Vb ⊔ V''} l at↦{γ} ζn
      ∗ ( (⌜b = false ∧ lit_neq lr v' ∧ ζn = ζ⌝
            ∧ (if decide (AcqRel ⊑ orf) then ⌜Vr ⊑ V''⌝ else ▽{tid} ⊒Vr))
        ∨ (⌜b = true ∧ v' = lr⌝
            ∧ let tn := (t'+1)%positive in ∃ Vw,
              ⌜ (* tn is fresh *)
                ζ !! tn = None ∧ ζn = <[tn := (vw, Vw)]>ζ
                ∧ ζ'' !! tn = Some (vw, Vw)
                (* release sequence: Vwrite includes Vread *)
                ∧ Vr ⊑ Vw ∧ Vr ≠ Vw
                ∧ (¬ V'' ⊑ Vr)
                ∧ V ≠ V''
                ∧ ( if decide (AcqRel ⊑ ow) then
                      ( if decide (AcqRel ⊑ or) then
                          (* release-acquire CAS *) Vw = V''
                        else (* release CAS: *) V'' ⊑ Vw )
                    else (* relaxed write CAS *) Vrel ⊑ Vw )⌝
                ∧ (if decide (AcqRel ⊑ ow) then @{Vw} l sn⊒{γ} ζ'' else emp)
                ∗ (if decide (AcqRel ⊑ or) then ⌜Vw ⊑ V''⌝ else ▽{tid} ⊒Vw)))
  }}}.
Proof.
  iIntros (ORF OR OW SUB COMP Φ). iIntros "(S & P & sV & HRel)".
  iApply (AtomicSeen_CON_CAS with "[$S $P $sV $HRel]"); done.
Qed.

(** Atomic shared Single-Writer CAS *)
Lemma AtomicSWriter_CAS
  l γ ζ' ζc ζ orf or ow (vr : lit) (vw : val) tid (Vrel : view) V Vb Vc E :
  Relaxed ⊑ orf → Relaxed ⊑ or → Relaxed ⊑ ow →
  ↑histN ⊆ E →
  (∀ t v, no_earlier_time ζ' t → fst <$> ζ !! t = Some v →
            ∃ vl : lit, v = #vl ∧ lit_comparable vr vl) →
  {{{ l sn⊒{γ} ζ' ∗ @{Vb} l sw↦{γ} ζ ∗ @{Vc} l sw⊒{γ} ζc ∗ ⊒V ∗
      (if decide (AcqRel ⊑ ow) then True else △{tid} ⊒Vrel) }}}
    CAS #l #vr vw orf or ow @ tid; E
  {{{ b t' (v' : lit) Vr V'' ζ'' ζn, RET #b;
      ⌜ ζ' ⊆ ζ'' ⊆ ζn
        ∧ (* read message (t', #v', Vr) *) ζ'' !! t' = Some (#v', Vr)
        ∧ (∀ t, is_Some (ζ' !! t) → (t ≤ t')%positive)
        ∧ (* pre-view ⊑ post-view *) V ⊑ V'' ⌝
      ∗ ⊒V'' ∗ @{V''} l sn⊒{γ} ζ''
      (* TODO: we should be able to prove that the writer can be returned at Vc ⊔ V'' *)
      ∗ @{Vb ⊔ V''} (l sw↦{γ} ζn ∗ l sw⊒{γ} ζn)
      ∗ ( (⌜b = false ∧ lit_neq vr v' ∧ ζn = ζ⌝
            ∧ (if decide (AcqRel ⊑ orf) then ⌜Vr ⊑ V''⌝ else ▽{tid} ⊒Vr))
        ∨ (⌜b = true ∧ v' = vr⌝
            ∧ let tn := (t'+1)%positive in ∃ Vw,
              ⌜ (* tn is fresh *)
                ζ !! tn = None ∧ ζn = <[tn := (vw, Vw)]>ζ
                ∧ ζ'' !! tn = Some (vw, Vw)
                (* release sequence: Vwrite includes Vread *)
                ∧ Vr ⊑ Vw ∧ Vr ≠ Vw
                ∧ (¬ V'' ⊑ Vr)
                ∧ V ≠ V''
                ∧ ( if decide (AcqRel ⊑ ow) then
                      ( if decide (AcqRel ⊑ or) then
                          (* release-acquire CAS *) Vw = V''
                        else (* release CAS: *) V'' ⊑ Vw )
                    else (* relaxed write CAS *) Vrel ⊑ Vw )⌝
                ∧ (if decide (AcqRel ⊑ ow) then @{Vw} l sn⊒{γ} ζ'' else emp)
                ∗ (if decide (AcqRel ⊑ or) then ⌜Vw ⊑ V''⌝ else ▽{tid} ⊒Vw)))
  }}}.
Proof.
  iIntros (ORF OR OW SUB COMP Φ). iIntros "(S & P & C & sV & HRel) Post".
  iDestruct (AtomicPtsTo_SWriter_agree with "P C") as %<-.
  iAssert (@{Vb} l at↦{γ} ζ)%I with "[P C]" as "P".
  { iDestruct (AtomicPtsTo_SW_to_CON with "P C") as "[$ SY]". }
  iApply wp_fupd.
  iApply (AtomicSeen_CON_CAS with "[$S $P $sV $HRel]"); [done..|simpl; eauto|].
  iIntros "!>" (b t' v' Vr V'' ζ'' ζn) "(F & sV & S & P & CASE)".
  iApply ("Post" $! b t' v' Vr V'' ζ'' ζn). iFrame.
  rewrite AtomicPtsTo_CON_to_SW. by iMod "P" as "$".
Qed.

Lemma AtomicSWriter_CAS_int
  l γ ζ' ζc ζ orf or ow (vr : Z) (vw : val) tid (Vrel : view) V Vb Vc E :
  Relaxed ⊑ orf → Relaxed ⊑ or → Relaxed ⊑ ow →
  ↑histN ⊆ E →
  (∀ t v, no_earlier_time ζ' t → fst <$> ζ !! t = Some v →
            ∃ vl : lit, v = #vl ∧ lit_comparable vr vl) →
  {{{ l sn⊒{γ} ζ' ∗ @{Vb} l sw↦{γ} ζ ∗ @{Vc} l sw⊒{γ} ζc ∗ ⊒V ∗
    (if decide (AcqRel ⊑ ow) then True else △{tid} ⊒Vrel) }}}
    CAS #l #vr vw orf or ow @ tid; E
  {{{ b t' (v' : lit) Vr V'' ζ'' ζn, RET #b;
      ⌜ ζ' ⊆ ζ'' ⊆ ζn
        ∧ (* read message (t', #v', Vr) *) ζ'' !! t' = Some (#v', Vr)
        ∧ (∀ t, is_Some (ζ' !! t) → (t ≤ t')%positive)
        ∧ (* pre-view ⊑ post-view *) V ⊑ V'' ⌝
      ∗ ⊒V'' ∗ @{V''} l sn⊒{γ} ζ''
      ∗ @{Vb ⊔ V''} (l sw↦{γ} ζn ∗ l sw⊒{γ} ζn)
      ∗ ( (⌜b = false ∧ lit_neq vr v' ∧ ζn = ζ⌝
            ∧ (if decide (AcqRel ⊑ orf) then ⌜Vr ⊑ V''⌝ else ▽{tid} ⊒Vr))
        ∨ (⌜b = true ∧ v' = vr⌝
            ∧ let tn := (t'+1)%positive in ∃ Vw,
              ⌜ (* tn is fresh *)
                ζ !! tn = None ∧ ζn = <[tn := (vw, Vw)]>ζ
                ∧ ζ'' !! tn = Some (vw, Vw)
                (* release sequence: Vwrite includes Vread *)
                ∧ Vr ⊑ Vw ∧ Vr ≠ Vw
                ∧ (¬ V'' ⊑ Vr)
                ∧ V ≠ V''
                ∧ ( if decide (AcqRel ⊑ ow) then
                      ( if decide (AcqRel ⊑ or) then
                          (* release-acquire CAS *) Vw = V''
                        else (* release CAS: *) V'' ⊑ Vw )
                    else (* relaxed write CAS *) Vrel ⊑ Vw )⌝
                ∧ (if decide (AcqRel ⊑ ow) then @{Vw} l sn⊒{γ} ζ'' else emp)
                ∗ (if decide (AcqRel ⊑ or) then ⌜Vw ⊑ V''⌝ else ▽{tid} ⊒Vw)))
  }}}.
Proof.
  iIntros (ORF OR OW SUB COMP Φ). iIntros "(S & P & C & sV & HRel) Post".
  iApply (AtomicSWriter_CAS _ _ _ _ _ _ _ _ _ _
            with "[$S $P $C $sV $HRel]"); [done..|simpl; eauto|].
  iIntros "!>" (b t' v' Vr V'' ζ'' ζn) "(F & sV & S & P & CASE)".
  iApply "Post". by iFrame.
Qed.

Lemma AtomicSWriter_CAS_live_loc
  l γ ζ' ζc ζ orf or ow (lr : loc) (vw : val) tid (Vrel : view) V Vb Vc E :
  Relaxed ⊑ orf → Relaxed ⊑ or → Relaxed ⊑ ow →
  ↑histN ⊆ E →
  (∀ t v, no_earlier_time ζ' t → fst <$> ζ !! t = Some v →
            ∃ vl : lit, v = #vl ∧ lit_comparable lr vl) →
  {{{ l sn⊒{γ} ζ' ∗ @{Vb} l sw↦{γ} ζ ∗ @{Vc} l sw⊒{γ} ζc ∗ ⊒V ∗
      (if decide (AcqRel ⊑ ow) then True else △{tid} ⊒Vrel) }}}
    CAS #l #lr vw orf or ow @ tid; E
  {{{ b t' (v' : lit) Vr V'' ζ'' ζn, RET #b;
      ⌜ ζ' ⊆ ζ'' ⊆ ζn
        ∧ (* read message (t', #v', Vr) *) ζ'' !! t' = Some (#v', Vr)
        ∧ (∀ t, is_Some (ζ' !! t) → (t ≤ t')%positive)
        ∧ (* pre-view ⊑ post-view *) V ⊑ V'' ⌝
      ∗ ⊒V'' ∗ @{V''} l sn⊒{γ} ζ''
      ∗ @{Vb ⊔ V''} (l sw↦{γ} ζn ∗ l sw⊒{γ} ζn)
      ∗ ( (⌜b = false ∧ lit_neq lr v' ∧ ζn = ζ⌝
            ∧ (if decide (AcqRel ⊑ orf) then ⌜Vr ⊑ V''⌝ else ▽{tid} ⊒Vr))
        ∨ (⌜b = true ∧ v' = lr⌝
            ∧ let tn := (t'+1)%positive in ∃ Vw,
              ⌜ (* tn is fresh *)
                ζ !! tn = None ∧ ζn = <[tn := (vw, Vw)]>ζ
                ∧ ζ'' !! tn = Some (vw, Vw)
                (* release sequence: Vwrite includes Vread *)
                ∧ Vr ⊑ Vw ∧ Vr ≠ Vw
                ∧ (¬ V'' ⊑ Vr)
                ∧ V ≠ V''
                ∧ ( if decide (AcqRel ⊑ ow) then
                      ( if decide (AcqRel ⊑ or) then
                          (* release-acquire CAS *) Vw = V''
                        else (* release CAS: *) V'' ⊑ Vw )
                    else (* relaxed write CAS *) Vrel ⊑ Vw )⌝
                ∧ (if decide (AcqRel ⊑ ow) then @{Vw} l sn⊒{γ} ζ'' else emp)
                ∗ (if decide (AcqRel ⊑ or) then ⌜Vw ⊑ V''⌝ else ▽{tid} ⊒Vw)))
  }}}.
Proof.
  iIntros (ORF OR OW SUB COMP Φ). iIntros "(S & P & C & sV & HRel)".
  iApply (AtomicSWriter_CAS with "[$S $P $C $sV $HRel]"); done.
Qed.

End ops_rules.
