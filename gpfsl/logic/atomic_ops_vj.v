From iris.proofmode Require Import proofmode.

From gpfsl.base_logic Require Import weakestpre.
From gpfsl.logic Require Import relacq.
From gpfsl.logic Require Import atomic_cmra atomic_ghost atomic_preds atomic_ops.

From gpfsl.lang Require Import notation.

Require Import iris.prelude.options.

Implicit Types (ζ : absHist) (l : loc) (t : time) (v : val) (V : view) (q : frac).

Section ops_rules.
Context `{!noprolG Σ, !atomicG Σ}.
#[local] Notation iProp := (iProp Σ).
#[local] Notation vProp := (vProp Σ).

Lemma AtomicSeen_read_vj l γ ζ ζ' mode o tid V Vb E :
  Relaxed ⊑ o → ↑histN ⊆ E →
  {{{ l sn⊒{γ} ζ' ∗ ⊔{Vb} AtomicPtsTo l γ ζ mode ∗ ⊒V }}}
    Read o #l @ tid; E
  {{{ t' v' V' V'' ζ'', RET v';
      ⌜ζ' ⊆ ζ'' ⊆ ζ
        ∧ ζ'' !! t' = Some (v', V')
        ∧ no_earlier_time ζ' t'
        ∧ V ⊑ V''⌝
      ∗ ⊒V''
      ∗ (if decide (AcqRel ⊑ o) then ⌜V' ⊑ V''⌝ else ▽{tid} ⊒V')
      ∗ @{V''} l sn⊒{γ} ζ''
      ∗ ⊔{Vb} AtomicPtsTo l γ ζ mode }}}.
Proof.
  (* TODO boring proof that is duplicated everywhere for [view_join]. *)
  iIntros (RLX HN Φ) "(SN & Pts & sV) Post".
  iDestruct (view_join_view_at_access with "sV Pts") as (V' LeV') "(#sV' & P & Close)".
  iApply (AtomicSeen_read with "[$SN $P $sV']"); [done..|].
  iIntros "!>" (t' v' V2 V3 ζ'') "(F & #sV3 & HV & SN' & P)".
  rewrite -lat_join_assoc_L.
  iDestruct ("Close" with "[] P") as "P".
  { rewrite -monPred_in_view_op. by iFrame "#". }
  iApply ("Post" $! t' v' V2 V3 ζ''). iFrame "# ∗".
  iDestruct "F" as %(?&?&?&Le). iPureIntro. do 3 (split; [done|]). solve_lat.
Qed.

Lemma AtomicSeen_acquire_read_vj l γ ζ ζ' mode tid V Vb E :
  ↑histN ⊆ E →
  {{{ l sn⊒{γ} ζ' ∗ ⊔{Vb} AtomicPtsTo l γ ζ mode ∗ ⊒V }}}
    !ᵃᶜ#l @ tid; E
  {{{ t' v' V' V'' ζ'', RET v';
      ⌜ζ' ⊆ ζ'' ⊆ ζ
        ∧ ζ'' !! t' = Some (v', V')
        ∧ no_earlier_time ζ' t'
        ∧ V ⊔ V' ⊑ V''⌝
      ∗ ⊒V'' ∗ @{V''} l sn⊒{γ} ζ''
      ∗ ⊔{Vb} AtomicPtsTo l γ ζ mode }}}.
Proof.
  iIntros (SUB Φ) "Pre Post".
  iApply (AtomicSeen_read_vj with "Pre"); [done|done|].
  simpl. iIntros "!>" (t' v' V' V'' ζ'') "(F & S'' & % & SN & P)".
  iApply "Post". iFrame.
  iDestruct "F" as %(?&?&?&?). iPureIntro. do 3 (split; [done|]). solve_lat.
Qed.

Lemma AtomicSeen_relaxed_read_vj l γ ζ ζ' mode tid V Vb E :
  ↑histN ⊆ E →
  {{{ l sn⊒{γ} ζ' ∗ ⊔{Vb} AtomicPtsTo l γ ζ mode ∗ ⊒V }}}
    !ʳˡˣ#l @ tid; E
  {{{ t' v' V' V'' ζ'', RET v';
      ⌜ζ' ⊆ ζ'' ⊆ ζ
        ∧ ζ'' !! t' = Some (v', V')
        ∧ no_earlier_time ζ' t'
        ∧ V ⊑ V''⌝
      ∗ ⊒V'' ∗ ▽{tid}(⊒V') ∗ @{V''} l sn⊒{γ} ζ''
      ∗ ⊔{Vb} AtomicPtsTo l γ ζ mode }}}.
Proof.
  iIntros (? Φ) "Pre Post".
  iApply (AtomicSeen_read_vj with "Pre"); [done|done|simpl; by iFrame].
Qed.

Lemma AtomicSWriter_read_vj l γ ζ mode o tid V Vb E :
  Relaxed ⊑ o → ↑histN ⊆ E →
  {{{ l sw⊒{γ} ζ ∗ ⊔{Vb} AtomicPtsTo l γ ζ mode ∗ ⊒V }}}
    Read o #l @ tid; E
  {{{ t' v' V' V'', RET v';
      ⌜ζ !! t' = Some (v', V')
        ∧ no_earlier_time ζ t'
        ∧ V ⊔ V' ⊑ V''⌝
      ∗ ⊒V'' ∗ l sw⊒{γ} ζ
      ∗ ⊔{Vb} AtomicPtsTo l γ ζ mode }}}.
Proof.
  iIntros (RLX HN Φ) "(SN & Pts & sV) Post".
  iDestruct (view_join_view_at_access with "sV Pts") as (V' LeV') "(#sV' & P & Close)".
  iApply (AtomicSWriter_read with "[$SN $P $sV']"); [done..|].
  iIntros "!>" (t' v' V2 V3) "(F & #sV3 & SN' & P)".
  rewrite -lat_join_assoc_L.
  iDestruct ("Close" with "[] P") as "P".
  { rewrite -monPred_in_view_op. by iFrame "#". }
  iApply ("Post" $! t' v' V2 V3). iFrame "# ∗".
  iDestruct "F" as %(?&?&Le). iPureIntro. do 2 (split; [done|]). solve_lat.
Qed.

Lemma AtomicCASer_read_vj l γ ζ ζ' q mode o tid V Vb E :
  Relaxed ⊑ o → ↑histN ⊆ E →
  {{{ l cas⊒{γ,q} ζ' ∗ ⊔{Vb} AtomicPtsTo l γ ζ mode ∗ ⊒V }}}
    Read o #l @ tid; E
  {{{ t' v' V' V'' ζ'', RET v';
      ⌜ζ' ⊆ ζ'' ⊆ ζ
        ∧ ζ'' !! t' = Some (v', V')
        ∧ no_earlier_time ζ' t'
        ∧ V ⊑ V''⌝
      ∗ ⊒V''
      ∗ (if decide (AcqRel ⊑ o) then ⌜V' ⊑ V''⌝ else ▽{tid} ⊒V')
      ∗ @{V''} l cas⊒{γ,q} ζ''
      ∗ ⊔{Vb} AtomicPtsTo l γ ζ mode }}}.
Proof.
  iIntros (RLX HN Φ) "(SN & Pts & sV) Post".
  iDestruct (view_join_view_at_access with "sV Pts") as (V' LeV') "(#sV' & P & Close)".
  iApply (AtomicCASer_read with "[$SN $P $sV']"); [done..|].
  iIntros "!>" (t' v' V2 V3 ζ'') "(F & #sV3 & LeV' & SN' & P)".
  rewrite -lat_join_assoc_L.
  iDestruct ("Close" with "[] P") as "P".
  { rewrite -monPred_in_view_op. by iFrame "#". }
  iApply ("Post" $! t' v' V2 V3). iFrame "# ∗".
  iDestruct "F" as %(?&?&?&Le). iPureIntro. do 3 (split; [done|]). solve_lat.
Qed.

Lemma AtomicSeen_concurrent_write_vj l γ ζ' ζ o tid (Vrel : view) V Vb v' E :
  Relaxed ⊑ o →
  ↑histN ⊆ E →
  {{{ l sn⊒{γ} ζ' ∗ ⊔{Vb} l at↦{γ} ζ ∗ ⊒V ∗
      (if decide (AcqRel ⊑ o) then True else △{tid} ⊒Vrel) }}}
    Write o #l v' @ tid; E
  {{{ t' V' V'', RET #☠;
      ⌜ fresh_max_time ζ' t'
        ∧ ζ !! t' = None
        ∧ V ⊑ V'' ∧ V ≠ V'' ∧ (¬ V' ⊑ V)
        ∧ if decide (AcqRel ⊑ o) then V'' = V' else Vrel ⊑ V' ∧ V' ⊑ V''⌝ ∗
      ⊒V'' ∗
      let ζ'' := <[t' := (v',V')]>ζ' in let ζn := <[t' := (v',V')]>ζ in
      @{V''} l sn⊒{γ} ζ'' ∗ ⊔{Vb} l at↦{γ} ζn }}}.
Proof.
  iIntros (RLX SUB Φ) "(SS & Pts & sV & HV) Post".
  iApply (AtomicSeen_write_vj _ _ _ _ _ 1 1 with "[$SS $Pts $sV $HV]"); [done..|].

  iIntros "!>" (t' V' V'') "(F & #sV'' & SN' & _ & SY' & Pts)".
  iApply ("Post" $! t' V' V''). by iFrame "∗#".
Qed.

Lemma AtomicSeen_concurrent_release_write_vj l γ ζ' ζ tid V Vb v' E :
  ↑histN ⊆ E →
  {{{ l sn⊒{γ} ζ' ∗ ⊔{Vb} l at↦{γ} ζ ∗ ⊒V }}}
    #l <-ʳᵉˡ v' @ tid; E
  {{{ t' V', RET #☠;
      ⌜ fresh_max_time ζ' t'
        ∧ ζ !! t' = None
        ∧ V ⊑ V' ∧ V ≠ V' ⌝ ∗
      ⊒V' ∗
      let ζ'' := <[t' := (v',V')]>ζ' in let ζn := <[t' := (v',V')]>ζ in
      @{V'} l sn⊒{γ} ζ'' ∗ ⊔{Vb} l at↦{γ} ζn }}}.
Proof.
  iIntros (SUB Φ) "(SS & Pts & sV) Post".
  iApply (AtomicSeen_concurrent_write_vj _ _ _ _ _ _ ∅ with "[$SS $Pts $sV]"); 
    [done..|]. simpl.

  iIntros "!>" (t' V' V'') "(F & sV' & SN' & Pts)".
  iDestruct "F" as %(?&?&?&?&?&->).
  iApply ("Post" $! t' V'). by iFrame.
Qed.

Lemma AtomicSeen_concurrent_relaxed_write_vj l γ ζ' ζ tid (Vrel : view) V Vb v' E :
  ↑histN ⊆ E →
  {{{ l sn⊒{γ} ζ' ∗ ⊔{Vb} l at↦{γ} ζ ∗ ⊒V ∗ △{tid} ⊒Vrel }}}
    #l <-ʳˡˣ v' @ tid; E
  {{{ t' V' V'', RET #☠;
      ⌜ fresh_max_time ζ' t'
        ∧ ζ !! t' = None
        ∧ V ⊑ V'' ∧ V ≠ V'' ∧ (¬ V' ⊑ V)
        ∧ Vrel ⊑ V' ∧ V' ⊑ V''⌝ ∗
      ⊒V'' ∗
      let ζ'' := <[t' := (v',V')]>ζ' in let ζn := <[t' := (v',V')]>ζ in
      @{V''} l sn⊒{γ} ζ'' ∗ ⊔{Vb} l at↦{γ} ζn }}}.
Proof.
  iIntros (SUB Φ) "(SS & Pts & sV & HRel) Post".
  iApply (AtomicSeen_concurrent_write_vj with "[$SS $Pts $sV HRel]");
    [done..|simpl; by iFrame|]. simpl.

  iIntros "!>" (t' V' V'') "(F & sV' & SN' & Pts)". iApply "Post". by iFrame.
Qed.

Lemma AtomicCASer_write_vj l γ q ζ' ζ o tid (Vrel : view) V Vb v' E :
  Relaxed ⊑ o →
  ↑histN ⊆ E →
  {{{ l cas⊒{γ,q} ζ' ∗ ⊔{Vb} l cas↦{γ} ζ ∗ ⊒V ∗
      (if decide (AcqRel ⊑ o) then True else △{tid} ⊒Vrel) }}}
    Write o #l v' @ tid; E
  {{{ t' V' V'', RET #☠;
      ⌜ fresh_max_time ζ' t'
        ∧ ζ !! t' = None
        ∧ V ⊑ V'' ∧ V ≠ V'' ∧ (¬ V' ⊑ V)
        ∧ if decide (AcqRel ⊑ o) then V'' = V' else Vrel ⊑ V' ∧ V' ⊑ V''⌝ ∗
      ⊒V'' ∗
      let ζ'' := <[t' := (v',V')]>ζ' in let ζn := <[t' := (v',V')]>ζ in
      @{V''} l cas⊒{γ,q} ζ'' ∗ ⊔{Vb} l cas↦{γ} ζn }}}.
Proof.
  iIntros (RLX SUB Φ) "(C & Pts & sV & HV) Post".
  rewrite AtomicCASer_eq /AtomicCASer_def AtomicCASerX_eq.
  iDestruct "C" as (tx') "[SS [SE %IS]]".

  iApply (AtomicSeen_write_vj _ _ _ _ _ q tx' with "[$SS $Pts SE $sV $HV]");
    [done..|].
  iIntros "!>" (t' V' V'') "(F & sV'' & SN' & SE & SY & Pts)".
  iApply ("Post" $! t' V' V''). iFrame.
  iExists tx'. iFrame "SE". iPureIntro.
  case (decide (tx' = t')) => [->|?].
  - rewrite lookup_insert. by eexists.
  - by rewrite lookup_insert_ne.
Qed.

Lemma AtomicSeen_CON_CAS_int_vj
  l γ ζ' ζ orf or ow (vr : Z) (vw : val) tid (Vrel : view) V Vb E :
  Relaxed ⊑ orf → Relaxed ⊑ or → Relaxed ⊑ ow →
  ↑histN ⊆ E →
  (∀ t v, no_earlier_time ζ' t → fst <$> ζ !! t = Some v →
            ∃ vl : lit, v = #vl ∧ lit_comparable vr vl) →
  {{{ l sn⊒{γ} ζ' ∗ ⊔{Vb} l at↦{γ} ζ ∗ ⊒V ∗
    (if decide (AcqRel ⊑ ow) then True else △{tid} ⊒Vrel) }}}
    CAS #l #vr vw orf or ow @ tid; E
  {{{ b t' (v' : lit) Vr V'' ζ'' ζn, RET #b;
      ⌜ ζ' ⊆ ζ'' ⊆ ζn
        ∧ (* read message (t', #v', Vr) *) ζ'' !! t' = Some (#v', Vr)
        ∧ no_earlier_time ζ' t'
        ∧ (* pre-view ⊑ post-view *) V ⊑ V'' ⌝
      ∗ ⊒V'' ∗ @{V''} l sn⊒{γ} ζ'' ∗ ⊔{Vb} l at↦{γ} ζn
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
  iDestruct (view_join_elim' with "P sV") as (V2) "(#sV2 & %LeV & P)".
  iApply (AtomicSeen_CON_CAS_int with "[$S $P $sV2 $HRel]"); [done..|].
  iIntros "!>" (b t' v' Vr V'' ζ'' ζn) "(F & #sV' & S & P & CASE)".
  iApply "Post". iFrame "sV' ∗".
  iDestruct "F" as %(?&?&?&?).
  assert (V ⊑ V'') by solve_lat. iSplitR; [done|]. iSplitR "CASE".
  - iApply (view_join_intro_at _ (V2 ⊔ V'') with "[$P] []").
    rewrite -monPred_in_view_op. iFrame "#".
  - iDestruct "CASE" as "[CASE|CASE]"; [by iLeft|iRight].
    iDestruct "CASE" as "[$ CASE]". iDestruct "CASE" as (Vw F) "CASE".
    iExists Vw. iFrame. iPureIntro.
    destruct F as (?&?&?&?&?&?&NE2&?). do 6 (split; [done|]). split; [|done].
    intros ->. apply NE2. solve_lat.
Qed.
End ops_rules.
