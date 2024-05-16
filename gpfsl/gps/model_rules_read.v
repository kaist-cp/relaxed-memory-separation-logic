From iris.proofmode Require Import proofmode.

From gpfsl.logic Require Import lifting.
From gpfsl.logic Require Import atomic_ghost atomic_preds atomic_ops.
From gpfsl.gps Require Import cbends.
From gpfsl.gps Require Export model_defs.

Require Import iris.prelude.options.

Implicit Types (t : time) (v : val) (V : view) (ζ : absHist) (γ : gname)
               (E : coPset) (tid : thread_id).

Section Read.
  Context `{!noprolG Σ, !gpsG Σ Prtcl, !atomicG Σ}
          (IP : interpO Σ Prtcl) (l : loc).
  Local Notation iProp := (iProp Σ).
  Local Notation vProp := (vProp Σ).
  Implicit Types
    (s : pr_stateT Prtcl) (χ : stateT Prtcl) (μ : time → pr_stateT Prtcl).

  Notation F := (IP true l).
  Notation F_read := (IP false l).

  (** READ *)
  Lemma GPSRaw_Read
    IW (isEx: bool) (tx: time) q Vx ζx
    Q R (tr: time) sr vr o (γ γs γl : gname) bs Vb E tid :
    ↑histN ⊆ E → o = Relaxed ∨ o = AcqRel → γ = encode (γs,γl) →
    let isEx' : bool := isEx && bs in
    let Px : vProp :=
      (if isEx'
       then (@{Vx} l casX⊒{γl,tx,q} ζx) ∗ ⌜(tx ≤ tr)%positive⌝
       else True)%I in
    {{{ (▷ <obj> ∀ t' s' v, ⌜sr ⊑ s' ∧ tr ⊑ t'⌝ -∗
                  ((F_read γ t' s' v ={E}=∗ F_read γ t' s' v ∗ R t' s' v) ∧
                  (F γ t' s' v ={E}=∗ F γ t' s' v ∗ R t' s' v) ∧
                  (if isEx then True
                   else IW l γ t' s' v ={E}=∗ IW l γ t' s' v ∗ R t' s' v)))
        ∗ (▷ ∀ t' s' v, ⌜sr ⊑ s' ∧ tr ⊑ t'⌝ -∗ (R t' s' v ={E}=∗ Q t' s' v))
        ∗ (⊔{Vb} ▷ gps_inv IP IW l γ bs)
        ∗ Px
        ∗ GPS_Reader l tr sr vr γ }}}
        Read o #l @ tid; E
    {{{ t' s' v, RET v;
        ⌜ sr ⊑ s' ∧ (tr ≤ t')%positive ⌝
        ∗ (⊔{Vb} ▷ gps_inv IP IW l γ bs)
        ∗ Px
        ∗ (if decide (AcqRel ⊑ o) then Q t' s' v else ▽{tid} Q t' s' v)
        ∗ GPS_Reader l t' s' v γ }}}.
  Proof.
    iIntros (SubE RLX ENC isEx' Px Φ) "(VP & VP2 & I & Px & R) Post".
    rewrite GPS_Reader_eq. iDestruct "R" as (γs' γl' Vr ENC') "(SS' & #SN)".
    rewrite ENC in ENC'. apply encode_inj, pair_inj in ENC' as [<- <-].
    iDestruct (view_at_intro with "VP2") as (V0) "[#sV0 VP2]".
    iDestruct (view_join_view_at_access with "sV0 I") as (V LeV0)
      "(#sV & I & Close)". rewrite !view_at_later.
    iDestruct "I" as (μ γs' γl' ζ tx') "(>%ENC' & >Go & >P & rB & rE & >rF)".
    rewrite ENC in ENC'. apply encode_inj, pair_inj in ENC' as [<- <-].
    iDestruct "rF" as %(FI & SS & SW).
    rewrite 3!view_at_objective_iff.

    iDestruct (gps_own_snap_singleton_sub with "Go SS'") as %Eqsr.
    iAssert (⌜ if isEx then (tx' ≤ tr)%positive else True⌝)%I
      with "[Px P]" as %IS.
    { rewrite /Px /isEx'. destruct isEx; [|done]. destruct bs; simpl.
      - iDestruct "Px" as "[C %]".
        by iDestruct (AtomicPtsToX_AtomicCASerX_latest with "P C") as %[<- _].
      - (* TODO: lemma *)
        iPureIntro. apply SW, elem_of_dom. apply elem_of_dom_2 in Eqsr.
        move : Eqsr. by apply dom_imap_subseteq. }

    iApply (wp_acq_intro with "sV0"). iIntros "sV0'".
    iApply wp_fupd.
    iApply (AtomicSeen_readX with "[$SN $P $sV]"); [|done|].
    { clear -RLX. by destruct RLX as [-> | ->]. }
    iIntros "!>" (t' v' V' V'' ζ'') "(%F & #sV'' & ACQ & S' & P)".
    destruct F as ([Sub1 Sub2] & Eqt' & MAX' & LeV).
    have Letr : tr ⊑ t'.
    { apply MAX'. rewrite lookup_insert. by eexists. }
    have Eqt'' := lookup_weaken _ _ _ _ Eqt' Sub2.
    have Eqμt : toState μ ζ !! t' = Some (μ t') by rewrite map_lookup_imap Eqt''.
    have Lesr : sr ⊑ μ t' by apply (SS _ t' _ _ Eqsr).
    iDestruct (gps_own_snap_singleton _ _ _ _ Eqμt with "Go") as "#Ss'".

    iMod (GPSRaw_read_resources _ _ _ isEx R _ _ _ tr t' with "[VP] rB rE")
      as "(rB & rE & R)"; [done|done|done|..].
    { iIntros "!>". by iApply (monPred_objectively_elim with "VP"). }
    iDestruct ("Close" $! (V ⊔ V'') with "[sV''] [Go P rB rE]") as "I".
    { rewrite -monPred_in_view_op. iFrame "sV sV''". }
    { iNext. iExists μ, γs, γl, ζ, tx'. iFrame. by iPureIntro. }
    iApply "Post". iFrame "I Px". iSplitR; [done|].
    iSplitR "S'".
    - destruct RLX as [-> | ->]; simpl.
      + rewrite -acq_fupd.
        iDestruct (acq_at_intro with "ACQ R") as "R".
        iDestruct (acq_at_intro with "sV0' VP2") as "VP2".
        iCombine "VP2 R" as "VP". iApply (relacq.acq_mono with "VP").
        iIntros "[VP R]". iApply ("VP" with "[//] R").
      + iDestruct "ACQ" as %LeV'. iApply (view_at_elim with "sV0 VP2 [//]").
        iApply (view_at_elim with "[] R").
        by iApply (monPred_in_mono with "sV''").
    - iIntros "!>". iExists γs, γl, V'. iFrame (ENC) "Ss'".
      iDestruct (view_at_elim with "sV'' S'") as "S'".
      by iApply (AtomicSeen_mono_lookup_singleton with "S'").
  Qed.

  Lemma GPSRaw_Read_ex
    IW Q R (tx: time) q Vx ζx (tr: time) sr vr o (γ γs γl : gname)
    (bs : bool) Vb E tid :
    ↑histN ⊆ E → o = Relaxed ∨ o = AcqRel → γ = encode (γs,γl) →
    let Px : vProp := if bs
                      then ((@{Vx} l casX⊒{γl,tx,q} ζx) ∗ ⌜ (tx ≤ tr)%positive ⌝)%I
                      else True%I in
    {{{ (▷ <obj> ∀ t' s' v, ⌜sr ⊑ s' ∧ tr ⊑ t'⌝ -∗
                  ((F_read γ t' s' v ={E}=∗ F_read γ t' s' v ∗ R t' s' v) ∧
                  (F γ t' s' v ={E}=∗ F γ t' s' v ∗ R t' s' v)))
        ∗ (▷ ∀ t' s' v, ⌜sr ⊑ s' ∧ tr ⊑ t'⌝ -∗ (R t' s' v ={E}=∗ Q t' s' v))
        ∗ (⊔{Vb} ▷ gps_inv IP IW l γ bs)
        ∗ Px
        ∗ GPS_Reader l tr sr vr γ }}}
        Read o #l @ tid; E
    {{{ t' s' v, RET v;
        ⌜ sr ⊑ s' ∧ (tr ≤ t')%positive ⌝
        ∗ (⊔{Vb} ▷ gps_inv IP IW l γ bs)
        ∗ Px
        ∗ (if decide (AcqRel ⊑ o) then Q t' s' v else ▽{tid} Q t' s' v)
        ∗ GPS_Reader l t' s' v γ }}}.
  Proof.
    iIntros (SUB OR ENC Px Φ) "(VP & VP2 & I & ex & R) Post".
    iApply (GPSRaw_Read IW true tx q Vx ζx Q R tr sr vr o γ γs γl bs Vb E _
              SUB OR ENC with "[VP $VP2 $I $ex $R] Post").
    by setoid_rewrite bi.and_True.
  Qed.

  Lemma GPSRaw_Read_non_ex
    IW Q R (tr: time) sr vr o (γ : gname) m Vb E tid :
    ↑histN ⊆ E → o = Relaxed ∨ o = AcqRel →
    {{{ (▷ <obj> ∀ t' s' v, ⌜sr ⊑ s' ∧ tr ⊑ t'⌝ -∗
                  ((F_read γ t' s' v ={E}=∗ F_read γ t' s' v ∗ R t' s' v) ∧
                  (F γ t' s' v ={E}=∗ F γ t' s' v ∗ R t' s' v) ∧
                  (IW l γ t' s' v ={E}=∗ IW l γ t' s' v ∗ R t' s' v)))
        ∗ (▷ ∀ t' s' v, ⌜sr ⊑ s' ∧ tr ⊑ t'⌝ -∗ (R t' s' v ={E}=∗ Q t' s' v))
        ∗ (⊔{Vb} ▷ gps_inv IP IW l γ m)
        ∗ GPS_Reader l tr sr vr γ }}}
        Read o #l @ tid; E
    {{{ t' s' v, RET v;
        ⌜ sr ⊑ s' ∧ (tr ≤ t')%positive ⌝
        ∗ (⊔{Vb} ▷ gps_inv IP IW l γ m)
        ∗ (if decide (AcqRel ⊑ o) then Q t' s' v else ▽{tid} Q t' s' v)
        ∗ GPS_Reader l t' s' v γ }}}.
  Proof.
    iIntros (SUB OR Φ) "(VP & VP2 & I & R) Post".
    (* TODO: lemma *)
    iAssert (⌜ ∃ (γs γl : gname), γ = encode (γs, γl) ⌝)%I
      with "[R]" as %(γs & γl & ENC).
    { rewrite GPS_Reader_eq.
      iDestruct "R" as (γs γl ? ENC) "?". iPureIntro. by do 2 eexists. }
    iApply (GPSRaw_Read IW false 1 1%Qp ∅ ∅ Q R tr sr vr o γ γs γl m Vb E _
              SUB OR ENC with "[$VP $VP2 $I $R //]").
    iIntros "!>" (???) "(?&?&_&?&?)". iApply "Post". by iFrame.
  Qed.

  (* SingleWriter reads *)
  Lemma GPSRaw_ReadSW
    IW R (tr: time) sr vr o (γ γs γl : gname) bs Vb ζ E tid
    (MAX: no_earlier_time ζ tr) :
    ↑histN ⊆ E → o = Relaxed ∨ o = AcqRel → γ = encode (γs,γl) →
    {{{ (▷ <obj> (F γ tr sr vr ={E}=∗ F γ tr sr vr ∗ R))
        ∗ (⊔{Vb} ▷ gps_inv IP IW l γ bs)
        ∗ GPS_Reader l tr sr vr γ
        ∗ l sw⊒{γl} ζ }}}
        Read o #l @ tid; E
    {{{ RET vr;
        (⊔{Vb} ▷ gps_inv IP IW l γ bs)
        ∗ l sw⊒{γl} ζ
        ∗ R }}}.
  Proof.
    iIntros (SubE RLX ENC Φ) "(VP & I & R & W) Post".
    rewrite GPS_Reader_eq. iDestruct "R" as (γs' γl' Vr ENC') "(SS' & #SN)".
    rewrite ENC in ENC'. apply encode_inj, pair_inj in ENC' as [<- <-].
    iDestruct (view_join_view_at_access' with "I") as (V)
      "(#sV & I & Close)". rewrite !view_at_later.
    iDestruct "I" as (μ γs' γl' ζ' tx) "(>%ENC' & >Go & >P & rB & rE & rF)".
    rewrite 4!view_at_objective_iff.
    rewrite ENC in ENC'. apply encode_inj, pair_inj in ENC' as [<- <-].
    iDestruct (AtomicPtsToX_AtomicSWriter_agree_1 with "P W") as %->.
    iDestruct (AtomicSWriter_latest with "W SN") as %Eqtr%map_singleton_subseteq_l.

    iApply wp_fupd.
    iApply (AtomicSWriter_readX with "[$W $P $sV]"); [|done|].
    { clear -RLX. by destruct RLX as [-> | ->]. }
    iIntros "!>" (t' v' V' V'') "(%F & #sV'' & W & P)".
    destruct F as (Eqt' & MAX' & LeV).
    assert (t' = tr) as ->.
    { apply : (anti_symm (⊑)); [apply MAX|apply MAX']; by eexists. }
    rewrite Eqtr in Eqt'. apply Some_inj, pair_inj in Eqt' as [<- <-].
    iDestruct (gps_own_snap_singleton_sub with "Go SS'") as %Eqsr.

    (* the top write is certainly a block-end *)
    have HLa : (cbends ζ) !! tr = Some (vr, Vr).
    { eapply (top_write_block_end μ); eauto.
      intros ? InD. apply MAX, elem_of_dom.
      revert InD. by apply dom_imap_subseteq. }
    iAssert ( ⌜ is_Some (ζ !! tx) ⌝ )%I with "[P]" as %ISx.
    { rewrite AtomicPtsToX_is_SomeX. by iDestruct "P" as %?. }
    apply MAX' in ISx.

    have Eqsr' : μ tr = sr.
    { rewrite map_lookup_imap Eqtr /= in Eqsr. by inversion Eqsr. }
    iAssert (|={E}=> @{Vr} R ∗ resBE IP IW l γ μ ζ tx)%I with "[VP rB]"
      as ">[Rs rB]".
    { rewrite {1}/resBE /gps_res.
      iDestruct (big_sepM_lookup_acc _ _ _ _ HLa with "rB") as "[Hm Close]".
      rewrite Eqsr' decide_True; [|done].
      iMod (view_at_objectively _ Vr with "VP Hm") as "[Hm $]".
      iIntros "!>". iApply ("Close" with "Hm"). }

    iDestruct ("Close" $! (V ⊔ V'') with "[sV''] [Go P rB rE rF]") as "I".
    { rewrite -monPred_in_view_op. iFrame "sV sV''". }
    { iNext. iExists μ, γs, γl, ζ, tx. iFrame. by iPureIntro. }
    iApply "Post". iFrame "I W". iIntros "!>".
    iApply (view_at_elim with "[] Rs").
    iApply (monPred_in_mono with "sV''"). simpl; solve_lat.
  Qed.

  (* We need to acquire the Writer (in [Wv]) to know that t' is the latest write
    event. If we don't need that for [R t' s'] then we won't need Wv. *)
  Lemma GPSRaw_Read_val_dealloc
    IW (isEx: bool) vd tx q (P : vProp) R R' (tc: time) sc vc
    (γ γs γl : gname) bs ζc (Vb Vc0 : view) tid E :
    ↑histN ⊆ E → γ = encode (γs, γl) →
    let Wv t s v : vProp :=
      (gps_snap γs {[t := s]} ∗ ∃ ζ, ⎡ at_writer γl ζ ⎤ ∗
        l sy⊒{γl} ζ ∗ ⌜(fst <$> ζ) !! t = Some v ∧ no_earlier_time ζ t⌝)%I in
    let Px := (if isEx then (@{Vc0} (l casX⊒{γl,tx,q} ζc) ∗ ⌜(tx ≤ tc)%positive ⌝)
               else True)%I in
    {{{ ▷ (∀ t' s', ⌜ sc ⊑ s' ∧ tc ⊑ t' ⌝ -∗
            (P -∗ Px -∗
              (F γ t' s' vd ={E}=∗ ⊒Vb ∗ Wv t' s' vd ∗ R t' s') ∧
              (F_read γ t' s' vd ={E}=∗ False) ∧
              (if isEx then True else IW l γ t' s' vd ={E}=∗ False)) ∧
            <obj> (∀ v,
                    (F_read γ t' s' v ={E}=∗ F_read γ t' s' v ∗ R' t' s' v) ∧
                    (F γ t' s' v ={E}=∗ F γ t' s' v ∗ R' t' s' v) ∧
                    (if isEx then True
                     else IW l γ t' s' v ={E}=∗ IW l γ t' s' v ∗ R' t' s' v)) )
        ∗ ⊔{Vb} ▷ gps_inv IP IW l γ bs
        ∗ P ∗ Px
        ∗ GPS_Reader l tc sc vc γ }}}
      !ᵃᶜ#l @ tid; E
    {{{ t' s' v', RET v';
        ⌜ sc ⊑ s' ∧ (tc ≤ t')%positive ⌝
        ∗ if (decide (v' = vd)) then (R t' s' ∗ l ↦ v')
          else P ∗ Px ∗ R' t' s' v'
               ∗ ⊔{Vb} ▷ gps_inv IP IW l γ bs
               ∗ GPS_Reader l t' s' v' γ }}}.
  Proof.
    iIntros (SUB ENC Wv Px Φ) "(VS & I & P & Px & #R) Post".
    iApply wp_hist_inv; [done|]. iIntros "#HInv".
    rewrite {1}GPS_Reader_eq. iDestruct "R" as (γs' γl' Vc ENC') "(SS' & #SN)".
    rewrite ENC in ENC'. apply encode_inj, pair_inj in ENC' as [<- <-].
    iDestruct (view_join_view_at_access' with "I") as (V) "(#sV & I & Close)".
    rewrite !view_at_later.
    iDestruct "I" as (μ γs' γl' ζ tx') "(>%ENC' & >Go & >Pt & rB & rE & >rF)".
    iAssert (⌜ is_Some (ζ !! tx') ⌝)%I with "[Pt]" as %ISx.
    { clear. rewrite AtomicPtsToX_is_SomeX. by iDestruct "Pt" as %?. }
    iDestruct "rF" as %(FIN & SS & SWCon). rewrite 3!view_at_objective_iff.
    rewrite ENC in ENC'. apply encode_inj, pair_inj in ENC' as [<- <-].
    iDestruct (AtomicPtsToX_AtomicSeen_latest_1 with "Pt SN") as
      %Eqtc%map_singleton_subseteq_l.

    iDestruct (gps_own_snap_singleton_sub with "Go SS'") as %Eqsc.

    iAssert (⌜ if isEx then ζc ⊆ ζ ∧ tx' = tx ∧ (tx' ≤ tc)%positive else True⌝)%I
              with "[Px Pt]" as %IS.
    { rewrite /Px. destruct isEx; [|done]. iDestruct "Px" as "[C %]".
      by iDestruct (AtomicPtsToX_AtomicCASerX_latest with "Pt C") as %[<- ?]. }

    iApply wp_fupd.
    iApply (AtomicSeen_readX with "[$SN $Pt $sV]"); [done..|].
    iIntros "!>" (t' v' V' V'' ζ'') "(%F & #sV'' & ACQ & S' & Pt)". simpl.
    destruct F as ([Sub1 Sub2] & Eqt' & MAX' & LeV). iDestruct "ACQ" as %LeV'.
    have Letc : tc ⊑ t'. { apply MAX'. rewrite lookup_insert. by eexists. }
    have Eqt'' := lookup_weaken _ _ _ _ Eqt' Sub2.
    have Eqμt : toState μ ζ !! t' = Some (μ t') by rewrite map_lookup_imap Eqt''.
    have Lesc : sc ⊑ μ t' by apply (SS _ t' _ _ Eqsc).
    iDestruct (gps_own_snap_singleton _ _ _ _ Eqμt with "Go") as "#Ss'".

    iAssert (GPS_Reader l t' (μ t') v' γ) with "[S']" as "#GR".
    { rewrite ENC. iApply (GPS_Reader_from_seen with "Ss'"); [exact Eqt'|].
      iApply (view_at_elim with "sV'' S'"). }
    iAssert (⊒V')%I with "[]" as "#sV'".
    { by iApply (monPred_in_mono with "sV''"). }

    iApply ("Post" $! t' (μ t') v'). iSplitR; [by iPureIntro|].
    iSpecialize ("VS" $! t' (μ t') with "[%//]").
    case (decide (v' = vd)) => Eqvd; [subst vd|]; last first.
    - rewrite bi.and_elim_r.
      iMod (GPSRaw_read_resources _ _ _ isEx R' _ _ _ tc t' with "[VS] rB rE")
        as "(rB & rE & R)"; [done|done|..].
      { clear -IS. destruct isEx; [|done]. by destruct IS as (?&?&?). }
      { iIntros "!>". rewrite monPred_objectively_elim. by iApply "VS". }
      iDestruct ("Close" $! (V ⊔ V'') with "[sV''] [Go Pt rB rE]") as "I".
      { rewrite -monPred_in_view_op. iFrame "sV sV''". }
      { iNext. iExists μ, γs, γl, ζ, tx'. iFrame. by iPureIntro. }
      iIntros "!>". iFrame "P Px I GR". iApply (view_at_elim with "sV' R").

    - rewrite bi.and_elim_l.
      iSpecialize ("VS" with "P Px").
      iAssert (|={E}=> ⊒Vb ∗ Wv t' (μ t') v' ∗ R t' (μ t'))%I
        with "[VS rB rE]" as ">(#sVb & W & R)".
      { destruct ((cbends ζ) !! t') as [mm'|] eqn: Eqmm'.
        - assert (mm' = (v',V')) as ->.
          { move : Eqmm' => /map_filter_lookup_Some. rewrite Eqt''.
            move => [[<- //]]. }
          rewrite /resBE /gps_res (big_sepM_lookup _ _ _ _ Eqmm').
          iDestruct (view_at_elim with "sV' rB") as "rB".
          destruct isEx; [|case decide => NEq]; simpl;
            [rewrite bi.and_elim_l; iApply "VS"..|rewrite 2!bi.and_elim_r].
          + destruct IS as (_& ? & Letx'). rewrite decide_True; [done|by etrans].
          + done.
          + by iMod ("VS" with "rB") as %?.
        - have Eqt2: (ζ ∖ (cbends ζ)) !! t' = Some (v',V')
            by apply lookup_difference_Some.
          rewrite /resD /gps_res (big_sepM_lookup _ _ _ _ Eqt2).
          iDestruct (view_at_elim with "sV' rE") as "rE".
          destruct isEx; [|case decide => NEq]; simpl.
          + destruct IS as (_& ? & Letx'). rewrite decide_True; [|by etrans].
            iDestruct "rE" as "[rE|rE]";
              [rewrite bi.and_elim_l|rewrite bi.and_elim_r bi.and_elim_l].
            * by iApply ("VS" with "rE").
            * by iMod ("VS" with "rE") as %?.
          + iDestruct "rE" as "[rE|rE]";
              [rewrite bi.and_elim_l|rewrite bi.and_elim_r bi.and_elim_l].
            * by iApply ("VS" with "rE").
            * by iMod ("VS" with "rE") as %?.
          + iDestruct "rE" as "[rE|[rE|rE]]"; [rewrite bi.and_elim_l
                |rewrite bi.and_elim_r bi.and_elim_l|rewrite 2!bi.and_elim_r].
            * by iApply ("VS" with "rE").
            * by iMod ("VS" with "rE") as %?.
            * by iMod ("VS" with "rE") as %?. }

      iDestruct "W" as "(_ & %ζ' & W & SY' & %IS' & %MAXx')".
      iDestruct (AtomicPtsToX_at_writer_agree with "Pt W") as %<-.
      iDestruct (view_at_elim with "[] Pt") as "Pt".
      { rewrite -2!monPred_in_view_op. by iFrame "sV'' sVb sV". }
      iMod (AtomicPtsToX_to_na with "HInv Pt") as (tm vm Vm) "(Pt & sVm & %F)";
        [done|]. destruct F as (Eqtm & Letm & MAXtm).
      assert (tm = t') as ->.
      { apply: (anti_symm (≤)%positive); [apply MAXx'|apply MAXtm]; by eexists. }
      rewrite Eqt'' in Eqtm. apply Some_inj, pair_inj in Eqtm as [<- <-].
      iIntros "!>". by iFrame "R Pt". (* ghost resources are dropped *)
  Qed.

  Lemma GPSRaw_Read_val_dealloc_ex
    IW (P : vProp) R R' vd q (tx tc: time) sc vc
    (γ γs γl : gname) bs ζc (Vb Vc0 : view) tid E :
    ↑histN ⊆ E → γ = encode (γs, γl) →
    let Wv t s v : vProp :=
      (gps_snap γs {[t := s]} ∗ ∃ ζ, ⎡ at_writer γl ζ ⎤ ∗
        l sy⊒{γl} ζ ∗ ⌜(fst <$> ζ) !! t = Some v ∧ no_earlier_time ζ t⌝)%I in
    let Px := (@{Vc0} (l casX⊒{γl,tx,q} ζc) ∗ ⌜(tx ≤ tc)%positive ⌝)%I in
    {{{ ▷ (∀ t' s', ⌜sc ⊑ s' ∧ tc ⊑ t'⌝ -∗
            (P -∗ Px -∗
                (F γ t' s' vd ={E}=∗ ⊒Vb ∗ Wv t' s' vd ∗ R t' s') ∧
                (F_read γ t' s' vd ={E}=∗ False)) ∧
            <obj> (∀ v,
                    (F_read γ t' s' v ={E}=∗ F_read γ t' s' v ∗ R' t' s' v) ∧
                    (F γ t' s' v ={E}=∗ F γ t' s' v ∗ R' t' s' v)))
        ∗ ⊔{Vb} ▷ gps_inv IP IW l γ bs
        ∗ P ∗ Px
        ∗ GPS_Reader l tc sc vc γ }}}
      !ᵃᶜ#l @ tid; E
    {{{ t' s' v', RET v';
        ⌜ sc ⊑ s' ∧ (tc ≤ t')%positive ⌝
        ∗ if (decide (v' = vd)) then (R t' s' ∗ l ↦ v')
          else P ∗ Px ∗ R' t' s' v'
               ∗ ⊔{Vb} ▷ gps_inv IP IW l γ bs
               ∗ GPS_Reader l t' s' v' γ }}}.
  Proof.
    iIntros (SUB ENC Wv Px Φ) "(VP & I & P & Px & R)".
    iApply (GPSRaw_Read_val_dealloc IW true vd tx q P R R' tc sc vc γ γs γl
              bs ζc Vb Vc0 tid E SUB ENC with "[VP $I $P $Px $R]").
    by setoid_rewrite bi.and_True.
  Qed.

  Lemma GPSRaw_Read_val_dealloc_non_ex
    IW (P: vProp) R R' vd (tc: time) sc vc (γ γs γl : gname) bs Vb tid E :
    ↑histN ⊆ E → γ = encode (γs, γl) →
    let Wv t s v : vProp :=
      (gps_snap γs {[t := s]} ∗ ∃ ζ, ⎡ at_writer γl ζ ⎤ ∗
        l sy⊒{γl} ζ ∗ ⌜(fst <$> ζ) !! t = Some v ∧ no_earlier_time ζ t⌝)%I in
    {{{ ▷ (∀ t' s', ⌜sc ⊑ s' ∧ tc ⊑ t'⌝ -∗
            (P -∗ (F γ t' s' vd ={E}=∗ ⊒Vb ∗ Wv t' s' vd ∗ R t' s') ∧
                  (F_read γ t' s' vd ={E}=∗ False) ∧
                  (IW l γ t' s' vd ={E}=∗ False)) ∧
            <obj> (∀ v,
                (F_read γ t' s' v ={E}=∗ F_read γ t' s' v ∗ R' t' s' v) ∧
                (F γ t' s' v ={E}=∗ F γ t' s' v ∗ R' t' s' v) ∧
                (IW l γ t' s' v ={E}=∗ IW l γ t' s' v ∗ R' t' s' v)))
         ∗ ⊔{Vb} ▷ gps_inv IP IW l γ bs
        ∗ P
        ∗ GPS_Reader l tc sc vc γ }}}
      !ᵃᶜ#l @ tid; E
    {{{ t' s' v', RET v';
        ⌜ sc ⊑ s' ∧ (tc ≤ t')%positive ⌝
        ∗ if (decide (v' = vd)) then (R t' s' ∗ l ↦ v')
          else P ∗ R' t' s' v'
               ∗ ⊔{Vb} ▷ gps_inv IP IW l γ bs
               ∗ GPS_Reader l t' s' v' γ }}}.
  Proof.
    iIntros (SUB ENC Wv Φ) "(VP & I & P & R) Post".
    iApply (GPSRaw_Read_val_dealloc IW false vd 1 1%Qp P R R' tc sc vc γ γs γl
              bs ∅ Vb ∅ tid E SUB ENC with "[VP $I $P $R]").
    - iIntros "!>" (t' s') "Le". iSpecialize ("VP" with "Le").
      iSplit; [rewrite bi.and_elim_l|by rewrite bi.and_elim_r].
      iIntros "P _". by iApply "VP".
    - iIntros "!>" (???) "H". iApply "Post". iDestruct "H" as "[$ H]".
      case decide => ?; [done|]. by rewrite bi.True_sep.
  Qed.
End Read.
