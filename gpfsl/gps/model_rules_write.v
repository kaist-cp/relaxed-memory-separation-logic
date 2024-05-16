From iris.proofmode Require Import proofmode.

From gpfsl.logic Require Import lifting.
From gpfsl.logic Require Import atomic_preds atomic_ops.
From gpfsl.gps Require Import cbends.
From gpfsl.gps Require Export model_defs.

Require Import iris.prelude.options.

Implicit Types (t : time) (v : val) (V : view) (ζ : absHist) (γ : gname)
               (E : coPset) (tid : thread_id).

Section Write.
  Context `{!noprolG Σ, !gpsG Σ Prtcl, !atomicG Σ}
          (IP : interpO Σ Prtcl) (l : loc).
  Local Notation iProp := (iProp Σ).
  Local Notation vProp := (vProp Σ).
  Implicit Types
    (s : pr_stateT Prtcl) (χ : stateT Prtcl) (μ : time → pr_stateT Prtcl).

  Notation F := (IP true l).
  Notation F_read := (IP false l).

  (** WRITE *)
  (* TODO: clean up*)
  Lemma resBE_full_impl IW ζ tx γ μ t' s' v V'
    (Lt : tx ⊏ t') (FRESH: ζ !! t' = None) :
    resBE IP IW l γ μ ζ tx -∗ resD IP IW l γ μ ζ tx -∗
    @{V'} F γ t' s' v -∗
      resBE IP IW l γ (<[t':=s']> μ) (<[t':=(v,V')]> ζ) tx ∗
      resD IP IW l γ (<[t':=s']> μ) (<[t':=(v,V')]> ζ) tx.
  Proof.
    iIntros "rBE rD F".
    have Letx: tx ⊑ t' by apply strict_include.
    have INS := cbends_ins_update t' (v,V') ζ FRESH.
    inversion INS; subst; simpl in *;
      match goal with
      | H : context[_ = mblock_ends _ _] |- _ => rename H into EqM
      end.
    - iSplitL "rBE".
      + rewrite /resBE /gps_res {2}/cbends -EqM.
        iApply (big_sepM_mono with "rBE") => t0 ? /map_filter_lookup_Some [Eq ?]/=.
        rewrite fn_lookup_insert_ne; [done|] =>?. subst t0. by rewrite FRESH in Eq.
      + rewrite /resD /gps_res.
        iApply (big_sepM_subseteq _ (<[t':=(v,V')]> (ζ ∖ cbends ζ))).
        { rewrite {1}/cbends -EqM. rewrite insert_difference'; [done|].
          apply map_filter_lookup_None; by left. }
        rewrite big_sepM_insert; last by (apply lookup_difference_None; left).
        rewrite fn_lookup_insert. iSplitL "F".
        { rewrite /= (decide_True _ _ Letx). by iLeft. }
        iApply (big_sepM_mono with "rD") => t0 ? /lookup_difference_Some [Eq _]/=.
        rewrite fn_lookup_insert_ne; [done|] =>?. subst t0. by rewrite FRESH in Eq.
    - have NEqk': k' ≠ t'.
      { move => ?. subst k'. by rewrite FRESH in In. }
      have IN: cbends ζ !! k' = Some v'.
      { apply map_filter_lookup_Some. split; [done|].
        move => t0 m0 Eq0 /= NEqt0. rewrite /cell_adj /= => Eqk'.
        rewrite /cell_adj /= -Eqk' in sL. subst t'. by rewrite FRESH in Eq0. }
      rewrite {1}/resBE /gps_res (big_sepM_delete _ _ _ _ IN).
      iDestruct "rBE" as "[Hm' rBE]". iSplitL "rBE F".
      + rewrite /resBE /gps_res {2}/cbends -EqM.
        rewrite big_sepM_insert; last first.
        { rewrite lookup_delete_ne; [|done]. apply map_filter_lookup_None. by left. }
        rewrite fn_lookup_insert.
        iSplitL "F". { by rewrite /= (decide_True _ _ Letx). }
        iApply (big_sepM_mono with "rBE") => t0 ? /lookup_delete_Some
          [_ /map_filter_lookup_Some [Eq _]]. rewrite fn_lookup_insert_ne; [done|].
        move => ?. subst t0. by rewrite FRESH in Eq.
      + rewrite /resD /gps_res {2}/cbends -EqM.
        iApply (big_sepM_subseteq _ (<[k':=v']> (ζ ∖ cbends ζ))).
        { etrans; [apply difference_insert_subseteq|by rewrite -difference_delete]. }
        rewrite big_sepM_insert; last first.
        { apply lookup_difference_None. right. by eexists. }
        rewrite fn_lookup_insert_ne; [|done]. iSplitL "Hm'".
        { case decide => ?; by iFrame "Hm'". }
        iApply (big_sepM_mono with "rD") => t0 ? /lookup_difference_Some [Eq _]/=.
        rewrite fn_lookup_insert_ne; [done|] =>?. subst t0. by rewrite FRESH in Eq.
    - iSplitR "rD".
      + rewrite /resBE /gps_res /cbends -EqM big_sepM_insert; last first.
        { apply map_filter_lookup_None. by left. } iSplitL "F".
        { by rewrite /= fn_lookup_insert (decide_True _ _ Letx). }
        iApply (big_sepM_mono with "rBE") => t0 ? /map_filter_lookup_Some [Eq _]/=.
        rewrite fn_lookup_insert_ne; [done|] =>?. subst t0. by rewrite FRESH in Eq.
      + rewrite /resD /gps_res {2}/cbends -EqM.
        iApply (big_sepM_subseteq _ (ζ ∖ cbends ζ)).
        { by apply difference_insert_subseteq. }
        iApply (big_sepM_mono with "rD") => t0 ? /lookup_difference_Some [Eq _]/=.
        rewrite fn_lookup_insert_ne; [done|] =>?. subst t0. by rewrite FRESH in Eq.
    - have NEqk': k' ≠ t'.
      { move => ?. subst k'. by rewrite FRESH in In. }
      have IN: cbends ζ !! k' = Some v'.
      { apply map_filter_lookup_Some. split; [done|].
        move => t0 m0 Eq0 /= NEqt0. rewrite /cell_adj /= => Eqk'.
        rewrite /cell_adj /= -Eqk' in sL.  subst t'. by rewrite FRESH in Eq0. }
      rewrite {1}/resBE /gps_res (big_sepM_delete _ _ _ _ IN).
      iDestruct "rBE" as "[Hm' rBE]". iSplitL "rBE".
      + rewrite /resBE /gps_res {2}/cbends -EqM.
        iApply (big_sepM_mono with "rBE") => t0 ? /lookup_delete_Some
          [_ /map_filter_lookup_Some [Eq _]]. rewrite fn_lookup_insert_ne; [done|].
        move => ?. subst t0. by rewrite FRESH in Eq.
      + rewrite /resD /gps_res {2}/cbends -EqM.
        iApply (big_sepM_subseteq _ (<[t':=(v,V')]> (ζ ∖ delete k' (cbends ζ)))).
        { rewrite /cbends. rewrite insert_difference'; [done|].
          apply lookup_delete_None. right. apply map_filter_lookup_None. by left. }
        rewrite big_sepM_insert; last first.
        { apply lookup_difference_None. by left. }
        rewrite fn_lookup_insert. iSplitL "F".
        { rewrite /= (decide_True _ _ Letx); by iFrame "F". }
        iApply (big_sepM_subseteq _ (<[k':=v']> (ζ ∖ cbends ζ))).
        { by rewrite -difference_delete. }
        rewrite big_sepM_insert; last first.
        { apply lookup_difference_None. right. by eexists. }
        rewrite fn_lookup_insert_ne; [|done]. iSplitL "Hm'".
        { case decide => ?; by iFrame "Hm'". }
        iApply (big_sepM_mono with "rD") => t0 ? /lookup_difference_Some [Eq _]/=.
        rewrite fn_lookup_insert_ne; [done|] =>?. subst t0. by rewrite FRESH in Eq.
  Qed.

  (* Normal protocol writes *)
  Lemma GPSRaw_Write
    IW (t : time) s v o v' s' γ (Vrel V Vb : view) E tid (FIN: final_st s') :
    ↑histN ⊆ E → o = Relaxed ∨ o = AcqRel →
    {{{ ⊔{Vb} ▷ gps_inv IP IW l γ false
        ∗ GPS_Reader l t s v γ
        ∗ ⊒V ∗ (if decide (AcqRel ⊑ o) then True else △{tid} ⊒Vrel) }}}
      Write o #l v' @ tid; E
    {{{ (t': time) V' V'', RET #☠;
        ⌜ (t < t')%positive
          ∧ V ⊑ V'' ∧ V ≠ V'' ∧ (¬ V' ⊑ V)
          ∧ if decide (AcqRel ⊑ o) then V'' = V' else Vrel ⊑ V' ∧ V' ⊑ V'' ⌝
        ∗ ⊒V''
        ∗ ⊒V'
        ∗ (@{V'} F γ t' s' v' -∗ ⊔{Vb} ▷ gps_inv IP IW l γ false)
        ∗ @{V'} GPS_Reader l t' s' v' γ }}}.
  Proof.
    iIntros (SUB OW Φ) "(I & R & #sV & sVrel) Post".
    iDestruct (view_join_view_at_access' with "I") as (V0)
      "(#sV0 & I & Close)". rewrite !view_at_later.
    iDestruct "I" as (μ γs γl ζ tx) "(>%ENC & >Go & >P & rB & rE & >rF)".
    iDestruct "rF" as %(FI & SS & MIN).
    rewrite GPS_Reader_eq. iDestruct "R" as (γs' γl' Vr ENC') "(SS & #SN)".
    rewrite ENC in ENC'. apply encode_inj, pair_inj in ENC' as [<- <-].

    iApply wp_fupd.
    iApply (AtomicSeen_concurrent_writeX with "[$SN $P $sV $sVrel]"); [|done|].
    { by destruct OW as [-> | ->]. }

    iIntros "!>" (t' V' V'') "(F & #sV'' & SN' & SN'' & P)".
    iDestruct "F" as %(MAX & FR & LeV'' & NEV'' & NLeV' & HR).
    specialize (MAX t). rewrite lookup_singleton in MAX.
    specialize (MAX ltac:(by eexists)).

    rewrite 3!view_at_objective_iff.
    iDestruct (gps_own_snap_singleton_sub with "Go SS") as %Eqt.
    iMod (gps_own_insert _ _ t' s' with "Go") as "[Go SS']".
    { by rewrite map_lookup_imap FR. }
    rewrite -(toState_insert μ _ _ (v',V')).
    iIntros "!>".
    iApply ("Post" $! t' V' V''). iSplit; [done|].
    iFrame "sV''". iSplitR.
    { iApply (monPred_in_mono with "sV''"). simpl. clear -HR OW.
      destruct OW as [-> | ->]; simpl in HR; by [apply HR|rewrite HR]. }
    iSplitR "SS' SN'"; last first.
    { iExists γs, γl, V'. by iFrame (ENC) "SS' SN'". }
    iIntros "F".
    iApply ("Close" $! (V0 ⊔ V'')).
    { rewrite -monPred_in_view_op. iFrame "sV0 sV''". }
    rewrite view_at_later assoc. iNext.
    iExists (<[t':=s']> μ), γs, γl, _, tx.
    iSplit; [by iPureIntro|]. iFrame "Go P". rewrite view_at_objective_iff.
    have Letx : tx ⊑ t.
    { apply elem_of_dom_2 in Eqt. apply MIN, elem_of_dom.
      move : Eqt. apply dom_imap_subseteq. }
    have Lttx' : tx ⊏ t'.
    { eapply strict_transitive_r; [exact Letx|].
      apply Pos.lt_nle in MAX. split; [|done]. change (t ≤ t')%positive. lia. }
    iDestruct (resBE_full_impl with "rB rE F") as "[$ $]"; [done..|].
    iPureIntro. split; last split.
    - intros t0. case (decide (t0 = t')) => [->|Neq].
      { intros _ _. by rewrite fn_lookup_insert. }
      rewrite lookup_insert_ne; [|done]. rewrite fn_lookup_insert_ne; [|done].
      intros IS DS. apply FI; [done|]. move : DS. clear.
      rewrite /disconnected_from. setoid_rewrite lookup_insert_None.
      naive_solver.
    - move => t1 t2 s1 s2. rewrite 2!map_lookup_imap.
      case (decide (t1 = t')) => [->|?];
        [rewrite lookup_insert fn_lookup_insert
        |rewrite lookup_insert_ne; last done;
        rewrite fn_lookup_insert_ne; last done];
      (case (decide (t2 = t')) => [->|?];
        [rewrite lookup_insert fn_lookup_insert
        |rewrite lookup_insert_ne; last done;
        rewrite fn_lookup_insert_ne; last done]); simpl; [naive_solver| | |].
      + intros <-%Some_inj. destruct (ζ !! t2) eqn:Eqt2; rewrite Eqt2; [|done].
        simpl. intros <-%Some_inj Ltt2. apply FI; [by eexists|].
        (* need to use disconnected_from *)
        exists t'. repeat split; [by apply strict_include|done..].
      + intros _ <-%Some_inj _. apply FIN.
      + clear -SS. specialize (SS t1 t2 s1 s2). by rewrite 2!map_lookup_imap in SS.
    - intros t0. case (decide (t0 = t')) => [->|Neq].
      + intros _. by apply strict_include.
      + rewrite lookup_insert_ne; [|done]. apply MIN.
  Qed.

  (* SingleWriter writes *)
  Lemma GPSRaw_SWWrite_resources IW γ μ ζ (tx: time) sx vx Vx t' s' v' V'
    (MAX: no_earlier_time ζ tx)
    (Lttx: (tx < t')%positive)
    (Eqt' : ζ !! t' = None)
    (Eqx : ζ !! tx = Some (vx, Vx))
    (Eqsx: sx = μ tx) :
    let ζ' : absHist := <[t':=(v',V')]> ζ in
    let μ' := <[t':=s']> μ in
    resBE IP IW l γ μ ζ tx -∗
    resD IP IW l γ μ ζ tx -∗
    @{Vx} F γ tx sx vx ∗
    (@{V'} F γ t' s' v' -∗
      @{Vx} (IW l γ tx sx vx) -∗
      resBE IP IW l γ μ' ζ' t' ∗ resD IP IW l γ μ' ζ' t')
    .
  Proof.
    have In: (cbends ζ) !! tx = Some (vx,Vx).
    { apply map_filter_lookup_Some. split; first done.
      move => t m Eqt NEqt. rewrite /cell_adj /= => Eqtx.
      apply (irreflexive_eq (R:= (Pos.lt)) t t); [done|].
      eapply Pos.le_lt_trans; [by apply MAX|]. rewrite Eqtx. lia. }
    have ?: cbends ζ !! t' = None by apply map_filter_lookup_None; left.
    have NLe: ¬ (t' ≤ tx)%positive by apply Pos.lt_nle.
    have NEqx: t' ≠ tx. { intros ->. by eapply (irreflexive_eq (R:= Pos.lt)). }
    have INS := cbends_ins_update t' (v',V') ζ Eqt'.
    iIntros "rBE rD".
    iDestruct (big_sepM_delete _ _ _ _ In with "rBE") as "[F rBE]".
    rewrite /= Eqsx decide_True; [|done]. iFrame "F".
    iIntros "F IW".
    inversion INS; subst; simpl in *;
      match goal with
      | H : context[_ = mblock_ends _ _] |- _ => rename H into EqM
      end.
    - exfalso. destruct sR as [t0 [m0 [Eqt0 Eqm0]]].
      have Lt': (t' < t0)%positive.
      { rewrite /cell_adj /= in Eqm0. rewrite Eqm0. lia. }
      apply (irreflexive_eq (R:= Pos.lt) t' t'); [done|]. etrans; [exact Lt'|].
      eapply Pos.le_lt_trans; [by eapply MAX|exact Lttx].
    - rewrite /cell_adj /= in sL. clear nR.
      have Eqtx: k' = tx.
      { apply : anti_symm; [by eapply MAX|]. apply Pos.lt_succ_r.
        move : NLe => /Pos.lt_nle. rewrite sL. lia. } subst k'. clear In0 INS.
      iSplitL "rBE F".
      + iApply (big_sepM_subseteq _ (<[t' := (v',V')]> (delete tx (cbends ζ)))).
        { eapply cbends_ins_extend_subseteq; eauto. }
        rewrite big_sepM_insert; last first.
        { apply lookup_delete_None. by right. }
        rewrite decide_True; [|done]. rewrite fn_lookup_insert. iFrame "F".
        iApply (big_sepM_mono with "rBE") => t0 m0 /lookup_delete_Some
          [NEq /map_filter_lookup_Some [Eq0 ?]] /=.
        rewrite fn_lookup_insert_ne; last first.
        { intros ->. by rewrite Eqt' in Eq0. }
        have Lt0: (t0 < tx)%positive.
        { specialize (MAX t0 ltac:(by eexists)). by apply Pos.le_lteq in MAX as []. }
        have NLe1: ¬ (tx ≤ t0)%positive by apply Pos.lt_nle.
        have NLe2: ¬ (t' ≤ t0)%positive. { apply Pos.lt_nle. by etrans. }
        by rewrite (decide_False _ _ NLe1) (decide_False _ _ NLe2).
      + iApply (big_sepM_subseteq _ (<[tx := (vx,Vx)]> (ζ ∖ cbends ζ))).
        { rewrite {1}/cbends -EqM. etrans; [apply difference_insert_subseteq|].
          by rewrite -difference_delete. }
        rewrite big_sepM_insert; last first.
        { apply lookup_difference_None. right. by eexists. }
        iSplitL "IW".
        { rewrite fn_lookup_insert_ne; [|done].
          rewrite (decide_False _ _ NLe); by iFrame "IW". }
        iApply (big_sepM_mono with "rD") => t0 m0 /lookup_difference_Some
          [Eq0 NEq0] /=.
        rewrite fn_lookup_insert_ne; last first.
        { intros ->. by rewrite Eqt' in Eq0. }
        have Lt0: (t0 < tx)%positive.
        { specialize (MAX t0 ltac:(by eexists)).
          apply Pos.le_lteq in MAX as [? | ->]; [done|]. by rewrite In in NEq0. }
        have NLe1: ¬ (tx ≤ t0)%positive by apply Pos.lt_nle.
        have NLe2: ¬ (t' ≤ t0)%positive. { apply Pos.lt_nle. by etrans. }
        by rewrite (decide_False _ _ NLe1) (decide_False _ _ NLe2).
    - iSplitL "rBE F IW".
      + iApply (big_sepM_subseteq _ (<[t':=(v',V')]> (cbends ζ))).
        { by apply mblock_ends_ins_fresh_mono. }
        rewrite big_sepM_insert; [|done].
        rewrite fn_lookup_insert decide_True; [|done]. iFrame "F".
        rewrite (big_sepM_delete _ _ _ _ In). iSplitL "IW".
        { rewrite fn_lookup_insert_ne // (decide_False _ _ NLe). by iFrame "IW". }
        iApply (big_sepM_mono with "rBE") => t0 m0 /lookup_delete_Some
          [NEq /map_filter_lookup_Some [Eq0 ?]] /=.
        rewrite fn_lookup_insert_ne; last first.
        { move => ?. subst t0. by rewrite Eqt' in Eq0. }
        have Lt0: (t0 < tx)%positive.
        { specialize (MAX t0 ltac:(by eexists)). by apply Pos.le_lteq in MAX as []. }
        have NLe1: ¬ (tx ≤ t0)%positive by apply Pos.lt_nle.
        have NLe2: ¬ (t' ≤ t0)%positive. { apply Pos.lt_nle. by etrans. }
        by rewrite (decide_False _ _ NLe1) (decide_False _ _ NLe2).
      + iApply (big_sepM_subseteq _ (ζ ∖ cbends ζ)).
        { rewrite {1}/cbends -EqM. by apply difference_insert_subseteq. }
        iApply (big_sepM_mono with "rD")
          => t0 m0 /lookup_difference_Some [Eq0 NEq0]/=.
        rewrite fn_lookup_insert_ne; last first.
        { intros ->. by rewrite Eqt' in Eq0. }
        have Lt0: (t0 < tx)%positive.
        { specialize (MAX t0 ltac:(by eexists)).
          apply Pos.le_lteq in MAX as [? | ->]; [done|]. by rewrite In in NEq0. }
        have NLe1: ¬ (tx ≤ t0)%positive by apply Pos.lt_nle.
        have NLe2: ¬ (t' ≤ t0)%positive. { apply Pos.lt_nle. by etrans. }
        by rewrite (decide_False _ _ NLe1) (decide_False _ _ NLe2).
    - exfalso. destruct sR as [t0 [m0 [Eqt0 Eqm0]]].
      have Lt': (t' < t0)%positive.
      { rewrite /cell_adj /= in Eqm0. rewrite Eqm0. lia. }
      apply (irreflexive_eq (R:= Pos.lt) t' t'); [done|]. etrans; [exact Lt'|].
      eapply Pos.le_lt_trans; [by eapply MAX|exact Lttx].
  Qed.

  Lemma GPSRaw_WriteSW IW
    (tx : time) sx vx o v' s' ζ (γ γs γl : gname) (Vrel V Vb : view) E tid
    (Exts : sx ⊑ s')
    (MAXt: no_earlier_time ζ tx)
    (Eqtx: (fst <$> ζ) !! tx = Some vx) :
    ↑histN ⊆ E → o = Relaxed ∨ o = AcqRel → γ = encode (γs, γl) →
    {{{ ⊔{Vb} ▷ gps_inv IP IW l γ true
        ∗ gps_snap γs {[tx := sx]}
        ∗ l sw⊒{γl} ζ
        ∗ ⊒V ∗ (if decide (AcqRel ⊑ o) then True else △{tid} ⊒Vrel) }}}
      Write o #l v' @ tid; E
    {{{ (t': time) Vx V' V'', RET #☠;
        let ζ' := <[t' := (v',V')]>ζ in
        ⌜ ζ !! tx = Some (vx, Vx)
          ∧ (tx < t')%positive
          ∧ no_earlier_time ζ' t'
          ∧ V ⊑ V'' ∧ V ≠ V'' ∧ (¬ V' ⊑ V)
          ∧ if decide (AcqRel ⊑ o) then V'' = V' else Vrel ⊑ V' ∧ V' ⊑ V''⌝ ∗
          ⊒V''
          ∗ gps_snap γs {[t' := s']}
          ∗ @{V''} l sw⊒{γl} ζ'
          ∗ @{Vx} F γ tx sx vx
          ∗ (@{V'} F γ t' s' v' -∗ @{Vx} IW l γ tx sx vx -∗
              @{V''} ⊔{Vb} ▷ gps_inv IP IW l γ true) }}}.
  Proof.
    iIntros (SUB OW ENC Φ) "(I & #SS & W & sV & sVrel) Post".
    iDestruct (view_join_elim' with "I sV") as (V0) "(#sV0 & %LeV0 & I)".
    rewrite !view_at_later.

    iDestruct "I" as (μ γs' γl' ζ' tx') "(>%ENC' & >Go & >P & rB & rE & >rF)".
    rewrite ENC in ENC'. apply encode_inj, pair_inj in ENC' as [<- <-].
    iDestruct "rF" as %(FI & SS & MIN).
    iDestruct (AtomicPtsToX_AtomicSWriter_agree_1 with "P W") as %->.
    apply lookup_fmap_Some in Eqtx as ([vx' Vx] & Eqv' & Eqtx).
    simpl in Eqv'. subst vx'.
    iDestruct (AtomicPtsToX_SW_max_time_1 with "P W") as %[ISx MAXtx].
    assert (tx' = tx) as ->.
    { clear -MAXt Eqtx ISx MAXtx.
      apply : (anti_symm (⊑)); [apply MAXt|apply MAXtx]; [done|by eexists]. }
    clear MAXt.

    iApply wp_fupd.
    iApply (AtomicSWriter_writeX with "[$W $P $sV0 $sVrel]"); [|done|].
    { by destruct OW as [-> | ->]. }
    iIntros "!>" (t' V' V'') "(F & #sV'' & W & P)".
    iDestruct "F" as %(MAX' & FR & LeV'' & NEV'' & NLeV' & HR).
    have Lttx: (tx < t')%positive. { by apply MAX'. }
    set ζ' : absHist := <[t':=(v', V')]> ζ.
    have MAX'' : no_earlier_time ζ' t'.
    { clear -MAX'. intros t0. case (decide (t0 = t')) => [->//|?].
      rewrite lookup_insert_ne // => ?. by apply Pos.lt_le_incl, MAX'. }

    rewrite 3!view_at_objective_iff.
    iDestruct (gps_own_snap_singleton_sub with "Go SS") as %Eqsx.
    iMod (gps_own_insert _ _ t' s' with "Go") as "[Go SS']".
    { by rewrite map_lookup_imap FR. }
    rewrite -(toState_insert μ _ _ (v',V')).
    iIntros "!>".
    iApply ("Post" $! t' Vx V' V''). iSplit.
    { iPureIntro. do 3 (split; [done|]). split; [solve_lat|].
      split; last split; last done.
      - intros ->. apply NEV''. by apply : (anti_symm (⊑)).
      - intros NLEV'. apply NLeV'. solve_lat. }
    iFrame "sV'' SS' W".
    have Eqsx': sx = μ tx.
    { rewrite map_lookup_imap Eqtx /= in Eqsx. by inversion Eqsx. }
    iDestruct (GPSRaw_SWWrite_resources _ γ μ ζ tx sx vx Vx t' s' v' V'
                  MAXtx Lttx FR Eqtx Eqsx' with "rB rE") as "[$ Close]".
    iIntros "F IW". iDestruct ("Close" with "F IW") as "[rB rE]".
    rewrite view_at_view_join. iNext.
    iExists _, γs, γl, _, _. iFrame (ENC) "Go rB rE". iSplitL.
    { iApply (view_at_mono_2 with "P"). clear -LeV''. solve_lat. }
    iPureIntro. split; last split.
    - intros t1. case (decide (t1 = t')) => [->|Neq].
      { move => _ [td [Le1 [Le2]]]. have ?: td = t' by apply : anti_symm.
        subst td. by rewrite lookup_insert. }
      rewrite fn_lookup_insert_ne; [|done].
      move => SOME [t0 [Le1 [Le2 Eq0]]].
      exfalso. apply (irreflexive_eq (R:= (Pos.lt)) t1 t1); [done|].
      eapply Pos.le_lt_trans; [apply MAXtx|lia].
      by rewrite lookup_insert_ne in SOME.
    - intros t1 t2 s1 s2.
      rewrite 2!map_lookup_imap.
      case (decide (t1 = t')) => [->|?];
        [rewrite lookup_insert fn_lookup_insert
        |rewrite lookup_insert_ne; last done;
        rewrite fn_lookup_insert_ne; last done];
      (case (decide (t2 = t')) => [->|?];
        [rewrite lookup_insert fn_lookup_insert
        |rewrite lookup_insert_ne; last done;
        rewrite fn_lookup_insert_ne; last done]); simpl; [naive_solver| | |].
      + intros <-%Some_inj. destruct (ζ !! t2) eqn:Eqt2; rewrite Eqt2; [|done].
        simpl. intros <-%Some_inj Ltt2. apply FI; [by eexists|].
        (* need to use disconnected_from *)
        exists t'. repeat split; [by apply Pos.lt_le_incl|done..].
      + destruct (ζ !! t1) eqn:Eqt1; rewrite Eqt1; [|done]. simpl.
        intros <-%Some_inj <-%Some_inj Lt'. etrans; [|apply Exts].
        rewrite Eqsx'. apply (SS t1 tx).
        * by rewrite map_lookup_imap Eqt1.
        * by rewrite map_lookup_imap Eqtx.
        * apply MAXtx. by eexists.
      + clear -SS. specialize (SS t1 t2 s1 s2). by rewrite 2!map_lookup_imap in SS.
    - intros t0. case (decide (t0 = t')) => [->|Neq].
      + move => _ _ [td [Le1 [Le2]]]. have ?: td = t' by apply : anti_symm.
        subst td. by rewrite lookup_insert.
      + rewrite lookup_insert_ne; [|done]. clear -MAX'.
        intros IS%MAX' Lt _. lia.
  Qed.
End Write.
