From iris.proofmode Require Import proofmode.

From gpfsl.logic Require Import lifting.
From gpfsl.logic Require Import atomic_ghost atomic_preds atomic_ops.
From gpfsl.gps Require Import cbends.
From gpfsl.gps Require Export model_defs.

Require Import iris.prelude.options.

Implicit Types (t : time) (v : val) (V : view) (ζ : absHist) (γ : gname)
               (E : coPset) (tid : thread_id).

Section CAS.
  Context `{!noprolG Σ, !gpsG Σ Prtcl, !atomicG Σ}
          (IP : interpO Σ Prtcl) (l : loc).
  Local Notation iProp := (iProp Σ).
  Local Notation vProp := (vProp Σ).
  Implicit Types
    (s : pr_stateT Prtcl) (χ : stateT Prtcl) (μ : time → pr_stateT Prtcl).

  Notation F := (IP true l).
  Notation F_read := (IP false l).

  (** * CAS rules for single-writer protocols --------------------------------*)
  Lemma GPSRaw_CAS_resources (IW: loc → gname → time → Prtcl → val → vProp)
    γ μ ζ (tx: time) t' v' V' t s v V
    (Letx': (tx ≤ t')%positive) (Let': (t' < t)%positive)
    (FRt: ζ !! t = None)
    (Eqt': ζ !! t' = Some (v',V')) (Eqm': cbends ζ !! t' = Some (v',V'))
    (ADJ: t = (t'+1)%positive) :
    gps_res (λ t v , if decide (tx ≤ t)%positive
                     then IP true l γ t (μ t) v else IW l γ t (μ t) v)%I
            (delete t' (cbends ζ)) -∗
    resD IP IW l γ μ ζ tx -∗
    @{V} F γ t s v -∗
    @{V'} F_read γ t' (μ t') v' -∗
      resBE IP IW l γ (<[t:=s]> μ) (<[t:=(v,V)]> ζ) tx ∗
      resD IP IW l γ (<[t:=s]> μ) (<[t:=(v,V)]> ζ) tx.
  Proof.
    iIntros "rBE rD F Fr".
    have ?: t' ≠ t. { lia. }
    have HLN: delete t' (cbends ζ) !! t = None.
    { rewrite lookup_delete_ne; [by apply map_filter_lookup_None; left|done]. }
    have Letx: (tx ≤ t)%positive by lia.
    have INS := cbends_ins_update t (v,V) ζ FRt.
    inversion INS; subst; simpl in *;
      match goal with
      | H : context[_ = mblock_ends _ _] |- _ => rename H into EqM
      end.
    - exfalso. by apply (nL _ _ Eqt').
    - rewrite /cell_adj /= in sL. have ?: k' = t' by lia. subst k'.
      rewrite Eqt' in In. apply Some_inj in In as <-. iSplitL "rBE F".
      + rewrite /resBE /gps_res {2}/cbends -EqM big_sepM_insert //=
                (decide_True _ _ Letx) fn_lookup_insert. iFrame "F".
        iApply (big_sepM_mono with "rBE") => t0 ? /lookup_delete_Some
          [_ /map_filter_lookup_Some [Eq _]].
        rewrite fn_lookup_insert_ne; [done|]. intros <-. by rewrite FRt in Eq.
      + iApply (big_sepM_subseteq _ (<[t':=(v',V')]> (ζ ∖ cbends ζ))).
        { rewrite {1}/cbends -EqM. etrans; [by apply difference_insert_subseteq|].
          by rewrite -difference_delete. }
        rewrite big_sepM_insert; last first.
        { apply lookup_difference_None. right. by eexists. }
        rewrite (decide_True _ _ Letx') fn_lookup_insert_ne; [|done].
        iSplitL "Fr"; [by iFrame "Fr"|].
        iApply (big_sepM_mono with "rD") => t0 ? /lookup_difference_Some [Eq _].
        rewrite fn_lookup_insert_ne; [done|]. intros <-. by rewrite FRt in Eq.
    - exfalso. by apply (nL _ _ Eqt').
    - rewrite /cell_adj /= in sL. have ?: k' = t' by lia. subst k'.
      rewrite Eqt' in In. apply Some_inj in In as <-. iSplitL "rBE".
      + rewrite /resBE /gps_res {2}/cbends -EqM.
        iApply (big_sepM_mono with "rBE") => t0 ? /lookup_delete_Some
          [_ /map_filter_lookup_Some [Eq _]].
        rewrite fn_lookup_insert_ne; [done|]. intros <-. by rewrite FRt in Eq.
      + rewrite /resD /gps_res {2}/cbends -EqM.
        rewrite (difference_delete _ _ _ (v',V')); [|by rewrite lookup_insert_ne].
        rewrite big_sepM_insert; last first.
        { apply lookup_difference_None. right. by eexists. }
        rewrite (decide_True _ _ Letx') fn_lookup_insert_ne; [|done].
        iSplitL "Fr"; [by iFrame "Fr"|].
        rewrite -insert_difference'; last first.
        { apply map_filter_lookup_None. by left. }
        rewrite big_sepM_insert; last first.
        { apply lookup_difference_None. by left. }
        rewrite (decide_True _ _ Letx) fn_lookup_insert.
        iSplitL "F"; [by iFrame "F"|].
        iApply (big_sepM_mono with "rD") => t0 ? /lookup_difference_Some [Eq _].
        rewrite fn_lookup_insert_ne; [done|]. intros <-. by rewrite FRt in Eq.
  Qed.

  (* We only use this rule for the case successful write mode ow = AcqRel,
    even though we can also state and prove it for ow = Relaxed.
    The precondition [oEX] of this rule ensures that the thread has seen the
    exclusive write [tx]. Furthermore, if the CAS succeeds, it only does so on
    the latest write [t], because
    (1) if the thread has observed [tx], the writes are in a contiguous block
      from [tx] to [t].
    (2) otherwise, due to [(P -∗ IW l γ t' s' #vr ={E}=∗ False)], the thread
      cannot CAS on a block end that is before [tx]. *)
  Lemma GPSRaw_CAS_int_write_view
    IW (isEx: bool) (tc tx: time) ζc sc vc orf or (vr: Z) (vw: val)
    (γ γs γl : gname) q (Vb V Vc0 : view) E
    (P: vProp) (R : time → pr_stateT Prtcl → lit → vProp) tid :
    ↑histN ⊆ E →
    orf = Relaxed ∨ orf = AcqRel → or = Relaxed ∨ or = AcqRel →
    γ = encode (γs, γl) →
    let Wv t s v : vProp :=
      (gps_snap γs {[t := s]} ∗ ∃ ζ, ⎡ at_writer γl ζ ⎤ ∗
        l sy⊒{γl} ζ ∗ ⌜(fst <$> ζ) !! t = Some v ∧ no_earlier_time ζ t⌝)%I in
    let Px := (if isEx then (@{Vc0} (l casX⊒{γl,tx,q} ζc) ∗ ⌜(tx ≤ tc)%positive ⌝)
                else P)%I in
    {{{ (▷ <obj> ∀ t' s' v, ⌜sc ⊑ s' ∧ tc ⊑ t'⌝ -∗
              (if isEx then (F γ t' s' v ∨ F_read γ t' s' v)
               else (F γ t' s' v ∨ F_read γ t' s' v ∨ IW l γ t' s' v)) -∗
              ⌜∃ vl, v = #vl ∧ lit_comparable vr vl⌝)
        ∗ (∀ t' s', ⌜sc ⊑ s' ∧ tc ⊑ t'⌝ -∗
            (if isEx then True else (P -∗ ▷ IW l γ t' s' #vr ={E}=∗ False)) ∧
            ∀ (v: lit), ⌜lit_neq vr v⌝ -∗
              ▷ <obj> ((F_read γ t' s' #v ={E}=∗ F_read γ t' s' #v ∗ R t' s' v) ∧
                      (F γ t' s' #v ={E}=∗ F γ t' s' #v ∗ R t' s' v) ∧
                      (if isEx then True else
                        IW l γ t' s' #v ={E}=∗ IW l γ t' s' #v ∗ R t' s' v)))
        ∗ ⊔{Vb} ▷ gps_inv IP IW l γ true
        ∗ GPS_Reader l tc sc vc γ
        ∗ Px
        ∗ ⊒V }}}
      CAS #l #vr vw orf or AcqRel @ tid; E
    {{{ b (v': lit) s' (t': time) V' V'', RET #b;
        ⌜ sc ⊑ s' ∧ V ⊑ V'' ⌝
        ∗ ⊒V''
        ∗ Px
        ∗ ( (∃ (t: time) (Vr : view),
              ⌜ b = true ∧ v' = LitInt vr ∧ (tc ≤ t)%positive ∧ (t < t')%positive
                ∧ Vr ⊑ V'
                ∧ if decide (AcqRel ⊑ or) then V' = V'' else V'' ⊑ V' ⌝
              ∗ (if decide (AcqRel ⊑ or) then ⊒V' else ▽{tid} ⊒V')
              ∗ (@{V'} Wv t s' #v' -∗
                  ∀ s'', ⌜s' ⊑ s''⌝ ={E}=∗
                    @{V''} GPS_Reader l t' s'' vw γ ∗
                    @{V'} Wv t' s'' vw ∗
                    (@{V'} F γ t' s'' vw -∗ @{Vr} F_read γ t s' #v'
                        ={E}=∗ @{V''} ⊔{Vb} ▷ gps_inv IP IW l γ true ))
              ∗ @{Vr} F γ t s' #v'
              ∗ GPS_Reader l t s' #v' γ)
          ∨ ( ⌜ b = false ∧ lit_neq vr v' ∧ (tc ≤ t')%positive ⌝
              ∗ (if decide (AcqRel ⊑ orf) then ⊒V' else ▽{tid} ⊒V')
              ∗ ⊔{Vb} ▷ gps_inv IP IW l γ true
              ∗ GPS_Reader l t' s' #v' γ
              ∗ if decide (AcqRel ⊑ orf) then R t' s' v' else ▽{tid} R t' s' v' ))
        }}}.
  Proof.
    iIntros (SUB ORF OR ENC Wv Px Φ) "(Comp & VS &I & #R & Px & #sV) Post".
    rewrite GPS_Reader_eq. iDestruct "R" as (γs' γl' Vc ENC') "(SS' & #SN)".
    rewrite ENC in ENC'. apply encode_inj, pair_inj in ENC' as [<- <-].
    iDestruct (view_join_view_at_access with "sV I") as (V0 LeVV0)
      "(#sV0 & I & Close)". rewrite !view_at_later.
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

    iAssert (▷ ⌜ ∀ t v, no_earlier_time {[tc := (vc, Vc)]} t →
                fst <$> ζ !! t = Some v → ∃ vl : lit, v = #vl ∧
                lit_comparable vr vl⌝)%I
    with "[rB rE Comp]" as "#> %COMP {Comp}".
    { iIntros "!>" (t v Letc' Eqv). rewrite -lookup_fmap in Eqv.
      apply lookup_fmap_Some in Eqv as [[v1 V1] [Eqv1 Eqv]].
      simpl in Eqv1. subst v1.
      have Eqs := toState_lookup_state_inv μ _ _ _ Eqv.
      have Letc: (tc ≤ t)%positive.
      { apply Letc'. rewrite lookup_insert. by eexists. }
      have Les: sc ⊑ μ t. { by apply (SS _ _ _ _ Eqsc Eqs). }
      iDestruct (view_at_objectively _ V1 with "Comp") as "Comp".
      iSpecialize ("Comp" $! t (μ t) v with "[%//]").
      destruct ((cbends ζ) !! t) as [vV|] eqn:Eqtm.
      - rewrite /resBE /gps_res (big_sepM_lookup _ _ _ _ Eqtm).
        assert (vV = (v, V1)) as ->.
        { move : Eqtm => /map_filter_lookup_Some [Eqtm _]. rewrite Eqv in Eqtm.
          by inversion Eqtm. }
        destruct isEx;
          [destruct IS as (? & -> & Lettt); rewrite /= decide_True; [|lia]
          |case_decide]; by iDestruct ("Comp" with "[$rB//]") as %?.
      - have Eqtm2: (ζ ∖ cbends ζ) !! t = Some (v,V1)
          by apply lookup_difference_Some.
        rewrite /resD /gps_res (big_sepM_lookup _ _ _ _ Eqtm2).
        destruct isEx;
          [destruct IS as (? & -> & Lettt); rewrite /= decide_True; [|lia]
          |case_decide]; [|rewrite assoc|];
          by iDestruct ("Comp" with "[$rE//]") as %?. }

    iApply (AtomicSeen_CASX_later _ _ _ ζ tx' orf or _ _ _ ∅ false _ _ _ _ _
                E (λ _, E) with "SN Pt sV0 []"); [| |done..|].
    { by destruct ORF as [-> | ->]. } { by destruct OR as [-> | ->]. }
    iIntros (b t' v' Vr Vw V'' ζ'' ζn) "F".
    iDestruct "F" as %([Sub1 Sub2] & Eqt' & Let' & LeV & CASE).
    have LeVV'' : V ⊑ V'' by etrans.

    iIntros (EqVr) "S1 !>". iExists ∅.
    rewrite andb_false_r. iSplit; [done|]. iIntros "_".
    destruct CASE as [(-> & NEqv' & ->)|
                (-> &FR & Eqζn & Eq'' & LeVw & NEqVw & NLeVr & NEqV'' & LeVw')].
    - (* failure case *)
      have Lec': (tc ≤ t')%positive.
      { apply Let'. rewrite lookup_insert. by eexists. }
      have Eqt'' := (lookup_weaken _ _ _ _ Eqt' Sub2).
      have Eqst' : toState μ ζ !! t' = Some (μ t').
      { by rewrite map_lookup_imap Eqt''. }
      have Exts: sc ⊑ μ t' by apply (SS _ _ _ _ Eqsc Eqst').

      iSpecialize ("VS" $! t' (μ t') with "[%]"); [done|].
      rewrite bi.and_elim_r. iSpecialize ("VS" $! v' with "[%]"); [done|].
      iIntros "#sV'' (SN' & Pt & sVr) !> !>".
      iMod (GPSRaw_read_resources _ _ IW isEx (λ t s v, ⌜v = #v'⌝ ∗ R t s v')%I
                _ _ _ _ _ #v' _ _ _ Eqt'' Lec' with "[VS] rB rE")
          as "(rB & rE & _ & Rd)".
      { clear -IS. destruct isEx; [|done]. by destruct IS as (?&?&?). }
      { iIntros "!>". rewrite monPred_objectively_elim.
        have Eqv' : #v' = #v' by done. destruct isEx; iFrame (Eqv').
        - by rewrite assoc bi.and_elim_l. - iFrame. }

      iDestruct (gps_own_snap_singleton _ _ _ _ Eqst' with "Go") as "#GS'".
      iIntros "!>". iApply ("Post" $! false v' (μ t') t' Vr V'').
      iSplit; [done|]. iFrame "sV'' Px". iRight. iSplit; [done|].
      iDestruct ("Close" $! (V0 ⊔ V'') with "[] [Go Pt rB rE]") as "$".
      { rewrite -monPred_in_view_op. iFrame "sV0 sV''". }
      { rewrite assoc. iNext. iExists μ, γs, γl, _, _.
        iFrame (ENC) "Go Pt rB rE". by iPureIntro. }
      iAssert (PrtSeen l t' (μ t') #v' γ) with "[S1]" as "$".
      { iExists γs, γl, _. iFrame (ENC) "GS'".
        iApply (view_at_elim with "sV'' S1"). }
      destruct ORF as [-> | ->]; simpl.
      + iSplit; [iFrame "sVr"|]. iApply (acq_at_intro with "sVr Rd").
      + iDestruct "sVr" as %?.
        iDestruct (monPred_in_mono with "sV''") as "sVr"; [done|].
        iDestruct (view_at_elim with "sVr Rd") as "$". by iFrame "sVr".

    - (* success case *)
      simpl in LeVw'. subst v'.
      set t:= (t'+1)%positive.
      have Letc: (tc ≤ t')%positive.
      { apply Let'. rewrite lookup_insert. by eexists. }
      have Eqt'' := (lookup_weaken _ _ _ _ Eqt' Sub2).
      have Eqtζ : ζ !! t' = Some (#vr, Vr).
      { rewrite Eqζn lookup_insert_ne in Eqt''; [done|clear;lia]. }
      have Eqst' : toState μ ζ !! t' = Some (μ t') by rewrite map_lookup_imap Eqtζ.
      have Exts: sc ⊑ μ t' by apply (SS _ _ _ _ Eqsc Eqst').

      iSpecialize ("VS" $! t' (μ t') with "[%//]"). rewrite bi.and_elim_l.
      iIntros "#sV'' [Vs sVw] !> !>".

      (* get full interpretation *)
      have Eqm': cbends ζ !! t' = Some (#vr,Vr).
      { apply map_filter_lookup_Some. split; [done|].
        move => /= t1 m1 Eqm1 NEqt1 Eqf. rewrite /cell_adj /= in Eqf.
        by rewrite Eqf FR in Eqm1. }
      rewrite /resBE /gps_res (big_sepM_delete _ _ _ _ Eqm') /=.
      iDestruct "rB" as "[F rB]".
      iAssert (|={E}=> (@{Vr} F γ t' (μ t') #vr) ∗ Px)%I
          with "[F VS Px]" as ">(F & Px)".
      { iClear "#". case decide => Lt; [by iFrame|]. rewrite /Px. destruct isEx.
        - exfalso. clear -Letc Lt IS. destruct IS as (? & -> & Letx'). lia.
        - iSpecialize ("VS" with "Px"). clear.
          iDestruct (view_at_intro with "VS") as (V0) "[_ VS]".
          iMod (view_at_mono_2 _ (Vr ⊔ V0) with "VS [$F//]") as %?;
            [solve_lat|done]. }

      have Lttt' : (t' < t)%positive by lia.

      iIntros "!>". iApply ("Post" $! _ vr (μ t') t Vw V'').
      iSplitR; [done|]. iFrame "sV'' Px".
      iLeft. iExists t', Vr. iSplit; [done|]. iSplitL "sVw".
      { clear -OR. destruct OR as [-> | ->]; simpl; [done|].
        iDestruct "sVw" as %?. by iApply (monPred_in_mono with "sV''"). }

      iDestruct (gps_own_snap_singleton _ _ _ _ Eqst' with "Go") as "#Got'".
      iSplitR "F S1"; last first.
      { iFrame "F". iExists γs, γl, Vr. iFrame (ENC) "Got'".
        iApply (view_at_elim with "sV'' S1"). }
      iIntros "(Gs & %ζx & W & SYs & %IS' & %MAX)" (s Exts').
      iMod ("Vs" with "[$W]") as "((-> & W & SY2) & SS2 & Pts & SS2')".

      iMod (gps_own_insert _ _ t s with "Go") as "[Go #Gs']".
      { by rewrite map_lookup_imap FR. }

      iIntros "!>". iSplitL "SS2"; last iSplitL "SY2 SYs W".
      { iExists γs, γl, _. iFrame (ENC) "Gs'".
        iApply (view_at_mono with "SS2"); [done|].
        by apply AtomicSeen_mono_lookup_singleton. }
      { iFrame "Gs'". iExists _. iFrame "W". rewrite Eqζn. iSplitL.
        - iCombine "SY2 SYs" as "SY". iApply (view_at_mono with "SY"); [done|].
          iIntros "[S1 S2]". rewrite insert_union_singleton_l.
          iApply (AtomicSync_join with "S1 S2").
        - iPureIntro. split. { by rewrite lookup_fmap lookup_insert. }
          move => t1. case (decide (t1 = t)) => [->//|?].
          rewrite lookup_insert_ne; [|done]. move => /MAX Le.
          etrans; [apply Le|]. rewrite /t. by apply Pos.lt_le_incl. }
      iIntros "F Fr".

      have ?: (tx' ≤ t')%positive by apply MAX.
      iDestruct (GPSRaw_CAS_resources IW γ μ ζ tx' t' #vr Vr t s vw Vw
                  with "rB rE F Fr") as "[rB rE]"; [done..|].
      iIntros "!>". iClear "Close". rewrite view_at_view_join.
      iNext. rewrite -(toState_insert μ ζ t (vw,Vw)) -Eqζn.
      iExists _, γs, γl, _, tx'. iFrame (ENC) "Go rB rE". iSplitL "Pts".
      { iApply (view_at_mono_2 with "Pts"). solve_lat. }
      iPureIntro. rewrite Eqζn. split; last split.
      + intros t0. case (decide (t0 = t)) => [->|Neq].
        { intros _ (td & ? & ? & [??]%lookup_insert_None) s0.
          rewrite fn_lookup_insert. etrans; last apply Exts'.
          apply FIN; [done|]. exists td. split; [done|]. split; [lia|done]. }
        rewrite lookup_insert_ne; [|done]. rewrite fn_lookup_insert_ne; [|done].
        intros IS0 DS. apply FIN; [done|]. move : DS. clear.
        rewrite /disconnected_from. setoid_rewrite lookup_insert_None.
        naive_solver.
      + move => t1 t2 s1 s2. rewrite 2!map_lookup_imap.
        case (decide (t1 = t)) => [->|?];
          [rewrite lookup_insert fn_lookup_insert
          |rewrite lookup_insert_ne; last done;
          rewrite fn_lookup_insert_ne; last done];
        (case (decide (t2 = t)) => [->|?];
          [rewrite lookup_insert fn_lookup_insert
          |rewrite lookup_insert_ne; last done;
          rewrite fn_lookup_insert_ne; last done]); simpl; [naive_solver| | |].
        * intros <-%Some_inj. destruct (ζ !! t2) eqn:Eqt2; rewrite Eqt2; [|done].
          simpl. intros <-%Some_inj Ltt2. apply FIN; [by eexists|].
          (* need to use disconnected_from *)
          exists t. repeat split; [lia|done..].
        * intros Eqt1 <-%Some_inj Let1.
          etrans; last apply Exts'. eapply (SS t1 t'); [|done..|lia].
          by rewrite map_lookup_imap.
        * specialize (SS t1 t2 s1 s2). by rewrite 2!map_lookup_imap in SS.
      + intros t0. case (decide (t0 = t)) => [->|Neq].
        * intros _ _ (td & ? & ? & [??]%lookup_insert_None).
          apply (SWCon t'); [done..|].
          exists td. split; [done|]. split; [lia|done].
        * rewrite lookup_insert_ne; [|done].
          intros IS0 Le0 (td & ? & ? & [??]%lookup_insert_None).
          apply (SWCon _ IS0 Le0).
          exists td. split; [done|]. split; [lia|done].
  Qed.

  (* TODO: cleanup with GPSRaw_CAS_int_write_view *)
  Lemma GPSRaw_CAS_int_write
    IW (isEx dropR: bool) (tc tx: time) q sc vc orf or ow (vr: Z) (vw: val)
    (γ γs γl : gname) ζc (V Vrel Vb Vc0 : view) tid (E E' : coPset)
    (P: vProp) (Q Q1 Q2: time → pr_stateT Prtcl → vProp)
    (R : time → pr_stateT Prtcl → lit → vProp) :
    ↑histN ⊆ E → E' ⊆ E →
    orf = Relaxed ∨ orf = AcqRel →
    or = Relaxed ∨ or = AcqRel → ow = Relaxed ∨ ow = AcqRel →
    γ = encode (γs, γl) →
    let Wv t s v : vProp :=
      (gps_snap γs {[t := s]} ∗ ∃ ζ, ⎡ at_writer γl ζ ⎤ ∗
        l sy⊒{γl} ζ ∗ ⌜(fst <$> ζ) !! t = Some v ∧ no_earlier_time ζ t⌝)%I in
    let Px := (if isEx then (@{Vc0} (l casX⊒{γl,tx,q} ζc) ∗ ⌜ (tx ≤ tc)%positive ⌝)
               else True)%I in
    let Rs t s v : vProp :=
      (GPS_Reader l t s v γ ∗
        ∃ tx ζs Vs, @{Vs} (l casX⊒{γl,tx,q} ζs) ∗ ⌜(tx ≤ t)%positive⌝)%I in
    let VS t' s' :=
      ((<obj> (▷ F γ t' s' #vr ={E}=∗ ▷ Q1 t' s' ∗ ▷ Q2 t' s')) ∗
             (P -∗ ▷ Q2 t' s' ={E}=∗ ▷ Wv t' s' #vr ∗
                ∃ s'', ⌜s' ⊑ s''⌝ ∗
                  (∀ t , ⌜(t' < t)%positive⌝ -∗
                      ▷ Wv t s'' vw -∗
                      (if isEx && dropR then ▷ Rs t s'' vw else True) ={E}=∗
                      (<obj> (▷ Q1 t' s' ={E}=∗ ▷ F_read γ t' s' #vr)) ∗
                      |={E}[E']▷=> Q t s'' ∗ ▷ F γ t s'' vw)))%I in
    let Vs V1 V2 o := if decide (AcqRel ⊑ o) then V1 else V2 in
    {{{ ⊒V ∗ (if decide (AcqRel ⊑ ow) then True else △{tid} ⊒Vrel) ∗
        Px ∗
        @{Vs V Vrel ow} P
        ∗ ▷ (<obj> ∀ t' s' v, ⌜ sc ⊑ s' ∧ tc ⊑ t' ⌝ -∗
              (if isEx then (F γ t' s' v ∨ F_read γ t' s' v)
              else (F γ t' s' v ∨ F_read γ t' s' v ∨ IW l γ t' s' v)) -∗
              ⌜∃ vl, v = #vl ∧ lit_comparable vr vl⌝)
        ∗ @{Vs V Vrel ow}
            (∀ t' s', ⌜ sc ⊑ s' ∧ tc ⊑ t' ⌝ -∗
              ((if isEx then True else (P -∗ ▷ IW l γ t' s' #vr ={E}=∗ False)) ∧
                VS t' s') ∧
              (▷ ∀ (v: lit), ⌜lit_neq vr v⌝ -∗
                <obj> ((F_read γ t' s' #v ={E}=∗ F_read γ t' s' #v ∗ R t' s' v) ∧
                      (F γ t' s' #v ={E}=∗ F γ t' s' #v ∗ R t' s' v) ∧
                      if isEx then True else
                      (IW l γ t' s' #v ={E}=∗ IW l γ t' s' #v ∗ R t' s' v))))
        ∗ ⊔{Vb} ▷ gps_inv IP IW l γ true
        ∗ GPS_Reader l tc sc vc γ }}}
      CAS #l #vr vw orf or ow @ tid; E
    {{{ b (v': lit) s' (t': time) V' V'', RET #b;
        ⌜ sc ⊑ s' ∧ V ⊑ V'' ⌝
        ∗ ⊒V''
        ∗ ⊔{Vb} ▷ gps_inv IP IW l γ true
        ∗ ( (⌜ b = true ∧ v' = LitInt vr ∧ (tc < t')%positive
              ∧ ( if decide (AcqRel ⊑ ow) then
                    ( if decide (AcqRel ⊑ or) then
                        (* release-acquire CAS *) V' = V''
                      else (* release CAS: *) V'' ⊑ V' )
                  else (* relaxed write CAS *) Vrel ⊑ V' ) ⌝
            ∗ (if dropR then True else Px)
            ∗ GPS_Reader l t' s' vw γ
            ∗ (if decide (AcqRel ⊑ or) then ⌜V' ⊑ V''⌝ else ▽{tid} ⊒V')
            ∗ @{V'} Q t' s')
        ∨ ( ⌜ b = false ∧ lit_neq vr v' ∧ (tc ≤ t')%positive ⌝
            ∗ GPS_Reader l t' s' #v' γ
            ∗ (if decide (AcqRel ⊑ orf) then ⊒V' else ▽{tid} ⊒V')
            ∗ Px
            ∗ @{V'} R t' s' v'
            ∗ @{Vs V Vrel ow} P ))
        }}}.
  Proof.
    iIntros (SUB1 SUB2 ORF OR OW ENC Wv Px Rs VS Vs Φ).
    iIntros "(sV & Hrel & Px & P & Comp & VS & I & #R) Post".
    rewrite {1}GPS_Reader_eq. iDestruct "R" as (γs' γl' Vc ENC') "(SS' & #SN)".
    rewrite ENC in ENC'. apply encode_inj, pair_inj in ENC' as [<- <-].
    iDestruct (view_join_view_at_access' with "I") as (V0)
      "(#sV0 & I & Close)". rewrite !view_at_later.
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

    iAssert (▷ ⌜ ∀ t v, no_earlier_time {[tc := (vc, Vc)]} t →
                fst <$> ζ !! t = Some v → ∃ vl : lit, v = #vl ∧
                lit_comparable vr vl⌝)%I
    with "[rB rE Comp]" as "#> %COMP {Comp}".
    { iIntros "!>" (t v Letc' Eqv). rewrite -lookup_fmap in Eqv.
      apply lookup_fmap_Some in Eqv as [[v1 V1] [Eqv1 Eqv]].
      simpl in Eqv1. subst v1.
      have Eqs := toState_lookup_state_inv μ _ _ _ Eqv.
      have Letc: (tc ≤ t)%positive.
      { apply Letc'. rewrite lookup_insert. by eexists. }
      have Les: sc ⊑ μ t. { by apply (SS _ _ _ _ Eqsc Eqs). }
      iDestruct (view_at_objectively _ V1 with "Comp") as "Comp".
      iSpecialize ("Comp" $! t (μ t) v with "[%//]").
      destruct ((cbends ζ) !! t) as [vV|] eqn:Eqtm.
      - rewrite /resBE /gps_res (big_sepM_lookup _ _ _ _ Eqtm).
        assert (vV = (v, V1)) as ->.
        { move : Eqtm => /map_filter_lookup_Some [Eqtm _]. rewrite Eqv in Eqtm.
          by inversion Eqtm. }
        destruct isEx;
          [destruct IS as (? & -> & Lettt); rewrite /= decide_True; [|lia]
          |case_decide]; by iDestruct ("Comp" with "[$rB//]") as %?.
      - have Eqtm2: (ζ ∖ cbends ζ) !! t = Some (v,V1)
          by apply lookup_difference_Some.
        rewrite /resD /gps_res (big_sepM_lookup _ _ _ _ Eqtm2).
        destruct isEx;
          [destruct IS as (? & -> & Lettt); rewrite /= decide_True; [|lia]
          |case_decide]; [|rewrite assoc|];
          by iDestruct ("Comp" with "[$rE//]") as %?. }

    iApply wp_fupd.
    iApply (AtomicSeen_CASX_later _ _ _ ζ tx' orf or _ _ _ Vrel true _ _ _ _ _
                E' (λ _, ↑histN) with "SN Pt sV Hrel"); [| | |done..|].
    { by destruct ORF as [-> | ->]. } { by destruct OR as [-> | ->]. }
    { by destruct OW as [-> | ->]. }

    iIntros (b t' v' Vr Vw V'' ζ'' ζn) "F".
    iDestruct "F" as %([Sub1 Sub2] & Eqt' & Let' & LeV & CASE).

    iIntros (Eqvr) "S1". rewrite andb_true_r.
    destruct CASE as [(-> & NEqv' & ->)|
                (-> &FR & Eqζn & Eq'' & LeVw & NEqVw & NLeVr & NEqV'' & LeVw')].
    - (* failure case *)
      have Lec': (tc ≤ t')%positive.
      { apply Let'. rewrite lookup_insert. by eexists. }
      have Eqt'' := (lookup_weaken _ _ _ _ Eqt' Sub2).
      have Eqst' : toState μ ζ !! t' = Some (μ t').
      { by rewrite map_lookup_imap Eqt''. }
      have Exts: sc ⊑ μ t' by apply (SS _ _ _ _ Eqsc Eqst').

      iIntros "!>". iExists ∅. iSplit; [done|]. iIntros "_".
      iSpecialize ("VS" $! t' (μ t') with "[%]"); [done|].
      rewrite bi.and_elim_r. iSpecialize ("VS" $! v' with "[%]"); [done|].
      rewrite view_at_objective_iff.
      iIntros "#sV'' (SN' & Pt & sVr)".
      iApply step_fupd_intro; [done|]. iIntros "!>".
      iMod (GPSRaw_read_resources _ _ IW isEx (λ t s v, ⌜v = #v'⌝ ∗ R t s v')%I
                _ _ _ _ _ #v' _ _ _ Eqt'' Lec' with "[VS] rB rE")
          as "(rB & rE & _ & Rd)".
      { clear -IS. destruct isEx; [|done]. by destruct IS as (?&?&?). }
      { iIntros "!>". rewrite monPred_objectively_elim.
        have Eqv' : #v' = #v' by done. destruct isEx; iFrame (Eqv').
        - by rewrite assoc bi.and_elim_l. - iFrame. }

      iDestruct (gps_own_snap_singleton _ _ _ _ Eqst' with "Go") as "#GS'".
      iIntros "!>".
      iApply ("Post" $! false v' (μ t') t' Vr V'').
      iSplit; [done|]. iFrame "sV''".
      iDestruct ("Close" $! (V0 ⊔ V'') with "[] [Go Pt rB rE]") as "$".
      { rewrite -monPred_in_view_op. iFrame "sV0 sV''". }
      { rewrite assoc. iNext. iExists μ, γs, γl, _, _.
        iFrame (ENC) "Go Pt rB rE". by iPureIntro. }
      iRight. iSplit; [done|]. iFrame "Px P Rd". iSplitL "S1".
      { iDestruct (view_at_elim with "sV'' S1") as "S1". rewrite ENC.
        by iApply (GPS_Reader_from_seen_singleton with "GS' S1"). }
      destruct ORF as [-> | ->]; simpl; [iFrame|]. iDestruct "sVr" as %?.
      by iApply (monPred_in_mono with "sV''").

    - (* success case *)
      simpl in LeVw'. subst v'.
      set t:= (t'+1)%positive.
      have Letc: (tc ≤ t')%positive.
      { apply Let'. rewrite lookup_insert. by eexists. }
      have Eqt'' := (lookup_weaken _ _ _ _ Eqt' Sub2).
      have Eqtζ : ζ !! t' = Some (#vr, Vr).
      { rewrite Eqζn lookup_insert_ne in Eqt''; [done|clear;lia]. }
      have Eqst' : toState μ ζ !! t' = Some (μ t') by rewrite map_lookup_imap Eqtζ.
      have Exts: sc ⊑ μ t' by apply (SS _ _ _ _ Eqsc Eqst').

      iSpecialize ("VS" $! t' (μ t') with "[%//]"). rewrite bi.and_elim_l.
      (* get full interpretation *)
      have Eqm': cbends ζ !! t' = Some (#vr,Vr).
      { apply map_filter_lookup_Some. split; [done|].
        move => /= t1 m1 Eqm1 NEqt1 Eqf. rewrite /cell_adj /= in Eqf.
        by rewrite Eqf FR in Eqm1. }

      rewrite /resBE /gps_res (big_sepM_delete _ _ _ _ Eqm') /=.
      iDestruct "rB" as "[F rB]".

      case (decide (tx' ≤ t')%positive) => [Letx|NLe]; last first.
      { rewrite bi.and_elim_l. destruct isEx.
        - exfalso. clear -NLe IS Letc. destruct IS as (? & -> & ?). lia.
        - iRevert "VS F P". iClear "#∗". clear.
          iIntros "VS IW P". iSpecialize ("VS" with "P").
          iMod (view_at_mono_2 _ (Vs V Vrel ow ⊔ Vr) with "VS [IW]") as %?;
            [solve_lat|..|done]. iNext. by iFrame. }

      have Ltt': (t' < t)%positive by rewrite /t; lia.
      have ?: (tx' < t)%positive by eapply Pos.le_lt_trans.
      have Lttc: (tc < t)%positive by eapply Pos.le_lt_trans; [|apply Ltt'].

      rewrite bi.and_elim_r. iDestruct "VS" as "[VS1 VS2]".
      rewrite view_at_objective_iff.
      iDestruct (view_at_objectively _ Vr with "VS1 [F]") as ">[Q1 Q2]".
      { iNext. by iFrame. }
      iSpecialize ("VS2" with "P").
      iMod (view_at_mono_2 _ (Vs V Vrel ow ⊔ Vr) with "VS2 [$Q2]")
        as "(W & %s & %Exts' & VS)"; [solve_lat|].
      rewrite (view_at_later (Wv _ _ _)).
      iDestruct "W" as ">(Gs & %ζ' & W & #SYs & %IS' & %MAX)".
      rewrite view_at_objective_iff.
      iIntros "!>". iExists ζ'. iFrame "W".
      iIntros "(-> & W & #SY2) #sV'' [VS' sVw]".

      iMod (gps_own_insert _ _ t s with "Go") as "[Go #Gs']".
      { by rewrite map_lookup_imap FR. }

      iAssert ((if dropR then True else Px) ∗
               (if dropR then Px else True))%I with "[Px]" as "[Px1 Px2]".
      { destruct dropR; by iFrame "Px". }

      iAssert (@{Vw} GPS_Reader l t s vw γ)%I with "[SY2]" as "#PSY'".
      { iApply (view_at_mono' with "SY2"); [done|].
        iApply (view_at_mono with "[SS']"); [reflexivity|..|].
        - rewrite ENC. apply GPS_Reader_from_sync_singleton.
        - by iFrame "Gs'". }

      have LeVrw : Vs V Vrel ow ⊔ Vr ⊑ Vw.
      { apply lat_join_lub; [|done]. clear -OW OR LeVw' LeV. rewrite /Vs.
        destruct OW as [-> | ->]; simpl in *; [done|].
        destruct OR as [-> | ->]; simpl in *; [solve_lat|by subst]. }
      iMod (view_at_mono_2 with "VS [%//] [W] [Px2]") as "[FR QF]";
        [exact LeVrw|..].
      { iNext. iFrame "Gs'". iExists ζn. iFrame "W". rewrite Eqζn. iSplit.
        - rewrite (view_at_mono_2 _ _ (l sy⊒{γl} ζ) LeVrw).
          iCombine "SY2 SYs" as "SY". iApply (view_at_mono with "SY"); [done|].
          iIntros "[S1 S2]". rewrite insert_union_singleton_l.
          iApply (AtomicSync_join with "S1 S2").
        - iPureIntro; split. { by rewrite lookup_fmap lookup_insert. }
          move => t1. case (decide (t1 = t)) => [->//|?].
          rewrite lookup_insert_ne; [|done]. move => /MAX Le.
          etrans; [apply Le|]. rewrite /t. by apply Pos.lt_le_incl. }
      { destruct dropR; [|by rewrite andb_false_r].
        rewrite /Px. rewrite andb_true_r. destruct isEx; [|done].
        rewrite /Rs. iNext. iFrame "PSY'".
        iExists tx, ζc, Vc0. iDestruct "Px2" as "($ & _)". clear -Lttc IS.
        iPureIntro. destruct IS as (? & -> & Letc'). lia. }
      rewrite view_at_objective_iff.
      iMod (view_at_objectively _ Vr with "FR Q1") as "Fr".
      iMod "QF" as "QF". iIntros "!> !>". iMod "QF" as "[Q F]".
      iMod ("VS'" $! ∅ with "[//]") as "(_ & #SS2 & Pt & SS2')".
      iIntros "!> !>".
      iApply ("Post" $! true vr s t Vw V'').
      iSplit. { iPureIntro. split; [|done]. by etrans. } iFrame "sV''".
      iSplitR "Px1 Q sVw"; last first.
      { iLeft. iSplit; [done|]. iFrame "Px1 Q sVw".
        iDestruct (view_at_elim with "sV'' SS2") as "SS". rewrite ENC.
        by iApply (GPS_Reader_from_seen with "Gs' SS"). }

      iApply ("Close" $! (V0 ⊔ V'')).
      { iApply monPred_in_view_op. iFrame "sV0 sV''". }
      rewrite assoc -(toState_insert μ ζ t (vw,Vw)).
      iNext. iExists _, γs, γl, _, tx'.

      iDestruct (GPSRaw_CAS_resources IW γ μ ζ tx' t' #vr Vr t s vw Vw
                  Letx Ltt' FR Eqtζ Eqm' with "rB rE F Fr") as "[rB rE]"; [done|].
      rewrite -Eqζn. iFrame (ENC) "Go Pt rB rE".

      iPureIntro. rewrite Eqζn. split; last split.
      + intros t0. case (decide (t0 = t)) => [->|Neq].
        { intros _ (td & ? & ? & [??]%lookup_insert_None) s0.
          rewrite fn_lookup_insert. etrans; last apply Exts'.
          apply FIN; [done|]. exists td. split; [done|]. split; [lia|done]. }
        rewrite lookup_insert_ne; [|done]. rewrite fn_lookup_insert_ne; [|done].
        intros IS0 DS. apply FIN; [done|]. move : DS. clear.
        rewrite /disconnected_from. setoid_rewrite lookup_insert_None.
        naive_solver.
      + move => t1 t2 s1 s2. rewrite 2!map_lookup_imap.
        case (decide (t1 = t)) => [->|?];
          [rewrite lookup_insert fn_lookup_insert
          |rewrite lookup_insert_ne; last done;
          rewrite fn_lookup_insert_ne; last done];
        (case (decide (t2 = t)) => [->|?];
          [rewrite lookup_insert fn_lookup_insert
          |rewrite lookup_insert_ne; last done;
          rewrite fn_lookup_insert_ne; last done]); simpl; [naive_solver| | |].
        * intros <-%Some_inj. destruct (ζ !! t2) eqn:Eqt2; rewrite Eqt2; [|done].
          simpl. intros <-%Some_inj Ltt2. apply FIN; [by eexists|].
          (* need to use disconnected_from *)
          exists t. repeat split; [lia|done..].
        * intros Eqt1 <-%Some_inj Let1.
          etrans; last apply Exts'. eapply (SS t1 t'); [|done..|lia].
          by rewrite map_lookup_imap.
        * specialize (SS t1 t2 s1 s2). by rewrite 2!map_lookup_imap in SS.
      + intros t0. case (decide (t0 = t)) => [->|Neq].
        * intros _ _ (td & ? & ? & [??]%lookup_insert_None).
          apply (SWCon t'); [done..|].
          exists td. split; [done|]. split; [lia|done].
        * rewrite lookup_insert_ne; [|done].
          intros IS0 Le0 (td & ? & ? & [??]%lookup_insert_None).
          apply (SWCon _ IS0 Le0).
          exists td. split; [done|]. split; [lia|done].
  Qed.

  (* TODO: Q might want to know about the timestamp/state it read *)
  Lemma GPSRaw_CAS_int_strong_write
    IW (tc tx: time) q sc vc orf or ow (vr: Z) (vw: val)
    (γ γs γl : gname) ζc (V Vrel Vb Vc0 : view) tid E E'
    (P: vProp) (Q Q1 Q2: time → pr_stateT Prtcl → vProp)
    (R : time → pr_stateT Prtcl → lit → vProp) (dropR: bool)
    (LEx: (tx ≤ tc)%positive) :
    ↑histN ⊆ E → E' ⊆ E →
    orf = Relaxed ∨ orf = AcqRel →
    or = Relaxed ∨ or = AcqRel → ow = Relaxed ∨ ow = AcqRel →
    γ = encode (γs, γl) →
    let Wv t s v : vProp :=
      (gps_snap γs {[t := s]} ∗ ∃ ζ, ⎡ at_writer γl ζ ⎤ ∗
        l sy⊒{γl} ζ ∗ ⌜(fst <$> ζ) !! t = Some v ∧ no_earlier_time ζ t⌝)%I in
    let Px := (@{Vc0} (l casX⊒{γl,tx,q} ζc))%I in
    let Rs t s v : vProp :=
      (GPS_Reader l t s v γ ∗
        ∃ tx ζs Vs, @{Vs} (l casX⊒{γl,tx,q} ζs) ∗ ⌜(tx ≤ t)%positive⌝)%I in
    let Vs V1 V2 o := if decide (AcqRel ⊑ o) then V1 else V2 in
    {{{ ⊒V ∗ (if decide (AcqRel ⊑ ow) then True else △{tid} ⊒Vrel) ∗
        @{Vs V Vrel ow} P
        ∗ ▷ (<obj> ∀ t' s' v, ⌜sc ⊑ s' ∧ tc ⊑ t'⌝ -∗
              (F γ t' s' v ∨ F_read γ t' s' v) -∗
              ⌜∃ vl, v = #vl ∧ lit_comparable vr vl⌝)
        ∗ @{Vs V Vrel ow}
            (∀ t' s', ⌜sc ⊑ s' ∧ tc ⊑ t'⌝ -∗
              ((<obj> (▷ F γ t' s' #vr ={E}=∗ ▷ Q1 t' s' ∗ ▷ Q2 t' s')) ∗
                (P -∗ ▷ Q2 t' s' ={E}=∗ ▷ Wv t' s' #vr ∗
                  ∃ s'', ⌜s' ⊑ s''⌝ ∗
                    (∀ t , ⌜(t' < t)%positive⌝ -∗ ▷ Wv t s'' vw -∗
                      (if dropR then ▷ Rs t s'' vw else True) ={E}=∗
                        (<obj> (▷ Q1 t' s' ={E}=∗ ▷ F_read γ t' s' #vr)) ∗
                        |={E}[E']▷=> Q t s'' ∗ ▷ F γ t s'' vw)) )
                ∧ (▷ ∀ (v: lit), ⌜lit_neq vr v⌝ -∗
                    <obj> ((F_read γ t' s' #v ={E}=∗
                              F_read γ t' s' #v ∗ R t' s' v) ∧
                            (F γ t' s' #v ={E}=∗ F γ t' s' #v ∗ R t' s' v))))
        ∗ ⊔{Vb} ▷ gps_inv IP IW l γ true
        ∗ GPS_Reader l tc sc vc γ
        ∗ Px }}}
      CAS #l #vr vw orf or ow @ tid; E
    {{{ b (v': lit) s' (t': time) V' V'', RET #b;
        ⌜ sc ⊑ s' ∧ V ⊑ V'' ⌝
        ∗ ⊒V''
        ∗ ⊔{Vb} ▷ gps_inv IP IW l γ true
        ∗ ( (⌜ b = true ∧ v' = LitInt vr ∧ (tc < t')%positive
              ∧ ( if decide (AcqRel ⊑ ow) then
                    ( if decide (AcqRel ⊑ or) then
                        (* release-acquire CAS *) V' = V''
                      else (* release CAS: *) V'' ⊑ V' )
                  else (* relaxed write CAS *) Vrel ⊑ V' ) ⌝
            ∗ (if dropR then True else Px)
            ∗ GPS_Reader l t' s' vw γ
            ∗ (if decide (AcqRel ⊑ or) then ⌜V' ⊑ V''⌝ else ▽{tid} ⊒V')
            ∗ @{V'} Q t' s')
        ∨ ( ⌜ b = false ∧ lit_neq vr v' ∧ (tc ≤ t')%positive ⌝
            ∗ GPS_Reader l t' s' #v' γ
            ∗ (if decide (AcqRel ⊑ orf) then ⊒V' else ▽{tid} ⊒V')
            ∗ Px
            ∗ @{V'} R t' s' v'
            ∗ @{Vs V Vrel ow} P ))
        }}}.
  Proof.
    iIntros (SUB SUB' ORF OR OW ENC Wv Px Rs Vs Φ)
            "(sV & Hrel & P & Comp & VS & I & R & Px) Post".
    iApply (GPSRaw_CAS_int_write IW true dropR tc tx q _ _ orf or ow vr vw γ _ _
              ζc _ Vrel Vb Vc0 _ E E' P Q Q1 Q2 R SUB SUB' ORF OR OW ENC
              with "[$sV $Hrel $Px $P $Comp VS $I $R]").
    { iFrame (LEx). iApply (view_at_mono with "VS"); [done|].
      iIntros "VS" (t' s' [Ext' Exts']).
      iSpecialize ("VS" $! t' s' with "[%//]"). iSplit; [iSplit|]; [done|..].
      - rewrite bi.and_elim_l. by iDestruct "VS" as "[$ $]".
      - rewrite bi.and_elim_r. by setoid_rewrite bi.and_True. }

    iIntros "!>" (b v' s' t' V' V'') "(F & sV'' & I & CASE )".
    iApply ("Post" $! b v' s' t' V' V''). iFrame "F sV'' I".
    iDestruct "CASE" as "[(FACT & Px & R & Q)|(FACT & R & sVr & Px & Q)]";
      [iLeft|iRight].
    - iFrame "FACT R Q". destruct dropR; [done|].
      by iDestruct "Px" as "($ & % & _)".
    - iFrame "FACT R Q sVr". by iDestruct "Px" as "($ & % & _)".
  Qed.

  Lemma GPSRaw_CAS_int_weak_write
    IW (tc: time) sc vc orf or ow (vr: Z) (vw: val)
    (γ γs γl : gname) (V Vrel Vb : view) tid E E'
    (P: vProp) (Q Q1 Q2: time → pr_stateT Prtcl → vProp)
    (R : time → pr_stateT Prtcl → lit → vProp) :
    ↑histN ⊆ E → E' ⊆ E →
    orf = Relaxed ∨ orf = AcqRel →
    or = Relaxed ∨ or = AcqRel → ow = Relaxed ∨ ow = AcqRel →
    γ = encode (γs, γl) →
    let Wv t s v : vProp :=
      (gps_snap γs {[t := s]} ∗ ∃ ζ, ⎡ at_writer γl ζ ⎤ ∗
        l sy⊒{γl} ζ ∗ ⌜(fst <$> ζ) !! t = Some v ∧ no_earlier_time ζ t⌝)%I in
    let Vs V1 V2 o := if decide (AcqRel ⊑ o) then V1 else V2 in
    {{{ ⊒V ∗ (if decide (AcqRel ⊑ ow) then True else △{tid} ⊒Vrel) ∗
        @{Vs V Vrel ow} P
        ∗ ▷ (<obj> ∀ t' s' v, ⌜sc ⊑ s' ∧ tc ⊑ t'⌝ -∗
              (F γ t' s' v ∨ F_read γ t' s' v ∨ IW l γ t' s' v) -∗
              ⌜∃ vl, v = #vl ∧ lit_comparable vr vl⌝)
        ∗ @{Vs V Vrel ow}
          (∀ t' s', ⌜sc ⊑ s' ∧ tc ⊑ t'⌝ -∗
            ((P -∗ ▷ IW l γ t' s' #vr ={E}=∗ False) ∧
             ((<obj> (▷ F γ t' s' #vr ={E}=∗ ▷ Q1 t' s' ∗ ▷ Q2 t' s')) ∗
             (P -∗ ▷ Q2 t' s' ={E}=∗ ▷ Wv t' s' #vr ∗
                ∃ s'', ⌜s' ⊑ s''⌝ ∗
                  (∀ t , ⌜(t' < t)%positive⌝ -∗ ▷ Wv t s'' vw ={E}=∗
                      (<obj> (▷ Q1 t' s' ={E}=∗ ▷ F_read γ t' s' #vr)) ∗
                      |={E}[E']▷=> Q t s'' ∗ ▷ F γ t s'' vw)) )) ∧
            (▷ ∀ (v: lit), ⌜lit_neq vr v⌝ -∗
              <obj> ((F_read γ t' s' #v ={E}=∗ F_read γ t' s' #v ∗ R t' s' v) ∧
                     (F γ t' s' #v ={E}=∗ F γ t' s' #v ∗ R t' s' v) ∧
                     (IW l γ t' s' #v ={E}=∗ IW l γ t' s' #v ∗ R t' s' v))))
        ∗ ⊔{Vb} ▷ gps_inv IP IW l γ true
        ∗ GPS_Reader l tc sc vc γ }}}
      CAS #l #vr vw orf or ow @ tid; E
    {{{ b (v': lit) s' (t': time) V' V'', RET #b;
        ⌜ sc ⊑ s' ∧ V ⊑ V'' ⌝
        ∗ ⊒V''
        ∗ ⊔{Vb} ▷ gps_inv IP IW l γ true
        ∗ ( (⌜ b = true ∧ v' = LitInt vr ∧ (tc < t')%positive
              ∧ ( if decide (AcqRel ⊑ ow) then
                    ( if decide (AcqRel ⊑ or) then
                        (* release-acquire CAS *) V' = V''
                      else (* release CAS: *) V'' ⊑ V' )
                  else (* relaxed write CAS *) Vrel ⊑ V' ) ⌝
            ∗ GPS_Reader l t' s' vw γ
            ∗ (if decide (AcqRel ⊑ or) then ⌜V' ⊑ V''⌝ else ▽{tid} ⊒V')
            ∗ @{V'} Q t' s')
        ∨ ( ⌜ b = false ∧ lit_neq vr v' ∧ (tc ≤ t')%positive ⌝
            ∗ GPS_Reader l t' s' #v' γ
            ∗ (if decide (AcqRel ⊑ orf) then ⊒V' else ▽{tid} ⊒V')
            ∗ @{V'} R t' s' v'
            ∗ @{Vs V Vrel ow} P ))
        }}}.
  Proof.
    iIntros (SUB SUB' ORF OR OW ENC Wv Vs Φ)
            "(sV & Hrel & P & Comp & VS & I & R) Post".
    iApply (GPSRaw_CAS_int_write IW false false tc 1 1%Qp _ _ orf or ow vr vw
              γ _ _ ∅ V Vrel Vb ∅ _ E E' P Q Q1 Q2 R SUB SUB' ORF OR OW ENC
              with "[$sV $Hrel P $Comp VS $I $R]").
    { iSplitL "P". { iFrame "P". }
      iApply (view_at_mono with "VS"); [done|].
      iIntros "VS" (t' s' [Ext' Exts']).
      iSpecialize ("VS" $! t' s' with "[%//]").
      iSplit; last by rewrite bi.and_elim_r.
      rewrite /= bi.and_elim_l. iSplit; first by rewrite bi.and_elim_l.
      rewrite bi.and_elim_r. iDestruct "VS" as "[$ VS]".
      iIntros "P Q". iMod ("VS" with "P Q") as "[$ VS]". iIntros "!>".
      iDestruct "VS" as (s'') "[Ext VS]". iExists s''. iFrame "Ext".
      iIntros (t) "Lt W _". iApply ("VS" with "Lt W"). }

    iIntros "!>" (b v' s' t' V' V'') "(F & sV'' & I & CASE)".
    iApply ("Post" $! b v' s' t' V' V''). iFrame "F sV'' I".
    iDestruct "CASE" as "[(FACT & _ & R & Q)|(FACT & R & ? & _ & Q)]";
      [iLeft|iRight]; by iFrame.
  Qed.

  (** * CAS rules for normal protocols ---------------------------------------*)
  Lemma GPSRaw_CAS_lit
    IW (tc: time) sc vc orf or ow (vr: lit) (vw: val)
    (γ : gname) (V Vrel Vb : view) tid E E' (El: loc → coPset)
    (P: vProp) (Q Q1 Q2: time → pr_stateT Prtcl → vProp)
    (R : time → pr_stateT Prtcl → lit → vProp) :
    ↑histN ⊆ E → E' ⊆ E → (∀ l', ↑histN ⊆ El l') →
    orf = Relaxed ∨ orf = AcqRel →
    or = Relaxed ∨ or = AcqRel → ow = Relaxed ∨ ow = AcqRel →
    let Vs V1 V2 o := if decide (AcqRel ⊑ o) then V1 else V2 in
    {{{ ⊒V ∗ (if decide (AcqRel ⊑ ow) then True else △{tid} ⊒Vrel) ∗
        @{Vs V Vrel ow} P ∗
        (▷ <obj> ∀ t' s' v, ⌜sc ⊑ s' ∧ tc ⊑ t'⌝ -∗
                  (F γ t' s' v ∨ F_read γ t' s' v) -∗
                  ⌜∃ vl, v = #vl ∧ lit_comparable vr vl⌝) ∗
        @{Vs V Vrel ow}
          (∀ t' s', ⌜sc ⊑ s' ∧ tc ⊑ t'⌝ -∗
            ((if vr is LitLoc lr
              then <obj> ∀ l' : loc, ⌜l' ≠ lr⌝ -∗ ▷ F γ t' s' #l'
                      ={E,E'}=∗ ▷|={E', (El l')}=> ∃ q' C', ▷ <subj> l' p↦{q'} C'
              else emp) ∗
              (<obj> (▷ F γ t' s' #vr ={E}=∗ ▷ Q1 t' s' ∗ ▷ Q2 t' s')) ∗
              (P -∗ ▷ Q2 t' s' ={E}=∗ ∃ s'', ⌜s' ⊑ s''⌝ ∗
                  (∀ t , ⌜(t' < t)%positive⌝ -∗ ▷ GPS_Reader l t s'' vw γ ={E}=∗
                    (<obj> (▷ Q1 t' s' ={E}=∗ ▷ F_read γ t' s' #vr)) ∗
                    |={E}[E']▷=> Q t s'' ∗ ▷ F γ t s'' vw)) )
              ∧ (▷ ∀ (v: lit), ⌜lit_neq vr v⌝ -∗
                  <obj> ((F_read γ t' s' #v ={E}=∗ F_read γ t' s' #v ∗ R t' s' v) ∧
                         (F γ t' s' #v ={E}=∗ F γ t' s' #v ∗ R t' s' v)))) ∗
        ⊔{Vb} ▷ gps_inv IP IW l γ false ∗
        GPS_Reader l tc sc vc γ }}}
      CAS #l #vr vw orf or ow @ tid; E
    {{{ b (v': lit) s' (t': time) V' V'', RET #b;
        ⌜ sc ⊑ s' ∧ V ⊑ V'' ⌝
        ∗ ⊒V''
        ∗ ⊔{Vb} ▷ gps_inv IP IW l γ false
        ∗ ( (⌜ b = true ∧ v' = vr ∧ (tc < t')%positive
              ∧ ( if decide (AcqRel ⊑ ow) then
                    ( if decide (AcqRel ⊑ or) then
                        (* release-acquire CAS *) V' = V''
                      else (* release CAS: *) V'' ⊑ V' )
                  else (* relaxed write CAS *) Vrel ⊑ V' ) ⌝
            ∗ GPS_Reader l t' s' vw γ
            ∗ (if decide (AcqRel ⊑ or) then ⌜V' ⊑ V''⌝ else ▽{tid} ⊒V')
            ∗ @{V'} Q t' s')
        ∨ ( ⌜ b = false ∧ lit_neq vr v' ∧ (tc ≤ t')%positive ⌝
            ∗ GPS_Reader l t' s' #v' γ
            ∗ (if decide (AcqRel ⊑ orf) then ⊒V' else ▽{tid} ⊒V')
            ∗ @{V'} R t' s' v'
            ∗ @{Vs V Vrel ow} P ))
        }}}.
  Proof.
    iIntros (SUB1 SUB2 SUB3 ORF OR OW Vs Φ)
            "(sV & Hrel & P & Comp & VS & I & #R) Post".
    rewrite {1}GPS_Reader_eq. iDestruct "R" as (γs γl Vc ENC) "(SS' & #SN)".
    iDestruct (view_join_view_at_access' with "I") as (V0)
      "(#sV0 & I & Close)". rewrite !view_at_later.
    iDestruct "I" as (μ γs' γl' ζ tx) "(>%ENC' & >Go & >Pt & rB & rE & >rF)".
    iAssert (⌜ is_Some (ζ !! tx) ⌝)%I with "[Pt]" as %ISx.
    { clear. rewrite AtomicPtsToX_is_SomeX. by iDestruct "Pt" as %?. }
    iDestruct "rF" as %(FIN & SS & SWCon). rewrite 3!view_at_objective_iff.
    rewrite ENC in ENC'. apply encode_inj, pair_inj in ENC' as [<- <-].
    iDestruct (AtomicPtsToX_AtomicSeen_latest_1 with "Pt SN") as
      %Eqtc%map_singleton_subseteq_l.
    have Letx : (tx ≤ tc)%positive. { apply SWCon. by eexists. }

    iDestruct (gps_own_snap_singleton_sub with "Go SS'") as %Eqsc.

    iAssert (▷ ⌜ ∀ t v, no_earlier_time {[tc := (vc, Vc)]} t →
                fst <$> ζ !! t = Some v → ∃ vl : lit, v = #vl ∧
                lit_comparable vr vl⌝)%I
    with "[rB rE Comp]" as "#> %COMP {Comp}".
    { iIntros "!>" (t v Letc' Eqv). rewrite -lookup_fmap in Eqv.
      apply lookup_fmap_Some in Eqv as [[v1 V1] [Eqv1 Eqv]].
      simpl in Eqv1. subst v1.
      have Eqs := toState_lookup_state_inv μ _ _ _ Eqv.
      have Letc: (tc ≤ t)%positive.
      { apply Letc'. rewrite lookup_insert. by eexists. }
      have Letx' : (tx ≤ t)%positive by lia.
      have Les: sc ⊑ μ t. { by apply (SS _ _ _ _ Eqsc Eqs). }
      iDestruct (view_at_objectively _ V1 with "Comp") as "Comp".
      iSpecialize ("Comp" $! t (μ t) v with "[%//]").
      destruct ((cbends ζ) !! t) as [vV|] eqn:Eqtm.
      - rewrite /resBE /gps_res (big_sepM_lookup _ _ _ _ Eqtm).
        assert (vV = (v, V1)) as ->.
        { move : Eqtm => /map_filter_lookup_Some [Eqtm _]. rewrite Eqv in Eqtm.
          by inversion Eqtm. }
        rewrite decide_True; [|done]. by iDestruct ("Comp" with "[$rB//]") as %?.
      - have Eqtm2: (ζ ∖ cbends ζ) !! t = Some (v,V1)
          by apply lookup_difference_Some.
        rewrite /resD /gps_res (big_sepM_lookup _ _ _ _ Eqtm2).
        rewrite decide_True; [|done]. by iDestruct ("Comp" with "[$rE//]") as %?. }

    iApply wp_fupd.
    iApply (AtomicSeen_CASX_later _ _ _ ζ tx orf or _ _ _ Vrel true _ _ _ _ _
                E' El with "SN Pt sV Hrel"); [| | |done..|].
    { by destruct ORF as [-> | ->]. } { by destruct OR as [-> | ->]. }
    { by destruct OW as [-> | ->]. }

    iIntros (b t' v' Vr Vw V'' ζ'' ζn) "F".
    iDestruct "F" as %([Sub1 Sub2] & Eqt' & Let' & LeV & CASE).

    destruct CASE as [(-> & NEqv' & ->)|
                (-> &FR & Eqζn & Eq'' & LeVw & NEqVw & NLeVr & NEqV'' & LeVw')].
    - (* CAS fails *)
      have Lec': (tc ≤ t')%positive.
      { apply Let'. rewrite lookup_insert. by eexists. }
      have Eqt'' := (lookup_weaken _ _ _ _ Eqt' Sub2).
      have Eqst' : toState μ ζ !! t' = Some (μ t').
      { by rewrite map_lookup_imap Eqt''. }
      have Exts: sc ⊑ μ t' by apply (SS _ _ _ _ Eqsc Eqst').

      iSpecialize ("VS" $! t' (μ t') with "[%//]").
      rewrite bi.and_elim_r. iSpecialize ("VS" $! v' with "[%//]").

      iIntros "_ S1 !>". iExists ∅. iSplit; [done|].
      iIntros "_ #sV'' (SN' & Pt & sVr)".
      iApply step_fupd_intro; [done|]. iIntros "!>".
      iMod (GPSRaw_read_resources _ _ IW true (λ t s v, ⌜v = #v'⌝ ∗ R t s v')%I
                _ _ _ _ _ #v' _ _ _ Eqt'' Lec' with "[VS] rB rE")
          as "(rB & rE & _ & Rd)"; [done|..].
      { iIntros "!>".
        rewrite view_at_objective_iff right_id monPred_objectively_elim.
        have Eqv' : #v' = #v' by done. iFrame (Eqv') "VS". }

      iDestruct (gps_own_snap_singleton _ _ _ _ Eqst' with "Go") as "#GS'".
      iIntros "!>".
      iApply ("Post" $! false v' (μ t') t' Vr V'').
      iSplit; [done|]. iFrame "sV''".
      iDestruct ("Close" $! (V0 ⊔ V'') with "[] [Go Pt rB rE]") as "$".
      { rewrite -monPred_in_view_op. iFrame "sV0 sV''". }
      { rewrite assoc. iNext. iExists μ, γs, γl, _, _.
        iFrame (ENC) "Go Pt rB rE". by iPureIntro. }
      iRight. iSplit; [done|]. iFrame "P Rd". iSplitL "S1".
      { iDestruct (view_at_elim with "sV'' S1") as "S1". rewrite ENC.
        by iApply (GPS_Reader_from_seen_singleton with "GS' S1"). }
      destruct ORF as [-> | ->]; simpl; [iFrame|]. iDestruct "sVr" as %?.
      by iApply (monPred_in_mono with "sV''").

    - (* CAS succeeds *)
      simpl in LeVw'.
      set t:= (t'+1)%positive.
      have Letc: (tc ≤ t')%positive.
      { apply Let'. rewrite lookup_insert. by eexists. }
      have Letx': (tx ≤ t')%positive by lia.
      have Eqt'' := (lookup_weaken _ _ _ _ Eqt' Sub2).

      have Eqtζ : ζ !! t' = Some (#v', Vr).
      { rewrite Eqζn lookup_insert_ne in Eqt''; [done|clear;lia]. }
      have Eqst' : toState μ ζ !! t' = Some (μ t') by rewrite map_lookup_imap Eqtζ.
      have Exts: sc ⊑ μ t' by apply (SS _ _ _ _ Eqsc Eqst').

      iSpecialize ("VS" $! t' (μ t') with "[%//]"). rewrite bi.and_elim_l.
      iDestruct "VS" as "(VS0 & VS1 & VS2)".
      (* get full interpretation *)
      have Eqm': cbends ζ !! t' = Some (#v',Vr).
      { apply map_filter_lookup_Some. split; [done|].
        move => /= t1 m1 Eqm1 NEqt1 Eqf. rewrite /cell_adj /= in Eqf.
        by rewrite Eqf FR in Eqm1. }

      rewrite /resBE /gps_res (big_sepM_delete _ _ _ _ Eqm')
              (decide_True _ _ Letx') /=.
      iDestruct "rB" as "[F rB]".

      iIntros (->) "S1".
      rewrite view_at_objective_iff.
      iMod (view_at_objectively _ Vr with "VS1 [F]") as "[Q1 Q2]".
      { by iNext; iFrame. }
      iSpecialize ("VS2" with "P").
      iMod (view_at_mono_2 _ (Vs V Vrel ow ⊔ Vr) with "VS2 [$Q2]")
        as (s Exts') "VS". { solve_lat. }
      iIntros "!>". iExists ∅. iSplit; [done|].
      iIntros "(_ & _ & SY2) #sV'' [VS' sVw]".

      iMod (gps_own_insert _ _ t s with "Go") as "[Go #Gs']".
      { by rewrite map_lookup_imap FR. }

      have Ltt': (t' < t)%positive by rewrite /t; lia.
      have Lttc: (tc < t)%positive by eapply Pos.le_lt_trans; [|apply Ltt'].
      have LeVrw : Vs V Vrel ow ⊔ Vr ⊑ Vw.
      { apply lat_join_lub; [|done]. clear -OW OR LeVw' LeV. rewrite /Vs.
        destruct OW as [-> | ->]; simpl in *; [done|].
        destruct OR as [-> | ->]; simpl in *; [solve_lat|by subst]. }
      iMod (view_at_mono_2 with "VS [%//] [SY2]") as "[FR QF]"; [exact LeVrw|..].
      { iNext. iApply (view_at_mono' with "SY2");[done|].
        rewrite ENC -GPS_Reader_from_sync_singleton. by iFrame "Gs'". }
      rewrite view_at_objective_iff.
      iMod (view_at_objectively _ Vr with "FR Q1") as "Fr".
      iMod "QF" as "QF". iIntros "!> !>". iMod "QF" as "[Q F]".
      iMod ("VS'" $! ∅ with "[//]") as "(_ & SS2 & Pt & SS2')".

      iIntros "!> !>".
      iApply ("Post" $! true vr s t Vw V'').
      iSplit. { iPureIntro. split; [|done]. by etrans. }
      iFrame "sV''".
      iSplitR "Q sVw SS2"; last first.
      { iLeft. iSplit; [done|]. iFrame "Q sVw".
        iDestruct (view_at_elim with "sV'' SS2") as "SS". rewrite ENC.
        by iApply (GPS_Reader_from_seen with "Gs' SS"). }

      iApply ("Close" $! (V0 ⊔ V'')).
      { iApply monPred_in_view_op. iFrame "sV0 sV''". }
      rewrite assoc -(toState_insert μ ζ t (vw,Vw)).
      iNext. iExists _, γs, γl, _, tx.

      iDestruct (GPSRaw_CAS_resources IW γ μ ζ tx t' #vr Vr t s vw Vw
                  Letx' Ltt' FR Eqtζ Eqm' with "rB rE F Fr") as "[rB rE]"; [done|].
      rewrite -Eqζn. iFrame (ENC) "Go Pt rB rE".

      iPureIntro. rewrite Eqζn. split; last split.
      + intros t0. case (decide (t0 = t)) => [->|Neq].
        { intros _ (td & ? & ? & [??]%lookup_insert_None) s0.
          rewrite fn_lookup_insert. etrans; last apply Exts'.
          apply FIN; [done|]. exists td. split; [done|]. split; [lia|done]. }
        rewrite lookup_insert_ne; [|done]. rewrite fn_lookup_insert_ne; [|done].
        intros IS0 DS. apply FIN; [done|]. move : DS. clear.
        rewrite /disconnected_from. setoid_rewrite lookup_insert_None.
        naive_solver.
      + move => t1 t2 s1 s2. rewrite 2!map_lookup_imap.
        case (decide (t1 = t)) => [->|?];
          [rewrite lookup_insert fn_lookup_insert
          |rewrite lookup_insert_ne; last done;
          rewrite fn_lookup_insert_ne; last done];
        (case (decide (t2 = t)) => [->|?];
          [rewrite lookup_insert fn_lookup_insert
          |rewrite lookup_insert_ne; last done;
          rewrite fn_lookup_insert_ne; last done]); simpl; [naive_solver| | |].
        * intros <-%Some_inj. destruct (ζ !! t2) eqn:Eqt2; rewrite Eqt2; [|done].
          simpl. intros <-%Some_inj Ltt2. apply FIN; [by eexists|].
          (* need to use disconnected_from *)
          exists t. repeat split; [lia|done..].
        * intros Eqt1 <-%Some_inj Let1.
          etrans; last apply Exts'. eapply (SS t1 t'); [|done..|lia].
          by rewrite map_lookup_imap.
        * specialize (SS t1 t2 s1 s2). by rewrite 2!map_lookup_imap in SS.
      + intros t0. case (decide (t0 = t)) => [->|Neq].
        * intros _. change (tx ≤ t)%positive. lia.
        * rewrite lookup_insert_ne; [|done]. apply SWCon.
  Qed.

  Lemma GPSRaw_CAS_int
    IW (tc: time) sc vc orf or ow (vr: Z) (vw: val)
    (γ : gname) (V Vrel Vb : view) tid E E'
    (P: vProp) (Q Q1 Q2: time → pr_stateT Prtcl → vProp)
    (R : time → pr_stateT Prtcl → lit → vProp) :
    ↑histN ⊆ E → E' ⊆ E →
    orf = Relaxed ∨ orf = AcqRel →
    or = Relaxed ∨ or = AcqRel → ow = Relaxed ∨ ow = AcqRel →
    let Vs V1 V2 o := if decide (AcqRel ⊑ o) then V1 else V2 in
    {{{ ⊒V ∗ (if decide (AcqRel ⊑ ow) then True else △{tid} ⊒Vrel) ∗
        @{Vs V Vrel ow} P ∗
        (▷ <obj> ∀ t' s' v, ⌜sc ⊑ s' ∧ tc ⊑ t'⌝ -∗
                (F γ t' s' v ∨ F_read γ t' s' v) -∗
                ⌜∃ vl, v = #vl ∧ lit_comparable vr vl⌝) ∗
        @{Vs V Vrel ow}
          (∀ t' s', ⌜sc ⊑ s' ∧ tc ⊑ t'⌝ -∗
            ((<obj> (▷ F γ t' s' #vr ={E}=∗ ▷ Q1 t' s' ∗ ▷ Q2 t' s')) ∗
            (P -∗ ▷ Q2 t' s' ={E}=∗ ∃ s'', ⌜s' ⊑ s''⌝ ∗
                (∀ t , ⌜(t' < t)%positive⌝ -∗ ▷ GPS_Reader l t s'' vw γ ={E}=∗
                    (<obj> (▷ Q1 t' s' ={E}=∗ ▷ F_read γ t' s' #vr)) ∗
                    |={E}[E']▷=> Q t s'' ∗ ▷ F γ t s'' vw)) )
              ∧ (▷ ∀ (v: lit), ⌜lit_neq vr v⌝ -∗
                  <obj> ((F_read γ t' s' #v ={E}=∗ F_read γ t' s' #v ∗ R t' s' v) ∧
                         (F γ t' s' #v ={E}=∗ F γ t' s' #v ∗ R t' s' v)))) ∗
        ⊔{Vb} ▷ gps_inv IP IW l γ false ∗
        GPS_Reader l tc sc vc γ }}}
      CAS #l #vr vw orf or ow @ tid; E
    {{{ b (v': lit) s' (t': time) V' V'', RET #b;
        ⌜ sc ⊑ s' ∧ V ⊑ V'' ⌝
        ∗ ⊒V''
        ∗ ⊔{Vb} ▷ gps_inv IP IW l γ false
        ∗ ( (⌜ b = true ∧ v' = LitInt vr ∧ (tc < t')%positive
              ∧ ( if decide (AcqRel ⊑ ow) then
                    ( if decide (AcqRel ⊑ or) then
                        (* release-acquire CAS *) V' = V''
                      else (* release CAS: *) V'' ⊑ V' )
                  else (* relaxed write CAS *) Vrel ⊑ V' ) ⌝
            ∗ GPS_Reader l t' s' vw γ
            ∗ (if decide (AcqRel ⊑ or) then ⌜V' ⊑ V''⌝ else ▽{tid} ⊒V')
            ∗ @{V'} Q t' s')
        ∨ ( ⌜ b = false ∧ lit_neq vr v' ∧ (tc ≤ t')%positive ⌝
            ∗ GPS_Reader l t' s' #v' γ
            ∗ (if decide (AcqRel ⊑ orf) then ⊒V' else ▽{tid} ⊒V')
            ∗ @{V'} R t' s' v'
            ∗ @{Vs V Vrel ow} P )) }}}.
  Proof.
    iIntros (SUB1 SUB2 ORF OR OW Vs Φ)
            "(sV & Hrel & P & Comp & VS & I & R) Post".
    iApply (GPSRaw_CAS_lit IW tc sc vc orf or ow vr vw γ V Vrel Vb
                _ E E' (λ _, ↑histN) P Q Q1 Q2 R SUB1 SUB2
              with "[$sV $Hrel $P $Comp VS $I $R]"); [done..| |].
    { iApply (view_at_mono with "VS"); [done|].
      iIntros "VS" (t' s') "Sub". rewrite left_id. by iApply "VS". }
    iIntros "!>" (b v' s' t' V' V'') "(s & F & I & CASE)".
    iApply "Post". by iFrame.
  Qed.

  Lemma GPSRaw_CAS_live_loc
    IW (tc: time) sc vc orf or ow (lr: loc) (vw: val)
    (γ : gname) (V Vrel Vb : view) tid E E' (El: loc → coPset)
    (P: vProp) (Q Q1 Q2: time → pr_stateT Prtcl → vProp)
    (R : time → pr_stateT Prtcl → lit → vProp) :
    ↑histN ⊆ E → E' ⊆ E → (∀ l', ↑histN ⊆ El l') →
    orf = Relaxed ∨ orf = AcqRel →
    or = Relaxed ∨ or = AcqRel → ow = Relaxed ∨ ow = AcqRel →
    let Vs V1 V2 o := if decide (AcqRel ⊑ o) then V1 else V2 in
    {{{ ⊒V ∗ (if decide (AcqRel ⊑ ow) then True else △{tid} ⊒Vrel) ∗
        @{Vs V Vrel ow} P ∗
        (▷ <obj> ∀ t' s' v, ⌜sc ⊑ s' ∧ tc ⊑ t'⌝ -∗
                  (F γ t' s' v ∨ F_read γ t' s' v) -∗
                  ⌜∃ vl, v = #vl ∧ lit_comparable lr vl⌝)∗
        @{Vs V Vrel ow}
          (∀ t' s', ⌜sc ⊑ s' ∧ tc ⊑ t'⌝ -∗
            ((<obj> ∀ l' : loc, ⌜l' ≠ lr⌝ -∗ ▷ F γ t' s' #l'
                ={E,E'}=∗ ▷|={E', (El l')}=> ∃ q' C', ▷ <subj> l' p↦{q'} C') ∗
             (<obj> (▷ F γ t' s' #lr ={E}=∗ ▷ Q1 t' s' ∗ ▷ Q2 t' s')) ∗
             (P -∗ ▷ Q2 t' s' ={E}=∗ ∃ s'', ⌜s' ⊑ s''⌝ ∗
                (∀ t , ⌜(t' < t)%positive⌝ -∗ ▷ GPS_Reader l t s'' vw γ ={E}=∗
                    (<obj> (▷ Q1 t' s' ={E}=∗ ▷ F_read γ t' s' #lr)) ∗
                    |={E}[E']▷=> Q t s'' ∗ ▷ F γ t s'' vw)) )
            ∧ (▷ ∀ (v: lit), ⌜lit_neq lr v⌝ -∗
                <obj> ((F_read γ t' s' #v ={E}=∗ F_read γ t' s' #v ∗ R t' s' v) ∧
                       (F γ t' s' #v ={E}=∗ F γ t' s' #v ∗ R t' s' v)))) ∗
        ⊔{Vb} ▷ gps_inv IP IW l γ false ∗
        GPS_Reader l tc sc vc γ }}}
      CAS #l #lr vw orf or ow @ tid; E
    {{{ b (v': lit) s' (t': time) V' V'', RET #b;
        ⌜ sc ⊑ s' ∧ V ⊑ V'' ⌝
        ∗ ⊒V''
        ∗ ⊔{Vb} ▷ gps_inv IP IW l γ false
        ∗ ( (⌜ b = true ∧ v' = LitLoc lr ∧ (tc < t')%positive
              ∧ ( if decide (AcqRel ⊑ ow) then
                    ( if decide (AcqRel ⊑ or) then
                        (* release-acquire CAS *) V' = V''
                      else (* release CAS: *) V'' ⊑ V' )
                  else (* relaxed write CAS *) Vrel ⊑ V' ) ⌝
            ∗ GPS_Reader l t' s' vw γ
            ∗ (if decide (AcqRel ⊑ or) then ⌜V' ⊑ V''⌝ else ▽{tid} ⊒V')
            ∗ @{V'} Q t' s')
        ∨ ( ⌜ b = false ∧ lit_neq lr v' ∧ (tc ≤ t')%positive ⌝
            ∗ GPS_Reader l t' s' #v' γ
            ∗ (if decide (AcqRel ⊑ orf) then ⊒V' else ▽{tid} ⊒V')
            ∗ @{V'} R t' s' v'
            ∗ @{Vs V Vrel ow} P )) }}}.
  Proof.
    iIntros (SUB1 SUB2 SUB3 ORF OR OW Vs Φ)
            "(sV & Hrel & P & Comp & VS & I & R)".
    iApply (GPSRaw_CAS_lit IW tc sc vc orf or ow lr vw γ V Vrel Vb
              _ E E' El P Q Q1 Q2 R SUB1 SUB2 SUB3 ORF OR OW
              with "[$sV $Hrel $P $Comp $VS $I $R]").
  Qed.
End CAS.
