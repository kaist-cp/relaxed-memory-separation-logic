From iris.bi Require Import fractional.
From iris.proofmode Require Import proofmode.

From gpfsl.logic Require Import lifting.
From gpfsl.logic Require Import atomic_preds.
From gpfsl.gps Require Import cbends.
From gpfsl.gps Require Export model_defs.

Require Import iris.prelude.options.

Implicit Types (t : time) (v : val) (V : view) (ζ : absHist) (γ : gname).

Section GName.
  Context `{!noprolG Σ, !gpsG Σ Prtcl, !atomicG Σ} (l : loc)
          (IP : gname → interpO Σ Prtcl).
  Local Notation iProp := (iProp Σ).
  Local Notation vProp := (vProp Σ).

  Lemma GPSRaw_Init_strong_vs_gname b v s E
    (Q: time → gname → vProp) :
    l ↦ v -∗
    (∀ γl γs t V,
      gps_snap γs {[t := s]} -∗
      l sw⊒{γl} {[t := (v,V)]} ={E}=∗
      let γ := encode (γs,γl) in ▷?b (IP γ) true l γ t s v ∗ Q t γ) ={E}=∗
    ∃ t γ, ∀ IW, ▷?b (gps_inv (IP γ) IW l γ true) ∗ Q t γ.
  Proof.
    iIntros "Pts F".
    iMod (AtomicPtsToX_from_na_rel_view with "F Pts")
      as (γl t V) "(#sV & F & W & Pts)".
    set μ : time → Prtcl := λ _, s.
    set ζ : absHist := {[t := (v,V)]}.
    set χ := toState μ ζ.
    have Eqχ: χ = {[t := s]}.
    { (* TODO: map_imap singleton *)
      by rewrite /χ /ζ /toState map_imap_insert map_imap_empty. }

    iMod (gps_own_alloc χ) as (γs) "[oA oS]".
    set γ := encode (γs,γl).
    rewrite {2}Eqχ.
    iExists t, γ. iMod ("F" with "[$oS //] W") as "[I Q]".
    iIntros "!>" (IW). iDestruct (view_at_elim with "sV Q") as "$".
    iIntros "!>".
    iExists μ, γs, γl, ζ, t. iSplit; [done|]. iFrame.
    iDestruct (view_at_elim with "sV Pts") as "$".
    iSplitL "I"; last iSplit.
    - rewrite /resBE /gps_res /cbends mblock_ends_singleton.
      iApply big_sepM_singleton.
      by rewrite decide_True.
    - by rewrite /resD /gps_res /cbends mblock_ends_singleton
                  map_difference_diag big_sepM_empty.
    - iPureIntro. split; last split.
      + move => ? [? /lookup_singleton_Some[<- ?]] [td[?[? DIS]]].
        have ?: td = t by apply : anti_symm. subst td.
        by rewrite lookup_insert in DIS.
      + rewrite -/χ Eqχ.
        by move => ???? /lookup_singleton_Some[? <-] /lookup_singleton_Some[? <-].
      + by apply SWConnect_singleton.
  Qed.
End GName.

Section TwoLoc.
  Context `{!noprolG Σ, !gpsG Σ Prtcl1, !gpsG Σ Prtcl2, !atomicG Σ}
          (l1 l2 : loc)
          (IP1 : gname → interpO Σ Prtcl1)
          (IP2 : gname → interpO Σ Prtcl2).
  Local Notation iProp := (iProp Σ).
  Local Notation vProp := (vProp Σ).

  Lemma GPSRaw_Init_strong_vs_2 b v1 v2 (s1: Prtcl1) (s2: Prtcl2) E
    (Q: time → time → gname → gname → vProp) :
    l1 ↦ v1 -∗ l2 ↦ v2 -∗
    (∀ (γl1 γs1 : gname) t1 V1 (γl2 γs2 : gname) t2 V2,
      gps_snap γs1 {[t1 := s1]} -∗
      l1 sw⊒{γl1} {[t1 := (v1,V1)]} -∗
      gps_snap γs2 {[t2 := s2]} -∗
      l2 sw⊒{γl2} {[t2 := (v2,V2)]} ={E}=∗
        let γ1 := encode (γs1,γl1) in let γ2 := encode (γs2,γl2) in
        ▷?b (IP1 γ2) true l1 γ1 t1 s1 v1 ∗
        ▷?b (IP2 γ1) true l2 γ2 t2 s2 v2 ∗
            Q t1 t2 γ1 γ2)
    ={E}=∗ ∃ (t1 t2 : time) (γ1 γ2 : gname), ∀ IW1 IW2,
        ▷?b (gps_inv (IP1 γ2) IW1 l1 γ1 true) ∗
        ▷?b (gps_inv (IP2 γ1) IW2 l2 γ2 true) ∗
        Q t1 t2 γ1 γ2.
  Proof.
    iIntros "Pts1 Pts2 F". iCombine "Pts2 F" as "P2F".
    iMod (AtomicPtsToX_from_na_rel_view with "P2F Pts1")
      as (γl1 t1 V1) "(#sV1 & [Pts2 F] & W1 & Pts1)".
    iAssert (@{V1} (⊒V1 ∗ l2 ↦ v2))%I with "[Pts2]" as "Pts2".
    { iSplit; [by iPureIntro|iFrame]. }
    rewrite (bi.wand_elim_l' _ _ _ (AtomicPtsToX_from_na_rel_view l2 v2 _)).
    iMod "Pts2" as (γl2 t2 V2) "(%LeV2 & %LeV1 & W2 & Pts2)".
    rewrite 2!view_at_view_at.
    assert (V1 = V2) as <-. { by apply : (anti_symm (⊑)). }
    set μ1 : time → Prtcl1 := λ _, s1.
    set ζ1 : absHist := {[t1 := (v1,V1)]}.
    set χ1 := toState μ1 ζ1.
    set μ2 : time → Prtcl2 := λ _, s2.
    set ζ2 : absHist := {[t2 := (v2,V1)]}.
    set χ2 := toState μ2 ζ2.
    have Eqχ1: χ1 = {[t1 := s1]}.
    { (* TODO: map_imap singleton *)
      by rewrite /χ1 /ζ1 /toState map_imap_insert map_imap_empty. }
    have Eqχ2: χ2 = {[t2 := s2]}.
    { (* TODO: map_imap singleton *)
      by rewrite /χ2 /ζ2 /toState map_imap_insert map_imap_empty. }

    iMod (gps_own_alloc χ1) as (γs1) "[oA1 oS1]".
    iMod (gps_own_alloc χ2) as (γs2) "[oA2 oS2]".
    set γ1 := encode (γs1,γl1).
    set γ2 := encode (γs2,γl2).
    rewrite {2}Eqχ1 {2}Eqχ2.
    iExists t1, t2, γ1, γ2.
    iMod ("F" with "[$oS1 //] W1 [$oS2 //] [$W2]") as "(I1 & I2 & Q)".
    iIntros "!>" (IW1 IW2). iDestruct (view_at_elim with "sV1 Q") as "$".
    iSplitL "Pts1 oA1 I1"; iIntros "!>".
    - iExists μ1, γs1, γl1, ζ1, t1. iSplit; [done|]. iFrame.
      iDestruct (view_at_elim with "sV1 Pts1") as "$".
      iSplitL "I1"; last iSplit.
      + rewrite /resBE /gps_res /cbends mblock_ends_singleton.
        iApply big_sepM_singleton. by rewrite decide_True.
      + by rewrite /resD /gps_res /cbends mblock_ends_singleton
                    map_difference_diag big_sepM_empty.
      + iPureIntro. split; last split.
        * move => ? [? /lookup_singleton_Some[<- ?]] [td[?[? DIS]]].
          have ?: td = t1 by apply : anti_symm. subst td.
          by rewrite lookup_insert in DIS.
        * rewrite -/χ1 Eqχ1.
          by move => ???? /lookup_singleton_Some[? <-] /lookup_singleton_Some[? <-].
        * by apply SWConnect_singleton.
    - iExists μ2, γs2, γl2, ζ2, t2. iSplit; [done|]. iFrame.
      iDestruct (view_at_elim with "[sV1] Pts2") as "$".
      { by iApply (monPred_in_mono with "sV1"). }
      iSplitL "I2"; last iSplit.
      + rewrite /resBE /gps_res /cbends mblock_ends_singleton.
        iApply big_sepM_singleton. by rewrite decide_True.
      + by rewrite /resD /gps_res /cbends mblock_ends_singleton
                    map_difference_diag big_sepM_empty.
      + iPureIntro. split; last split.
        * move => ? [? /lookup_singleton_Some[<- ?]] [td[?[? DIS]]].
          have ?: td = t2 by apply : anti_symm. subst td.
          by rewrite lookup_insert in DIS.
        * rewrite -/χ2 Eqχ2.
          by move => ???? /lookup_singleton_Some[? <-] /lookup_singleton_Some[? <-].
        * by apply SWConnect_singleton.
  Qed.
End TwoLoc.


Section RawRules.
  Context `{!noprolG Σ, !gpsG Σ Prtcl, !atomicG Σ}
          (IP : interpO Σ Prtcl) (l : loc).
  Local Notation iProp := (iProp Σ).
  Local Notation vProp := (vProp Σ).
  Implicit Types
           (s : pr_stateT Prtcl) (χ : stateT Prtcl)
           (μ : time → pr_stateT Prtcl).

  Notation F := (IP true l).
  Notation F_read := (IP false l).

  (** INIT *)
  Lemma GPSRaw_Init_vs IW b v s bs :
    l ↦ v -∗
    (∀ t γ, ▷?b F γ t s v) ==∗
    ∃ t (γ γs γl : gname),
      ▷?b (gps_inv IP IW l γ bs) ∗
      ⌜ γ = encode (γs,γl) ⌝ ∗
      gps_snap γs {[t := s]} ∗
      ∃ V, let ζ : absHist := {[t := (v,V)]} in
      if bs then l sw⊒{γl} ζ else l sy⊒{γl} ζ.
  Proof.
    iIntros "Pts F".
    iMod (AtomicPtsToX_from_na_rel with "F Pts") as (γl t V) "(#sV & F & W & Pts)".
    set μ : time → Prtcl := λ _, s.
    set ζ : absHist := {[t := (v,V)]}.
    set χ := toState μ ζ.
    have Eqχ: χ = {[t := s]}.
    { (* TODO: map_imap singleton *)
      by rewrite /χ /ζ /toState map_imap_insert map_imap_empty. }

    iMod (gps_own_alloc χ) as (γs) "[oA #oS]".
    set γ := encode (γs,γl).
    rewrite {2}Eqχ. iExists t, γ, γs, γl.
    have EQ: γ = encode (γs, γl) by done.
    iFrame (EQ).
    iAssert ((▷?b resBE IP IW l γ μ ζ t) ∗ resD IP IW l γ μ ζ t ∗
              ⌜FinalInv μ ζ t ∧ stsorted (toState μ ζ) ∧ SWConnect ζ t⌝)%I with "[F]"
      as "(F & Fr & (%&%&%))".
    { iSplitL "F"; last iSplit.
      - iNext. rewrite /resBE /gps_res /cbends mblock_ends_singleton.
        iApply big_sepM_singleton. rewrite decide_True //.
        iApply ("F" $! t γ).
      - by rewrite /resD /gps_res /cbends mblock_ends_singleton
                    map_difference_diag big_sepM_empty.
      - iPureIntro. split; last split.
        * move => ? [? /lookup_singleton_Some[<- ?]] [td[?[? DIS]]].
          have ?: td = t by apply : anti_symm. subst td.
          by rewrite lookup_insert in DIS.
        * rewrite -/χ Eqχ.
          by move => ???? /lookup_singleton_Some[? <-] /lookup_singleton_Some[? <-].
        * by apply SWConnect_singleton. }
    iIntros "!>". rewrite -Eqχ. iFrame "oS". destruct bs.
    - iSplitR "W".
      + iExists μ, γs, γl, ζ, t. iSplit; [done|]. iNext. by iFrame.
      + iExists _. by iFrame.
    - iDestruct (AtomicPtsToX_SW_to_CON_2 with "Pts W") as "[Pts SY]".
      iSplitR "SY".
      + iExists μ, γs, γl, ζ, t. iSplit; [done|].
        iNext. iFrame. iPureIntro. do 2 (split; [done|]).
        by move => ? [?/lookup_singleton_Some [->]].
      + iExists _. by iFrame.
  Qed.

  Lemma GPSRaw_Init_strong_vs_open IW b v s (P Q: time → gname → vProp) E :
    l ↦ v -∗
    (∀ γl γs t V,
      gps_snap γs {[t := s]} -∗
      l sw⊒{γl} {[t := (v,V)]} -∗
      let γ := encode (γs,γl) in
      (<obj> P t γ) ={E}=∗ ▷?b F γ t s v ∗ Q t γ)
    ={E}=∗ ∃ t γ,
    |={E}=> ((<obj> P t γ) ={E}=∗ ▷?b (gps_inv IP IW l γ true) ∗ Q t γ).
  Proof.
    iIntros "Pts F".
    iMod (AtomicPtsToX_from_na_rel_view with "F Pts")
      as (γl t V) "(#sV & F & W & Pts)".
    set μ : time → Prtcl := λ _, s.
    set ζ : absHist := {[t := (v,V)]}.
    set χ := toState μ ζ.
    have Eqχ: χ = {[t := s]}.
    { (* TODO: map_imap singleton *)
      by rewrite /χ /ζ /toState map_imap_insert map_imap_empty. }

    iMod (gps_own_alloc χ) as (γs) "[oA oS]".
    set γ := encode (γs,γl).
    rewrite {2}Eqχ.
    iExists t, γ. iIntros "!> !> P".
    iMod ("F" with "[$oS //] W [P]") as "[I Q]".
    { rewrite view_at_objective_iff. by iFrame. }
    iIntros "!>". iDestruct (view_at_elim with "sV Q") as "$".
    iIntros "!>".
    iExists μ, γs, γl, ζ, t. iSplit; [done|]. iFrame.
    iDestruct (view_at_elim with "sV Pts") as "$".
    iSplitL "I"; last iSplit.
    - rewrite /resBE /gps_res /cbends mblock_ends_singleton.
      iApply big_sepM_singleton.
      by rewrite decide_True.
    - by rewrite /resD /gps_res /cbends mblock_ends_singleton
                  map_difference_diag big_sepM_empty.
    - iPureIntro. split; last split.
      + move => ? [? /lookup_singleton_Some[<- ?]] [td[?[? DIS]]].
        have ?: td = t by apply : anti_symm. subst td.
        by rewrite lookup_insert in DIS.
      + rewrite -/χ Eqχ.
        by move => ???? /lookup_singleton_Some[? <-] /lookup_singleton_Some[? <-].
      + by apply SWConnect_singleton.
  Qed.

  Lemma GPSRaw_Init_strong_vs IW b v s
    (Q: time → gname → vProp) E :
    l ↦ v -∗
    (∀ γl γs t V,
      gps_snap γs {[t := s]} -∗
      l sw⊒{γl} {[t := (v,V)]} ={E}=∗
      let γ := encode (γs,γl) in ▷?b F γ t s v ∗ Q t γ)
    ={E}=∗ ∃ t γ, (▷?b (gps_inv IP IW l γ true) ∗ Q t γ).
  Proof.
    iIntros "P F".
    iMod (GPSRaw_Init_strong_vs_gname _ (λ _, IP) b _ s _ Q with "P F")
      as (t γ) "I".
    iDestruct ("I" $! IW) as "[I Q]".
    iExists t, γ. by iFrame.
  Qed.
End RawRules.
