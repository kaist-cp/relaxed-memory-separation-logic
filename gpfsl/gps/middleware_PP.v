From iris.proofmode Require Import proofmode.

From gpfsl.base_logic Require Import iwp na.
From gpfsl.logic Require Export lifting proofmode.
From gpfsl.logic Require Import atomic_preds.
From gpfsl.gps Require Export model_defs.
From gpfsl.gps Require Import model.
From gpfsl.logic Require Export relacq.

Require Import iris.prelude.options.

Implicit Types (t : time) (v : val) (V : view) (E : coPset) (q: Qp) (ζ : absHist).

Section PP.
  Context `{!noprolG Σ, !gpsG Σ Prtcl, !atomicG Σ}
          (IP : interpO Σ Prtcl) (l : loc).
  Local Notation iProp := (iProp Σ).
  Local Notation vProp := (vProp Σ).

  Implicit Types (s : pr_stateT Prtcl) (χ : stateT Prtcl).

  Notation F := (IP true l).        (* full interp *)
  Notation F_read := (IP false l).  (* read interp *)

  Definition GPS_PPInv_def (γ : gname) : vProp :=
    gps_inv IP (λ _ _ _ _ _, True)%I l γ false.
  Definition GPS_PPInv_aux : seal (@GPS_PPInv_def). Proof. by eexists. Qed.
  Definition GPS_PPInv := unseal (@GPS_PPInv_aux).
  Definition GPS_PPInv_eq : @GPS_PPInv = _ := seal_eq _.

  Lemma GPS_Readers_agree t1 t2 s1 s2 v1 v2 γ Vb E:
    GPS_Reader l t1 s1 v1 γ -∗ GPS_Reader l t2 s2 v2 γ -∗
    (⊒Vb → ▷ GPS_PPInv γ) ={E}=∗
    (⊒Vb → ▷ GPS_PPInv γ) ∗ ⌜(t1 ⊑ t2 → s1 ⊑ s2) ∧ (t2 ⊑ t1 → s2 ⊑ s1)⌝.
  Proof.
    rewrite GPS_PPInv_eq -view_join_unfold.
    apply : GPS_Readers_agree.
  Qed.

  Lemma GPS_PPInv_own_loc_prim b γ :
    ▷?b GPS_PPInv γ -∗ ∃ C, ▷?b own_loc_prim l 1 C.
  Proof.
    rewrite GPS_PPInv_eq /GPS_PPInv_def gps_inv_own_loc_prim.
    iDestruct 1 as (C) "?". iExists C. iNext. by iFrame.
  Qed.

  Lemma GPS_PPInv_dealloc b γ E (SUB: ↑histN ⊆ E):
    ⎡ hist_inv ⎤ -∗
    ▷?b GPS_PPInv γ ={E}=∗ ∃ t s v, l ↦ v ∗ ▷?b F γ t s v.
  Proof. rewrite GPS_PPInv_eq. by apply : GPSRaw_dealloc. Qed.

  Lemma GPS_PPRaw_Init_vs b v s:
    l ↦ v -∗
    (∀ t γ, ▷?b F γ t s v) ==∗
    ∃ γ t, GPS_Reader l t s v γ ∗ ▷?b GPS_PPInv γ.
  Proof.
    iIntros "P F".
    iMod (GPSRaw_Init_vs IP _ _ _ v s false with "P F")
      as (t γ γs γl) "(I & %ENC & SS & %V & SY)".
    iIntros "!>". iExists γ, t.
    rewrite GPS_PPInv_eq. iFrame "I". rewrite ENC.
    iApply (GPS_Reader_from_sync_singleton with "SS SY").
  Qed.

  Lemma GPS_PPRaw_Init b v s E tid :
    ↑histN ⊆ E →
    {{{ l ↦ ? ∗ (∀ t γ, ▷?b F γ t s v) }}}
      #l <- v @ tid; E
    {{{ γ t, RET #☠; GPS_Reader l t s v γ ∗ ▷?b GPS_PPInv γ }}}.
  Proof.
    iIntros (? Φ) "(own & F) Post". iApply wp_fupd. wp_write.
    iMod (GPS_PPRaw_Init_vs with "own F") as (γ t) "?". by iApply "Post".
  Qed.

  Lemma GPS_PPRaw_Read R o t s v γ tid Vb E:
    ↑histN ⊆ E → o = Relaxed ∨ o = AcqRel →
    {{{ GPS_Reader l t s v γ ∗ (⊒Vb → ▷ GPS_PPInv γ) ∗
        (▷ ∀ t' s' v', ⌜s ⊑ s' ∧ t ⊑ t'⌝ -∗
            <obj> ((F_read γ t' s' v' ={E}=∗ F_read γ t' s' v' ∗ R t' s' v') ∧
                  (F γ t' s' v' ={E}=∗ F γ t' s' v' ∗ R t' s' v'))) }}}
      Read o #l @ tid; E
    {{{ t' s' v', RET v'; ⌜s ⊑ s' ∧ t ⊑ t'⌝
        ∗ GPS_Reader l t' s' v' γ ∗ (⊒Vb → ▷ GPS_PPInv γ)
        ∗ if (decide (AcqRel ⊑ o)) then R t' s' v'
                                    else ▽{tid} R t' s' v' }}}.
  Proof.
    iIntros (SUB OR Φ) "(R & I & D) Post".
    (* TODO: lemma *)
    iAssert (⌜ ∃ (γs γl : gname), γ = encode(γs,γl) ⌝)%I as %(γs & γl & ENC).
    { rewrite GPS_Reader_eq. iDestruct "R" as (??? ENC) "?".
      iPureIntro. by do 2 eexists. }
    iApply (GPSRaw_Read_ex IP l _ R R t 1%Qp ∅ ∅ t s _ o γ _ _ false _ E _
                SUB OR ENC with "[$R I D]").
    { rewrite -view_join_unfold GPS_PPInv_eq.
      iFrame "I". iSplitL; [|eauto].
      iIntros "!> !>" (???) "I". iSpecialize ("D" with "I").
      iApply (monPred_objectively_elim with "D"). }
    iIntros "!>" (t' s' v') "(Lt & I & _ & R & R')".
    iApply "Post". iFrame. rewrite -view_join_unfold GPS_PPInv_eq. by iFrame.
  Qed.

  Lemma GPS_PPRaw_Write o t v v' s s' γ Vb tid E (FIN: final_st s'):
    ↑histN ⊆ E → o = Relaxed ∨ o = AcqRel →
    let VS : vProp := (∀ t' : time, ⌜(t < t')%positive⌝ -∗
                        GPS_Reader l t' s' v' γ ={E}=∗ F γ t' s' v')%I in
    {{{ GPS_Reader l t s v γ
        ∗ (⊒Vb → ▷ GPS_PPInv γ)
        ∗ ▷ if decide (AcqRel ⊑ o) then VS else △{tid} VS }}}
      Write o #l v' @ tid; E
    {{{ t', RET #☠; GPS_Reader l t' s' v' γ ∗ (⊒Vb → ▷ GPS_PPInv γ) }}}.
  Proof.
    iIntros (SUB OW VS Φ) "(R & I & VS) Post".
    rewrite -{1}view_join_unfold GPS_PPInv_eq.
    iApply wp_fupd. destruct OW as [-> | ->]; simpl.
    - iMod (rel_later_intro with "VS") as "VS".
      iApply (wp_rel_revert_view_at with "VS").
      iIntros (Vrel) "sVrel VS sV".
      iApply (GPSRaw_Write IP l _ t s v _ v' s' γ Vrel Vrel Vb E _
                FIN SUB with "[$sV $I $R sVrel]"); [by left|iFrame "sVrel"|..].
      iIntros "!>" (t' V' V'') "(F & sV'' & sV' & I & #RF)". simpl.
      iDestruct "F" as %(Lt' & LeV'' & NEqV'' & NLeV' & LeV1 & LeV2).
      iAssert (@{V'} |={E}=> F γ t' s' v')%I with "[VS RF]" as ">F".
      { iApply (view_at_mono' with "VS"); [done|].
        iApply (view_at_mono with "RF"); [done|]. rewrite /VS.
        iIntros "R VS". by iApply ("VS" with "[//] R"). }
      iIntros "!>". iApply ("Post" $! t'). iSplitR "I F".
      + iApply (view_at_elim with "sV' RF").
      + rewrite -view_join_unfold. iApply ("I" with "F").
    - iDestruct (view_at_intro with "VS") as (V) "[#sV VS]".
      iApply (GPSRaw_Write IP l _ t s v _ v' s' γ V V Vb E _
                FIN SUB with "[$sV $I $R]"); [by right|simpl; done|..].
      iIntros "!>" (t' V' V'') "(F & sV'' & sV' & I & #RF)". simpl.
      iDestruct "F" as %(Lt' & LeV'' & NEqV'' & NLeV' & ->).
      iAssert (@{V'} |={E}=> F γ t' s' v')%I with "[VS RF]" as ">F".
      { iApply (view_at_mono' with "VS"); [done|].
        iApply (view_at_mono with "RF"); [done|]. rewrite /VS.
        iIntros "R VS". by iApply ("VS" with "[//] R"). }
      iIntros "!>". iApply ("Post" $! t'). iSplitR "I F".
      + iApply (view_at_elim with "sV' RF").
      + rewrite -view_join_unfold. iApply ("I" with "F").
  Qed.

  Lemma GPS_PPRaw_CAS_int
    orf or ow v (vr: Z) (vw: val) t s P Q Q1 Q2 R γ tid Vb E :
    ↑histN ⊆ E →
    orf = Relaxed ∨ orf = AcqRel →
    or = Relaxed ∨ or = AcqRel → ow = Relaxed ∨ ow = AcqRel →
    let VSC : vProp :=
      (<obj> ∀ t' s' v', ⌜s ⊑ s' ∧ t ⊑ t'⌝ -∗
                    (F γ t' s' v' ∨ F_read γ t' s' v') -∗
                    ⌜∃ vl, v' = #vl ∧ lit_comparable vr vl⌝)%I in
    let VS : vProp :=
      (∀ t' s', ⌜s ⊑ s' ∧ t ⊑ t'⌝ -∗
        ((<obj> (▷ F γ t' s' #vr ={E}=∗ ▷ Q1 t' s' ∗ ▷ Q2 t' s')) ∗
          (P -∗ ▷ Q2 t' s' ={E}=∗ ∃ s'', ⌜s' ⊑ s''⌝ ∗
            (∀ t , ⌜(t' < t)%positive⌝ -∗ ▷ (GPS_Reader l t s'' vw γ) ={E}=∗
                (<obj> (▷ Q1 t' s' ={E}=∗ ▷ F_read γ t' s' #vr)) ∗
                |={E}▷=> Q t s'' ∗ ▷ F γ t s'' vw)) ) ∧
        (▷ ∀ (v: lit), ⌜lit_neq vr v⌝ -∗
            <obj> ((F_read γ t' s' #v ={E}=∗ F_read γ t' s' #v ∗ R t' s' v) ∧
                    (F γ t' s' #v ={E}=∗ F γ t' s' #v ∗ R t' s' v))))%I in
    {{{ GPS_Reader l t s v γ ∗ (⊒Vb → ▷ GPS_PPInv γ)
        ∗ ▷ VSC
        ∗ (if decide (AcqRel ⊑ ow) then VS else △{tid} VS)
        ∗ (if decide (AcqRel ⊑ ow) then P  else △{tid} P )  }}}
      CAS #l #vr vw orf or ow @ tid; E
    {{{ (b: bool) t' s' (v': lit), RET #b;
        (⊒Vb → ▷ GPS_PPInv γ) ∗ ⌜s ⊑ s'⌝
        ∗ ( (⌜b = true  ∧ v' = LitInt vr ∧ (t < t')%positive⌝
              ∗ GPS_Reader l t' s' vw γ
              ∗ if decide (AcqRel ⊑ or) then Q t' s' else ▽{tid} Q t' s')
          ∨ (⌜b = false ∧ lit_neq vr v' ∧ (t ≤ t')%positive⌝
              ∗ GPS_Reader l t' s' #v' γ
              ∗ (if decide (AcqRel ⊑ orf) then R t' s' v' else ▽{tid} (R t' s' v'))
              ∗ (if decide (AcqRel ⊑ ow) then P  else △{tid} P ))) }}}.
  Proof.
    iIntros (SUB ORF OR OW VSC VSW Φ) "(R & I & Comp & VS & P) Post".
    rewrite -{1}view_join_unfold GPS_PPInv_eq.
    iCombine "P VS" as "PVS".
    destruct OW as [-> | ->]; simpl.
    - rewrite rel_sep. iApply (wp_rel_revert_view_at with "PVS").
      iIntros (Vrel) "#Hrel [P VS] #sVrel".
      iDestruct (view_at_intro True%I with "[//]") as (V) "[#sV _]".
      iApply (GPSRaw_CAS_int IP l (λ _ _ _ _ _, True)%I t s v orf or _ vr vw
                  γ _ Vrel Vb _ _ E P Q Q1 Q2 R SUB
                with "[$sV Hrel P $Comp VS $I $R]"); [done..|by left| |].
      { simpl. iFrame "Hrel P VS". } clear VSC VSW.
      iIntros "!>" (b v' s' t' V' V'') "([%Lets %LeV] & #sV'' & I & CASE)".
      rewrite view_join_unfold.
      iApply ("Post" $! b t' s' v'). iFrame (Lets) "I".
      iDestruct "CASE" as "[(F & GR & sVw & Q)|(F & GR & sVr & R' & P)]"; simpl.
      + iLeft. iDestruct "F" as %(? & ? & ? & LeV').
        iSplit; [done|]. iFrame "GR". destruct OR as [-> | ->]; simpl.
        * iApply (acq_at_intro with "sVw Q").
        * iApply (view_at_elim with "[sV'' sVw] Q").
          iDestruct "sVw" as %?. by iApply (monPred_in_mono with "sV''").
      + iRight. iFrame "F GR". iDestruct (rel_at_intro with "Hrel P") as "$".
        destruct ORF as [-> | ->]; simpl.
        * iApply (acq_at_intro with "sVr R'").
        * iApply (view_at_elim with "sVr R'").

    - iDestruct (view_at_intro with "PVS") as (V) "[#sV [P VS]]".
      iApply (GPSRaw_CAS_int IP l (λ _ _ _ _ _, True)%I t s v orf or _ vr vw
                γ _ ∅ Vb _ _ E P Q Q1 Q2 R SUB with "[$sV P $Comp VS $I $R]");
        [done..|by right| |].
      { simpl. iFrame "P VS". } clear VSC VSW.
      iIntros "!>" (b v' s' t' V' V'') "([%Lets %LeV] & #sV'' & I & CASE)".
      rewrite view_join_unfold.
      iApply ("Post" $! b t' s' v'). iFrame (Lets) "I".
      iDestruct "CASE" as "[(F & GR & sVw & Q)|(F & GR & sVr & R' & P)]"; simpl.
      + iLeft. iDestruct "F" as %(? & ? & ? & LeV').
        iSplit; [done|]. iFrame "GR". destruct OR as [-> | ->]; simpl.
        * iApply (acq_at_intro with "sVw Q").
        * iApply (view_at_elim with "[sV'' sVw] Q").
          iDestruct "sVw" as %?. by iApply (monPred_in_mono with "sV''").
      + iRight. iFrame "F GR". iDestruct (view_at_elim with "sV P") as "$".
        destruct ORF as [-> | ->]; simpl.
        * iApply (acq_at_intro with "sVr R'").
        * iApply (view_at_elim with "sVr R'").
  Qed.

  Lemma GPS_PPRaw_CAS_live_loc
    orf or ow v (lr: loc) (vw: val) t s P Q Q1 Q2 R γ tid Vb
    E (El: loc → coPset) (SUBl: ∀ l', ↑histN ⊆ El l') :
    ↑histN ⊆ E →
    orf = Relaxed ∨ orf = AcqRel →
    or = Relaxed ∨ or = AcqRel → ow = Relaxed ∨ ow = AcqRel →
    let VSC : vProp :=
      (<obj> ∀ t' s' v', ⌜s ⊑ s' ∧ t ⊑ t'⌝ -∗
                    (F γ t' s' v' ∨ F_read γ t' s' v') -∗
                    ⌜∃ vl, v' = #vl ∧ lit_comparable lr vl⌝)%I in
    let VS : vProp :=
      (∀ t' s', ⌜s ⊑ s' ∧ t ⊑ t'⌝ -∗
        ((<obj> ∀ l' : loc, ⌜l' ≠ lr⌝ -∗ ▷ F γ t' s' #l' -∗
                ▷ |={E, El l'}=> ∃ q' C', ▷ <subj> own_loc_prim l' q' C') ∗
          (<obj> (▷ F γ t' s' #lr ={E}=∗ ▷ Q1 t' s' ∗ ▷ Q2 t' s')) ∗
          (P -∗ ▷ Q2 t' s' ={E}=∗ ∃ s'', ⌜s' ⊑ s''⌝ ∗
            (∀ t , ⌜(t' < t)%positive⌝ -∗ ▷ GPS_Reader l t s'' vw γ ={E}=∗
                (<obj> (▷ Q1 t' s' ={E}=∗ ▷ F_read γ t' s' #lr)) ∗
                |={E}▷=> Q t s'' ∗ ▷ F γ t s'' vw)) ) ∧
        (▷ ∀ (v: lit), ⌜lit_neq lr v⌝ -∗
            <obj> ((F_read γ t' s' #v ={E}=∗ F_read γ t' s' #v ∗ R t' s' v) ∧
                    (F γ t' s' #v ={E}=∗ F γ t' s' #v ∗ R t' s' v))))%I in
    {{{ GPS_Reader l t s v γ ∗ (⊒Vb → ▷ GPS_PPInv γ)
        ∗ ▷ VSC
        ∗ (if decide (AcqRel ⊑ ow) then VS else △{tid} VS)
        ∗ (if decide (AcqRel ⊑ ow) then P  else △{tid} P )  }}}
      CAS #l #lr vw orf or ow @ tid; E
    {{{ (b: bool) t' s' (v': lit), RET #b;
        (⊒Vb → ▷ GPS_PPInv γ) ∗ ⌜s ⊑ s'⌝
        ∗ ( (⌜b = true  ∧ v' = LitLoc lr ∧ (t < t')%positive⌝
              ∗ GPS_Reader l t' s' vw γ
              ∗ if decide (AcqRel ⊑ or) then Q t' s' else ▽{tid} Q t' s')
          ∨ (⌜b = false ∧ lit_neq lr v' ∧ (t ≤ t')%positive⌝
              ∗ GPS_Reader l t' s' #v' γ
              ∗ (if decide (AcqRel ⊑ orf) then R t' s' v' else ▽{tid} (R t' s' v'))
              ∗ (if decide (AcqRel ⊑ ow)  then P          else △{tid} P ))) }}}.
  Proof.
    iIntros (SUB ORF OR OW VSC VSW Φ) "(R & I & Comp & VS & P) Post".
    rewrite -{1}view_join_unfold GPS_PPInv_eq.
    iCombine "P VS" as "PVS".
    destruct OW as [-> | ->]; simpl.
    - rewrite rel_sep. iApply (wp_rel_revert_view_at with "PVS").
      iIntros (Vrel) "#Hrel [P VS] #sVrel".
      iDestruct (view_at_intro True%I with "[//]") as (V) "[#sV _]".
      iApply (GPSRaw_CAS_live_loc IP l (λ _ _ _ _ _, True)%I t s v orf or _
                lr vw γ V Vrel Vb _ _ E El P Q Q1 Q2 R SUB
              with "[$sV Hrel P Comp VS $I $R]"); [done..|by left| |].
      { simpl. iFrame "Hrel P Comp".
        iApply (view_at_mono with "VS"); [done|]. rewrite /VSW.
        iIntros "VS". iIntros (t' s') "Le". iSpecialize ("VS" with "Le").
        iSplit; [rewrite bi.and_elim_l|by rewrite bi.and_elim_r].
        iDestruct "VS" as "[VS1 $]". iIntros "!>".
        rewrite monPred_objectively_elim.
        iIntros (l') "NE F !>". iApply ("VS1" with "NE F"). } clear VSC VSW.
        iIntros "!>" (b v' s' t' V' V'') "([%Lets %LeV] & #sV'' & I & CASE)".
        rewrite view_join_unfold.
        iApply ("Post" $! b t' s' v'). iFrame (Lets) "I".
        iDestruct "CASE" as "[(F & GR & sVw & Q)|(F & GR & sVr & R' & P)]"; simpl.
        + iLeft. iDestruct "F" as %(? & ? & ? & LeV').
          iSplit; [done|]. iFrame "GR". destruct OR as [-> | ->]; simpl.
          * iApply (acq_at_intro with "sVw Q").
          * iApply (view_at_elim with "[sV'' sVw] Q").
            iDestruct "sVw" as %?. by iApply (monPred_in_mono with "sV''").
        + iRight. iFrame "F GR". iDestruct (rel_at_intro with "Hrel P") as "$".
          destruct ORF as [-> | ->]; simpl.
          * iApply (acq_at_intro with "sVr R'").
          * iApply (view_at_elim with "sVr R'").

    - iDestruct (view_at_intro with "PVS") as (V) "[#sV [P VS]]".
      iApply (GPSRaw_CAS_live_loc IP l (λ _ _ _ _ _, True)%I t s v orf or _
                lr vw γ V ∅ Vb _ _ E El P Q Q1 Q2 R SUB
              with "[$sV P Comp VS $I $R]"); [done..|by right| |].
      { simpl. iSplitR; [done|]. iFrame "P Comp".
        iApply (view_at_mono with "VS"); [done|]. rewrite /VSW.
        iIntros "VS". iIntros (t' s') "Le". iSpecialize ("VS" with "Le").
        iSplit; [rewrite bi.and_elim_l|by rewrite bi.and_elim_r].
        iDestruct "VS" as "[VS1 $]". iIntros "!>".
        rewrite monPred_objectively_elim.
        iIntros (l') "NE F !>". iApply ("VS1" with "NE F"). } clear VSC VSW.
        iIntros "!>" (b v' s' t' V' V'') "([%Lets %LeV] & #sV'' & I & CASE)".
        rewrite view_join_unfold.
        iApply ("Post" $! b t' s' v'). iFrame (Lets) "I".
        iDestruct "CASE" as "[(F & GR & sVw & Q)|(F & GR & sVr & R' & P)]"; simpl.
        + iLeft. iDestruct "F" as %(? & ? & ? & LeV').
          iSplit; [done|]. iFrame "GR". destruct OR as [-> | ->]; simpl.
          * iApply (acq_at_intro with "sVw Q").
          * iApply (view_at_elim with "[sV'' sVw] Q").
            iDestruct "sVw" as %?. by iApply (monPred_in_mono with "sV''").
        + iRight. iFrame "F GR". iDestruct (view_at_elim with "sV P") as "$".
          destruct ORF as [-> | ->]; simpl.
          * iApply (acq_at_intro with "sVr R'").
          * iApply (view_at_elim with "sVr R'").
  Qed.

  Lemma GPS_PPRaw_CAS_live_loc_simple
    orf or ow v (lr: loc) (vw: val) t s P Q Q1 Q2 R γ tid Vb E :
    ↑histN ⊆ E →
    orf = Relaxed ∨ orf = AcqRel →
    or = Relaxed ∨ or = AcqRel → ow = Relaxed ∨ ow = AcqRel →
    let VSC : vProp :=
      (<obj> ∀ t' s' v', ⌜s ⊑ s' ∧ t ⊑ t'⌝ -∗
                    (F γ t' s' v' ∨ F_read γ t' s' v') -∗
                    ⌜∃ vl, v' = #vl ∧ lit_comparable lr vl⌝)%I in
    let VS : vProp :=
      (∀ t' s', ⌜s ⊑ s' ∧ t ⊑ t'⌝ -∗
        ((<obj> ∀ l' : loc, ⌜l' ≠ lr⌝ -∗ ▷ F γ t' s' #l'
                ={E}=∗ ∃ q', ▷ l' ↦{q'} -) ∗
          (<obj> (▷ F γ t' s' #lr ={E}=∗ ▷ Q1 t' s' ∗ ▷ Q2 t' s')) ∗
          (P -∗ ▷ Q2 t' s' ={E}=∗ ∃ s'', ⌜s' ⊑ s''⌝ ∗
            (∀ t , ⌜(t' < t)%positive⌝ -∗ ▷ GPS_Reader l t s'' vw γ ={E}=∗
                (<obj> (▷ Q1 t' s' ={E}=∗ ▷ F_read γ t' s' #lr)) ∗
                |={E}▷=> Q t s'' ∗ ▷ F γ t s'' vw)) ) ∧
        (▷ ∀ (v: lit), ⌜lit_neq lr v⌝ -∗
            <obj> ((F_read γ t' s' #v ={E}=∗ F_read γ t' s' #v ∗ R t' s' v) ∧
                    (F γ t' s' #v ={E}=∗ F γ t' s' #v ∗ R t' s' v))))%I in
    {{{ GPS_Reader l t s v γ ∗ (⊒Vb → ▷ GPS_PPInv γ)
        ∗ ▷ VSC
        ∗ (if decide (AcqRel ⊑ ow) then VS else △{tid} VS)
        ∗ (if decide (AcqRel ⊑ ow) then P  else △{tid} P )  }}}
      CAS #l #lr vw orf or ow @ tid; E
    {{{ (b: bool) t' s' (v': lit), RET #b;
        (⊒Vb → ▷ GPS_PPInv γ) ∗ ⌜s ⊑ s'⌝
        ∗ ( (⌜b = true  ∧ v' = LitLoc lr ∧ (t < t')%positive⌝
              ∗ GPS_Reader l t' s' vw γ
              ∗ if decide (AcqRel ⊑ or) then Q t' s' else ▽{tid} Q t' s')
          ∨ (⌜b = false ∧ lit_neq lr v' ∧ (t ≤ t')%positive⌝
              ∗ GPS_Reader l t' s' #v' γ
              ∗ (if decide (AcqRel ⊑ orf) then R t' s' v' else ▽{tid} (R t' s' v'))
              ∗ (if decide (AcqRel ⊑ ow)  then P          else △{tid} P ))) }}}.
  Proof.
    iIntros (SUB ORF OR OW VSC VS Φ) "(R & Inv & Comp & VS & P) Post".
    iApply (GPS_PPRaw_CAS_live_loc orf or ow _ lr vw _ _
              P Q Q1 Q2 R _ _ _ E (λ _, E)
              with "[$R $Inv $Comp VS $P] Post"); [done..|].
    case decide => ?.
    - iIntros (t' s') "Le'". iSpecialize ("VS" with "Le'").
      iSplit; [rewrite bi.and_elim_l|by rewrite bi.and_elim_r].
      iDestruct "VS" as "[VS $]".
      iIntros "!>" (l') "NEq F !>". rewrite monPred_objectively_elim.
      iMod ("VS" with "NEq F") as (q') ">Hq'". iIntros "!>". iExists _.
      iApply (own_loc_any_own_loc_prim_subjectively with "Hq'").
    - iApply (rel_mono with "VS").
      iIntros "VS" (t' s') "Le'". iSpecialize ("VS" with "Le'").
      iSplit; [rewrite bi.and_elim_l|by rewrite bi.and_elim_r].
      iDestruct "VS" as "[VS $]".
      iIntros "!>" (l') "NEq F !>". rewrite monPred_objectively_elim.
      iMod ("VS" with "NEq F") as (q') ">Hq'". iIntros "!>". iExists _.
      iApply (own_loc_any_own_loc_prim_subjectively with "Hq'").
  Qed.
End PP.

Global Instance: Params (@GPS_PPInv) 5 := {}.

Section Extra.
  Context `{!noprolG Σ, !gpsG Σ Prtcl, !atomicG Σ}.
  Implicit Types (IP : interpO Σ Prtcl).

  Global Instance GPS_PPInv_ne l γ :
    NonExpansive (λ IP, GPS_PPInv IP l γ).
  Proof.
    move => n f1 f2 EQ. rewrite 2!GPS_PPInv_eq. by apply gps_inv_ne.
  Qed.

  Lemma GPS_PPInv_proper :
    Proper ((≡) ==> (=) ==> (=) ==> (≡)) (λ IP l, GPS_PPInv IP l).
  Proof.
    move => ?? Eq ??????. subst. rewrite 2!GPS_PPInv_eq. by apply gps_inv_proper.
  Qed.
End Extra.
