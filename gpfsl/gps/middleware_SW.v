From iris.bi.lib Require Import fractional.
From iris.proofmode Require Import proofmode.

From gpfsl.base_logic Require Import iwp.
From gpfsl.logic Require Export lifting proofmode.
From gpfsl.logic Require Import atomic_ghost atomic_preds.
From gpfsl.gps Require Export model_defs.
From gpfsl.gps Require Import model.

Require Import iris.prelude.options.

Implicit Types (t : time) (v : val) (V : view) (E : coPset) (q: Qp) (ζ : absHist).

Section SingleWriter.
  Context `{!noprolG Σ, !gpsG Σ Prtcl, !atomicG Σ}
          (IP : interpO Σ Prtcl) (l : loc).
  Local Notation iProp := (iProp Σ).
  Local Notation vProp := (vProp Σ).

  Implicit Types (s : pr_stateT Prtcl) (χ : stateT Prtcl).

  Notation F := (IP true l).        (* full interp *)
  Notation F_read := (IP false l).  (* read interp *)

  Definition GPS_INV_def IW (γ : gname) : vProp := gps_inv IP IW l γ true.
  Definition GPS_INV_aux : seal (@GPS_INV_def). Proof. by eexists. Qed.
  Definition GPS_INV := unseal (@GPS_INV_aux).
  Definition GPS_INV_eq : @GPS_INV = _ := seal_eq _.

  Program Definition GPS_SWWriter_def t s v γ : vProp :=
    ∃ ζ (γs γl : gname),
      ⌜ γ = encode (γs, γl) ⌝
      ∗ gps_snap γs {[t := s]}
      ∗ l sw⊒{γl} ζ ∗ ⌜ (fst <$> ζ) !! t = Some v ∧ no_earlier_time ζ t ⌝.
  Definition GPS_SWWriter_aux : seal (@GPS_SWWriter_def). Proof. by eexists. Qed.
  Definition GPS_SWWriter := unseal (@GPS_SWWriter_aux).
  Definition GPS_SWWriter_eq : @GPS_SWWriter = _ := seal_eq _.

  Global Instance GPS_SWWriter_timeless t s v γ : Timeless (GPS_SWWriter t s v γ).
  Proof. rewrite GPS_SWWriter_eq. by apply _. Qed.

  (* Single-writers can be shared temporarily.
     Writes are not exclusive in this phase *)
  Definition GPS_SWSharedWriter_def t s v γ : vProp :=
    ∃ ζ (γs γl : gname),
      ⌜γ = encode (γs, γl)⌝
      ∗ gps_snap γs {[t := s]}
      ∗ l sy⊒{γl} ζ ∗ ⎡ at_writer γl ζ ⎤
      ∗ ⌜ (fst <$> ζ) !! t = Some v ∧ no_earlier_time ζ t ⌝
    .
  Definition GPS_SWSharedWriter_aux : seal (@GPS_SWSharedWriter_def).
  Proof. by eexists. Qed.
  Definition GPS_SWSharedWriter := unseal (@GPS_SWSharedWriter_aux).
  Definition GPS_SWSharedWriter_eq : @GPS_SWSharedWriter = _ := seal_eq _.

  Global Instance GPS_SWSharedWriter_timeless t s v γ :
    Timeless (GPS_SWSharedWriter t s v γ).
  Proof. rewrite GPS_SWSharedWriter_eq. by apply _. Qed.

  (* SharedReader holds a share of the exclusive write *)
  Definition GPS_SWSharedReader_def t s v q γ : vProp :=
    GPS_Reader l t s v γ ∗
      ∃ (tx: time) ζ V (γs γl : gname),
      ⌜ γ = encode (γs, γl) ∧ (tx ≤ t)%positive ⌝ ∗
      @{V} l casX⊒{γl,tx,q} ζ.
  Definition GPS_SWSharedReader_aux : seal (@GPS_SWSharedReader_def).
  Proof. by eexists. Qed.
  Definition GPS_SWSharedReader := unseal (@GPS_SWSharedReader_aux).
  Definition GPS_SWSharedReader_eq : @GPS_SWSharedReader = _ := seal_eq _.

  Global Instance GPS_SWSharedReader_timeless t s v q γ : Timeless (GPS_SWSharedReader t s v q γ).
  Proof. rewrite GPS_SWSharedReader_eq. by apply _. Qed.

  #[local] Lemma GPS_SWSharedReader_unfold {t s v q} {γ γs γl : gname} :
    γ = encode (γs,γl) →
    GPS_SWSharedReader t s v q γ ⊣⊢
    GPS_Reader l t s v γ ∗
    ∃ tx ζs Vs, @{Vs} l casX⊒{γl,tx,q} ζs ∗ ⌜ tx ≤ t ⌝%positive.
  Proof.
    intros ENC. rewrite GPS_SWSharedReader_eq. apply bi.sep_proper; [done|].
    do 3 (apply bi.exist_proper => ?). iSplit.
    - iDestruct 1 as (?? [ENC' ?]) "?".
      rewrite ENC in ENC'. apply encode_inj, pair_inj in ENC' as [<- <-].
      by iFrame.
    - iIntros "[C %]". iExists _, _. by iFrame.
  Qed.

  Global Instance GPS_SWSharedReader_fractional t s v γ :
    Fractional (λ q, GPS_SWSharedReader t s v q γ).
  Proof.
    rewrite /Fractional =>p q. iSplit.
    - rewrite {1}GPS_SWSharedReader_eq.
      iIntros "[#R C]". iDestruct "C" as (tx ζ V γs γl [ENC ?]) "[Hp Hq]".
      rewrite 2!(GPS_SWSharedReader_unfold ENC). iFrame "R".
      iSplitL "Hp"; iExists tx, ζ, V; by iFrame "#∗".
    - rewrite {1}GPS_SWSharedReader_eq. iIntros "[[R Hp] Hq]".
      iDestruct "Hp" as (tx ζ1 V γs γl [ENC ?]) "Hp".
      rewrite 2!(GPS_SWSharedReader_unfold ENC).
      iDestruct "Hq" as "[_ Hq]". iDestruct "Hq" as (tx' ζ2 V') "[Hq %]".
      iFrame "R". iExists tx, _, (V ⊔ V'). iSplit; [|done].
      iApply (view_at_mono' with "[Hp]"); [|eauto|]; [solve_lat|].
      iApply (view_at_mono with "Hq"); [solve_lat|].
      iIntros "Hq Hp". iApply (AtomicCASerXs_join with "Hp Hq").
  Qed.
  Global Instance GPS_SWSharedReader_asfractional t s v q γ :
    AsFractional (GPS_SWSharedReader t s v q γ)
                 (λ q, GPS_SWSharedReader t s v q γ) q.
  Proof. split; [done|apply _]. Qed.
  Global Instance frame_GPS_SWSharedReader p t s v γ q1 q2 RES :
    FrameFractionalHyps p (GPS_SWSharedReader t s v q1 γ)
                        (λ q, GPS_SWSharedReader t s v q γ) RES q1 q2 →
    Frame p (GPS_SWSharedReader t s v q1 γ) (GPS_SWSharedReader t s v q2 γ) RES | 5.
Proof. apply: frame_fractional. Qed.

  (** Properties of Assertions *)

  (* Unfolding *)
  #[local] Lemma GPS_SWWriter_from_SW γs γl ζ t s v V :
    ζ !! t = Some (v, V) → no_earlier_time ζ t →
    gps_snap γs {[t := s]} -∗ l sw⊒{γl} ζ -∗
    GPS_SWWriter t s v (encode (γs, γl)).
  Proof.
    rewrite GPS_SWWriter_eq. iIntros (EQ ?) "S W". iExists _, γs, γl.
    iFrame "S W". iPureIntro. split; [done|split]; [|done].
    by rewrite lookup_fmap EQ.
  Qed.

  #[local] Lemma GPS_SWWriter_from_SW_singleton γs γl t s v V :
    gps_snap γs {[t := s]} -∗ l sw⊒{γl} {[t := (v, V)]} -∗
    GPS_SWWriter t s v (encode (γs, γl)).
  Proof.
    apply : GPS_SWWriter_from_SW.
    - by rewrite lookup_insert.
    - by move => ? [?/lookup_singleton_Some [->//]].
  Qed.

  #[local] Lemma GPS_SWSharedWriter_unfold {t s v} {γ γs γl : gname} :
    γ = encode (γs,γl) →
    GPS_SWSharedWriter t s v γ ⊣⊢
    gps_snap γs {[t := s]} ∗
    (∃ ζ, ⎡ at_writer γl ζ ⎤ ∗ l sy⊒{γl} ζ ∗
      ⌜(fst <$> ζ) !! t = Some v ∧ no_earlier_time ζ t⌝).
  Proof.
    intros ENC. rewrite GPS_SWSharedWriter_eq. iSplit.
    - iDestruct 1 as (ζ ?? ENC') "(R & SY & W & F)".
      rewrite ENC in ENC'. apply encode_inj, pair_inj in ENC' as [<- <-].
      iFrame "R". iExists _. by iFrame.
    - iIntros "(R & %ζ & W & SY & S)". iExists ζ, _, _. by iFrame.
  Qed.

  (* SW-Single Mode *)
  Lemma GPS_SWWriter_PrtSync t s v γ:
    GPS_SWWriter t s v γ ⊢ PrtSync l t s v γ.
  Proof.
    rewrite GPS_SWWriter_eq.
    iDestruct 1 as (ζ γs γl ENC) "(Gs & SW & %IS & %MAX)".
    apply lookup_fmap_Some in IS as [[v' V] [Eq1 Eqt]]. simplify_eq.
    iExists γs, γl, V. iSplit; [done|]. iFrame "Gs".
    rewrite AtomicSWriter_AtomicSync.
    by iApply (AtomicSync_mono_lookup_singleton with "SW").
  Qed.

  Lemma GPS_SWWriter_Reader t s v γ:
    GPS_SWWriter t s v γ ⊢ GPS_Reader l t s v γ.
  Proof. by rewrite GPS_SWWriter_PrtSync PrtSync_GPS_Reader. Qed.

  Lemma GPS_Readers_agree IW t1 t2 s1 s2 v1 v2 γ Vb E:
    GPS_Reader l t1 s1 v1 γ -∗ GPS_Reader l t2 s2 v2 γ -∗
    (⊒Vb → ▷ GPS_INV IW γ) ={E}=∗
    (⊒Vb → ▷ GPS_INV IW γ) ∗ ⌜(t1 ⊑ t2 → s1 ⊑ s2) ∧ (t2 ⊑ t1 → s2 ⊑ s1)⌝.
  Proof. rewrite GPS_INV_eq -view_join_unfold. apply : GPS_Readers_agree. Qed.

  Lemma GPS_SWWriter_exclusive t1 t2 s1 s2 v1 v2 γ :
    GPS_SWWriter t1 s1 v1 γ -∗ GPS_SWWriter t2 s2 v2 γ -∗ False.
  Proof.
    rewrite GPS_SWWriter_eq.
    iDestruct 1 as (??? EQ1) "(_ & W1 & _)".
    iDestruct 1 as (??? EQ2) "(_ & W2 & _)".
    rewrite EQ1 in EQ2. apply encode_inj, pair_inj in EQ2 as [<- <-].
    by iApply (AtomicSWriter_exclusive with "W1 W2").
  Qed.

  Lemma GPS_SWWriter_latest IW t t' s s' v v' γ Vb E:
    GPS_SWWriter t s v γ -∗ GPS_Reader l t' s' v' γ
    -∗ (⊒Vb → ▷ GPS_INV IW γ)
    ={E}=∗ GPS_SWWriter t s v γ ∗ (⊒Vb → ▷ GPS_INV IW γ) ∗
          ⌜s' ⊑ s ∧ t' ⊑ t⌝.
  Proof.
    iIntros "W".
    iDestruct (GPS_SWWriter_Reader with "W") as "#R'".
    iIntros "#R I".
    iMod (GPS_Readers_agree with "R R' I") as "[$ %SUB]". iClear "R'".
    iIntros "!>".
    rewrite GPS_SWWriter_eq GPS_Reader_eq.
    iDestruct "W" as (??? EQ1) "(SW & W & %MAX)".
    iDestruct "R" as (??? EQ2) "[SR R]".
    rewrite EQ1 in EQ2. apply encode_inj, pair_inj in EQ2 as [<- <-].
    iDestruct (AtomicSWriter_latest with "W R") as %Sub.
    iSplit. { iExists _, _, _. by iFrame (EQ1) "SW W". }
    iPureIntro. destruct SUB as [SUB _]. destruct MAX as [? MAX].
    apply map_singleton_subseteq_l in Sub.
    specialize (MAX t' ltac:(by eexists)). split; [by apply SUB|done].
  Qed.

  (* SW-Shared Mode *)
  Lemma GPS_SWWriter_shared t s v γ :
    GPS_SWWriter t s v γ -∗
    GPS_SWSharedWriter t s v γ ∗ GPS_SWSharedReader t s v 1%Qp γ.
  Proof.
    iIntros "SW". iDestruct (GPS_SWWriter_Reader with "SW") as "#R".
    rewrite GPS_SWWriter_eq.
    iDestruct "SW" as (ζ γs γl ENC) "(#SN & SW & %IS & %MAX)".
    iDestruct (AtomicSWriter_AtomicCASerX with "SW")
      as "(#SY & %t' & C & W & %IS' & %MAX')".
    assert (t' = t) as ->.
    { apply : (anti_symm (≤)%positive); [by apply MAX|].
      apply MAX'. apply lookup_fmap_Some in IS as (?&?&?). by eexists. }
    rewrite (GPS_SWSharedWriter_unfold ENC) (GPS_SWSharedReader_unfold ENC).
    iFrame "SN R". iSplitL "W".
    - iExists _. by iFrame "SY W".
    - iDestruct (view_at_intro with "C") as (V) "[sV C]".
      iExists t, _, _. by iFrame.
  Qed.

  Lemma GPS_SWSharedWriter_Reader t s v γ :
    GPS_SWSharedWriter t s v γ -∗ GPS_Reader l t s v γ.
  Proof.
    rewrite GPS_SWSharedWriter_eq GPS_Reader_eq.
    iDestruct 1 as (ζ γs γl ENC) "(Gs & SY & W & %IS & %MAX)".
    apply lookup_fmap_Some in IS as [[v' V] [Eq1 Eqt]]. simpl in Eq1; subst v'.
    iExists γs, γl, V. iFrame (ENC) "Gs". rewrite AtomicSync_AtomicSeen.
    by iApply (AtomicSeen_mono_lookup_singleton with "SY").
  Qed.

  Lemma GPS_SWSharedReader_Reader t s v q γ:
    GPS_SWSharedReader t s v q γ -∗ GPS_Reader l t s v γ.
  Proof. rewrite GPS_SWSharedReader_eq. by iIntros "[$ ?]". Qed.

  Lemma GPS_SWSharedReader_Reader_join_subjectively t s v s' v' q γ:
    GPS_Reader l t s v γ -∗
    <subj> GPS_SWSharedReader t s' v' q γ -∗
    GPS_SWSharedReader t s v q γ.
  Proof.
    rewrite {1}GPS_SWSharedReader_eq. iIntros "R [_ SR]".
    iDestruct "SR" as (tx ζ V γs γl [ENC ?]) "C".
    rewrite objective_subjectively (GPS_SWSharedReader_unfold ENC).
    iFrame "R". iExists tx, ζ, V. by iFrame.
  Qed.

  Lemma GPS_SWSharedReaders_join_subjectively t1 t2 s1 s2 v1 v2 q1 q2 γ:
    GPS_SWSharedReader t1 s1 v1 q1 γ -∗
    <subj> GPS_SWSharedReader t2 s2 v2 q2 γ -∗
    GPS_SWSharedReader t1 s1 v1 (q1 + q2) γ.
  Proof.
    rewrite {1}GPS_SWSharedReader_eq. iIntros "[R SR]".
    iDestruct "SR" as (tx ζ1 V1 γs γl [ENC ?]) "C1".
    rewrite 2!(GPS_SWSharedReader_unfold ENC). iIntros "[_ SR]".
    iDestruct "SR" as (tx2 ζ2 V2) "[C2 %]". rewrite objective_subjectively.
    iFrame "R". iExists tx, (ζ1 ∪ ζ2), (V1 ⊔ V2). iSplit; [|done].
    rewrite -(bi.wand_elim_l' _ _ _ (AtomicCASerXs_join _ _ _ _ _ _ _ _)).
    iFrame "C1 C2".
  Qed.

  Lemma GPS_SWSharedReaders_join t1 t2 s1 s2 v1 v2 q1 q2 γ:
    GPS_SWSharedReader t1 s1 v1 q1 γ -∗ GPS_SWSharedReader t2 s2 v2 q2 γ -∗
    GPS_SWSharedReader t1 s1 v1 (q1 + q2) γ.
  Proof.
    iIntros "R1 R2". iApply (GPS_SWSharedReaders_join_subjectively with "R1").
    by iModIntro.
  Qed.

  Lemma GPS_SWRaw_SharedReader_Reader_agree IW t1 t2 s1 s2 v1 v2 q2 γ Vb E:
    GPS_Reader l t1 s1 v1 γ -∗ GPS_SWSharedReader t2 s2 v2 q2 γ -∗
    (⊒Vb → ▷ GPS_INV IW γ) ={E}=∗
      GPS_SWSharedReader t2 s2 v2 q2 γ ∗ (⊒Vb → ▷ GPS_INV IW γ) ∗
     ⌜ (t1 ⊑ t2 → s1 ⊑ s2) ∧ (t2 ⊑ t1 → s2 ⊑ s1) ⌝.
  Proof.
    iIntros "R1 R2".
    iDestruct (GPS_SWSharedReader_Reader with "R2") as "#RR2".
    iFrame "R2". by iApply (GPS_Readers_agree with "R1 RR2").
  Qed.

  Lemma GPS_SWRaw_SharedReaders_agree IW t1 t2 s1 s2 v1 v2 q1 q2 γ Vb E:
    GPS_SWSharedReader t1 s1 v1 q1 γ -∗ GPS_SWSharedReader t2 s2 v2 q2 γ -∗
    (⊒Vb → ▷ GPS_INV IW γ) ={E}=∗
      GPS_SWSharedReader t1 s1 v1 q1 γ ∗ GPS_SWSharedReader t2 s2 v2 q2 γ ∗
      (⊒Vb → ▷ GPS_INV IW γ) ∗ ⌜ (t1 ⊑ t2 → s1 ⊑ s2) ∧ (t2 ⊑ t1 → s2 ⊑ s1) ⌝.
  Proof.
    iIntros "R1". iDestruct (GPS_SWSharedReader_Reader with "R1") as "#RR1".
    iFrame "R1". by iApply (GPS_SWRaw_SharedReader_Reader_agree with "RR1").
  Qed.

  Lemma GPS_SWWriter_SharedWriter_excluded t1 t2 s1 s2 v1 v2 γ :
    GPS_SWWriter t1 s1 v1 γ -∗ GPS_SWSharedWriter t2 s2 v2 γ -∗ False.
  Proof.
    rewrite GPS_SWWriter_eq. iDestruct 1 as (? γs γl ENC) "(_ & Ex1 & _)".
    rewrite (GPS_SWSharedWriter_unfold ENC). iIntros "(_ & %ζ' & Ex2 & _)".
    iDestruct (AtomicSWriter_AtomicCASerX with "Ex1") as "(_ & % & _ & Ex1 & _)".
    by iDestruct (at_writer_exclusive with "Ex1 Ex2") as %?.
  Qed.

  Lemma GPS_SWWriter_SharedReader_excluded t1 t2 s1 s2 v1 v2 (q2: Qp) γ :
    GPS_SWWriter t1 s1 v1 γ -∗ GPS_SWSharedReader t2 s2 v2 q2 γ -∗ False.
  Proof.
    rewrite GPS_SWWriter_eq. iDestruct 1 as (? γs γl ENC) "(_ & Ex1 & _)".
    rewrite (GPS_SWSharedReader_unfold ENC). iIntros "[_ R]".
    iDestruct "R" as (???) "[Ex2 ?]".
    iApply (AtomicSWriter_CASerX_excluded_1 with "Ex1 Ex2").
  Qed.

  Lemma GPS_SWSharedWriter_latest_time_view t t' s s' v v' γ V1 V2 :
    @{V1} GPS_SWSharedWriter t s v γ -∗ @{V2} GPS_Reader l t' s' v' γ -∗ ⌜t' ⊑ t⌝.
  Proof.
    rewrite GPS_Reader_eq. iIntros "SR". iDestruct 1 as (γs γl V ENC) "[_ SN]".
    rewrite (GPS_SWSharedWriter_unfold ENC).
    iDestruct "SR" as "[_ SR]". iDestruct "SR" as (ζ) "(W & _ & %IS & %MAX)".
    rewrite view_at_objective_iff -(view_at_objective_iff (embed _) V2).
    rewrite at_writer_AtomicSeen_latest_1.
    iDestruct ("W" with "SN") as %Sub%map_singleton_subseteq_l.
    iPureIntro. apply MAX. by eexists.
  Qed.
  Lemma GPS_SWSharedWriter_latest_time_2 t t' s s' v v' γ V2 :
    GPS_SWSharedWriter t s v γ -∗ @{V2} GPS_Reader l t' s' v' γ -∗ ⌜t' ⊑ t⌝.
  Proof. by apply view_at_wand_l, GPS_SWSharedWriter_latest_time_view. Qed.
  Lemma GPS_SWSharedWriter_latest_time_1 t t' s s' v v' γ:
    GPS_SWSharedWriter t s v γ -∗ GPS_Reader l t' s' v' γ -∗ ⌜t' ⊑ t⌝.
  Proof. by apply view_at_wand_lr, GPS_SWSharedWriter_latest_time_view. Qed.

  Lemma GPS_SWSharedWriter_latest_time t t' s s' v v' q γ:
    GPS_SWSharedWriter t s v γ -∗ GPS_SWSharedReader t' s' v' q γ -∗ ⌜t' ⊑ t⌝.
  Proof.
    iIntros "W R". iDestruct (GPS_SWSharedReader_Reader with "R") as "R".
    by iApply (GPS_SWSharedWriter_latest_time_1 with "W R").
  Qed.

  Lemma GPS_SWSharedReader_Reader_update_max q t1 t2 s1 s2 v1 v2 γ:
    GPS_SWSharedReader t1 s1 v1 q γ -∗ GPS_Reader l t2 s2 v2 γ -∗
    let t := if (decide (t2 ≤ t1)%positive) then t1 else t2 in
    let s := if (decide (t2 ≤ t1)%positive) then s1 else s2 in
    let v := if (decide (t2 ≤ t1)%positive) then v1 else v2 in
    GPS_SWSharedReader t s v q γ.
  Proof.
    iIntros "SR R". case decide => [//|/Pos.lt_nle Le1].
    rewrite GPS_SWSharedReader_eq /GPS_SWSharedReader_def.
    iFrame "R". iDestruct "SR" as "[_ SR]". iDestruct "SR" as (?????[? ?]) "C".
    iExists _,_,_,_,_. iFrame "C". iPureIntro. split; [done|]. lia.
  Qed.

  Lemma GPS_SWSharedReader_Reader_update_max_2 q t1 t2 s1 s2 v1 v2 γ:
    GPS_SWSharedReader t1 s1 v1 q γ -∗ GPS_Reader l t2 s2 v2 γ -∗
    let t := if (decide (t1 ≤ t2)%positive) then t2 else t1 in
    let s := if (decide (t1 ≤ t2)%positive) then s2 else s1 in
    let v := if (decide (t1 ≤ t2)%positive) then v2 else v1 in
    GPS_SWSharedReader t s v q γ.
  Proof.
    iIntros "SR R". case decide => [Le1|//].
    rewrite GPS_SWSharedReader_eq /GPS_SWSharedReader_def.
    iFrame "R". iDestruct "SR" as "[_ SR]". iDestruct "SR" as (?????[? ?]) "C".
    iExists _,_,_,_,_. iFrame "C". iPureIntro. split; [done|]. lia.
  Qed.

  Lemma GPS_SWSharedWriter_Reader_update t t' s s' v v' q γ :
    GPS_SWSharedWriter t s v γ -∗ GPS_SWSharedReader t' s' v' q γ -∗
    GPS_SWSharedWriter t s v γ ∗ GPS_SWSharedReader t s v q γ.
  Proof.
    iIntros "W SR".
    iDestruct (GPS_SWSharedWriter_latest_time with "W SR") as %Le.
    iDestruct (GPS_SWSharedWriter_Reader with "W") as "#R".
    iFrame "W".
    iDestruct (GPS_SWSharedReader_Reader_update_max_2 with "SR R") as "SR".
    rewrite 3!(decide_True _ _ Le). by iFrame.
  Qed.

  (* The fupd is only needed to strip laters on timeless resources. *)
  Lemma GPS_SWRaw_SharedWriter_revert_subjectively IW t t' s s' v v' γ Vb E:
    GPS_SWSharedWriter t s v γ -∗ <subj> GPS_SWSharedReader t' s' v' 1%Qp γ
    -∗ (⊒Vb → ▷ GPS_INV IW γ)
    ={E}=∗ GPS_SWWriter t s v γ ∗ (⊒Vb → ▷ GPS_INV IW γ).
  Proof.
    rewrite -view_join_unfold GPS_INV_eq view_at_subjectively_inv.
    iIntros "SW [%Vr SR] I".
    iDestruct (GPS_SWSharedWriter_latest_time_2 with "SW [SR]") as %Let'.
    { by rewrite GPS_SWSharedReader_Reader. }
    iDestruct (view_join_view_at_access' with "I") as (V) "(sV & I & Close)".
    rewrite view_at_later.
    iDestruct "I" as (μ γs γl ζ tx) "(>%ENC & Go & >P & rB & rE & >rF)".
    iDestruct "rF" as %(FI & SS & SWCon).
    rewrite (GPS_SWSharedWriter_unfold ENC) (GPS_SWSharedReader_unfold ENC).
    iDestruct "SW" as "(St & %ζ' & W & SY & %IS & %MAX)".
    apply lookup_fmap_Some in IS as ([vx Vt]&Eq1&Eqt). simpl in Eq1. subst vx.
    iDestruct (AtomicPtsToX_at_writer_agree with "P W") as %<-.
    iDestruct "SR" as "[R SR]". iDestruct "SR" as (tx' ζs Vs) "[C %Le]".
    rewrite view_at_view_at.
    iDestruct (AtomicPtsToX_AtomicCASerX_latest with "P C") as %[-> Subs].
    iMod (AtomicPtsToX_CAS_update with "P C") as (tx' MAXx') "[P C]".
    assert (tx' = t) as ->.
    { apply: (anti_symm (≤)%positive); by [apply MAX, MAXx'|apply MAXx'; eexists]. }
    have ? : (tx ≤ t)%positive by etrans.
    iDestruct (AtomicCASerX_AtomicWriter with "SY C W") as "W"; [done|].
    iIntros "!>". iSplitL "St W".
    { rewrite ENC. by iApply (GPS_SWWriter_from_SW with "St W"). }
    iApply ("Close" with "sV"). iIntros "!>".
    iExists μ, γs, γl, ζ, t. iFrame (ENC) "Go P".
    iSplitL "rB"; last iSplitL; last iPureIntro.
    - rewrite 2!view_at_objective_iff. iApply (big_sepM_mono with "rB").
      intros t0 [v0 V0] Eqt0. simpl.
      case (decide (tx ≤ t0)%positive) => [Le0|NLe0].
      + rewrite decide_True; [done|].
        by eapply (SWConnect_cbends_le _ _ _ _ _ _ MAX SWCon).
      + rewrite decide_False; [done|lia].
    - rewrite 2!view_at_objective_iff. iApply (big_sepM_mono with "rE").
      intros t0 [v0 V0] Eqt0. simpl. apply view_at_mono; [done|].
      case (decide (tx ≤ t0)%positive) => [Le0|NLe0].
      + case decide => _; [|rewrite assoc]; eauto.
      + rewrite decide_False; [done|lia].
    - split; last split; [|done|].
      + intros t0 Et0 DS. apply (FI _ Et0).
        destruct DS as (td & ? & ?). exists td. split; [lia|done].
      + intros t0 Eqt0 Let0 DS. apply (SWCon _ Eqt0); [lia|].
        destruct DS as (td & ? & ?). exists td. split; [lia|done].
  Qed.

  Lemma GPS_SWRaw_SharedWriter_revert IW t t' s s' v v' γ Vb E:
    GPS_SWSharedWriter t s v γ -∗ GPS_SWSharedReader t' s' v' 1%Qp γ
    -∗ (⊒Vb → ▷ GPS_INV IW γ)
    ={E}=∗ GPS_SWWriter t s v γ ∗ (⊒Vb → ▷ GPS_INV IW γ).
  Proof.
    iIntros "W R". iApply (GPS_SWRaw_SharedWriter_revert_subjectively with "W").
    by iModIntro.
  Qed.

  (** Semantics of Operations *)

  (* DEALLOC *)
  Lemma GPS_INV_dealloc IW b γ E (SUB: ↑histN ⊆ E):
    ⎡ hist_inv ⎤ -∗ ▷?b GPS_INV IW γ ={E}=∗
      ∃ t s v, l ↦ v ∗ ▷?b F γ t s v.
  Proof.
    iIntros "HInv Inv". rewrite GPS_INV_eq /GPS_INV_def.
    by iApply (GPSRaw_dealloc with "HInv Inv").
  Qed.

  (* SW DEALLOC *)
  Lemma GPS_SWWriter_dealloc IW b t s v γ E (SUB: ↑histN ⊆ E) :
    ⎡ hist_inv ⎤ -∗ ▷?b GPS_INV IW γ -∗ GPS_SWWriter t s v γ ={E}=∗
      l ↦ v ∗ ▷?b F γ t s v.
  Proof.
    iIntros "HInv Inv W".
    rewrite GPS_INV_eq /GPS_INV_def GPS_SWWriter_eq /=.
    iDestruct "W" as (ζ γs γl ENC) "(SS & W & %IS & %MAX)".
    apply lookup_fmap_Some in IS as ([v' ?] & Eqv & Eqt). simpl in Eqv. subst v'.
    iDestruct (AtomicSWriter_AtomicSync with "W") as "#SY".
    rewrite AtomicSync_mono_lookup_singleton; [|done].
    by iApply (GPSRaw_SW_dealloc with "HInv SS SY W Inv").
  Qed.

  (* INIT *)
  Lemma GPS_SWRaw_Init_vs IW b s v:
    l ↦ v -∗ (∀ t γ, ▷?b F γ t s v)
    ==∗ ∃ γ t, GPS_SWWriter t s v γ ∗ ▷?b GPS_INV IW γ.
  Proof.
    rewrite GPS_INV_eq. iIntros "P F".
    iMod (GPSRaw_Init_vs IP _ IW b v s true with "P F")
      as (t γ γs γl) "(I & -> & SS & %V & W)".
    iIntros "!>". iExists _, t. iFrame "I".
    by iApply (GPS_SWWriter_from_SW_singleton with "SS W").
  Qed.

  Lemma GPS_SWRaw_Init IW b v s tid E:
    ↑histN ⊆ E →
    {{{ l ↦ ? ∗ (∀ t γ, ▷?b F γ t s v) }}}
      #l <- v @ tid; E
    {{{ γ t, RET #☠; GPS_SWWriter t s v γ ∗ ▷?b GPS_INV IW γ }}}.
  Proof.
    iIntros (? Φ) "(own & F) Post". iApply wp_fupd. wp_write.
    iMod (GPS_SWRaw_Init_vs with "own F") as (γ t) "?". by iApply "Post".
  Qed.

  Lemma GPS_SWRaw_Init_vs_strong_open IW b v s
    (P Q: time → gname → vProp) E :
    l ↦ v -∗
    (∀ t γ, (<obj> P t γ) -∗ GPS_SWWriter t s v γ ={E}=∗ ▷?b F γ t s v ∗ Q t γ )
    ={E}=∗ ∃ γ t, |={E}=> ((<obj> P t γ) ={E}=∗ ▷?b GPS_INV IW γ ∗ Q t γ).
  Proof.
    iIntros "oL F".
    iMod (GPSRaw_Init_strong_vs_open IP _ _ b v s P Q with "oL [F]")
      as (t γ) "PQ".
    { iIntros (γl γs t V) "S W P". iApply ("F" with "P").
      iApply (GPS_SWWriter_from_SW_singleton with "S W"). }
    iIntros "!>". iExists γ, t. rewrite GPS_INV_eq. by iFrame.
  Qed.

  Lemma GPS_SWRaw_Init_vs_strong IW b v s (Q: time → gname → vProp) E :
    l ↦ v -∗
    (∀ t γ, GPS_SWWriter t s v γ ={E}=∗ ▷?b F γ t s v ∗ Q t γ )
    ={E}=∗ ∃ γ t, ▷?b GPS_INV IW γ ∗ Q t γ.
  Proof.
    iIntros "oL F".
    iMod (GPSRaw_Init_strong_vs IP _ _ b v s Q with "oL [F]")
      as (t γ) "[I Q]".
    { iIntros (γl γs t V) "S W". iApply "F".
      iApply (GPS_SWWriter_from_SW_singleton with "S W"). }
    iIntros "!>". iExists γ, t. rewrite GPS_INV_eq. by iFrame.
  Qed.

  (* SW READ *)
  Lemma GPS_SWRaw_SWRead IW (R : vProp) o t s v γ Vb tid E:
    ↑histN ⊆ E → o = Relaxed ∨ o = AcqRel →
    {{{ GPS_SWWriter t s v γ ∗ (⊒Vb → ▷ GPS_INV IW γ)
      ∗ ▷ <obj> (F γ t s v ={E}=∗ F γ t s v ∗ R) }}}
      Read o #l @ tid; E
    {{{ RET v; GPS_SWWriter t s v γ ∗ (⊒Vb → ▷ GPS_INV IW γ) ∗ R }}}.
  Proof.
    iIntros (SUB OR Φ) "(W & I & D) Post".
    iDestruct (GPS_SWWriter_Reader with "W") as "#R".
    rewrite GPS_SWWriter_eq -view_join_unfold GPS_INV_eq.
    iDestruct "W" as (ζ γs γl ENC) "(#Prt & W & %IS & %MAX)".
    iApply (GPSRaw_ReadSW with "[$D $I $W $R]"); [done..|].
    iIntros "!> (I & W & R')". iApply "Post".
    iFrame "I R'". iExists _, γs, γl. iFrame "Prt W". by iPureIntro.
  Qed.

  (* Reader READ *)
  Lemma GPS_SWRaw_Read' IW (Q R : time → _ → val → vProp) o t s v γ tid Vb E :
    ↑histN ⊆ E → o = Relaxed ∨ o = AcqRel →
    {{{ GPS_Reader l t s v γ
        ∗ (⊒Vb → ▷ GPS_INV IW γ)
        ∗ (▷ ∀ t' s' v', ⌜s ⊑ s' ∧ t ⊑ t'⌝ -∗
             <obj> ((F_read γ t' s' v' ={E}=∗ F_read γ t' s' v' ∗ R t' s' v') ∧
                    (F γ t' s' v' ={E}=∗ F γ t' s' v' ∗ R t' s' v') ∧
                    (IW l γ t' s' v' ={E}=∗ IW l γ t' s' v' ∗ R t' s' v')))
        ∗ (▷ ∀ t' s' v', ⌜s ⊑ s' ∧ t ⊑ t'⌝ -∗ R t' s' v' ={E}=∗ Q t' s' v') }}}
      Read o #l @ tid; E
    {{{ t' s' v', RET v'; ⌜s ⊑ s' ∧ t ⊑ t'⌝
        ∗ GPS_Reader l t' s' v' γ ∗ (⊒Vb → ▷ GPS_INV IW γ)
        ∗ if (decide (AcqRel ⊑ o)) then Q t' s' v' else ▽{tid} Q t' s' v' }}}.
  Proof.
    iIntros (SUB OR Φ) "(R & I & D & VQ) Post".
    iApply (GPSRaw_Read_non_ex with "[D $VQ I $R]"); [done..| |].
    { iSplitR "I".
      - iIntros "!> !>" (???) "I". iSpecialize ("D" with "I").
        iApply (monPred_objectively_elim with "D").
      - rewrite -view_join_unfold GPS_INV_eq. by iFrame "I". }
    iIntros "!>" (t' s' v') "(F & I & Q & R)".
    iApply "Post". iFrame.
    by rewrite -view_join_unfold GPS_INV_eq.
  Qed.

  Lemma GPS_SWRaw_Read IW (R : time → _ → val → vProp) o t s v γ tid Vb E:
    ↑histN ⊆ E → o = Relaxed ∨ o = AcqRel →
    {{{ GPS_Reader l t s v γ
        ∗ (⊒Vb → ▷ GPS_INV IW γ)
        ∗ (▷ ∀ t' s' v', ⌜s ⊑ s' ∧ t ⊑ t'⌝ -∗
             <obj> ((F_read γ t' s' v' ={E}=∗ F_read γ t' s' v' ∗ R t' s' v') ∧
                    (F γ t' s' v' ={E}=∗ F γ t' s' v' ∗ R t' s' v') ∧
                    (IW l γ t' s' v' ={E}=∗ IW l γ t' s' v' ∗ R t' s' v'))) }}}
      Read o #l @ tid; E
    {{{ t' s' v', RET v'; ⌜s ⊑ s' ∧ t ⊑ t'⌝
        ∗ GPS_Reader l t' s' v' γ ∗ (⊒Vb → ▷ GPS_INV IW γ)
        ∗ if (decide (AcqRel ⊑ o)) then R t' s' v' else ▽{tid} R t' s' v' }}}.
  Proof.
    iIntros (SUB OR Φ) "(R & Inv & D) Post".
    iApply (GPS_SWRaw_Read' IW R R o t s v γ tid Vb E SUB OR
              with "[$R $Inv $D] Post").
    by iIntros "!>" (????) "$".
  Qed.

  (* SW WRITE *)
  Lemma GPS_SWRaw_SWWrite IW R
    o t s s' v v' γ tid Vb E (Exts: s ⊑ s'):
    ↑histN ⊆ E → o = Relaxed ∨ o = AcqRel →
    let WVS: vProp := (∀ t', ⌜(t < t')%positive⌝ ={E}=∗ F γ t' s' v')%I in
    {{{ GPS_SWWriter t s v γ ∗ (⊒Vb → ▷ GPS_INV IW γ)
        ∗ ▷ (if decide (AcqRel ⊑ o) then WVS else △{tid} WVS)
        ∗ ▷ <obj> (F γ t s v ={E}=∗ IW l γ t s v ∗ R) }}}
      Write o #l v' @ tid; E
    {{{ t', RET #☠; ⌜(t < t')%positive⌝ ∗ GPS_SWWriter t' s' v' γ ∗
        (⊒Vb → ▷ GPS_INV IW γ) ∗ R }}}.
  Proof.
    iIntros (SUB OW WVS Φ) "(W & I & VS & IW) Post".
    rewrite -{1}view_join_unfold GPS_INV_eq {1}GPS_SWWriter_eq.
    iDestruct "W" as (ζ γs γl ENC) "(Gs & W & %IS & %MAXt)".
    (* we use different views in different access modes [o] *)
    iApply wp_fupd. destruct OW as [-> | ->]; simpl.
    - iMod (rel_later_intro with "VS") as "VS".
      iApply (wp_rel_revert_view_at with "VS").
      iIntros (Vrel) "sVrel VS sV".
      iApply (GPSRaw_WriteSW IP l _ t s v _ v' s' _ γ γs γl Vrel Vrel Vb E _
                Exts MAXt IS SUB with "[$I $Gs $W $sV sVrel]");
        [by left|done|iFrame "sVrel"|..].
      iIntros "!>" (t' Vt V' V'') "(F & #sV'' & SP' & W & RF & I)". simpl.
      iDestruct "F" as %(EqVt' & Lt' & MAXt' & LeV'' & ? & ? & LeV1 & LeV2).
      iMod (view_at_objectively _ Vt with "IW RF") as "[IW R]".
      iMod (view_at_mono_2 _ _ _ LeV1 with "VS [%//]") as "F".
      iSpecialize ("I" with "F IW").
      iIntros "!>". iApply ("Post" $! t'). iFrame (Lt').
      iAssert (⊒Vt)%I with "[W]" as "#sVt".
      { rewrite AtomicSWriter_AtomicSync (AtomicSync_lookup _ _ _ t v Vt).
        - iApply (view_at_elim with "sV'' W").
        - rewrite lookup_insert_ne; [done|lia]. }
      iDestruct (view_at_elim with "sVt R") as "$". iSplitR "I".
      + iDestruct (view_at_elim with "sV'' W") as "W".
        rewrite ENC. iApply (GPS_SWWriter_from_SW with "SP' W"); [|done].
        by rewrite lookup_insert.
      + rewrite view_at_view_join -view_join_unfold.
        iApply (view_join_intro_at with "I sV''").

    - iDestruct (view_at_intro with "VS") as (V) "[#sV VS]".
      iApply (GPSRaw_WriteSW IP l _ t s v _ v' s' _ γ γs γl V V Vb E _
                Exts MAXt IS SUB with "[$I $Gs $W $sV]"); [by right|done..|].
      iIntros "!>" (t' Vt V' V'') "(F & #sV'' & SP' & W & RF & I)". simpl.
      iDestruct "F" as %(EqVt' & Lt' & MAXt' & LeV' & NEqV' & NLeV' & ->).
      iMod (view_at_objectively _ Vt with "IW RF") as "[IW R]".
      iMod (view_at_mono_2 _ _ _ LeV' with "VS [%//]") as "F".
      iSpecialize ("I" with "F IW").
      iIntros "!>". iApply ("Post" $! t'). iFrame (Lt').
      iAssert (⊒Vt)%I with "[W]" as "#sVt".
      { rewrite AtomicSWriter_AtomicSync (AtomicSync_lookup _ _ _ t v Vt).
        - iApply (view_at_elim with "sV'' W").
        - rewrite lookup_insert_ne; [done|lia]. }
      iDestruct (view_at_elim with "sVt R") as "$". iSplitR "I".
      + iDestruct (view_at_elim with "sV'' W") as "W".
        rewrite ENC. iApply (GPS_SWWriter_from_SW with "SP' W"); [|done].
        by rewrite lookup_insert.
      + rewrite view_at_view_join -view_join_unfold.
        iApply (view_join_intro_at with "I sV''").
  Qed.

  (* SW WRITE RELEASE itself *)
  Lemma GPS_SWRaw_SWWrite_rel_view
    IW Q Q1 Q2 P t s s' v v' γ tid Vb E (Exts: s ⊑ s'):
    ↑histN ⊆ E →
    let WVS: vProp :=
      (∀ t', ⌜(t < t')%positive⌝ -∗ GPS_SWWriter t' s' v' γ -∗ Q2 -∗ P
                ={E}=∗ (<obj> (Q1 ={E}=∗ IW l γ t s v)) ∗
                       |={E}=> (F γ t' s' v' ∗ Q t'))%I in
    {{{ GPS_SWWriter t s v γ ∗ (⊒Vb → ▷ GPS_INV IW γ)
        ∗ ▷ WVS ∗ ▷ P ∗ ▷ <obj> (F γ t s v ={E}=∗ Q1 ∗ Q2) }}}
      #l <-ʳᵉˡ v' @ tid; E
    {{{ t' V', RET #☠; ⌜(t < t')%positive⌝ ∗ GPS_Reader l t' s' v' γ ∗
          ⊒V' ∗ ⎡ P V' ⎤ ∗
          (⎡ P V' ⎤ ={E}=∗ ⎡ (⊒Vb → ▷ GPS_INV IW γ) V' ⎤ ∗ Q t') }}}.
  Proof.
    iIntros (SUB WVS Φ) "(W & I & WVS & P & VS) Post".
    rewrite -{1}view_join_unfold GPS_INV_eq GPS_SWWriter_eq.
    iDestruct "W" as (ζ γs γl ENC) "(#Gs & W & %IS & %MAXt)".
    iCombine "WVS P" as "WVSP".
    iDestruct (view_at_intro with "WVSP") as (V) "[#sV [WVS P]]".
    iApply (GPSRaw_WriteSW IP l _ t s v _ v' s' _ γ γs γl V V Vb E _
                Exts MAXt IS SUB with "[$I $Gs $W $sV]"); [by right|done..|].
    iIntros "!>" (t' Vt V' V'') "(F & #sV' & #SP' & W & RF & I)". simpl.
    iDestruct "F" as %(EqVt' & Lt' & MAXt' & LeV' & NEqV' & NLeV' & ->).
    iAssert (@{V'} ⊒Vt)%I with "[W]" as %LeVt.
    { rewrite AtomicSWriter_AtomicSync (AtomicSync_lookup _ _ _ t v Vt).
      - iFrame. - rewrite lookup_insert_ne; [done|lia]. }

    iApply ("Post" $! t' V'). rewrite -2!view_at_unfold. iFrame (Lt') "sV' P".
    iSplit.
    { iDestruct (view_at_elim with "sV' W") as "W".
      iDestruct (AtomicSWriter_AtomicSeen with "W") as "R".
      rewrite ENC. iApply (GPS_Reader_from_seen with "SP' R").
      by rewrite lookup_insert. }
    iIntros "P".
    iMod (view_at_objectively _ Vt with "VS RF") as "[Q1 Q2]".
    iMod (view_at_mono_2 _ _ _ LeV' with "WVS [%//] [W] [$Q2] P") as "[V1 >[F Q]]".
    { iApply (view_at_mono' with "W"); [done|].
      iApply (view_at_mono V' with "[SP']"); [done|..]; last first.
      { iApply (view_at_objective_iff with "SP'"). }
      rewrite ENC. apply : GPS_SWWriter_from_SW; [by rewrite lookup_insert|done]. }
    rewrite view_at_objective_iff -view_join_unfold.
    iMod (view_at_objectively _ Vt with "V1 Q1") as "IW".
    iIntros "!>". iDestruct ("I" with "F IW") as "$".
    iApply (view_at_elim with "sV' Q").
  Qed.

  Lemma GPS_SWRaw_SWWrite_rel
    IW Q Q1 Q2 t s s' v v' γ tid Vb E (Exts: s ⊑ s'):
    ↑histN ⊆ E →
    let WVS: vProp :=
      (∀ t', ⌜(t < t')%positive⌝ -∗ GPS_SWWriter t' s' v' γ -∗ Q2
                ={E}=∗ (<obj> (Q1 ={E}=∗ IW l γ t s v)) ∗
                       |={E}=> (F γ t' s' v' ∗ Q t'))%I in
    {{{ GPS_SWWriter t s v γ ∗ (⊒Vb → ▷ GPS_INV IW γ)
        ∗ ▷ WVS ∗ ▷ <obj> (F γ t s v ={E}=∗ Q1 ∗ Q2) }}}
      #l <-ʳᵉˡ v' @ tid; E
    {{{ t', RET #☠; ⌜(t < t')%positive⌝ ∗ GPS_Reader l t' s' v' γ ∗
          (⊒Vb → ▷ GPS_INV IW γ) ∗ Q t' }}}.
  Proof.
    iIntros (SUB WVS Φ). iIntros "(W & Inv & F & IW) Post".
    iApply wp_fupd.
    iApply (GPS_SWRaw_SWWrite_rel_view _ Q Q1 Q2 True%I
              with "[$W $Inv F $IW]"); [done..| |].
    { iSplit; [|done]. iIntros "!>" (t' Let) "W Q2 _".
      iApply ("F" with "[%//] W Q2"). }
    iIntros "!>" (t' V') "(Let & W & In & _ & VS)".
    iMod ("VS" with "[//]") as "[Inv Q]".
    iDestruct (monPred_in_elim with "In Inv") as "Inv".
    by iApply ("Post" with "[$Let $W $Inv $Q]").
  Qed.

  Lemma GPS_SWRaw_SharedReader_Read' IW Q R o t s v (q: frac) γ tid Vb E:
    ↑histN ⊆ E → o = Relaxed ∨ o = AcqRel →
    {{{ GPS_SWSharedReader t s v q γ ∗ (⊒Vb → ▷ GPS_INV IW γ)
        ∗ (▷ ∀ t' s' v', ⌜s ⊑ s' ∧ t ⊑ t'⌝ -∗
             <obj> ((F_read γ t' s' v' ={E}=∗ F_read γ t' s' v' ∗ R t' s' v') ∧
                    (F γ t' s' v' ={E}=∗ F γ t' s' v' ∗ R t' s' v')))
        ∗ (▷ ∀ t' s' v', ⌜s ⊑ s' ∧ t ⊑ t'⌝ -∗ R t' s' v' ={E}=∗ Q t' s' v') }}}
      Read o #l @ tid; E
    {{{ t' s' v', RET v'; ⌜s ⊑ s' ∧ t ⊑ t'⌝
        ∗ GPS_SWSharedReader t' s' v' q γ ∗ (⊒Vb → ▷ GPS_INV IW γ)
        ∗ if (decide (AcqRel ⊑ o)) then Q t' s' v' else ▽{tid} Q t' s' v' }}}.
  Proof.
    iIntros (SUB OR Φ) "(SR & I & D & VQ) Post".
    rewrite GPS_SWSharedReader_eq GPS_INV_eq -{1}view_join_unfold.
    iDestruct "SR" as "[#R SR]".
    iDestruct "SR" as (tx ζx Vx γs γl [ENC Letx]) "C".
    iApply (GPSRaw_Read_ex IP l IW Q R tx q Vx ζx t s v o γ γs γl _ Vb E _
                          SUB OR ENC with "[D $VQ $I $R C]").
    { iSplitL "D".
      - iIntros "!> !>" (???) "I". iSpecialize ("D" with "I").
        iApply (monPred_objectively_elim with "D").
      - iFrame (Letx). by iFrame. }
    iIntros "!>" (t' s' v') "([%Les' %Let'] & I & [C _] & Q & R')".
    iApply "Post". iSplit; [done|]. rewrite -view_join_unfold. iFrame "I Q R'".
    iExists tx, _, _, γs, γl. iFrame "C". iPureIntro. split; [done|lia].
  Qed.

  Lemma GPS_SWRaw_SharedReader_Read IW R o t s v (q: frac) γ tid Vb E:
    ↑histN ⊆ E → o = Relaxed ∨ o = AcqRel →
    {{{ GPS_SWSharedReader t s v q γ ∗ (⊒Vb → ▷ GPS_INV IW γ)
        ∗ (▷ ∀ t' s' v', ⌜s ⊑ s' ∧ t ⊑ t'⌝ -∗
             <obj> ((F_read γ t' s' v' ={E}=∗ F_read γ t' s' v' ∗ R t' s' v') ∧
                    (F γ t' s' v' ={E}=∗ F γ t' s' v' ∗ R t' s' v'))) }}}
      Read o #l @ tid; E
    {{{ t' s' v', RET v'; ⌜s ⊑ s' ∧ t ⊑ t'⌝
        ∗ GPS_SWSharedReader t' s' v' q γ ∗ (⊒Vb → ▷ GPS_INV IW γ)
        ∗ if (decide (AcqRel ⊑ o)) then R t' s' v' else ▽{tid} R t' s' v' }}}.
  Proof.
    iIntros (SUB OR Φ) "(R & Inv & D) Post".
    iApply (GPS_SWRaw_SharedReader_Read' IW R R o t s v q γ tid Vb E SUB OR
              with "[$R $Inv $D] Post").
    by iIntros "!>" (????) "$".
  Qed.

  Lemma GPS_SWRaw_SharedReader_Read_val_dealloc
    IW P R R' vd t s v (q: frac) γ tid Vb E:
    ↑histN ⊆ E →
    {{{ GPS_SWSharedReader t s v q γ ∗ (⊒Vb → ▷ GPS_INV IW γ)
        ∗ P
        ∗ (▷ ∀ t' s', ⌜s ⊑ s' ∧ t ⊑ t'⌝ -∗
            (P -∗ GPS_SWSharedReader t s v q γ -∗
              (F γ t' s' vd ={E}=∗ ⊒Vb ∗ GPS_SWSharedWriter t' s' vd γ ∗ R t' s') ∧
              (F_read γ t' s' vd ={E}=∗ False)) ∧
            <obj> (∀ v',
                    (F_read γ t' s' v' ={E}=∗ F_read γ t' s' v' ∗ R' t' s' v') ∧
                    (F γ t' s' v' ={E}=∗ F γ t' s' v' ∗ R' t' s' v'))) }}}
      !ᵃᶜ#l @ tid; E
    {{{ t' s' v', RET v'; ⌜s ⊑ s' ∧ t ⊑ t'⌝ ∗
        if (decide (v' = vd)) then l ↦ v' ∗ R t' s'
        else P ∗ R' t' s' v' ∗ GPS_SWSharedReader t' s' v' q γ
             ∗ (⊒Vb → ▷ GPS_INV IW γ) }}}.
  Proof.
    iIntros (SUB Φ) "(SR & I & P & VS) Post".
    rewrite -{1}view_join_unfold GPS_INV_eq {1}GPS_SWSharedReader_eq.
    iDestruct "SR" as "[#R SR]".
    iDestruct "SR" as (tx ζx Vx γs γl [ENC Letx]) "C".
    iApply (GPSRaw_Read_val_dealloc_ex IP l IW P R R' vd q tx t s v γ γs γl true
              ζx Vb Vx tid E SUB ENC with "[VS $I $R $P $C]").
    { iSplitL; [|done]. iIntros "!>" (??) "Le". iSpecialize ("VS" with "Le").
      iSplit; [rewrite bi.and_elim_l|by rewrite bi.and_elim_r].
      iIntros "P [C _]". iSpecialize ("VS" with "P [C]").
      { rewrite (GPS_SWSharedReader_unfold ENC). iFrame "R".
        iExists _, _, _. by iFrame "C". }
      iSplit; [rewrite bi.and_elim_l|by rewrite bi.and_elim_r].
      iIntros "F". iMod ("VS" with "F") as "($ & SW & $)".
      rewrite (GPS_SWSharedWriter_unfold ENC). by iFrame. }
    iIntros "!>" (???) "[[% %] H]". iApply "Post". iSplit; [done|].
    case decide => ?.
    - iDestruct "H" as "[$ $]".
    - rewrite -view_join_unfold. iDestruct "H" as "($ & H & $ & $ & R')".
      rewrite (GPS_SWSharedReader_unfold ENC). iFrame "R'".
      iExists _, _, _. iDestruct "H" as "[$ %]". iPureIntro. lia.
  Qed.

  Lemma GPS_SWRaw_Reader_Read_val_dealloc IW P R R' vd t s v γ tid Vb E:
    ↑histN ⊆ E →
    {{{ GPS_Reader l t s v γ ∗ (⊒Vb → ▷ GPS_INV IW γ) ∗ P
        ∗ (▷ ∀ t' s', ⌜s ⊑ s' ∧ t ⊑ t'⌝ -∗
            (P -∗
              (F γ t' s' vd ={E}=∗ ⊒Vb ∗ GPS_SWSharedWriter t' s' vd γ ∗ R t' s') ∧
              (F_read γ t' s' vd ={E}=∗ False) ∧
              (IW l γ t' s' vd ={E}=∗ False)) ∧
            <obj> (∀ v',
                  (F_read γ t' s' v' ={E}=∗ F_read γ t' s' v' ∗ R' t' s' v') ∧
                  (F γ t' s' v' ={E}=∗ F γ t' s' v' ∗ R' t' s' v') ∧
                  (IW l γ t' s' v' ={E}=∗ IW l γ t' s' v' ∗ R' t' s' v'))) }}}
      !ᵃᶜ#l @ tid; E
    {{{ t' s' v', RET v'; ⌜s ⊑ s' ∧ t ⊑ t'⌝ ∗
        if (decide (v' = vd)) then l ↦ v' ∗ R t' s'
        else P ∗ R' t' s' v'
             ∗ GPS_Reader l t' s' v' γ ∗ (⊒Vb → ▷ GPS_INV IW γ) }}}.
  Proof.
    iIntros (SUB Φ) "(#R & I & P & VS) Post".
    rewrite -{1}view_join_unfold GPS_INV_eq.
    iAssert (⌜ ∃ γs γl : gname, γ = encode (γs, γl) ⌝)%I with "[R]"
      as %(γs & γl & ENC).
    { clear. rewrite GPS_Reader_eq. iDestruct "R" as (????) "_".
      iPureIntro. by do 2 eexists. }

    iApply (GPSRaw_Read_val_dealloc_non_ex IP l IW P R R' vd t s v γ γs γl true
              Vb tid E SUB ENC with "[VS $I $R $P]").
    { iIntros "!>" (??) "Le". iSpecialize ("VS" with "Le").
      iSplit; [rewrite bi.and_elim_l|by rewrite bi.and_elim_r].
      iIntros "P". iSpecialize ("VS" with "P").
      iSplit; [rewrite bi.and_elim_l|by rewrite bi.and_elim_r].
      iIntros "F". iMod ("VS" with "F") as "($ & SW & $)".
      rewrite (GPS_SWSharedWriter_unfold ENC). by iFrame. }
    iIntros "!>" (???) "[Le H]". iApply "Post". iFrame "Le".
    case decide => ?.
    - iDestruct "H" as "[$ $]".
    - rewrite -view_join_unfold. iDestruct "H" as "($ & $ & $ & $)".
  Qed.

  Lemma GPS_SWRaw_SharedWriter_CAS_int_view_strong
    IW (dropR: bool) orf or (vr: Z) (vw: val) t s v q γ P P' Q R tid Vb E :
    ↑histN ⊆ E → orf = Relaxed ∨ orf = AcqRel → or = Relaxed ∨ or = AcqRel →
    let VSC : vProp :=
      (<obj> ∀ t' s' v', ⌜s ⊑ s' ∧ t ⊑ t'⌝ -∗
                (F γ t' s' v' ∨ F_read γ t' s' v') -∗
                ⌜∃ vl, v' = #vl ∧ lit_comparable vr vl⌝)%I in
    let VS : vProp :=
      (▷ ∀ t' s', ⌜s ⊑ s' ∧ t ⊑ t'⌝ -∗
          (P -∗ F γ t' s' #vr ={E}=∗
            GPS_SWSharedWriter t' s' #vr γ ∗
            ∃ s'', ⌜s' ⊑ s''⌝ ∗
              (∀ t'' , ⌜(t' < t'')%positive⌝ -∗
                GPS_SWSharedWriter t'' s'' vw γ -∗
                (if dropR then GPS_SWSharedReader t'' s'' vw q γ else True) ={E}=∗
                  (<obj> (|={E}=> F_read γ t' s' #vr)) ∗
                  |={E}=> Q t'' s'' ∗ F γ t'' s'' vw) ))%I in
    let VSF: vProp :=
      (∀ t' s' (v: lit), ⌜s ⊑ s' ∧ t ⊑ t' ∧ lit_neq vr v⌝ -∗
          ▷ <obj> ((F_read γ t' s' #v ={E}=∗ F_read γ t' s' #v ∗ R t' s' v) ∧
                   (F γ t' s' #v ={E}=∗ F γ t' s' #v ∗ R t' s' v)))%I in
    {{{ GPS_SWSharedReader t s v q γ
        ∗ (⊒Vb → ▷ GPS_INV IW γ)
        ∗ ▷ VSC ∗ VS ∗ VSF ∗ P ∗ P'}}}
      CAS #l #vr vw orf or AcqRel @ tid; E
    {{{ (b: bool) t' s' (v': lit), RET #b;
        ⌜s ⊑ s'⌝ ∗
        ( (⌜b = true  ∧ v' = LitInt vr ∧ (t < t')%positive⌝
            ∗ ∃ V', ⊒V' ∗ ⎡ P V' ⎤ ∗ ⎡ P' V' ⎤ ∗
              (⎡ P V' ⎤ ={E}=∗ ⎡ (⊒Vb → ▷ GPS_INV IW γ) V' ⎤
                ∗ ∃ s'', ⌜s' ⊑ s''⌝
                ∗ (if dropR then True else GPS_SWSharedReader t' s'' vw q γ)
                ∗ if decide (AcqRel ⊑ or) then Q t' s'' else ▽{tid} Q t' s''))
        ∨ (⌜b = false ∧ lit_neq vr v' ∧ (t ≤ t')%positive⌝
            ∗ (⊒Vb → ▷ GPS_INV IW γ)
            ∗ GPS_SWSharedReader t' s' #v' q γ
            ∗ (if decide (AcqRel ⊑ orf) then R t' s' v' else ▽{tid} (R t' s' v'))
            ∗ P ∗ P') ) }}}.
  Proof.
    iIntros (SUB ORF OR VSC VS VSF Φ) "(R & I & Comp & VS & VSF & P & P') Post".
    rewrite -{1}view_join_unfold GPS_INV_eq {1}GPS_SWSharedReader_eq.
    iDestruct "R" as "[R C]". iDestruct "C" as (tx ζs Vs γs γl [ENC Letx]) "C".
    iCombine "P P' VS" as "PPVS".
    iDestruct (view_at_intro with "PPVS") as (V) "[#sV PPVS]".
    iApply (GPSRaw_CAS_int_write_view IP l IW true t tx ζs s v orf or
              vr vw γ _ _ q Vb V Vs E True%I R _ SUB ORF OR ENC
            with "[$Comp VSF $I $R C $sV]").
    { iFrame (Letx) "C". clear.
      setoid_rewrite bi.and_True. setoid_rewrite bi.True_and.
      iIntros (t' s' [] v' NE). by iApply "VSF". } clear VSC VSF.
    iIntros "!>" (b v' s' t' V' V'') "([%Les %LeV] & #sV'' & [C %] & CASE)".
    iApply ("Post" $! b t' s' v'). iFrame (Les).
    iDestruct "CASE" as "[CASE|(F & sVr & I & SR & R)]"; [iLeft|iRight].
    - iDestruct "CASE" as (tr Vr (-> & -> & ? & ? & LeVr & LeV'))
                          "(sVr & VS' & F' & SR)".
      have ?: (t ≤ t')%positive by lia.
      have LeV'' : V'' ⊑ V'.
      { clear -LeV' OR. destruct OR as [-> | ->]; [done|]. simpl in *. by subst. }
      have LeV2 : V ⊑ V' by solve_lat.

      iSplitR. { iPureIntro. do 2 (split; [done|]). lia. }
      iDestruct "PPVS" as "(P & P' & VS)".
      iSpecialize ("VS" $! tr s' with "[%//]"). clear VS.
      iExists V''. rewrite -2!view_at_unfold. iFrame "sV'' P P'".
      iIntros "P".
      iMod (view_at_mono_2 _ _ _ LeV2 with "VS [$P] [$F']")
        as "(W & %s'' & %Les'' & VS)".
      iMod ("VS'" with "[W] [%//]") as "(SRw & W & VS')".
      { by rewrite (GPS_SWSharedWriter_unfold ENC). }
      iSpecialize ("VS" $! t' with "[%//] [W]").
      { by rewrite (GPS_SWSharedWriter_unfold ENC). }

      iAssert (@{V''} GPS_SWSharedReader t' s'' vw q γ)%I with "[C SRw]" as "C".
      { rewrite (GPS_SWSharedReader_unfold ENC). iFrame "SRw".
        iExists tx, _, _. iFrame "C". iPureIntro. lia. }
      iAssert ((if dropR then True else GPS_SWSharedReader t' s'' vw q γ) ∗
               (@{V'} if dropR then GPS_SWSharedReader t' s'' vw q γ else True))%I
               with "[C]" as "[C1 C2]".
      { destruct dropR; [by iFrame "C"|].
        by iDestruct (view_at_elim with "sV'' C") as "$". }
      iMod ("VS" with "C2") as "[Fr >[Q F]]".
      rewrite view_at_objective_iff (view_at_objectively _ Vr)
              -view_at_unfold -view_join_unfold.
      iMod "Fr" as "Fr". iMod ("VS'" with "F Fr") as "$".
      iIntros "!>". iExists s''. iFrame (Les'') "C1".
      clear -LeV' OR. destruct OR as [-> | ->]; simpl.
      + iApply (acq_at_intro with "sVr Q").
      + iApply (view_at_elim with "[] Q"). simpl in LeV'. subst V'. iFrame "sV''".

    - iDestruct "F" as %(?&?&?). iSplitR; [done|]. rewrite view_join_unfold.
      iFrame "I R". iDestruct (view_at_elim with "sV PPVS") as "($ & $ & _)".
      rewrite (GPS_SWSharedReader_unfold ENC). iFrame "SR".
      iExists _, _, _. iFrame "C". iPureIntro. lia.
  Qed.

  Lemma GPS_SWRaw_SharedWriter_CAS_int_view_weak
    IW orf or (vr: Z) (vw: val) t s v γ P P' Q R tid Vb E :
    ↑histN ⊆ E → orf = Relaxed ∨ orf = AcqRel → or = Relaxed ∨ or = AcqRel →
    let VSC : vProp :=
      (<obj> ∀ t' s' v', ⌜s ⊑ s' ∧ t ⊑ t'⌝ -∗
                    (F γ t' s' v' ∨ F_read γ t' s' v' ∨ IW l γ t' s' v') -∗
                    ⌜∃ vl, v' = #vl ∧ lit_comparable vr vl⌝)%I in
    let VS : vProp :=
      (▷ ∀ t' s', ⌜s ⊑ s' ∧ t ⊑ t'⌝ -∗
          (P -∗ F γ t' s' #vr ={E}=∗ GPS_SWSharedWriter t' s' #vr γ ∗
              ∃ s'', ⌜s' ⊑ s''⌝ ∗
                (∀ t'' , ⌜(t' < t'')%positive⌝ -∗ GPS_SWSharedWriter t'' s'' vw γ ={E}=∗
                  (<obj> (|={E}=> F_read γ t' s' #vr)) ∗
                  |={E}=> Q t'' s'' ∗ F γ t'' s'' vw) ))%I in
    let VSF: vProp :=
      (∀ t' s', ⌜s ⊑ s' ∧ t ⊑ t'⌝ -∗
          ((P -∗ ▷ IW l γ t' s' #vr ={E}=∗ False)) ∧
        ∀ (v: lit), ⌜lit_neq vr v⌝ -∗
          ▷ <obj> ((F_read γ t' s' #v ={E}=∗ F_read γ t' s' #v ∗ R t' s' v) ∧
               (F γ t' s' #v ={E}=∗ F γ t' s' #v ∗ R t' s' v) ∧
               (IW l γ t' s' #v ={E}=∗ IW l γ t' s' #v ∗ R t' s' v)))%I in
    {{{ GPS_Reader l t s v γ
        ∗ (⊒Vb → ▷ GPS_INV IW γ)
        ∗ ▷ VSC ∗ VS ∗ VSF ∗ P ∗ P' }}}
      CAS #l #vr vw orf or AcqRel @ tid; E
    {{{ (b: bool) t' s' (v': lit), RET #b;
        ⌜s ⊑ s'⌝ ∗
        ( (⌜b = true  ∧ v' = LitInt vr ∧ (t < t')%positive⌝
            ∗ ∃ V', ⊒V' ∗ ⎡ P V' ⎤ ∗ ⎡ P' V' ⎤ ∗
              (⎡ P V' ⎤ ={E}=∗ ⎡ (⊒Vb → ▷ GPS_INV IW γ) V' ⎤
                ∗ ∃ s'', ⌜s' ⊑ s''⌝
                ∗ GPS_Reader l t' s'' vw γ
                ∗ if decide (AcqRel ⊑ or) then Q t' s'' else ▽{tid} Q t' s''))
        ∨ (⌜b = false ∧ lit_neq vr v' ∧ (t ≤ t')%positive⌝
            ∗ (⊒Vb → ▷ GPS_INV IW γ)
            ∗ GPS_Reader l t' s' #v' γ
            ∗ (if decide (AcqRel ⊑ orf) then R t' s' v' else ▽{tid} (R t' s' v'))
            ∗ P ∗ P') ) }}}.
  Proof.
    iIntros (SUB ORF OR VSC VS VSF Φ) "(R & I & Comp & VS & VSF & P & P') Post".
    rewrite -{1}view_join_unfold GPS_INV_eq.
    iCombine "P P' VS" as "PPVS".
    iDestruct (view_at_intro with "PPVS") as (V) "(#sV & P & PVS)".
    iAssert (⌜ ∃ γs γl : gname, γ = encode (γs, γl) ⌝)%I with "[R]"
      as %(γs & γl & ENC).
    { clear. rewrite GPS_Reader_eq. iDestruct "R" as (????) "_".
      iPureIntro. by do 2 eexists. }
    iApply (GPSRaw_CAS_int_write_view IP l IW false t t ∅ s v orf or
              vr vw γ _ _ 1 Vb V ∅ E (@{V} P)%I R _ SUB ORF OR ENC
            with "[$Comp VSF $P $I $R $sV]").
    { clear. iIntros (t' s') "Le". iSpecialize ("VSF" with "Le").
      iSplit; [rewrite bi.and_elim_l|by rewrite bi.and_elim_r].
      iIntros "P". iApply "VSF". iApply (view_at_elim with "sV P"). }
    clear VSC VSF.
    iIntros "!>" (b v' s' t' V' V'') "([%Les %LeV] & #sV'' & P & CASE)".
    iApply ("Post" $! b t' s' v'). iFrame (Les).
    iDestruct "CASE" as "[CASE|(F & sVr & I & SR & R)]"; [iLeft|iRight].
    - iDestruct "CASE" as (tr Vr (-> & -> & ? & ? & LeVr & LeV'))
                          "(sVr & VS' & F' & SR)".
      have ?: (t ≤ t')%positive by lia.
      have LeV'' : V'' ⊑ V'.
      { clear -LeV' OR. destruct OR as [-> | ->]; [done|]. simpl in *. by subst. }
      have LeV2 : V ⊑ V' by solve_lat.

      iSplitR. { iPureIntro. do 2 (split; [done|]). lia. }
      iDestruct "PVS" as "(P' & VS)".
      iSpecialize ("VS" $! tr s' with "[%//]"). clear VS.
      iExists V''. rewrite -2!view_at_unfold. iFrame "sV'' P P'". iIntros "P".
      iMod (view_at_mono_2 _ _ _ LeV2 with "VS [$P] [$F']")
        as "(W & %s'' & %Les'' & VS)".
      iMod ("VS'" with "[W] [%//]") as "(SRw & W & VS')".
      { by rewrite (GPS_SWSharedWriter_unfold ENC). }
      iMod ("VS" $! t' with "[%//] [W]") as "[Fr >[Q F]]".
      { by rewrite (GPS_SWSharedWriter_unfold ENC). }

      rewrite view_at_objective_iff (view_at_objectively _ Vr)
              -view_at_unfold -view_join_unfold.
      iMod "Fr" as "Fr". iMod ("VS'" with "F Fr") as "$".
      iIntros "!>". iExists s''. iFrame (Les'').
      iDestruct (view_at_elim with "sV'' SRw") as "$".
      clear -LeV' OR. destruct OR as [-> | ->]; simpl.
      + iApply (acq_at_intro with "sVr Q").
      + iApply (view_at_elim with "[] Q"). simpl in LeV'. subst V'. iFrame "sV''".
    - iDestruct "F" as %(?&?&?). iSplitR; [done|]. rewrite view_join_unfold.
      iFrame "I R SR". iDestruct (view_at_elim with "sV PVS") as "($ & _)".
      iApply (view_at_elim with "sV P").
  Qed.

  Lemma GPS_SWRaw_SharedWriter_CAS_int_strong
    IW (dropR: bool) orf or ow (vr: Z) (vw: val) t s v q γ P Q Q1 Q2 R tid Vb E
    E' (SUBE: E' ⊆ E):
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
         (P -∗ ▷ Q2 t' s' ={E}=∗ ▷ GPS_SWSharedWriter t' s' #vr γ ∗
            ∃ s'', ⌜s' ⊑ s''⌝ ∗
              (∀ t'' , ⌜(t' < t'')%positive⌝ -∗
                ▷ GPS_SWSharedWriter t'' s'' vw γ -∗
                (if dropR then ▷ GPS_SWSharedReader t'' s'' vw q γ else True) ={E}=∗
                  (<obj> (▷ Q1 t' s' ={E}=∗ ▷ F_read γ t' s' #vr)) ∗
                  |={E}[E']▷=> Q t'' s'' ∗ ▷ F γ t'' s'' vw)) ) ∧
        ▷ ∀ (v: lit), ⌜lit_neq vr v⌝ -∗
            <obj> ((F_read γ t' s' #v ={E}=∗ F_read γ t' s' #v ∗ R t' s' v) ∧
                   (F γ t' s' #v ={E}=∗ F γ t' s' #v ∗ R t' s' v)))%I in
    {{{ GPS_SWSharedReader t s v q γ
        ∗ (⊒Vb → ▷ GPS_INV IW γ)
        ∗ (▷ VSC)
        ∗ (if decide (AcqRel ⊑ ow) then VS else △{tid} VS)
        ∗ (if decide (AcqRel ⊑ ow) then P else △{tid} P) }}}
      CAS #l #vr vw orf or ow @ tid; E
    {{{ (b: bool) t' s' (v': lit), RET #b;
        (⊒Vb → ▷ GPS_INV IW γ) ∗ ⌜s ⊑ s'⌝
        ∗ ( (⌜b = true  ∧ v' = LitInt vr ∧ (t < t')%positive⌝
              ∗ (if dropR then True else GPS_SWSharedReader t' s' vw q γ)
              ∗ if decide (AcqRel ⊑ or) then Q t' s' else ▽{tid} Q t' s')
          ∨ (⌜b = false ∧ lit_neq vr v' ∧ (t ≤ t')%positive⌝
              ∗ GPS_SWSharedReader t' s' #v' q γ
              ∗ (if decide (AcqRel ⊑ orf) then R t' s' v' else ▽{tid} (R t' s' v'))
              ∗ (if decide (AcqRel ⊑ ow) then P else △{tid} P) ) ) }}}.
  Proof.
    iIntros (SUB ORF OR OW VSC VS Φ) "(R & I & Comp & VS & P) Post".
    rewrite -{1}view_join_unfold GPS_INV_eq {1}GPS_SWSharedReader_eq.
    iDestruct "R" as "[R C]". iDestruct "C" as (tx ζs Vs γs γl [ENC Letx]) "C".
    iCombine "P VS" as "PVS".
    destruct OW as [-> | ->]; simpl.
    - rewrite rel_sep. iApply (wp_rel_revert_view_at with "PVS").
      iIntros (Vrel) "#Hrel [P VS] #sVrel".
      iDestruct (view_at_intro True%I with "[//]") as (V) "[#sV _]".

      iApply (GPSRaw_CAS_int_strong_write IP l _ t tx q s v orf or _ vr vw
                γ _ _ _ V Vrel Vb _ _ E E' P Q Q1 Q2 R dropR Letx SUB SUBE ORF OR
            with "[$sV Hrel P $Comp VS $I $R $C]"); [by left|exact ENC|..].
      { simpl. iFrame "Hrel P". iApply (view_at_mono with "VS"); [done|].
        iIntros "VS" (t' s') "Le". iSpecialize ("VS" with "Le").
        iSplit; [rewrite bi.and_elim_l|by rewrite bi.and_elim_r].
        iDestruct "VS" as "[$ VS]".
        iIntros "P Q". iMod ("VS" with "P Q") as "[W VS]".
        iIntros "!>". iSplitL "W".
        { iIntros "!>". by rewrite (GPS_SWSharedWriter_unfold ENC). }
        iDestruct "VS" as (s'' Les'') "VS".
        iExists s''. iFrame (Les''). iIntros (t'') "Le W".
        iSpecialize ("VS" with "Le [W]").
        { iIntros "!>". by rewrite (GPS_SWSharedWriter_unfold ENC). }
        clear -ENC. iIntros "SR". iApply "VS". destruct dropR; [|done].
        iNext. by rewrite (GPS_SWSharedReader_unfold ENC). } clear VS VSC.

      iIntros "!>" (b v' s' t' V' V'') "([%Lets %LeV] & #sV'' & I & CASE)".
      rewrite view_join_unfold.
      iApply ("Post" $! b t' s' v'). iFrame (Lets) "I".
      iDestruct "CASE" as "[(F & C & GR & sVw & Q)|(F & GR & sVr & C & R' & P)]"; simpl.
      + iLeft. iDestruct "F" as %(? & ? & ? & LeV').
        iSplit; [done|]. iSplitL "GR C".
        { destruct dropR; [done|]. rewrite (GPS_SWSharedReader_unfold ENC).
          iFrame "GR". iExists _, _, _. iFrame "C". iPureIntro. lia. }
        destruct OR as [-> | ->]; simpl.
        * iApply (acq_at_intro with "sVw Q").
        * iApply (view_at_elim with "[sV'' sVw] Q").
          iDestruct "sVw" as %?. by iApply (monPred_in_mono with "sV''").
      + iRight. iDestruct "F" as %(?&?&?). iSplit; [done|]. iSplitL "GR C".
        { rewrite (GPS_SWSharedReader_unfold ENC).
          iFrame "GR". iExists _, _, _. iFrame "C". iPureIntro. lia. }
        iDestruct (rel_at_intro with "Hrel P") as "$".
        destruct ORF as [-> | ->]; simpl.
        * iApply (acq_at_intro with "sVr R'").
        * iApply (view_at_elim with "sVr R'").

    - iDestruct (view_at_intro with "PVS") as (V) "[#sV [P VS]]".
      iApply (GPSRaw_CAS_int_strong_write IP l _ t tx q s v orf or _ vr vw
                γ _ _ _ V ∅ Vb _ _ E E' P Q Q1 Q2 R dropR Letx SUB SUBE ORF OR
            with "[$sV P $Comp VS $I $R $C]"); [by right|exact ENC|..].
      { simpl. iSplit; [done|]. iFrame "P".
        iApply (view_at_mono with "VS"); [done|].
        iIntros "VS" (t' s') "Le". iSpecialize ("VS" with "Le").
        iSplit; [rewrite bi.and_elim_l|by rewrite bi.and_elim_r].
        iDestruct "VS" as "[$ VS]".
        iIntros "P Q". iMod ("VS" with "P Q") as "[W VS]".
        iIntros "!>". iSplitL "W".
        { iIntros "!>". by rewrite (GPS_SWSharedWriter_unfold ENC). }
        iDestruct "VS" as (s'' Les'') "VS".
        iExists s''. iFrame (Les''). iIntros (t'') "Le W".
        iSpecialize ("VS" with "Le [W]").
        { iIntros "!>". by rewrite (GPS_SWSharedWriter_unfold ENC). }
        iIntros "SR". iApply "VS". destruct dropR; [|done].
        iNext. by rewrite (GPS_SWSharedReader_unfold ENC). } clear VS VSC.

      iIntros "!>" (b v' s' t' V' V'') "([%Lets %LeV] & #sV'' & I & CASE)".
      rewrite view_join_unfold.
      iApply ("Post" $! b t' s' v'). iFrame (Lets) "I".
      iDestruct "CASE" as "[(F & C & GR & sVw & Q)|(F & GR & sVr & C & R' & P)]"; simpl.
      + iLeft. iDestruct "F" as %(? & ? & ? & LeV').
        iSplit; [done|]. iSplitL "GR C".
        { destruct dropR; [done|]. rewrite (GPS_SWSharedReader_unfold ENC).
          iFrame "GR". iExists _, _, _. iFrame "C". iPureIntro. lia. }
        destruct OR as [-> | ->]; simpl.
        * iApply (acq_at_intro with "sVw Q").
        * iApply (view_at_elim with "[sV'' sVw] Q").
          iDestruct "sVw" as %?. by iApply (monPred_in_mono with "sV''").
      + iRight. iDestruct "F" as %(?&?&?). iSplit; [done|]. iSplitL "GR C".
        { rewrite (GPS_SWSharedReader_unfold ENC).
          iFrame "GR". iExists _, _, _. iFrame "C". iPureIntro. lia. }
        iDestruct (view_at_elim with "sV P") as "$".
        destruct ORF as [-> | ->]; simpl.
        * iApply (acq_at_intro with "sVr R'").
        * iApply (view_at_elim with "sVr R'").
  Qed.

  Lemma GPS_SWRaw_SharedWriter_CAS_int_weak
    IW orf or ow (vr: Z) (vw: val) t s v γ P Q Q1 Q2 R tid Vb E E'
    (SUBE: E' ⊆ E):
    ↑histN ⊆ E →
    orf = Relaxed ∨ orf = AcqRel →
    or = Relaxed ∨ or = AcqRel → ow = Relaxed ∨ ow = AcqRel →
    let VSC : vProp :=
      (<obj> ∀ t' s' v', ⌜s ⊑ s' ∧ t ⊑ t'⌝ -∗
                (F γ t' s' v' ∨ F_read γ t' s' v' ∨ IW l γ t' s' v') -∗
                ⌜∃ vl, v' = #vl ∧ lit_comparable vr vl⌝)%I in
    let VS : vProp :=
      (∀ t' s', ⌜s ⊑ s' ∧ t ⊑ t'⌝ -∗
        ((P -∗ ▷ IW l γ t' s' #vr ={E}=∗ False) ∧
         ((<obj> (▷ F γ t' s' #vr ={E}=∗ ▷ Q1 t' s' ∗ ▷ Q2 t' s')) ∗
          (P -∗ ▷ Q2 t' s' ={E}=∗ ▷ GPS_SWSharedWriter t' s' #vr γ ∗
            ∃ s'', ⌜s' ⊑ s''⌝ ∗
              (∀ t'' , ⌜(t' < t'')%positive⌝ -∗
                ▷ GPS_SWSharedWriter t'' s'' vw γ ={E}=∗
                  (<obj> (▷ Q1 t' s' ={E}=∗ ▷ F_read γ t' s' #vr)) ∗
                  |={E}[E']▷=> Q t'' s'' ∗ ▷ F γ t'' s'' vw))) ) ∧
        ▷ (∀ (v: lit), ⌜lit_neq vr v⌝ -∗
              <obj> ((F_read γ t' s' #v ={E}=∗ F_read γ t' s' #v ∗ R t' s' v) ∧
                     (F γ t' s' #v ={E}=∗ F γ t' s' #v ∗ R t' s' v) ∧
                     (IW l γ t' s' #v ={E}=∗ IW l γ t' s' #v ∗ R t' s' v))))%I in
    {{{ GPS_Reader l t s v γ
        ∗ (⊒Vb → ▷ GPS_INV IW γ)
        ∗ (▷ VSC)
        ∗ (if decide (AcqRel ⊑ ow) then VS else △{tid} VS)
        ∗ (if decide (AcqRel ⊑ ow) then P else △{tid} P) }}}
      CAS #l #vr vw orf or ow @ tid; E
    {{{ (b: bool) t' s' (v': lit), RET #b;
        (⊒Vb → ▷ GPS_INV IW γ) ∗ ⌜s ⊑ s'⌝
        ∗ ( (⌜b = true  ∧ v' = LitInt vr ∧ (t < t')%positive⌝
              ∗ GPS_Reader l t' s' vw γ
              ∗ if decide (AcqRel ⊑ or) then Q t' s' else ▽{tid} Q t' s')
          ∨ (⌜b = false ∧ lit_neq vr v' ∧ (t ≤ t')%positive⌝
              ∗ GPS_Reader l t' s' #v' γ
              ∗ (if decide (AcqRel ⊑ orf) then R t' s' v' else ▽{tid} (R t' s' v'))
              ∗ (if decide (AcqRel ⊑ ow) then P else △{tid} P) ) ) }}}.
  Proof.
    iIntros (SUB ORF OR OW VSC VSW Φ) "(R & I & Comp & VS & P) Post".
    rewrite -{1}view_join_unfold GPS_INV_eq.
    iAssert (⌜ ∃ γs γl : gname, γ = encode (γs, γl) ⌝)%I with "[R]"
      as %(γs & γl & ENC).
    { clear. rewrite GPS_Reader_eq. iDestruct "R" as (????) "_".
      iPureIntro. by do 2 eexists. }
    iCombine "P VS" as "PVS".
    destruct OW as [-> | ->]; simpl.
    - rewrite rel_sep. iApply (wp_rel_revert_view_at with "PVS").
      iIntros (Vrel) "#Hrel [P VS] #sVrel".
      iDestruct (view_at_intro True%I with "[//]") as (V) "[#sV _]".

      iApply (GPSRaw_CAS_int_weak_write IP l _ t s v orf or _ vr vw
                γ _ _ V Vrel Vb _ E E' P Q Q1 Q2 R SUB SUBE ORF OR
            with "[$sV Hrel P $Comp VS $I $R]"); [by left|exact ENC|..].
      { simpl. iFrame "Hrel P". iApply (view_at_mono with "VS"); [done|].
        iIntros "VS" (t' s') "Le". iSpecialize ("VS" with "Le").
        iSplit; [rewrite bi.and_elim_l|by rewrite bi.and_elim_r].
        iSplit; [by rewrite bi.and_elim_l|rewrite bi.and_elim_r].
        iDestruct "VS" as "[$ VS]".
        iIntros "P Q". iMod ("VS" with "P Q") as "[W VS]".
        iIntros "!>". iSplitL "W".
        { iIntros "!>". by rewrite (GPS_SWSharedWriter_unfold ENC). }
        iDestruct "VS" as (s'' Les'') "VS".
        iExists s''. iFrame (Les''). iIntros (t'') "Le W".
        iApply ("VS" with "Le [W]").
        iIntros "!>". by rewrite (GPS_SWSharedWriter_unfold ENC). }
      clear VSW VSC.

      iIntros "!>" (b v' s' t' V' V'') "([%Lets %LeV] & #sV'' & I & CASE)".
      rewrite view_join_unfold.
      iApply ("Post" $! b t' s' v'). iFrame (Lets) "I".
      iDestruct "CASE" as "[(F & GR & sVw & Q)|(F & GR & sVr & R' & P)]"; simpl.
      + iLeft. iDestruct "F" as %(? & ? & ? & LeV').
        iSplit; [done|]. iFrame "GR".
        destruct OR as [-> | ->]; simpl.
        * iApply (acq_at_intro with "sVw Q").
        * iApply (view_at_elim with "[sV'' sVw] Q").
          iDestruct "sVw" as %?. by iApply (monPred_in_mono with "sV''").
      + iRight. iDestruct "F" as %(?&?&?). iSplit; [done|]. iFrame "GR".
        iDestruct (rel_at_intro with "Hrel P") as "$".
        destruct ORF as [-> | ->]; simpl.
        * iApply (acq_at_intro with "sVr R'").
        * iApply (view_at_elim with "sVr R'").

    - iDestruct (view_at_intro with "PVS") as (V) "[#sV [P VS]]".
      iApply (GPSRaw_CAS_int_weak_write IP l _ t s v orf or _ vr vw
                γ _ _ V ∅ Vb _ E E' P Q Q1 Q2 R SUB SUBE ORF OR
            with "[$sV P $Comp VS $I $R]"); [by right|exact ENC|..].
      { simpl. iSplit; [done|]. iFrame "P".
        iApply (view_at_mono with "VS"); [done|].
        iIntros "VS" (t' s') "Le". iSpecialize ("VS" with "Le").
        iSplit; [rewrite bi.and_elim_l|by rewrite bi.and_elim_r].
        iSplit; [by rewrite bi.and_elim_l|rewrite bi.and_elim_r].
        iDestruct "VS" as "[$ VS]".
        iIntros "P Q". iMod ("VS" with "P Q") as "[W VS]".
        iIntros "!>". iSplitL "W".
        { iIntros "!>". by rewrite (GPS_SWSharedWriter_unfold ENC). }
        iDestruct "VS" as (s'' Les'') "VS".
        iExists s''. iFrame (Les''). iIntros (t'') "Le W".
        iApply ("VS" with "Le [W]").
        iIntros "!>". by rewrite (GPS_SWSharedWriter_unfold ENC). }
      clear VSW VSC.

      iIntros "!>" (b v' s' t' V' V'') "([%Lets %LeV] & #sV'' & I & CASE)".
      rewrite view_join_unfold.
      iApply ("Post" $! b t' s' v'). iFrame (Lets) "I".
      iDestruct "CASE" as "[(F & GR & sVw & Q)|(F & GR & sVr & R' & P)]"; simpl.
      + iLeft. iDestruct "F" as %(? & ? & ? & LeV').
        iSplit; [done|]. iFrame "GR".
        destruct OR as [-> | ->]; simpl.
        * iApply (acq_at_intro with "sVw Q").
        * iApply (view_at_elim with "[sV'' sVw] Q").
          iDestruct "sVw" as %?. by iApply (monPred_in_mono with "sV''").
      + iRight. iDestruct "F" as %(?&?&?). iSplit; [done|]. iFrame "GR".
        iDestruct (view_at_elim with "sV P") as "$".
        destruct ORF as [-> | ->]; simpl.
        * iApply (acq_at_intro with "sVr R'").
        * iApply (view_at_elim with "sVr R'").
  Qed.
End SingleWriter.

Global Instance: Params (@GPS_INV) 5 := {}.
Global Instance: Params (@GPS_SWWriter) 5 := {}.
Global Instance: Params (@GPS_SWSharedWriter) 5 := {}.
Global Instance: Params (@GPS_SWSharedReader) 5 := {}.

Section GName.
  Context `{!noprolG Σ, !gpsG Σ Prtcl, !atomicG Σ} (l : loc)
          (IP : gname → interpO Σ Prtcl).
  Local Notation iProp := (iProp Σ).
  Local Notation vProp := (vProp Σ).

  Lemma GPS_SWRaw_Init_vs_gname b v s (Q: time → gname → vProp) E :
    l ↦ v -∗
    (∀ t γ, GPS_SWWriter l t s v γ ={E}=∗ ▷?b (IP γ) true l γ t s v ∗ Q t γ)
    ={E}=∗ ∃ γ t, ∀ IW, ▷?b GPS_INV (IP γ) l IW γ ∗ Q t γ.
  Proof.
    iIntros "P F".
    iMod (GPSRaw_Init_strong_vs_gname l IP b v s _ Q with "P [F]") as (t γ) "F".
    { iIntros (γl γs t V) "SS W". iApply "F".
      iApply (GPS_SWWriter_from_SW_singleton with "SS W"). }
    iIntros "!>". iExists γ, t. iIntros (IW). rewrite GPS_INV_eq. by iApply "F".
  Qed.
End GName.

Section Dual.
  Context `{!noprolG Σ, !gpsG Σ Prtcl1, !gpsG Σ Prtcl2, !atomicG Σ}
          (l1 l2 : loc)
          (IP1 : gname → interpO Σ Prtcl1)
          (IP2 : gname → interpO Σ Prtcl2).
  Local Notation iProp := (iProp Σ).
  Local Notation vProp := (vProp Σ).

  Lemma GPS_SWRaw_Init_vs_strong_2 b v1 v2 (s1 : Prtcl1) (s2: Prtcl2)
    (Q: time → time → gname → gname → vProp) E :
    l1 ↦ v1 -∗ l2 ↦ v2 -∗
    (∀ t1 t2 γ1 γ2, GPS_SWWriter l1 t1 s1 v1 γ1 -∗
          GPS_SWWriter l2 t2 s2 v2 γ2 ={E}=∗ ▷?b (IP1 γ2) true l1 γ1 t1 s1 v1
          ∗ ▷?b (IP2 γ1) true l2 γ2 t2 s2 v2 ∗ Q t1 t2 γ1 γ2)
    ={E}=∗ ∃ γ1 γ2 t1 t2, ∀ IW1 IW2,
          ▷?b GPS_INV (IP1 γ2) l1 IW1 γ1 ∗
          ▷?b GPS_INV (IP2 γ1) l2 IW2 γ2 ∗ Q t1 t2 γ1 γ2.
  Proof.
    iIntros "O1 O2 F".
    iMod (GPSRaw_Init_strong_vs_2 l1 l2 IP1 IP2 b v1 v2 s1 s2 _ Q
            with "O1 O2 [F]") as (t1 t2 γ1 γ2) "I".
    { iIntros (γl1 γs1 t1 V1 γl2 γs2 t2 V2) "SS1 W1 SS2 W2".
      iApply ("F" with "[SS1 W1]").
      - iApply (GPS_SWWriter_from_SW_singleton with "SS1 W1").
      - iApply (GPS_SWWriter_from_SW_singleton with "SS2 W2"). }
    iIntros "!>". iExists γ1, γ2, t1, t2. iIntros (IW1 IW2).
    rewrite 2!GPS_INV_eq. by iApply "I".
  Qed.
End Dual.

Section Extra.
  Context `{!noprolG Σ, !gpsG Σ Prtcl, !atomicG Σ}.
  Implicit Types (IP : interpO Σ Prtcl).

  Global Instance GPS_INV_ne l γ :
    NonExpansive2 (λ IP IW, GPS_INV IP l IW γ).
  Proof. move => ???????. rewrite 2!GPS_INV_eq. by apply gps_inv_ne. Qed.

  Lemma GPS_INV_proper:
    Proper ((≡) ==> (=) ==> (≡) ==> (eq) ==> (≡)) GPS_INV.
  Proof.
    move => ????????????. subst. rewrite 2!GPS_INV_eq.
    by apply gps_inv_proper.
  Qed.
End Extra.
