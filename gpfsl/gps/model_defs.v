From stdpp Require Import countable.
From iris.bi Require Import fractional.
From iris.proofmode Require Import proofmode.

From gpfsl.algebra Require Import to_agree.
From gpfsl.base_logic Require Import base_lifting.
From gpfsl.logic Require Import atomic_preds.
From gpfsl.gps Require Import cbends.
From gpfsl.gps Require Export cmras.
From gpfsl.lang Require Export lang.

Require Import iris.prelude.options.

Local Existing Instance gps_inG.

Implicit Types (ζ : absHist)
               (l : loc) (t : time) (v : val) (V : view) (γ : gname).

(* States disconnected from the exclusive write tx must be final, where
  disconnected means that there is an unused timestamp td in between. *)
Definition disconnected_from (tx t : time) ζ :=
  ∃ (td: time), (tx ≤ td)%positive ∧ (td ≤ t)%positive ∧ ζ !! td = None.
Definition SWConnect ζ (tx : time) : Prop :=
  ∀ t, is_Some (ζ !! t) → (tx ≤ t)%positive → ¬ disconnected_from tx t ζ.

Lemma SWConnect_singleton t m: SWConnect {[t := m]} t.
Proof.
  move => t' [m' /lookup_singleton_Some [? ?]] Le [td [? [? NIN]]].
  subst t' m'. have ?: td = t by apply : anti_symm. subst td.
  by rewrite lookup_insert in NIN.
Qed.

Lemma SWConnect_cbends_le ζ (tx t t': time) m m'
  (MAX: no_earlier_time ζ t) :
  SWConnect ζ tx → (tx ≤ t)%positive → (tx ≤ t')%positive → ζ !! t = Some m →
  cbends ζ !! t' = Some m' → (t ≤ t')%positive.
Proof.
  move => SC Letx Letx' Eqt /map_filter_lookup_Some [Eqt' /= NADJ].
  case (decide (t ≤ t')%positive) => [//|/Pos.lt_nle NLe]. exfalso.
  apply (SC t); [by eexists|done|].
  exists (t' + 1)%positive. repeat split.
  - etrans; [apply Letx'|]. lia.
  - rewrite Pos.add_1_r. by apply Pos.le_succ_l.
  - destruct (ζ !! (t' + 1)%positive) as [m1|] eqn:Eq1; [|done].
    exfalso. apply (NADJ (t'+ 1)%positive m1 Eq1); [lia|done].
Qed.

Section sorted.
Context {Prtcl: protocolT}.
Implicit Types (μ : time → Prtcl) (χ : stateT Prtcl).

(* μ assigns write events (identified by timestamps) to protocol states *)
(* μ must be monotone. *)
Definition stsorted χ :=
  ∀ (t1 t2 : time) e1 e2,
  χ !! t1 = Some e1 → χ !! t2 = Some e2 → (t1 ≤ t2)%positive → e1 ⊑ e2.

(* TODO: finality is too strong, can we weaken it? *)
Definition final_st (s : Prtcl) := ∀ s', s' ⊑ s.
(* Final say that anything disconnected from the exclusive write must be final. *)
Definition FinalInv μ ζ tx :=
  ∀ t, is_Some (ζ !! t) → disconnected_from tx t ζ → final_st (μ t).

Lemma FinalInv_mono μ ζ t1 t2 (LE: (t1 ≤ t2)%positive):
  FinalInv μ ζ t1 → FinalInv μ ζ t2.
Proof.
  move => FIN t IS [td [Le Le']]. apply FIN; [done|].
  exists td. split; [|done]. by etrans.
Qed.

Global Instance stsorted_mono : Proper ((⊆) ==> (flip impl)) (stsorted).
Proof. move => ??? FS ??????. apply FS; by eapply lookup_weaken. Qed.
End sorted.

Notation interpO Σ Prtcl
  := (bool -d> loc -d> gname -d> time -d> pr_stateT Prtcl -d> val -d> vPropO Σ).
Notation interpCasO Σ Prtcl
  := (loc -d> gname -d> time -d> pr_stateT Prtcl -d> val -d> vPropO Σ).

Section to_state.
Context {Prtcl: protocolT}.
Implicit Types (μ : time → Prtcl) (χ : stateT Prtcl).
(* The ghost state of the GPS protocol stores the protocol states associated
  with the write event in the history [ζ] identified by the timestamp [t].
  This is already stored in [μ], but the ghost state makes sure it's monotone. *)
Definition toState μ ζ : stateT Prtcl := map_imap (λ t _, Some (μ t)) ζ.

Lemma toState_singleton_lookup μ ζ t svV :
  {[t := svV]} ⊆ toState μ ζ ↔ toState μ ζ !! t = Some svV.
Proof. apply : map_singleton_subseteq_l. Qed.

Lemma toState_lookup_state μ ζ t s :
  toState μ ζ !! t = Some s → μ t = s.
Proof. rewrite map_lookup_imap bind_Some => [[? [_ Hv]]]. by simplify_eq. Qed.

Lemma toState_lookup_message μ ζ t s :
  toState μ ζ !! t = Some s → ∃ vV, ζ !! t = Some vV.
Proof. rewrite map_lookup_imap bind_Some. move => [m [? Hv]]. by eexists. Qed.

Lemma toState_lookup_state_inv μ ζ t m :
  ζ !! t = Some m → toState μ ζ !! t = Some (μ t).
Proof. by rewrite map_lookup_imap => ->. Qed.

Lemma toState_insert μ ζ t m s :
  toState (<[t:=s]> μ) (<[t:=m]> ζ) = <[t:= s]> (toState μ ζ).
Proof.
  apply map_eq => t'. rewrite /toState map_lookup_imap.
  case (decide (t' = t)) => [->|?].
  - by rewrite 2!lookup_insert fn_lookup_insert /=.
  - rewrite !lookup_insert_ne // map_lookup_imap.
    destruct (ζ !! t') as [m'|] eqn:Eqt'; rewrite Eqt'; last done.
    rewrite /= fn_lookup_insert_ne //.
Qed.

End to_state.

Section Definitions.
  Context `{!noprolG Σ, !gpsG Σ Prtcl, !atomicG Σ}
          (IP : interpO Σ Prtcl) (IW: interpCasO Σ Prtcl)
          (l : loc).
  Local Notation iProp := (iProp Σ).
  Local Notation vProp := (vProp Σ).
  Implicit Types
    (s : pr_stateT Prtcl) (χ : stateT Prtcl) (μ : time → pr_stateT Prtcl).

  Notation F := (IP true l).        (* full interp *)
  Notation F_read := (IP false l).  (* read interp *)

  (* full resources are available at BEs (block ends)
    that are after the exwr (exclusive write) identified by tx *)
  Definition gps_res (π : time → val → vProp) ζ : vProp :=
    ([∗ map] t ↦ m ∈ ζ, @{m.2} π t m.1)%I.

  (* Block-ends have F or IW *)
  Definition resBE γ μ ζ tx :=
    gps_res (λ t v, if (decide (tx ≤ t)%positive)
                    then F γ t (μ t) v
                    else IW l γ t(μ t) v)%I
            (cbends ζ).

  (* The rest has something *)
  Definition resD γ μ ζ tx :=
    gps_res (λ t v, if (decide (tx ≤ t)%positive)
                    then F γ t (μ t) v ∨ F_read γ t (μ t) v
                    else F γ t (μ t) v ∨ F_read γ t (μ t) v ∨ IW l γ t (μ t) v)%I
            (ζ ∖ (cbends ζ)).

  Definition gps_own γ χ : vProp := ⎡ own γ (stateMap_auth χ) ⎤.
  Definition gps_snap γ χ : vProp := ⎡ own γ (stateMap_frag χ) ⎤.

  Definition gps_inv γ (bs : bool) : vProp :=
    ∃ μ γs γl ζ (tx : time),
      ⌜ γ = encode (γs, γl) ⌝
      ∗ gps_own γs (toState μ ζ)
      ∗ AtomicPtsToX l γl tx ζ (if bs then SingleWriter else ConcurrentWriter)
      ∗ resBE γ μ ζ tx ∗ resD γ μ ζ tx
      ∗ ⌜ FinalInv μ ζ tx ∧ stsorted (toState μ ζ)
          ∧ if bs then SWConnect ζ tx
            else ∀ t, is_Some (ζ !! t) → tx ⊑ t ⌝.

  Definition PrtSeen (t : time) s v γ : vProp :=
    ∃ γs γl V,
      ⌜ γ = encode (γs, γl) ⌝
      ∗ gps_snap γs {[t := s]}
      ∗ l sn⊒{γl} {[t := (v,V)]} .

  Definition PrtSync (t: time) s v γ : vProp :=
    ∃ γs γl V,
      ⌜ γ = encode (γs, γl) ⌝
      ∗ gps_snap γs {[t := s]}
      ∗ l sy⊒{γl} {[t := (v,V)]} .

  Definition GPS_Reader_def t s v γ : vProp := PrtSeen t s v γ.
  Definition GPS_Reader_aux : seal (@GPS_Reader_def). Proof. by eexists. Qed.
  Definition GPS_Reader := unseal (@GPS_Reader_aux).
  Definition GPS_Reader_eq : @GPS_Reader = _ := seal_eq _.
End Definitions.

Global Instance: Params (@gps_inv) 5 := {}.
Global Instance: Params (@PrtSeen) 5 := {}.
Global Instance: Params (@PrtSync) 5 := {}.
Global Instance: Params (@GPS_Reader) 5 := {}.

Section Properties.
  Context `{!noprolG Σ, !gpsG Σ Prtcl, !atomicG Σ}
          (IP : interpO Σ Prtcl)
          (l : loc).
  Local Notation iProp := (iProp Σ).
  Local Notation vProp := (vProp Σ).
  Implicit Types
    (s : pr_stateT Prtcl) (χ : stateT Prtcl) (μ : time → pr_stateT Prtcl).

  Notation F := (IP true l).        (* full interp *)
  Notation F_read := (IP false l).  (* read interp *)

  (** Instances *)
  Global Instance PrtSeen_persistent t s v γ : Persistent (PrtSeen l t s v γ) := _.
  Global Instance PrtSeen_timeless t s v γ : Timeless (PrtSeen l t s v γ) := _.
  Global Instance PrtSync_persistent t s v γ : Persistent (PrtSync l t s v γ) := _.
  Global Instance PrtSync_timeless t s v γ : Timeless (PrtSync l t s v γ) := _.

  Global Instance gps_res_objective π ζ : Objective (gps_res π ζ : vProp) := _.

  Global Instance gps_inv_ne n γ bs :
    Proper (dist n ==> dist n ==> dist n) (λ IP IW, gps_inv IP IW l γ bs).
  Proof.
    move => f1 f2 EQ fw1 fw2 EQ2.
    repeat apply bi.exist_ne => ?. repeat (apply bi.sep_ne; [done|]).
    rewrite /resBE /resD /gps_res.
    repeat apply bi.sep_ne; [..|done];
      (apply big_opM_ne => ? vV ?;
        case decide => ?//; apply view_at_ne; try apply EQ);
      rewrite ?monPred_at_or; repeat (apply bi.or_ne; apply EQ).
    + apply EQ2.
    + apply bi.or_ne; [apply EQ|apply bi.or_ne; [apply EQ|apply EQ2]].
  Qed.

  Lemma gps_inv_proper :
    Proper ((≡) ==> (≡) ==> (=) ==> (=) ==> (=) ==> (≡)) gps_inv.
  Proof.
    move => ?? Eq1 ?? Eq2 ?? ???????. subst.
    do 5 apply bi.exist_proper => ?. do 3 (apply bi.sep_proper; [done|]).
    apply bi.sep_proper; last (apply bi.sep_proper; [|done]).
    - apply big_sepM_proper => ? vV ? /=. apply view_at_proper; [done|].
      case decide => ?; [apply Eq1|apply Eq2].
    - apply big_sepM_proper => ? vV ? /=. apply view_at_proper; [done|].
      case decide => ? /=; apply bi.or_proper;
        try apply bi.or_proper; try apply Eq1; try apply Eq2.
  Qed.

  Global Instance GPS_Reader_persistent t s v γ :
    Persistent (GPS_Reader l t s v γ).
  Proof. rewrite GPS_Reader_eq. by apply _. Qed.
  Global Instance GPS_Reader_timeless t s v γ : Timeless (GPS_Reader l t s v γ).
  Proof. rewrite GPS_Reader_eq. by apply _. Qed.

  (** Ghost rules *)
  Lemma gps_snap_mono γ χ χ' :
    χ' ⊆ χ → gps_snap γ χ ⊢ gps_snap γ χ'.
  Proof.
    intros. by apply embed_mono, own_mono, auth_frag_mono, to_agreeM_included.
  Qed.
  Lemma gps_snap_mono_singleton γ χ t s :
    χ !! t = Some s → gps_snap γ χ ⊢ gps_snap γ {[t := s]}.
  Proof. intros. by apply gps_snap_mono, map_singleton_subseteq_l. Qed.

  Lemma gps_own_snap γ χ :
    gps_own γ χ ⊢ gps_snap γ χ.
  Proof. by apply embed_mono, own_mono, cmra_included_r. Qed.
  Lemma gps_own_snap_singleton γ χ t s :
    χ !! t = Some s → gps_own γ χ ⊢ gps_snap γ {[t := s]}.
  Proof.
    intros. etrans; [apply gps_own_snap|]. by apply gps_snap_mono_singleton.
  Qed.
  Lemma gps_own_snap_subseteq γ χ χ' :
    χ' ⊆ χ → gps_own γ χ ⊢ gps_snap γ χ'.
  Proof. intros. etrans; [apply gps_own_snap|by apply gps_snap_mono]. Qed.

  Lemma gps_own_alloc' χ : ⊢ |==> ∃ γ, gps_own γ χ.
  Proof.
    rewrite -embed_exist -embed_bupd.
    apply embed_emp_valid, own_alloc, auth_both_valid_discrete.
    split; [done|]. by apply to_agreeM_valid.
  Qed.
  Lemma gps_own_alloc χ : ⊢ |==> ∃ γ, gps_own γ χ ∗ gps_snap γ χ.
  Proof.
    iMod (gps_own_alloc' χ) as (γ) "O".
    iExists γ. iDestruct (gps_own_snap with "O") as "#$". by iFrame.
  Qed.

  Lemma gps_own_insert' γ χ t s (FRESH: χ !! t = None) :
    gps_own γ χ ==∗ gps_own γ (<[t := s]> χ).
  Proof.
    rewrite -embed_bupd.
    by apply embed_mono, own_update, auth_update, to_agreeM_local_update_insert.
  Qed.
  Lemma gps_own_insert γ χ t s (FRESH: χ !! t = None) :
    gps_own γ χ ==∗ gps_own γ (<[t := s]> χ) ∗ gps_snap γ ({[ t := s ]}).
  Proof.
    iIntros "O". iMod (gps_own_insert' with "O") as "O'"; [done|].
    iDestruct (gps_own_snap_singleton with "O'") as "#$".
    - by rewrite lookup_insert.
    - by iFrame "O'".
  Qed.

  Lemma gps_own_snap_sub γ χ χ' :
    gps_own γ χ' -∗ gps_snap γ χ -∗ ⌜ χ ⊆ χ' ⌝.
  Proof.
    iIntros "oA R".
    iCombine "oA R" gives %VAL.
    iPureIntro. move : VAL.
    rewrite /stateMap_auth /stateMap_frag -assoc auth_both_valid_discrete /=.
    intros [? _]. apply stateMap_included. etrans; [apply cmra_included_r|done].
  Qed.

  Lemma gps_own_snap_singleton_sub γ χ t s :
    gps_own γ χ -∗ gps_snap γ {[t := s]} -∗ ⌜ χ !! t = Some s ⌝.
  Proof.
    iIntros "oA R".
    by iDestruct (gps_own_snap_sub with "oA R") as %SUB%map_singleton_subseteq_l.
  Qed.

  Lemma gps_snap_singleton_agree γ χ t1 s1 t2 s2 :
    stsorted χ →
    gps_own γ χ -∗
    gps_snap γ {[t1 := s1]} -∗ gps_snap γ {[t2 := s2]} -∗
    ⌜ (t1 ⊑ t2 → s1 ⊑ s2) ∧ (t2 ⊑ t1 → s2 ⊑ s1) ⌝.
  Proof.
    iIntros (SORTED) "oA R1 R2".
    iDestruct (gps_own_snap_singleton_sub with "oA R1") as %Sub1.
    iDestruct (gps_own_snap_singleton_sub with "oA R2") as %Sub2.
    iPureIntro. split.
    - intros. by apply (SORTED _ _ _ _ Sub1 Sub2).
    - intros. by apply (SORTED _ _ _ _ Sub2 Sub1).
  Qed.

  Lemma gps_inv_snap_singleton_agree
    IW γ bs Vo (γs γl : gname) t1 s1 t2 s2 E :
    γ = encode (γs,γl) →
    (@{Vo} ▷ gps_inv IP IW l γ bs) -∗
    gps_snap γs {[t1 := s1]} -∗ gps_snap γs {[t2 := s2]} ={E}=∗
    (@{Vo} ▷ gps_inv IP IW l γ bs) ∗ ⌜ (t1 ⊑ t2 → s1 ⊑ s2) ∧ (t2 ⊑ t1 → s2 ⊑ s1) ⌝.
  Proof.
    intros ENC. rewrite view_at_later.
    iDestruct 1 as (μ γs' γl' ζ tx) "(>%EN' & >O & O1 & O2 & O3 & >%F)".
    destruct F as (? & SORTED & ?).
    rewrite ENC in EN'. apply encode_inj, pair_inj in EN' as [<- <-].
    rewrite view_at_objective_iff.
    iIntros "R1 R2 !>".
    iDestruct (gps_snap_singleton_agree with "O R1 R2") as %?; [done|].
    iSplit; [|done].
    iExists μ, γs, γl, ζ, tx. iNext. iFrame (ENC) "O O1 O2 O3". by iPureIntro.
  Qed.

  Lemma gps_inv_own_loc_prim IW γ bs :
    gps_inv IP IW l γ bs -∗ ∃ C, l p↦ C.
  Proof.
    iDestruct 1 as (μ ?????) "(? & SW & ?)".
    by iApply (AtomicPtsToX_own_loc_prim with "SW").
  Qed.

  Lemma PrtSync_PrtSeen t s v γ : PrtSync l t s v γ ⊢ PrtSeen l t s v γ.
  Proof. by rewrite /PrtSync; setoid_rewrite AtomicSync_AtomicSeen. Qed.
  Lemma PrtSync_GPS_Reader t s v γ : PrtSync l t s v γ ⊢ GPS_Reader l t s v γ.
  Proof. rewrite GPS_Reader_eq. apply PrtSync_PrtSeen. Qed.

  Lemma GPS_Reader_from_seen_singleton γs γl t s v V :
    gps_snap γs {[t := s]} -∗ l sn⊒{γl} {[t := (v, V)]} -∗
    GPS_Reader l t s v (encode (γs, γl)).
  Proof.
    rewrite GPS_Reader_eq. iIntros "S R". iExists γs, γl, _. by iFrame "S R".
  Qed.
  Lemma GPS_Reader_from_sync_singleton γs γl t s v V :
    gps_snap γs {[t := s]} -∗ l sy⊒{γl} {[t := (v, V)]} -∗
    GPS_Reader l t s v (encode (γs, γl)).
  Proof.
    rewrite AtomicSync_AtomicSeen. apply GPS_Reader_from_seen_singleton.
  Qed.

  Lemma GPS_Reader_from_seen γs γl ζ t s v V :
    ζ !! t = Some (v, V) →
    gps_snap γs {[t := s]} -∗ l sn⊒{γl} ζ -∗
    GPS_Reader l t s v (encode (γs, γl)).
  Proof.
    iIntros (EQ) "S R". iApply (GPS_Reader_from_seen_singleton with "S [R]").
    by iApply (AtomicSeen_mono_lookup_singleton with "R").
  Qed.
  Lemma GPS_Reader_from_sync γs γl ζ t s v V :
    ζ !! t = Some (v, V) →
    gps_snap γs {[t := s]} -∗ l sy⊒{γl} ζ -∗
    GPS_Reader l t s v (encode (γs, γl)).
  Proof. rewrite AtomicSync_AtomicSeen. apply GPS_Reader_from_seen. Qed.

  Lemma GPS_Readers_agree IW γ bs t1 t2 s1 s2 v1 v2 Vb E:
    GPS_Reader l t1 s1 v1 γ -∗ GPS_Reader l t2 s2 v2 γ
    -∗ (⊔{Vb} ▷ gps_inv IP IW l γ bs)
    ={E}=∗ (⊔{Vb} ▷ gps_inv IP IW l γ bs) ∗
            ⌜ (t1 ⊑ t2 → s1 ⊑ s2) ∧ (t2 ⊑ t1 → s2 ⊑ s1) ⌝.
  Proof.
    rewrite GPS_Reader_eq.
    iDestruct 1 as (??? EQ1) "[R1 _]". iDestruct 1 as (??? EQ2) "[R2 _]".
    rewrite EQ1 in EQ2. apply encode_inj, pair_inj in EQ2 as [<- <-].
    iIntros "I".
    iDestruct (view_join_view_at_access' with "I") as (Vo) "[sV [I Close]]".
    iMod (gps_inv_snap_singleton_agree with "I R1 R2") as "[I $]"; [done|].
    iIntros "!>". iApply ("Close" with "sV I").
  Qed.

  Lemma GPSRaw_read_resources
    IW (isEx: bool) R μ ζ (tx tr t': time) v V' γ E
    (Eqt': ζ !! t' = Some (v,V')) (Letr: tr ⊑ t')
    (IEX: if isEx then (tx ≤ tr)%positive else True):
    (<obj>
      ((F_read γ t' (μ t') v ={E}=∗ F_read γ t' (μ t') v ∗ R t' (μ t') v) ∧
      (F γ t' (μ t') v ={E}=∗ F γ t' (μ t') v ∗ R t' (μ t') v) ∧
      (if isEx then True
       else IW l γ t' (μ t') v ={E}=∗ IW l γ t' (μ t') v ∗ R t' (μ t') v))) -∗
    resBE IP IW l γ μ ζ tx -∗
    resD IP IW l γ μ ζ tx ={E}=∗
    resBE IP IW l γ μ ζ tx ∗
    resD IP IW l γ μ ζ tx ∗
    @{V'} (R t' (μ t') v).
  Proof.
    iIntros "VP rBE rD".
    destruct ((cbends ζ) !! t') as [mm'|] eqn: Eqmm'.
    - iFrame "rD".
      assert (mm' = (v,V')) as ->. (* TODO lemma *)
      { move : Eqmm' => /map_filter_lookup_Some [Eq' _]. rewrite Eqt' in Eq'.
        by inversion Eq'. }
      rewrite bi.and_elim_r.
      rewrite /resBE /gps_res (big_sepM_delete _ _ _ _ Eqmm').
      iDestruct "rBE" as "(Hm & $)". rewrite /= -view_at_sep -view_at_fupd.
      destruct isEx.
      + rewrite bi.and_elim_l decide_True; [|by etrans].
        by iApply (view_at_objectively with "VP Hm").
      + case (decide _) => Letx; by iApply (view_at_objectively with "VP Hm").
    - iFrame "rBE".
      have Eqt2: (ζ ∖ (cbends ζ)) !! t' = Some (v, V')
        by apply lookup_difference_Some.
      rewrite /resD /gps_res (big_sepM_delete _ _ _ _ Eqt2).
      iDestruct "rD" as "(Hm & $)". rewrite /=.
      destruct isEx.
      + rewrite decide_True; [|by etrans].
        iDestruct "Hm" as "[Hm|Hm]";
          by iMod (view_at_objectively with "VP Hm") as "[$$]".
      + case (decide _) => Letx;
          [iDestruct "Hm" as "[Hm|Hm]"|iDestruct "Hm" as "[Hm|[Hm|Hm]]"];
          by iMod (view_at_objectively with "VP Hm") as "[$$]".
  Qed.

  Lemma top_write_block_end μ ζ t m
    (TOP : ∀ t', t' ∈ dom (toState μ ζ) → t' ⊑ t)
    (EQ : ζ !! t = Some m) :
    cbends ζ !! t = Some m.
  Proof.
    apply map_filter_lookup_Some. split; [done|]. rewrite /cell_adj.
    move => t0 m0 Eq0 /= NEq0 ?. subst t0.
    apply (irreflexive_eq (R:=(⊏)) t t); [done|].
    eapply (strict_transitive_l _ (t+1)%positive).
    - split; [apply Pos.lt_le_incl|apply Pos.lt_nle]; lia.
    - apply TOP, elem_of_dom. exists (μ (t + 1)%positive).
      by eapply toState_lookup_state_inv.
  Qed.
End Properties.

(** Recursive protocol *)
Section recursive.
  Context {Prtcl : protocolT}.
  Global Instance InterpType_cofe Σ : Cofe (interpO Σ Prtcl) := _.
  Global Instance interp_inhabited Σ : Inhabited (interpO Σ Prtcl).
  Proof. constructor; repeat intro; exact True%I. Qed.
  Global Instance InterpCasType_cofe Σ : Cofe (interpCasO Σ Prtcl) := _.
  Global Instance interpCas_inhabited Σ : Inhabited (interpCasO Σ Prtcl).
  Proof. constructor; repeat intro; exact True%I. Qed.
End recursive.
Program Example intExample Σ : interpO Σ unitProtocol :=
  @fixpoint _ _ _
    (λ (F : interpO Σ unitProtocol) b l γ t s v, ∃ c, ⌜c = #1⌝ ∗ ▷ F b l γ t s v)%I _.
Next Obligation.
  repeat intro.
  apply bi.exist_ne => ? . apply bi.sep_ne; [done|]. f_contractive. apply H.
Qed.
