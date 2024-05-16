From gpfsl.lang Require Export notation tactics.
From gpfsl.logic Require Import logatom atomics relacq.

From gpfsl.logic Require Import lifting proofmode.

Require Import iris.prelude.options.

(* Base definition of XCHG, used for both actual XCHG and FAA *)
(* f is assumed to be a pure function that computes the output value *)
Definition XCHG_aux (or ow : memOrder) (f : val) : val :=
  rec: "XCHG" ["x"; "vn"] :=
    let: "vo"  := !ʳˡˣ "x" in
      if: CAS "x" "vo" (f ["vo"; "vn"]) Relaxed or ow (* the failure case is a relaxed read by default *)
      then "vo"
      else "XCHG" ["x"; "vn"]
  .

Definition XCHG (or ow : memOrder) : val :=
  XCHG_aux or ow (λ: ["vo"; "vn"], "vn"). (* swap in the input value *)

Definition FAA (or ow : memOrder) : val :=
  XCHG_aux or ow (λ: ["vo"; "vn"], "vo" + "vn"). (* add the input value to the current value *)

(* A fully relaxed XCHG *)
Notation "'XCHGʳˡˣ(' l , e )" := (XCHG Relaxed Relaxed [l ; e]%E)
  (at level 80, format "XCHGʳˡˣ( l ,  e )") : expr_scope.
(* A release XCHG, only the successful case makes a release write *)
Notation "'XCHGʳᵉˡ(' l , e )" := (XCHG Relaxed AcqRel [l ; e]%E)
  (at level 80, format "XCHGʳᵉˡ( l ,  e )") : expr_scope.
(* An acquire XCHG, only the successful case makes an acquire read *)
Notation "'XCHGᵃᶜ(' l , e )" := (XCHG AcqRel Relaxed [l ; e]%E)
  (at level 80, format "XCHGᵃᶜ( l ,  e )") : expr_scope.
(* A release-acquire XCHG, only the successful case makes an acquire read AND
  a release write *)
Notation "'XCHGʳᵃ(' l , e )" := (XCHG AcqRel AcqRel [l ; e]%E)
  (at level 80, format "XCHGʳᵃ( l ,  e )") : expr_scope.

(* A fully relaxed FAA *)
Notation "'FAAʳˡˣ(' l , e )" := (FAA Relaxed Relaxed [l ; e]%E)
  (at level 80, format "FAAʳˡˣ( l ,  e )") : expr_scope.
(* A release FAA, only the successful case makes a release write *)
Notation "'FAAʳᵉˡ(' l , e )" := (FAA Relaxed AcqRel [l ; e]%E)
  (at level 80, format "FAAʳᵉˡ( l ,  e )") : expr_scope.
(* An acquire FAA, only the successful case makes an acquire read *)
Notation "'FAAᵃᶜ(' l , e )" := (FAA AcqRel Relaxed [l ; e]%E)
  (at level 80, format "FAAᵃᶜ( l ,  e )") : expr_scope.
(* A release-acquire FAA, only the successful case makes an acquire read AND
  a release write *)
Notation "'FAAʳᵃ(' l , e )" := (FAA AcqRel AcqRel [l ; e]%E)
  (at level 80, format "FAAʳᵃ( l ,  e )") : expr_scope.

(* We only have rules for int *)
(* TODO: we can also have rules for comparing with int, e.g. exchange an int for
  a location (nullable locations). *)
Definition int_only_hist (ζ : absHist) : Prop :=
  ∀ t (v : val), fst <$> ζ !! t = Some v → ∃ z : Z, v = #z.

(* TODO: more rules for other forms of AtomicPtsto *)
Section atomic_exchange.
Context `{!noprolG Σ, !atomicG Σ}.
#[local] Notation iProp := (iProp Σ).
#[local] Notation vProp := (vProp Σ).

Lemma AtomicSeen_CON_XCHG_aux_int
  (l : loc) γ ζ' or ow (f : val) φ (v : Z) tid (Vrel : view) V
  (OR : Relaxed ⊑ or) (OW : Relaxed ⊑ ow) :
  (∀ (vo vn : Z) tid',
    {{{ True }}} f [ #vo; #vn] @ tid'; ⊤ {{{ (vn' : Z), RET #vn'; ⌜φ vo vn vn'⌝ }}}) →
  ⊒V -∗
  l sn⊒{γ} ζ' -∗
  (if decide (AcqRel ⊑ ow) then True else △{tid} ⊒Vrel) -∗
  <<< ∀ Vb ζ, ⊔{Vb} l at↦{γ} ζ ∗ ⌜ int_only_hist ζ ⌝ >>>
    XCHG_aux or ow f [ #l ; #v] @ tid; ∅
  <<< ∃ (tr : time) (vr vw : Z) Vr Vw V'' ζ'' ζn,
      @{V''} l sn⊒{γ} ζ'' ∗ ⊔{Vb} l at↦{γ} ζn
      ∗ ⊒V''
      ∗ (if decide (AcqRel ⊑ ow) then @{Vw} l sn⊒{γ} ζ'' else emp)
      ∗ (if decide (AcqRel ⊑ or) then ⌜Vw ⊑ V''⌝ else ▽{tid} ⊒Vw)
      ∗ ⌜ int_only_hist ζn
          ∧ ζ' ⊆ ζ'' ⊆ ζn
          ∧ (* read message (t', #v', Vr) *) ζ'' !! tr = Some (#vr, Vr)
          ∧ no_earlier_time ζ' tr
          ∧ (* pre-view ⊑ post-view *) V ⊑ V''
          ∧ φ vr v vw
          ∧ let tw := (tr+1)%positive in
            ζ !! tw = None ∧ ζn = <[tw := (#vw, Vw)]>ζ
          ∧ ζ'' !! tw = Some (#vw, Vw)
          (* release sequence: Vwrite includes Vread *)
          ∧ Vr ⊑ Vw ∧ Vr ≠ Vw
          ∧ (¬ V'' ⊑ Vr)
          ∧ V ≠ V''
          ∧ ( if decide (AcqRel ⊑ ow) then
                ( if decide (AcqRel ⊑ or) then
                    (* release-acquire CAS *) Vw = V''
                  else (* release CAS: *) V'' ⊑ Vw )
              else (* relaxed write CAS *) Vrel ⊑ Vw ) ⌝,
      RET #vr, True >>>.
Proof.
  intros Hf.
  assert (Persistent (PROP:=vPropI _)
                     (if decide (AcqRel ⊑ ow) then True else △{tid} ⊒Vrel)%I).
  { case decide; apply _. }
  iIntros "#sV #sζ' #Hrel" (Φ) "AU".
  iLöb as "IH".

  wp_rec. wp_bind (!ʳˡˣ_)%E.

  iMod "AU" as (Vb ζ) "[[lA %INT] HClose]".

  wp_apply (AtomicSeen_relaxed_read_vj with "[$sζ' $lA $sV]"); [done|].
  iIntros (t1 v1 V1' V1 ζ1) "(F & #sV1 & #sV1' & sζ1 & lA)".
  rewrite bi.and_elim_l. iMod ("HClose" with "[$lA //]") as "AU". clear Vb.

  iIntros "!>".
  iDestruct "F" as %(Subζ' & Eqt1 & MAXt1 & LeV').
  destruct (INT t1 v1) as [vr ->].
  { destruct Subζ' as [_ Subζ1]. by rewrite (lookup_weaken _ _ _ _ Eqt1 Subζ1). }

  wp_let. wp_bind (f _)%E.
  wp_apply (Hf with "[//]").
  iIntros (vw Hφ).
  wp_bind (CAS _ _ _ _ _ _)%E.

  iMod "AU" as (Vb ζ2) "[[lA %INT2] HClose]".
  iDestruct (view_at_elim with "sV1 sζ1") as "sζ1".
  wp_apply (AtomicSeen_CON_CAS_int_vj _ _ _ _ _ _ _ vr #vw with "[$sζ1 $lA $sV1]");
    [done..| | |].
  { intros t' v' _ [z ->]%INT2. exists z. split; [done|constructor]. }
  { iFrame "Hrel". }

  iIntros (b t2 v2 Vr V2 ζ2' ζn) "(F & #sV2 & sζ2' & lA & CASE)".
  iDestruct "F" as %([Subζ1 Subζ2'] & Eqt2 & MAXt2 & LeV1).

  iDestruct "CASE" as "[[F sVr]|[F HVw]]".
  - iDestruct "F" as %(-> & NEq & ->).
    rewrite bi.and_elim_l. iMod ("HClose" with "[$lA //]") as "AU". clear Vb.

    (* failure case: repeat *)
    iIntros "!>". wp_if. by iApply ("IH" with "AU").
  - iDestruct "F" as %[-> ->]. iDestruct "HVw" as (Vw F) "[sζ2w' sVw]".
    rewrite bi.and_elim_r.
    iMod ("HClose" $!  _ vr vw Vr Vw V2 with "[$sζ2' $lA $sV2 $sζ2w' $sVw]") as "HΦ".
    { iPureIntro.
      destruct F as (FRtw & Eqζn & Eqtw & LeV & ? & ? & NEq12 & ?).
      destruct Subζ' as [Subζ' _].
      assert (V ≠ V2). { intros ->. apply NEq12. solve_lat. }
      split; last split; last split; last split; last split;
        [..|done| |solve_lat|done].
      - intros t' v'. rewrite Eqζn.
        case (decide (t' = (t2 + 1)%positive)) => [->|?].
        + clear. rewrite lookup_insert /=. naive_solver.
        + rewrite lookup_insert_ne; [by apply INT2|done].
      - clear -Subζ1 Subζ2' Subζ'. split; [by etrans|done].
      - intros t IS. by apply MAXt2, (lookup_weaken_is_Some _ _ _ IS Subζ'). }
    iIntros "!>". wp_if. by iApply "HΦ".
Qed.

Lemma AtomicSeen_CON_XCHG_int
  (l : loc) γ ζ' or ow (v : Z) tid (Vrel : view) V
  (OR : Relaxed ⊑ or) (OW : Relaxed ⊑ ow) :
  ⊒V -∗
  l sn⊒{γ} ζ' -∗
  (if decide (AcqRel ⊑ ow) then True else △{tid} ⊒Vrel) -∗
  <<< ∀ Vb ζ, ⊔{Vb} l at↦{γ} ζ ∗ ⌜ int_only_hist ζ ⌝ >>>
    XCHG or ow [ #l ; #v] @ tid; ∅
  <<< ∃ (tr : time) (vr : Z) Vr Vw V'' ζ'' ζn,
      @{V''} l sn⊒{γ} ζ'' ∗ ⊔{Vb} l at↦{γ} ζn
      ∗ ⊒V''
      ∗ (if decide (AcqRel ⊑ ow) then @{Vw} l sn⊒{γ} ζ'' else emp)
      ∗ (if decide (AcqRel ⊑ or) then ⌜Vw ⊑ V''⌝ else ▽{tid} ⊒Vw)
      ∗ ⌜ int_only_hist ζn
          ∧ ζ' ⊆ ζ'' ⊆ ζn
          ∧ (* read message (t', #v', Vr) *) ζ'' !! tr = Some (#vr, Vr)
          ∧ no_earlier_time ζ' tr
          ∧ (* pre-view ⊑ post-view *) V ⊑ V''
          ∧ let tw := (tr+1)%positive in
            ζ !! tw = None ∧ ζn = <[tw := (#v, Vw)]>ζ
          ∧ ζ'' !! tw = Some (#v, Vw)
          (* release sequence: Vwrite includes Vread *)
          ∧ Vr ⊑ Vw ∧ Vr ≠ Vw
          ∧ (¬ V'' ⊑ Vr)
          ∧ V ≠ V''
          ∧ ( if decide (AcqRel ⊑ ow) then
                ( if decide (AcqRel ⊑ or) then
                    (* release-acquire CAS *) Vw = V''
                  else (* release CAS: *) V'' ⊑ Vw )
              else (* relaxed write CAS *) Vrel ⊑ Vw ) ⌝,
      RET #vr, True >>>.
Proof.
  iIntros "sV sζ' Hrel" (Φ) "AU".
  iApply (AtomicSeen_CON_XCHG_aux_int _ _ _ _ _ _ (λ vr vn vw', vw' = vn)
            with "sV sζ' Hrel"); [done..| |].
  { clear. iIntros (vo vn tid Φ) "_ HΦ". wp_lam. by iApply "HΦ". }
  iAuIntro. iApply (aacc_aupd_commit with "AU"); [done|].
  iIntros (Vb ζ) "P".
  iAaccIntro with "P"; first by eauto with iFrame.
  iIntros (t vr vw Vr Vw V' ζ'' ζn) "(sζ'' & P & sV' & sζw & sVw & F)".
  iIntros "!>".
  iExists t, vr, Vr, Vw, V', ζ'', ζn. iFrame. iSplit; [|eauto].
  iDestruct "F" as %(? & ? & ? & ? & ? & -> & ?).
  by iPureIntro.
Qed.

Lemma AtomicSeen_CON_FAA
  (l : loc) γ ζ' or ow (v : Z) tid (Vrel : view) V
  (OR : Relaxed ⊑ or) (OW : Relaxed ⊑ ow) :
  ⊒V -∗
  l sn⊒{γ} ζ' -∗
  (if decide (AcqRel ⊑ ow) then True else △{tid} ⊒Vrel) -∗
  <<< ∀ Vb ζ, ⊔{Vb} l at↦{γ} ζ ∗ ⌜ int_only_hist ζ ⌝ >>>
    FAA or ow [ #l ; #v] @ tid; ∅
  <<< ∃ (tr : time) (vr : Z) Vr Vw V'' ζ'' ζn,
      @{V''} l sn⊒{γ} ζ'' ∗ ⊔{Vb} l at↦{γ} ζn
      ∗ ⊒V''
      ∗ (if decide (AcqRel ⊑ ow) then @{Vw} l sn⊒{γ} ζ'' else emp)
      ∗ (if decide (AcqRel ⊑ or) then ⌜Vw ⊑ V''⌝ else ▽{tid} ⊒Vw)
      ∗ ⌜ int_only_hist ζn
          ∧ ζ' ⊆ ζ'' ⊆ ζn
          ∧ (* read message (t', #v', Vr) *) ζ'' !! tr = Some (#vr, Vr)
          ∧ no_earlier_time ζ' tr
          ∧ (* pre-view ⊑ post-view *) V ⊑ V''
          ∧ let tw := (tr+1)%positive in
            ζ !! tw = None ∧ ζn = <[tw := (#(vr + v), Vw)]>ζ
          ∧ ζ'' !! tw = Some (#(vr + v), Vw)
          (* release sequence: Vwrite includes Vread *)
          ∧ Vr ⊑ Vw ∧ Vr ≠ Vw
          ∧ (¬ V'' ⊑ Vr)
          ∧ V ≠ V''
          ∧ ( if decide (AcqRel ⊑ ow) then
                ( if decide (AcqRel ⊑ or) then
                    (* release-acquire CAS *) Vw = V''
                  else (* release CAS: *) V'' ⊑ Vw )
              else (* relaxed write CAS *) Vrel ⊑ Vw ) ⌝,
      RET #vr, True >>>.
Proof.
  iIntros "sV sζ' Hrel" (Φ) "AU".
  iApply (AtomicSeen_CON_XCHG_aux_int _ _ _ _ _ _ (λ vr vn vw', vw' = vr + vn)
            with "sV sζ' Hrel"); [done..| |].
  { clear. iIntros (vo vn tid Φ) "_ HΦ". wp_pures. by iApply "HΦ". }
  iAuIntro. iApply (aacc_aupd_commit with "AU"); [done|].
  iIntros (Vb ζ) "P".
  iAaccIntro with "P"; first by eauto with iFrame.
  iIntros (t vr vw Vr Vw V' ζ'' ζn) "(sζ'' & P & sV' & sζw & sVw & F)".
  iIntros "!>".
  iExists t, vr, Vr, Vw, V', ζ'', ζn. iFrame. iSplit; [|eauto].
  iDestruct "F" as %(? & ? & ? & ? & ? & -> & ?).
  by iPureIntro.
Qed.
End atomic_exchange.
