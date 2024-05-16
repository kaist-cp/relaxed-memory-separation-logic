From iris.algebra Require Import agree.
From iris.proofmode Require Import proofmode.

From gpfsl.base_logic Require Import vprop history.
From gpfsl.base_logic Require Import iwp.
From gpfsl.base_logic Require Import weakestpre base_lifting na.

From gpfsl.lang Require Import notation.

Require Import iris.prelude.options.

(* TODO: move to master *)
Definition ro_ptstoR : cmra := agreeR (leibnizO (time * val * view)).

Class ro_ptstoG Σ := { ro_ptsto_inG : inG Σ ro_ptstoR; }.
Local Existing Instance ro_ptsto_inG.
Definition ro_ptstoΣ : gFunctors := #[ GFunctor (constRF ro_ptstoR) ].
Global Instance subG_ro_ptstoΣ {Σ} : subG ro_ptstoΣ Σ → ro_ptstoG Σ.
Proof. solve_inG. Qed.

Section preds.
Context `{!noprolG Σ, !ro_ptstoG Σ}.
#[local] Notation vProp := (vProp Σ).

Definition ROPtsTo_def (l : loc) γ v : vProp :=
  ∃ t m rsa rsn ws V,
    let C : cell := {[t := m]} in
    ⌜ good_hist C ∧ memval_val_rel (mval m) v ∧ default ∅ m.(mrel) ⊑ V ⌝ ∗
    (* local assertions *)
    (seen_view l t V ∗ AtRLocal l rsa ∗ (@{V} AtWLocal l ws) ∗ ∃ Va', NaLocal l rsn Va') ∗
    (* own the history of l *)
    ⎡ hist l 1 C ⎤ ∗
    (* and related race detector states *)
    ⎡ atread l 1 rsa ∗ atwrite l 1 ws ∗ naread l 1 rsn ⎤ ∗
    (* authoritative ghost state of this construction *)
    ⎡ own γ (to_agree ((t, v, V) : leibnizO _)) ⎤
    .
Definition ROPtsTo_aux : seal (@ROPtsTo_def). Proof. by eexists. Qed.
Definition ROPtsTo := unseal (@ROPtsTo_aux).
Definition ROPtsTo_eq : @ROPtsTo = _ := seal_eq _.

Definition ROSeen_def (l : loc) γ v : vProp :=
  ∃ t V, seen_view l t V ∗ (* seen the writes, but not sync *)
    ⎡ own γ (to_agree ((t, v, V) : leibnizO _)) ⎤.
Definition ROSeen_aux : seal (@ROSeen_def). Proof. by eexists. Qed.
Definition ROSeen := unseal (@ROSeen_aux).
Definition ROSeen_eq : @ROSeen = _ := seal_eq _.
End preds.

Notation "l 'ro↦{' γ '}' v" := (ROPtsTo l γ v)
  (at level 20, format "l  ro↦{ γ }  v")  : bi_scope.
Notation "l 'ro⊒{' γ '}' v" := (ROSeen l γ v)
  (at level 20, format "l  ro⊒{ γ }  v")  : bi_scope.

Implicit Types (l : loc) (t : time) (v : val) (V : view).

Section ops_rules.
Context `{!noprolG Σ, !ro_ptstoG Σ}.
#[local] Notation iProp := (iProp Σ).
#[local] Notation vProp := (vProp Σ).

#[global] Instance ROPtsTo_timeless l γ v : Timeless (l ro↦{γ} v).
Proof. rewrite ROPtsTo_eq. apply _. Qed.

#[global] Instance ROSeen_persistent l γ v : Persistent (l ro⊒{γ} v).
Proof. rewrite ROSeen_eq. by apply _. Qed.
#[global] Instance ROSeen_timeless l γ v : Timeless (l ro⊒{γ} v).
Proof. rewrite ROSeen_eq. by apply _. Qed.

Lemma ROSeen_agree' l γ v v' V V' :
  @{V} l ro⊒{γ} v -∗ @{V'} l ro⊒{γ} v' -∗ ⌜ v' = v ⌝.
Proof.
  rewrite ROSeen_eq.
  iDestruct 1 as (??) "[_ O1]". iDestruct 1 as (??) "[_ O2]".
  rewrite !view_at_objective_iff.
  iCombine "O1 O2" gives %?%to_agree_op_valid_L.
  iPureIntro. by simplify_eq.
Qed.
Lemma ROSeen_agree_l l γ v v' V :
  @{V} l ro⊒{γ} v -∗ l ro⊒{γ} v' -∗ ⌜ v' = v ⌝.
Proof.
  iIntros "O1 O2". iDestruct (view_at_intro with "O2") as (V') "[_ O2]".
  iApply (ROSeen_agree' with "O1 O2").
Qed.
Lemma ROSeen_agree_r l γ v v' V' :
  l ro⊒{γ} v -∗ @{V'} l ro⊒{γ} v' -∗ ⌜ v' = v ⌝.
Proof.
  iIntros "O1". iDestruct (view_at_intro with "O1") as (V) "[_ O1]".
  iApply (ROSeen_agree' with "O1").
Qed.

Lemma ROSeen_agree l γ v v' :
  l ro⊒{γ} v -∗ l ro⊒{γ} v' -∗ ⌜ v' = v ⌝.
Proof.
  iIntros "O1". iDestruct (view_at_intro with "O1") as (V) "[_ O1]".
  iApply (ROSeen_agree_l with "O1").
Qed.

Lemma ROPtsTo_ROSeen_agree' l γ v v' V V' :
  @{V} l ro↦{γ} v -∗ @{V'} l ro⊒{γ} v' -∗ ⌜ v' = v ⌝.
Proof.
  rewrite ROPtsTo_eq ROSeen_eq.
  iDestruct 1 as (???????) "(_&_&_&O1)". iDestruct 1 as (??) "[_ O2]".
  rewrite !view_at_objective_iff.
  iCombine "O1 O2" gives %?%to_agree_op_valid_L.
  iPureIntro. by simplify_eq.
Qed.
Lemma ROPtsTo_ROSeen_agree_l l γ v v' V :
  @{V} l ro↦{γ} v -∗ l ro⊒{γ} v' -∗ ⌜ v' = v ⌝.
Proof.
  iIntros "O1 O2". iDestruct (view_at_intro with "O2") as (V') "[_ O2]".
  iApply (ROPtsTo_ROSeen_agree' with "O1 O2").
Qed.
Lemma ROPtsTo_ROSeen_agree_r l γ v v' V' :
  l ro↦{γ} v -∗ @{V'} l ro⊒{γ} v' -∗ ⌜ v' = v ⌝.
Proof.
  iIntros "O1". iDestruct (view_at_intro with "O1") as (V) "[_ O1]".
  iApply (ROPtsTo_ROSeen_agree' with "O1").
Qed.

Lemma ROPtsTo_ROSeen_agree l γ v v' :
  l ro↦{γ} v -∗ l ro⊒{γ} v' -∗ ⌜ v' = v ⌝.
Proof.
  iIntros "O1". iDestruct (view_at_intro with "O1") as (V) "[_ O1]".
  iApply (ROPtsTo_ROSeen_agree_l with "O1").
Qed.

Lemma ROPtsTo_from_na l v :
  l ↦ v ==∗ ∃ γ, l ro↦{γ} v.
Proof.
  rewrite own_loc_na_eq ROPtsTo_eq /ROPtsTo_def /own_loc_na_def.
  iDestruct 1 as (t m) "(Own & %VAL & #sVm)".
  iDestruct "Own" as (rsa rsn ws GH) "(AL & ARL & AWL & [%Va NAL] & HC & AW)".
  set C := {[t := m]}.
  iDestruct (view_at_intro_incl with "AWL sVm") as (Vna) "(sVna & %LeVna & AWL)".
  iMod (own_alloc (to_agree ((t,v,Vna) : leibnizO _))) as (γ) "#A"; [done|].
  iIntros "!>". iExists γ, t, m, rsa, rsn, ws, Vna. iSplit; [by iPureIntro|].
  iFrame "ARL AWL HC AW A". iSplitR "NAL"; [|by eauto].
  rewrite seen_time_AllocLocal_singleton_inv seen_view_seen_time. by iFrame.
Qed.

Lemma ROPtsTo_ROSeen l γ v :
  l ro↦{γ} v ⊢ l ro⊒{γ} v.
Proof.
  rewrite ROPtsTo_eq ROSeen_eq.
  iDestruct 1 as (t m rsa rns ws Va (GH & Eqv' & LeVa))
                  "((sV & ARL & AWL & [%Vna NA]) & HC & As & AR)".
  iExists t, Va. by iFrame.
Qed.

(* TODO: generalize with the next lemma *)
Lemma ROSeen_read_atomic l γ v v' o tid V Vb E :
  Relaxed ⊑ o → ↑histN ⊆ E →
  {{{ l ro⊒{γ} v ∗ @{Vb} l ro↦{γ} v' ∗ ⊒V }}}
    Read o #l @ tid; E
  {{{ V', RET v;
      ⌜ v' = v ∧ V ⊑ V' ⌝
      ∗ ⊒V'
      ∗ @{Vb ⊔ V'} l ro↦{γ} v }}}.
Proof.
  intros RLX SUB Φ. iStartProof iProp. iIntros (V0) "(SR & Pts & sV)".
  iIntros (V1 ->) "Post". iDestruct "sV" as %LeV1.
  rewrite wp_eq /wp_def /=.
  iIntros (𝓥 Le𝓥) "oL sV".
  rewrite ROPtsTo_eq /ROPtsTo_def ROSeen_eq /ROSeen_def.
  rewrite !view_at_unfold_2.
  iDestruct "Pts" as (t m rsa rns ws Va (GH & Eqv' & LeVa))
            "((SLV & ARL & AWL & NAL) & HC & (AR & AW & NA) & AR1)".
  iDestruct "SR" as (t' V') "[SLV' AR2]".
  iCombine "AR1 AR2" gives %Eq'%to_agree_op_valid_L.
  inversion Eq'; clear Eq'; subst t' v' V'.

  iDestruct (seen_time_AllocLocal_singleton l t m with "[SLV']") as %AL.
  { by inversion Eqv'. } { iDestruct (seen_view_seen_time with "SLV'") as "[$ ?]". }
  iAssert (⌜atr_local l rsa Vb⌝)%I as %?. { by iDestruct "ARL" as %?. }

  iApply iwp_fupd.
  iApply (iwp_read_atomic with "[$sV $HC $AR]");
    [done|by eapply alloc_local_mono|done..|].

  iNext. iIntros (𝓥' v' ?) "(s' & hist & at & Ext)".
  iDestruct "Ext" as %(Le𝓥' & _ & t' & m' & HL & ISV & RH & AT').
  apply lookup_singleton_Some in HL as []. subst t' m'.
  assert (v' = v).
  { clear -ISV Eqv'. inversion ISV; clear ISV; subst;
      inversion Eqv'; clear Eqv'; congruence. } subst v'.
  iMod (own_lat_auth_update with "oL") as "[$ oTV]"; [done|].
  iIntros "!>".

  set V'' := 𝓥'.(cur).
  have LEV1 : V1 ⊑ V'' by rewrite /V'' Le𝓥 Le𝓥'.
  iApply ("Post" $! V'').
  iSplitR; last iSplitR; [iPureIntro; solve_lat|by iPureIntro|..].
  iExists t, m, _, rns, ws, Va. iSplit; [done|].
  rewrite (view_at_unfold_2 _ (_ ⊔ _)). iFrame. iSplit.
  - iPureIntro. exact AT'.
  - iDestruct "NAL" as (Vna) "NAL". iExists Vna. iFrame.
Qed.

Lemma ROSeen_read_non_atomic l γ v v' tid V Vb E :
  ↑histN ⊆ E →
  {{{ l ro⊒{γ} v ∗ @{Vb} l ro↦{γ} v' ∗ ⊒V }}}
    !#l @ tid; E
  {{{ V', RET v;
      ⌜ v' = v ∧ V ⊑ V' ⌝
      ∗ ⊒V'
      ∗ @{Vb ⊔ V'} l ro↦{γ} v }}}.
Proof.
  intros SUB Φ. iStartProof iProp. iIntros (V0) "(SR & Pts & sV)".
  iIntros (V1 ->) "Post". iDestruct "sV" as %LeV1.
  rewrite wp_eq /wp_def /=.
  iIntros (𝓥 Le𝓥) "oL sV".
  rewrite ROPtsTo_eq /ROPtsTo_def ROSeen_eq /ROSeen_def.
  rewrite !view_at_unfold_2.
  iDestruct "Pts" as (t m rsa rns ws Va (GH & Eqv' & LeVa))
            "((SLV & ARL & #AWL & NAL) & HC & (AR & AW & NA) & AR1)".
  iDestruct "SR" as (t' V') "[SLV' AR2]".
  iCombine "AR1 AR2" gives %Eq'%to_agree_op_valid_L.
  inversion Eq'; clear Eq'; subst t' v' V'.
  iDestruct (seen_time_AllocLocal_singleton l t m with "[SLV']") as %AL.
  { by inversion Eqv'. } { iDestruct (seen_view_seen_time with "SLV'") as "[$ ?]". }
  iDestruct (bi.persistent_sep_dup with "SLV'") as "[SLV' SLV2]".

  iApply iwp_fupd.
  iApply (iwp_read _ _ _ _ _ _ _ V1 with "[$sV $HC NA AW SLV2]");
    [by eapply alloc_local_mono|done|eauto|done|..].
  { iFrame. iDestruct (seen_view_seen_time with "SLV2") as "[? %]".
    rewrite view_at_unfold_2. iDestruct "AWL" as %AWL. iPureIntro.
    eapply atw_local_mono; last exact AWL; [done|solve_lat]. }

  iNext. iIntros (𝓥' v' ?) "(s' & hist & at & AW & Ext)".
  iDestruct "Ext" as %(Le𝓥' & _ & t' & m' & HL & ISV & RH & NA').
  apply lookup_singleton_Some in HL as []. subst t' m'.
  assert (v' = v).
  { clear -ISV Eqv'. inversion ISV; clear ISV; subst;
      inversion Eqv'; clear Eqv'; congruence. } subst v'.

  iMod (own_lat_auth_update with "oL") as "[$ oTV]"; [done|].
  iIntros "!>".

  set V'' := 𝓥'.(cur).
  have LEV1 : V1 ⊑ V'' by rewrite /V'' Le𝓥 Le𝓥'.
  iApply ("Post" $! V'').
  iSplitR; last iSplitR; [iPureIntro; solve_lat|by iPureIntro|..].
  iExists t, m, _, _, ws, Va. iSplitR; [by iPureIntro|].
  rewrite (view_at_unfold_2 _ (_ ⊔ _)). iFrame "AWL ∗".
  iDestruct "NAL" as (Vna) "NA". iExists (Vna ⊔ 𝓥'.(cur)).
  iRevert "NA". iClear "#∗". iPureIntro. intros []. split; [|solve_lat].
  by apply NA'.
Qed.

Lemma ROPtsTo_to_na l γ v :
  l ro↦{γ} v ⊢ l ↦ v.
Proof.
  rewrite own_loc_na_eq ROPtsTo_eq /ROPtsTo_def /own_loc_na_def.
  iDestruct 1 as (t m rsa rns ws Va (GH & Eqv' & LeVa))
    "((sV & ARL & AWL & [%Vna NA]) & HC & As & _)".
  iExists t, m.
  iDestruct (seen_view_seen_time with "sV") as "#[st sV']". iFrame (Eqv').
  iSplitL; last first. { by iApply (monPred_in_mono with "sV'"). }
  iDestruct (view_at_elim with "sV' AWL") as "AWL".
  iExists rsa, rns, ws. iFrame (GH) "∗".
  iDestruct (seen_time_AllocLocal_singleton with "st") as "$"; [by inversion Eqv'|].
  eauto.
Qed.

End ops_rules.
