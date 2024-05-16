From iris.algebra Require Import auth.
From iris.proofmode Require Import proofmode.

From gpfsl.base_logic Require Import base_lifting.
From gpfsl.logic Require Import lifting.
From gpfsl.logic Require Import invariants.

Require Import iris.prelude.options.

Section sc_invariant.
  Context `{!noprolG Σ}.
  #[local] Notation vProp := (vProp Σ).
  Implicit Types (P Q : vProp) (N: namespace) (E: coPset).

  Definition sc_inv_def N P: vProp :=
    (∃ V, ⊒V ∗ inv N (@{V} P ∨ ∃ 𝓢, ⌜V ⊑ 𝓢⌝ ∗ ⎡ sc_view 𝓢 ⎤ ∗ @{𝓢} P))%I.
  Definition sc_inv_aux : seal (@sc_inv_def). Proof. by eexists. Qed.
  Definition sc_inv := unseal (@sc_inv_aux).
  Definition sc_inv_eq : @sc_inv = _ := seal_eq _.

  #[global] Instance sc_inv_persistent N P : Persistent (sc_inv N P).
  Proof. rewrite sc_inv_eq. apply _. Qed.
  #[global] Instance sc_inv_contractive N : Contractive (sc_inv N).
  Proof. rewrite sc_inv_eq. solve_contractive. Qed.
  #[global] Instance sc_inv_ne N : NonExpansive (sc_inv N) := _.
  #[global] Instance sc_inv_proper N : Proper ((≡) ==> (≡)) (sc_inv N) := _.

  Lemma sc_inv_alloc P N E : ▷ P ={E}=∗ sc_inv N P.
  Proof.
    rewrite (view_at_intro (▷ _)%I) sc_inv_eq. iDestruct 1 as (V) "[In P]".
    iExists V. iMod (inv_alloc with "[P]") as "$"; last done.
    iLeft. iNext. by iFrame.
  Qed.

  Lemma sc_inv_fence P Q N tid E:
    ↑N ⊆ E → ↑histN ⊆ E → N ## histN →
    {{{ sc_inv N P ∗ ▷ ▽{tid}(P ={E∖↑N}=∗ P ∗ Q) }}}
      FenceSC @ tid; @ E
    {{{ RET #☠; △{tid} Q }}}.
  Proof.
    iIntros (SUB1 SUB2 DISJ Φ). iStartProof (iProp _).
    iIntros (?) "[Inv VS]". iIntros (V ->) "Post".
    rewrite wp_eq /wp_def sc_inv_eq /sc_inv_def acq_mod_eq /=.
    iIntros (𝓥 Ext) "H𝓥 #s".
    iDestruct "Inv" as (V0 Ext0) "#Inv".
    iDestruct "VS" as (𝓥acq) "[#>H𝓥acq VS]".
    iDestruct (own_lat_auth_max with "H𝓥 H𝓥acq") as %H𝓥acq.
    have SUB3: ↑histN ⊆ E ∖ ↑N by solve_ndisj.
    iMod (inv_acc with "Inv") as "[[HP|HP] Close]"; [done|..].
    - iApply (iwp_sc_fence' with "[$s]"); [done|].
      iIntros "!>" (𝓢' 𝓥') "(#s' & #SC & F)". iDestruct "F" as %(H𝓥 & 𝓢0 & SH).
      iMod (own_lat_auth_update with "H𝓥") as "[$ #H𝓥acq']"; [done|].
      rewrite view_at_unfold_2 (monPred_mono _ 𝓥acq.(acq) 𝓥'.(cur)); last first.
      { rewrite H𝓥acq. inversion SH. subst. simpl in *. solve_lat. }
      iMod ("VS" with "[HP]") as "[HP HQ]".
      { rewrite view_at_unfold_2.
        iApply (monPred_mono with "HP"). by rewrite Ext0 Ext H𝓥. }
      iMod ("Close" with "[HP]") as "_".
      { iRight. iNext. iExists 𝓢'. iFrame "SC". iSplit.
        - iPureIntro. inversion SH. subst. simpl in *.
          rewrite Ext0 Ext cur_acq. solve_lat.
        - rewrite view_at_unfold_2. iApply (monPred_mono with "HP"). by inversion SH. }
      iIntros "!>".
      rewrite (monPred_mono (_ -∗ _)%I V 𝓥'.(cur)); last by rewrite Ext H𝓥.
      iApply "Post". rewrite rel_mod_eq. iExists 𝓥'. iFrame "H𝓥acq'".
      rewrite view_at_unfold_2.
      iApply (monPred_mono with "HQ"). by inversion SH.
    - iDestruct "HP" as (𝓢) "(>%H𝓢 & >#SC & HP)".
      iApply (iwp_sc_fence with "[$s $SC]"); [done|].
      iIntros "!>" (𝓢' 𝓥') "(#s' & #SC' & F)". iDestruct "F" as %(H𝓥 & 𝓢0 & H𝓢' & SH).
      iMod (own_lat_auth_update with "H𝓥") as "[$ #H𝓥acq']"; [done|].
      rewrite view_at_unfold_2 (monPred_mono _ 𝓥acq.(acq) 𝓥'.(cur)); last first.
      { rewrite H𝓥acq. inversion SH. subst. simpl in *. solve_lat. }
      iMod ("VS" with "[HP]") as "[HP HQ]".
      { rewrite view_at_unfold_2.
        iApply (monPred_mono with "HP"). inversion SH. solve_lat. }
      iMod ("Close" with "[HP]") as "_".
      { iRight. iNext. iExists 𝓢'. iFrame "SC'". iSplit.
        - iPureIntro. inversion SH. subst. simpl in *.
          rewrite Ext0 Ext cur_acq. solve_lat.
        - rewrite view_at_unfold_2.
          iApply (monPred_mono with "HP"). by inversion SH. }
      iIntros "!>".
      rewrite (monPred_mono (_ -∗ _)%I V 𝓥'.(cur)); last by rewrite Ext H𝓥.
      iApply "Post". rewrite rel_mod_eq. iExists 𝓥'. iFrame "H𝓥acq'".
      rewrite view_at_unfold_2.
      iApply (monPred_mono with "HQ"). by inversion SH.
  Qed.
End sc_invariant.

#[global] Instance: Params (@sc_inv) 1 := {}.
#[global] Typeclasses Opaque sc_inv.
