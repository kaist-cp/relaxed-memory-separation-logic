From iris.bi Require Import interface.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth.

From gpfsl.base_logic Require Import iwp.
From gpfsl.lang Require Export notation tactics.
From gpfsl.base_logic Require Export vprop na weakestpre.
From gpfsl.base_logic Require Import history base_lifting.
From gpfsl.logic Require Export relacq.

Require Import iris.prelude.options.

Section lifting.

Context `{!noprolG Σ}.

Implicit Types (P Q : vProp Σ).
Implicit Types (E : coPset) (e : expr) (v : val) (Φ : val → vProp Σ) (tid : thread_id).

Lemma wp_bind {tid E e} K Φ (SUB: ↑histN ⊆ E) :
  WP e @ tid; E {{ v, WP fill K (of_val v) @ tid; E {{ Φ }} }}
  -∗ WP fill K e @ tid; E {{ Φ }}.
Proof. (* in iProp *)
  constructor => ?. rewrite wp_eq /wp_def /=.
  iIntros "WP" (𝓥 Ext) "H𝓥 #s".
  iSpecialize ("WP" $! 𝓥 Ext with "H𝓥 s").
  iDestruct (wp_seen_post with "s WP") as "WP"; [done|].
  rewrite fill_base_nopro. iApply iwp_bind. iApply (iwp_mono with "WP").
  iIntros ([? 𝓥']) "(s & H𝓥' & WP')". rewrite -fill_base_nopro.
  by iApply ("WP'" with "[//] H𝓥'").
Qed.

Lemma wp_bindi {tid E e} Ki Φ (SUB: ↑histN ⊆ E) :
  WP e @ tid; E {{ v, WP fill_item Ki (of_val v) @ tid; E {{ Φ }} }} -∗
  WP fill_item Ki e @ tid; E {{ Φ }}.
Proof. (* in iProp *)
  constructor => ?. rewrite wp_eq /wp_def /=.
  iIntros "WP" (𝓥 Ext) "H𝓥 #s".
  iSpecialize ("WP" $! 𝓥 Ext with "H𝓥 s").
  rewrite (_: (fill_item Ki e at 𝓥)%E = nopro_lang.fill_item Ki (e at 𝓥)%E); [|done].
  iApply iwp_bind.
  iDestruct (wp_seen_post with "s WP") as "WP"; [done|].
  iApply (iwp_mono with "WP").
  iIntros ([? 𝓥']) "(s & H𝓥' & WP')". by iApply ("WP'" with "[//] H𝓥'").
Qed.

(** Base rules for core primitives of the language: Stateful reductions *)

Lemma wp_fork tid e E (SUB: ↑histN ⊆ E) :
  {{{ ▷ ∀ tid', WP e @ tid'; ⊤ {{ _, True }} }}}
    Fork e @ tid; E
  {{{ RET #☠; True }}}.
Proof.
  rewrite wp_eq /wp_def /=. iStartProof (iProp _). iIntros (Φ V).
  iIntros "WP" (??) "HΦ". iIntros (𝓥 ?) "H𝓥 #s".
  iApply wp_lift_atomic_head_step; eauto.
  iIntros (σ1 ????) "Hσ !>". iSplit.
  - iPureIntro. destruct (fork_head_step e σ1 𝓥) as [σ2 [𝓥2 STEP]].
    econstructor. do 3 eexists. exact STEP.
  - iNext. iSpecialize ("HΦ" with "[]"); first done.
    iMod (hist_interp_seen_wf with "Hσ s") as "[Hσ [%WF %HC]]"; [done|].
    iIntros (v2 σ2 efs Hstep) "_"; inv_head_step. iModIntro. iFrame. iSplit; [|done].
    iDestruct (seen_mono _ _ (nopro_lang.forkView_subseteq _) with "s") as "s'".
    iMod (own_alloc (● to_latT (nopro_lang.forkView 𝓥))) as (tid') "H𝓥'";
      [by apply auth_auth_valid|].
    iSpecialize ("WP" with "[%] H𝓥' s'"); first by etrans.
    iApply (iwp_mono with "WP"). by iIntros (?) "_".
Qed.

(** Allocation *)
Lemma wp_alloc tid E n:
  ↑histN ⊆ E → 0 < n →
  {{{ True }}}
    Alloc #n @ tid; E
  {{{ (l: loc), RET #l;
      ⎡†l…(Z.to_nat n)⎤ ∗ l ↦∗ repeat #☠ (Z.to_nat n)
      ∗ [∗ list] i ∈ seq 0 (Z.to_nat n), meta_token (l >> i) ⊤ }}}.
Proof. (* in iProp *)
  iIntros (SUB ? Φ). iStartProof (iProp _). iIntros (?) "_". iIntros (V ?) "Post".
  rewrite wp_eq /wp_def. iIntros (𝓥 ?) "H𝓥 s". iApply iwp_fupd.
  iApply (iwp_alloc with "s"); [done..|].
  iNext. iIntros (l 𝓥') "(% & s' & hF & hC & hM)".
  iMod (own_lat_auth_update with "H𝓥") as "[$ _]"; [done|].
  assert (V ⊑ 𝓥'.(cur)) by (etrans; [eassumption|by f_equiv]).
  iApply ("Post" $! l). by iFrame.
Qed.

(** Deallocation *)
Lemma wp_free tid E n (l: loc) :
  ↑histN ⊆ E → 0 ≤ n →
  {{{ ▷ ⎡†l…Z.to_nat n⎤ ∗ ▷ own_loc_vec l 1 (Z.to_nat n) }}}
    Free #n #l @ tid; E
  {{{ RET #☠; True }}}.
Proof. (* in iProp *)
  iIntros (?? Φ). iStartProof (iProp _). iIntros (?).
  iIntros "[hF own]" (? ->) "Post".
  rewrite wp_eq /wp_def.
  iIntros (𝓥 ->) "H𝓥 s". iApply iwp_fupd.
  iApply (iwp_free with "[$s $own $hF]"); [done..|].
  iNext. iIntros (𝓥') "[% ?]".
  iMod (own_lat_auth_update with "H𝓥") as "[$ _]"; [done|].
  assert (𝓥.(cur) ⊑ 𝓥'.(cur)) by by f_equiv. by iApply "Post".
Qed.

(** Reads *)
Lemma wp_read_non_atomic l q v tid E:
  ↑histN ⊆ E → {{{ l ↦{q} v }}} !#l @ tid; E {{{ RET v; l ↦{q} v }}}.
Proof. (* in iProp *)
  iIntros (? Φ). iStartProof (iProp _). iIntros (?).
  iIntros "own" (V ?) "Post". rewrite wp_eq /wp_def. iIntros (𝓥 ?) "H𝓥 s".
  iApply iwp_fupd. iApply (iwp_read_non_atomic with "[$s $own]"); [done..|].
  iNext. iIntros (𝓥') "(% & ? & ?)".
  iMod (own_lat_auth_update with "H𝓥") as "[$ _]"; [done|].
  assert (V ⊑ 𝓥'.(cur)) by (etrans; [eassumption|by f_equiv]).
  by iApply "Post".
Qed.

Lemma wp_read_atomic l q v o tid E (HRLX: Relaxed ⊑ o):
  ↑histN ⊆ E → {{{ l ↦{q} v }}} Read o #l @ tid; E {{{ RET v; l ↦{q} v }}}.
Proof.
  iIntros (? Φ). iStartProof (iProp _). iIntros (V0).
  iIntros "own" (V ?) "Post". rewrite wp_eq /wp_def. iIntros (𝓥 ?) "H𝓥 s".
  iApply iwp_fupd. rewrite own_loc_na_eq.
  iDestruct "own" as (t m) "[own [%Eqv %LE]]".
  iDestruct "own" as (rsa rsn ws WF ALL AT AW (Vna & NA & LeVna)) "(hist & at & aw & na)".
  have ?: alloc_local l {[t := m]} 𝓥.(cur).
  { eapply alloc_local_mono; [done|..|done]. by solve_lat. }
  have ?: atr_local l rsa 𝓥.(cur).
  { eapply atr_local_mono; [done|..|done]. solve_lat. }
  iApply (iwp_read_atomic with "[$s $hist at]"); [done..|].
  iNext. iIntros (𝓥' v' ?) "(s' & hist & at & Ext)".
  iDestruct "Ext" as %(Ext &?&t'&m'&[? ?]%lookup_singleton_Some&Eqv'&?&AT').
  subst t' m'.
  iMod (own_lat_auth_update with "H𝓥") as "[$ _]"; [done|].
  assert (V ⊑ 𝓥'.(cur)) by (etrans; [eassumption|by f_equiv]).
  have ?: v' = v.
  { inversion Eqv as [? Eq1|Eq1]; inversion Eqv' as [? Eq2|Eq2]; subst;
    rewrite -Eq1 in Eq2; try done. by inversion Eq2. } subst v'.
  iApply "Post". iModIntro. iExists _,_. iSplit.
  - iExists _,_,_. iFrame.
    iPureIntro. rewrite lat_le_join_r_L in AT'; [|by apply Ext].
    split; last split; last split; last split; [done| |done|..].
    + eapply alloc_local_mono; [done|apply Ext|done].
    + eapply atw_local_mono; [done|..|done]. solve_lat.
    + eexists. split; [exact NA|solve_lat].
  - iPureIntro. split; [done|]. rewrite LE -Ext. change (V0 ⊑ 𝓥.(cur)).
    solve_lat.
Qed.

Lemma wp_read l q v o tid E :
  ↑histN ⊆ E → {{{ l ↦{q} v }}} Read o #l @ tid; E {{{ RET v; l ↦{q} v }}}.
Proof. destruct o; [by apply wp_read_non_atomic|by apply wp_read_atomic..]. Qed.

Lemma wp_read_own l q o tid E (HRLX: Relaxed ⊑ o):
  ↑histN ⊆ E → {{{ l ↦{q} ? }}} Read o #l @ tid; E {{{ v, RET v; l ↦{q} ? }}}.
Proof.
  iIntros (? Φ). iStartProof (iProp _). iIntros (?).
  iIntros "own" (V ?) "Post". rewrite wp_eq /wp_def. iIntros (𝓥 ?) "H𝓥 s".
  iApply iwp_fupd. rewrite own_loc_eq.
  iDestruct "own" as (t m rsa rsn ws WF ALL AT AW (Vna & NA &?)) "(hist & at & aw & na)".
  have ?: alloc_local l {[t := m]} 𝓥.(cur).
  { eapply alloc_local_mono; [done|..|done]. by solve_lat. }
  have ?: atr_local l rsa 𝓥.(cur).
  { eapply atr_local_mono; [done|..|done]. solve_lat. }
  iApply (iwp_read_atomic with "[$s $hist at]"); [done..|].
  iNext. iIntros (𝓥' v ?) "(s' & hist & at & Ext)".
  iDestruct "Ext" as %(Ext &?&?&?&?&?&?&AT').
  iMod (own_lat_auth_update with "H𝓥") as "[$ _]"; [done|].
  assert (V ⊑ 𝓥'.(cur)) by (etrans; [eassumption|by f_equiv]).
  iApply "Post". iExists _,_,_,_,_. iFrame.
  iPureIntro. rewrite lat_le_join_r_L in AT'; [|by apply Ext].
  split; last split; last split; last split; [done| |done|..].
  - eapply alloc_local_mono; [done|apply Ext|done].
  - eapply atw_local_mono; [done|..|done]. solve_lat.
  - eexists; split; [exact NA|solve_lat].
Qed.

(** Writes *)
Lemma wp_write_non_atomic l v tid E:
  ↑histN ⊆ E → {{{ l ↦ ? }}} #l <- v @ tid; E {{{ RET #☠; l ↦ v }}}.
Proof. (* in iProp *)
  iIntros (? Φ). constructor => ?.
  iIntros "own" (V ?) "Post". rewrite wp_eq /wp_def. iIntros (??) "H𝓥 s".
  iApply iwp_fupd. iApply (iwp_write_non_atomic with "[$s $own]"); [done..|].
  iNext. iIntros (𝓥') "(% & ? & ?)".
  iMod (own_lat_auth_update with "H𝓥") as "[$ _]"; [done|].
  assert (V ⊑ 𝓥'.(cur)) by (etrans; [eassumption|by f_equiv]).
  by iApply "Post".
Qed.

Lemma wp_write_atomic l v o tid E (HRLX: Relaxed ⊑ o) :
  ↑histN ⊆ E → {{{ l ↦ ? }}} Write o #l v @ tid; E {{{ RET #☠; l ↦ v }}}.
Proof.
  iIntros (? Φ). constructor => ?.
  iIntros "own" (? ->) "Post". iApply wp_hist_inv; [done|]. iIntros (? ->) "#HInv".
  rewrite wp_eq /wp_def. iIntros (𝓥 ->) "H𝓥 s".
  iApply iwp_fupd. rewrite own_loc_eq.
  iDestruct "own" as (t m rsa rsn ws WF ALL AT AW (Vna & NA &?)) "(hist & at & aw & na)".
  iApply (iwp_write_atomic with "[$s $hist $na $aw]"); [try done..|].
  { by eapply na_local_mono; eauto. }
  iIntros "!>" (𝓥' C' t') "(s' & hist & na & aw & %F)".
  destruct F as (Ext&?&GH'&AW'&m'&?&?&Eqv'&ADD&?&?&WH). simpl in *. subst C'.
  iMod (own_lat_auth_update with "H𝓥") as "[$ _]"; [done|].
  iInv histN as (σ) ">[Hσ ctx]" "HClose".
  iMod (hist_ctx_hist_drop_singleton with "ctx hist") as "[ctx hist]";
    [|by rewrite Eqv'|].
  { move => ? [? /lookup_singleton_Some [<- _]].
    change (Some t ⊑ Some t').
    move : ALL => [?[? [/lookup_singleton_Some [<- <-] [? SL]]]].
    etrans; [apply SL|]. by apply strict_include, (write_helper_fresh WH). }
  iDestruct (hist_ctx_hist_good with "ctx hist") as %GH2.
  iMod ("HClose" with "[ctx Hσ]") as "_". { iExists _. by iFrame. }
  rewrite (monPred_mono _ _ _ (cur_mono _ _ Ext)).
  iIntros "!>". iApply "Post". rewrite own_loc_na_eq.
  iExists _,_. iSplit.
  - iExists _,_,_. iFrame "hist at na aw".
    iPureIntro. split; last split; [done| |split]; last split.
    + exists t',m'. rewrite lookup_insert Eqv'. repeat split; [done|].
      by apply (write_helper_seen_local WH).
    + eapply atr_local_mono; [done|..|done]. apply Ext.
    + rewrite lat_le_join_r_L in AW'; [done|by apply Ext].
    + eexists. split; [exact NA|]. etrans; last apply Ext. done.
  - iPureIntro. split; [by rewrite Eqv'; constructor|].
    etrans; first by eapply write_helper_read_write_relaxed_inv. by rewrite left_id.
Qed.

Lemma wp_write l v o tid E :
  ↑histN ⊆ E → {{{ l ↦ ? }}} Write o #l v @ tid; E {{{ RET #☠; l ↦ v }}}.
Proof. destruct o; [by apply wp_write_non_atomic|by apply wp_write_atomic..]. Qed.

(** Release fences *)
Lemma fill_base_constructor K e e':
  (e' = FenceRel ∨ e' = FenceAcq ∨ e' = FenceSC) →
  fill K e = e' → e = e' ∧ K = [].
Proof.
  revert e. induction K as [|k K] => e; first done.
  destruct k; simpl; move => Eq1 /(IHK _ Eq1) [??];
    subst e'; destruct Eq1 as [|[|]] => //.
Qed.

(* TODO: this should be generalized to characterizing global effects of
   taking a step *)

Lemma wp_rel_revert_view_at (P : vProp Σ) e tid E Φ :
  △{tid} P -∗
  (∀ V : view, △{tid} (⊒V) -∗ @{V} P -∗ ⊒V -∗ WP e @ tid; E {{ Φ }}) -∗
  WP e @ tid; E {{ Φ }}.
Proof.
  constructor => ?. iIntros "RP" (V ->) "WP". rewrite wp_eq /wp_def /=.
  iIntros (𝓥' Ext) "H𝓥 #s". rewrite rel_mod_eq /rel_mod_def /=.
  iDestruct "RP" as (𝓥) "[HH𝓥 RP]". rewrite view_at_unfold_2.
  iDestruct (own_lat_auth_max with "H𝓥 HH𝓥") as %Sub.
  iSpecialize ("WP" $! 𝓥.(frel)).
  iApply (monPred_mono _ _ _ Ext with "WP [HH𝓥] [RP] [] [//] H𝓥 s").
  - iExists 𝓥. iFrame "HH𝓥". by iPureIntro.
  - rewrite view_at_unfold_2. iFrame "RP".
  - iPureIntro. etrans; by [apply frel_cur|apply cur_mono].
Qed.

Lemma wp_rel_revert (P : vProp Σ) e tid E Φ :
  △{tid} P -∗
  (P -∗ WP e @ tid; E {{ Φ }}) -∗
  WP e @ tid; E {{ Φ }}.
Proof.
  iIntros "P WP". iApply (wp_rel_revert_view_at with "P").
  iIntros (V) "rV P sV". iApply "WP". iApply (view_at_elim with "sV P").
Qed.

Lemma wp_rel_fence_intro (P : vProp Σ) tid E Φ (SUB: ↑histN ⊆ E):
  P -∗ WP FenceRel @ tid; E {{ v, △{tid} P -∗ Φ v }}
    -∗ WP FenceRel @ tid; E {{ v, Φ v }}.
Proof.
  constructor => V. iIntros "P" (? Ext0) "WP".
  rewrite wp_eq /wp_def /=.
  iIntros (𝓥 Ext) "H𝓥 #s". iSpecialize ("WP" $! 𝓥 Ext with "H𝓥 s").
  rewrite (monPred_mono _ _ _ Ext0) (monPred_mono _ _ _ Ext). clear -SUB.
  iDestruct (wp_larger_view_post with "WP") as "WP".
  rewrite !wp_unfold /wp_pre /=.
  iIntros (σ1 _ κ κs n) "Hσ".
  iMod (hist_interp_seen_wf with "Hσ s") as "[Hσ [%WFm %INV]]"; [done|].
  iMod ("WP" $! σ1 0%nat κ κs n with "Hσ") as "[$ WP]". iModIntro.
  iIntros (e2 σ2 efs [K [e_ ?] [e_' 𝓥2] He1'%eq_sym He2'%eq_sym STEP]) "Hlc".
  iMod ("WP" $! _ σ2 efs with "[%] [$]") as "WP". { by econstructor. }
  rewrite /= -!fill_base_nopro in He1', He2'. inversion He1'. clear He1'. subst.
  have Eq: e_ = FenceRel ∧ K = [] by apply fill_base_constructor; [left|].
  destruct Eq. subst e_ K; simpl.
  have Ext': 𝓥 ⊑ 𝓥2 by eapply nopro_lang.head_step_tview_sqsubseteq.
  iIntros "!> !>". iMod "WP". iModIntro. iMod "WP" as "($ & WP & $)".
  iDestruct (wp_larger_view_post with "WP") as "WP".
  iModIntro. iApply iwp_fupd. iApply (iwp_wand with "WP").
  iIntros ([v 𝓥3]) "(%Ext3 & _ & H𝓥3 & Post)".
  iMod (own_lat_auth_update_fork with "H𝓥3") as "[$ ?]".
  iApply "Post". rewrite rel_mod_eq /rel_mod_def /=.
  iExists _. iFrame. rewrite view_at_unfold_2.
  assert (𝓥.(cur) ⊑ 𝓥3.(frel)); [|by iFrame].
  simpl in Ext3. rewrite Ext' -Ext3.
  inv_head_step. inversion PStep. by inversion FREL.
Qed.

Global Instance elim_modal_wp_rel_fence (P : vProp Σ) tid E Φ p :
  ElimModal (↑histN ⊆ E) p true P True
                        (WP FenceRel @ tid; E {{ Φ }})
                        (WP FenceRel @ tid; E {{ v, (△{tid} P -∗ Φ v)%I }}).
Proof.
  rewrite /ElimModal bi.intuitionistically_if_elim /= => ?.
  iIntros "[P WP]". iSpecialize ("WP" with "[//]").
  by iApply (wp_rel_fence_intro with "P WP").
Qed.

Lemma wp_rel_fence (P: vProp Σ) tid E:
  ↑histN ⊆ E → {{{ P }}} FenceRel @ tid; E {{{ RET #☠; △{tid} P }}}.
Proof.
  iIntros (SUB Φ). iStartProof (iProp _). iIntros (?) "P". iIntros (? ->) "Post".
  iApply (wp_rel_fence_intro _ _ _ Φ with "P"); [done|].
  rewrite wp_eq /wp_def. iIntros (𝓥 ->) "H𝓥 s".
  iApply iwp_fupd. iApply (iwp_rel_fence with "s"); [done|]. iNext.
  iIntros (𝓥') "(_ & [%H𝓥' _])".
  iMod (own_lat_auth_update with "H𝓥") as "[$ _]"; [done|].
  iIntros "!>". rewrite (monPred_mono _ _ _ (cur_mono _ _ H𝓥')). iFrame "Post".
Qed.

(** Acquire fences *)
Lemma wp_acq_intro (P : vProp Σ) e tid E Φ :
  P -∗
  (▽{tid} P -∗ WP e @ tid; E {{ Φ }}) -∗
  WP e @ tid; E {{ Φ }}.
Proof.
  constructor => ?. iIntros "AP" (V ->) "WP". rewrite wp_eq /wp_def /=.
  iIntros (𝓥' Ext) "H𝓥 #s". rewrite acq_mod_eq /acq_mod_def /=.
  iMod (own_lat_auth_update_fork with "H𝓥") as "[H𝓥 HH𝓥]".
  iApply ("WP" with "[AP HH𝓥] [//] H𝓥 s").
  iExists _. iFrame "HH𝓥". rewrite view_at_unfold_2.
  iApply (monPred_mono with "AP"). etrans; [done|apply cur_acq].
Qed.

Lemma wp_acq_fence_elim (P : vProp Σ) tid E Φ (SUB: ↑histN ⊆ E):
  ▽{tid} P -∗ WP FenceAcq @ tid; E {{ v, P -∗ Φ v }}
  -∗ WP FenceAcq @ tid; E {{ v, Φ v }}.
Proof.
  constructor => ?. iIntros "AP" (V ->) "WP". rewrite wp_eq /wp_def /=.
  iIntros (𝓥' Ext) "H𝓥 #s". rewrite acq_mod_eq /acq_mod_def /=.
  iDestruct "AP" as (𝓥Acq) "[F ?]".
  iDestruct (own_lat_auth_max with "H𝓥 F") as %H𝓥Acq.
  iSpecialize ("WP" $! 𝓥' Ext with "H𝓥 s").
  iDestruct (wp_larger_view_post with "WP") as "WP".
  rewrite !wp_unfold /wp_pre /=. iIntros (σ1 _ κ κs n) "Hσ".
  iMod (hist_interp_seen_wf with "Hσ s") as "[Hσ [%WFm %INV]]"; [done|].
  iMod ("WP" $! σ1 0%nat κ κs n with "Hσ") as "[$ WP]". iModIntro.
  iIntros (e2 σ2 efs [K [e_ ?] [e_' 𝓥2] He1'%eq_sym He2'%eq_sym STEP]) "Hlc".
  iMod ("WP" $! _ σ2 efs with "[%] [$]") as "WP". { by econstructor. }
  rewrite /= -!fill_base_nopro in He1', He2'. inversion He1'. clear He1'. subst.
  have Eq: e_ = FenceAcq ∧ K = [] by apply fill_base_constructor; [right;left|].
  destruct Eq. subst e_ K; simpl.
  have Ext': 𝓥' ⊑ 𝓥2. { by eapply nopro_lang.head_step_tview_sqsubseteq. }
  iIntros "!> !>". iMod "WP". iModIntro. iMod "WP" as "($ & WP & $)".
  iDestruct (wp_larger_view_post with "WP") as "WP".
  iModIntro. iApply (iwp_wand with "WP").
  iIntros ([v 𝓥3]) "/= (% & _ & $ & H)". iApply "H". rewrite view_at_unfold_2.
  assert (𝓥Acq.(acq) ⊑ 𝓥3.(cur)); [|by iFrame].
  rewrite H𝓥Acq.
  inv_head_step. inversion PStep. inversion FACQ. subst. simpl in *.
  change 𝓥'.(acq) with (acq_fence_tview 𝓥').(cur). by f_equiv.
Qed.

Global Instance elim_modal_wp_acq_fence  (P : vProp Σ) tid E Φ p:
  ElimModal (↑histN ⊆ E) p true (▽{tid} P) True
                          (WP (FenceAcq) @ tid; E {{ Φ }})
                          (WP (FenceAcq) @ tid; E {{ v, P -∗ Φ v }})%I.
Proof.
  rewrite /ElimModal bi.intuitionistically_if_elim /= => ?.
  iIntros "[AP WP]". iSpecialize ("WP" with "[//]").
  by iApply (wp_acq_fence_elim with "AP WP").
Qed.

Lemma wp_acq_fence (P: vProp Σ) tid E:
  ↑histN ⊆ E → {{{ ▽{tid} P }}} FenceAcq @ tid; E {{{ RET #☠; P }}}.
Proof.
  iIntros (SUB Φ). iStartProof (iProp _). iIntros (?) "P". iIntros (??) "Post".
  iApply (wp_acq_fence_elim _ _ _ Φ with "P"); [done|].
  rewrite wp_eq /wp_def. iIntros (𝓥 ->) "H𝓥 s".
  iApply iwp_fupd. iApply (iwp_acq_fence with "s"); [done|]. iNext.
  iIntros (𝓥') "(_ & [%H𝓥' _])".
  iMod (own_lat_auth_update with "H𝓥") as "[$ _]"; [done|].
  iIntros "!>". rewrite (monPred_mono _ _ _ (cur_mono _ _ H𝓥')). iFrame "Post".
Qed.

(** SC fences *)
Lemma wp_sc_fence_rel_intro (P : vProp Σ) tid E Φ (SUB: ↑histN ⊆ E):
  P -∗ WP FenceSC @ tid; E {{ v, △{tid} P -∗ Φ v }}
  -∗ WP FenceSC @ tid; E {{ v, Φ v }}.
Proof.
  constructor => V. iIntros "P" (? Ext0) "WP".
  rewrite wp_eq /wp_def /=.
  iIntros (𝓥 Ext) "H𝓥 #s". iSpecialize ("WP" $! 𝓥 Ext with "H𝓥 s").
  rewrite (monPred_mono _ _ _ Ext0) (monPred_mono _ _ _ Ext). clear -SUB.
  iDestruct (wp_larger_view_post with "WP") as "WP".
  rewrite !wp_unfold /wp_pre /=.
  iIntros (σ1 _ κ κs n) "Hσ".
  iMod (hist_interp_seen_wf with "Hσ s") as "[Hσ [%WFm %INV]]"; [done|].
  iMod ("WP" $! σ1 0%nat κ κs n with "Hσ") as "[$ WP]". iModIntro.
  iIntros (e2 σ2 efs [K [e_ ?] [e_' 𝓥2] He1'%eq_sym He2'%eq_sym STEP]) "Hlc".
  iMod ("WP" $! _ σ2 efs with "[%] [$]") as "WP". { by econstructor. }
  rewrite /= -!fill_base_nopro in He1', He2'. inversion He1'. clear He1'. subst.
  have Eq: e_ = FenceSC ∧ K = [] by apply fill_base_constructor; [right;right|].
  destruct Eq. subst e_ K; simpl.
  have Ext': 𝓥 ⊑ 𝓥2 by eapply nopro_lang.head_step_tview_sqsubseteq.
  iIntros "!> !>". iMod "WP". iModIntro. iMod "WP" as "($ & WP & $)".
  iDestruct (wp_larger_view_post with "WP") as "WP".
  iModIntro. iApply iwp_fupd. iApply (iwp_wand with "WP").
  iIntros ([v 𝓥3]) "(%Ext3 & _ & H𝓥3 & Post)".
  iMod (own_lat_auth_update_fork with "H𝓥3") as "[$ ?]".
  iApply "Post". rewrite rel_mod_eq /rel_mod_def /=.
  iExists _. iFrame. rewrite view_at_unfold_2.
  assert (𝓥.(cur) ⊑ 𝓥3.(frel)); [|by iFrame].
  simpl in Ext3. rewrite Ext' -Ext3.
  inv_head_step. inversion PStep. inversion FSC. by inversion SC.
Qed.

Global Instance elim_modal_wp_sc_fence_rel (P : vProp Σ) tid E Φ p:
  ElimModal (↑histN ⊆ E) p true P True
                (WP FenceSC @ tid; E {{ Φ }})
                (WP FenceSC @ tid; E {{ v, (△{tid} P -∗ Φ v)%I }}).
Proof.
  rewrite /ElimModal bi.intuitionistically_if_elim /= => ?.
  iIntros "[P WP]". iSpecialize ("WP" with "[//]").
  by iApply (wp_sc_fence_rel_intro with "P WP").
Qed.

Lemma wp_sc_rel_fence (P: vProp Σ) tid E:
  ↑histN ⊆ E → {{{ P }}} FenceSC @ tid; E {{{ RET #☠; △{tid} P }}}.
Proof.
  iIntros (SUB Φ). iStartProof (iProp _). iIntros (?) "P". iIntros (? ->) "Post".
  iApply (wp_sc_fence_rel_intro _ _ _ Φ with "P"); [done|].
  rewrite wp_eq /wp_def. iIntros (𝓥 ->) "H𝓥 s".
  iApply iwp_fupd. iApply (iwp_sc_fence' with "s"); [done|]. iNext.
  iIntros (𝓢' 𝓥') "(_ & _ & [%H𝓥' _])".
  iMod (own_lat_auth_update with "H𝓥") as "[$ _]"; [done|].
  iIntros "!>". rewrite (monPred_mono _ _ _ (cur_mono _ _ H𝓥')). iFrame "Post".
Qed.

Lemma wp_sc_fence_acq_elim (P : vProp Σ) tid E Φ (SUB: ↑histN ⊆ E):
  ▽{tid} P -∗ WP FenceSC @ tid; E {{ v, P -∗ Φ v }}
  -∗ WP FenceSC @ tid; E {{ v, Φ v }}.
Proof.
  constructor => ?. iIntros "AP" (V ->) "WP".
  rewrite wp_eq /wp_def acq_mod_eq /acq_mod_def /=.
  iIntros (𝓥' Ext) "H𝓥 #s".
  iDestruct "AP" as (𝓥Acq) "[F ?]".
  iDestruct (own_lat_auth_max with "H𝓥 F") as %H𝓥Acq.
  iSpecialize ("WP" $! 𝓥' Ext with "H𝓥 s").
  iDestruct (wp_larger_view_post with "WP") as "WP".
  rewrite !wp_unfold /wp_pre /=. iIntros (σ1 _ κ κs n) "Hσ".
  iMod (hist_interp_seen_wf with "Hσ s") as "[Hσ [%WFm %INV]]"; [done|].
  iMod ("WP" $! σ1 0%nat κ κs n with "Hσ") as "[$ WP]". iModIntro.
  iIntros (e2 σ2 efs [K [e_ ?] [e_' 𝓥2] He1'%eq_sym He2'%eq_sym STEP]) "Hlc".
  iMod ("WP" $! _ σ2 efs with "[%] [$]") as "WP". { by econstructor. }
  rewrite /= -!fill_base_nopro in He1', He2'. inversion He1'. clear He1'. subst.
  have Eq: e_ = FenceSC ∧ K = [] by apply fill_base_constructor; [right;right|].
  destruct Eq. subst e_ K; simpl.
  have Ext': 𝓥' ⊑ 𝓥2. { by eapply nopro_lang.head_step_tview_sqsubseteq. }
  iIntros "!> !>". iMod "WP". iModIntro. iMod "WP" as "($ & WP & $)".
  iDestruct (wp_larger_view_post with "WP") as "WP".
  iModIntro. iApply (iwp_wand with "WP").
  iIntros ([v 𝓥3]) "/= (%Ext3 & _ & $ & H)". iApply "H".
  rewrite view_at_unfold_2.
  assert (𝓥Acq.(acq) ⊑ 𝓥3.(cur)); [|by iFrame].
  simpl in Ext3. rewrite H𝓥Acq -Ext3.
  inv_head_step. inversion PStep.
  inversion FSC. inversion SC. subst. simpl in *. solve_lat.
Qed.

Global Instance elim_modal_wp_sc_fence_acq (P : vProp Σ) tid E Φ p:
  ElimModal (↑histN ⊆ E) p true (▽{tid} P) True
                            (WP FenceSC @ tid; E {{ Φ }})
                            (WP FenceSC @ tid; E {{ v, P -∗ Φ v }})%I.
Proof.
  rewrite /ElimModal bi.intuitionistically_if_elim /= => ?.
  iIntros "[AP WP]". iSpecialize ("WP" with "[//]").
  by iApply (wp_sc_fence_acq_elim with "AP WP").
Qed.

Lemma wp_sc_acq_fence (P: vProp Σ) tid E:
  ↑histN ⊆ E → {{{ ▽{tid} P }}} FenceSC @ tid; E {{{ RET #☠; P }}}.
Proof.
  iIntros (SUB Φ). iStartProof (iProp _). iIntros (?) "P". iIntros (??) "Post".
  iApply (wp_sc_fence_acq_elim _ _ _ Φ with "P"); [done|].
  rewrite wp_eq /wp_def. iIntros (𝓥 ->) "H𝓥 s".
  iApply iwp_fupd. iApply (iwp_sc_fence' with "s"); [done|]. iNext.
  iIntros (𝓢' 𝓥') "(_ & _ & [%H𝓥' _])".
  iMod (own_lat_auth_update with "H𝓥") as "[$ _]"; [done|].
  iIntros "!>". rewrite (monPred_mono _ _ _ (cur_mono _ _ H𝓥')). iFrame "Post".
Qed.


(** Pointer comparison *)
Lemma wp_eq_loc tid E (l1 l2 : loc) q1 q2 P Φ (SUB: ↑histN ⊆ E):
  (P -∗ ▷ l1 ↦{q1} ?) →
  (P -∗ ▷ l2 ↦{q2} ?) →
  (P -∗ ▷ Φ (#(bool_decide (l1 = l2)))) →
  P -∗ WP #l1 = #l2 @ tid; E {{ Φ }}.
Proof.
  iIntros (Hl1 Hl2 Hpost). iStartProof (iProp _).
  iIntros (?) "HP". rewrite wp_eq /wp_def. iIntros (𝓥 ->) "H𝓥 _".
  destruct (bool_decide_reflect (l1 = l2)) as [->|].
  - iApply wp_lift_pure_det_head_step_no_fork'; [done| | |].
    + repeat intro. eexists _, _, _, []; repeat constructor.
    + intros. by inv_head_step; inv_bin_op_eval; inv_lit.
    + iPoseProof (Hpost with "HP") as "?".
      iIntros "!> _". iApply iwp_value. iFrame.
  - iApply wp_lift_atomic_head_step_no_fork; subst=>//.
    iIntros (σ1 ? κ κs ?) "Hσ1 !>". inv_head_step.
    iSplitR.
    { iPureIntro. eexists _, _, _, []. constructor; [|by simpl].
      apply BinOpS, BinOpEqFalse. by constructor. }
    (* We need to do a little gymnastics here to apply Hne now and strip away a
       ▷ but also have the ↦s. *)
    iAssert (((▷ ∃ q, l1 ↦{q} ?) ∧ (▷ ∃ q, l2 ↦{q} ?)
                ∧ ▷ Φ (LitV false)) 𝓥.(cur))%I with "[HP]" as "HP".
    { iSplit; last iSplit.
      + iExists _. by iApply Hl1.
      + iExists _. by iApply Hl2.
      + by iApply Hpost. }
    clear Hl1 Hl2. iNext. iIntros (e2 σ2 efs Hs) "_".
    inv_head_step. iSplitR=>//. inv_bin_op_eval; inv_lit.
    iModIntro. iDestruct "HP" as "[_ [_ HP]]". iFrame.
Qed.

(** Proof rules for working on the n-ary argument list. *)
Lemma wp_app_ind tid E f
  (el : list expr) (Ql : vec (val → vProp Σ) (length el)) vs Φ
  (SUB: ↑histN ⊆ E) :
  AsVal f →
  ([∗ list] eQ ∈ zip el Ql, WP eQ.1 @ tid; E {{ eQ.2 }}) -∗
    (∀ vl : vec val (length el), ([∗ list] vQ ∈ zip vl Ql, vQ.2 $ vQ.1) -∗
                    WP App f (of_val <$> vs ++ vl) @ tid; E {{ Φ }}) -∗
    WP App f ((of_val <$> vs) ++ el) @ tid; E {{ Φ }}.
Proof.
  intros [vf <-]. revert vs Ql.
  induction el as [|e el IH]=>/= vs Ql; inv_vec Ql; simpl.
  - iIntros "_ H". iSpecialize ("H" $! [#]). rewrite !app_nil_r /=. by iApply "H".
  - iIntros (Q Ql) "[He Hl] HΦ".
    change (App (of_val vf) ((of_val <$> vs) ++ e :: el)) with (fill_item (AppRCtx vf vs el) e).
    iApply (wp_bind [_]); [done|]. iApply (wp_wand with "He").
    iIntros (v) "HQ /=".
    rewrite cons_middle (assoc app) -(fmap_app _ _ [v]) //.
    iApply (IH _ _ with "Hl"). iIntros "* Hvl". rewrite -assoc.
    iApply ("HΦ" $! (v:::vl)). iFrame.
Qed.

Lemma wp_app_vec tid E f el (Ql : vec (val → vProp Σ) (length el)) Φ
  (SUB: ↑histN ⊆ E):
  AsVal f →
  ([∗ list] eQ ∈ zip el Ql, WP eQ.1 @ tid; E {{ eQ.2 }}) -∗
    (∀ vl : vec val (length el), ([∗ list] vQ ∈ zip vl Ql, vQ.2 $ vQ.1) -∗
                    WP App f (of_val <$> (vl : list val)) @ tid; E {{ Φ }}) -∗
    WP App f el @ tid; E {{ Φ }}.
Proof. iIntros (Hf). by iApply (wp_app_ind _ _ _ _ _ []). Qed.

Lemma wp_app (Ql : list (val → vProp Σ)) tid E f el Φ
  (SUB: ↑histN ⊆ E) :
  length Ql = length el → AsVal f →
  ([∗ list] eQ ∈ zip el Ql, WP eQ.1 @ tid; E {{ eQ.2 }}) -∗
    (∀ vl : list val, ⌜length vl = length el⌝ -∗
            ([∗ list] k ↦ vQ ∈ zip vl Ql, vQ.2 $ vQ.1) -∗
             WP App f (of_val <$> (vl : list val)) @ tid; E {{ Φ }}) -∗
    WP App f el @ tid; E {{ Φ }}.
Proof.
  iIntros (Hlen Hf) "Hel HΦ". rewrite -(vec_to_list_to_vec Ql).
  generalize (list_to_vec Ql). rewrite Hlen. clear Hlen Ql=>Ql.
  iApply (wp_app_vec with "Hel"); [done|]. iIntros (vl) "Hvl".
  iApply ("HΦ" with "[%] Hvl"). by rewrite vec_to_list_length.
Qed.

(* NOTES: for other lemmas, look for the iProp version (iwp_) in base_lifting. *)

(* TODO: add syscall to the language *)

End lifting.
