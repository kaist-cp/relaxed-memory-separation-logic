From iris.proofmode Require Export proofmode.
From iris.algebra Require Import gmap excl auth.
From iris.program_logic Require weakestpre.
From iris.program_logic Require Import ownp.
From gpfsl.base_logic Require Export history vprop.
From gpfsl.lang Require Export notation tactics.

Require Import iris.prelude.options.

Implicit Types (σ : state) (E : coPset) (e : expr)
               (tid : thread_id) (𝓥 : threadView).

Local Existing Instances
  histGpreS_hist histGpreS_freeable histGpreS_read histGpreS_na_view
  histGpreS_at_write histGpreS_tview
  hist_inG
  .

Section base_prop.
Context `{!noprolG Σ}.
Implicit Type (Φ : val → vProp Σ).

Lemma hist_head_step_seen e e' efs 𝓥 𝓥' σ σ' κs
  (IN: 𝓥 ∈ σ.(mem)) (WF: Wf σ):
  nopro_lang.head_step (e at 𝓥)%E σ κs (e' at 𝓥')%E σ' efs →
  hist_ctx σ' -∗ seen 𝓥 ==∗
  hist_ctx σ' ∗ seen 𝓥' ∗ ([∗ list] ef ∈ efs, seen ef.(nopro_lang.expr_view)).
Proof.
  iIntros (STEP) "ctx #s". inv_head_step.
  - iFrame "ctx #". destruct efs as [|?[]]; inversion BaseStep; subst=>//=.
    inversion ForkViews as [|? ? Eq1]. subst. rewrite -Eq1.
    by iDestruct (seen_mono _ _ (nopro_lang.forkView_subseteq _) with "s") as "$".
  - iDestruct "ctx" as (hF V Vc) "(MEM & HF & NA & AW & AR & SC & VT & WF)".
    iDestruct "WF" as %(WFs & HRel & IN' & LE).
    iMod (own_lat_auth_update_join _ V (𝓥'.(acq)) with "VT") as "[VT VTo]".
    have INV' := machine_step_closed_tview _ _ _ _ _ _ _ _ _ PStep
                    (global_wf_mem _ WF) IN (global_wf_sc _ WF).
    iDestruct (seen_own_join with "VTo") as "$".
    iModIntro. iExists _, _, _. iFrame. iPureIntro.
    do 2 (split; [done|]). split; [|done].
    apply join_closed_view; [done|by apply INV'].
Qed.

Lemma hist_interp_head_step_seen
  e e' efs 𝓥 𝓥' σ σ' κs E
  (IN: 𝓥 ∈ σ.(mem)) (WF: Wf σ) (SUB: ↑histN ⊆ E) :
  nopro_lang.head_step (e at 𝓥)%E σ κs (e' at 𝓥')%E σ' efs →
  hist_interp σ' -∗ seen 𝓥 ={E}=∗
  hist_interp σ' ∗ seen 𝓥' ∗ ([∗ list] ef ∈ efs, seen ef.(nopro_lang.expr_view)).
Proof.
  iIntros (STEP) "Hσ' Hs".
  iMod (hist_interp_open _ _ SUB with "Hσ'") as "[Hσ' HClose]".
  iMod (hist_head_step_seen _ _ _ _ _ _ _ _ IN WF STEP with "Hσ' Hs")
    as "(Hσ' & $ & $)".
  by iMod ("HClose" with "Hσ'") as "$".
Qed.

Lemma wp_larger_view_post E e (Φ: nopro_lang.val → iProp Σ) 𝓥 :
  WP e at 𝓥 @ E {{ Φ }} -∗
  WP e at 𝓥 @ E {{ λ v𝓥', ⌜𝓥 ⊑ (nopro_lang.of_val v𝓥').(nopro_lang.expr_view)⌝ ∗ Φ v𝓥' }}%V.
Proof.
  iLöb as "IH" forall (e 𝓥). iIntros "WP".
  rewrite !wp_unfold /wp_pre /= /nopro_lang.to_val /=.
  destruct (to_val e) as [v|] eqn:EQe; simpl; [by iSplitL ""|].
  iIntros (σ _ κs _ n) "Hσ". iMod ("WP" $! σ 0%nat κs κs n with "Hσ") as "[$ WP]".
  iIntros "!>" (e' σ' efs [K [e_ ?] [e_' 𝓥'] He1'%eq_sym He2'%eq_sym STEP]) "Hlc".
  iMod ("WP" $! e' σ' efs with "[%] [$]") as "WP". { by econstructor. }
  iIntros "!> !>". iMod "WP". iModIntro. iMod "WP" as "($ & WP & $)".
  rewrite /= -!fill_base_nopro in He1', He2'. inversion He1'. subst.
  iModIntro. iSpecialize ("IH" $! _ _ with "WP").
  iApply (wp_wand with "IH"); [done..|]. iIntros (?) "(% & $)". iPureIntro.
  etrans.
  + apply (nopro_lang.head_step_tview_sqsubseteq _ _ _ _ _ _ _ _ STEP). + done.
Qed.

Lemma wp_larger_view_post_inv E e (Φ: nopro_lang.val → iProp Σ) 𝓥 :
  WP e at 𝓥 @ E {{ λ v𝓥', ⌜𝓥 ⊑ (nopro_lang.of_val v𝓥').(nopro_lang.expr_view)⌝ -∗ Φ v𝓥' }} -∗
  WP e at 𝓥 @ E {{ Φ }}%V.
Proof.
  iLöb as "IH" forall (e 𝓥). iIntros "WP".
  rewrite !wp_unfold /wp_pre /= /nopro_lang.to_val /=.
  destruct (to_val e) as [v|] eqn:EQe; simpl.
  { by iMod ("WP" with "[//]") as "$". }
  iIntros (σ _ κs _ n) "Hσ". iMod ("WP" $! σ 0%nat κs κs n with "Hσ") as "[$ WP]".
  iIntros "!>" (e' σ' efs [K [e_ ?] [e_' 𝓥'] He1'%eq_sym He2'%eq_sym STEP]) "Hlc".
  iMod ("WP" $! e' σ' efs with "[%] [$]") as "WP". { by econstructor. }
  iIntros "!> !>". iMod "WP". iModIntro. iMod "WP" as "($ & WP & $)".
  rewrite /= -!fill_base_nopro in He1', He2'. inversion He1'. subst.
  iModIntro.
  iApply "IH". iApply (wp_wand with "WP").
  iIntros (?) "HV". iIntros (Le). iApply "HV". iPureIntro.
  etrans; last exact Le.
  by apply (nopro_lang.head_step_tview_sqsubseteq _ _ _ _ _ _ _ _ STEP).
Qed.

Lemma wp_seen_post E e (Φ: nopro_lang.val → iProp Σ) 𝓥 (SUB: ↑histN ⊆ E) :
  seen 𝓥 -∗
  WP e at 𝓥 @ E {{ Φ }} -∗
  WP e at 𝓥 @ E {{ λ v𝓥', seen (nopro_lang.of_val v𝓥').(nopro_lang.expr_view) ∗ Φ v𝓥' }}%V.
Proof.
  iLöb as "IH" forall (e 𝓥). iIntros "#Hs WP".
  rewrite !wp_unfold /wp_pre /= /nopro_lang.to_val /=.
  destruct (to_val e) as [v|] eqn:EQe; simpl; [by iFrame "Hs"|].
  iIntros (σ _ κs' _ n) "Hσ".
  iMod (hist_interp_seen_wf _ _ _ SUB with "Hσ Hs") as "[Hσ [%WFm %INV]]".
  iMod ("WP" $! σ 0%nat κs' κs' n with "Hσ") as "[$ WP]". iModIntro.
  iIntros (e' σ' efs [K [e_ ?] [e_' 𝓥'] He1'%eq_sym He2'%eq_sym STEP]) "Hlc".
  iMod ("WP" $! e' σ' efs with "[%] [$]") as "WP". { by econstructor. }
  iIntros "!> !>". iMod "WP". iModIntro. iMod "WP" as "(Hσ' & WP & $)".
  rewrite /= -!fill_base_nopro in He1', He2'. inversion He1'. subst.
  iMod (hist_interp_head_step_seen _ _ _ _ _ _ _ _ _ INV WFm SUB STEP with "Hσ' Hs")
    as "($ & #Hs' & _)".
  by iApply "IH".
Qed.

Lemma wp_seen_post_inv E e (Φ: nopro_lang.val → iProp Σ) 𝓥 (SUB: ↑histN ⊆ E) :
  seen 𝓥 -∗
  WP e at 𝓥 @ E {{ λ v𝓥', seen (nopro_lang.of_val v𝓥').(nopro_lang.expr_view) -∗ Φ v𝓥' }} -∗
  WP e at 𝓥 @ E {{ Φ }}%V.
Proof.
  iLöb as "IH" forall (e 𝓥). iIntros "#Hs WP".
  rewrite !wp_unfold /wp_pre /= /nopro_lang.to_val /=.
  destruct (to_val e) as [v|] eqn:EQe; simpl.
  { by iMod ("WP" with "Hs") as "$". }
  iIntros (σ _ κs' _ n) "Hσ".
  iMod (hist_interp_seen_wf _ _ _ SUB with "Hσ Hs") as "[Hσ [%WFm %INV]]".
  iMod ("WP" $! σ 0%nat κs' κs' n with "Hσ") as "[$ WP]". iModIntro.
  iIntros (e' σ' efs [K [e_ ?] [e_' 𝓥'] He1'%eq_sym He2'%eq_sym STEP]) "Hlc".
  iMod ("WP" $! e' σ' efs with "[%] [$]") as "WP". { by econstructor. }
  iIntros "!> !>". iMod "WP". iModIntro. iMod "WP" as "(Hσ' & WP & $)".
  rewrite /= -!fill_base_nopro in He1', He2'. inversion He1'. subst.
  iMod (hist_interp_head_step_seen _ _ _ _ _ _ _ _ _ INV WFm SUB STEP with "Hσ' Hs")
    as "($ & #Hs' & _)".
  by iApply ("IH" with "Hs' WP").
Qed.
End base_prop.

Program Definition wp_def `{!noprolG Σ} : Wp (vPropI Σ) expr val thread_id :=
  λ tid E e Φ,
    MonPred (λ V,
      ∀ 𝓥, ⌜V ⊑ 𝓥.(cur)⌝ -∗ own tid (● to_latT 𝓥) -∗ seen 𝓥 -∗
        WP e at 𝓥 @ E {{ λ v𝓥', let '(v at 𝓥') := v𝓥' return _ in
          own tid (● to_latT 𝓥') ∗ (Φ v) 𝓥'.(cur) }})%I%V _.
Next Obligation. solve_proper. Qed.
Definition wp_aux : seal (@wp_def). Proof. by eexists. Qed.
Definition wp' := unseal (wp_aux).
Global Arguments wp' {Σ _}.
Global Existing Instance wp'.

Lemma wp_eq `{!noprolG Σ} : wp = @wp_def Σ _.
Proof. rewrite -wp_aux.(seal_eq) //. Qed.

Section WeakestPre.
Context `{!noprolG Σ}.
Implicit Type (Φ : val → vProp Σ).

Global Instance wp_ne tid E e n :
  Proper (pointwise_relation _ (dist n) ==> dist n) (wp tid E e).
Proof. rewrite wp_eq. split=>V. solve_proper. Qed.
Global Instance wp_proper tid E e :
  Proper (pointwise_relation _ (≡) ==> (≡)) (wp tid E e).
Proof. rewrite wp_eq. split=>V. solve_proper. Qed.

Lemma wp_value' tid E Φ v : Φ v ⊢ wp tid E (of_val v) Φ.
Proof.
  rewrite wp_eq /wp_def. iStartProof (iProp _). iIntros "% HΦ % -> ? _".
  iApply (wp_value' _ _ _ (v at _)). iFrame.
Qed.

Lemma wp_strong_mono tid E1 E2 e Φ Ψ :
  E1 ⊆ E2 → wp tid E1 e Φ -∗ (∀ v, Φ v ={E2}=∗ Ψ v) -∗ wp tid E2 e Ψ.
Proof.
  rewrite wp_eq /wp_def. iStartProof (iProp _).
  iIntros "%% WP %-> H /=" (𝓥 H𝓥) "H𝓥 #Hs".
  iApply (wp_strong_mono NotStuck _ E1 with "[WP H𝓥]"); [done|done| |].
  { iApply wp_larger_view_post. by iApply ("WP" with "[//] H𝓥"). }
  iIntros ([v 𝓥']) "/= (% & $ & HΦ)". iSpecialize ("H" $! v).
  rewrite (monPred_mono _ _ _ H𝓥) (monPred_mono _ _ _ (cur_mono 𝓥 𝓥' _)) //.
  iApply ("H" with "HΦ").
Qed.

Lemma fupd_wp tid E e Φ :
  (|={E}=> wp tid E e Φ) ⊢ wp tid E e Φ.
Proof.
  rewrite wp_eq /wp_def. iStartProof (iProp _). iIntros "% H %% ?".
  iMod "H". by iApply "H".
Qed.

Lemma wp_fupd tid E e Φ : wp tid E e (λ v, |={E}=> Φ v) ⊢ wp tid E e Φ.
Proof.
  rewrite wp_eq /wp_def. iStartProof (iProp _). iIntros "% H %% H𝓥 ? /=".
  iApply wp_fupd. iApply wp_mono; [|by iApply ("H" with "[//] H𝓥")].
  by iIntros ([??]) "[$ H]".
Qed.

Lemma wp_atomic tid E1 E2 e Φ `{!Atomic e} :
  (|={E1,E2}=> wp tid E2 e (λ v, |={E2,E1}=> Φ v)) ⊢ wp tid E1 e Φ.
Proof.
  iStartProof (iProp _). rewrite wp_eq /wp_def. iIntros "% H %% H𝓥 #?".
  iApply wp_atomic. iMod "H". iModIntro.
  iApply wp_mono; [|by iApply ("H" with "[//] H𝓥")]. by iIntros ([??]) "[$ ?]".
Qed.

Lemma wp_step_fupd tid E1 E2 e P Φ :
  to_val e = None → E2 ⊆ E1 →
  (|={E1}[E2]▷=> P) -∗ wp tid E2 e (λ v, P ={E1}=∗ Φ v) -∗ wp tid E1 e Φ.
Proof.
  iStartProof (iProp _). rewrite wp_eq /wp_def. iIntros (He ? V) "VS %% WP %% H𝓥 #? /=".
  iApply (wp_step_fupd with "VS"); [by rewrite /= /nopro_lang.to_val /= He|done|].
  iDestruct (wp_larger_view_post with "[-]") as "WP";
    [by iApply ("WP" with "[//] H𝓥 [//]")|].
  iApply wp_mono; [|by iApply "WP"]. iIntros ([v 𝓥']) "(% & [$ H]) H'".
  iApply ("H" with "[H']"). rewrite (_ : V ⊑ 𝓥'.(cur)) //.
  do 2 (etrans; [eassumption|]). by f_equiv.
Qed.

Lemma wp_hist_inv tid E e Φ :
  to_val e = None →
  (⎡ hist_inv ⎤ -∗ wp tid E e Φ) ⊢ wp tid E e Φ.
Proof.
  move => NV. iStartProof (iProp _). iIntros (V) "WP".
  rewrite monPred_at_wand /= wp_eq /wp_def /=. iIntros (?) "Ext own s".
  rewrite wp_unfold /wp_pre /= /nopro_lang.to_val NV /=.
  iIntros (σ1 _ κs _ n) "int". iDestruct "int" as "[oA #Inv]".
  iCombine "oA Inv" as "int".
  iSpecialize ("WP" $! V with "[] Inv Ext own s"); [done..|].
  rewrite !wp_unfold /wp_pre /= /nopro_lang.to_val NV /=.
  by iApply ("WP" $! σ1 0%nat κs κs n with "int").
Qed.
End WeakestPre.

Section WeakestPre_derived.
  Context `{!noprolG Σ}.
  Implicit Types (Φ Ψ : val → vProp Σ) (P : vProp Σ).

  (** * Derived rules *)
  Lemma wp_mono tid E e Φ Ψ :
    (∀ v, Φ v ⊢ Ψ v) → WP e @ tid; E {{ Φ }} ⊢ WP e @ tid; E {{ Ψ }}.
  Proof.
    iIntros (HΦ) "H"; iApply (wp_strong_mono with "H"); auto.
    iIntros (v) "?". by iApply HΦ.
  Qed.
  Lemma wp_mask_mono tid E1 E2 e Φ :
    E1 ⊆ E2 → WP e @ tid; E1 {{ Φ }} ⊢ WP e @ tid; E2 {{ Φ }}.
  Proof. iIntros (?) "H"; iApply (wp_strong_mono with "H"); auto. Qed.
  Global Instance wp_mono' tid E e:
    Proper (pointwise_relation _ (⊢) ==> (⊢)) (wp tid E e).
  Proof. by intros Φ Φ' ?; apply wp_mono. Qed.

  Lemma wp_value tid E Φ e v : IntoVal e v → Φ v ⊢ WP e @ tid; E {{ Φ }}.
  Proof. intros <-; by apply wp_value'. Qed.
  Lemma wp_value_fupd' tid E Φ v : (|={E}=> Φ v) ⊢ WP of_val v @ tid; E {{ Φ }}.
  Proof. intros. by rewrite -wp_fupd -wp_value'. Qed.
  Lemma wp_value_fupd tid E Φ e v `{!IntoVal e v} :
    (|={E}=> Φ v) ⊢ WP e @ tid; E {{ Φ }}.
  Proof. intros. rewrite -wp_fupd -wp_value //. Qed.

  Lemma wp_frame_l tid E e Φ R :
    R ∗ WP e @ tid; E {{ Φ }} ⊢ WP e @ tid; E {{ v, R ∗ Φ v }}.
  Proof. iIntros "[? H]". iApply (wp_strong_mono with "H"); auto with iFrame. Qed.
  Lemma wp_frame_r tid E e Φ R :
    WP e @ tid; E {{ Φ }} ∗ R ⊢ WP e @ tid; E {{ v, Φ v ∗ R }}.
  Proof. iIntros "[H ?]". iApply (wp_strong_mono with "H"); auto with iFrame. Qed.

  Lemma wp_frame_step_l tid E1 E2 e Φ R :
    to_val e = None → E2 ⊆ E1 →
    (|={E1}[E2]▷=> R) ∗ WP e @ tid; E2 {{ Φ }} ⊢ WP e @ tid; E1 {{ v, R ∗ Φ v }}.
  Proof.
    iIntros (??) "[Hu Hwp]". iApply (wp_step_fupd with "Hu"); try done.
    iApply (wp_mono with "Hwp"). by iIntros (?) "$$".
  Qed.
  Lemma wp_frame_step_r tid E1 E2 e Φ R :
    to_val e = None → E2 ⊆ E1 →
    WP e @ tid; E2 {{ Φ }} ∗ (|={E1}[E2]▷=> R) ⊢ WP e @ tid; E1 {{ v, Φ v ∗ R }}.
  Proof.
    rewrite [(WP _ @ _ ; _ {{ _ }} ∗ _)%I]comm; setoid_rewrite (comm _ _ R).
    apply wp_frame_step_l.
  Qed.
  Lemma wp_frame_step_l' tid E e Φ R :
    to_val e = None →
    ▷ R ∗ WP e @ tid; E {{ Φ }} ⊢ WP e @ tid; E {{ v, R ∗ Φ v }}.
  Proof.
    iIntros (?) "[??]". iApply (wp_frame_step_l tid E E); try iFrame; eauto.
  Qed.
  Lemma wp_frame_step_r' tid E e Φ R :
    to_val e = None →
    WP e @ tid; E {{ Φ }} ∗ ▷ R ⊢ WP e @ tid; E {{ v, Φ v ∗ R }}.
  Proof.
    iIntros (?) "[??]". iApply (wp_frame_step_r tid E E); try iFrame; eauto.
  Qed.

  Lemma wp_wand tid E e Φ Ψ :
    WP e @ tid; E {{ Φ }} -∗ (∀ v, Φ v -∗ Ψ v) -∗ WP e @ tid; E {{ Ψ }}.
  Proof.
    iIntros "Hwp H". iApply (wp_strong_mono with "Hwp"); auto.
    iIntros (?) "?". by iApply "H".
  Qed.
  Lemma wp_wand_l tid E e Φ Ψ :
    (∀ v, Φ v -∗ Ψ v) ∗ WP e @ tid; E {{ Φ }} ⊢ WP e @ tid; E {{ Ψ }}.
  Proof. iIntros "[H Hwp]". by iApply (wp_wand with "Hwp H"). Qed.
  Lemma wp_wand_r tid E e Φ Ψ :
    WP e @ tid; E {{ Φ }} ∗ (∀ v, Φ v -∗ Ψ v) ⊢ WP e @ tid; E {{ Ψ }}.
  Proof. iIntros "[Hwp H]". by iApply (wp_wand with "Hwp H"). Qed.
  Lemma wp_frame_wand_l tid E e Q Φ :
    Q ∗ WP e @ tid; E {{ v, Q -∗ Φ v }} -∗ WP e @ tid; E {{ Φ }}.
  Proof.
    iIntros "[HQ HWP]". iApply (wp_wand with "HWP").
    iIntros (v) "HΦ". by iApply "HΦ".
  Qed.

  Global Instance frame_wp p tid E e R Φ Ψ :
    (∀ v, Frame p R (Φ v) (Ψ v)) →
    Frame p R (WP e @ tid; E {{ Φ }}) (WP e @ tid; E {{ Ψ }}).
  Proof. rewrite /Frame=> HR. rewrite wp_frame_l. apply wp_mono, HR. Qed.

  Global Instance is_except_0_wp tid E e Φ :
    IsExcept0 (WP e @ tid; E {{ Φ }}).
  Proof. by rewrite /IsExcept0 -{2}fupd_wp// -except_0_fupd -fupd_intro. Qed.

  Global Instance elim_modal_bupd_wp p tid E e P Φ :
    ElimModal True p false (|==> P) P
              (WP e @ tid; E {{ Φ }}) (WP e @ tid; E {{ Φ }}).
  Proof.
    by rewrite /ElimModal bi.intuitionistically_if_elim
      (bupd_fupd E) fupd_frame_r bi.wand_elim_r fupd_wp.
  Qed.

  Global Instance elim_modal_fupd_wp p tid E e P Φ :
    ElimModal True p false (|={E}=> P) P
              (WP e @ tid; E {{ Φ }}) (WP e @ tid; E {{ Φ }}).
  Proof.
    by rewrite /ElimModal bi.intuitionistically_if_elim
      fupd_frame_r bi.wand_elim_r fupd_wp.
  Qed.

  Global Instance elim_modal_fupd_wp_atomic p tid E1 E2 e P Φ :
    Atomic e →
    ElimModal True p false (|={E1,E2}=> P) P
              (WP e @ tid; E1 {{ Φ }}) (WP e @ tid; E2 {{ v, |={E2,E1}=> Φ v }})%I.
  Proof.
    intros. by rewrite /ElimModal bi.intuitionistically_if_elim
      fupd_frame_r bi.wand_elim_r wp_atomic.
  Qed.

  Global Instance add_modal_fupd_wp tid E e P Φ :
    AddModal (|={E}=> P) P (WP e @ tid; E {{ Φ }}).
  Proof. intros. by rewrite /AddModal fupd_frame_r bi.wand_elim_r fupd_wp. Qed.
End WeakestPre_derived.
