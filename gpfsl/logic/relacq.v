From iris.algebra Require Import auth.
From iris.bi Require Import monpred.
From iris.base_logic.lib Require Import wsat.
From iris.proofmode Require Import proofmode monpred modality_instances.

From gpfsl.base_logic Require Import vprop history.
From gpfsl.base_logic Require Import frame_instances.

Require Import iris.prelude.options.

Implicit Types tid : thread_id.

Local Existing Instances
  histGpreS_tview hist_inG
  .

Section RelAcq.
  Context `{histGS Σ}.
  Local Notation vProp := (vProp Σ).
  Implicit Types (P Q : vProp).

  Definition acq_mod_def tid P : vProp :=
    ∃ 𝓥, ⎡ own tid (◯ to_latT 𝓥) ⎤ ∗ @{𝓥.(acq)} P.
  Definition acq_mod_aux : seal (@acq_mod_def). Proof. by eexists. Qed.
  Definition acq_mod := unseal (@acq_mod_aux).
  Definition acq_mod_eq : @acq_mod = _ := seal_eq _.

  Definition rel_mod_def tid P : vProp :=
    ∃ 𝓥, ⎡ own tid (◯ to_latT 𝓥) ⎤ ∗ @{𝓥.(frel)} P.
  Definition rel_mod_aux : seal (@rel_mod_def). Proof. by eexists. Qed.
  Definition rel_mod := unseal (@rel_mod_aux).
  Definition rel_mod_eq : @rel_mod = _ := seal_eq _.
End RelAcq.

Global Instance: Params (@rel_mod) 3 := {}.
Global Instance: Params (@acq_mod) 3 := {}.

Notation "△{ tid } P" := (rel_mod tid P%I)
  (at level 20, right associativity, format "△{ tid }  P"): bi_scope.

Notation "▽{ tid } P" := (acq_mod tid P%I)
  (at level 20, right associativity, format "▽{ tid }  P"): bi_scope.

Local Ltac unseal :=
  rewrite ?acq_mod_eq ?rel_mod_eq /acq_mod_def /rel_mod_def.

Section RelAcqProp.
  Context `{histGS Σ}.
  Local Notation vProp := (vProp Σ).
  Local Notation iProp := (iProp Σ).
  Implicit Types (P Q: vProp).

  Lemma rel_objectively_intro P tid :
    <obj> P ==∗ △{tid} P.
  Proof.
    unseal. iIntros "obj".
    iExists ∅. rewrite -view_at_objectively. iFrame "obj".
    rewrite (_: (◯ to_latT (∅: threadView) : authR _) = ε) //.
    rewrite -embed_bupd. by iApply own_unit.
  Qed.

  Lemma rel_True_intro tid : ⊢|==> △{tid} True.
  Proof. iApply rel_objectively_intro. by iIntros "!>". Qed.

  Lemma rel_sep_objectively P Q tid :
    △{tid} P ∗ <obj> Q ⊢ △{tid} (P ∗ Q).
  Proof.
    unseal. iIntros "[rel obj]".
    iDestruct "rel" as (𝓥) "[own P]".
    iExists 𝓥. iFrame "own P". by rewrite -view_at_objectively.
  Qed.

  Lemma rel_mono_objectively P Q tid :
    △{tid} P ∗ <obj> (P -∗ Q) ⊢ △{tid} Q.
  Proof.
    unseal. iIntros "[rel obj]".
    iDestruct "rel" as (𝓥) "[own P]".
    iExists 𝓥. iFrame "own". by iApply (view_at_objectively with "obj").
  Qed.

  Lemma rel_mono P Q tid :
    (P ⊢ Q) → △{tid} P ⊢ △{tid} Q.
  Proof.
    iIntros (PQ). unseal. iDestruct 1 as (𝓥) "[own P]".
    iExists 𝓥. iFrame "own". by rewrite PQ.
  Qed.

  Lemma rel_pure_elim φ tid :
    (△{tid} ⌜ φ ⌝) ⊢ ⌜ φ ⌝.
  Proof.
    unseal. iDestruct (1) as (?) "[_ ?]". by rewrite view_at_pure.
  Qed.

  Lemma rel_and_elim P Q tid :
    △{tid} (P ∧ Q) ⊢ △{tid} P ∧ △{tid} Q.
  Proof.
    unseal. iDestruct 1 as (𝓥) "[#own PQ]".
    iSplit; iExists 𝓥; iFrame "#"; by [rewrite bi.and_elim_l|rewrite bi.and_elim_r].
  Qed.

  Lemma rel_or_elim P Q tid :
    △{tid} (P ∨ Q) ⊢ △{tid} P ∨ △{tid} Q.
  Proof.
    unseal. iDestruct 1 as (𝓥) "[#own [P|Q]]";
      [iLeft|iRight]; iExists 𝓥; by iFrame "#".
  Qed.

  Lemma rel_or_intro P Q tid :
    △{tid} P ∨ △{tid} Q ⊢ △{tid} (P ∨ Q).
  Proof.
    unseal. iIntros "[P|Q]".
    - iDestruct "P" as (𝓥) "[own P]". iExists _. by iFrame.
    - iDestruct "Q" as (𝓥) "[own Q]". iExists _. by iFrame.
  Qed.

  Lemma rel_or P Q tid :
    △{tid} P ∨ △{tid} Q ⊣⊢ △{tid} (P ∨ Q).
  Proof. iSplit; [by iApply rel_or_intro|by iApply rel_or_elim]. Qed.

  Lemma rel_exist {A: Type} (Ψ: A → vProp) tid :
    (△{tid} ∃ x, Ψ x) ⊣⊢ ∃ x, △{tid} Ψ x.
  Proof.
    unseal. setoid_rewrite view_at_exist. setoid_rewrite bi.sep_exist_l.
    by rewrite bi.exist_exist.
  Qed.

  Lemma rel_forall_elim {A: Type} (Ψ: A → vProp) tid :
    (△{tid} ∀ x, Ψ x) ⊢ ∀ x, △{tid} Ψ x.
  Proof.
    unseal. setoid_rewrite view_at_forall. setoid_rewrite bi.sep_forall_l.
    by rewrite bi.exist_forall.
  Qed.

  Lemma rel_sep_elim P Q tid :
    △{tid} (P ∗ Q) ⊢ △{tid} P ∗ △{tid} Q.
  Proof.
    unseal. iDestruct 1 as (𝓥) "[#own [P Q]]". iSplitL "P"; iExists 𝓥; by iFrame "#".
  Qed.

  Lemma rel_sep_intro P Q tid :
     △{tid} P ∗ △{tid} Q ⊢ △{tid} (P ∗ Q).
  Proof.
    unseal. iIntros "[P Q]".
    iDestruct "P" as (𝓥1) "[#own1 P]". iDestruct "Q" as (𝓥2) "[#own2 Q]".
    iExists (𝓥1 ⊔ 𝓥2). iFrame "P Q".
    rewrite -lat_op_join' auth_frag_op own_op. by iFrame "own1 own2".
  Qed.

  Lemma rel_sep P Q tid :
    △{tid} P ∗ △{tid} Q ⊣⊢ △{tid} (P ∗ Q).
  Proof. iSplit; [by iApply rel_sep_intro|by iApply rel_sep_elim]. Qed.

  Lemma rel_wand_1 P Q tid :
    △{tid} (P -∗ Q) ⊢ (△{tid} P -∗ △{tid} Q).
  Proof.
    unseal. iDestruct 1 as (𝓥1) "[own1 PQ]". iDestruct 1 as (𝓥2) "[own2 P]".
    iExists (join 𝓥1 𝓥2). iSplitL "own1 own2".
    - rewrite -lat_op_join' auth_frag_op own_op. by iFrame.
    - iApply (view_at_mono_2 with "PQ [P]"); [solve_lat|]. by iFrame "P".
  Qed.

  Lemma rel_later_intro `{fancy_updates.invGS Σ} P tid E :
    ▷ (△{tid} P) ={E}=∗ △{tid} ▷ P.
  Proof.
    unseal. iDestruct 1 as (?) "[>own P]". iIntros "!>". iExists _.
    rewrite view_at_later. iFrame.
  Qed.

  Lemma rel_later_elim P tid :
    (△{tid} ▷ P) ⊢ ▷ △{tid} P.
  Proof.
    unseal. iDestruct 1 as (?) "[own P]". rewrite view_at_later. iExists _. by iFrame.
  Qed.
  Lemma rel_laterN_elim P tid n :
    (△{tid} ▷^n P) ⊢ ▷^n △{tid} P.
  Proof.
    unseal. iDestruct 1 as (?) "[own P]". rewrite view_at_laterN. iExists _. by iFrame.
  Qed.
  Lemma rel_except_0 P tid : △{tid} ◇ P ⊢ ◇ △{tid} P.
  Proof.
    unseal. rewrite bi.except_0_exist.
    setoid_rewrite bi.except_0_sep. setoid_rewrite view_at_except_0.
    by setoid_rewrite <-(bi.except_0_intro (⎡ own _ _ ⎤)).
  Qed.

  Lemma rel_bupd P tid : (△{tid} |==> P) ⊢ |==> △{tid} P.
  Proof.
    unseal. rewrite -bupd_exist. setoid_rewrite <-bupd_sep.
    setoid_rewrite view_at_bupd.
    by setoid_rewrite <-(bupd_intro (⎡ own _ _ ⎤)).
  Qed.
  Lemma rel_fupd `{fancy_updates.invGS Σ} (E1 E2 : coPset) P tid :
    △{tid} (|={E1,E2}=> P) ⊢ |={E1,E2}=> △{tid} P.
  Proof. unseal. iDestruct 1 as (𝓥) "[own >P]". eauto. Qed.

  Lemma rel_objectively_elim P tid :
    (△{tid} <obj> P) ⊢ <obj> P.
  Proof.
    unseal. iDestruct 1 as (?) "[_ P]". by rewrite view_at_objective_iff.
  Qed.

  Lemma rel_embed_elim (P: iProp) tid :
    (△{tid} ⎡ P ⎤) ⊢ ⎡ P ⎤.
  Proof.
    unseal. iDestruct (1) as (?) "[_ ?]". by rewrite view_at_embed.
  Qed.

  Lemma rel_subjective P tid :
    △{tid} P ⊢ <subj> P.
  Proof.
    unseal. iDestruct 1 as (𝓥) "[_ P]". by rewrite view_at_subjectively.
  Qed.

  Lemma rel_affinely P tid :
    <affine> △{tid} P ⊢ △{tid} <affine> P.
  Proof.
    unseal. rewrite bi.affinely_exist. setoid_rewrite bi.affinely_sep.
    setoid_rewrite view_at_affinely.
    by setoid_rewrite (bi.affinely_elim ⎡ own _ _ ⎤).
  Qed.
  Lemma rel_affinely_if P tid b :
    <affine>?b △{tid} P ⊢ △{tid} <affine>?b P.
  Proof. destruct b; [apply rel_affinely|done]. Qed.

  Lemma rel_persistently P tid :
    △{tid} <pers> P ⊢ <pers> △{tid} P.
  Proof.
    unseal. rewrite bi.persistently_exist. setoid_rewrite bi.persistently_sep.
    setoid_rewrite view_at_persistently.
    by setoid_rewrite <-(bi.persistent_persistently_2 ⎡ own _ _ ⎤).
  Qed.
  Lemma rel_persistently_if P tid b :
    △{tid} <pers>?b P ⊢ <pers>?b △{tid} P.
  Proof. destruct b; [apply rel_persistently|done]. Qed.

  Lemma rel_intuitionistically P tid :
    □ △{tid} P ⊢ △{tid} □ P.
  Proof.
    unseal. rewrite bi.intuitionistically_exist.
    setoid_rewrite bi.intuitionistically_sep.
    setoid_rewrite view_at_intuitionistically.
    by setoid_rewrite (bi.intuitionistically_elim ⎡ own _ _ ⎤).
  Qed.
  Lemma rel_intuitionistically_if P tid b :
    □?b △{tid} P ⊢ △{tid} □?b P.
  Proof. destruct b; [apply rel_intuitionistically|done]. Qed.

  Lemma rel_at_unfold P tid 𝓥 V :
    (△{tid} P) V -∗ own tid (● to_latT 𝓥)
    -∗ P 𝓥.(frel) ∗ own tid (● to_latT 𝓥).
  Proof.
    iIntros "P oL". unseal. iDestruct "P" as (𝓥') "[own P]".
    iDestruct (own_lat_auth_max with "oL own") as %SUB%tview_sqsubseteq_frel.
    rewrite view_at_unfold_2.
    by iFrame.
  Qed.

  Lemma rel_at_intro P tid V :
    △{tid} (⊒V) -∗ @{V} P -∗ △{tid} P.
  Proof.
    unseal. iDestruct 1 as (𝓥) "[oV %LE]". iIntros "P".
    iExists _. iFrame "oV". iFrame "P".
  Qed.

  (** Acquire modality *)
  Lemma acq_mono_objectively P Q tid :
    ▽{tid} P ∗ <obj> (P -∗ Q) ⊢ ▽{tid} Q.
  Proof.
    unseal. iIntros "[rel obj]".
    iDestruct "rel" as (𝓥) "[own P]".
    iExists 𝓥. iFrame "own". by iApply (view_at_objectively with "obj").
  Qed.

  Lemma acq_mono P Q tid :
    (P ⊢ Q) → ▽{tid} P ⊢ ▽{tid} Q.
  Proof.
    iIntros (PQ). unseal. iDestruct 1 as (𝓥) "[own P]".
    iExists 𝓥. iFrame "own". by rewrite PQ.
  Qed.

  Lemma acq_pure_elim φ tid :
    (▽{tid} ⌜ φ ⌝) ⊢ ⌜ φ ⌝.
  Proof.
    unseal. iDestruct (1) as (?) "[_ ?]". by rewrite view_at_pure.
  Qed.

  Lemma acq_and_elim P Q tid :
    ▽{tid} (P ∧ Q) ⊢ ▽{tid} P ∧ ▽{tid} Q.
  Proof.
    unseal. iDestruct 1 as (𝓥) "[#own PQ]".
    iSplit; iExists 𝓥; iFrame "#"; by [rewrite bi.and_elim_l|rewrite bi.and_elim_r].
  Qed.

  Lemma acq_or_elim P Q tid :
    ▽{tid} (P ∨ Q) ⊢ ▽{tid} P ∨ ▽{tid} Q.
  Proof.
    unseal. iDestruct 1 as (𝓥) "[#own [P|Q]]";
      [iLeft|iRight]; iExists 𝓥; by iFrame "#".
  Qed.

  Lemma acq_or_intro P Q tid :
    ▽{tid} P ∨ ▽{tid} Q ⊢ ▽{tid} (P ∨ Q).
  Proof.
    unseal. iIntros "[P|Q]".
    - iDestruct "P" as (𝓥) "[own P]". iExists _. by iFrame.
    - iDestruct "Q" as (𝓥) "[own Q]". iExists _. by iFrame.
  Qed.

  Lemma acq_or P Q tid :
    ▽{tid} P ∨ ▽{tid} Q ⊣⊢ ▽{tid} (P ∨ Q).
  Proof. iSplit; [by iApply acq_or_intro|by iApply acq_or_elim]. Qed.

  Lemma acq_exist {A: Type} (Ψ: A → vProp) tid :
    (▽{tid} ∃ x, Ψ x) ⊣⊢ ∃ x, ▽{tid} Ψ x.
  Proof.
    unseal. setoid_rewrite view_at_exist. setoid_rewrite bi.sep_exist_l.
    by rewrite bi.exist_exist.
  Qed.

  Lemma acq_forall_elim {A: Type} (Ψ: A → vProp) tid :
    (▽{tid} ∀ x, Ψ x) ⊢ ∀ x, ▽{tid} Ψ x.
  Proof.
    unseal. setoid_rewrite view_at_forall. setoid_rewrite bi.sep_forall_l.
    by rewrite bi.exist_forall.
  Qed.

  Lemma acq_sep_elim P Q tid :
    ▽{tid} (P ∗ Q) ⊢ ▽{tid} P ∗ ▽{tid} Q.
  Proof.
    unseal. iDestruct 1 as (𝓥) "[#own [P Q]]". iSplitL "P"; iExists 𝓥; by iFrame "#".
  Qed.

  Lemma acq_sep_intro P Q tid :
     ▽{tid} P ∗ ▽{tid} Q ⊢ ▽{tid} (P ∗ Q).
  Proof.
    unseal. iIntros "[P Q]".
    iDestruct "P" as (𝓥1) "[#own1 P]". iDestruct "Q" as (𝓥2) "[#own2 Q]".
    iExists (𝓥1 ⊔ 𝓥2). iFrame "P Q".
    rewrite -lat_op_join' auth_frag_op own_op. by iFrame "own1 own2".
  Qed.

  Lemma acq_sep P Q tid :
    ▽{tid} P ∗ ▽{tid} Q ⊣⊢ ▽{tid} (P ∗ Q).
  Proof. iSplit; [by iApply acq_sep_intro|by iApply acq_sep_elim]. Qed.

  Lemma acq_wand_1 P Q tid :
    ▽{tid} (P -∗ Q) ⊢ (▽{tid} P -∗ ▽{tid} Q).
  Proof.
    unseal. iDestruct 1 as (𝓥1) "[own1 PQ]". iDestruct 1 as (𝓥2) "[own2 P]".
    iExists (join 𝓥1 𝓥2). iSplitL "own1 own2".
    - rewrite -lat_op_join' auth_frag_op own_op. by iFrame.
    - iApply (view_at_mono_2 with "PQ [P]"); [solve_lat|]. by iFrame.
  Qed.

  Lemma acq_later_elim P tid :
    (▽{tid} ▷ P) ⊢ ▷ ▽{tid} P.
  Proof.
    unseal. iDestruct 1 as (?) "[own P]". rewrite view_at_later. iExists _. by iFrame.
  Qed.
  Lemma acq_laterN_elim P tid n :
    (▽{tid} ▷^n P) ⊢ ▷^n ▽{tid} P.
  Proof.
    unseal. iDestruct 1 as (?) "[own P]". rewrite view_at_laterN. iExists _. by iFrame.
  Qed.
  Lemma acq_except_0 P tid : ▽{tid} ◇ P ⊢ ◇ ▽{tid} P.
  Proof.
    unseal. rewrite bi.except_0_exist.
    setoid_rewrite bi.except_0_sep. setoid_rewrite view_at_except_0.
    by setoid_rewrite <-(bi.except_0_intro (⎡ own _ _ ⎤)).
  Qed.

  Lemma acq_bupd P tid : (▽{tid} |==> P) ⊢ |==> ▽{tid} P.
  Proof.
    unseal. rewrite -bupd_exist. setoid_rewrite <-bupd_sep.
    setoid_rewrite view_at_bupd.
    by setoid_rewrite <-(bupd_intro (⎡ own _ _ ⎤)).
  Qed.
  Lemma acq_fupd `{fancy_updates.invGS Σ} (E1 E2 : coPset) P tid :
    ▽{tid} (|={E1,E2}=> P) ⊢ |={E1,E2}=> ▽{tid} P.
  Proof. unseal. iDestruct 1 as (𝓥) "[own >P]". eauto. Qed.

  Lemma acq_objectively_elim P tid :
    (▽{tid} <obj> P) ⊢ <obj> P.
  Proof.
    unseal. iDestruct 1 as (?) "[_ P]". by rewrite view_at_objective_iff.
  Qed.

  Lemma acq_embed_elim (P: iProp) tid :
    (▽{tid} ⎡ P ⎤) ⊢ ⎡ P ⎤.
  Proof.
    unseal. iDestruct (1) as (?) "[_ ?]". by rewrite view_at_embed.
  Qed.

  Lemma acq_subjective P tid :
    ▽{tid} P ⊢ <subj> P.
  Proof.
    unseal. iDestruct 1 as (𝓥) "[_ P]". by rewrite view_at_subjectively.
  Qed.

  Lemma acq_affinely P tid :
    <affine> ▽{tid} P ⊢ ▽{tid} <affine> P.
  Proof.
    unseal. rewrite bi.affinely_exist. setoid_rewrite bi.affinely_sep.
    setoid_rewrite view_at_affinely.
    by setoid_rewrite (bi.affinely_elim ⎡ own _ _ ⎤).
  Qed.
  Lemma acq_affinely_if P tid b :
    <affine>?b ▽{tid} P ⊢ ▽{tid} <affine>?b P.
  Proof. destruct b; [apply acq_affinely|done]. Qed.

  Lemma acq_persistently P tid :
    ▽{tid} <pers> P ⊢ <pers> ▽{tid} P.
  Proof.
    unseal. rewrite bi.persistently_exist. setoid_rewrite bi.persistently_sep.
    setoid_rewrite view_at_persistently.
    by setoid_rewrite <-(bi.persistent_persistently_2 ⎡ own _ _ ⎤).
  Qed.
  Lemma acq_persistently_if P tid b :
    ▽{tid} <pers>?b P ⊢ <pers>?b ▽{tid} P.
  Proof. destruct b; [apply acq_persistently|done]. Qed.

  Lemma acq_intuitionistically P tid :
    □ ▽{tid} P ⊢ ▽{tid} □ P.
  Proof.
    unseal. rewrite bi.intuitionistically_exist.
    setoid_rewrite bi.intuitionistically_sep.
    setoid_rewrite view_at_intuitionistically.
    by setoid_rewrite (bi.intuitionistically_elim ⎡ own _ _ ⎤).
  Qed.
  Lemma acq_intuitionistically_if P tid b :
    □?b ▽{tid} P ⊢ ▽{tid} □?b P.
  Proof. destruct b; [apply acq_intuitionistically|done]. Qed.

  Lemma acq_at_unfold P tid 𝓥 V :
    (▽{tid} P) V -∗ own tid (● to_latT 𝓥)
      -∗ P 𝓥.(acq) ∗ own tid (● to_latT 𝓥).
  Proof.
    iIntros "P oL". unseal. iDestruct "P" as (𝓥') "[own P]".
    iDestruct (own_lat_auth_max with "oL own") as %SUB%tview_sqsubseteq_acq.
    rewrite view_at_unfold_2.
    by iFrame.
  Qed.

  Lemma acq_at_intro P tid V :
    ▽{tid} (⊒V) -∗ @{V} P -∗ ▽{tid} P.
  Proof.
    unseal. iDestruct 1 as (𝓥) "[oV %LE]". iIntros "P".
    iExists _. iFrame "oV". iFrame "P".
  Qed.

  (* TODO: more Proper instances *)
  Global Instance rel_mod_ne tid : NonExpansive (rel_mod tid).
  Proof. unseal. solve_proper. Qed.
  Global Instance rel_mod_proper tid : Proper ((≡) ==> (≡)) (rel_mod tid).
  Proof. apply (ne_proper _). Qed.
  Global Instance rel_mod_mono tid : Proper ((⊢) ==> (⊢)) (rel_mod tid).
  Proof. intros ??. apply rel_mono. Qed.
  Global Instance rel_mod_flip_mono tid : Proper (flip (⊢) ==> flip (⊢)) (rel_mod tid).
  Proof. intros ??. apply rel_mono. Qed.

  Global Instance acq_mod_ne tid : NonExpansive (acq_mod tid).
  Proof. unseal. solve_proper. Qed.
  Global Instance acq_mod_proper tid : Proper ((≡) ==> (≡)) (acq_mod tid).
  Proof. apply (ne_proper _). Qed.
  Global Instance acq_mod_mono tid : Proper ((⊢) ==> (⊢)) (acq_mod tid).
  Proof. intros ??. apply acq_mono. Qed.
  Global Instance acq_mod_flip_mono tid : Proper (flip (⊢) ==> flip (⊢)) (acq_mod tid).
  Proof. intros ??. apply acq_mono. Qed.

  Global Instance rel_persistent P tid :
    Persistent P → Persistent (△{tid} P).
  Proof. unseal. apply _. Qed.
  Global Instance rel_timeless P tid :
    Timeless P → Timeless (△{tid} P).
  Proof. unseal. apply _. Qed.

  Global Instance acq_persistent P tid :
    Persistent P → Persistent (▽{tid} P).
  Proof. unseal. apply _. Qed.
  Global Instance acq_timeless P tid :
    Timeless P → Timeless (▽{tid} P).
  Proof. unseal. apply _. Qed.

End RelAcqProp.

Section proofmode.
  Context `{histGS Σ}.
  Local Notation vProp := (vProp Σ).
  Local Notation iProp := (iProp Σ).
  Implicit Types (P Q: vProp).

  (** Release modality *)
  Global Instance into_pure_rel_mod (φ : Prop) P tid :
    IntoPure P φ → IntoPure (△{tid} P) φ.
  Proof. rewrite /IntoPure=> ->. by rewrite rel_pure_elim. Qed.
  (* No FromPure instance because that direction needs a [bupd]. *)

  Global Instance into_wand_rel_mod p q R P Q tid :
    IntoWand p q R P Q → IntoWand p q (△{tid} R) (△{tid} P) (△{tid} Q).
  Proof.
    rewrite /IntoWand !rel_intuitionistically_if => ->. by rewrite rel_wand_1.
  Qed.

  Global Instance into_sep_rel_mod P Q1 Q2 tid :
    IntoSep P Q1 Q2 → IntoSep (△{tid} P) (△{tid} Q1) (△{tid} Q2).
  Proof. by rewrite /IntoSep rel_sep => ->. Qed.
  Global Instance from_sep_rel_mod P Q1 Q2 tid :
    FromSep P Q1 Q2 → FromSep (△{tid} P) (△{tid} Q1) (△{tid} Q2).
  Proof. by rewrite /FromSep rel_sep => ->. Qed.
  Global Instance maybe_combine_sep_as_rel_mod P Q1 Q2 tid progress :
    MaybeCombineSepAs P Q1 Q2 progress →
    MaybeCombineSepAs (△{tid} P) (△{tid} Q1) (△{tid} Q2) progress.
  Proof. by rewrite /MaybeCombineSepAs rel_sep => ->. Qed.

  Global Instance into_or_rel_mod P Q1 Q2 tid :
    IntoOr P Q1 Q2 → IntoOr (△{tid} P) (△{tid} Q1) (△{tid} Q2).
  Proof. by rewrite /IntoOr rel_or => ->. Qed.
  Global Instance from_or_rel_mod P Q1 Q2 tid :
    FromOr P Q1 Q2 → FromOr (△{tid} P) (△{tid} Q1) (△{tid} Q2).
  Proof. by rewrite /FromOr rel_or => ->. Qed.

  Global Instance into_exist_rel_mod {A} P tid (Φ : A → vProp) name :
    IntoExist P Φ name → IntoExist (△{tid} P) (λ a, (△{tid} Φ a)%I) name.
  Proof. by rewrite /IntoExist -rel_exist => ->. Qed.
  Global Instance from_exist_rel_mod {A} P tid (Φ : A → vProp) :
    FromExist P Φ → FromExist (△{tid} P) (λ a, (△{tid} Φ a)%I).
  Proof. by rewrite /FromExist -rel_exist => ->. Qed.

  Global Instance into_forall_rel_mod {A} P tid (Φ : A → vProp) :
    IntoForall P Φ → IntoForall (△{tid} P) (λ a, (△{tid} Φ a)%I).
  Proof. by rewrite /IntoForall -rel_forall_elim => ->. Qed.
  (* No FromForall instance. *)

  Global Instance into_later_rel_mod n P Q tid :
    IntoLaterN false n P Q → IntoLaterN false n (△{tid} P) (△{tid} Q).
  Proof. rewrite /IntoLaterN /MaybeIntoLaterN => ->. by rewrite rel_laterN_elim. Qed.

  Global Instance from_modal_id_rel_mod φ `(sel : A) P Q tid :
    FromModal φ modality_id sel P Q →
    FromModal φ modality_id sel (△{tid} P) (△{tid} Q) | 100.
  Proof. rewrite /FromModal /= =>HPQ ?. rewrite HPQ //. Qed.

  Global Instance from_modal_affinely_rel_mod φ `(sel : A) P Q tid :
    FromModal φ modality_affinely sel P Q →
    FromModal φ modality_affinely sel (△{tid} P) (△{tid} Q) | 100.
  Proof. rewrite /FromModal /= =>HPQ ?. by rewrite -HPQ // rel_affinely. Qed.
  Global Instance from_modal_intuitionistically_rel_mod φ `(sel : A) P Q tid :
    FromModal φ modality_intuitionistically sel P Q →
    FromModal φ modality_intuitionistically sel (△{tid} P) (△{tid} Q) | 100.
  Proof. rewrite /FromModal /= =>HPQ ?. by rewrite -HPQ // rel_intuitionistically. Qed.

  Global Instance elim_modal_rel_mod_bupd_hyp p p' φ P P' Q Q' tid :
    ElimModal φ p p' (|==> △{tid} P)%I P' Q Q' →
    ElimModal φ p p' (△{tid} |==> P) P' Q Q'.
  Proof. by rewrite /ElimModal !rel_bupd. Qed.

  Global Instance elim_modal_rel_mod_fupd_hyp `{fancy_updates.invGS Σ}
      p p' φ E1 E2 P P' Q Q' tid :
    ElimModal φ p p' (|={E1,E2}=> △{tid} P)%I P' Q Q' →
    ElimModal φ p p' (△{tid} |={E1,E2}=> P) P' Q Q'.
  Proof. by rewrite /ElimModal rel_fupd. Qed.

  (** Acquire modality *)
  Global Instance into_pure_acq_mod (φ : Prop) P tid :
    IntoPure P φ → IntoPure (▽{tid} P) φ.
  Proof. rewrite /IntoPure=> ->. by rewrite acq_pure_elim. Qed.
  (* No FromPure instance because that direction needs a [bupd]. *)

  Global Instance into_wand_acq_mod p q R P Q tid :
    IntoWand p q R P Q → IntoWand p q (▽{tid} R) (▽{tid} P) (▽{tid} Q).
  Proof.
    rewrite /IntoWand !acq_intuitionistically_if => ->. by rewrite acq_wand_1.
  Qed.

  Global Instance into_sep_acq_mod P Q1 Q2 tid :
    IntoSep P Q1 Q2 → IntoSep (▽{tid} P) (▽{tid} Q1) (▽{tid} Q2).
  Proof. by rewrite /IntoSep acq_sep => ->. Qed.
  Global Instance from_sep_acq_mod P Q1 Q2 tid :
    FromSep P Q1 Q2 → FromSep (▽{tid} P) (▽{tid} Q1) (▽{tid} Q2).
  Proof. by rewrite /FromSep acq_sep => ->. Qed.
  Global Instance maybe_combine_sep_as_acq_mod P Q1 Q2 tid progress :
    MaybeCombineSepAs P Q1 Q2 progress →
    MaybeCombineSepAs (▽{tid} P) (▽{tid} Q1) (▽{tid} Q2) progress.
  Proof. by rewrite /MaybeCombineSepAs acq_sep => ->. Qed.

  Global Instance into_or_acq_mod P Q1 Q2 tid :
    IntoOr P Q1 Q2 → IntoOr (▽{tid} P) (▽{tid} Q1) (▽{tid} Q2).
  Proof. by rewrite /IntoOr acq_or => ->. Qed.
  Global Instance from_or_acq_mod P Q1 Q2 tid :
    FromOr P Q1 Q2 → FromOr (▽{tid} P) (▽{tid} Q1) (▽{tid} Q2).
  Proof. by rewrite /FromOr acq_or => ->. Qed.

  Global Instance into_exist_acq_mod {A} P tid (Φ : A → vProp) name :
    IntoExist P Φ name → IntoExist (▽{tid} P) (λ a, (▽{tid} Φ a)%I) name.
  Proof. by rewrite /IntoExist -acq_exist => ->. Qed.
  Global Instance from_exist_acq_mod {A} P tid (Φ : A → vProp) :
    FromExist P Φ → FromExist (▽{tid} P) (λ a, (▽{tid} Φ a)%I).
  Proof. by rewrite /FromExist -acq_exist => ->. Qed.

  Global Instance into_forall_acq_mod {A} P tid (Φ : A → vProp) :
    IntoForall P Φ → IntoForall (▽{tid} P) (λ a, (▽{tid} Φ a)%I).
  Proof. by rewrite /IntoForall -acq_forall_elim => ->. Qed.
  (* No FromForall instance. *)

  Global Instance into_later_acq_mod n P Q tid :
    IntoLaterN false n P Q → IntoLaterN false n (▽{tid} P) (▽{tid} Q).
  Proof. rewrite /IntoLaterN /MaybeIntoLaterN => ->. by rewrite acq_laterN_elim. Qed.

  Global Instance from_modal_id_acq_mod φ `(sel : A) P Q tid :
    FromModal φ modality_id sel P Q →
    FromModal φ modality_id sel (▽{tid} P) (▽{tid} Q) | 100.
  Proof. rewrite /FromModal /= =>HPQ ?. rewrite HPQ //. Qed.

  Global Instance from_modal_affinely_acq_mod φ `(sel : A) P Q tid :
    FromModal φ modality_affinely sel P Q →
    FromModal φ modality_affinely sel (▽{tid} P) (▽{tid} Q) | 100.
  Proof. rewrite /FromModal /= =>HPQ ?. by rewrite -HPQ // acq_affinely. Qed.
  Global Instance from_modal_intuitionistically_acq_mod φ `(sel : A) P Q tid :
    FromModal φ modality_intuitionistically sel P Q →
    FromModal φ modality_intuitionistically sel (▽{tid} P) (▽{tid} Q) | 100.
  Proof. rewrite /FromModal /= =>HPQ ?. by rewrite -HPQ // acq_intuitionistically. Qed.

  Global Instance elim_modal_acq_mod_bupd_hyp p p' φ P P' Q Q' tid :
    ElimModal φ p p' (|==> ▽{tid} P)%I P' Q Q' →
    ElimModal φ p p' (▽{tid} |==> P) P' Q Q'.
  Proof. by rewrite /ElimModal !acq_bupd. Qed.

  Global Instance elim_modal_acq_mod_fupd_hyp `{fancy_updates.invGS Σ}
      p p' φ E1 E2 P P' Q Q' tid :
    ElimModal φ p p' (|={E1,E2}=> ▽{tid} P)%I P' Q Q' →
    ElimModal φ p p' (▽{tid} |={E1,E2}=> P) P' Q Q'.
  Proof. by rewrite /ElimModal acq_fupd. Qed.
End proofmode.
