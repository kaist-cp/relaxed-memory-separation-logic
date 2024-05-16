From iris.bi Require Import bi monpred.
From iris.proofmode Require Import proofmode monpred.

Require Import iris.prelude.options.

Notation "'⊒' V" := (monPred_in V) (at level 30, format "⊒ V") : bi_scope.

Local Definition monPred_unseal_eqs :=
  (@monPred_at_embed, @monPred_at_pure, @monPred_at_emp,
   @monPred_at_and, @monPred_at_or, @monPred_at_impl,
   @monPred_at_sep,
   @monPred_at_exist, @monPred_at_forall, @monPred_at_wand,
   @monPred_at_persistently, @monPred_at_affinely,
   @monPred_at_intuitionistically, @monPred_at_absorbingly,
   @monPred_at_fupd, @monPred_at_bupd, @monPred_at_later, @monPred_at_laterN,
   @monPred_at_except_0).

Local Ltac unseal_monpred := rewrite !monPred_unseal_eqs /=.

Section ExtraMonpred.
Context `{I : biIndex, PROP : bi}.
#[local] Notation monPred := (monPred I PROP).
Implicit Types (P Q : monPred) (i : I).

(* TODO: move to Iris *)
Global Instance big_sepL2_objective {A B} (Φ : nat → A → B → monPred)
  (l1 : list A) (l2 : list B)
  `{H : ∀ n x y, Objective (Φ n x y)} :
  @Objective I PROP ([∗ list] n↦x;y ∈ l1;l2, Φ n x y).
Proof.
  intros i j. rewrite big_sepL2_alt 2!monPred_at_and 2!monPred_at_pure.
  apply bi.and_mono_r. rewrite 2!monPred_at_big_sepL.
  apply big_sepL_mono => ???. apply H.
Qed.

(* monPred_in *)
Lemma monPred_in_bot `{BiIndexBottom _ bot} : ⊢ ⊒bot : monPred.
Proof. constructor. eauto. Qed.

#[global] Instance objective_monPred_in_bot `{BiIndexBottom _ bot} :
  Objective (⊒bot : monPred)%I.
Proof. intros ??. eauto. Qed.

Lemma monPred_in_intro_incl `{BiAffine PROP} P i' :
  P -∗ ⊒i' -∗ ∃ i, ⊒i ∧ ⌜i' ⊑ i⌝ ∧ ⎡ P i ⎤.
Proof.
  apply bi.wand_intro_r. iIntros "P".
  iDestruct (monPred_in_intro with "P") as (i) "(V & P & %)". eauto.
Qed.

Lemma monPred_in_elim' `{BiAffine PROP} P i :
  ⊒i -∗ ⎡ P i ⎤ -∗ P.
Proof. iIntros "In At". iApply (monPred_in_elim with "In At"). Qed.

Lemma monPred_in_and P Q V : (⊒V → P ∧ Q) ⊣⊢ ((⊒V → P) ∧ (⊒V → Q)).
Proof.
  constructor => i. unseal_monpred.
  iSplit; iIntros "PQ"; first iSplit; iIntros (j Lej Lej'); last iSplit.
  - iSpecialize ("PQ" $! j Lej Lej'). by rewrite bi.and_elim_l.
  - iSpecialize ("PQ" $! j Lej Lej'). by rewrite bi.and_elim_r.
  - rewrite bi.and_elim_l. by iApply ("PQ" $! j Lej Lej').
  - rewrite bi.and_elim_r. by iApply ("PQ" $! j Lej Lej').
Qed.

Lemma monPred_in_forall {A} (Ψ: A → monPred) i : (⊒i → ∀ x, Ψ x) ⊣⊢ ∀ x, ⊒i → Ψ x.
Proof.
  constructor => j. unseal_monpred. iSplit; iIntros "P".
  - iIntros (x k Lej Lei). by iApply ("P" $! k Lej Lei x).
  - iIntros (k Lej Lei x). by iApply ("P" $! x k Lej k with "[%//] [%//]").
Qed.

(* The reverses of the follow 4 lemmas need a lattice on biIndex *)
Lemma monPred_in_or P Q i : (⊒i → P) ∨ (⊒i → Q) ⊢ (⊒i → P ∨ Q).
Proof.
  constructor => j. unseal_monpred. iIntros "PQ" (k Lej Lei).
  iDestruct "PQ" as "[PQ|PQ]"; [iLeft|iRight]; by iApply ("PQ" $! k Lej Lei).
Qed.
Lemma monPred_in_sep P Q i : (⊒i → P) ∗ (⊒i → Q) ⊢ ⊒i → P ∗ Q.
Proof.
  constructor => j. unseal_monpred. iIntros "[P Q]" (k Lej Lei). iSplitL "P".
  - by iApply ("P" $! k Lej Lei).
  - by iApply ("Q" $! k Lej Lei).
Qed.
Lemma monPred_in_exist {A} (Ψ : A → monPred) i :
  (∃ x, ⊒i → Ψ x) ⊢ (⊒i → ∃ x, Ψ x).
Proof.
  constructor => j. unseal_monpred. iIntros "P" (k Lej Lei).
  iDestruct "P" as (x) "P". iExists x.
  by iApply ("P" $! k Lej k with "[%//] [%//]").
Qed.
Lemma monPred_in_embed (P : PROP) i : ⎡ P ⎤ ⊢ (⊒i → ⎡ P ⎤).
Proof. constructor => j. unseal_monpred. eauto. Qed.

(* Intentionally phrased as a non-instance to avoid TC divergence. *)
Lemma monPred_timeless P : (∀ i, Timeless (P i)) → Timeless P.
Proof.
  intros HP. constructor=> i.
  rewrite monPred_at_later monPred_at_except_0. apply HP.
Qed.

Lemma monPred_objectively_intuitionistically `{BiPersistentlyForall PROP} P :
  <obj> □ P ⊣⊢ □ <obj> P.
Proof.
  apply bi.equiv_entails; split; iIntros "#P"; iModIntro; iModIntro; iApply "P".
Qed.
Lemma monPred_objectively_intuitionistically_if `{BiPersistentlyForall PROP} p P :
  <obj> □?p P ⊣⊢ □?p <obj> P.
Proof. destruct p=>//=. apply monPred_objectively_intuitionistically. Qed.

Lemma monPred_objectively_subjectively P Q :
  <obj> (<subj> P -∗ Q) -∗ <subj> P -∗ <obj> Q.
Proof.
  iStartProof PROP. iIntros (?) "PQ". iIntros (??) "P".
  rewrite 2!monPred_at_objectively. iIntros (?). iApply "PQ".
  by rewrite 2!monPred_at_subjectively.
Qed.

Lemma monPred_at_revert P i : (⊢ P) → ⊢ P i.
Proof. intros HP. by iApply HP. Qed.

Lemma monPred_objectively_later P : ▷ <obj> P ⊣⊢ <obj> ▷ P.
Proof.
  iStartProof PROP. iIntros (?). rewrite 2!monPred_at_objectively.
  rewrite bi.later_forall. eauto.
Qed.

Lemma monPred_objectively_exist_inv `{@BiIndexBottom I bot} {A}
  (Φ : A → monPred) :
  <obj> (∃ x, (Φ x)) ⊢ (∃ x, <obj> (Φ x)).
Proof.
  constructor => i. rewrite monPred_at_objectively monPred_at_exist.
  iIntros "E". iDestruct ("E" $! bot) as (x) "E".
  iExists x. rewrite monPred_at_objectively. iIntros (j).
  by rewrite (monPred_mono _ _ _ (bi_index_bot j)).
Qed.

Lemma monPred_objectively_or_inv `{@BiIndexBottom I bot} P Q :
  <obj> (P ∨ Q) ⊢ <obj> P ∨ <obj> Q.
Proof.
  constructor => i. rewrite monPred_at_or !monPred_at_objectively.
  setoid_rewrite monPred_at_or.
  iIntros "PQ".
  iDestruct ("PQ" $! bot) as "[H|H]"; [iLeft|iRight]; iIntros (j);
    by rewrite (monPred_mono _ _ _ (bi_index_bot j)).
Qed.

Lemma monPred_objectively_at P : (⊢ P) ↔ (⊢ <obj> P).
Proof.
  split; intros [HP]; constructor => i.
  - rewrite monPred_at_objectively. setoid_rewrite <-HP. eauto.
  - setoid_rewrite monPred_at_objectively in HP. rewrite HP. eauto.
Qed.

(** The inverse doesn't hold, unless P is Objective.
  This is why Objective is more applicable (because it is weaker) that <obj>. *)
Lemma monPred_objectively_wand P Q : <obj> (P -∗ Q) ⊢ (<obj> P -∗ <obj> Q).
Proof.
  constructor => V1.
  rewrite /= monPred_at_objectively !monPred_at_wand /=.
  setoid_rewrite monPred_at_objectively. setoid_rewrite monPred_at_wand.
  iIntros "W" (V2 Le) "P". iIntros (V3).
  iSpecialize ("P" $! V3).
  by iApply ("W" $! V3 V3 with "[%] P").
Qed.

Lemma monPred_subjectively_later P :
  ▷ <subj> P ⊣⊢ <subj> ▷ P.
Proof.
  constructor => i.
  rewrite monPred_subjectively_unfold monPred_at_later !monPred_at_embed.
  setoid_rewrite monPred_at_later.
  apply bi.later_exist.
Qed.

(** proofmode *)
#[global] Instance into_exist_objectively `{!@BiIndexBottom I bot} {A}
  P (Φ : A → monPred) name :
  IntoExist P Φ name → IntoExist (<obj> P) (λ a, (<obj> Φ a)%I) name.
Proof. by rewrite /IntoExist -monPred_objectively_exist_inv => ->. Qed.
#[global] Instance from_exist_objectively {A} P (Φ : A → monPred) :
  FromExist P Φ → FromExist (<obj> P) (λ a, (<obj> Φ a)%I).
Proof. by rewrite /FromExist monPred_objectively_exist => ->. Qed.

#[global] Instance into_and_objectively `{BiPersistentlyForall PROP} p P Q1 Q2:
  IntoAnd p P Q1 Q2 → IntoAnd p (<obj> P) (<obj> Q1) (<obj> Q2).
Proof.
  rewrite /IntoAnd -monPred_objectively_and=> HP.
  by rewrite -!monPred_objectively_intuitionistically_if HP.
Qed.
#[global] Instance from_and_objectively P Q1 Q2 :
  FromAnd P Q1 Q2 → FromAnd (<obj> P) (<obj> Q1) (<obj> Q2).
Proof. by rewrite /FromAnd -monPred_objectively_and => <-. Qed.

#[global] Instance into_or_objectively P Q1 Q2:
  FromOr P Q1 Q2 → FromOr (<obj> P) (<obj> Q1) (<obj> Q2).
Proof. by rewrite /FromOr monPred_objectively_or => ->. Qed.
#[global] Instance from_or_objectively P Q1 Q2 :
  FromOr P Q1 Q2 → FromOr (<obj> P) (<obj> Q1) (<obj> Q2).
Proof. by rewrite /FromOr monPred_objectively_or => <-. Qed.

#[global] Instance into_pure_objectively (φ : Prop) P :
  IntoPure P φ → IntoPure (<obj> P) φ.
Proof. rewrite /IntoPure => ->. by rewrite monPred_objectively_pure. Qed.
#[global] Instance from_pure_objectively a P φ :
  FromPure a P φ → FromPure a (<obj> P) φ.
Proof.
  rewrite /FromPure -embed_pure -embed_affinely_if => <-.
  apply objective_objectively, _.
Qed.

#[global] Instance into_pure_subjectively (φ : Prop) P :
  IntoPure P φ → IntoPure (<subj> P) φ.
Proof. rewrite /IntoPure=> ->. apply objective_subjectively, _. Qed.
#[global] Instance from_pure_subjectively a P φ :
  FromPure a P φ → FromPure a (<subj> P) φ.
Proof.
  rewrite /FromPure -embed_pure -embed_affinely_if => <-.
  apply monPred_subjectively_intro.
Qed.

#[global] Instance into_sep_subjectively P Q1 Q2 :
  IntoSep P Q1 Q2 → IntoSep (<subj> P) (<subj> Q1) (<subj> Q2).
Proof. by rewrite /IntoSep -monPred_subjectively_sep => ->. Qed.

#[global] Instance into_exist_subjectively {A}
  P (Φ : A → monPred) name :
  IntoExist P Φ name → IntoExist (<subj> P) (λ a, (<subj> Φ a)%I) name.
Proof. by rewrite /IntoExist -monPred_subjectively_exist => ->. Qed.
#[global] Instance from_exist_subjectively {A} P (Φ : A → monPred) :
  FromExist P Φ → FromExist (<subj> P) (λ a, (<subj> Φ a)%I).
Proof. by rewrite /FromExist -monPred_subjectively_exist => ->. Qed.
End ExtraMonpred.
(* End MOVE *)

Global Hint Extern 2 (environments.envs_entails _ (<subj> _)) => iModIntro : core.
