From iris.bi Require Export monpred big_op.
From iris.proofmode Require Import proofmode monpred modality_instances.
From iris.base_logic.lib Require Import fancy_updates.

From gpfsl.lang Require Export lang.
From gpfsl.base_logic Require Export bi.

Require Import iris.prelude.options.

Canonical Structure lat_bi_index (Lat : latticeT) :=
  {| bi_index_type := Lat |}.
Global Instance lat_bi_index_bot (Lat : latticeT) (bot : Lat) :
  LatBottom bot → BiIndexBottom bot.
Proof. done. Qed.

Canonical Structure view_bi_index :=
  {| bi_index_type := view |}.

(* Types of view predicates. *)
Definition vProp Σ := monPred view_bi_index (uPredI (iResUR Σ)).
Definition vPropO Σ := monPredO view_bi_index (uPredI (iResUR Σ)).
Definition vPropI Σ := monPredI view_bi_index (uPredI (iResUR Σ)).

Global Hint Extern 10 (IsBiIndexRel _ _) => unfold IsBiIndexRel; solve_lat
            : typeclass_instances.

Global Bind Scope bi_scope with vProp.

Implicit Types (V: view).

Section defs.
Context `{Σ: gFunctors}.
#[local] Notation vProp := (vProp Σ).
Implicit Types (P : vProp).

Program Definition view_join_def V P : vProp := MonPred (λ V0, P (V0 ⊔ V)) _.
Next Obligation. intros V P V1 V2 Le. eauto. Qed.
Definition view_join_aux : seal (@view_join_def). Proof. by eexists. Qed.
Definition view_join := unseal (@view_join_aux).
Definition view_join_eq : @view_join = _ := seal_eq _.

Definition view_at_def V P : vProp := ⎡ P V ⎤.
Definition view_at_aux : seal (@view_at_def). Proof. by eexists. Qed.
Definition view_at := unseal (@view_at_aux).
Definition view_at_eq : @view_at = _ := seal_eq _.

End defs.

Arguments view_join {_} _ _%I : simpl never.
Arguments view_at {_} _ _%I : simpl never.

Notation "'⊔{' V '}' P" := (view_join V P) (at level 25, format "⊔{ V }  P") : bi_scope.
Notation "'@{' V '}' P" := (view_at V P) (at level 25, format "@{ V }  P") : bi_scope.

Global Instance : Params (@view_join) 1 := {}.
Global Instance : Params (@view_at) 1 := {}.

Section props.
Context `{Σ : gFunctors}.
#[local] Notation vProp := (vProp Σ).
Implicit Types (P Q : vProp).

(** These lemmas require a semi-lattice structure on the index,
  which monPred doesn't have *)

#[local] Definition unseal_eqs :=
  (@monPred_at_embed, @monPred_at_pure, @monPred_at_emp,
   @monPred_at_and, @monPred_at_or, @monPred_at_impl,
   @monPred_at_sep,
   @monPred_at_exist, @monPred_at_forall, @monPred_at_wand,
   @monPred_at_plainly, @monPred_at_persistently, @monPred_at_affinely,
   @monPred_at_intuitionistically, @monPred_at_absorbingly,
   @monPred_at_fupd, @monPred_at_bupd, @monPred_at_later, @monPred_at_laterN,
   @monPred_at_except_0).
#[local] Definition unseal_eqs_embed :=
   (@embed_pure, @embed_emp,
    @embed_and, @embed_or, @embed_impl,
    @embed_sep,
    @embed_exist, @embed_forall, @embed_wand,
    @embed_plainly, @embed_persistently, @embed_affinely,
    @embed_intuitionistically, @embed_absorbingly,
    @embed_fupd, @embed_bupd, @embed_later, @embed_laterN,
    @embed_except_0).
#[local] Ltac un_va :=
  rewrite view_at_eq /view_at_def /= ?unseal_eqs /= ?unseal_eqs_embed /=.

(* view_at *)
Lemma view_at_unfold P V : @{V} P ⊣⊢ ⎡ P V ⎤.
Proof. by un_va. Qed.
Lemma view_at_unfold_2 P V V' : (@{V} P) V' ⊣⊢ P V.
Proof. by un_va. Qed.

#[local] Ltac un_va_2 := rewrite !view_at_unfold.
#[local] Ltac un_va_3 := setoid_rewrite view_at_unfold.

#[global] Instance view_at_ne V : NonExpansive (view_at V : _ → vProp).
Proof. un_va; solve_proper. Qed.
#[global] Instance view_at_proper :
  Proper ((≡) ==> (≡) ==> (≡)) (view_at : _ → vProp → vProp).
Proof. intros ?? ->%leibniz_equiv_iff. apply (ne_proper _). Qed.

#[global] Instance view_at_mono :
  Proper ((⊑) ==> (⊢) ==> (⊢)) (view_at : _ → vProp → vProp).
Proof.
  intros V1 V2 Ext P Q EN. un_va_2. by rewrite EN monPred_mono.
Qed.
#[global] Instance view_at_flip_mono :
  Proper ((flip (⊑)) ==> (flip (⊢)) ==> flip (⊢)) (view_at : _ → vProp → vProp).
Proof. intros ?????. simpl in *. by apply view_at_mono. Qed.

#[global] Instance view_at_persistent P V : Persistent P → Persistent (@{V} P).
Proof. un_va_2. apply _. Qed.
#[global] Instance view_at_timeless P V : Timeless P → Timeless (@{V} P).
Proof. un_va_2. apply _. Qed.

(* TODO : need Proper for Objective *)
#[global] Instance view_at_objective P V : Objective (@{V} P).
Proof. un_va. apply _. Qed.

Lemma view_at_mono' V1 V2 P Q :
  V1 ⊑ V2 → @{V1} P -∗ @{V2} (P -∗ Q) -∗ @{V2} Q.
Proof. intros Le. un_va_2. iIntros "P PQ". iApply "PQ". iFrame "P". Qed.

Lemma view_at_mono_2 V1 V2 P : V1 ⊑ V2 → @{V1} P ⊢ @{V2} P.
Proof. intros. by apply view_at_mono. Qed.

Lemma view_at_intro P : P ⊢ ∃ V, ⊒V ∧ @{V} P.
Proof. un_va_3. by apply monPred_in_intro. Qed.
Lemma view_at_intro_incl P V' : P -∗ ⊒V' -∗ ∃ V, ⊒V ∧ ⌜V' ⊑ V⌝ ∧ @{V} P.
Proof. un_va_3. by apply monPred_in_intro_incl. Qed.
Lemma view_at_elim V P : ⊒V -∗ @{V} P -∗ P.
Proof. un_va_2. by apply monPred_in_elim'. Qed.

Lemma view_at_and P Q V : @{V} (P ∧ Q) ⊣⊢ @{V} P ∧ @{V} Q.
Proof. by un_va. Qed.
Lemma view_at_or  P Q V : @{V} (P ∨ Q) ⊣⊢ @{V} P ∨ @{V} Q.
Proof. by un_va. Qed.
Lemma view_at_pure φ V : (@{V} ⌜φ⌝ : vProp) ⊣⊢ ⌜φ⌝.
Proof. by un_va. Qed.
Lemma view_at_emp V : (@{V} emp) ⊣⊢@{vPropI Σ} emp.
Proof. un_va. by apply bi.True_emp. Qed.
Lemma view_at_embed (P : iProp Σ) V : @{V} ⎡ P ⎤ ⊣⊢ ⎡ P ⎤.
Proof. by un_va. Qed.

Lemma view_at_view_at P V1 V2 : @{V2} (@{V1} P) ⊣⊢ @{V1} P.
Proof. by un_va. Qed.

Lemma view_at_subjectively P V : @{V} P ⊢ <subj> P.
Proof. un_va_2. rewrite monPred_subjectively_unfold. iIntros "P". by iExists _. Qed.

Lemma view_at_subjectively_inv P : <subj> P ⊢ ∃ V, @{V} P.
Proof. un_va_3. by rewrite monPred_subjectively_unfold embed_exist. Qed.

Lemma view_at_sep P Q V : @{V} (P ∗ Q) ⊣⊢ @{V} P ∗ @{V} Q.
Proof. by un_va. Qed.

Lemma view_at_plainly P V : @{V} (■ P) ⊢ ■ (@{V} P).
Proof.
  un_va_2. rewrite monPred_at_plainly -embed_plainly.
  iIntros "HP". by iApply ("HP" $! V).
Qed.

Lemma view_at_persistently P V : @{V} <pers> P ⊣⊢ <pers> @{V} P.
Proof. by un_va. Qed.
Lemma view_at_persistently_if p P V : @{V} <pers>?p P ⊣⊢ <pers>?p (@{V} P).
Proof. destruct p=>//=. by apply view_at_persistently. Qed.
Lemma view_at_affinely P V : @{V} <affine> P ⊣⊢ <affine> @{V} P.
Proof. by un_va. Qed.
Lemma view_at_affinely_if p P V : @{V} <affine>?p P ⊣⊢ <affine>?p (@{V} P).
Proof. destruct p=>//=. apply view_at_affinely. Qed.
Lemma view_at_intuitionistically P V : @{V} □ P ⊣⊢ □ @{V} P.
Proof. by un_va. Qed.
Lemma view_at_intuitionistically_if p P V : @{V} □?p P ⊣⊢ □?p (@{V} P).
Proof. destruct p=>//=. apply view_at_intuitionistically. Qed.

Lemma view_at_absorbingly P V : @{V} <absorb> P ⊣⊢ <absorb> @{V} P.
Proof. by un_va. Qed.
Lemma view_at_absorbingly_if p P V : @{V} <absorb>?p P ⊣⊢ <absorb>?p (@{V} P).
Proof. destruct p=>//=. apply view_at_absorbingly. Qed.

Lemma view_at_at P V : (⊢ P) → ⊢ @{V} P.
Proof. intros [HP]. constructor => ?. un_va_2. rewrite -HP. eauto. Qed.

(* The reverse doesn't hold *)
Lemma view_at_impl P Q V : @{V} (P → Q) ⊢ (@{V} P → @{V} Q).
Proof.
  un_va_2. rewrite monPred_at_impl -embed_impl. apply embed_mono.
  iIntros "PQ". by iApply "PQ".
Qed.

Lemma view_at_exist {A} (Ψ : A → vProp) V : @{V} (∃ x, Ψ x) ⊣⊢ ∃ x, @{V} Ψ x.
Proof. by un_va. Qed.
Lemma view_at_forall {A} (Ψ : A → vProp) V : @{V} (∀ x, Ψ x) ⊣⊢ ∀ x, @{V} Ψ x.
Proof. by un_va. Qed.

(* The reverse doesn't hold *)
Lemma view_at_wand P Q V : @{V} (P -∗ Q) ⊢ (@{V} P -∗ @{V} Q).
Proof. un_va_2. iIntros "PQ P". by iApply "PQ". Qed.
Lemma view_at_wand_2 P Q V : (⊢ @{V} (P -∗ Q)) → @{V} P -∗ @{V} Q.
Proof. intros HP. iApply view_at_wand. iApply HP. Qed.

Lemma view_at_bupd P V : @{V} (|==> P ) ⊣⊢ |==> @{V} P.
Proof. by un_va. Qed.
Lemma view_at_fupd `{invGS Σ} E1 E2 P V :
  @{V} (|={E1,E2}=> P) ⊣⊢ (|={E1,E2}=> @{V} P).
Proof. by un_va. Qed.

Lemma view_at_later P V : @{V} ▷ P ⊣⊢ ▷ @{V} P.
Proof. by un_va. Qed.
Lemma view_at_laterN n P V : @{V} ▷^n P ⊣⊢ ▷^n (@{V} P).
Proof. by un_va. Qed.
Lemma view_at_except_0 P V : @{V} ◇ P ⊣⊢ ◇ @{V} P.
Proof. by un_va. Qed.

Lemma view_at_objective_iff P V `{!Objective P}: @{V} P ⊣⊢ P.
Proof. constructor=>?. un_va. by apply : (anti_symm); apply : objective_at. Qed.

Lemma view_at_objectively P V : <obj> P ⊢ @{V} P.
Proof. un_va_2. rewrite monPred_objectively_unfold embed_forall. eauto. Qed.

(* Convenient lemmas to create specialized instances that drop views *)
Lemma view_at_wand_l P Q R :
  (∀ V1 V2, @{V1} P -∗ @{V2} Q -∗ R) → ∀ V2, P -∗ @{V2} Q -∗ R.
Proof.
  intros IMPL V2. iIntros "P".
  iDestruct (view_at_intro with "P") as (V1) "[_ P]". iApply (IMPL with "P").
Qed.

Lemma view_at_wand_r P Q R :
  (∀ V1 V2, @{V1} P -∗ @{V2} Q -∗ R) → ∀ V1, @{V1} P -∗ Q -∗ R.
Proof.
  intros IMPL V1. iIntros "P Q".
  iDestruct (view_at_intro with "Q") as (V2) "[_ Q]". iApply (IMPL with "P Q").
Qed.

Lemma view_at_wand_lr P Q R :
  (∀ V1 V2, @{V1} P -∗ @{V2} Q -∗ R) → P -∗ Q -∗ R.
Proof.
  intros IMPL. iIntros "P Q".
  iDestruct (view_at_intro with "Q") as (V2) "[_ Q]".
  by iApply (view_at_wand_l with "P Q").
Qed.

(* monPred_in *)
Lemma monPred_in_view_op V1 V2 : ⊒V1 ∗ ⊒V2 ⊣⊢@{vPropI Σ} ⊒(V1 ⊔ V2).
Proof.
  iStartProof (iProp _). iIntros (V'). iPureIntro.
  split; [intros []| intros]; solve_lat.
Qed.

(* view_join *)
#[local] Ltac intros_vj :=
  constructor => ?; rewrite /= view_join_eq /view_join_def /=.
#[local] Ltac un_vj := intros_vj; rewrite !unseal_eqs /=.

Lemma view_join_op P V1 V2 : (⊔{V1} ⊔{V2} P) ⊣⊢ ⊔{V1 ⊔ V2} P.
Proof. intros_vj. by rewrite assoc. Qed.

Lemma view_at_view_join P V1 V2 : @{V1} (⊔{V2} P) ⊣⊢ @{V1 ⊔ V2} P.
Proof. un_va. by un_vj. Qed.
Lemma view_join_view_at P V1 V2 : ⊔{V2} (@{V1} P) ⊣⊢ @{V1} P.
Proof. un_va. by un_vj. Qed.
Lemma view_at_to_view_join P V : @{V} P ⊢ ⊔{V} P.
Proof. un_va. by un_vj; eauto. Qed.

Lemma view_join_at P V : (⊢ P)→ ⊢ ⊔{V} P.
Proof. intros [HP]. intros_vj. iIntros "_". by iApply HP. Qed.

Lemma view_join_pure φ V : (⊔{V} ⌜φ⌝ : vProp) ⊣⊢ ⌜φ⌝.
Proof. by un_vj. Qed.
Lemma view_join_emp V : (⊔{V} emp : vProp) ⊣⊢ emp.
Proof. by un_vj. Qed.
Lemma view_join_and P Q V : ⊔{V} (P ∧ Q) ⊣⊢ ⊔{V} P ∧ ⊔{V} Q.
Proof. by un_vj. Qed.
Lemma view_join_or P Q V : ⊔{V} (P ∨ Q) ⊣⊢ ⊔{V} P ∨ ⊔{V} Q.
Proof. by un_vj. Qed.
Lemma view_join_embed (P : iProp Σ) V : ⊔{V} ⎡ P ⎤ ⊣⊢ ⎡ P ⎤.
Proof. by un_vj. Qed.

Lemma view_join_impl P Q V : ⊔{V} (P → Q) ⊣⊢ (⊔{V} P → ⊔{V} Q).
Proof.
  un_vj. iSplit.
  - iIntros "W" (V2 Le). iApply "W". iPureIntro; solve_lat.
  - iIntros "W" (V2 Le).
    iSpecialize ("W" $! V2 with "[%]"); first solve_lat.
    rewrite (_: V2 ⊔ V = V2) //.
    apply : anti_symm; simpl; solve_lat.
Qed.

Lemma view_join_sep P Q V : ⊔{V} (P ∗ Q) ⊣⊢ ⊔{V} P ∗ ⊔{V} Q.
Proof. by un_vj. Qed.

Lemma view_join_exist {A} (Ψ : A → vProp) V : ⊔{V} (∃ x, Ψ x) ⊣⊢ ∃ x, ⊔{V} Ψ x.
Proof. by un_vj. Qed.
Lemma view_join_forall {A} (Ψ : A → vProp) V : ⊔{V} (∀ x, Ψ x) ⊣⊢ ∀ x, ⊔{V} Ψ x.
Proof. by un_vj. Qed.

Lemma view_join_wand P Q V : ⊔{V} (P -∗ Q) ⊣⊢ (⊔{V} P -∗ ⊔{V} Q).
Proof.
  un_vj. iSplit.
  - iIntros "W" (V2 Le). iApply "W". iPureIntro; solve_lat.
  - iIntros "W" (V2 Le).
    iSpecialize ("W" $! V2 with "[%]"); first solve_lat.
    rewrite (_: V2 ⊔ V = V2) //.
    apply : anti_symm; simpl; solve_lat.
Qed.
Lemma view_join_wand_2 P Q V : (⊢ ⊔{V} (P -∗ Q)) → ⊔{V} P -∗ ⊔{V} Q.
Proof. intros HP. iApply view_join_wand. iApply HP. Qed.

Lemma view_join_plainly P V : ⊔{V} (■ P) ⊢ ■ (⊔{V} P).
Proof. un_vj. iIntros "HP" (j). by iApply "HP". Qed.

Lemma view_join_persistently P V : ⊔{V} <pers> P ⊣⊢ <pers> ⊔{V} P.
Proof. by un_vj. Qed.
Lemma view_join_persistently_if p P V : ⊔{V} <pers>?p P ⊣⊢ <pers>?p ⊔{V} P.
Proof. destruct p=>//=. by apply view_join_persistently. Qed.
Lemma view_join_affinely P V : ⊔{V} <affine> P ⊣⊢ <affine> ⊔{V} P.
Proof. by un_vj. Qed.
Lemma view_join_affinely_if p P V : ⊔{V} <affine>?p P ⊣⊢ <affine>?p ⊔{V} P.
Proof. destruct p=>//=. apply view_join_affinely. Qed.
Lemma view_join_intuitionistically P V : ⊔{V} □ P ⊣⊢ □ ⊔{V} P.
Proof. by un_vj. Qed.
Lemma view_join_intuitionistically_if p P V : ⊔{V} □?p P ⊣⊢ □?p ⊔{V} P.
Proof. destruct p=>//=. apply view_join_intuitionistically. Qed.

Lemma view_join_absorbingly P V : ⊔{V} <absorb> P ⊣⊢ <absorb> ⊔{V} P.
Proof. by un_vj. Qed.
Lemma view_join_absorbingly_if p P V : ⊔{V} <absorb>?p P ⊣⊢ <absorb>?p ⊔{V} P.
Proof. destruct p=>//=. apply view_join_absorbingly. Qed.

Lemma view_join_bupd P V : ⊔{V} (|==> P) ⊣⊢ |==> ⊔{V} P.
Proof. by un_vj. Qed.
Lemma view_join_fupd `{invGS Σ} E1 E2 P V :
  ⊔{V} (|={E1,E2}=> P) ⊣⊢ (|={E1,E2}=> ⊔{V} P).
Proof. by un_vj. Qed.

Lemma view_join_later P V : ⊔{V} ▷ P ⊣⊢ ▷ ⊔{V} P.
Proof. by un_vj. Qed.
Lemma view_join_laterN n P V : ⊔{V} ▷^n P ⊣⊢ ▷^n ⊔{V} P.
Proof. by un_vj. Qed.
Lemma view_join_except_0 P V : ⊔{V} ◇ P ⊣⊢ ◇ ⊔{V} P.
Proof. by un_vj. Qed.

Lemma view_join_mono_I P Q V : (P -∗ Q) -∗ (⊔{V} P -∗ ⊔{V} Q).
Proof. intros_vj. iIntros "PQ" (? ->). rewrite /= -monPred_wand_force. eauto. Qed.

#[global] Instance view_join_ne V : NonExpansive (view_join V : _ → vProp).
Proof. intros ????. intros_vj. solve_proper. Qed.
#[global] Instance view_join_proper V :
  Proper ((≡) ==> (≡)) (view_join V : _ → vProp).
Proof. apply (ne_proper _). Qed.
Lemma view_join_mono P Q V : (P ⊢ Q) → (⊔{V} P ⊢ ⊔{V} Q).
Proof. intros MN. iApply view_join_mono_I. by iApply MN. Qed.
#[global] Instance view_join_mono' V :
  Proper ((⊢) ==> (⊢)) (view_join V : _ → vProp).
Proof. intros ???. by apply view_join_mono. Qed.
#[global] Instance view_join_flip_mono' V :
  Proper (flip (⊢) ==> flip (⊢)) (view_join V : _ → vProp).
  Proof. intros ???. by apply view_join_mono. Qed.
Lemma view_join_mono_view P Q V1 V2 : V1 ⊑ V2 → (P ⊢ Q) → (⊔{V1} P ⊢ ⊔{V2} Q).
Proof. intros ? [MN]. intros_vj. rewrite MN. eauto. Qed.
#[global] Instance view_join_mono_view' :
  Proper ((⊑) ==> (⊢) ==> (⊢)) (view_join : _ → _ → vProp).
Proof. intros ?????. by apply view_join_mono_view. Qed.

#[global] Instance view_join_objective P `{!Objective P} V : Objective (⊔{V} P).
Proof. intros ??. rewrite view_join_eq /=. by apply objective_at. Qed.

#[global] Instance view_join_timeless P V : Timeless P → Timeless (⊔{V} P).
Proof.
  intros. rewrite /Timeless -view_join_later -view_join_except_0.
  by apply view_join_wand_2, view_join_at, bi.entails_wand.
Qed.

#[global] Instance view_join_persistent P V : Persistent P → Persistent (⊔{V} P).
Proof.
  intros. rewrite /Persistent -view_join_persistently.
  by apply view_join_wand_2, view_join_at, bi.entails_wand.
Qed.
#[global] Instance view_join_absorbing P V : Absorbing P → Absorbing (⊔{V} P).
Proof.
  intros. rewrite /Absorbing -view_join_absorbingly.
  by apply view_join_wand_2, view_join_at, bi.entails_wand.
Qed.
#[global] Instance view_join_affine P V : Affine P → Affine (⊔{V} P).
Proof. intros [AF]. rewrite /Affine. intros_vj. rewrite AF. eauto. Qed.

Lemma view_join_objective_iff P V `{!Objective P}: ⊔{V} P ⊣⊢ P.
Proof. intros_vj. by apply : (anti_symm); apply : objective_at. Qed.
Lemma view_join_objectively P V : <obj> P ⊢ ⊔{V} P.
Proof. intros_vj. rewrite monPred_objectively_unfold /= monPred_at_embed. eauto. Qed.

Lemma view_join_join_l P Q V : P ∗ ⊔{V} Q ⊢ ⊔{V} (P ∗ Q).
Proof. un_vj. by iIntros "[$ $]". Qed.
Lemma view_join_join_r P Q V : ⊔{V} P ∗ Q ⊢ ⊔{V} (P ∗ Q).
Proof. un_vj. by iIntros "[$ $]". Qed.

Lemma view_join_unfold V P :
  ⊔{V} P ⊣⊢ (⊒V → P).
Proof.
  un_vj. iSplit.
  - iIntros "P" (V'' Le Le3). by iFrame.
  - iIntros "P". iApply "P"; iPureIntro; solve_lat.
Qed.

Lemma view_join_intro_current P V : P -∗ ⊔{V} P.
Proof. rewrite view_join_unfold. eauto. Qed.

Lemma view_join_intro_at P V1 V2 : @{V1 ⊔ V2} P -∗ ⊒V1 -∗ ⊔{V2} P.
Proof.
  rewrite -view_at_view_join. iIntros "P V1". iApply (view_at_elim with "V1 P").
Qed.

Lemma view_join_elim P V : ⊔{V} P -∗ ⊒V -∗ P.
Proof. rewrite view_join_unfold. iIntros "P In". by iApply "P". Qed.

Lemma view_join_elim' P V0 V :
  ⊔{V} P -∗ ⊒V0 -∗ ∃ V', ⊒V' ∧ ⌜V0 ⊑ V'⌝ ∧ @{V ⊔ V'} P.
Proof.
  iIntros "P In".
  iDestruct (view_at_intro_incl with "P In") as (V') "(In' & ? & At)".
  rewrite view_at_view_join.
  iExists _. iFrame. iApply (view_at_mono_2 with "At"). solve_lat.
Qed.

Lemma view_join_to_view_at P V :
  ⊔{V} P -∗ ∃ V', ⊒V' ∧ @{V ⊔ V'} P.
Proof.
  iIntros "P". iDestruct (view_join_elim' with "P []") as (V') "(sV' & ? & P)".
  - iApply monPred_in_bot.
  - iExists V'. by iFrame.
Qed.

Lemma view_join_later_timeless `{invGS Σ} P `{!Timeless P} V E:
  ⊔{V} ▷ P ={E}=∗ ⊔{V} P.
Proof. rewrite view_join_later. by iIntros ">$". Qed.

(* These need a lattice on biIndex. *)
Lemma monPred_in_or' P Q V : (⊒V → P ∨ Q) ⊣⊢ ((⊒V → P) ∨ (⊒V → Q)).
Proof. rewrite -!view_join_unfold. by apply view_join_or. Qed.

Lemma monPred_in_sep' P Q V : (⊒V → P ∗ Q) ⊣⊢ ((⊒V → P) ∗ (⊒V → Q)).
Proof. rewrite -!view_join_unfold. by apply view_join_sep. Qed.

Lemma monPred_in_exist' {A} (Ψ : A → vProp) V : (⊒V → ∃ x, Ψ x) ⊣⊢ ∃ x, ⊒V → Ψ x.
Proof.
  rewrite -view_join_unfold. setoid_rewrite <- view_join_unfold.
  by apply view_join_exist.
Qed.

Lemma monPred_in_embed' (P : iProp Σ) V : (⊒V → ⎡ P ⎤) ⊣⊢ ⎡ P ⎤.
Proof. rewrite -view_join_unfold. by apply view_join_embed. Qed.

Lemma monPred_in_join_l P Q V : P ∗ (⊒V → Q) ⊢ ⊒V → P ∗ Q.
Proof. rewrite -!view_join_unfold. by apply view_join_join_l. Qed.
Lemma monPred_in_join P Q V : (⊒V → P) ∗ Q ⊢ ⊒V → P ∗ Q.
Proof. rewrite -!view_join_unfold. by apply view_join_join_r. Qed.

Lemma monPred_in_view_elim P V : (⊒V → P) -∗ ⎡ ∃ V', P V' ⎤.
Proof.
  constructor=> Vx. iIntros "H". iExists (V ⊔ Vx). iApply "H". iPureIntro. solve_lat.
Qed.

Lemma monPred_in_later_timeless `{invGS Σ} P `{!Timeless P} V E :
  (⊒V → ▷ P) ={E}=∗ ⊒V → P.
Proof. rewrite -!view_join_unfold. by apply view_join_later_timeless. Qed.

Lemma view_join_view_at_access P Vb V :
  ⊒V -∗ ⊔{Vb} P -∗
  ∃ V', ⌜V ⊑ V'⌝ ∗ ⊒V' ∗ @{Vb ⊔ V'} P ∗ □ (∀ V'', ⊒V'' -∗ @{Vb ⊔ V''} P -∗ ⊔{Vb} P).
Proof.
  iIntros "InV P".
  iDestruct (view_join_elim' with "P InV") as (V') "[InV' [LeV' P]]".
  iExists V'. iFrame.
  iIntros "!>" (V'') "InV'' P".
  rewrite lat_join_comm_L. by iApply (view_join_intro_at with "P InV''").
Qed.

Lemma view_join_view_at_access' (P : vProp) Vb :
  ⊔{Vb} P -∗ ∃ V', ⊒V' ∗ @{Vb ⊔ V'} P ∗ □ (∀ V'', ⊒V'' -∗ @{Vb ⊔ V''} P -∗ ⊔{Vb} P).
Proof.
  iIntros "P".
  iDestruct (monPred_in_intro True%I with "[//]") as (V) "[InV _]".
  iDestruct (view_join_view_at_access with "InV P") as (V') "(_ & InV' & CL)".
  iExists V'. by iFrame.
Qed.

(* subjectively : the reverse direction needs a lattice on the biIndex *)
Lemma view_subjectively_sep P Q : <subj> (P ∗ Q) ⊣⊢ <subj> P ∗ <subj> Q.
Proof.
  constructor => ?. iSplit.
  - rewrite -monPred_wand_force -monPred_at_revert // monPred_subjectively_sep.
    eauto.
  - iIntros "[P1 P2]".
    rewrite !monPred_at_subjectively.
    iDestruct "P1" as (V1) "P1". iDestruct "P2" as (V2) "P2".
    iExists (V1 ⊔ V2). by iFrame "P1 P2".
Qed.
End props.

Section proofmode.
Context `{Σ : gFunctors}.
#[local] Notation vProp := (vProp Σ).
Implicit Types (P Q R : vProp).

#[global] Instance into_pure_view_join (φ : Prop) P V :
  IntoPure P φ → IntoPure (⊔{V} P) φ.
Proof. rewrite /IntoPure=> ->. by rewrite view_join_pure. Qed.
#[global] Instance from_pure_view_join a P φ V :
  FromPure a P φ → FromPure a (⊔{V} P) φ.
Proof. rewrite /FromPure=> <-. by rewrite -{1}view_join_pure view_join_affinely_if. Qed.

#[global] Instance into_wand_view_join p q R P Q V :
  IntoWand p q R P Q → IntoWand p q (⊔{V} R) (⊔{V} P) (⊔{V} Q).
Proof.
  rewrite /IntoWand -!view_join_intuitionistically_if -view_join_wand => ?.
  by apply view_join_wand_2, view_join_at, bi.entails_wand.
Qed.
#[global] Instance from_wand_view_join P Q1 Q2 V :
  FromWand P Q1 Q2 → FromWand (⊔{V} P) (⊔{V} Q1) (⊔{V} Q2).
Proof. by rewrite /FromWand -view_join_wand => <-. Qed.

#[global] Instance from_impl_view_join P Q1 Q2 V :
  FromImpl P Q1 Q2 → FromImpl (⊔{V} P) (⊔{V} Q1) (⊔{V} Q2).
Proof. by rewrite /FromImpl -view_join_impl => <-. Qed.

#[global] Instance into_and_view_join p P Q1 Q2 V :
  IntoAnd p P Q1 Q2 → IntoAnd p (⊔{V} P) (⊔{V} Q1) (⊔{V} Q2).
Proof.
  rewrite /IntoAnd -view_join_and=> HP.
  rewrite -!view_join_intuitionistically_if.
  by apply view_join_wand_2, view_join_at, bi.entails_wand.
Qed.
#[global] Instance from_and_view_join P Q1 Q2 V :
  FromAnd P Q1 Q2 → FromAnd (⊔{V} P) (⊔{V} Q1) (⊔{V} Q2).
Proof. by rewrite /FromAnd -view_join_and => <-. Qed.

#[global] Instance into_sep_view_join P Q1 Q2 V :
  IntoSep P Q1 Q2 → IntoSep (⊔{V} P) (⊔{V} Q1) (⊔{V} Q2).
Proof. rewrite /IntoSep -view_join_sep=> -> //. Qed.
#[global] Instance from_sep_view_join P Q1 Q2 V :
  FromSep P Q1 Q2 → FromSep (⊔{V} P) (⊔{V} Q1) (⊔{V} Q2).
Proof. by rewrite /FromSep -view_join_sep => <-. Qed.
#[global] Instance maybe_combine_sep_as_view_join P Q1 Q2 V progress :
  MaybeCombineSepAs P Q1 Q2 progress →
  MaybeCombineSepAs (⊔{V} P) (⊔{V} Q1) (⊔{V} Q2) progress.
Proof. by rewrite /MaybeCombineSepAs -view_join_sep => <-. Qed.

#[global] Instance into_or_view_join P Q1 Q2 V :
  IntoOr P Q1 Q2 → IntoOr (⊔{V} P) (⊔{V} Q1) (⊔{V} Q2).
Proof. by rewrite /IntoOr -view_join_or => <-. Qed.
#[global] Instance from_or_view_join P Q1 Q2 V :
  FromOr P Q1 Q2 → FromOr (⊔{V} P) (⊔{V} Q1) (⊔{V} Q2).
Proof. by rewrite /FromOr -view_join_or => <-. Qed.

#[global] Instance into_exist_view_join {A} P V (Φ : A → vProp) name :
  IntoExist P Φ name → IntoExist (⊔{V} P) (λ a, (⊔{V} Φ a)%I) name.
Proof. by rewrite /IntoExist -view_join_exist => <-. Qed.
#[global] Instance from_exist_view_join {A} P V (Φ : A → vProp) :
  FromExist P Φ → FromExist (⊔{V} P) (λ a, (⊔{V} Φ a)%I).
Proof. by rewrite /FromExist -view_join_exist => <-. Qed.

#[global] Instance into_forall_view_join {A} P V (Φ : A → vProp) :
  IntoForall P Φ → IntoForall (⊔{V} P) (λ a, (⊔{V} Φ a)%I).
Proof. by rewrite /IntoForall -view_join_forall => <-. Qed.
#[global] Instance from_forall_view_join {A} P V (Φ : A → vProp) name :
  FromForall P Φ name → FromForall (⊔{V} P) (λ a, (⊔{V} Φ a)%I) name.
Proof. by rewrite /FromForall -view_join_forall => <-. Qed.

#[global] Instance into_later_view_join n P Q V :
  IntoLaterN false n P Q → IntoLaterN false n (⊔{V} P) (⊔{V} Q).
Proof. rewrite /IntoLaterN /MaybeIntoLaterN => ->. by rewrite view_join_laterN. Qed.

#[global] Instance from_modal_id_view_join φ `(sel : A) P Q V :
  FromModal φ modality_id sel P Q →
  FromModal φ modality_id sel (⊔{V} P) (⊔{V} Q) | 100.
Proof. rewrite /FromModal /= =>HPQ ?. rewrite -HPQ //. Qed.

#[global] Instance from_modal_affinely_view_join φ `(sel : A) P Q V :
  FromModal φ modality_affinely sel P Q →
  FromModal φ modality_affinely sel (⊔{V} P) (⊔{V} Q) | 100.
Proof. rewrite /FromModal /= =>HPQ ?. by rewrite -HPQ // view_join_affinely. Qed.
#[global] Instance from_modal_persistently_view_join φ `(sel : A) P Q V :
  FromModal φ modality_persistently sel P Q →
  FromModal φ modality_persistently sel (⊔{V} P) (⊔{V} Q) | 100.
Proof. rewrite /FromModal /= =>HPQ ?. by rewrite -HPQ // view_join_persistently. Qed.
#[global] Instance from_modal_intuitionistically_view_join φ `(sel : A) P Q V :
  FromModal φ modality_intuitionistically sel P Q →
  FromModal φ modality_intuitionistically sel (⊔{V} P) (⊔{V} Q) | 100.
Proof. rewrite /FromModal /= =>HPQ ?. by rewrite -HPQ // view_join_intuitionistically. Qed.

#[global] Instance from_modal_later_view_join φ `(sel : A) n P Q V :
  FromModal φ (modality_laterN n) sel P Q →
  FromModal φ (modality_laterN n) sel (⊔{V} P) (⊔{V} Q).
Proof. rewrite /FromModal /= =>HPQ ?. by rewrite -HPQ // view_join_laterN. Qed.

#[global] Instance elim_modal_view_join_bupd_goal p p' φ P P' Q Q' V :
  ElimModal φ p p' P P' (|==> ⊔{V} Q)%I (|==> ⊔{V} Q')%I →
  ElimModal φ p p' P P' (⊔{V} |==> Q) (⊔{V} |==> Q').
Proof. by rewrite /ElimModal !view_join_bupd. Qed.
#[global] Instance elim_modal_view_join_bupd_hyp p p' φ P P' Q Q' V :
  ElimModal φ p p' (|==> ⊔{V} P)%I P' Q Q' →
  ElimModal φ p p' (⊔{V} |==> P) P' Q Q'.
Proof. by rewrite /ElimModal !view_join_bupd. Qed.

#[global] Instance elim_modal_view_join_fupd_goal `{invGS Σ}
    p p' φ E1 E2 E3 P P' Q Q' V :
  @ElimModal (vPropI Σ) φ p p' P P' (|={E1,E3}=> ⊔{V} Q)%I (|={E2,E3}=> ⊔{V} Q')%I →
  ElimModal φ p p' P P' (⊔{V} (|={E1,E3}=> Q)) (⊔{V} (|={E2,E3}=> Q')).
Proof. by rewrite /ElimModal !view_join_fupd. Qed.
#[global] Instance elim_modal_view_join_fupd_hyp `{invGS Σ}
    p p' φ E1 E2 P P' Q Q' V :
  ElimModal φ p p' (|={E1,E2}=> ⊔{V} P)%I P' Q Q' →
  ElimModal φ p p' (⊔{V} |={E1,E2}=> P) P' Q Q'.
Proof. by rewrite /ElimModal view_join_fupd. Qed.

#[global] Instance add_modal_view_join_bupd_goal P P' Q V :
  AddModal P P' (|==> ⊔{V} Q)%I → AddModal P P' (⊔{V} |==> Q).
Proof. by rewrite /AddModal !view_join_bupd. Qed.

#[global] Instance add_modal_view_join_fupd_goal `{invGS Σ} E1 E2 P P' Q V :
  AddModal P P' (|={E1,E2}=> ⊔{V} Q)%I → AddModal P P' (⊔{V} |={E1,E2}=> Q).
Proof. by rewrite /AddModal !view_join_fupd. Qed.


(* view_at *)
#[global] Instance into_pure_view_at (φ : Prop) P V :
  IntoPure P φ → IntoPure (@{V} P) φ.
Proof. rewrite /IntoPure=> ->. by rewrite view_at_pure. Qed.
#[global] Instance from_pure_view_at a P φ V :
  FromPure a P φ → FromPure a (@{V} P) φ.
Proof. rewrite /FromPure=> <-. by rewrite -{1}view_at_pure view_at_affinely_if. Qed.

#[global] Instance from_pure_view_at_monPred_in V1 V2 :
  @FromPure (vPropI Σ) false (@{V1} (⊒V2)) (V2 ⊑ V1).
Proof.
  by rewrite /FromPure view_at_eq /view_at_def /= monPred_at_in embed_pure.
Qed.

#[global] Instance into_pure_view_at_monPred_in V1 V2 :
  @IntoPure (vPropI Σ) (@{V1} (⊒V2)) (V2 ⊑ V1).
Proof.
  by rewrite /IntoPure view_at_eq /view_at_def /= monPred_at_in embed_pure.
Qed.

#[global] Instance into_embed_view_at P V : IntoEmbed (@{V} P) (P V).
Proof. by rewrite /IntoEmbed view_at_eq. Qed.

#[global] Instance into_wand_view_at p q R P Q V :
  IntoWand p q R P Q → IntoWand p q (@{V} R) (@{V} P) (@{V} Q).
Proof.
  rewrite /IntoWand -!view_at_intuitionistically_if -view_at_wand => ?.
  by apply view_at_wand_2, view_at_at, bi.entails_wand.
Qed.
(* no FromWand and FromImpl instance for view_at: they don't hold. *)

#[global] Instance into_and_view_at p P Q1 Q2 V :
  IntoAnd p P Q1 Q2 → IntoAnd p (@{V} P) (@{V} Q1) (@{V} Q2).
Proof.
  rewrite /IntoAnd -view_at_and=> HP.
  rewrite -!view_at_intuitionistically_if.
  by apply view_at_wand_2, view_at_at, bi.entails_wand.
Qed.
#[global] Instance from_and_view_at P Q1 Q2 V :
  FromAnd P Q1 Q2 → FromAnd (@{V} P) (@{V} Q1) (@{V} Q2).
Proof. by rewrite /FromAnd -view_at_and => <-. Qed.

#[global] Instance into_sep_view_at P Q1 Q2 V :
  IntoSep P Q1 Q2 → IntoSep (@{V} P) (@{V} Q1) (@{V} Q2).
Proof. rewrite /IntoSep -view_at_sep=> -> //. Qed.
#[global] Instance from_sep_view_at P Q1 Q2 V :
  FromSep P Q1 Q2 → FromSep (@{V} P) (@{V} Q1) (@{V} Q2).
Proof. by rewrite /FromSep -view_at_sep => <-. Qed.
#[global] Instance maybe_combine_sep_as_view_at P Q1 Q2 V progress :
  MaybeCombineSepAs P Q1 Q2 progress →
  MaybeCombineSepAs (@{V} P) (@{V} Q1) (@{V} Q2) progress.
Proof. by rewrite /MaybeCombineSepAs -view_at_sep => <-. Qed.

#[global] Instance into_or_view_at P Q1 Q2 V :
  IntoOr P Q1 Q2 → IntoOr (@{V} P) (@{V} Q1) (@{V} Q2).
Proof. by rewrite /IntoOr -view_at_or => <-. Qed.
#[global] Instance from_or_view_at P Q1 Q2 V :
  FromOr P Q1 Q2 → FromOr (@{V} P) (@{V} Q1) (@{V} Q2).
Proof. by rewrite /FromOr -view_at_or => <-. Qed.

#[global] Instance into_exist_view_at {A} P V (Φ : A → vProp) name :
  IntoExist P Φ name → IntoExist (@{V} P) (λ a, (@{V} Φ a)%I) name.
Proof. by rewrite /IntoExist -view_at_exist => <-. Qed.
#[global] Instance from_exist_view_at {A} P V (Φ : A → vProp) :
  FromExist P Φ → FromExist (@{V} P) (λ a, (@{V} Φ a)%I).
Proof. by rewrite /FromExist -view_at_exist => <-. Qed.

#[global] Instance into_forall_view_at {A} P V (Φ : A → vProp) :
  IntoForall P Φ → IntoForall (@{V} P) (λ a, (@{V} Φ a)%I).
Proof. by rewrite /IntoForall -view_at_forall => <-. Qed.
#[global] Instance from_forall_view_at {A} P V (Φ : A → vProp) name :
  FromForall P Φ name → FromForall (@{V} P) (λ a, (@{V} Φ a)%I) name.
Proof. by rewrite /FromForall -view_at_forall => <-. Qed.

#[global] Instance into_later_view_at n P Q V :
  IntoLaterN false n P Q → IntoLaterN false n (@{V} P) (@{V} Q).
Proof. rewrite /IntoLaterN /MaybeIntoLaterN => ->. by rewrite view_at_laterN. Qed.

#[global] Instance from_modal_id_view_at φ `(sel : A) P Q V :
  FromModal φ modality_id sel P Q →
  FromModal φ modality_id sel (@{V} P) (@{V} Q) | 100.
Proof. rewrite /FromModal /= =>HPQ ?. rewrite -HPQ //. Qed.

#[global] Instance from_modal_affinely_view_at φ `(sel : A) P Q V :
  FromModal φ modality_affinely sel P Q →
  FromModal φ modality_affinely sel (@{V} P) (@{V} Q) | 100.
Proof. rewrite /FromModal /= =>HPQ ?. by rewrite -HPQ // view_at_affinely. Qed.
#[global] Instance from_modal_persistently_view_at φ `(sel : A) P Q V :
  FromModal φ modality_persistently sel P Q →
  FromModal φ modality_persistently sel (@{V} P) (@{V} Q) | 100.
Proof. rewrite /FromModal /= =>HPQ ?. by rewrite -HPQ // view_at_persistently. Qed.
#[global] Instance from_modal_intuitionistically_view_at φ `(sel : A) P Q V :
  FromModal φ modality_intuitionistically sel P Q →
  FromModal φ modality_intuitionistically sel (@{V} P) (@{V} Q) | 100.
Proof. rewrite /FromModal /= =>HPQ ?. by rewrite -HPQ // view_at_intuitionistically. Qed.

#[global] Instance from_modal_later_view_at φ `(sel : A) n P Q V :
  FromModal φ (modality_laterN n) sel P Q →
  FromModal φ (modality_laterN n) sel (@{V} P) (@{V} Q).
Proof. rewrite /FromModal /= =>HPQ ?. by rewrite -HPQ // view_at_laterN. Qed.

#[global] Instance elim_modal_view_at_bupd_goal p p' φ P P' Q Q' V :
  ElimModal φ p p' P P' (|==> @{V} Q)%I (|==> @{V} Q')%I →
  ElimModal φ p p' P P' (@{V} |==> Q) (@{V} |==> Q').
Proof. by rewrite /ElimModal !view_at_bupd. Qed.
#[global] Instance elim_modal_view_at_bupd_hyp p p' φ P P' Q Q' V :
  ElimModal φ p p' (|==> @{V} P)%I P' Q Q' →
  ElimModal φ p p' (@{V} |==> P) P' Q Q'.
Proof. by rewrite /ElimModal !view_at_bupd. Qed.

#[global] Instance elim_modal_view_at_fupd_goal `{invGS Σ}
    p p' φ E1 E2 E3 P P' Q Q' V :
  @ElimModal (vPropI Σ) φ p p' P P' (|={E1,E3}=> @{V} Q)%I (|={E2,E3}=> @{V} Q')%I →
  ElimModal φ p p' P P' (@{V} (|={E1,E3}=> Q)) (@{V} (|={E2,E3}=> Q')).
Proof. by rewrite /ElimModal !view_at_fupd. Qed.
#[global] Instance elim_modal_view_at_fupd_hyp `{invGS Σ}
    p p' φ E1 E2 P P' Q Q' V :
  ElimModal φ p p' (|={E1,E2}=> @{V} P)%I P' Q Q' →
  ElimModal φ p p' (@{V} |={E1,E2}=> P) P' Q Q'.
Proof. by rewrite /ElimModal view_at_fupd. Qed.

#[global] Instance add_modal_view_at_bupd_goal P P' Q V :
  AddModal P P' (|==> @{V} Q)%I → AddModal P P' (@{V} |==> Q).
Proof. by rewrite /AddModal !view_at_bupd. Qed.

#[global] Instance add_modal_view_at_fupd_goal `{invGS Σ} E1 E2 P P' Q V :
  AddModal P P' (|={E1,E2}=> @{V} Q)%I → AddModal P P' (@{V} |={E1,E2}=> Q).
Proof. by rewrite /AddModal !view_at_fupd. Qed.

End proofmode.
