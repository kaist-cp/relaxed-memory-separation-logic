From iris.algebra Require Import auth gmap.
From iris.proofmode Require Import tactics.
From iris.base_logic.lib Require Import own.

From gpfsl.base_logic Require Import vprop.
From gpfsl.examples.event Require Import event.

Require Import iris.prelude.options.

Section logview.
Context {eventT : Type}.
Context {Σ : gFunctors}.
Notation event_list := (event_list eventT).
Notation iProp := (iProp Σ).
Notation vProp := (vProp Σ).

Implicit Types (E : event_list) (M : logView).

(* `M` is the thread's local "view" on the graph, which includes events
  that the thread is ordered after (ROUGHLY, synchronized with). *)
Program Definition SyncLogview E M : vProp :=
  MonPred (λ V, ⌜sync_logview E M V⌝)%I _.
Next Obligation.
  intros; intros ???. iPureIntro. by apply sync_logview_view_mono.
Qed.

Program Definition SeenLogview E M : vProp :=
  MonPred (λ V, ⌜seen_logview E M V⌝)%I _.
Next Obligation.
  intros; intros ???. iPureIntro. by apply seen_logview_view_mono.
Qed.

#[global] Instance SeenLogview_map_mono :
  Proper ((⊑) ==> (=) ==> (⊢)) (SeenLogview).
Proof.
  move => E E' /= SUB ? M ->. constructor => V. simpl. iPureIntro.
  by apply seen_logview_mono.
Qed.

#[global] Instance SyncLogview_map_mono :
  Proper ((⊑) ==> (=) ==> (⊢)) (SyncLogview).
Proof.
  move => E E' /= SUB ? M ->. constructor => V. simpl. iPureIntro.
  by apply sync_logview_mono.
Qed.

#[global] Instance SyncLogview_timeless E M :
  Timeless (SyncLogview E M).
Proof. apply monPred_timeless, _. Qed.
#[global] Instance SyncLogview_persistent E M :
  Persistent (SyncLogview E M).
Proof. apply monPred_persistent, _. Qed.
#[global] Instance SyncLogview_empty_objective E :
  Objective (SyncLogview E ∅).
Proof. intros ??. iPureIntro. intros _. apply set_Forall_empty. Qed.

#[global] Instance SeenLogview_timeless E M :
  Timeless (SeenLogview E M).
Proof. apply monPred_timeless, _. Qed.
#[global] Instance SeenLogview_persistent E M :
  Persistent (SeenLogview E M).
Proof. apply monPred_persistent, _. Qed.
#[global] Instance SeenLogview_empty_objective E :
  Objective (SeenLogview E ∅).
Proof. intros ??. iPureIntro. intros _. apply set_Forall_empty. Qed.

(* A proof that one has observed the event [eV], which means that one has
  observed its physical view [eV.(ge_view)], and that physical view in turn has
  observed the logical view [eV.(ge_lview)], as required by [SyncLogview]. *)
Definition SyncEvent E eid eV : vProp :=
  ⌜ E !! eid = Some eV ⌝ ∗
  @{eV.(ge_view).(dv_comm)} SyncLogview E eV.(ge_lview) ∗
  ⊒eV.(ge_view).(dv_comm).

#[global] Instance SyncEvent_persistent E eid eV :
  Persistent (SyncEvent E eid eV) := _.
#[global] Instance SyncEvent_timeless E eid eV :
  Timeless (SyncEvent E eid eV) := _.

(* SeenEvent *)
Definition SeenEvent E eid eV : vProp :=
  ⌜ E !! eid = Some eV ⌝ ∗
  @{eV.(ge_view).(dv_comm)} SeenLogview E eV.(ge_lview) ∗
  ⊒eV.(ge_view).(dv_comm).

#[global] Instance SeenEvent_persistent E eid eV :
  Persistent (SeenEvent E eid eV) := _.
#[global] Instance SeenEvent_timeless E eid eV :
  Timeless (SeenEvent E eid eV) := _.

(* Properties *)
Lemma SeenLogview_union E M1 M2 :
  SeenLogview E M1 -∗ SeenLogview E M2 -∗ SeenLogview E (M1 ∪ M2).
Proof.
  constructor => ?. iIntros "P1" (V ->). iDestruct "P1" as %P1. iPureIntro.
  by apply seen_logview_union.
Qed.

Definition SeenLogview_union' E M1 M2 :=
  bi.wand_elim_l' _ _ _ (SeenLogview_union E M1 M2).

Lemma SeenLogview_unfold E M :
  SeenLogview E M ⊣⊢
    ∀ e, ⌜ e ∈ M ⌝ → ∃ eV, ⌜ E !! e = Some eV ⌝ ∧ ⊒ eV.(ge_view).(dv_comm).
Proof.
  constructor => ?. iSplit.
  - iIntros "PV" (e V -> Ine). iDestruct "PV" as %PV.
    specialize (PV e Ine) as (eV & ? & ?).
    iPureIntro. by exists eV.
  - iIntros "PV" (e InV).
    iDestruct ("PV" $! e InV) as (eV) "[% %]".
    iPureIntro. by exists eV.
Qed.

Lemma SeenLogview_closed E M :
  SeenLogview E M ⊢ ⌜ set_in_bound M E ⌝.
Proof.
  rewrite SeenLogview_unfold.
  iIntros "SL" (e InM). iDestruct ("SL" $! _ InM) as (eV EqeV) "_".
  iPureIntro. by eexists.
Qed.

Lemma SeenLogview_downclosed E M M' :
  M' ⊆ M →
  SeenLogview E M ⊢ SeenLogview E M'.
Proof.
  rewrite 2!SeenLogview_unfold => SubM'.
  iIntros "SL" (e InM'). iApply "SL". iPureIntro. by apply SubM'.
Qed.

Lemma SeenLogview_singleton E e eV :
  E !! e = Some eV →
  ⊒eV.(ge_view).(dv_comm) ⊢ SeenLogview E {[e]}.
Proof.
  rewrite SeenLogview_unfold.
  iIntros (Eqe) "sV". iIntros (e'). rewrite elem_of_singleton. iIntros (->).
  iExists eV. by iFrame.
Qed.

Lemma SeenLogview_singleton_insert E eV :
  ⊒eV.(ge_view).(dv_comm) ⊢ SeenLogview (E ++ [eV]) {[length E]}.
Proof. apply SeenLogview_singleton. by rewrite lookup_app_1_eq. Qed.

Lemma SeenLogview_insert E M eV :
  SeenLogview E M -∗
  ⊒eV.(ge_view).(dv_comm) -∗
  SeenLogview (E ++ [eV]) ({[length E]} ∪ M).
Proof.
  iIntros "SL sV". rewrite -SeenLogview_union'. iSplitL "sV".
  - iApply (SeenLogview_singleton_insert with "sV").
  - iApply (SeenLogview_map_mono with "SL"); [by eexists|done].
Qed.

Lemma SeenLogview_insert' E M eV :
  SeenLogview E M ∗ ⊒eV.(ge_view).(dv_comm)
  ⊢ SeenLogview (E ++ [eV]) ({[length E]} ∪ M).
Proof. iIntros "[H1 H2]". iApply (SeenLogview_insert with "H1 H2"). Qed.

Lemma SeenLogview_empty E : ⊢ SeenLogview E ∅.
Proof. rewrite SeenLogview_unfold. by iIntros (??). Qed.

Lemma SeenEvent_mono E E' eid eV :
  E ⊑ E' → SeenEvent E eid eV -∗ SeenEvent E' eid eV.
Proof.
  iIntros (Sub) "(% & At & $)". erewrite SeenLogview_map_mono; eauto. iFrame.
  iPureIntro. by eapply prefix_lookup_Some.
Qed.

(** SyncLogview *)
Lemma sync_logview_seen_logview E M V :
  sync_logview E M V → seen_logview E M V.
Proof. intros SY e Ine%SY. naive_solver. Qed.

Lemma SyncLogview_SeenLogview E M :
  SyncLogview E M ⊢ SeenLogview E M.
Proof. constructor => ?. iPureIntro. by apply sync_logview_seen_logview. Qed.

Lemma SyncLogview_union E M1 M2 :
  SyncLogview E M1 -∗ SyncLogview E M2 -∗ SyncLogview E (M1 ∪ M2).
Proof.
  constructor => ?. iIntros "P1" (V ->). iDestruct "P1" as %P1. iPureIntro.
  by apply sync_logview_union.
Qed.

Definition SyncLogview_union' E M1 M2 :=
  bi.wand_elim_l' _ _ _ (SyncLogview_union E M1 M2).

Lemma SyncLogview_unfold E M :
  SyncLogview E M ⊣⊢
    ∀ e, ⌜ e ∈ M ⌝ →
    ∃ eV, ⌜ E !! e = Some eV ∧ eV.(ge_lview) ⊑ M ⌝ ∧ ⊒ eV.(ge_view).(dv_comm).
Proof.
  constructor => ?. iSplit.
  - iIntros "PV" (e V -> Ine). iDestruct "PV" as %PV.
    specialize (PV e Ine) as (eV & ? & ? & ?).
    iPureIntro. by exists eV.
  - iIntros "PV" (e InV).
    iDestruct ("PV" $! e InV) as (eV) "[[% %] %]".
    iPureIntro. by exists eV.
Qed.

Lemma SyncLogview_closed E M :
  SyncLogview E M ⊢ ⌜ set_in_bound M E ⌝.
Proof.
  rewrite SyncLogview_unfold.
  iIntros "SL" (e InM). iDestruct ("SL" $! _ InM) as (eV [EqeV _]) "_".
  iPureIntro. by eexists.
Qed.

Lemma SyncLogview_empty E : ⊢ SyncLogview E ∅.
Proof. rewrite SyncLogview_unfold. by iIntros (??). Qed.

Lemma SyncEvent_mono E E' eid eV :
  E ⊑ E' → SyncEvent E eid eV -∗ SyncEvent E' eid eV.
Proof.
  iIntros (Sub) "(% & At & $)". erewrite SyncLogview_map_mono; eauto. iFrame.
  iPureIntro. by eapply prefix_lookup_Some.
Qed.

End logview.
