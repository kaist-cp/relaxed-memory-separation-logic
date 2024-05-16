From iris.algebra Require Import auth gmap.
From iris.algebra Require Import lib.mono_list.
From iris.bi Require Import fractional.
From iris.proofmode Require Import tactics.
From iris.base_logic.lib Require Import own.

From gpfsl.base_logic Require Import vprop.
From gpfsl.examples.event Require Import event ghost.
From gpfsl.examples.graph Require Import ghost.
From gpfsl.examples.history Require Import history.

Require Import iris.prelude.options.

(** CMRA for history *)
Notation historyR := elistR.

Definition ghost_history_master {A} f E : historyR A :=
  ●ML{#f} (E : listO (leibnizO _)).
Definition ghost_history_snap {A} E : historyR A :=
  ◯ML (E : listO (leibnizO _)).

Notation history_gmaster γg f E := (own γg (ghost_history_master f E)).
Notation history_gsnap  γg E := (own γg (ghost_history_snap E)).
Notation history_gsnapv γg E := (⎡ history_gsnap γg E ⎤%I : vProp _).

Section Graphs.
Context {eventT : Type}.
Context {Σ : gFunctors} `{egRG : inG Σ (historyR eventT)}.
Notation history := (history eventT).
Notation iProp := (iProp Σ).
Notation vProp := (vProp Σ).

Implicit Types (E : history) (M : logView).

Definition history_master γg q E : vProp :=
  ⎡ history_gmaster γg q E ⎤ ∗
  ⌜ history_wf E ⌝.

Definition history_snap γg E M : vProp :=
  history_gsnapv γg E ∗ SeenLogview E M.

#[global] Instance history_gmaster_timeless γg q E :
  Timeless (history_gmaster γg q E) := _.

#[global] Instance history_master_timeless γg f E :
  Timeless (history_master γg f E) := _.
#[global] Instance history_master_objective γg f E :
  Objective (history_master γg f E) := _.

#[global] Instance history_snap_timelesss γg E M :
  Timeless (history_snap γg E M) := _.
#[global] Instance history_snap_persistent γg E M :
  Persistent (history_snap γg E M) := _.

#[global] Instance history_snap_empty_objective γg E :
  Objective (history_snap γg E ∅) := _.

(** Ghost properties *)

(* Updates *)
Lemma ghost_history_update γ E E' (Le: E ⊑ E') :
  history_gmaster γ 1 E ==∗ history_gmaster γ 1 E'.
Proof. by apply own_update, mono_list_update. Qed.

Lemma ghost_history_master_snap γ f E :
  history_gmaster γ f E ⊢ history_gsnap γ E.
Proof. apply own_mono, mono_list_included. Qed.

Lemma ghost_history_snap_sub γ E G' :
  E ⊑ G' →
  history_gsnap γ G' -∗ history_gsnap γ E.
Proof. intros Le. apply own_mono, mono_list_lb_mono, Le. Qed.

(* Alloc *)
Lemma ghost_history_alloc E :
  ⊢ |==> ∃ γ, history_gmaster γ 1 E.
Proof. apply own_alloc, mono_list_auth_valid. Qed.

(* Agreements *)
Lemma ghost_history_master_agree γ f1 E1 f2 E2  :
  history_gmaster γ f1 E1 -∗ history_gmaster γ f2 E2 -∗ ⌜E1 = E2⌝.
Proof.
  iIntros "o1 o2".
  by iCombine "o1 o2" gives %[_ ?%leibniz_equiv]%mono_list_auth_dfrac_op_valid.
Qed.

Lemma ghost_history_master_snap_included γg f E E' :
  history_gmaster γg f E -∗ history_gsnap γg E' -∗ ⌜E' ⊑ E⌝.
Proof.
  iIntros "oM oS".
  by iCombine "oM oS" gives %[_ ?]%mono_list_both_dfrac_valid_L.
Qed.

(** Graph's Master-Snapshot properties *)
#[global] Instance history_master_fractional γg E :
  Fractional (λ q, history_master γg q E).
Proof.
  intros p q. rewrite /history_master. iSplit.
  - iIntros "[E %]". iFrame "%".
    rewrite -embed_sep -own_op. by rewrite -mono_list_auth_dfrac_op.
  - iIntros "[[E1 _] [E2 $]]". iCombine "E1 E2" as "$".
Qed.

#[global] Instance history_master_asfractional γg E q :
  AsFractional (history_master γg q E) (λ q, history_master γg q E) q.
Proof. constructor; [done|apply _]. Qed.

Lemma history_master_update γ E E' :
  E ⊑ E' → history_wf E' →
  history_master γ 1 E ==∗
  history_master γ 1 E' ∗ history_gsnapv γ E'.
Proof.
  iIntros (SE EC) "[EM %]".
  iMod (ghost_history_update with "EM") as "EM"; [exact SE|].
  iDestruct (ghost_history_master_snap with "EM") as "#$". by iFrame "EM".
Qed.

Lemma history_master_alloc_empty :
  ⊢ |==> ∃ γ, history_master γ 1 [] ∗ history_gsnapv γ [].
Proof.
  iMod (ghost_history_alloc []) as (γ) "Em".
  iIntros "!>". iExists γ. iDestruct (ghost_history_master_snap with "Em") as "#$".
  iFrame. by iPureIntro.
Qed.

Lemma history_master_wf γg f E :
  history_master γg f E -∗ ⌜ history_wf E ⌝.
Proof. by iIntros "[? %]". Qed.

Lemma history_master_agree γg f1 E1 f2 E2 :
  history_master γg f1 E1 -∗ history_master γg f2 E2 -∗
  ⌜ E1 = E2 ⌝.
Proof.
  iIntros "[E1 _] [E2 _]".
  by iDestruct (ghost_history_master_agree with "E1 E2") as %?.
Qed.

Lemma history_master_snap γg f E :
  history_master γg f E ⊢  history_snap γg E ∅.
Proof.
  iIntros "[E %EGc]".
  iDestruct (ghost_history_master_snap with "E") as "$".
  by rewrite -SeenLogview_empty.
Qed.

Lemma history_master_snap_included' γg f E E' M V V' :
  @{V} history_master γg f E -∗ @{V'} history_snap γg E' M -∗
  ⌜ E' ⊑ E ⌝.
Proof.
  iIntros "[E _] [Es _]". rewrite !view_at_objective_iff.
  by iDestruct (ghost_history_master_snap_included with "E Es") as %?.
Qed.

Lemma history_master_snap_included γg q E E' M :
  history_master γg q E -∗ history_snap γg E' M -∗ ⌜ E' ⊑ E ⌝.
Proof. by apply view_at_wand_lr, history_master_snap_included'. Qed.
Lemma history_master_snap_included_2 γg q E E' M V' :
  history_master γg q E -∗ @{V'} history_snap γg E' M -∗ ⌜ E' ⊑ E ⌝.
Proof. by apply view_at_wand_l, history_master_snap_included'. Qed.

Lemma history_snap_mono γg E M E' M'
  (In1: E' ⊑ E) :
  history_snap γg E M -∗ history_snap γg E' M' -∗
  history_snap γg E M'.
Proof.
  iIntros "[$ PS1] [_ PS2]".
  by iApply (SeenLogview_map_mono with "PS2").
Qed.

Lemma history_snap_downclosed γg E M M' :
  M' ⊆ M → history_snap γg E M ⊢ history_snap γg E M'.
Proof. iIntros (SubM') "[$ SL]". by iApply SeenLogview_downclosed. Qed.

Lemma history_snap_union γg E M M' :
  history_snap γg E M -∗ history_snap γg E M' -∗ history_snap γg E (M ∪ M').
Proof. iIntros "[$ S1] [E2 S2]". rewrite -SeenLogview_union'. by iFrame. Qed.
Lemma history_snap_union' γg E M M' :
  history_snap γg E M ∗ history_snap γg E M' ⊢ history_snap γg E (M ∪ M').
Proof. iIntros "[S1 S2]". iApply (history_snap_union with "S1 S2"). Qed.

Lemma history_snap_upgrade γg q E' E M :
  history_master γg q E' -∗ history_snap γg E M -∗ history_snap γg E' M.
Proof.
  iIntros "Em Es".
  iDestruct (history_master_snap_included with "Em Es") as %SubE.
  iDestruct (history_master_snap with "Em") as "E0".
  by iApply (history_snap_mono with "E0 Es").
Qed.

Lemma history_snap_lookup γg E M e dV :
  ge_view <$> E !! e = Some dV → e ∈ M →
  history_snap γg E M -∗ ⊒(dV.(dv_comm)).
Proof.
  intros Eqe Inm. constructor => V'' /=.
  iIntros "[_ %InM']". iPureIntro.
  specialize (InM' _  Inm) as ([e' V'] & Eq' & SubV'). simpl in SubV'.
  rewrite Eq' /= in Eqe. by simplify_eq.
Qed.

(* Stupid lemma done at iRC11 level *)
Lemma history_snap_empty γg :
  history_gsnapv γg [] -∗ history_snap γg [] ∅.
Proof. iIntros "$". by rewrite -SeenLogview_empty. Qed.

End Graphs.

#[global] Typeclasses Opaque history_master graph_gmaster.
