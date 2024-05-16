From iris.algebra Require Import auth gmap.
From iris.algebra Require Import lib.mono_list.
From iris.bi Require Import fractional.
From iris.proofmode Require Import tactics.
From iris.base_logic.lib Require Import own.

From gpfsl.base_logic Require Import vprop.
From gpfsl.examples.event Require Import event ghost.
From gpfsl.algebra Require Import lat_auth.
From gpfsl.examples.graph Require Import graph.

Require Import iris.prelude.options.

(** CMRA for events lists *)
Definition elistR (eventT : Type) := mono_listR (leibnizO (graph_event eventT)).

(** CMRA for graphs *)

Definition relations_Lat :=
  prod_Lat (gset_Lat (event_id * event_id)) (gset_Lat (event_id * event_id)).
Definition relationsR := lat_authR relations_Lat.
Definition graphR (eventT : Type) := prodR (elistR eventT) relationsR.

Definition ghost_graph_master {A} q (G : graph A) : graphR A :=
  ( ●ML{#q} (G.(Es) : listO (leibnizO _)),
    ●L{#q} (G.(so), G.(com))).

Definition ghost_graph_snap {A} (G : graph A) : graphR A :=
  ( ◯ML (G.(Es) : listO (leibnizO _)),
    ◯L (G.(so), G.(com))).


Section Graphs.
Context {eventT : Type}.
Context {Σ : gFunctors} `{egRG : inG Σ (graphR eventT)}.
Notation event_list := (event_list eventT).
Notation graph := (graph eventT).
Notation iProp := (iProp Σ).
Notation vProp := (vProp Σ).

Implicit Types (G : graph) (E : event_list) (M : logView).

Definition graph_gmaster γg q G := own γg (ghost_graph_master q G).
Definition graph_gmasterv γg q G : vProp := ⎡ graph_gmaster γg q G ⎤.
Definition graph_gsnap  γg G := own γg (ghost_graph_snap G).
Definition graph_gsnapv γg G : vProp := ⎡ graph_gsnap γg G ⎤.

Definition graph_master γg q G : vProp :=
  graph_gmasterv γg q G  ∗ ⌜ eventgraph_consistent G ⌝.

Definition graph_snap γg G M : vProp :=
  graph_gsnapv γg G ∗ SeenLogview G.(Es) M.

#[global] Instance graph_gmaster_timeless γg q G :
  Timeless (graph_gmaster γg q G) := _.

#[global] Instance graph_master_timeless γg q G :
  Timeless (graph_master γg q G) := _.
#[global] Instance graph_master_objective γg q G :
  Objective (graph_master γg q G) := _.

#[global] Instance graph_snap_timelesss γg G M :
  Timeless (graph_snap γg G M) := _.
#[global] Instance graph_snap_persistent γg G M :
  Persistent (graph_snap γg G M) := _.

#[global] Instance graph_snap_empty_objective γg G :
  Objective (graph_snap γg G ∅) := _.

(** Ghost properties *)

(* Updates *)
Lemma ghost_graph_update γ G G' (Le: G ⊑ G') :
  graph_gmaster γ 1 G ==∗ graph_gmaster γ 1 G'.
Proof.
  apply own_update, prod_update; simpl.
  - by apply mono_list_update, Le.
  - apply lat_auth_update. split; apply Le.
Qed.

Lemma ghost_graph_master_snap γ q G :
  graph_gmaster γ q G -∗ graph_gsnap γ G.
Proof.
  apply own_mono, prod_included. split.
  - apply mono_list_included.
  - apply lat_auth_included.
Qed.

Lemma ghost_graph_snap_sub γ G G' :
  G ⊑ G' →
  graph_gsnap γ G' -∗ graph_gsnap γ G.
Proof.
  intros Le. apply own_mono, prod_included. split.
  - apply mono_list_lb_mono, Le.
  - apply lat_lb_mono. split; apply Le.
Qed.

(* Alloc *)
Lemma ghost_graph_alloc G :
  ⊢ |==> ∃ γ, graph_gmaster γ 1 G.
Proof.
  apply own_alloc. split.
  - apply mono_list_auth_valid.
  - apply lat_auth_valid.
Qed.

(* Agreements *)
Lemma ghost_graph_master_agree γ q1 G1 q2 G2  :
  graph_gmaster γ q1 G1 -∗ graph_gmaster γ q2 G2 -∗ ⌜G1 = G2⌝.
Proof.
  iIntros "o1 o2".
  iCombine "o1 o2" gives
    %[[? ?]%mono_list_auth_dfrac_op_valid_L
      [? EqCo%leibniz_equiv_iff]%lat_auth_auth_valid].
  iPureIntro. simplify_eq.
  by apply graph_eq.
Qed.

Lemma ghost_graph_master_snap_included γg q G G' :
  graph_gmaster γg q G -∗ graph_gsnap γg G' -∗ ⌜ G' ⊑ G ⌝.
Proof.
  iIntros "oM oS".
  iCombine "oM oS" gives
    %[[? ?]%mono_list_both_dfrac_valid_L [? [??]]%lat_auth_both_valid].
  iPureIntro. by constructor.
Qed.

(** Graph's Master-Snapshot properties *)
#[global] Instance ghost_graph_master_fractional γg G :
  Fractional (λ q, graph_gmaster γg q G).
Proof.
  intros p q.
  rewrite {1}/graph_gmaster /ghost_graph_master -dfrac_op_own
          mono_list_auth_dfrac_op lat_auth_frac_op pair_op own_op. iSplit.
  - iIntros "[$ $]".
  - iIntros "[G1 G2]". iSplitL "G1"; iFrame.
Qed.
#[global] Instance ghost_graph_master_asfractional γg G q :
  AsFractional (graph_gmaster γg q G)
               (λ q, graph_gmaster γg q G) q.
Proof. constructor; [done|apply _]. Qed.

#[global] Instance ghost_graph_masterv_fractional γg G :
  Fractional (λ q, graph_gmasterv γg q G) | 0.
Proof.
  intros p q. rewrite -embed_sep. apply embed_proper, ghost_graph_master_fractional.
Qed.
#[global] Instance ghost_graph_masterv_asfractional γg G q :
  AsFractional (graph_gmasterv γg q G)
               (λ q, graph_gmasterv γg q G) q | 0.
Proof. constructor; [done|apply _]. Qed.

#[global] Typeclasses Opaque graph_gmaster.

#[global] Instance graph_master_fractional γg G :
  Fractional (λ q, graph_master γg q G).
Proof.
  intros p q. iSplit.
  - iIntros "[[$ $] #$]".
  - iIntros "[[G1 F1] [G2 $]]". iSplitL "G1"; iFrame.
Qed.

#[global] Instance graph_master_asfractional γg G q :
  AsFractional (graph_master γg q G) (λ q, graph_master γg q G) q.
Proof. constructor; [done|apply _]. Qed.

Lemma graph_master_update γ G G' :
  G ⊑ G' → eventgraph_consistent G' →
  graph_master γ 1 G ==∗
  graph_master γ 1 G' ∗ graph_gsnapv γ G'.
Proof.
  iIntros (SG EC) "[GM %]". iFrame (EC).
  iMod (ghost_graph_update with "GM") as "GM"; [exact SG|].
  iDestruct (ghost_graph_master_snap with "GM") as "#$". by iFrame "GM".
Qed.

Lemma graph_master_alloc_empty :
  ⊢ |==> ∃ γ, graph_master γ 1 ∅ ∗ graph_gsnapv γ ∅.
Proof.
  iMod (ghost_graph_alloc ∅) as (γ) "Gm".
  iIntros "!>". iExists γ. iDestruct (ghost_graph_master_snap with "Gm") as "#$".
  iFrame. by iPureIntro.
Qed.

Lemma graph_master_consistent γg q G :
  graph_master γg q G -∗ ⌜ eventgraph_consistent G ⌝.
Proof. by iIntros "[? %]". Qed.

Lemma graph_master_agree γg q1 G1 q2 G2 :
  graph_master γg q1 G1 -∗ graph_master γg q2 G2 -∗
  ⌜ G1 = G2 ⌝.
Proof.
  iIntros "[G1 _] [G2 _]".
  by iDestruct (ghost_graph_master_agree with "G1 G2") as %?.
Qed.

Lemma graph_master_snap γg q G :
  graph_master γg q G ⊢ graph_snap γg G ∅.
Proof.
  iIntros "[G %EGc]".
  iDestruct (ghost_graph_master_snap with "G") as "$".
  by rewrite -SeenLogview_empty.
Qed.

Lemma graph_master_snap_included' γg q G G' M V V' :
  @{V} graph_master γg q G -∗ @{V'} graph_snap γg G' M -∗
  ⌜ G' ⊑ G ⌝.
Proof.
  iIntros "[G _] [Gs _]". rewrite !view_at_objective_iff.
  by iDestruct (ghost_graph_master_snap_included with "G Gs") as %?.
Qed.

Lemma graph_master_snap_included γg q G G' M :
  graph_master γg q G -∗ graph_snap γg G' M -∗ ⌜ G' ⊑ G ⌝.
Proof. by apply view_at_wand_lr, graph_master_snap_included'. Qed.
Lemma graph_master_snap_included_2 γg q G G' M V' :
  graph_master γg q G -∗ @{V'} graph_snap γg G' M -∗ ⌜ G' ⊑ G ⌝.
Proof. by apply view_at_wand_l, graph_master_snap_included'. Qed.

Lemma graph_snap_mono γg G M G' M' :
  G' ⊑ G →
  graph_snap γg G M -∗ graph_snap γg G' M' -∗
  graph_snap γg G M'.
Proof.
  iIntros (SUB) "[G1 S1] [G2 S2]".
  iFrame "G1". iApply (SeenLogview_map_mono with "S2"); [apply SUB|done].
Qed.

Lemma graph_snap_downclosed γg G M M' :
  M' ⊆ M → graph_snap γg G M ⊢ graph_snap γg G M'.
Proof. intros. by apply bi.sep_mono_r, SeenLogview_downclosed. Qed.

Lemma graph_snap_union γg G M M' :
  graph_snap γg G M -∗ graph_snap γg G M' -∗ graph_snap γg G (M ∪ M').
Proof. iIntros "[$ S1] [G2 S2]". rewrite -SeenLogview_union'. by iFrame. Qed.
Lemma graph_snap_union' γg G M M' :
  graph_snap γg G M ∗ graph_snap γg G M' ⊢ graph_snap γg G (M ∪ M').
Proof. iIntros "[S1 S2]". iApply (graph_snap_union with "S1 S2"). Qed.

Lemma graph_snap_upgrade γg q G' G M :
  graph_master γg q G' -∗ graph_snap γg G M -∗ graph_snap γg G' M.
Proof.
  iIntros "Gm Gs".
  iDestruct (graph_master_snap_included with "Gm Gs") as %SubG.
  iDestruct (graph_master_snap with "Gm") as "G0".
  by iApply (graph_snap_mono with "G0 Gs").
Qed.

Lemma graph_snap_lookup γg G M e dV :
  ge_view <$> G.(Es) !! e = Some dV → e ∈ M →
  graph_snap γg G M -∗ ⊒(dV.(dv_comm)).
Proof.
  iIntros (Eqe Inm) "[? H]". rewrite SeenLogview_unfold.
  iDestruct ("H" with "[%//]") as (eV Eq') "S".
  rewrite Eq' /= in Eqe. inversion Eqe. iFrame.
Qed.

(* Stupid lemma done at iRC11 level *)
Lemma graph_snap_empty γg :
  graph_gsnapv γg ∅ ⊢ graph_snap γg ∅ ∅.
Proof. iIntros "$". by rewrite -SeenLogview_empty. Qed.

End Graphs.

#[global] Typeclasses Opaque graph_master graph_gmaster.
