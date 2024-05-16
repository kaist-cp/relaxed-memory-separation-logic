From iris.algebra Require Import gmap.

From gpfsl.lang Require Import lang.
From gpfsl.examples.event Require Import event.

Require Import iris.prelude.options.

Definition functional_pair_1 `{Countable A} (Ps : gset (A * A)) : Prop
  := ∀ p1 p2, p1 ∈ Ps → p2 ∈ Ps → p1.1 = p2.1 → p1.2 = p2.2.
Definition functional_pair_2 `{Countable A} (Ps : gset (A * A)) : Prop
  := ∀ p1 p2, p1 ∈ Ps → p2 ∈ Ps → p1.2 = p2.2 → p1.1 = p2.1.
Definition functional_pair `{Countable A} (Ps : gset (A * A)) : Prop :=
  functional_pair_1 Ps ∧ functional_pair_2 Ps.

Definition symmetric_pair `{Countable A} (Ps : gset (A * A)) : Prop
  := ∀ a1 a2, (a1, a2) ∈ Ps ↔ (a2, a1) ∈ Ps.

Definition irreflexive_pair `{Countable A} (Ps : gset (A * A)) : Prop
  := ∀ a, (a, a) ∉ Ps.

(* ∀ p, p ∈ Ps → p.1 ∈ S ∧ p.2 ∈ S. *)
Definition pair_in_set `{Countable A} (Ps : gset (A * A)) (S : gset A) : Prop
  := set_Forall (λ p, p.1 ∈ S ∧ p.2 ∈ S) Ps.

Definition pair_in_bound (Ps : gset (event_id * event_id)) (n : event_id) : Prop
  := set_Forall (λ p, p.1 < n ∧ p.2 < n)%nat Ps.

(* We don't need so ⊆ (po ∪ com)+ because we don't have po. The view inclusion
  relation includes po, among other relations. *)
Record graph {A : Type} := mkGraph {
  Es  : event_list A;
  com : gset (event_id * event_id) ;
  so  : gset (event_id * event_id) ;
  gcons_com_included_dec : bool_decide (pair_in_bound com (length Es));
  gcons_so_included_dec  : bool_decide (pair_in_bound so (length Es)) ;
}.

Global Arguments graph : clear implicits.
Global Arguments mkGraph {_} _ _ _ _ _.

Section defs.
Context {eventT : Type}.
Notation graph := (graph eventT).
Notation graph_event := (graph_event eventT).
Notation event_list   := (event_list eventT).

Implicit Types (G: graph) (E: event_list) (V: view).

Lemma gcons_com_included G : pair_in_bound G.(com) (length G.(Es)).
Proof. eapply bool_decide_unpack, gcons_com_included_dec. Qed.
Lemma gcons_so_included G : pair_in_bound G.(so) (length G.(Es)).
Proof. eapply bool_decide_unpack, gcons_so_included_dec. Qed.

Lemma graph_eq G1 G2 :
  G1.(Es) = G2.(Es) → G1.(com) = G2.(com) → G1.(so) = G2.(so) → G1 = G2.
Proof. destruct G1, G2=>/= ???. subst. f_equal; apply proof_irrel. Qed.

Global Program Instance empty_graph : Empty graph := mkGraph [] ∅ ∅ _ _.
Solve Obligations with intros; eapply bool_decide_pack; intros ??; set_solver.
#[global] Instance graphInhabited : Inhabited graph := populate empty.

Record graph_le G1 G2 :=
  mkGraphSqSubsetEq {
    graph_sqsubseteq_E  : G1.(Es) ⊑ G2.(Es) ;
    graph_sqsubseteq_com: G1.(com) ⊆ G2.(com) ;
    graph_sqsubseteq_so : G1.(so) ⊆ G2.(so) ;
  }.

#[global] Instance graph_sqsubseteq : SqSubsetEq graph := graph_le.
#[global] Instance graph_sqsubseteq_po : PartialOrder ((⊑) : SqSubsetEq graph).
Proof.
  constructor; [constructor|]; [done|..].
  - intros [][][] [??] [??]; constructor; simpl in *; by etrans.
  - intros [][][][]. apply graph_eq; by apply : (anti_symm (⊑)).
Qed.

(** * Event graph basic consistency *)
Record eventgraph_consistent G :=
  mkEventGraphConsistent {
    egcons_so:
      ∀ e1 e2, (e1, e2) ∈ G.(so) → ∃ eV1 eV2,
        G.(Es) !! e1 = Some eV1 ∧ G.(Es) !! e2 = Some eV2 ∧ eV1 ⊑ eV2 ;
    (* logview includes the event itself *)
    egcons_logview_event :
      ∀ e eV, G.(Es) !! e = Some eV → e ∈ eV.(ge_lview) ;
    (* logview is closed w.r.t E *)
    egcons_logview_closed :
      ∀ e eV, G.(Es) !! e = Some eV → set_in_bound eV.(ge_lview) G.(Es) ;
  }.

(** * Several basic consistency conditions *)

(** * Our two extra relations on the graph events are xo and eco.
  - xo : execution order, in which the atomic commits are applied.
  - eco : extended communication order, which includes the real constraint on
    ordering of operations. Intuitively, any actual ordering must be consistent
    with hb and all mo's of all physical locations. The mo's of the
    physical locations include, for example, the ordering of CAS operations.
    Succintly, hb ∪ mo ⊆ eco.

  xo is encoded as the timestamp order of the history of events : (e1 ≤ e2)%nat.
  Meanwhile, eco is encoded as the logical view inclusion: e1 ∈ eV2.(ge_lview). *)
(* TODO: use co as eco? More theory on eco. *)

(** eco must agree with xo : eco ⊆ xo.
  This prevents cycles in eco, which doesn't work for exchanger.
  See also "Benign Synchronisation Cycles" in the Yacovet (POPL'19) paper. *)
Definition graph_xo_eco E : Prop :=
  ∀ e1 e2 eV2, E !! e2 = Some eV2 → e1 ∈ eV2.(ge_lview) → (e1 ≤ e2)%nat
  (* ∧ eV1.(ge_lview) ⊑ eV2.(ge_lview) *)
  (*   ^^ this doesn't work because we are not rel-acq (have relaxed ops). *)
  .

Definition graph_event_is_releasing E (P : eventT → Prop) :=
  ∀ e eV, E !! e = Some eV → P eV.(ge_event) →
    eV.(ge_view).(dv_comm) ⊑ eV.(ge_view).(dv_wrt).

Definition graph_event_is_acquiring E (P : eventT → Prop) :=
  ∀ e eV, E !! e = Some eV → P eV.(ge_event) →
    eV.(ge_view).(dv_wrt) ⊑ eV.(ge_view).(dv_comm).

Definition graph_event_is_writing E (P : eventT → Prop) :=
  ∀ e eV, E !! e = Some eV → P eV.(ge_event) →
    eV.(ge_view).(dv_in) ≠ eV.(ge_view).(dv_comm).

Definition graph_event_is_relacq E (P : eventT → Prop) :=
  ∀ e eV, E !! e = Some eV → P eV.(ge_event) →
    eV.(ge_view).(dv_comm) = eV.(ge_view).(dv_wrt).

Lemma eventgraph_consistent_empty : eventgraph_consistent ∅.
Proof. done. Qed.

Lemma gcons_not_in_so_l G e : (length G.(Es), e) ∉ G.(so).
Proof. intros [Lt _]%gcons_so_included. simpl in Lt. lia. Qed.
Lemma gcons_not_in_so_r G e : (e, length G.(Es)) ∉ G.(so).
Proof. intros [_ Lt]%gcons_so_included. simpl in Lt. lia. Qed.
Lemma gcons_not_in_com_l G e : (length G.(Es), e) ∉ G.(com).
Proof. intros [Lt _]%gcons_com_included. simpl in Lt. lia. Qed.
Lemma gcons_not_in_com_r G e : (e, length G.(Es)) ∉ G.(com).
Proof. intros [_ Lt]%gcons_com_included. simpl in Lt. lia. Qed.

Lemma graph_event_is_relacq_releasing E (P Q : eventT → Prop) :
  (∀ e, P e → Q e) →
  graph_event_is_relacq E Q → graph_event_is_releasing E P.
Proof.
  intros PQ RA e eV Eqe Pe%PQ. by rewrite (RA _ _ Eqe Pe).
Qed.
Lemma graph_event_is_relacq_releasing_True E (P : eventT → Prop) :
  graph_event_is_relacq E (λ _, True) → graph_event_is_releasing E P.
Proof. by apply graph_event_is_relacq_releasing. Qed.

Lemma graph_event_is_relacq_acquiring E (P Q : eventT → Prop) :
  (∀ e, P e → Q e) →
  graph_event_is_relacq E Q → graph_event_is_acquiring E P.
Proof.
  intros PQ RA e eV Eqe Pe%PQ. by rewrite (RA _ _ Eqe Pe).
Qed.
Lemma graph_event_is_relacq_acquiring_True E (P : eventT → Prop) :
  graph_event_is_relacq E (λ _, True) → graph_event_is_acquiring E P.
Proof. by apply graph_event_is_relacq_acquiring. Qed.
End defs.
