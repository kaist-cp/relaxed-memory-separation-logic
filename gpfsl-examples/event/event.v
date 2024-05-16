From iris.algebra Require Import gmap.

From gpfsl.lang Require Import lang.
From gpfsl.examples Require Export list_helper.

Require Import iris.prelude.options.

Definition event_id := nat.
Definition dummy_eid : event_id := O.

(** * The lattice of data structure views *)
Record dataView : Type :=
  mkDView {
    dv_in : view;    (* the starting view of the caller *)
    dv_comm : view;  (* the commiting view of the caller *)
    dv_wrt : view;    (* the actual view of the write event *)
    dv_in_comm_dec : bool_decide (dv_in ⊑ dv_comm);
  }.

Lemma dv_in_com dV : dV.(dv_in) ⊑ dV.(dv_comm).
Proof. eapply bool_decide_unpack, dv_in_comm_dec. Qed.

Lemma dataView_eq dV1 dV2 :
  dV1.(dv_in) = dV2.(dv_in) → dV1.(dv_comm) = dV2.(dv_comm) → dV1.(dv_wrt) = dV2.(dv_wrt) →
  dV1 = dV2.
Proof. destruct dV1, dV2=>/= ???. subst. f_equal; apply proof_irrel. Qed.

Global Program Instance empty_dataView : Empty dataView := mkDView ∅ ∅ ∅ _.
Solve Obligations with eapply bool_decide_pack; set_solver.

#[global] Instance dataViewInhabited : Inhabited dataView := populate empty.

Record dview_le dV1 dV2 :=
  mkDViewSqSubsetEq {
    dview_sqsubseteq_in  : dV1.(dv_in) ⊑ dV2.(dv_in);
    dview_sqsubseteq_domm  : dV1.(dv_comm) ⊑ dV2.(dv_comm);
    dview_sqsubseteq_wrt  : dV1.(dv_wrt) ⊑ dV2.(dv_wrt);
  }.

#[global] Instance dview_sqsubseteq : SqSubsetEq dataView := dview_le.
#[global] Instance dview_sqsubseteq_po : PartialOrder ((⊑) : SqSubsetEq dataView).
Proof.
  split.
  - split; [by split|] => ??? [???] [???]. split; simpl; by etrans.
  - intros [][][][]. apply dataView_eq; simpl; by apply: (anti_symm (⊑)).
Qed.

Program Definition dview_join dV1 dV2 := {|
  dv_in := dV1.(dv_in) ⊔ dV2.(dv_in) ;
  dv_comm := dV1.(dv_comm) ⊔ dV2.(dv_comm) ;
  dv_wrt := dV1.(dv_wrt) ⊔ dV2.(dv_wrt) ;
|}.
Next Obligation. intros. apply bool_decide_pack. by rewrite 2!dv_in_com. Qed.

Program Definition dview_meet dV1 dV2 := {|
  dv_in := dV1.(dv_in) ⊓ dV2.(dv_in) ;
  dv_comm := dV1.(dv_comm) ⊓ dV2.(dv_comm) ;
  dv_wrt := dV1.(dv_wrt) ⊓ dV2.(dv_wrt) ;
|}.
Next Obligation. intros. apply bool_decide_pack. by rewrite 2!dv_in_com. Qed.

Program Canonical Structure dview_Lat :=
  Make_Lat dataView (=) _ dview_join dview_meet
            _ _ _ _ _ _ _ _ _ _ _ _ _.
Next Obligation. intros ??. split; simpl; solve_lat. Qed.
Next Obligation. intros ??. split; simpl; solve_lat. Qed.
Next Obligation. intros ??? [][]. split; simpl; solve_lat. Qed.
Next Obligation. intros ??. split; simpl; solve_lat. Qed.
Next Obligation. intros ??. split; simpl; solve_lat. Qed.
Next Obligation. intros ??? [][]. split; simpl; solve_lat. Qed.

#[global] Instance dataView_bot : @LatBottom dview_Lat empty_dataView.
Proof. intros; repeat split; apply empty_subseteq. Qed.

(** * A logical view *)
Definition logView := gset event_id.

Definition set_in_bound {A} (M: gset nat) (E : list A)  :=
  set_Forall (λ e, is_Some (E !! e)) M.

(** * A graph event *)
Record graph_event (eventT : Type) :=
  mkGraphEvent {
    ge_event : eventT;
    ge_view : dataView;
    ge_lview : logView;
  }.
Arguments mkGraphEvent {_} _ _ _.
Arguments ge_event {_} _.
Arguments ge_view {_} _.
Arguments ge_lview {_} _.

Notation event_list eventT := (list (graph_event eventT))%type.

#[global] Instance graph_event_Inhabited eventT (H : Inhabited eventT) : Inhabited (graph_event eventT) :=
  match H with
  | populate x => populate (mkGraphEvent x empty ∅)
  end.

(** * Event maps *)
Section defs.
Context {eventT : Type}.
Notation graph_event := (graph_event eventT).
Notation event_list   := (event_list eventT).

Implicit Types (E : event_list).

Record graph_event_le (ge1 ge2 : graph_event) :=
  mkGraphEventLe {
    (* physically, only the in view of ge1 is included in the commit view of ge2 *)
    ge_le_view : ge1.(ge_view).(dv_in) ⊑ ge2.(ge_view).(dv_comm) ;
    ge_le_lview : ge1.(ge_lview) ⊆ ge2.(ge_lview);
  }.
#[global] Instance graph_event_le_sqsubseteq : SqSubsetEq graph_event
  := graph_event_le.

(** * Logview observations *)
Definition sync_logview E (lV: logView) (V: view) : Prop :=
  set_Forall (λ eid, ∃ eV, E !! eid = Some eV ∧
                      eV.(ge_lview) ⊑ lV ∧ eV.(ge_view).(dv_comm) ⊑ V) lV.

Definition seen_logview E (lV: logView) (V: view) : Prop :=
  set_Forall (λ eid, ∃ eV, E !! eid = Some eV ∧ eV.(ge_view).(dv_comm) ⊑ V) lV.
End defs.


Lemma set_in_bound_mono' {A} (M M' : gset nat) (E E' : list A):
  M' ⊆ M → E ⊑ E' → set_in_bound M E → set_in_bound M' E'.
Proof. intros LeM LeE HE e []%LeM%HE. eexists. by eapply prefix_lookup_Some. Qed.
Lemma set_in_bound_mono {A} (M: gset nat) (E E' : list A):
  E ⊑ E' → set_in_bound M E → set_in_bound M E'.
Proof. by apply set_in_bound_mono'. Qed.
Lemma set_in_bound_union {A} (M M' : gset nat) (E : list A):
  set_in_bound M E → set_in_bound M' E → set_in_bound (M ∪ M') E.
Proof. intros H1 H2 ? [?%H1|?%H2]%elem_of_union; done. Qed.

Lemma sync_logview_view_mono {A} (E : event_list A) lV V1 V2 :
  V1 ⊑ V2 → sync_logview E lV V1 → sync_logview E lV V2.
Proof.
  move => ? LV e /LV [eV [?[??]]]. exists eV. repeat split; [done..|solve_lat].
Qed.

Lemma sync_logview_mono {A} (E E' : event_list A) lV V
  (SUB: E' ⊑ E) :
  sync_logview E' lV V → sync_logview E lV V.
Proof.
  intros LV e In.
  destruct (LV _ In) as (eV & EqeV & ? & ?).
  exists eV. repeat split; [|done..].
  by eapply prefix_lookup_Some.
Qed.

Lemma sync_logview_union {A} (E : event_list A) lV1 lV2 V :
  sync_logview E lV1 V → sync_logview E lV2 V →
  sync_logview E (lV1 ∪ lV2) V.
Proof. move => LV1 LV2 e /elem_of_union [/LV1|/LV2]; set_solver. Qed.

Lemma seen_logview_view_mono {A} (E : event_list A) lV V1 V2 :
  V1 ⊑ V2 → seen_logview E lV V1 → seen_logview E lV V2.
Proof.
  move => ? LV e /LV [eV [??]]. exists eV. repeat split; [done..|solve_lat].
Qed.

Lemma seen_logview_mono {A} (E E' : event_list A) lV V
  (SUB: E' ⊑ E) :
  seen_logview E' lV V → seen_logview E lV V.
Proof.
  intros LV e In.
  destruct (LV _ In) as (eV & EqeV & ?).
  exists eV. repeat split; [|done..].
  by eapply prefix_lookup_Some.
Qed.

Lemma seen_logview_union {A} (E : event_list A) lV1 lV2 V :
  seen_logview E lV1 V → seen_logview E lV2 V →
  seen_logview E (lV1 ∪ lV2) V.
Proof. move => LV1 LV2 e /elem_of_union [/LV1|/LV2]; set_solver. Qed.
