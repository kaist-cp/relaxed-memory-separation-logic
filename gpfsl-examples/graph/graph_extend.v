From iris.algebra Require Import gmap.

From gpfsl.lang Require Import lang.
From gpfsl.examples.event Require Import event.
From gpfsl.examples.graph Require Import graph.

Require Import iris.prelude.options.

Section graph_insert_props.
Context {A : Type}.
Notation graph_event := (graph_event A).
Notation graph := (graph A).
Notation event_list := (event_list A).
Implicit Types (G : graph) (E : event_list) (M : logView) (V : dataView).

Lemma graph_insert_event_is_writing P E eV :
  graph_event_is_writing E P →
  (P eV.(ge_event) → eV.(ge_view).(dv_in) ≠  eV.(ge_view).(dv_comm)) →
  graph_event_is_writing (E ++ [eV]) P.
Proof. intros RA ??? [?%RA|[-> <-]]%lookup_app_1; done. Qed.

Lemma graph_insert_event_is_relacq P E eV :
  graph_event_is_relacq E P →
  (P eV.(ge_event) → eV.(ge_view).(dv_comm) = eV.(ge_view).(dv_wrt)) →
  graph_event_is_relacq (E ++ [eV]) P.
Proof. intros RA ??? [?%RA|[-> <-]]%lookup_app_1; done. Qed.

Lemma graph_insert_event_is_releasing P E eV :
  graph_event_is_releasing E P →
  (P eV.(ge_event) → eV.(ge_view).(dv_comm) ⊑ eV.(ge_view).(dv_wrt)) →
  graph_event_is_releasing (E ++ [eV]) P.
Proof. intros RA ??? [?%RA|[-> <-]]%lookup_app_1; done. Qed.

Lemma graph_insert_event_is_acquiring P E eV :
  graph_event_is_acquiring E P →
  (P eV.(ge_event) → eV.(ge_view).(dv_wrt) ⊑ eV.(ge_view).(dv_comm)) →
  graph_event_is_acquiring (E ++ [eV]) P.
Proof. intros RA ??? [?%RA|[-> <-]]%lookup_app_1; done. Qed.

Lemma graph_insert_xo_eco E eV :
  graph_xo_eco E →
  set_in_bound eV.(ge_lview) (E ++ [eV]) →
  graph_xo_eco (E ++ [eV]).
Proof.
  intros EC IN e1 e2 eV2 [Eqe|[-> <-]]%lookup_app_1.
  - apply (EC _ _ _ Eqe).
  - intros Lt%IN%lookup_lt_is_Some. rewrite app_length /= in Lt. lia.
Qed.
End graph_insert_props.

Section graph_ex.
Context {A : Type}.
Notation graph_event := (graph_event A).
Notation graph := (graph A).
Notation event_list := (event_list A).
Implicit Types (G : graph) (E : event_list) (M : logView) (V : dataView).

(** Extending a Graph with a new event *)
Program Definition graph_insert_event eV G : graph :=
  mkGraph (G.(Es) ++ [eV]) G.(com) G.(so) _ _.
Next Obligation.
  intros; eapply bool_decide_pack; intros ? []%gcons_com_included;
  rewrite app_length /=; lia. Qed.
Next Obligation.
  intros; eapply bool_decide_pack; intros ? []%gcons_so_included;
  rewrite app_length /=; lia. Qed.

Lemma graph_insert_event_eq eV G :
  let G' := graph_insert_event eV G in
  G ⊑ G' ∧
  G'.(Es) = G.(Es) ++ [eV] ∧ G'.(so) = G.(so) ∧ G'.(com) = G.(com).
Proof. split ; [|done]. constructor; simpl; [by eexists|done..]. Qed.

Record graph_insert_props G eV M V : Prop := {
  gins_e := length G.(Es) ;
  gins_M : logView := {[gins_e]} ⊔ M ;
  gins_eV := mkGraphEvent eV V gins_M ;
  gins_G := graph_insert_event gins_eV G ;
  gins_subG : G ⊑ gins_G ;
  gins_subM : M ⊑ gins_M ;
  gins_subME : set_in_bound gins_M gins_G.(Es) ;
  gins_inM : gins_e ∈ gins_M ;
  gins_freshM : gins_e ∉ M ;
  gins_cons : eventgraph_consistent gins_G ;
}.

Lemma graph_insert_props_base G eV M V :
  set_in_bound M G.(Es) →
  eventgraph_consistent G →
  graph_insert_props G eV M V.
Proof.
  intros SubM EGc.
  set e := length G.(Es).
  set M' := {[e]} ⊔ M.
  set egV' := mkGraphEvent eV V M'.
  set G' := graph_insert_event egV' G.
  have InB: set_in_bound M' G'.(Es).
  { intros ? [->%elem_of_singleton|[]%SubM]%elem_of_union; eexists.
    - by rewrite lookup_app_1_eq.
    - by apply lookup_app_l_Some. }
  have FR: e ∉ M. { intros ?%SubM%lookup_lt_is_Some. lia. }
  constructor; [apply graph_insert_event_eq|solve_lat|done|
                set_solver|done|constructor; simpl].
  - intros e1 e2 InSo. destruct (gcons_so_included _ _ InSo) as [].
    do 2 rewrite lookup_app_l //. by apply EGc.
  - intros ?? [?%(egcons_logview_event _ EGc)|[-> <-]]%lookup_app_1; [done|].
    simpl; set_solver-.
  - intros ?? [EqL%(egcons_logview_closed _ EGc)|[-> <-]]%lookup_app_1; [|done].
    intros ? []%EqL. eexists. by apply lookup_app_l_Some.
Qed.

(** Extend a graph with a new pair of events that is synchronized. *)
Program Definition graph_insert_edge
  (e1 : event_id) eV2 G (Le1 : bool_decide (e1 < length G.(Es))%nat) : graph :=
  mkGraph (G.(Es) ++ [eV2])
          ({[(e1, length G.(Es))]} ∪ G.(com))
          ({[(e1, length G.(Es))]} ∪ G.(so)) _ _.
Next Obligation.
  intros. apply bool_decide_unpack in Le1.
  eapply bool_decide_pack;
    intros ? [->%elem_of_singleton|[]%gcons_com_included]%elem_of_union;
    rewrite app_length /=; lia. Qed.
Next Obligation.
  intros. apply bool_decide_unpack in Le1.
  eapply bool_decide_pack;
    intros ? [->%elem_of_singleton|[]%gcons_so_included]%elem_of_union;
    rewrite app_length /=; lia. Qed.

Lemma graph_insert_edge_eq (e1 : event_id) eV2 G
  (Le1 : bool_decide (e1 < length G.(Es))%nat) :
  let G' := graph_insert_edge e1 eV2 G Le1 in
  let e2 := length G.(Es) in
  G ⊑ G' ∧
  G'.(Es) = G.(Es) ++ [eV2] ∧
  G'.(so) = {[(e1, e2)]} ∪ G.(so) ∧ G'.(com) = {[(e1, e2)]} ∪ G.(com).
Proof.
  intros In1 G'. split; last split; [constructor| |done]; simpl; [|set_solver..|done].
  by eexists.
Qed.

Record graph_insert_edge_props
  (e1 : event_id) G
  (eV2 : A) M M1 V2 (Le1 : bool_decide (e1 < length G.(Es))%nat) := {
  ginse_e2 := length G.(Es) ;
  ginse_M : logView := M ∪ ({[ginse_e2]} ∪ M1) ;
  ginse_eV := (mkGraphEvent eV2 V2 ginse_M) ;
  ginse_G := graph_insert_edge e1 ginse_eV G Le1 ;
  ginse_ne : e1 ≠ ginse_e2 ∧ (e1 < ginse_e2)%nat ;
  ginse_subG : G ⊑ ginse_G ;
  ginse_subM : M ⊑ ginse_M ∧ M1 ⊑ ginse_M ;
  ginse_subME : set_in_bound ginse_M ginse_G.(Es) ;
  ginse_inM : e1 ∈ ginse_M ∧ ginse_e2 ∈ ginse_M ;
  ginse_freshM : ginse_e2 ∉ M ;
  ginse_cons : eventgraph_consistent ginse_G ;
}.

Lemma graph_insert_edge_props_base
  e1 G (eV1 : graph_event) (eV2 : A) M V2
  (Eqe1 : G.(Es) !! e1 = Some eV1) :
  set_in_bound M G.(Es) →
  eventgraph_consistent G →
  eV1.(ge_view).(dv_in) ⊑ V2.(dv_comm) →
  let M1 := eV1.(ge_lview) in
  ∃ b : bool_decide (e1 < length G.(Es))%nat,
  graph_insert_edge_props e1 G eV2 M M1 V2 b.
Proof.
  intros SubM EGc SubV M1.
  have InMe1 : e1 ∈ M1 by apply EGc.
  set e2 := length G.(Es).
  set Lt := lookup_lt_Some _ _ _ Eqe1.
  have NEqid : e1 ≠ e2. { clear -Lt. lia. }
  set M' : logView := M ∪ ({[e2]} ∪ M1).
  set eV2n := mkGraphEvent eV2 V2 M'.
  set G' := graph_insert_edge e1 eV2n G (bool_decide_pack _ Lt).
  have FRm : e2 ∉ M. { intros ?%SubM%lookup_lt_is_Some. lia. }
  have SubM1 : set_in_bound M1 G.(Es) by apply (egcons_logview_closed _ EGc _ _ Eqe1).
  have SubM' : set_in_bound M' G'.(Es).
  { intros e. rewrite /= !elem_of_union elem_of_singleton.
    intros [[]%SubM|[->|[]%SubM1]].
    * eexists. by apply lookup_app_l_Some.
    * eexists. apply lookup_app_1_eq.
    * eexists. by apply lookup_app_l_Some. }
  exists (bool_decide_pack _ (lookup_lt_Some _ _ _ Eqe1)).
  constructor; [done|apply graph_insert_edge_eq|solve_lat|done|set_solver|done|constructor];
    rewrite -/G'.
  - intros e1' e2'. rewrite /= elem_of_union elem_of_singleton -/e2.
    intros [Eq|(eV1' & eV2' & Eqe1' & Eqe2' & Le12')%(egcons_so _ EGc)].
    + inversion Eq. subst e1' e2'. clear Eq.
      do 2 eexists. split; [by apply lookup_app_l_Some|].
      split; [by apply lookup_app_1_eq|].
      constructor; simpl; [done|clear; set_solver].
    + exists eV1', eV2'.
      do 2 (split; [by apply lookup_app_l_Some|]). done.
  - intros ?? [?%(egcons_logview_event _ EGc)|[-> <-]]%lookup_app_1; [done|].
    rewrite -/e2 /=. set_solver-.
  - intros ?? [EqL%(egcons_logview_closed _ EGc)|[-> <-]]%lookup_app_1; [|done].
    intros ? []%EqL. eexists. by apply lookup_app_l_Some.
Qed.

(** Extend a graph with a new pair of events that is synchronized with each other. *)
Program Definition graph_insert2
  (eV1 eV2 : graph_event) (G : graph) : graph :=
    mkGraph (G.(Es) ++ [eV1; eV2])
            ({[(length G.(Es), S (length G.(Es))); (S (length G.(Es)), (length G.(Es)))]} ∪ G.(com))
            ({[(length G.(Es), S (length G.(Es))); (S (length G.(Es)), (length G.(Es)))]} ∪ G.(so))
            _ _.
Next Obligation.
  intros; eapply bool_decide_pack => ?;
    rewrite !elem_of_union !elem_of_singleton app_length;
    intros [[->| ->]|[]%gcons_com_included]; simpl; lia. Qed.
Next Obligation.
  intros; eapply bool_decide_pack => ?;
    rewrite !elem_of_union !elem_of_singleton app_length;
    intros [[->| ->]|[]%gcons_so_included]; simpl; lia. Qed.

Lemma graph_insert2_eq eV1 eV2 G :
  let G' := graph_insert2 eV1 eV2 G in
  let e1 := length G.(Es) in let e2 := S (length G.(Es)) in
  G ⊑ G' ∧
  G'.(Es) = G.(Es) ++ [eV1; eV2] ∧
  G'.(so) = {[(e1, e2); (e2, e1)]} ∪ G.(so) ∧
  G'.(com) = {[(e1, e2); (e2, e1)]} ∪ G.(com).
Proof.
  intros G'. split; last split; [constructor|done..]; simpl; [by eexists|set_solver..].
Qed.

Record graph_insert2_props
  G (eV1 eV2 : A) M1 M2 V1 V2 := {
  gins2_e1 : event_id := length G.(Es) ;
  gins2_e2 : event_id := S (length G.(Es)) ;
  gins2_M : logView := {[gins2_e1; gins2_e2]} ∪ M1 ∪ M2 ;
  gins2_eV1 := (mkGraphEvent eV1 V1 gins2_M) ;
  gins2_eV2 := (mkGraphEvent eV2 V2 gins2_M) ;
  gins2_G := graph_insert2 gins2_eV1 gins2_eV2 G ;
  gins2_subG : G ⊑ gins2_G ;
  gins2_subM : M1 ⊑ gins2_M ∧ M2 ⊑ gins2_M ;
  gins2_subME : set_in_bound gins2_M gins2_G.(Es) ;
  gins2_inM : gins2_e1 ∈ gins2_M ∧ gins2_e2 ∈ gins2_M ;
  gins2_ne : gins2_e1 ≠ gins2_e2 ∧ (gins2_e1 < gins2_e2)%nat ;
  gins2_freshM : gins2_e1 ∉ M1 ∪ M2 ∧ gins2_e2 ∉ M1 ∪ M2 ;
  gins2_cons : eventgraph_consistent gins2_G ;
}.

Lemma graph_insert2_props_base G (eV1 eV2 : A) M1 M2 V1 V2 :
  set_in_bound M1 G.(Es) → set_in_bound M2 G.(Es) →
  eventgraph_consistent G →
  V1.(dv_in) ⊑ V2.(dv_comm) →
  V2.(dv_in) ⊑ V1.(dv_comm) →
  graph_insert2_props G eV1 eV2 M1 M2 V1 V2.
Proof.
  intros SubM1 SubM2 EGc SubV1 SubV2.
  set e1 := length G.(Es).
  set e2 := S (length G.(Es)).
  set M' : logView := {[e1;e2]} ∪ M1 ∪ M2.
  set eV1' := mkGraphEvent eV1 V1 M'.
  set eV2' := mkGraphEvent eV2 V2 M'.
  set G' := graph_insert2 eV1' eV2' G.
  have Eqe2 : e2 = length (G.(Es) ++ [eV1']). { rewrite app_length /=; lia. }
  have SubM' : set_in_bound M' G'.(Es).
  { intros ?. rewrite !elem_of_union !elem_of_singleton /=.
    intros [[[-> | ->]|[]%SubM1]|[]%SubM2].
    - rewrite list_lookup_middle; [by eexists|done].
    - rewrite (app_assoc _ [_] [_]) Eqe2 lookup_app_1_eq. by eexists.
    - eexists. by apply lookup_app_l_Some.
    - eexists. by apply lookup_app_l_Some. }
  have FRe1 : e1 ∉ M1 ∪ M2.
  { rewrite elem_of_union.
    intros [?%SubM1%lookup_lt_is_Some|?%SubM2%lookup_lt_is_Some]; lia. }
  have FRe2 : e2 ∉ M1 ∪ M2.
  { rewrite elem_of_union.
    intros [?%SubM1%lookup_lt_is_Some|?%SubM2%lookup_lt_is_Some]; lia. }
  constructor; [apply graph_insert2_eq|set_solver-|solve_lat|set_solver-|lia|done|constructor];
    rewrite -/G'.
  - intros e1' e2'. rewrite /= 2!elem_of_union 2!elem_of_singleton -/e1 -/e2.
    intros [[Eq|Eq]|(? & ? & Eqe1' & Eqe2' & Le12')%(egcons_so _ EGc)].
    + inversion Eq. subst e1' e2'. clear Eq.
      do 2 eexists.
      by rewrite list_lookup_middle //
                 (app_assoc _ [_] [_]) -{2}/e2 Eqe2 lookup_app_1_eq.
    + inversion Eq. subst e1' e2'. clear Eq.
      do 2 eexists.
      by rewrite {1}(app_assoc _ [_] [_]) -{1}/e2 Eqe2 lookup_app_1_eq
                 list_lookup_middle.
    + do 2 eexists. split; last split; [by apply lookup_app_l_Some..|done].
  - intros ?? [?%(egcons_logview_event _ EGc)|[[-> <-]|[-> <-]]]%lookup_app_2;
      [done|..]; rewrite -/e1 -/e2 /=; set_solver-.
  - intros ?? [EqL%(egcons_logview_closed _ EGc)|[[-> <-]|[-> <-]]]%lookup_app_2;
      [|done..]. intros ? []%EqL. eexists. by apply lookup_app_l_Some.
Qed.

Lemma graph_insert2_props_choice (b : bool) G (eV1 eV2 : A) M1 M2 V1 V2 :
  set_in_bound M1 G.(Es) → set_in_bound M2 G.(Es) →
  eventgraph_consistent G →
  V1.(dv_in) ⊑ V2.(dv_comm) →
  V2.(dv_in) ⊑ V1.(dv_comm) →
  graph_insert2_props G
                      (if b then eV1 else eV2) (if b then eV2 else eV1)
                      (if b then M1 else M2) (if b then M2 else M1)
                      (if b then V1 else V2) (if b then V2 else V1).
Proof.
  intros SubM1 SubM2 EGc SubV1 SubV2.
  apply graph_insert2_props_base; [| |done|..]; by destruct b.
Qed.

End graph_ex.

Arguments gins_M {_ _ _ _ _} _.
Arguments gins_e {_ _ _ _ _} _.
Arguments gins_eV {_ _ _ _ _} _.
Arguments gins_G {_ _ _ _ _} _.
Arguments gins_subG {_ _ _ _ _} _.
Arguments gins_subM {_ _ _ _ _} _.
Arguments gins_subME {_ _ _ _ _} _.
Arguments gins_inM {_ _ _ _ _} _.
Arguments gins_freshM {_ _ _ _ _} _.
Arguments gins_cons {_ _ _ _ _} _.

Arguments ginse_e2 {_ _ _ _ _ _ _ _} _.
Arguments ginse_M {_ _ _ _ _ _ _ _} _.
Arguments ginse_eV {_ _ _ _ _ _ _ _} _.
Arguments ginse_G {_ _ _ _ _ _ _ _} _.
Arguments ginse_ne {_ _ _ _ _ _ _ _} _.
Arguments ginse_subG {_ _ _ _ _ _ _ _} _.
Arguments ginse_subM {_ _ _ _ _ _ _ _} _.
Arguments ginse_subME {_ _ _ _ _ _ _ _} _.
Arguments ginse_inM {_ _ _ _ _ _ _ _} _.
Arguments ginse_freshM {_ _ _ _ _ _ _ _} _.
Arguments ginse_cons {_ _ _ _ _ _ _ _} _.

Arguments gins2_e1 {_ _ _ _ _ _ _ _} _.
Arguments gins2_e2 {_ _ _ _ _ _ _ _} _.
Arguments gins2_M {_ _ _ _ _ _ _ _} _.
Arguments gins2_eV1 {_ _ _ _ _ _ _ _} _.
Arguments gins2_eV2 {_ _ _ _ _ _ _ _} _.
Arguments gins2_G {_ _ _ _ _ _ _ _} _.
Arguments gins2_subG {_ _ _ _ _ _ _ _} _.
Arguments gins2_subM {_ _ _ _ _ _ _ _} _.
Arguments gins2_subME {_ _ _ _ _ _ _ _} _.
Arguments gins2_inM {_ _ _ _ _ _ _ _} _.
Arguments gins2_freshM {_ _ _ _ _ _ _ _} _.
Arguments gins2_ne {_ _ _ _ _ _ _ _} _.
Arguments gins2_cons {_ _ _ _ _ _ _ _} _.
