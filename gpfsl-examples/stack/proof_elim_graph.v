From iris.bi Require Import lib.fractional.
From iris.algebra Require Import auth gset gmap agree.
From iris.algebra Require Import lib.mono_list.
From iris.proofmode Require Import tactics.

From gpfsl.base_logic Require Import meta_data.
From gpfsl.logic Require Import logatom invariants.
From gpfsl.logic Require Import readonly_ptsto.
From gpfsl.logic Require Import new_delete.
From gpfsl.logic Require Import proofmode.

From gpfsl.examples.stack Require Import spec_graph code_elimination.
From gpfsl.examples.exchanger Require Import spec_graph_piggyback.

Require Import iris.prelude.options.

(* TODO: move *)
Lemma sum_relation_impl {A B} (RA RA' : relation A) (RB RB': relation B) :
  ∀ ab1 ab2,
  (∀ a1 a2, ab1 = inl a1 → ab2 = inl a2 → RA a1 a2 → RA' a1 a2) →
  (∀ b1 b2, ab1 = inr b1 → ab2 = inr b2 → RB b1 b2 → RB' b1 b2) →
  sum_relation RA RB ab1 ab2 → sum_relation RA' RB' ab1 ab2.
Proof.
  intros ab1 ab2 HA HB SR.
  inversion SR as [?? HRA|?? HRB]; subst ab1 ab2; constructor; naive_solver.
Qed.

Lemma sum_relation_iff {A B} (RA RA' : relation A) (RB RB': relation B) :
  ∀ ab1 ab2,
  (∀ a1 a2, ab1 = inl a1 → ab2 = inl a2 → RA a1 a2 ↔ RA' a1 a2) →
  (∀ b1 b2, ab1 = inr b1 → ab2 = inr b2 → RB b1 b2 ↔ RB' b1 b2) →
  sum_relation RA RB ab1 ab2 ↔ sum_relation RA' RB' ab1 ab2.
Proof. intros ab1 ab2 HA HB; split; apply sum_relation_impl; naive_solver. Qed.
(* END move *)

Implicit Types (γ : gname) (s : loc) (N : namespace) (V : view).
Implicit Type T : list (event_id + event_id).

Definition estkN N := N .@ "estk".

(** Filtering exchange events that are to be simulated. *)
(* "Successful" exchanges only include push-pop exchanges, and
  exclude accidental push-push or pop-pop exchanges. *)
Definition is_push_xchg (xe : graph_event xchg_event) : Prop :=
  match xe.(ge_event) with
  | Exchange v1 v2 => 0 < v1 ∧ v2 = 0
  end.
Local Instance is_push_xchg_dec :
  ∀ xe, Decision (is_push_xchg xe).
Proof. intros [[] ? ?]. solve_decision. Defined.

Definition is_pop_xchg (xe : graph_event xchg_event) : Prop :=
  match xe.(ge_event) with
  | Exchange v1 v2 => v1 = 0 ∧ 0 < v2
  end.
Local Instance is_pop_xchg_dec :
  ∀ xe, Decision (is_pop_xchg xe).
Proof. intros [[] ? ?]. solve_decision. Defined.

Definition is_successful_xchg (xe : graph_event xchg_event) : Prop :=
  match xe.(ge_event) with
  | Exchange v1 v2 => 0 < v1 ∧ v2 = 0 ∨ v1 = 0 ∧ 0 < v2
  end.
Local Instance is_successful_xchg_dec :
  ∀ xe, Decision (is_successful_xchg xe).
Proof. intros [[] ? ?]. solve_decision. Defined.

Definition is_xchg_event
  (P : graph_event xchg_event → Prop) (Ex : event_list xchg_event) e : Prop :=
  ∃ eV, Ex !! e = Some eV ∧ P eV.

Definition is_successful_xchg_event := is_xchg_event is_successful_xchg.
Definition is_push_xchg_event := is_xchg_event is_push_xchg.
Definition is_pop_xchg_event := is_xchg_event is_pop_xchg.

(* Translating an exchange event to a stack event *)
Definition xchg_2_stk (xe : xchg_event) : sevent :=
  match xe with
  | Exchange v1 v2 =>
    if bool_decide (0 < v1 ∧ v2 = 0) then       Push v1
    else if bool_decide (v1 = 0 ∧ 0 < v2) then  Pop v2
    else (* FALSE case, can never happen *)     EmpPop
  end.

Lemma is_xchg_event_impl (P Q : _ → Prop) E e :
  (∀ e, P e → Q e) → is_xchg_event P E e → is_xchg_event Q E e.
Proof. intros HP (eV & Eqe & HPe). exists eV. split; [done|]. by apply HP. Qed.
Lemma is_xchg_event_iff (P Q : _ → Prop) E e :
  (∀ e, P e ↔ Q e) → is_xchg_event P E e ↔ is_xchg_event Q E e.
Proof. intros HP. split; apply is_xchg_event_impl => ?; by apply HP. Qed.

Lemma is_push_succ e : is_push_xchg e → is_successful_xchg e.
Proof. rewrite /is_push_xchg /is_successful_xchg. case_match; naive_solver. Qed.
Lemma is_push_xchg_successful Ex e :
  is_push_xchg_event Ex e → is_successful_xchg_event Ex e.
Proof. apply is_xchg_event_impl, is_push_succ. Qed.

Lemma is_pop_succ e : is_pop_xchg e → is_successful_xchg e.
Proof. rewrite /is_pop_xchg /is_successful_xchg. case_match; naive_solver. Qed.
Lemma is_pop_xchg_successful Ex e :
  is_pop_xchg_event Ex e → is_successful_xchg_event Ex e.
Proof. apply is_xchg_event_impl, is_pop_succ. Qed.

Lemma is_xchg_event_append_not P Ex eV e :
  ¬ P eV → is_xchg_event P Ex e ↔ is_xchg_event P (Ex ++ [eV]) e.
Proof.
  intros UN. apply exist_proper => eV'. split; intros [Eqe SS]; split; auto.
  - by apply lookup_app_l_Some.
  - apply lookup_app_1 in Eqe as [?|[? <-]]; done.
Qed.
Lemma is_xchg_event_append P Ex eV e :
  is_xchg_event P Ex e ∨ e = length Ex ∧ P eV ↔ is_xchg_event P (Ex ++ [eV]) e.
Proof.
  split.
  - intros [(eV' & Eqe & SS)| [-> ?]].
    + exists eV'. split; [|done]. by apply lookup_app_l_Some.
    + exists eV. split; [|done]. by apply list_lookup_middle.
  - intros (eV' & [Eqe|[-> <-]]%lookup_app_1 & SS).
    + left. by exists eV'.
    + by right.
Qed.

Definition stk_props_inj T : Prop :=
  ∀ ee1 ee2 e, T !! ee1 = Some e → T !! ee2 = Some e → ee1 = ee2.

Definition stk_props_dom_l (Eb : event_list sevent) T : Prop :=
  ∀ e, inl e ∈ T ↔ (e < length Eb)%nat.
Definition stk_props_dom_r (Ex : event_list xchg_event) T : Prop :=
  ∀ e, inr e ∈ T ↔ is_successful_xchg_event Ex e.

(** If T contains an exchange event (inr e1), then it must be matched. *)
Definition xchgs_in_pairs (G : graph sevent) T : Prop :=
  ∀ ee1 e1, T !! ee1 = Some (inr e1) →
    ∃ ee2 e2, T !! ee2 = Some (inr e2) ∧ ((ee1,ee2) ∈ G.(so) ∨ (ee2,ee1) ∈ G.(so)).

(** Simulating events *)
Definition stk_props_xchg_map (G : graph sevent) (Gx : graph xchg_event) T : Prop :=
  ∀ e ee eV eVx,
    G.(Es) !! e = Some eV → T !! e = Some (inr ee) → Gx.(Es) !! ee = Some eVx →
    eV.(ge_event) = xchg_2_stk eVx.(ge_event) ∧
    eV.(ge_view).(dv_in) ⊑ eVx.(ge_view).(dv_in) ∧
    (∀ v, eV.(ge_event) = Push v → eV.(ge_view).(dv_comm) ⊑ eVx.(ge_view).(dv_in)) ∧
    (∀ v, eV.(ge_event) = Pop v → eVx.(ge_view).(dv_comm) ⊑ eV.(ge_view).(dv_comm))
  .

Definition stk_props_stk_map (G Gb : graph sevent) T : Prop :=
  ∀ e ee eV eVb,
    G.(Es) !! e = Some eV → T !! e = Some (inl ee) → Gb.(Es) !! ee = Some eVb →
    eVb.(ge_event) = eV.(ge_event) ∧
    eV.(ge_view).(dv_in) ⊑ eVb.(ge_view).(dv_in) ∧
    (∀ v, eV.(ge_event) = Push v → eV.(ge_view).(dv_comm) ⊑ eVb.(ge_view).(dv_comm)) ∧
    (∀ v, eV.(ge_event) = Pop v → eVb.(ge_view).(dv_comm) ⊑ eV.(ge_view).(dv_comm))
  .

Definition stk_props_so_sim (G Gb : graph sevent) (Gx : graph xchg_event) T : Prop :=
  ∀ ee1 ee2 e1 e2, T !! ee1 = Some e1 → T !! ee2 = Some e2 →
    (ee1, ee2) ∈ G.(so) ↔
    sum_relation (λ eb1 eb2, (eb1, eb2) ∈ Gb.(so))
                 (λ ex1 ex2, (ex1, ex2) ∈ Gx.(so) ∧
                             is_push_xchg_event Gx.(Es) ex1 ∧
                             is_pop_xchg_event Gx.(Es) ex2)
                 e1 e2.

Definition stk_props_stk_logview (E Eb : event_list sevent) T : Prop :=
  ∀ ee1 ee2 e1 e2, T !! ee1 = Some (inl e1) → T !! ee2 = Some (inl e2) →
    ∀ eV22 eV2, E !! ee2 = Some eV22 → Eb !! e2 = Some eV2 →
      ee1 ∈ eV22.(ge_lview) → e1 ∈ eV2.(ge_lview).

Record StackProps
  {G Gb : graph sevent} {Gx : graph xchg_event} {T : list (event_id + event_id)}
  {cons : bool} := mkStackProps {
  stk_dom_length : (* T maps G to Gb and Ex *) length T = length G.(Es) ;
  stk_event_id_map_inj : (* T is injective *) stk_props_inj T ;
  stk_event_id_map_dom_l :
    (* Left elements in T simulate the base stack events *)
    stk_props_dom_l Gb.(Es) T ;
  stk_event_id_map_dom_r :
    (* Right elements in T simulate the successful exchange events *)
    stk_props_dom_r Gx.(Es) T ;
  stk_base_stack_map : (* connecting to base stack *) stk_props_stk_map G Gb T ;
  stk_xchg_map : (* connecting to exchanger *) stk_props_xchg_map G Gx T ;
  stk_xchg_push_pop :
    if cons
    (* successful matched PUSH-POP exchange events must be consecutive, with
      PUSH before POP. *)
    then xchgs_in_pairs G T
    else (* if cons = false, we are in the middle of an exchange pair *)
      ∃ Ex xe, Gx.(Es) = Ex ++ [xe] ∧
      if (bool_decide (is_push_xchg xe))
      then (* and only if in the middle of a PUSH-POP exchange pair, then
        (1) the last of T points to the last of Gx, and
        (2) the last of T is unmatched in G
        (3) the history before that only has matched exchanges *)
        ∃ Tr, T = Tr ++ [inr (length Ex)] ∧
        (∀ id : event_id, (length Tr, id) ∉ G.(so)) ∧
        xchgs_in_pairs G Tr
      else (* if they are the other pairs (PUSH-PUSH or POP-POP), then
        they are not in T anyway. *)
        xchgs_in_pairs G T ;
  stk_so_sim : (* simulation of so *) stk_props_so_sim G Gb Gx T ;
  stk_xchg_consec :
    (* exchange event pairs are adjacent *)
    ∀ ee1 ee2 e1 e2,
      T !! ee1 = Some (inr e1) → T !! ee2 = Some (inr e2) →
      (ee1, ee2) ∈ G.(so) → ee2 = S ee1 ;
  stk_base_stack_logview :
    (* eco between elim stack events implies eco between base-stack events *)
    stk_props_stk_logview G.(Es) Gb.(Es) T ;
}.

Arguments StackProps : clear implicits.

(** Local observations of M on G simulate the observations of Mb and Mx *)
(* This also requires that M and Mb are included T.
  TODO: this seems useful only for Mb, not Mx. *)

Definition ElimStackLocalEvents T (M Mb : logView) : Prop :=
  ∀ e, e ∈ M →
  ∃ eo, T !! e = Some eo ∧
    match eo with
    | inl e' => e' ∈ Mb
    | inr e' =>
        (* one always observe the pair of exchange events together *)
        (* e' ∈ Mx ∧ ∃ e'', e'' ∈ Mx ∧ (e', e'') ∈ Gx.(so) *)
        True
    end.

(** Quick helper lemmas *)
Lemma StackProps_empty : StackProps ∅ ∅ ∅ [] true.
Proof.
  constructor; try done; intros ?; rewrite elem_of_nil /=; [lia|].
  rewrite /is_successful_xchg_event /is_xchg_event lookup_nil. naive_solver.
Qed.

Lemma StackProps_is_Some {G Gb Gx T b} ee :
  StackProps G Gb Gx T b → is_Some (T !! ee) ↔ is_Some (G.(Es) !! ee).
Proof. intros SP. by rewrite !lookup_lt_is_Some (stk_dom_length SP). Qed.
Lemma StackProps_is_Some_1 {G Gb Gx T b ee e} :
  StackProps G Gb Gx T b → T !! ee = Some e → is_Some (G.(Es) !! ee).
Proof. intros SP ?. apply (StackProps_is_Some ee SP). by eexists. Qed.
Lemma StackProps_is_Some_2 {G Gb Gx T b ee eV} :
  StackProps G Gb Gx T b → G.(Es) !! ee = Some eV → is_Some (T !! ee).
Proof. intros SP ?. apply (StackProps_is_Some ee SP). by eexists. Qed.

Lemma StackProps_is_Some_so {G Gb Gx T b ee1 ee2} :
  StackProps G Gb Gx T b → (ee1, ee2) ∈ G.(so) →
  is_Some (T !! ee1) ∧ is_Some (T !! ee2).
Proof.
  intros SP Lt%gcons_so_included.
  rewrite /= -(stk_dom_length SP) in Lt. by rewrite <-!lookup_lt_is_Some in Lt.
Qed.
Lemma StackProps_Some_so_l {G Gb Gx T b e1 e2} :
  StackProps G Gb Gx T b → (e1, e2) ∈ Gb.(so) →
  (∃ ee1, T !! ee1 = Some (inl e1)) ∧ (∃ ee2, T !! ee2 = Some (inl e2)).
Proof.
  intros SP [?%(stk_event_id_map_dom_l SP)%elem_of_list_lookup
             ?%(stk_event_id_map_dom_l SP)%elem_of_list_lookup]%gcons_so_included.
  done.
Qed.

Lemma StackProps_is_Some_l {G Gb Gx T b} e :
  StackProps G Gb Gx T b → (∃ ee, T !! ee = Some (inl e)) ↔ is_Some (Gb.(Es) !! e).
Proof.
  intros SP. by rewrite -elem_of_list_lookup (stk_event_id_map_dom_l SP) lookup_lt_is_Some.
Qed.
Lemma StackProps_is_Some_l_1 {G Gb Gx T b ee e} :
  StackProps G Gb Gx T b → T !! ee = Some (inl e) → is_Some (Gb.(Es) !! e).
Proof. intros SP ?. apply (StackProps_is_Some_l e SP). by eexists. Qed.
Lemma StackProps_is_Some_l_1_2 {G Gb Gx T b e} :
  StackProps G Gb Gx T b → inl e ∈ T → is_Some (Gb.(Es) !! e).
Proof. by intros SP [? ?%(StackProps_is_Some_l_1 SP)]%elem_of_list_lookup. Qed.
Lemma StackProps_is_Some_l_2 {G Gb Gx T b e eV} :
  StackProps G Gb Gx T b → Gb.(Es) !! e = Some eV → ∃ ee, T !! ee = Some (inl e).
Proof. intros SP ?. apply (StackProps_is_Some_l e SP). by eexists. Qed.

Lemma StackProps_is_Some_r {G Gb Gx T b} e :
  StackProps G Gb Gx T b →
    (∃ ee, T !! ee = Some (inr e)) ↔ is_successful_xchg_event Gx.(Es) e.
Proof. intros SP. by rewrite -elem_of_list_lookup (stk_event_id_map_dom_r SP). Qed.
Lemma StackProps_is_Some_r_1 {G Gb Gx T b ee e} :
  StackProps G Gb Gx T b → T !! ee = Some (inr e) →
  is_successful_xchg_event Gx.(Es) e.
Proof. intros SP ?. apply (StackProps_is_Some_r e SP). by eexists. Qed.
Lemma StackProps_is_Some_r_1_1 {G Gb Gx T b ee e} :
  StackProps G Gb Gx T b → T !! ee = Some (inr e) → is_Some (Gx.(Es) !! e).
Proof. intros SP HT. destruct (StackProps_is_Some_r_1 SP HT) as (?&?&?). by eexists. Qed.
Lemma StackProps_is_Some_r_1_2 {G Gb Gx T b e} :
  StackProps G Gb Gx T b → inr e ∈ T → is_Some (Gx.(Es) !! e).
Proof. intros SP (?&?&?)%(stk_event_id_map_dom_r SP). by eexists. Qed.

(** For any pair of successful exchanges, one is push iff the other is pop *)
Lemma is_push_pop_xchg_so Gx x1 x2 :
  ExchangerConsistent Gx →
  (x1, x2) ∈ Gx.(so) →
  is_push_xchg_event Gx.(Es) x1 ↔ is_pop_xchg_event Gx.(Es) x2.
Proof.
  intros EC InSo. rewrite (xchg_cons_so_com _ EC) in InSo.
  destruct (xchg_cons_matches _ EC _ _ InSo) as
    (? & eV1 & eV2 & v1 & v2 & Eq1 & Eq2 & Eqev1 & Eqev2 & _).
  rewrite /is_push_xchg_event /is_pop_xchg_event /is_xchg_event Eq1 Eq2
          /is_push_xchg /is_pop_xchg.
  split; intros (? & <-%Some_inj & IS);
    [exists eV2|exists eV1]; move : IS; rewrite Eqev1 Eqev2; naive_solver.
Qed.

Lemma StackProps_inj_insert T e :
  let T' := T ++ [e] in e ∉ T → stk_props_inj T → stk_props_inj T'.
Proof.
  intros T' FR INJ ?? ee [Eq1|[-> <-]]%lookup_app_1 [Eq2|[-> Eqee]]%lookup_app_1;
    [..|done].
  - apply (INJ _ _ _ Eq1 Eq2).
  - subst ee. exfalso. apply FR. by apply elem_of_list_lookup_2 in Eq1.
  - exfalso. apply FR. by apply elem_of_list_lookup_2 in Eq2.
Qed.

Lemma StackProps_dom_l_insert Eb T eV :
  let e' := length Eb in let T' := T ++ [inl e'] in
  stk_props_dom_l Eb T → stk_props_dom_l (Eb ++ [eV]) T'.
Proof.
  intros e' T' DL. intros e.
  rewrite elem_of_app elem_of_list_singleton app_length /= DL.
  rewrite Nat.add_1_r Nat.lt_succ_r Nat.lt_eq_cases. naive_solver.
Qed.
Lemma StackProps_dom_l_insert_r Eb T e :
  let T' := T ++ [inr e] in stk_props_dom_l Eb T → stk_props_dom_l Eb T'.
Proof.
  intros T' DL e'. rewrite elem_of_app elem_of_list_singleton DL. naive_solver.
Qed.

Lemma StackProps_dom_r_insert Ex T eV :
  let e' := length Ex in let T' := T ++ [inr e'] in
  is_successful_xchg eV →
  stk_props_dom_r Ex T → stk_props_dom_r (Ex ++ [eV]) T'.
Proof.
  intros e' T' SS DR. intros e.
  rewrite elem_of_app elem_of_list_singleton DR /is_successful_xchg_event
          -is_xchg_event_append. naive_solver.
Qed.
Lemma StackProps_dom_r_insert_l Ex T e :
  let T' := T ++ [inl e] in stk_props_dom_r Ex T → stk_props_dom_r Ex T'.
Proof.
  intros T' DR e'. rewrite elem_of_app elem_of_list_singleton DR. naive_solver.
Qed.

Lemma StackProps_stk_logview_insert_r E Eb T e eV :
  let E' := E ++ [eV] in let T' := T ++ [inr e] in
  length T = length E →
  stk_props_stk_logview E Eb T → stk_props_stk_logview E' Eb T'.
Proof.
  intros E' T' EqL SL ee1 ee2 e1 e2 [Eqee1|[_ ?]]%lookup_app_1; [|done].
  intros [Eqee2|[_ ?]]%lookup_app_1; [|done].
  intros eV22 eV2 [EqeV2|[-> <-]]%lookup_app_1.
  - apply (SL _ _ _ _ Eqee1 Eqee2 _ _ EqeV2).
  - exfalso. clear -EqL Eqee2. apply lookup_lt_Some in Eqee2. lia.
Qed.

Lemma StackProps_stk_logview_insert E Eb T eV eVb :
  let E' := E ++ [eV] in let Eb' := Eb ++ [eVb] in
  let e' := length E in let eb' := length Eb in let T' := T ++ [inl eb'] in
  length T = length E →
  (∀ e eV, E !! e = Some eV → set_in_bound eV.(ge_lview) E) →
  stk_props_dom_l Eb T →
  (∀ ee1 e1, T !! ee1 = Some (inl e1) → ee1 ∈ eV.(ge_lview) → e1 ∈ eVb.(ge_lview)) →
  (e' ∈ eV.(ge_lview) → eb' ∈ eVb.(ge_lview)) →
  stk_props_stk_logview E Eb T → stk_props_stk_logview E' Eb' T'.
Proof.
  intros E' Eb' e' eb' T' EqL EGC DL HEEb HEEb' SL.
  intros ee1 ee2 e1 e2 Eqee1 Eqee2 eV22 eV2 EqeV22 EqeV2 IneV22.
  apply lookup_app_1 in EqeV22 as [EqeV22|[-> <-]]; last first.
  { rewrite -EqL lookup_app_1_eq in Eqee2. apply Some_inj, inl_inj in Eqee2 as <-.
    rewrite lookup_app_1_eq in EqeV2. apply Some_inj in EqeV2 as <-.
    apply lookup_app_1 in Eqee1 as [Eqee1|[-> <-%inl_inj]].
    - apply (HEEb _ _ Eqee1 IneV22).
    - apply HEEb'. by rewrite /e' -EqL. }
  rewrite lookup_app_1_ne in Eqee2; last first.
  { clear -EqeV22 EqL. intros ->. apply lookup_lt_Some in EqeV22. lia. }
  rewrite lookup_app_1_ne in Eqee1; last first.
  { apply (EGC _ _ EqeV22), lookup_lt_is_Some in IneV22. intros ->. lia. }
  rewrite lookup_app_1_ne in EqeV2; last first.
  { apply elem_of_list_lookup_2, DL in Eqee2. clear -Eqee2. intros ->. lia. }
  by apply (SL _ _ _ _ Eqee1 Eqee2 _ _ EqeV22 EqeV2).
Qed.

(** Simulating unmatched push of base stack *)
Lemma StackProps_unmatched_push {G Gb Gx T u ub} :
  StackProps G Gb Gx T true →
  T !! u = Some (inl ub) →
  unmatched_push G u ↔ unmatched_push Gb ub.
Proof.
  intros SP Equ.
  destruct (StackProps_is_Some_1 SP Equ) as [eV EqeV].
  destruct (StackProps_is_Some_l_1 SP Equ) as [eVb EqeVb].
  rewrite /unmatched_push EqeV EqeVb /=.
  destruct (stk_base_stack_map SP _ _ _ _ EqeV Equ EqeVb) as [-> _].
  apply and_iff_compat_l. split; intros UM pp InSo.
  - destruct (StackProps_Some_so_l SP InSo) as [_ [pp2 Eqpp2]].
    (* stk_so_sim ELIM : from base stack to elim stack *)
    apply (UM pp2), (stk_so_sim SP _ _ _ _ Equ Eqpp2). by constructor.
  - destruct (StackProps_is_Some_so SP InSo) as [_ [ee Eqee]].
    (* stk_so_sim ELIM : from elim stack to base stack *)
    apply (stk_so_sim SP _ _ _ _ Equ Eqee) in InSo.
    inversion InSo as [? pb InSo'|]; clear InSo.
    by apply (UM pb), InSo'.
Qed.

(** Going from the simulating elim graph to the simulated base stack,
  for unmatched push. *)
Lemma StackProps_unmatched_push_1 {G Gb Gx T u} :
  StackProps G Gb Gx T true →
  StackConsistent G →
  unmatched_push G u →
  ∃ ub, T !! u = Some (inl ub) ∧ unmatched_push Gb ub.
Proof.
  intros SP SC UM. set UM' := UM.
  (* from u we get ub, a successful, matched exchange event that u simulates *)
  destruct UM' as [[vu (eVu & Eqvu & Equ)%list_lookup_fmap_inv'] UM'].
  destruct (StackProps_is_Some_2 SP Equ) as [[ub|ub] Equb].
  { exists ub. split; [done|]. by apply (StackProps_unmatched_push SP Equb). }
  (* impossible, any events coming from the exchanger must have been matched. *)
  exfalso.
  (* we get ub2, the one matched with ub, and u2, the one that simulates ub2. *)
  (* stk_xchg_push_pop ELIM *)
  destruct (stk_xchg_push_pop SP _ _ Equb) as (u2 & ub2 & _ & [InSo|InSo]).
  - by apply (UM' u2).
  - rewrite (stk_cons_so_com _ SC) in InSo.
    apply (stk_cons_matches _ SC) in InSo as (_ & _ & dV & v & _ & EqdV & _ & Eqp & _).
    rewrite Equ in EqdV. apply Some_inj in EqdV as <-. by rewrite Eqp in Eqvu.
Qed.

(** Going from the simulated base stack back to the simulating elim stack,
  for unmatched push. *)
Lemma StackProps_unmatched_push_2 {G Gb Gx T ub} :
  StackProps G Gb Gx T true →
  unmatched_push Gb ub →
  ∃ u, T !! u = Some (inl ub) ∧ unmatched_push G u.
Proof.
  intros SP UM. set UM' := UM.
  destruct UM' as
    [[_ (_ & _ & [u Equ]%(StackProps_is_Some_l_2 SP))%list_lookup_fmap_inv'] _].
  exists u. split; [done|]. by apply (StackProps_unmatched_push SP Equ).
Qed.

Lemma StackProps_xchg_map_xchg_insert G Gx T Gx' eVx :
  Gx'.(Es) = Gx.(Es) ++ [eVx] →
  inr (length Gx.(Es)) ∉ T →
  stk_props_xchg_map G Gx T → stk_props_xchg_map G Gx' T.
Proof.
  intros EqGx' FRT XM ???? EqG EqT Eqee. apply (XM _ _ _ _ EqG EqT).
  (* new event is not in T *)
  rewrite EqGx' in Eqee.
  apply lookup_app_1 in Eqee as [?|[-> <-]]; [done|].
  exfalso. apply FRT. by apply elem_of_list_lookup_2 in EqT.
Qed.

Lemma StackProps_so_sim_xchg_insert G Gb Gx T Gx' eVx ep :
  Gx'.(Es) = Gx.(Es) ++ [eVx] →
  let e' := length Gx.(Es) in
  (Gx'.(so) = Gx.(so) ∨ Gx'.(so) = {[(e', ep); (ep, e')]} ∪ Gx.(so)) →
  inr e' ∉ T →
  ¬ is_push_xchg eVx → ¬ is_pop_xchg eVx →
  stk_props_so_sim G Gb Gx T → stk_props_so_sim G Gb Gx' T.
Proof.
  intros EqGx' e' Eqso FRT NPU NPO SO.
  intros ???? Eq1 Eq2. rewrite (SO _ _ _ _ Eq1 Eq2).
  apply sum_relation_iff; [done|]. rewrite EqGx'.
  intros x1 x2 -> ->. destruct Eqso as [->| ->].
  (* TODO hard to find lemmas *)
  - apply and_iff_compat_l, Morphisms_Prop.and_iff_morphism;
      by apply is_xchg_event_append_not.
  - apply Morphisms_Prop.and_iff_morphism;
      [|apply Morphisms_Prop.and_iff_morphism; by apply is_xchg_event_append_not].
    split; [set_solver-|].
    rewrite 2!elem_of_union 2!elem_of_singleton. clear -FRT Eq1 Eq2.
    intros [[[<- <-]%pair_inj|[<- <-]%pair_inj]|Eq']; [..|done];
      exfalso; apply FRT; clear FRT; by eapply elem_of_list_lookup_2.
Qed.

Lemma ElimStackLocalEvents_mono {T T' M Mb Mb'} :
  ElimStackLocalEvents T M Mb →
  T ⊑ T' → Mb ⊆ Mb' →
  ElimStackLocalEvents T' M Mb'.
Proof.
  intros EL SubT' Subb' e (eo & Eqeo & CASE)%EL.
  exists eo. split; [by eapply prefix_lookup_Some|].
  destruct eo as [|eo]; [by apply Subb'|done].
Qed.


Section proof.
Context `{!noprolG Σ}.
Context `{!inG Σ (graphR sevent), !inG Σ (graphR xchg_event)}.
Context `{!ro_ptstoG Σ}.
Context `{!inG Σ (mono_listR (leibnizO (event_id + event_id)))}.

Hypothesis (stk : basic_stack_spec Σ).
Hypothesis (ex  : exchanger_piggyback_spec Σ).

Notation vProp := (vProp Σ).
Notation try_push' := (spec_graph.try_push stk).
Notation try_pop' := (spec_graph.try_pop stk).

Local Existing Instances
  StackInv_Timeless
  StackInv_Objective
  StackInv_Fractional
  StackInv_AsFractional
  StackLocal_Persistent
  StackLocalLite_Persistent
  StackLocalLite_Timeless
  ExchangerInv_Timeless
  ExchangerInv_Objective
  ExchangerInv_Fractional
  ExchangerInv_AsFractional
  ExchangerLocal_Persistent
  ExchangerLocalLite_Persistent
  ExchangerLocalLite_Timeless
  .

(** * Ghost assertions *)
Definition ge_list_auth γ q T : vProp :=
  ⎡ own γ (●ML{#q} (T : listO (leibnizO (event_id + event_id)))) ⎤.
Definition ge_list_lb γ T : vProp :=
  ⎡ own γ (◯ML (T : listO (leibnizO (event_id + event_id)))) ⎤.
Local Instance ge_list_lb_persistent γ T : Persistent (ge_list_lb γ T) := _.

(* Only share the ghost state with the client. *)
Definition StackSharedInv γg (s : loc) (q : Qp) G b γb γx γ Gb Gx T : vProp :=
  ⌜ StackConsistent G ⌝ ∗ graph_master γg (q/2) G ∗
    StackInv stk γb b (q/2)%Qp Gb ∗
    ExchangerInv ex γx (q/2)%Qp Gx ∗
    ge_list_auth γ (q/2) T.

Definition StackInv' γg (s : loc) q G : vProp :=
  ∃ (b : loc) (γsb γsx γb γx γ : gname) Gb Gx T,
    StackSharedInv γg s q G b γb γx γ Gb Gx T ∗
    meta s nroot (γsb,γsx,γb,γx,γ,b).

Global Instance StackInv'_timeless γg s q G : Timeless (StackInv' γg s q G) := _.
Global Instance StackInv'_objective γg s q G : Objective (StackInv' γg s q G) := _.

(* We only need to transfer these things for push events *)
Definition StackViews γb b (G Gb : graph sevent) T : vProp :=
  ∀ e eV v, ⌜ G.(Es) !! e = Some eV ∧ eV.(ge_event) = Push v ⌝ →
    (* the physical view observed the logical view *)
    @{eV.(ge_view).(dv_comm)} (SeenLogview G.(Es) eV.(ge_lview) ∗
      ∃ Mb, StackLocalLite stk γb b Gb Mb ∗ ⌜ ElimStackLocalEvents T eV.(ge_lview) Mb ⌝) .

Definition ElimStackInv_no_exist
  γg (s b x : loc) γsb γsx γb γx γ (cons : bool)
  (Vbx : view) (G Gb : graph sevent) (Gx : graph xchg_event) T : vProp :=
  @{Vbx} (s ro↦{γsb} #b ∗ (s >> 1) ro↦{γsx} #x) ∗
  StackSharedInv γg s 1%Qp G b γb γx γ Gb Gx T ∗
  StackViews γb b G Gb T ∗
  ⌜ StackProps G Gb Gx T cons ∧
    if cons then eventgraph_consistent Gx ∧ ExchangerConsistent Gx else True ⌝
  .

Definition ElimStackInv γg γsb γsx γb γx γ s b x cons : vProp :=
  ∃ Vbx G Gb Gx T,
  ElimStackInv_no_exist γg s b x γsb γsx γb γx γ cons Vbx G Gb Gx T.

Global Instance ElimStackInv_objective γg γsb γsx γb γx γ s b x cons :
  Objective (ElimStackInv γg γsb γsx γb γx γ s b x cons) := _.
Global Instance ElimStackInv_timeless γg γsb γsx γb γx γ s b x cons :
  Timeless (ElimStackInv γg γsb γsx γb γx γ s b x cons) := _.

Definition StackLocalLite' : StackLocalT Σ :=
  (λ γg s G M,
    graph_snap γg G M ∗
    ∃ (b x : loc) (γsb γsx γb γx γ : gname),
    meta s nroot (γsb,γsx,γb,γx,γ,b) ∗
    s ro⊒{γsb} #b ∗ (s >> 1) ro⊒{γsx} #x ∗
    ∃ Gb Mb Gx Mx T,
    StackLocalLite stk γb b Gb Mb ∗
    ExchangerLocalLite ex γx x Gx Mx ∗
    (* observing M means Mb and Mx are at least M *)
    ⌜ ElimStackLocalEvents T M Mb ⌝ ∗
    ge_list_lb γ T
  )%I.

Global Instance StackLocalLite'_persistent γg s G M :
  Persistent (StackLocalLite' γg s G M) := _.
Global Instance StackLocalLite'_timeless γg s G M :
  Timeless (StackLocalLite' γg s G M) := _.

Definition StackLocal' N : StackLocalT Σ :=
  (λ γg s G M,
    graph_snap γg G M ∗
    ∃ (b x : loc) (γsb γsx γb γx γ : gname),
    meta s nroot (γsb,γsx,γb,γx,γ,b) ∗
    s ro⊒{γsb} #b ∗ (s >> 1) ro⊒{γsx} #x ∗
    ∃ Gb Mb Gx Mx T,
    StackLocal stk (estkN N) γb b Gb Mb ∗
    ExchangerLocal ex (ElimStackInv γg γsb γsx γb γx γ s b x) N γx x Gx Mx ∗
    (* observing M means Mb and Mx are at least M *)
    ⌜ ElimStackLocalEvents T M Mb ⌝ ∗
    ge_list_lb γ T ∗
    inv (xchgUN N) (ElimStackInv γg γsb γsx γb γx γ s b x true)
  )%I.

(* TODO: := _. diverges *)
Global Instance StackLocal'_persistent N γg s G M :
  Persistent (StackLocal' N γg s G M).
Proof. apply bi.sep_persistent; apply _. Qed.

(** * Ghost assertions properties *)
#[global] Instance ge_list_auth_fractional γ T :
  Fractional (λ q, ge_list_auth γ q T).
Proof.
  intros p q. by rewrite -embed_sep -own_op -mono_list_auth_dfrac_op.
Qed.
#[global] Instance ge_list_auth_asfractional γ q T :
  AsFractional (ge_list_auth γ q T) (λ q, ge_list_auth γ q T) q.
Proof. constructor; [done|apply _]. Qed.

Lemma ge_list_auth_lb_get γ q T :
  ge_list_auth γ q T -∗ ge_list_lb γ T.
Proof. intros. by apply embed_mono, own_mono, mono_list_included. Qed.
Lemma ge_list_lb_mono γ T T' :
  T' ⊑ T → ge_list_lb γ T -∗ ge_list_lb γ T'.
Proof. intros. by apply embed_mono, own_mono, mono_list_lb_mono. Qed.
Lemma ge_list_auth_lb_get_mono γ q T T' :
  T' ⊑ T → ge_list_auth γ q T -∗ ge_list_lb γ T'.
Proof. intros. etrans; [apply ge_list_auth_lb_get|by apply ge_list_lb_mono]. Qed.

Lemma ge_list_auth_lb_valid γ q T T' :
  ge_list_auth γ q T -∗ ge_list_lb γ T' -∗ ⌜ T' ⊑ T ⌝.
Proof.
  iIntros "o1 o2".
  by iCombine "o1 o2" gives %[_ ?]%mono_list_both_dfrac_valid_L.
Qed.

Lemma ge_list_auth_agree γ q T q' T' :
  ge_list_auth γ q T -∗ ge_list_auth γ q' T' -∗ ⌜ T = T' ⌝.
Proof.
  iIntros "o1 o2".
  by iCombine "o1 o2" gives %[_ ?]%mono_list_auth_dfrac_op_valid_L.
Qed.

Lemma ge_list_alloc T :
  ⊢ |==> ∃ γ, ge_list_auth γ 1 T ∗ ge_list_lb γ T.
Proof.
  iMod (own_alloc (●ML (T : listO (leibnizO (event_id + event_id))))) as (γ) "oT".
  { apply mono_list_auth_valid. }
  iIntros "!>". iExists γ.
  iDestruct (ge_list_auth_lb_get with "oT") as "#$". by iFrame "oT".
Qed.

Lemma ge_list_auth_update γ T T' :
  T ⊑ T' → ge_list_auth γ 1 T ==∗ ge_list_auth γ 1 T'.
Proof.
  intros. rewrite -embed_bupd. by apply embed_mono, own_update, mono_list_update.
Qed.
Lemma ge_list_auth_update' γ T T' :
  T ⊑ T' → ge_list_auth γ 1 T ==∗ ge_list_auth γ 1 T' ∗ ge_list_lb γ T'.
Proof.
  iIntros (SubT) "oT".
  iMod (ge_list_auth_update _ _ _ SubT with "oT") as "oT".
  iDestruct (ge_list_auth_lb_get with "oT") as "#$". by iFrame "oT".
Qed.


Lemma ElimStackInv_locs_access γg γsb γsx γb γx γ s b x cons :
  ElimStackInv γg γsb γsx γb γx γ s b x cons ⊢
  ∃ Vbx, @{Vbx} (s ro↦{γsb} #b ∗ (s >> 1) ro↦{γsx} #x) ∗
        (∀ Vbx', @{Vbx'} (s ro↦{γsb} #b ∗ (s >> 1) ro↦{γsx} #x) -∗
                  ElimStackInv γg γsb γsx γb γx γ s b x cons).
Proof.
  iDestruct 1 as (Vbx G Gb Gx T) "[F R]".
  iExists Vbx. iFrame "F". iIntros (Vbx') "F".
  iExists Vbx', _, _, _, _. by iFrame.
Qed.

#[global] Instance StackSharedInv_fractional γg s G b γb γx γ Gb Gx T :
  Fractional (λ q, StackSharedInv γg s q G b γb γx γ Gb Gx T).
Proof.
  intros p q. rewrite {1}/StackSharedInv.
  rewrite Qp.div_add_distr.
  rewrite graph_master_fractional ge_list_auth_fractional.
  rewrite StackInv_Fractional ExchangerInv_Fractional.
  rewrite (bi.persistent_sep_dup (⌜_⌝)%I).
  iSplit.
  - iIntros "([??] & [??] & [??] & [??] & [??])"; eauto with iFrame.
  - iIntros "[(?&?&?&?&?) (?&?&?&?&?)]"; eauto with iFrame.
Qed.
#[global] Instance StackSharedInv_asfractional γg s q G b γb γx γ Gb Gx T :
  AsFractional (StackSharedInv γg s q G b γb γx γ Gb Gx T)
               (λ q, StackSharedInv γg s q G b γb γx γ Gb Gx T) q.
Proof. constructor; [done|apply _]. Qed.

Lemma StackSharedInv_agree γg s q G b γb γx γ Gb Gx T q' G' Gb' Gx' T' :
  StackSharedInv γg s q G b γb γx γ Gb Gx T -∗
  StackSharedInv γg s q' G' b γb γx γ Gb' Gx' T' -∗
  ⌜ G' = G ∧ Gb' = Gb ∧ Gx' = Gx ∧ T' = T ⌝.
Proof.
  iIntros "(_ & G1 & S1 & E1 & T1) (_ & G2 & S2 & E2 & T2)".
  iDestruct (graph_master_agree with "G2 G1") as %?.
  iDestruct (StackInv_agree with "S2 S1") as %?.
  iDestruct (ExchangerInv_agree with "E2 E1") as %?.
  iDestruct (ge_list_auth_agree with "T1 T2") as %?.
  done.
Qed.

#[global] Instance StackInv'_fractional γg s G :
  Fractional (λ q, StackInv' γg s q G).
Proof.
  intros p q. iSplit.
  - iDestruct 1 as (?????????) "[S #MT]".
    iDestruct (StackSharedInv_fractional with "S") as "[S1 S2]".
    iSplitL "S1"; iExists _,_,_,_,_,_; iExists _,_,_; iFrame "MT ∗".
  - iIntros "[S1 S2]".
    iDestruct "S1" as (?????????) "[S1 #MT1]".
    iDestruct "S2" as (?????????) "[S2 #MT2]".
    iDestruct (meta_agree with "MT2 MT1") as %?. simplify_eq.
    iDestruct (StackSharedInv_agree with "S2 S1") as %(_ & -> & -> & ->).
    iExists _,_,_,_,_,_. iExists _,_,_.
    iFrame "MT1". iApply StackSharedInv_fractional. by iFrame.
Qed.
#[global] Instance StackInv'_asfractional γg s q G :
  AsFractional (StackInv' γg s q G) (λ q, StackInv' γg s q G) q.
Proof. constructor; [done|apply _]. Qed.

Lemma StackInv'_graph_snap_empty γg s q G :
  StackInv' γg s q G -∗ graph_snap γg G ∅.
Proof.
  iDestruct 1 as (?????????) "[(?&G&?) ?]". iApply (graph_master_snap with "G").
Qed.

Lemma StackSharedInv_StackInv'_combine
  γg s G G' b (γsb γsx γb γx γ : gname) Gb Gx T :
  meta s nroot (γsb, γsx, γb, γx, γ, b) -∗
  StackSharedInv γg s 1 G b γb γx γ Gb Gx T -∗
  StackInv' γg s 1 G' -∗
  ⌜ G' = G ⌝ ∗ StackSharedInv γg s (1 + 1) G b γb γx γ Gb Gx T.
Proof.
  iIntros "MT SI SI'". iDestruct "SI'" as (?????????) "[SI' MT']".
  iDestruct (meta_agree with "MT' MT") as "% {MT MT'}". simplify_eq.
  iDestruct (StackSharedInv_agree with "SI SI'") as %(-> & -> & -> & ->).
  iSplit; [done|]. iCombine "SI SI'" as "SI". iFrame.
Qed.

(** * Verifications of Assertions properties *)
Lemma StackInv'_StackConsistent_instance :
  ∀ γg s q G, StackInv' γg s q G ⊢ ⌜ StackConsistent G ⌝.
Proof. intros. iDestruct 1 as (?????????) "[($&?) ?]". Qed.

Lemma StackInv'_graph_master_acc_instance :
  ∀ γg s q G, StackInv' γg s q G ⊢
    ∃ q', graph_master γg q' G ∗ (graph_master γg q' G -∗ StackInv' γg s q G).
Proof.
  intros. iDestruct 1 as (?????????) "[(?&?&?) ?]".
  iExists _. iFrame. iIntros "?". eauto 10 with iFrame.
Qed.

Lemma StackInv'_graph_snap_instance :
  ∀ γg s q G G' M',
    StackInv' γg s q G -∗ graph_snap γg G' M' -∗ ⌜ G' ⊑ G ⌝.
Proof.
  intros. rewrite StackInv'_graph_master_acc_instance.
  iDestruct 1 as (q') "[G _]". iApply (graph_master_snap_included with "G").
Qed.

Lemma StackInv'_agree_instance :
  ∀ γg s q G q' G',
  StackInv' γg s q G -∗ StackInv' γg s q' G' -∗ ⌜ G' = G ⌝.
Proof.
  iDestruct 1 as (?????????) "[(?&S1&?) ?]".
  iDestruct 1 as (?????????) "[(?&S2&?) ?]".
  iApply (graph_master_agree with "S2 S1").
Qed.


Lemma StackLocal'_graph_snap_instance N :
  ∀ γg s G M, StackLocal' N γg s G M ⊢ graph_snap γg G M.
Proof. by iIntros "* [$ _]". Qed.

Lemma StackLocal'_union_instance :
  ∀ N γg s q G G1 G2 M1 M2,
    StackInv' γg s q G -∗ StackLocal' N γg s G1 M1 -∗ StackLocal' N γg s G2 M2 -∗
    StackLocal' N γg s G (M1 ∪ M2).
Proof.
  intros.
  iDestruct 1 as (b γsb γsx γb γx γ Gb Gx T) "[(%SC & G & S & E & T) MT]".
  iIntros "[Gs1 SL1]".
  iDestruct "SL1" as (???????) "(MT' & s0 & s1 & SL1)".
  iDestruct (meta_agree with "MT' MT") as "{MT'} %". simplify_eq.
  iIntros "[Gs2 SL2]".
  iDestruct "SL2" as (???????) "(MT' & _ & s1' & SL2)".
  iDestruct (meta_agree with "MT' MT") as "{MT'} %". simplify_eq.
  iDestruct (ROSeen_agree with "s1 s1'") as %?. simplify_eq.
  iDestruct "SL1" as (Gb1 Mb1 Gx1 Mx1 T1) "(SL1 & EL1 & %EL1 & LT1 & II)".
  iDestruct "SL2" as (Gb2 Mb2 Gx2 Mx2 T2) "(SL2 & EL2 & %EL2 & LT2 & _)".
  iDestruct (ge_list_auth_lb_valid with "T LT1") as %LT1.
  iDestruct (ge_list_auth_lb_valid with "T LT2") as %LT2.
  iDestruct (graph_snap_upgrade with "G Gs1") as "{Gs1} #Gs1".
  iDestruct (graph_snap_upgrade with "G Gs2") as "{Gs2} #Gs2".
  iDestruct (graph_snap_union with "Gs1 Gs2") as "$".
  iExists b, _, γsb, γsx, γb, γx, γ. iFrame "MT s0 s1".
  iExists Gb, (Mb1 ∪ Mb2), Gx, (Mx1 ∪ Mx2), T.
  iDestruct (ge_list_auth_lb_get with "T") as "$". iFrame "II".
  iDestruct (StackLocal_union with "S SL1 SL2") as "$".
  iDestruct (ExchangerLocal_union with "E EL1 EL2") as "$".
  iPureIntro.
  intros e [InM|InM]%elem_of_union.
  - apply (ElimStackLocalEvents_mono EL1 LT1); [set_solver|done].
  - apply (ElimStackLocalEvents_mono EL2 LT2); [set_solver|done].
Qed.

Lemma StackLocalLite'_from_instance N :
  ∀ γg s G M, StackLocal' N γg s G M ⊢ StackLocalLite' γg s G M.
Proof.
  iIntros "* [$ SL]".
  iDestruct "SL" as (???????) "(MT & s0 & s1 & SL)".
  iExists _, _, _, _, _, _, _. iFrame "MT s0 s1".
  iDestruct "SL" as (?????) "(SL & EL & F & oT & ?)".
  iExists _, _, _, _, _. iFrame "F oT".
  iDestruct (StackLocalLite_from with "SL") as "$".
  iDestruct (ExchangerLocalLite_from with "EL") as "$".
Qed.
Lemma StackLocalLite'_to_instance N :
  ∀ γg s G' M' G M,
    StackLocalLite' γg s G M -∗ StackLocal' N γg s G' M' -∗
    StackLocal' N γg s G M.
Proof.
  iIntros "* [$ SL] [_ SL']".
  iDestruct "SL" as (???????) "(#MT & #s0 & #s1 & SL)".
  iExists _, _, _, _, _, _, _. iFrame "MT s0 s1".
  iDestruct "SL" as (?????) "(SL & EL & F & oT)".
  iExists _, _, _, _, _. iFrame "F oT".
  iDestruct "SL'" as (???????) "(MT' & s0' & s1' & SL')".
  iDestruct "SL'" as (?????) "(SL' & EL' & _ & _ & II)".
  iDestruct (meta_agree with "MT MT'") as %?. simplify_eq.
  iDestruct (ROSeen_agree with "s0 s0'") as %?.
  iDestruct (ROSeen_agree with "s1 s1'") as %?. simplify_eq.
  iFrame "II".
  iDestruct (StackLocalLite_to with "SL SL'") as "$".
  iDestruct (ExchangerLocalLite_to with "EL EL'") as "$".
Qed.

Lemma StackLocalLite'_graph_snap_instance :
  ∀ γg s G M, StackLocalLite' γg s G M ⊢ graph_snap γg G M.
Proof. by iIntros "* [$ _]". Qed.


Lemma StackLocalLite'_upgrade_instance :
  ∀ γg s q G' G M,
    StackInv' γg s q G' -∗ StackLocalLite' γg s G M -∗ StackLocalLite' γg s G' M.
Proof.
  intros.
  iDestruct 1 as (b γsb γsx γb γx γ Gb Gx T) "[(%SC & G & S & E & T) MT]".
  iIntros "[Gs SL]".
  iDestruct "SL" as (???????) "(MT' & s0 & s1 & SL)".
  iDestruct (meta_agree with "MT' MT") as "{MT'} %". simplify_eq.
  iDestruct "SL" as (Gb0 Mb Gx0 Mx T0) "(SL & EL & EL0 & LT)".
  iDestruct (graph_snap_upgrade with "G Gs") as "#$".
  iExists b, _, γsb, γsx, γb, γx, γ. iFrame "MT s0 s1".
  iExists Gb0, Mb, Gx0, Mx, T0. by iFrame.
Qed.

(* TODO: general w.r.t StackLocalLite *)
Lemma StackLocal'_upgrade_instance :
  ∀ N γg s q G' G M,
    StackInv' γg s q G' -∗ StackLocal' N γg s G M -∗ StackLocal' N γg s G' M.
Proof.
  iIntros "* SI #SL".
  iDestruct (StackLocalLite'_from_instance with "SL") as "-#SLL".
  iDestruct (StackLocalLite'_upgrade_instance with "SI SLL") as "SLL".
  iApply (StackLocalLite'_to_instance with "SLL SL").
Qed.

(** * Verifications of functions *)
Lemma new_stack_spec :
  new_stack_spec' (new_estack stk.(new_stack) ex.(new_exchanger))
                  StackLocal' StackInv'.
Proof.
  iIntros (N tid Φ) "T Post". wp_lam.
  (* allocate space for pointers *)
  wp_apply wp_new; [done..|].
  iIntros (s) "([H†|%] & Hs & Hms & Hme & _)"; [|done].
  rewrite own_loc_na_vec_cons own_loc_na_vec_singleton.
  iDestruct "Hs" as "[Hbs Hx]".
  wp_let.

  (* allocate the base stack *)
  wp_op. rewrite shift_0.
  wp_apply (new_stack_spec with "T").
  iIntros (γb b) "[SLs [Is1 Is2]]".
  wp_write.

  (* allocate the exchanger *)
  wp_op.
  wp_apply (new_exchanger_spec with "[//]").
  iIntros (γx x) "[[Ix1 Ix2] ELx]".
  iApply wp_fupd. wp_write.

  have SC0 := StackConsistent_empty.
  have SP0 := StackProps_empty.
  have EG0 := (@eventgraph_consistent_empty sevent).

  iMod (graph_master_alloc_empty (eventT:=sevent)) as (γg) "([GM1 GM2] & Gs)".
  iDestruct (graph_snap_empty with "Gs") as "#Gn".

  iMod (ROPtsTo_from_na with "Hbs") as (γsb) "Hbs".
  iDestruct (ROPtsTo_ROSeen with "Hbs") as "#sbs".
  iMod (ROPtsTo_from_na with "Hx") as (γsx) "Hx".
  iDestruct (ROPtsTo_ROSeen with "Hx") as "#sx".
  iCombine "Hbs Hx" as "Hsx".
  iDestruct (view_at_intro with "Hsx") as (Vbx) "[sVbx Hsx]".

  iMod (ge_list_alloc []) as (γ) "[[oT1 oT2] #oTs]".
  iMod (meta_set _ _ (γsb, γsx, γb, γx, γ, b) nroot with "Hms") as "#Hms"; [done|].

  (* allocate the extra invariant for the elimination stack *)
  iMod (inv_alloc (xchgUN N) _ (ElimStackInv γg γsb γsx γb γx γ s b x true)
          with "[Is1 Ix1 GM1 Hsx oT1]") as "#I".
  { iNext. iExists Vbx, ∅, ∅, ∅, []. iFrame. iSplit; [done|]. iSplit; [|done].
    by iIntros (???[]). }

  iApply ("Post" $! γg). iSplitL "SLs ELx".
  (* StackLocal *)
  - iFrame "Gn". iExists b, x, γsb, γsx, γb, γx, γ.
    iFrame "Hms sbs sx". iExists ∅, ∅, ∅, ∅, []. iFrame "SLs I oTs".
    iMod ("ELx" $! _ _ N) as "$". iIntros "!>".
    iPureIntro. by intros ??.
  - iIntros "!>". iExists b, γsb, γsx, γb, γx, γ. iExists ∅, ∅, ∅. by iFrame "Hms ∗".
Qed.

Lemma try_push_spec :
  try_push_spec' (try_push try_push' ex.(exchange)) StackLocal' StackInv'.
Proof.
  iIntros (N DISJ s tid γg G1 M V0 v Posv) "#sV0 #[Gs1 SL]".
  iIntros (Φ) "AU".
  iDestruct "SL" as (b x γsb γsx γb γx γ) "(MT & sbs & sx & SL)".
  iDestruct "SL" as (Gb0 Mb0 Gx0 Mx0 T0) "(SLb0 & ELx0 & %EL0 & LT0 & II)".
  set E1 := G1.(Es).

  (* store our local observations at an old view *)
  iCombine "sbs sx Gs1 SLb0 ELx0" as "THUNK".
  iDestruct (view_at_intro_incl with "THUNK sV0")
    as (V1) "(sV1 & %LeV0 & sbs' & sx' & Gs1' & SLb0' & ELx0') {THUNK}".

  wp_lam. wp_op. rewrite shift_0.
  (* read base stack pointer *)
  wp_bind (!# _)%E.
  iInv "II" as ">I" "Close".
  iDestruct (ElimStackInv_locs_access with "I") as (Vbx) "[[Hs Hx] Close2]".
  iApply (ROSeen_read_non_atomic with "[$sbs $Hs $sV1]"); [solve_ndisj|].
  iIntros "!>" (V2) "([_ %LeV1] & #sV2 & Hs)".
  iMod ("Close" with "[Hs Hx Close2]") as "_".
  { iNext. iApply "Close2". by iFrame "Hs Hx". } clear Vbx.
  iIntros "!>". wp_let.
  (* try push on base stack *)
  awp_apply (try_push_spec stk with "sV1 SLb0"); [solve_ndisj|done|].
  (* open our internal invariant *)
  iInv "II" as (Vbx G Gb Gx T) ">(Locs & SI & R)".
  (* then the AU *)
  iApply (aacc_aupd with "AU"); [solve_ndisj|].
  iIntros (G') ">SI'".
  iDestruct (StackSharedInv_StackInv'_combine with "MT SI SI'") as "[-> SI]".
  iDestruct "SI" as "(%SC & Gm & BI & E & oT)".
  rewrite Qp.div_add_distr Qp.half_half.

  iAaccIntro with "BI".
  { (* peeking case *)
    iIntros "BI !>".
    iDestruct "Gm" as "[G1 G2]". iDestruct "BI" as "[B1 B2]".
    iDestruct "E" as "[E1 E2]". iDestruct "oT" as "[T1 T2]".
    iSplitL "G1 B1 E1 T1".
    { iNext. iExists _,_,_,_,_,_. iExists _,_,_. by iFrame "MT ∗". }
    iIntros "$ !> !>". iExists Vbx, G, Gb, Gx, T. by iFrame. }

  (* committing case *)
  iIntros (b' V3 Gb' psId ps Vps Mb') "(>BI & #sV3 & #SLb' & %CASE)".
  destruct CASE as [(-> & -> & ->)|[-> CASE]].
  - (* push fails, try to exchange *)
    (* but before that, we need to clean up because we're not committing *)
    iLeft. iIntros "!>".
    iDestruct "Gm" as "[G1 G2]". iDestruct "BI" as "[B1 B2]".
    iDestruct "E" as "[E1 E2]". iDestruct "oT" as "[T1 T2]".
    iSplitL "G1 B1 E1 T1".
    { iNext. iExists _,_,_,_,_,_. iExists _,_,_. by iFrame "MT ∗". }
    iIntros "AU !>". iSplitR "AU".
    { (* close the invariant *) iNext. iExists _, G, Gb, Gx, T. by iFrame. }
    iIntros "_ {SLb'}". clear SC Vbx G Gb Gx psId ps Vps T.
    wp_if. wp_op.

    (* read the exchanger pointer *)
    wp_bind (!# _)%E.
    iInv "II" as ">I" "Close".
    iDestruct (ElimStackInv_locs_access with "I") as (Vbx) "[[Hs Hx] Close2]".
    iApply (ROSeen_read_non_atomic with "[$sx $Hx $sV1]"); [solve_ndisj|].
    iIntros "!>" (V4) "([_ %LeV14] & #sV4 & Hx)".
    iMod ("Close" with "[Hs Hx Close2]") as "_".
    { iNext. iApply "Close2". by iFrame "Hx Hs". } clear Vbx.
    iIntros "!>". wp_let.

    wp_apply (exchange_spec ex with "sV1 ELx0 II"); [done|lia|..|iApply "AU"].
    iIntros "!>" (b1 b2) "AU I".
    iAuIntro.
    (* open our internal invariant *)
    iDestruct "I" as (Vbx G Gb Gx T) ">(Locs & SI & SV & SP)".
    (* then the AU *)
    iApply (aacc_aupd with "AU"); [solve_ndisj|].
    iIntros (G') ">SI'".

    iDestruct (StackInv'_graph_snap_empty with "SI'") as "#GEs".
    iDestruct (StackInv'_graph_snap_instance with "SI' Gs1") as %SubG1.

    iDestruct (StackSharedInv_StackInv'_combine with "MT SI SI'") as "[-> SI]".
    iDestruct "SI" as "(%SC & Gm & BI & EI & oT)".
    rewrite Qp.div_add_distr Qp.half_half.
    iAaccIntro with "EI".
    { (* peeking case *)
      iIntros "EI !>".
      iDestruct "Gm" as "[G1 G2]". iDestruct "BI" as "[B1 B2]".
      iDestruct "EI" as "[E1 E2]". iDestruct "oT" as "[T1 T2]".
      iSplitL "G1 B1 E1 T1".
      { iNext. iExists _,_,_,_,_,_. iExists _,_,_. by iFrame "MT ∗". }
      iIntros "$ !> !>". iExists Vbx, G, Gb, Gx, T. by iFrame. }

    (* committing case *)
    iIntros (V5 Gx' psx ppx vp Vpsx Vppx Mx') "(>EI & #sV5 & %F & CASE)".

    iDestruct (SeenLogview_closed with "[]") as %SubM1.
    { iDestruct "Gs1" as "[_ $]". }

    set E := G.(Es).
    have SubE1 : E1 ⊑ E by apply SubG1.
    have SubM : set_in_bound M E. { by eapply set_in_bound_mono. }

    destruct F as (SubGx & SubMx0 & <- & EqV5 & -> & EqGx' & InMx' & NInMx').
    set psx := length Gx.(Es).
    (* The commit view of the push event cannot be the commit view of
      exchange event, it can only be the input view of the exchange event *)
    set V' := Vpsx.(dv_in).
    have bLeV' : bool_decide (V0 ⊑ V') by eapply bool_decide_unpack; eauto.
    set Vpsx' := mkDView V0 V' V' bLeV'.
    set eVx' := mkGraphEvent (Exchange v vp) Vpsx Mx'.

    iDestruct "SP" as %[SP EGC].
    have FRT: inr psx ∉ T.
    { clear -SP. by intros ?%(StackProps_is_Some_r_1_2 SP)%lookup_length_not_is_Some. }

    iDestruct (ge_list_auth_lb_valid with "oT LT0") as %LeT0.

    (* some properties that hold for all cases *)
    have NPO : ¬ is_pop_xchg eVx'.
    { rewrite /is_pop_xchg /=. clear -Posv. lia. }
    have EqeVx' : Gx'.(Es) !! psx = Some eVx'.
    { by rewrite EqGx' lookup_app_1_eq. }

    case (decide (vp = 0)) as [->|NEq0]; last first.
    { (* Failure case: either the exchange fails,
        or we accidentally exchanged with another push *)
      iIntros "!>". iRight.
      iExists false, V', G, psx, dummy_sevt, Vpsx, M.
      iDestruct "Gm" as "[G1 G2]". iDestruct "BI" as "[B1 B2]".
      iDestruct "EI" as "[E1 E2]". iDestruct "oT" as "[T1 T2]".
      iSplitL "G1 B1 E1 T1".
      { iFrame "sV1". iSplitL; last iSplit; [..|iSplit|iPureIntro; by left].
        - iNext. iExists _,_,_,_,_,_. iExists _,_,_. by iFrame "MT ∗".
        - (* TODO: lemma; dup with MS queue *)
          (* @{V'} graph_snap γg G M *)
          rewrite -(view_at_objective_iff (graph_snap γg _ ∅) V').
          iCombine "GEs Gs1'" as "Gs". iApply (view_at_mono with "Gs"); [done|].
          iIntros "(Gs1 & Gs2)". by iApply (graph_snap_mono with "Gs1 Gs2").
        - iExists _, _, _, _, _, _, _. iFrame "MT sbs' sx'".
          iExists Gb0, Mb0, Gx0, Mx0, T0. by iFrame (EL0) "SLb0' ELx0' LT0 II". }

      iAssert (⌜ StackProps G Gb Gx' T (b1 || negb b2)
                ∧ (if b1 || negb b2
                   then eventgraph_consistent Gx' ∧ ExchangerConsistent Gx'
                   else True) ⌝)%I with "[CASE]" as %[SP' EGx'].
      { (* TODO: avoid dups *)
        (* a few more properties that are true for all of these sub cases *)
        have NPU : ¬ is_push_xchg eVx'.
        { rewrite /is_push_xchg /=. clear -NEq0. lia. }
        have NSX : ¬ is_successful_xchg eVx'.
        { rewrite /is_successful_xchg /=. clear -Posv NEq0. lia. }
        have ISC' : ∀ e, inr e ∈ T ↔ is_successful_xchg_event Gx'.(Es) e.
        { intros e. rewrite (stk_event_id_map_dom_r SP) EqGx'.
          by apply is_xchg_event_append_not. }
        have XM' : stk_props_xchg_map G Gx' T.
        { apply (StackProps_xchg_map_xchg_insert _ _ _ _ _ EqGx' FRT),
                (stk_xchg_map SP). }

        (* StackProps *)
        iDestruct "CASE" as "[[F EL]|[F CASE]]".
        { (* exchange fails *)
          iDestruct "F" as %(-> & Eqsox' & ? & ? & ? & ->).
          simpl in *. iPureIntro. split; [|done].
          constructor; [apply SP..|done|apply SP|done|apply SP| |apply SP|apply SP].
          apply (StackProps_so_sim_xchg_insert _ _ _ _ _ _ psx EqGx');
            [by left|done..|by apply (stk_so_sim SP)]. }

        (* we accidentally matched with a push *)
        iDestruct "F" as %(?&?&?&?&?&?&->). simpl in EGC, SP.
        iDestruct "CASE" as "[[F EL]|[F EL]]".
        - (* and we're the later push *)
          iDestruct "F" as %(Lt & -> & EqGx & Eqsox' & Eqcox' & ? & ? & EGx' & ECx').
          simpl. iPureIntro. split; [|done].
          (* StackProps false ==> StackProps true *)
          constructor; [apply SP..|done|apply SP|done| | |apply SP|apply SP].
          + clear -SP EqGx' ECx' Eqcox' Lt Posv EqGx.
            (* xchgs_in_pairs G T *)
            destruct (stk_xchg_push_pop SP) as (Ex & xe & EqEx & Eqxe).
            have Eqppx : ppx = (psx - 1)%nat.
            { destruct (xchg_cons_matches _ ECx' psx ppx) as [EqS _].
              - rewrite Eqcox'. set_solver-.
              - clear -Lt EqS. destruct EqS as [-> | ->]; lia. }

            set egVx := mkGraphEvent (Exchange vp v) Vppx Mx'.
            assert (egVx = xe) as <-.
            { rewrite /psx EqEx app_length /= Nat.add_sub in Eqppx.
              apply (lookup_last_Some_2 Ex). rewrite -EqEx -Eqppx. exact EqGx. }
            rewrite /= bool_decide_false in Eqxe; last first.
            { clear -Posv. by intros [_ ->]. }
            (* now we can use the old xchgs_in_pairs *)
            exact Eqxe.
          + clear -Eqsox' EqGx' FRT SP NPU NPO.
            apply (StackProps_so_sim_xchg_insert _ _ _ _ _ _ ppx EqGx');
              [by right|done..|by apply (stk_so_sim SP)].

        - (* and we're the earlier push *)
          iDestruct "F" as %(Lt & -> & Eqsox' & Eqcox').
          simpl. iPureIntro. split; [|done].
          (* StackProps true ==> StackProps false *)
          constructor; [apply SP..|done|apply SP|done| | |apply SP|apply SP].
          + exists Gx.(Es). eexists. split; [exact EqGx'|].
            rewrite /= bool_decide_false; [apply SP|done].
          + clear -Eqsox' EqGx' SP NPU NPO ppx FRT.
            apply (StackProps_so_sim_xchg_insert _ _ _ _ _ _ ppx EqGx');
              [by left|done..|by apply (stk_so_sim SP)].
      }

      iIntros "HΦ !>". iSplitL "HΦ".
      { (* private post *)
        iIntros "_". wp_op. rewrite bool_decide_false; [|done]. by iApply "HΦ". }
      (* internal invariant *)
      iNext. iExists Vbx, G, Gb, Gx', T. iFrame. by iPureIntro.
    } (* End failure case *)

    (* exchange succeed case *)
    (* first, discharge of failure cases in "CASE" *)
    iDestruct "CASE" as "[[[% _] _]|CASE]"; [by exfalso|].
    iDestruct "CASE" as ((_ & MAXppx & InMppx' & ? & NEqx & ORD & ->)) "CASE".
    specialize (ORD ltac:(lia)).
    iDestruct "CASE" as "[[%F' _]|[CASE #EL]]".
    { exfalso. clear -ORD F' Posv. destruct F' as [? _]. lia. }

    (* now the actual case we need to deal with *)
    iDestruct "CASE" as %(Lt & -> & Eqso & Eqco). simpl.
    (* We know that b1 || b2 = true, and (b1 || negb b2) = false *)
    iDestruct (graph_master_consistent with "Gm") as %EGCs.

    destruct EGC as [EGCsx ECx].
    assert (GIP:= graph_insert_props_base G (Push v) _ Vpsx' SubM EGCs).
    destruct GIP as [psId M' egV' G' LeG' SubM' SUB' Inps NInps EGCs'].
    set E' := G'.(Es).
    have LeE' : E ⊑ E' by apply LeG'.
    set T' := T ++ [(inr psx)].
    have LeT' : T ⊑ T' by eexists.

    iRight. iExists true, V', G', psId, (Push v), Vpsx', M'.

    have NI : ∀ e1 e2, (e1, e2) ∈ G.(com) → e1 ≠ psId ∧ e2 ≠ psId.
    { move => ?? /(gcons_com_included G) [/= ??]. lia. }
    have IPU : is_push_xchg eVx'. { by rewrite /is_push_xchg /=. }
    have ISX : is_successful_xchg eVx' by apply is_push_succ.
    have EqLT : psId = length T. { by rewrite (stk_dom_length SP). }
    have EqTps : T' !! psId = Some (inr psx).
    { by rewrite EqLT lookup_app_1_eq. }

    assert (SP': StackProps G' Gb Gx' T' false).
    { constructor.
      - by rewrite /= !app_length /= (stk_dom_length SP).
      - by apply (StackProps_inj_insert _ _ FRT), (stk_event_id_map_inj SP).
      - by apply StackProps_dom_l_insert_r, (stk_event_id_map_dom_l SP).
      - rewrite EqGx'. apply StackProps_dom_r_insert; [done|].
        by apply (stk_event_id_map_dom_r SP).
      - intros ???? EqG [EqT|[_ Eqr]]%lookup_app_1 Eqee; [|clear -Eqr; done].
        eapply (stk_base_stack_map SP); [|exact EqT|exact Eqee].
        rewrite lookup_app_l in EqG; [done|].
        by apply (StackProps_is_Some_1 SP), lookup_lt_is_Some in EqT.
      - intros ???? EqG [EqT|[-> <-%inr_inj]]%lookup_app_1 Eqee.
        + eapply (stk_xchg_map SP); [|exact EqT|].
          * rewrite lookup_app_l in EqG; [done|].
            by apply (StackProps_is_Some_1 SP), lookup_lt_is_Some in EqT.
          * clear -EqT Eqee EqGx' FRT. rewrite EqGx' in Eqee.
            apply lookup_app_1 in Eqee as [?|[-> <-]]; [done|].
            exfalso. apply FRT. by apply elem_of_list_lookup_2 in EqT.
        + rewrite (stk_dom_length SP) in EqG.
          apply lookup_last_Some_2 in EqG as ->. rewrite EqeVx' in Eqee.
          clear -Eqee Posv LeV0. apply Some_inj in Eqee as <-. simpl.
          split; [|done]. by rewrite bool_decide_true.
      - exists Gx.(Es). eexists. split; [exact EqGx'|].
        rewrite /= bool_decide_true; [|done].
        exists T. split; [done|]. clear -SP. split; [|by apply SP].
        by intros ? [?%lookup_length_not_is_Some _]%(StackProps_is_Some_so SP).
      - intros e1 e2 ee1 ee2 Eq1 Eq2. rewrite Eqso /=.
        apply lookup_app_1 in Eq1 as [Eq1|[-> <-]]; last first.
        { split.
          - by intros [?%lookup_length_not_is_Some _]%(StackProps_is_Some_so SP).
          - clear. intros SR. exfalso. inversion SR as [|?? (Eql & _)]; clear SR.
            by apply gcons_not_in_so_l in Eql. }
        apply lookup_app_1 in Eq2 as [Eq2|[-> <-]]; last first.
        { split.
          - by intros [_ ?%lookup_length_not_is_Some]%(StackProps_is_Some_so SP).
          - clear. intros SR. exfalso. inversion SR as [|?? (Eql & _)]; clear SR.
            by apply gcons_not_in_so_r in Eql. }
        rewrite (stk_so_sim SP _ _ _ _ Eq1 Eq2).
        apply sum_relation_iff; [done|]. intros x1 x2 -> ->. rewrite EqGx'.
        rewrite /is_push_xchg_event /is_pop_xchg_event -2!is_xchg_event_append.
        clear.
        split; intros (InSo & IP1 & IP2); (split; [done|]); [split; by left|split].
        * clear -IP1 InSo. destruct IP1 as [|[-> _]]; [done|].
          exfalso. by apply gcons_not_in_so_l in InSo.
        * clear -IP2 InSo. destruct IP2 as [|[-> _]]; [done|].
          exfalso. by apply gcons_not_in_so_r in InSo.
      - (* consecutiveness of exchange pair *)
        intros ee1 ee2 e1 e2 Eqe1 Eqe2 InG.
        rewrite -(stk_cons_so_com _ SC) EqLT in NI. destruct (NI _ _ InG).
        rewrite lookup_app_1_ne in Eqe1; [|done].
        rewrite lookup_app_1_ne in Eqe2; [|done].
        apply (stk_xchg_consec SP _ _ _ _ Eqe1 Eqe2 InG).
      - (* logview of base stack *)
        apply StackProps_stk_logview_insert_r;
          [apply (stk_dom_length SP)|apply (stk_base_stack_logview SP)]. }

    assert (SC' : StackConsistent G').
    { destruct SC as [SCNZ SCMA SCFN SCME SCNE SCSO SCLIFO SCMO].
      constructor; [| |done| | |done| |].
      - apply stack_positive_value_insert; [|exact SCNZ].
        clear -Posv. simpl => v'. inversion 1; by subst v'.
      - apply stack_matches_value_insert, SCMA.
      - apply stack_unmatched_pop_empty_insert; [|exact SCME].
        clear; left; by eexists.
      - apply stack_empty_unmatched_push_insert; [done| |exact SCNE].
        simpl; clear; by inversion 1.
      - apply stack_LIFO_insert, SCLIFO.
      - clear -SCMO SUB'. by apply graph_insert_xo_eco. }

    iMod (ge_list_auth_update' _ _ _ LeT' with "oT") as "[oT' #LT']".
    iMod (graph_master_update _ _ G' with "Gm") as "[[G1 G2] #Gs']"; [done..|].

    iAssert (@{V'} SeenLogview E' M')%I as "#SL'".
    { rewrite -SeenLogview_insert'. iSplit; [|done].
      iDestruct "Gs1'" as "[_ SL]". iApply (view_at_mono with "SL"); [done|].
      by apply SeenLogview_map_mono. }

    iAssert (@{V'} SeenLogview Gb.(Es) Mb0)%I with "[BI]" as "#SLb'".
    { rewrite StackLocal_graph_snap.
      iDestruct (StackInv_graph_snap with "BI SLb0") as %SubGb0.
      iDestruct "SLb0'" as "[_ SLb0']".
      iApply (view_at_mono with "SLb0'"); [done|].
      apply SeenLogview_map_mono; [|done]. by apply SubGb0. }

    have EL' : ElimStackLocalEvents T' M' Mb0.
    { (* connecting local events *)
      intros e [->%elem_of_singleton|InM]%elem_of_union.
      - by exists (inr psx).
      - have LeT0' : T0 ⊑ T' by etrans.
        by apply (ElimStackLocalEvents_mono EL0). }

    iAssert (@{V'} graph_snap γg G' M')%I as "#Gs5". { iFrame "Gs' SL'". }

    iAssert (@{V'} StackLocal' N γg s G' M')%I with "[]" as "#SSL'".
    { (* updated StackLocal' *)
      iFrame "Gs5".
      iExists b, x, γsb, γsx, γb, γx, γ. iFrame "MT sbs' sx'".
      (* We can just use the old observation because the observations of
        exchanges SOMEHOW(?!) do not matter. *)
      iExists Gb0, Mb0, Gx0, Mx0, T'. by iFrame (EL') "SLb0' ELx0' II LT' ". }

    iAssert (StackViews γb b G' Gb T') with "[SV BI]" as "#SV'".
    { iIntros (e eV ve [[EqeV|[-> <-]]%lookup_app_1 IP]).
      - iDestruct ("SV" $! e eV ve with "[%//]") as "SV".
        iApply (view_at_mono with "SV"); [done|].
        iIntros "[SV EL]". iSplitL "SV".
        + by iApply (SeenLogview_map_mono with "SV").
        + iDestruct "EL" as (Mb) "[SL %EL]". iExists Mb. iFrame "SL".
          iPureIntro. by apply (ElimStackLocalEvents_mono EL).
      - iFrame "SL'". iExists Mb0. iSplit; last by iPureIntro.
        iApply (view_at_mono' with "SLb0'"); [done|].
        iClear "#". rewrite -(view_at_objective_iff (StackInv _ _ _ _ _)).
        iApply (view_at_mono with "BI"); [reflexivity|].
        iIntros "SI SL". rewrite StackLocalLite_from.
        iApply (StackLocalLite_upgrade with "SI SL"). }

    iIntros "!>".
    iDestruct "BI" as "[B1 B2]". iDestruct "EI" as "[E1 E2]".
    iDestruct "oT'" as "[T1 T2]". iSplitL "G1 B1 E1 T1".
    { iFrame "sV1 SSL'". iSplitL; [|iPureIntro; by right].
      iNext. iExists _,_,_,_,_,_. iExists _,_,_. by iFrame "MT ∗". }
    iIntros "HΦ !>". iSplitL "HΦ".
    { iIntros "_". wp_op. by iApply "HΦ". }
    (* re-establish our internal invariant *)
    iNext. iExists Vbx, G', Gb, Gx', T'. by iFrame "∗ SV'".

  - (* push succeeds, commit *)
    iRight.
    iDestruct "R" as "[SV SP]". iDestruct "SP" as %(SP & EGx & ECx).
    destruct CASE as (SubGb & SubMb0 & <- & <- & IS & -> &
                      EqGb' & Eqsob' & Eqcob' & InMb' & ?).
    set psId := length Gb.(Es). set V1 := Vps.(dv_in).

    iDestruct (ge_list_auth_lb_valid with "oT LT0") as %LeT0.
    iDestruct (graph_master_consistent with "Gm") as %EGCs.
    iDestruct (graph_master_snap with "Gm") as "#GEs".
    iDestruct (SeenLogview_closed with "[]") as %SubM1.
    { iDestruct "Gs1" as "[_ $]". }
    iDestruct (graph_master_snap_included with "Gm Gs1") as %SubG1.
    set E := G.(Es).
    have SubE1 : E1 ⊑ E by apply SubG1.
    have SubM : set_in_bound M E. { by eapply set_in_bound_mono. }

    set V' := Vps.(dv_comm).
    have LeV1' : V1 ⊑ V'. { apply dv_in_com. }
    have LeV03 : V0 ⊑ V'. { etrans; [exact LeV0|exact LeV1']. }
    have bLeV0 : bool_decide (V0 ⊑ V') by eapply bool_decide_unpack; eauto.
    set Vps' := mkDView V0 V' Vps.(dv_wrt) bLeV0.

    assert (GIP:= graph_insert_props_base _ (Push v) _ Vps' SubM EGCs).
    destruct GIP as [psIde M' egV' G' LeG' SubM' SUB' Inps NInps EGCs'].
    set E' := G'.(Es).
    have LeE' : E ⊑ E' by apply LeG'.

    set T' := T ++ [(inl psId)].
    have LeT' : T ⊑ T'. { by eexists. }

    iExists true, V', G', psIde, (Push v), Vps', M'.

    have EqLGb' : length Gb'.(Es) = S (length Gb.(Es)).
    { (* TODO: add to spec to avoid repeat *) rewrite EqGb' app_length /=. lia. }
    have EqTps' : T' !! psIde = Some (inl psId).
    { by rewrite /psIde -(stk_dom_length SP) lookup_app_1_eq. }
    have EqGbps : Gb'.(Es) !! psId = Some (mkGraphEvent ps Vps Mb').
    { by rewrite EqGb' lookup_app_1_eq. }

    assert (FRT : inl psId ∉ T).
    { clear -SP. by intros ?%(StackProps_is_Some_l_1_2 SP)%lookup_length_not_is_Some. }
    have NI : ∀ e1 e2, (e1, e2) ∈ G'.(com) → e1 ≠ psIde ∧ e2 ≠ psIde.
    { move => ?? /(gcons_com_included G) [/= ??]. lia. }

    have SP' : StackProps G' Gb' Gx T' true.
    { constructor.
      - by rewrite 2!app_length (stk_dom_length SP) /=.
      - by apply (StackProps_inj_insert _ _ FRT), (stk_event_id_map_inj SP).
      - rewrite EqGb'. apply StackProps_dom_l_insert, (stk_event_id_map_dom_l SP).
      - apply StackProps_dom_r_insert_l, (stk_event_id_map_dom_r SP).
      - intros ?? eV' ? EqG [EqT|[-> Eql]]%lookup_app_1 Eqee.
        + eapply (stk_base_stack_map SP); [|exact EqT|].
          * rewrite lookup_app_l in EqG; [done|].
            by apply (StackProps_is_Some_1 SP), lookup_lt_is_Some in EqT.
          * clear -EqT Eqee EqGb' FRT. rewrite EqGb' in Eqee.
            apply lookup_app_1 in Eqee as [?|[-> <-]]; [done|].
            exfalso. apply FRT. by apply elem_of_list_lookup_2 in EqT.
        + rewrite (stk_dom_length SP) in EqG.
          apply lookup_last_Some_2 in EqG as ->. apply inl_inj in Eql as <-.
          rewrite EqGbps in Eqee. clear -Eqee IS LeV0.
          apply Some_inj in Eqee as <-. done.
      - intros ???? EqG [EqT|[_ Eqr]]%lookup_app_1; [|clear -Eqr; done].
        eapply (stk_xchg_map SP); [|exact EqT].
        rewrite lookup_app_l in EqG; [done|].
        by apply (StackProps_is_Some_1 SP), lookup_lt_is_Some in EqT.
      - intros ?? [EqT|[_ Eqr]]%lookup_app_1; [|clear -Eqr; done].
        destruct (stk_xchg_push_pop SP _ _ EqT) as (ee2 & e2 & Eqee2 & ?).
        exists ee2, e2. split; [|done]. by apply lookup_app_l_Some.
      - intros e1 e2 ee1 ee2 Eq1 Eq2. rewrite /= Eqsob'.
        apply lookup_app_1 in Eq1 as [Eq1|[-> <-]]; last first.
        { split.
          - by intros [?%lookup_length_not_is_Some _]%(StackProps_is_Some_so SP).
          - clear. intros SR. exfalso. inversion SR as [?? Eql|]; clear SR.
            by apply gcons_not_in_so_l in Eql. }
        apply lookup_app_1 in Eq2 as [Eq2|[-> <-]]; last first.
        { split.
          - by intros [_ ?%lookup_length_not_is_Some]%(StackProps_is_Some_so SP).
          - clear. intros SR. exfalso. inversion SR as [?? Eql|]; clear SR.
            by apply gcons_not_in_so_r in Eql. }
        apply (stk_so_sim SP _ _ _ _ Eq1 Eq2).
      - (* consecutiveness of exchange pair *)
        intros ee1 ee2 e1 e2 Eqe1 Eqe2 InG.
        rewrite -(stk_cons_so_com _ SC) /psIde -(stk_dom_length SP) in NI.
        destruct (NI _ _ InG).
        rewrite lookup_app_1_ne in Eqe1; [|done].
        rewrite lookup_app_1_ne in Eqe2; [|done].
        apply (stk_xchg_consec SP _ _ _ _ Eqe1 Eqe2 InG).
      - (* logview of base stack *)
        rewrite EqGb'.
        apply StackProps_stk_logview_insert;
          [apply (stk_dom_length SP)|apply (egcons_logview_closed _ EGCs)
          |apply (stk_event_id_map_dom_l SP)|..|done
          |apply (stk_base_stack_logview SP)].
        clear -SP EL0 SubMb0 LeT0. simpl. intros ee1 e1 Eqee1.
        rewrite /= elem_of_union elem_of_singleton. intros [->|InM].
        + exfalso. apply lookup_lt_Some in Eqee1.
          rewrite /psIde (stk_dom_length SP) in Eqee1. lia.
        + apply EL0 in InM as (ee' & Eqee' & In').
          rewrite (prefix_lookup_Some _ _ _ _ Eqee' LeT0) in Eqee1.
          apply Some_inj in Eqee1 as ->. by apply SubMb0, In'. }

    assert (SC' : StackConsistent G').
    { destruct SC as [SCNZ SCMA SCFN SCME SCNE SCSO SCLIFO SCMO].
      constructor; [| |done|..|done| |].
      - apply stack_positive_value_insert; [|exact SCNZ].
        clear -Posv; simpl => v'; inversion 1; by subst v'.
      - apply stack_matches_value_insert, SCMA.
      - apply stack_unmatched_pop_empty_insert; [|exact SCME].
        clear; left; by eexists.
      - apply stack_empty_unmatched_push_insert; [done| |exact SCNE].
        clear; simpl; by inversion 1.
      - apply stack_LIFO_insert, SCLIFO.
      - clear -SCMO SUB'. by  apply graph_insert_xo_eco. }

    iMod (ge_list_auth_update' _ _ _ LeT' with "oT") as "[oT' #LT']".
    iMod (graph_master_update _ _ _ LeG' with "Gm") as "[[G1 G2] #Gs']"; [done..|].

    iAssert (@{V'} SeenLogview E' M')%I as "#SL'".
    { rewrite -SeenLogview_insert'. iSplit; [|done].
      iDestruct "Gs1'" as "[_ SL]". iApply (view_at_mono with "SL"); [done|].
      by apply SeenLogview_map_mono. }

    have EL' : ElimStackLocalEvents T' M' Mb'.
    { (* linking Local observations *)
      intros e [->%elem_of_singleton|InM]%elem_of_union.
      - by exists (inl psId).
      - have LeT0' : T0 ⊑ T' by etrans.
        by apply (ElimStackLocalEvents_mono EL0). }

    iAssert (@{V'} graph_snap γg G' M')%I as "#Gs3". { iFrame "Gs' SL'". }
    iAssert (@{V'} StackLocal' N γg s G' M')%I with "[]" as "#SSL'".
    { iFrame "Gs3". iExists b, x, γsb, γsx, γb, γx, γ. iFrame "MT sbs' sx'".
      iExists Gb', Mb', Gx0, Mx0, T'. by iFrame (EL') "SLb' ELx0' II LT'". }

    iAssert (StackViews γb b G' Gb' T') with "[SV BI]" as "#SV'".
    { iIntros (e eV ve [[EqeV|[-> <-]]%lookup_app_1 IP]).
      - iDestruct ("SV" $! e eV with "[%//]") as "[SV EL]". iSplitL "SV".
        + iApply (view_at_mono with "SV"); [done|]. by apply SeenLogview_map_mono.
        + iDestruct "EL" as (Mb) "[SL %EL]". iExists Mb. iSplitL.
          * iApply (view_at_mono' with "SL"); [done|].
            iClear "#". rewrite -(view_at_objective_iff (StackInv _ _ _ _ _)).
            iApply (view_at_mono with "BI"); [reflexivity|].
            apply StackLocalLite_upgrade.
          * iPureIntro. by apply (ElimStackLocalEvents_mono EL).
      - iFrame "SL'". iExists Mb'. simpl. iSplit; [|by iPureIntro].
        iApply (view_at_mono with "SLb'"); [done|]. apply StackLocalLite_from. }

    iIntros "!>".
    iDestruct "BI" as "[B1 B2]". iDestruct "E" as "[E1 E2]".
    iDestruct "oT'" as "[T1 T2]". iSplitL "G1 B1 E1 T1".
    { iFrame "sV3 SSL'". iSplitL; [|iPureIntro; by right].
      iNext. iExists _,_,_,_,_,_. iExists _,_,_. by iFrame "MT ∗". }
    iIntros "HΦ !>". iSplitR "HΦ".
    { (* re-establish our internal invariant *)
      iNext. iExists Vbx, G', Gb', Gx, T'. by iFrame "SV' ∗". }
    iIntros "_".
    wp_if. by iApply "HΦ".
Qed.

(* TODO : this proof is general w.r.t. to try_push *)
Lemma push_spec :
  push_spec' (push try_push' ex.(exchange)) StackLocal' StackInv'.
Proof.
  intros N DISJ s tid γg G0 M V v Posv.
  iIntros "#sV #SL" (Φ) "AU".
  iLöb as "IH". wp_rec.
  awp_apply (try_push_spec with "sV SL"); [done..|].
  iApply (aacc_aupd with "AU"); [done|].
  iIntros (G) "QI".
  iAaccIntro with "QI"; first by eauto with iFrame.
  iIntros (b V' G' psId ps Vps M') "(QI & sV' & SL' & CASE) !>".
  iDestruct "CASE" as %[(-> & -> & ->)|[-> F]].
  - iLeft. iFrame "QI". iIntros "AU !> _".
    wp_if. by iApply ("IH" with "AU").
  - iRight. iExists V', G', psId, ps, Vps, M'.
    iFrame "QI sV' SL'". iSplit; [done|].
    iIntros "HΦ !> _". wp_if. by iApply "HΦ".
Qed.

Lemma try_pop_spec :
  try_pop_spec' (try_pop try_pop' ex.(exchange)) StackLocal' StackInv'.
Proof.
  iIntros (N DISJ s tid γg G1 M V0) "#sV0 #[Gs1 SL]".
  iIntros (Φ) "AU".
  iDestruct "SL" as (b x γsb γsx γb γx γ) "(MT & sbs & sx & SL)".
  iDestruct "SL" as (Gb0 Mb0 Gx0 Mx0 T0) "(SLb0 & ELx0 & %EL0 & LT0 & II)".

  (* store our local observations at an old view *)
  iCombine "sbs sx Gs1 SLb0 ELx0" as "THUNK".
  iDestruct (view_at_intro_incl with "THUNK sV0")
    as (V1) "(sV1 & %LeV0 & sbs' & sx' & Gs1' & SLb0' & ELx0') {THUNK}".

  wp_lam. wp_op. rewrite shift_0.
  (* read base stack pointer *)
  wp_bind (!# _)%E.
  iInv "II" as ">I" "Close".
  iDestruct (ElimStackInv_locs_access with "I") as (Vbx) "[[Hs Hx] Close2]".
  iApply (ROSeen_read_non_atomic with "[$sbs $Hs $sV1]"); [solve_ndisj|].
  iIntros "!>" (V2) "([_ %LeV1] & #sV2 & Hs)".
  iMod ("Close" with "[Hs Hx Close2]") as "_".
  { iNext. iApply "Close2". by iFrame "Hs Hx". } clear Vbx.
  iIntros "!>". wp_let.
  (* try pop on base stack *)
  awp_apply (try_pop_spec stk with "sV1 SLb0"); [solve_ndisj|].
  (* open our internal invariant *)
  iInv "II" as (Vbx G Gb Gx T) ">(Locs &  SI & R)".
  (* then the AU *)
  iApply (aacc_aupd with "AU"); [solve_ndisj|].
  iIntros (G') ">SI'".
  iDestruct (StackSharedInv_StackInv'_combine with "MT SI SI'") as "[-> SI]".
  iDestruct "SI" as "(%SC & Gm & BI & E & oT)".
  rewrite Qp.div_add_distr Qp.half_half.

  iAaccIntro with "BI".
  { (* peeking case *)
    iIntros "BI !>".
    iDestruct "Gm" as "[G1 G2]". iDestruct "BI" as "[B1 B2]".
    iDestruct "E" as "[E1 E2]". iDestruct "oT" as "[T1 T2]".
    iSplitL "G1 B1 E1 T1".
    { iNext. iExists _,_,_,_,_,_. iExists _,_,_. by iFrame "MT ∗". }
    iIntros "$ !> !>". iExists Vbx, G, Gb, Gx, T. by iFrame. }

  iIntros (v V3 Gb' psId ppId psE ppE Vpp Mb') "(>BI & #sV3 & #SLb' & %CASE)".

  destruct CASE as [F [CASE|CASE]].
  { (* pop fail due to race *)
    (* not committing yet *)
    destruct CASE as (-> & -> & ->).
    iLeft. iIntros "!>".
    iDestruct "Gm" as "[G1 G2]". iDestruct "BI" as "[B1 B2]".
    iDestruct "E" as "[E1 E2]". iDestruct "oT" as "[T1 T2]".
    iSplitL "G1 B1 E1 T1".
    { iNext. iExists _,_,_,_,_,_. iExists _,_,_. by iFrame "MT ∗". }
    iIntros "AU !>". iSplitR "AU".
    { (* close the invariant *) iNext. iExists _, G, Gb, Gx, T. by iFrame. }
    iIntros "_ {SLb'}". clear SC Vbx F G Gb Gx T psId ppId psE ppE Vpp.
    wp_let. wp_op. wp_if. wp_op.

    (* read the exchanger pointer *)
    wp_bind (!# _)%E.
    iInv "II" as ">I" "Close".
    iDestruct (ElimStackInv_locs_access with "I") as (Vbx) "[[Hs Hx] Close2]".
    iApply (ROSeen_read_non_atomic with "[$sx $Hx $sV1]"); [solve_ndisj|].
    iIntros "!>" (V4) "([_ %LeV14] & #sV4 & Hx)".
    iMod ("Close" with "[Hs Hx Close2]") as "_".
    { iNext. iApply "Close2". by iFrame "Hx Hs". } clear Vbx.
    iIntros "!>". wp_let.
    (* now exchange *)
    wp_apply (exchange_spec ex with "sV1 ELx0 II"); [done|lia| |iApply "AU"].
    iIntros "!>" (b1 b2) "AU I".
    iAuIntro.

    (* open our internal invariant *)
    iDestruct "I" as (Vbx G Gb Gx T) ">(Locs & SI & SV & SP)".
    (* then the AU *)
    iApply (aacc_aupd with "AU"); [solve_ndisj|].
    iIntros (G') ">SI'".

    iDestruct (StackInv'_graph_snap_empty with "SI'") as "#GEs".
    iDestruct (StackInv'_graph_snap_instance with "SI' Gs1") as %SubG1.

    iDestruct (StackSharedInv_StackInv'_combine with "MT SI SI'") as "[-> SI]".
    iDestruct "SI" as "(%SC & Gm & BI & EI & oT)".
    rewrite Qp.div_add_distr Qp.half_half.
    iAaccIntro with "EI".
    { (* peeking case *)
      iIntros "EI !>".
      iDestruct "Gm" as "[G1 G2]". iDestruct "BI" as "[B1 B2]".
      iDestruct "EI" as "[E1 E2]". iDestruct "oT" as "[T1 T2]".
      iSplitL "G1 B1 E1 T1".
      { iNext. iExists _,_,_,_,_,_. iExists _,_,_. by iFrame "MT ∗". }
      iIntros "$ !> !>". iExists Vbx, G, Gb, Gx, T. by iFrame. }

    (* committing case *)
    iIntros (V5 Gx' ppx psx vp Vppx Vpsx Mx') "(>EI & #sV5 & %F & CASE)".

    iDestruct (SeenLogview_closed with "[]") as %SubM1.
    { iDestruct "Gs1" as "[_ $]". }
    set E1 := G1.(Es). set E := G.(Es).
    have SubE1 : E1 ⊑ E by apply SubG1.
    have SubM : set_in_bound M E. { by eapply set_in_bound_mono. }

    destruct F as (SubGx & SubMx0 & <- & <- & -> & EqGx' & InMx' & InMx0).

    set ppx := length Gx.(Es).
    set V1 := Vppx.(dv_in).
    set V' := Vppx.(dv_comm).
    have LeV1' : V1 ⊑ V' by apply dv_in_com.
    have LeV05 : V0 ⊑ V'. { etrans; [apply LeV0|exact LeV1']. }
    have bLeV0 : bool_decide (V0 ⊑ V') by eapply bool_decide_unpack; eauto.
    set Vpp' := mkDView V0 V' Vppx.(dv_wrt) bLeV0.
    set eVppx := mkGraphEvent (Exchange 0 vp) Vppx Mx'.
    set eVpsx := mkGraphEvent (Exchange vp 0) Vpsx Mx'.

    iDestruct (graph_master_consistent with "Gm") as %EGCs.
    iDestruct "SP" as %[SP EC].

    (* some properties that hold for all cases *)
    have NPU : ¬ is_push_xchg eVppx. { rewrite /is_push_xchg /=. lia. }
    have EqLpp : Gx'.(Es) !! ppx = Some eVppx by rewrite EqGx' lookup_app_1_eq.
    have FRT : inr ppx ∉ T.
    { clear -SP. by intros ?%(StackProps_is_Some_r_1_2 SP)%lookup_length_not_is_Some. }

    case (decide (0 < vp)) as [Lt0|NLt0]; last first.
    { (* Failure case: either exchange fails, or we accidentally exchanged with
          another pop *)
      iIntros "!>". iRight.
      iExists (-1), V', G, dummy_eid, dummy_eid, dummy_sevt, dummy_sevt.
      iExists Vpp', M.

      iAssert (@{V'} StackLocal' N γg s G M)%I with "[]" as "#SSL'".
      { iSplit.
        - (* TODO: lemma; dup with MS queue *)
          (* @{V'} graph_snap γg G M *)
          rewrite -(view_at_objective_iff (graph_snap γg _ ∅) V1).
          iCombine "GEs Gs1'" as "Gs". iApply (view_at_mono with "Gs"); [done|].
          iIntros "(Gs1 & Gs2)". by iApply (graph_snap_mono with "Gs1 Gs2").
        - iExists b, x, γsb, γsx, γb, γx, γ. iFrame "MT sbs' sx'".
          iExists Gb0, Mb0, Gx0, Mx0, T0. by iFrame (EL0) "SLb0' ELx0' LT0 II". }

      iDestruct "Gm" as "[G1 G2]". iDestruct "BI" as "[B1 B2]".
      iDestruct "EI" as "[E1 E2]". iDestruct "oT" as "[T1 T2]".
      iSplitL "G1 B1 E1 T1".
      { iFrame "sV5 SSL'". iSplitL; [|iPureIntro; split; [done|by left]].
        iNext. iExists _,_,_,_,_,_. iExists _,_,_. by iFrame "MT ∗". }

      iIntros "HΦ !>". iSplitL "HΦ".
      { (* private post *)
        iIntros "_". wp_let. wp_op. rewrite bool_decide_false; [|done].
        wp_if. by iApply "HΦ". }
      (* internal invariant *)
      iNext. iExists Vbx, G, Gb, Gx', T. iFrame (SC) "∗".

      have NPO : ¬ is_pop_xchg eVppx.
      { rewrite /is_pop_xchg /=. clear -NLt0. lia. }
      have NSX : ¬ is_successful_xchg eVppx.
      { rewrite /is_successful_xchg /=. clear -NLt0. lia. }
      have ISC' : ∀ e, inr e ∈ T ↔ is_successful_xchg_event Gx'.(Es) e.
      { intros e. rewrite (stk_event_id_map_dom_r SP) EqGx'.
        by apply is_xchg_event_append_not. }
      have XM' : stk_props_xchg_map G Gx' T.
      { apply (StackProps_xchg_map_xchg_insert _ _ _ _ _ EqGx' FRT),
              (stk_xchg_map SP). }

      iDestruct "CASE" as "[[F EL]|[F CASE]]".
      { (* exchange failure case *)
        iDestruct "F" as %(-> & EqSo' & ? & ? & ? & ->).
        simpl. iPureIntro. split; [|done].
        (* StackProps G Gb Gx' T true *)
        constructor; [apply SP..|done|apply SP|done|apply SP| |apply SP|apply SP].
        clear -EqSo' EqGx' FRT SP NPO NPU.
        apply (StackProps_so_sim_xchg_insert _ _ _ _ _ _ ppx EqGx');
            [by left|done..|by apply (stk_so_sim SP)]. }

      (* accidental exchange cases *)
      iDestruct "F" as %(Ge0&?&?&?&?&?&->).
      have ? : vp = 0. { clear -NLt0 Ge0. lia. } clear NLt0 Ge0. subst vp.
      simpl.
      iDestruct "CASE" as "[[F EL]|[F EL]]".
      - iDestruct "F" as %(Lt & -> & EqGx & Eqsox' & Eqcox' & ? & ? & ? & ECx').
        simpl. iPureIntro. split; [|done].
        (* StackProps false ==> StackProps true *)
        constructor; [apply SP..|done|apply SP|done| | |apply SP|apply SP].
        + destruct (stk_xchg_push_pop SP) as (Ex' & xe & EqEx' & ISP).
          have Eqpsx : psx = (length Gx.(Es) - 1)%nat.
          { destruct (xchg_cons_matches _ ECx' psx ppx) as [EqS _].
            - rewrite Eqcox'. set_solver-.
            - clear -Lt EqS. subst ppx. destruct EqS as [-> | ->]; lia. }
          set egVx := mkGraphEvent dummy_exevt Vpsx Mx'.
          assert (xe = egVx) as ->.
          { rewrite Eqpsx in EqGx. apply lookup_last_Some in EqGx as [Exx' Eqx'].
            rewrite EqEx' in Eqx'. clear -Eqx'. by simplify_list_eq. }
          rewrite /= in ISP. done.
        + clear -Eqsox' EqGx' SP NPU NPO FRT.
          apply (StackProps_so_sim_xchg_insert _ _ _ _ _ _ psx EqGx');
            [by right|done..|by apply (stk_so_sim SP)].

      - iDestruct "F" as %(? & -> & EqSo' & ?).
        simpl. iPureIntro. split; [|done].
        (* StackProps true ==> StackProps false *)
        constructor; [apply SP..|done|apply SP|done| | |apply SP|apply SP].
        + exists Gx.(Es). eexists. split; [exact EqGx'|]. rewrite /=. apply SP.
        + clear -EqSo' EqGx' SP NPU NPO FRT.
          apply (StackProps_so_sim_xchg_insert _ _ _ _ _ _ ppx EqGx');
            [by left|done..|by apply (stk_so_sim SP)].
    } (* END exchange failure case *)

    (* exchange succeed case *)
    iRight.
    iDestruct "CASE" as "[[[% _] _]|CASE]"; [exfalso; subst vp; by lia|].
    iDestruct "CASE" as ((_ & FAx & FRppx & ? & NEqx & ORD & ->)) "CASE".
    iDestruct "CASE" as "[[F EL']|[F EL']]"; last first.
    { iDestruct "F" as %[Lt _]. exfalso. clear -Lt0 ORD NEqx Lt. lia. }
    iDestruct "F" as %(Lt & -> & EqLps & Eqsox' & Eqcox' & FRppx' &
                      FRpsx' & EGCsx' & ECx').

    have InCox': (psx, ppx) ∈ Gx'.(com).
    { rewrite Eqcox'. set_solver-. }
    (* We know that the psx exchange is tied to a push event that is
      at the top of elim stack graph. This comes from StackProps false. *)
    clear EC; simpl in SP.
    (* stk_xchg_push_pop ELIM. TODO: lemma *)
    destruct (stk_xchg_push_pop SP) as (Ex' & xe & EqEx' & ISP).
    have Eqpsx : psx = (length Gx.(Es) - 1)%nat.
    { destruct (xchg_cons_matches _ ECx' psx ppx) as [EqS _]; [done|].
      clear -Lt EqS. subst ppx. destruct EqS as [-> | ->]; lia. }
    have EqL' : length Ex' = psx.
    { by rewrite Eqpsx EqEx' app_length /= Nat.add_sub. }

    assert (xe = eVpsx) as ->.
    { rewrite Eqpsx in EqLps. apply lookup_last_Some in EqLps as [Exx' Eqx'].
      rewrite EqEx' in Eqx'. clear -Eqx'. by simplify_list_eq. }
    rewrite /= bool_decide_true in ISP; [|done].
    destruct ISP as (Tr & EqlT & UPp & EXP).

    set psId := (length G.(Es) - 1)%nat.

    assert (EqLTr : psId = length Tr).
    { clear -EqlT SP.
      by rewrite /psId -(stk_dom_length SP) EqlT app_length /= Nat.add_sub. }
    rewrite -EqLTr in UPp.
    have EqlT' : T !! psId = Some (inr psx).
    { rewrite EqlT EqLTr -EqL'. by apply list_lookup_middle. }
    destruct (StackProps_is_Some_1 SP EqlT') as [eVps EqeVps].
    destruct (stk_xchg_map SP _ _ _ eVpsx EqeVps EqlT') as [EqeVs LeeV].
    { by rewrite EqEx' -EqL' lookup_app_1_eq. }
    rewrite /= bool_decide_true in EqeVs; [|done].

    assert (NP : ¬ is_push_xchg_event Gx'.(Es) ppx).
    { clear -NPU EqLpp. intros (? & Eqx & ?). rewrite EqLpp in Eqx.
      apply Some_inj in Eqx as <-. by apply NPU. }
    have IPO : is_pop_xchg eVppx. { by rewrite /is_pop_xchg /=. }
    have ISX : is_successful_xchg eVppx by apply is_pop_succ.

    have EqLps' : Gx'.(Es) !! psx = Some eVpsx.
    { rewrite EqGx'. by apply lookup_app_l_Some. }

    set M'' := eVps.(ge_lview).
    destruct LeeV as (LeeVps & ISV & ?).
    specialize (ISV _ EqeVs). simpl in ISV.
    have SubVpp : eVps.(ge_view).(dv_comm) ⊑ Vppx.(dv_comm).
    { etrans; [apply ISV|].
      destruct (xchg_cons_matches _ ECx' _ _ InCox')
        as (_ & eV1 & eV2 & _ & _ & Eq1 & Eq2 & _ & _ & _ & _ & LeeV1 & _).
      rewrite EqLps' in Eq1. rewrite EqLpp in Eq2.
      apply Some_inj in Eq1 as <-. apply Some_inj in Eq2 as <-.
      apply strict_include. exact LeeV1. }
    have SubVin : eVps.(ge_view).(dv_in) ⊑ Vpp'.(dv_comm).
    { rewrite /= /V'. etrans; [apply dv_in_com|exact SubVpp]. }

    assert (GIP := graph_insert_edge_props_base _ _ _ (Pop vp) M Vpp'
                      EqeVps SubM EGCs SubVin).
    rewrite -/M'' in GIP.
    destruct GIP as [b' [ppId M' egV' G' [NEqed Lted] LeG' [Subm' SubeV'] SubM'
                        [Inps' Inpp'] FRpp EGCs']].

    assert (EqG' := graph_insert_edge_eq psId egV' G b').
    rewrite -/G' -/ppId in EqG'. destruct EqG' as (_ & EqEs' & EqSo' & EqCo').

    set E' := G'.(Es).
    have LeE' : E ⊑ E' by apply LeG'.
    set T' := T ++ [(inr ppx)].
    have LeT' : T ⊑ T' by eexists.

    iDestruct (ge_list_auth_lb_valid with "oT LT0") as %LeT0.

    have EqLT : ppId = length T. { by rewrite (stk_dom_length SP). }
    have EqTpp : T' !! ppId = Some (inr ppx).
    { rewrite EqLT. by apply list_lookup_middle. }

    have NI : ∀ e1 e2, (e1, e2) ∈ G.(com) → e1 ≠ ppId ∧ e2 ≠ ppId.
    { move => ?? /(gcons_com_included G) [/= ??]. lia. }
    have SC' : StackConsistent G'.
    { destruct SC as [SCNZ SCMA SCFN SCME SCNE SCSO SCLIFO SCMO]. constructor.
      - apply stack_positive_value_insert; [|exact SCNZ].
        clear; simpl; intros ?; inversion 1.
      - by apply (stack_matches_value_insert_edge _ _ _ _ _ _ EqeVps EqeVs).
      - (* 3 *)
        clear -UPp SCFN SCSO. rewrite SCSO in UPp.
        by apply (stack_com_functional_insert_edge _ _ _ _ UPp SCFN).
      - (* 4 *) apply stack_unmatched_pop_empty_insert_edge, SCME.
      - (* 5 *) by apply stack_empty_unmatched_push_insert_edge.
      - by rewrite /G' /= SCSO.
      - (* stack_LIFO *)
        apply (stack_LIFO_insert_edge _ _ _ _ _ _ EqeVps EqeVs); [|done..]. clear.
        intros u1 o1 _ [_ In1]%gcons_com_included [_ Lto1] _ _ _ _.
        (* we know that psId is the biggest in G, so it cannot be smaller than o1 *)
        simpl in In1. subst psId. lia.
      - clear -SubM' SCMO. by  apply graph_insert_xo_eco.
    }

    have SP' : StackProps G' Gb Gx' T' true.
    { constructor.
      - by rewrite /= !app_length /= (stk_dom_length SP).
      - by apply (StackProps_inj_insert _ _ FRT), (stk_event_id_map_inj SP).
      - apply StackProps_dom_l_insert_r, (stk_event_id_map_dom_l SP).
      - rewrite EqGx'. apply StackProps_dom_r_insert; [done|].
        by apply (stk_event_id_map_dom_r SP).
      - intros ???? EqG [EqT|[_ Eqr]]%lookup_app_1 Eqee; [|clear -Eqr; done].
        eapply (stk_base_stack_map SP); [|exact EqT|exact Eqee].
        rewrite lookup_app_l in EqG; [done|].
        by apply (StackProps_is_Some_1 SP), lookup_lt_is_Some in EqT.
      - intros ???? EqG [EqT|[-> <-%inr_inj]]%lookup_app_1 Eqee.
        + eapply (stk_xchg_map SP); [|exact EqT|].
          * rewrite lookup_app_l in EqG; [done|].
            by apply (StackProps_is_Some_1 SP), lookup_lt_is_Some in EqT.
          * clear -EqT Eqee EqGx' FRT. rewrite EqGx' in Eqee.
            apply lookup_app_1 in Eqee as [?|[-> <-]]; [done|].
            exfalso. apply FRT. by apply elem_of_list_lookup_2 in EqT.
        + rewrite -EqLT in EqG. apply lookup_last_Some_2 in EqG as ->.
          rewrite EqLpp in Eqee. clear -Eqee Lt0 LeV0.
          apply Some_inj in Eqee as <-. rewrite /= bool_decide_true; done.
      - intros ??. rewrite EqSo'. intros [EqT|[-> <-%inr_inj]]%lookup_app_1.
        + clear -EqlT EqLTr EXP EqT EqTpp.
          rewrite EqlT in EqT. apply lookup_app_1 in EqT as [EqT|[-> <-%inr_inj]].
          * destruct (EXP _ _ EqT) as (ee2 & e2 & Eq22 & InSo).
            exists ee2, e2. split.
            { rewrite /T' EqlT. by do 2 apply lookup_app_l_Some. }
            { set_solver+InSo. }
          * exists ppId, ppx. split; [done|]. rewrite -EqLTr. left. set_solver-.
        + clear -EqlT' EqLT. exists psId, psx. split.
          * by apply lookup_app_l_Some.
          * right. rewrite -EqLT. set_solver-.
      - intros ee1 ee2 e1 e2 Eq1 Eq2.
        rewrite EqSo' Eqsox' elem_of_union elem_of_singleton.
        apply lookup_app_1 in Eq1 as [Eq1|[-> <-]]; last first.
        { rewrite -EqLT. split.
          - clear -NEqed. intros [[? _]%pair_inj|?%gcons_not_in_so_l]; done.
          - clear -NP. intros SR. exfalso.
            inversion SR as [|?? (_ & IS & _)]; clear SR. by apply NP. }
        apply lookup_app_1 in Eq2 as [Eq2|[-> <-]].
        + rewrite (stk_so_sim SP _ _ _ _ Eq1 Eq2). split.
          * intros [Eq'|SR].
            { exfalso. clear -Eq2 Eq' SP. apply pair_inj in Eq' as [-> ->].
              by apply (StackProps_is_Some_1 SP), lookup_length_not_is_Some in Eq2. }
            { revert SR; clear -EqGx'. apply sum_relation_impl; [done|].
              intros x1 x2 -> -> (InSo & ? & ?). rewrite EqGx'. split; [|split].
              - set_solver+InSo.
              - apply is_xchg_event_append. by left.
              - apply is_xchg_event_append. by left. }
          * intros SR. right. revert SR. apply sum_relation_impl; [done|].
            intros x1 x2 -> ->. rewrite 2!elem_of_union 2!elem_of_singleton.
            intros (Eqx & ISx & IPx).
            destruct Eqx as [[Eq'%pair_inj|Eq'%pair_inj]|InSo'].
            { exfalso. apply NP. clear -Eq' ISx. by destruct Eq' as [-> _]. }
            { exfalso. apply FRT. clear -Eq2 Eq'. destruct Eq' as [_ ->].
              by apply elem_of_list_lookup_2 in Eq2. }
            { split; [done|].
              rewrite EqGx' in ISx, IPx. apply is_xchg_event_append in ISx, IPx.
              destruct ISx as [ISx|[Eqx1 _]]; last first.
              { exfalso. apply FRppx', elem_of_list_fmap. exists (x1, x2).
                split; [|by apply elem_of_elements]. by rewrite Eqx1. }
              destruct IPx as [IPx|[Eqx2 _]]; last first.
              { exfalso. clear -InSo' Eqx2. subst.
                by apply gcons_not_in_so_r in InSo'. }
              done. }
        + rewrite -EqLT. split.
          * intros [[-> _]%pair_inj|Eq']; last first.
            { exfalso. clear -Eq'. by apply gcons_not_in_so_r in Eq'. }
            (* finally, the main case *)
            rewrite EqlT' in Eq1. apply Some_inj in Eq1 as <-.
            constructor. split; last split.
            { set_solver-. }
            { eexists. rewrite EqGx'. split.
              - apply lookup_app_l_Some. exact EqLps.
              - (* TODO: pull out *) clear -Lt0. done. }
            { eexists. split; [exact EqLpp|exact IPO]. }
          * intros SR. left. inversion SR as [|e1' ? InSo]; clear SR.
            subst e1. move : InSo. rewrite 2!elem_of_union 2!elem_of_singleton.
            intros ([[[-> _]%pair_inj|[-> _]%pair_inj]|InSo] & IS' & IP').
            { exfalso. clear -NP IS'. by apply NP, IS'. }
            { f_equal. (* INJ ELIM, in stk_so_sim right-to-left *)
              apply (stk_event_id_map_inj SP _ _ _ Eq1 EqlT'). }
            exfalso. clear -InSo. by apply gcons_not_in_so_r in InSo.
      - (* consecutiveness of exchange pair *)
        intros ee1 ee2 e1 e2 Eqe1 Eqe2.
        rewrite /= elem_of_union elem_of_singleton -/ppId.
        intros [[-> ->]%pair_inj|InG].
        { rewrite lookup_app_1_ne in Eqe1; [|by rewrite (stk_dom_length SP)].
          rewrite EqTpp in Eqe2. apply Some_inj, inr_inj in Eqe2 as <-.
          clear -Lted. lia. }
        rewrite -(stk_cons_so_com _ SC) EqLT in NI. destruct (NI _ _ InG).
        rewrite lookup_app_1_ne in Eqe1; [|done].
        rewrite lookup_app_1_ne in Eqe2; [|done].
        apply (stk_xchg_consec SP _ _ _ _ Eqe1 Eqe2 InG).
      - (* logview of base stack *)
        apply StackProps_stk_logview_insert_r;
          [apply (stk_dom_length SP)|apply (stk_base_stack_logview SP)]. }

    (* update the graph *)
    iMod (graph_master_update _ _ _ LeG' with "Gm") as "[[G1 G2] #Gs']"; [done..|].
    iMod (ge_list_auth_update' _ _ _ LeT' with "oT") as "[oT #LT']".

    (* the only use of StackView *)
    iAssert (@{V'} SeenLogview E' M')%I with "[SV]" as "#SL'".
    { rewrite -SeenLogview_union' -SeenLogview_insert'.
      iSplitR; last iSplitL; [..| |done].
      - iDestruct "Gs1'" as "[_ SL]". iApply (view_at_mono with "SL").
        + rewrite /V1 /V' /=. apply dv_in_com.
        + apply SeenLogview_map_mono; [|done]. by etrans.
      - iDestruct ("SV" $! psId eVps vp with "[%//]") as "[SV _]".
        iApply (view_at_mono with "SV"); [|done]. exact SubVpp. }

    iAssert (∃ Mb, ⌜ ElimStackLocalEvents T eVps.(ge_lview) Mb ⌝ ∧
              @{eVps.(ge_view).(dv_comm)} StackLocalLite stk γb b Gb Mb)%I
      with "[SV]" as (Mb ELb) "#ELb".
    { iDestruct ("SV" $! psId eVps vp with "[%//]") as "[_ SV]".
      iDestruct "SV" as (Mb) "[SLL %EL]".
      iExists Mb. iSplit; [done|]. iFrame "SLL". }

    set Mb' : logView := Mb0 ∪ Mb.
    have EL' : ElimStackLocalEvents T' M' Mb'.
    { (* connecting local events *)
      have LeT0' : T0 ⊑ T' by etrans.
      intros e. rewrite !elem_of_union elem_of_singleton.
      intros [InM|[->|InM'']].
      + apply (ElimStackLocalEvents_mono EL0); [done|set_solver-|done].
      + by exists (inr ppx).
      + apply (ElimStackLocalEvents_mono ELb); [done|set_solver-|done]. }

    iAssert (@{V'} StackLocal stk (estkN N) γb b Gb Mb')%I with "[BI]" as "#SLL'".
    { iApply (view_at_mono' with "ELb"); [done|].
      iApply (view_at_mono' with "SLb0'"); [done|].
      rewrite -(view_at_objective_iff (StackInv _ _ _ _ _) V').
      iApply (view_at_mono with "BI"); [reflexivity|].
      iIntros "SI SL SLL".
      iDestruct (StackLocalLite_to with "SLL SL") as "#SLL'".
      iApply (StackLocal_union with "SI SL SLL'"). }
    iAssert (StackViews γb b G' Gb T') with "[SV]" as "SV".
    { iIntros (e eV ve [[EqeV|[-> <-]]%lookup_app_1 IS]).
      - iSpecialize ("SV" $! e eV ve with "[%//]").
        iApply (view_at_mono with "SV"); [done|].
        iIntros "[SV EL]". iSplitL "SV".
        + by iApply (SeenLogview_map_mono with "SV").
        + iDestruct "EL" as (Mbb) "[SL %EL]". iExists Mbb. iFrame "SL".
          iPureIntro. by apply (ElimStackLocalEvents_mono EL).
      - iFrame "SL'". iExists Mb'. iSplit; [|by iPureIntro].
        iApply (view_at_mono with "SLL'"); [done|]. apply StackLocalLite_from. }

    iAssert (@{V'} graph_snap γg G' M')%I as "#Gs5". { iFrame "Gs' SL'". }
    iAssert (@{V'} StackLocal' N γg s G' M')%I as "#SSL'".
    { iFrame "Gs5". iExists b, x, γsb, γsx, γb, γx, γ. iFrame "MT sbs' sx'".
      iExists Gb, Mb', Gx', Mx', T'. by iFrame (EL') "SLL' EL' LT' II". }

    iIntros "!>".
    iExists vp, V', G', psId, ppId, (Push vp), (Pop vp).
    iExists Vpp', M'.
    iDestruct "BI" as "[B1 B2]". iDestruct "EI" as "[E1 E2]".
    iDestruct "oT" as "[T1 T2]".
    iSplitL "G1 B1 E1 T1".
    { iFrame "sV5 SSL'". iSplitL.
      - iNext. iExists _,_,_,_,_,_. iExists _,_,_. by iFrame "MT ∗".
      - iPureIntro. split; [done|]. right; right.
        do 11 (split; [done|]). by exists eVps. }
    iIntros "HΦ !>". iSplitL "HΦ".
    { iIntros "_". wp_let. wp_op.
      rewrite bool_decide_true; [|done]. wp_if. by  iApply "HΦ". }
    (* re-establish our internal invariant *)
    iNext. iExists Vbx, G', Gb, Gx', T'. iFrame. simpl. by iPureIntro.
  } (* END exchange case *)

  (* commit case : base stack's pop succeeds or returns empty *)
  iRight.
  destruct F as (SubGb & SubMb0 & <- & <-).

  iDestruct (graph_master_snap with "Gm") as "#GEs".
  iDestruct (SeenLogview_closed with "[]") as %SubM1.
  { iDestruct "Gs1" as "[_ $]". }
  iDestruct (graph_master_snap_included with "Gm Gs1") as %SubG1.
  set E1 := G1.(Es). set E := G.(Es).
  have SubE1 : E1 ⊑ E by apply SubG1.
  have SubM : set_in_bound M E. { by eapply set_in_bound_mono. }

  iDestruct (graph_master_consistent with "Gm") as %EGCs.
  iDestruct "R" as "[SV %SP]". destruct SP as (SP & EGCx & ECx).
  iDestruct (ge_list_auth_lb_valid with "oT LT0") as %LeT0.

  set V1 := Vpp.(dv_in).
  set V' := Vpp.(dv_comm).
  have LeV1' : V1 ⊑ V' by apply dv_in_com.
  have LeV03 : V0 ⊑ V'. { etrans; [apply LeV0|exact LeV1']. }
  have bLeV0 : bool_decide (V0 ⊑ V') by eapply bool_decide_unpack; eauto.
  set Vpp' := mkDView V0 V' Vpp.(dv_wrt) bLeV0.

  set T' := T ++ [inl ppId].
  have LeT' : T ⊑ T' by eexists.
  iMod (ge_list_auth_update' _ _ _ LeT' with "oT") as "[oT' #LT']".

  iDestruct (StackInv_StackConsistent with "BI") as %SCb'.
  iAssert (⌜eventgraph_consistent Gb'⌝)%I with "[BI]" as %ECb'.
  { iDestruct (StackInv_graph_master_acc with "BI") as (q') "[GE ?]".
    iApply (graph_master_consistent with "GE"). }

  assert (Gb'.(Es) !! ppId = Some (mkGraphEvent ppE Vpp Mb') ∧
          length Gb'.(Es) = S (length Gb.(Es)) ∧
          inl ppId ∉ T) as (Eqpp & EqLGb' & FRT).
  { clear -CASE SP. destruct CASE as [(_&_&->&->&_)|(_&_&_&->&_&->&_)];
      (split; [by apply list_lookup_middle|]);
      (split; [rewrite app_length /=; lia|]);
      by intros ?%(StackProps_is_Some_l_1_2 SP)%lookup_length_not_is_Some. }

  destruct CASE as [CASE|CASE].
  - (* empty pop case, commit *)
    destruct CASE as (-> & -> & -> & EqGb' & Eqsob & Eqcob & EqMb' & NInMb0 & UMb).
    set ppId := length Gb.(Es).
    assert (GIP:= graph_insert_props_base _ EmpPop _ Vpp' SubM EGCs).
    destruct GIP as [ppIde M' egV' G' LeG' SubM' SUB' Inpp NInpp EGCs'].
    set E' := G'.(Es).
    have LeE' : E ⊑ E' by apply LeG'.

    (* Empty pop *)
    have NI : ∀ e1 e2, (e1, e2) ∈ G'.(com) → e1 ≠ ppIde ∧ e2 ≠ ppIde.
    { move => ?? /(gcons_com_included G) [/= ??]. lia. }
    have EqLT : ppIde = length T. { by rewrite (stk_dom_length SP). }
    have EqTpp : T' !! ppIde = Some (inl ppId).
    { rewrite EqLT. by apply list_lookup_middle. }

    assert (SC' : StackConsistent G').
    { have SC' := SC.
      destruct SC' as [SCNZ SCMA SCFN SCME SCNE SCSO SCLIFO SCMO].
      constructor; [| |done| | |done| |].
      - apply stack_positive_value_insert; [|exact SCNZ].
        clear; simpl => ?; by inversion 1.
      - apply stack_matches_value_insert, SCMA.
      - apply stack_unmatched_pop_empty_insert; [|exact SCME]. clear; by right.
      - apply stack_empty_unmatched_push_insert; [done| |exact SCNE].
        intros _ u. rewrite elem_of_union elem_of_singleton => [[->|InM]].
        { intros [[v Eqp] _]. rewrite lookup_app_1_eq /= in Eqp. by inversion Eqp. }
        intros UM'.
        have UM : unmatched_push G u.
        { apply (unmatched_push_mono _ _ _ LeG'); [apply SubM, InM|done]. }
        (* Any unmatched push u in G is from Gb, so we piggy back on Gb's
          consistency. *)
        destruct (StackProps_unmatched_push_1 SP SC UM) as (ub & Equb & UMub).
        apply (stk_cons_non_empty _ SCb' _ _ Eqpp eq_refl ub).
        + (* need ub ∈ Mb0 *)
          clear -EL0 InM LeT0 Equb EqMb'.
          destruct (EL0 _ InM) as (eeu & Eqeeu & Inu).
          assert (Equ' := prefix_lookup_inv _ _ _ _ Equb ltac:(by eexists) LeT0).
          rewrite Eqeeu in Equ'. inversion Equ'; clear Eqeeu Equ'; subst eeu.
          rewrite /= EqMb'. set_solver+Inu.
        + destruct UMub as [Eqv NInso]. split; [|by rewrite Eqsob].
          rewrite EqGb'. clear -Eqv.
          destruct Eqv as [v (eV & EqeV & Eqb)%list_lookup_fmap_inv'].
          exists v. apply list_lookup_fmap_inv'. exists eV. split; [done|].
          by apply lookup_app_l_Some.
      - apply stack_LIFO_insert, SCLIFO.
      - clear -SCMO SUB'. by apply graph_insert_xo_eco. }

    have SP' : StackProps G' Gb' Gx T' true.
    { constructor.
      - by rewrite 2!app_length /= (stk_dom_length SP).
      - by apply (StackProps_inj_insert _ _ FRT), (stk_event_id_map_inj SP).
      - rewrite EqGb'. apply StackProps_dom_l_insert, (stk_event_id_map_dom_l SP).
      - by apply StackProps_dom_r_insert_l, (stk_event_id_map_dom_r SP).
      - intros ?? eV' eVb EqG [EqT|[-> <-%inl_inj]]%lookup_app_1 Eqee.
        + eapply (stk_base_stack_map SP); [|exact EqT|].
          * rewrite lookup_app_l in EqG; [done|].
            by apply (StackProps_is_Some_1 SP), lookup_lt_is_Some in EqT.
          * clear -EqT Eqee EqGb' FRT. rewrite EqGb' in Eqee.
            apply lookup_app_1 in Eqee as [?|[-> <-]]; [done|].
            exfalso. apply FRT. by apply elem_of_list_lookup_2 in EqT.
        + rewrite (stk_dom_length SP) in EqG.
          apply lookup_last_Some_2 in EqG as ->. rewrite Eqpp in Eqee.
          clear -Eqee LeV0. apply Some_inj in Eqee as <-. done.
      - intros ???? EqG [EqT|[_ Eqr]]%lookup_app_1; [|clear -Eqr; done].
        eapply (stk_xchg_map SP); [|exact EqT].
        rewrite lookup_app_l in EqG; [done|].
        by apply (StackProps_is_Some_1 SP), lookup_lt_is_Some in EqT.
      - intros ?? [EqT|[_ Eqr]]%lookup_app_1; [|clear -Eqr; done].
        destruct (stk_xchg_push_pop SP _ _ EqT) as (ee2 & e2 & Eqee2 & InSo).
        exists ee2, e2. split; [by apply lookup_app_l_Some|done].
      - intros e1 e2 ee1 ee2 Eq1 Eq2. rewrite /= Eqsob.
        apply lookup_app_1 in Eq1 as [Eq1|[-> <-]]; last first.
        { rewrite -EqLT. split.
          - by intros ?%gcons_not_in_so_l.
          - clear. intros SR. exfalso. inversion SR as [?? InSo|]; clear SR.
            by apply gcons_not_in_so_l in InSo. }
        apply lookup_app_1 in Eq2 as [Eq2|[-> <-]].
        { apply (stk_so_sim SP _ _ _ _ Eq1 Eq2). }
        + rewrite (stk_dom_length SP) -/ppIde. split.
          * by intros ?%gcons_not_in_so_r.
          * clear. intros SR. exfalso. inversion SR as [?? InSo|]; clear SR.
            by apply gcons_not_in_so_r in InSo.
      - (* consecutiveness of exchange pair *)
        intros ee1 ee2 e1 e2 Eqe1 Eqe2 InG.
        rewrite -(stk_cons_so_com _ SC) EqLT in NI. destruct (NI _ _ InG).
        rewrite lookup_app_1_ne in Eqe1; [|done].
        rewrite lookup_app_1_ne in Eqe2; [|done].
        apply (stk_xchg_consec SP _ _ _ _ Eqe1 Eqe2 InG).
      - (* logview of base stack *)
        rewrite EqGb'.
        apply StackProps_stk_logview_insert;
          [apply (stk_dom_length SP)|apply (egcons_logview_closed _ EGCs)
          |apply (stk_event_id_map_dom_l SP)|..| |
          |apply (stk_base_stack_logview SP)]; last first.
        { intros _. simpl. rewrite EqMb'. set_solver-. }
        clear -SP EL0 SubMb0 LeT0. simpl. intros ee1 e1 Eqee1.
        rewrite /= elem_of_union elem_of_singleton. intros [->|InM].
        + exfalso. apply lookup_lt_Some in Eqee1.
          rewrite /ppIde (stk_dom_length SP) in Eqee1. lia.
        + apply EL0 in InM as (ee' & Eqee' & In').
          rewrite (prefix_lookup_Some _ _ _ _ Eqee' LeT0) in Eqee1.
          apply Some_inj in Eqee1 as ->. by apply SubMb0, In'. }

    iMod (graph_master_update _ _ _ LeG' with "Gm") as "[[G1 G2] #Gs']"; [done..|].

    iAssert (@{V'} SeenLogview E' M')%I as "#SL'".
    { rewrite -SeenLogview_insert'. iSplit; [|done].
      iDestruct "Gs1'" as "[_ SL]". iApply (view_at_mono with "SL"); [done|].
      by apply SeenLogview_map_mono. }

    have EL' : ElimStackLocalEvents T' M' Mb'.
    { (* connecting local events *)
      intros e [->%elem_of_singleton|InM]%elem_of_union.
      - exists (inl ppId). split; [done|]. rewrite EqMb' -/ppId. set_solver-.
      - apply (ElimStackLocalEvents_mono EL0); [by etrans|done..]. }

    iAssert (StackViews γb b G' Gb' T') with "[SV BI]" as "#SV'".
    { iIntros (e eV ve [[EqeV|[-> <-]]%lookup_app_1 IS]).
      - iDestruct ("SV" $! e eV with "[%//]") as "[SV EL]". iSplitL "SV".
        + iApply (view_at_mono with "SV"); [done|]. by apply SeenLogview_map_mono.
        + iDestruct "EL" as (Mb) "[SL %EL]". iExists Mb. iSplitL.
          * iApply (view_at_mono' with "SL"); [done|].
            iClear "#". rewrite -(view_at_objective_iff (StackInv _ _ _ _ _)).
            iApply (view_at_mono with "BI"); [reflexivity|].
            apply StackLocalLite_upgrade.
          * iPureIntro. by apply (ElimStackLocalEvents_mono EL).
      - iFrame "SL'". iExists Mb'. rewrite (StackLocalLite_from _ _ _ _ Gb').
        iFrame "SLb'". simpl. by iPureIntro. }

    iAssert (@{V'} graph_snap γg G' M')%I as "#Gs3". { iFrame "Gs' SL'". }

    iAssert (@{V'} StackLocal' N γg s G' M')%I as "#SSL'".
    { iFrame "Gs3". iExists b, x, γsb, γsx, γb, γx, γ. iFrame "MT sbs' sx'".
      iExists Gb', Mb', Gx0, Mx0, T'. by iFrame (EL') "SLb' ELx0' LT' II". }

    iIntros "!>".
    iExists 0, V', G', dummy_eid, ppIde, dummy_sevt, EmpPop.
    iExists Vpp', M'.

    iDestruct "BI" as "[B1 B2]". iDestruct "E" as "[E1 E2]".
    iDestruct "oT'" as "[T1 T2]". iSplitL "G1 B1 E1 T1".
    { iFrame "sV3 SSL'". iSplitL.
      - iNext. iExists _,_,_,_,_,_. iExists _,_,_. by iFrame "MT ∗".
      - iPureIntro. split; [done|]. right; left. do 8 (split; [done|]).
        (* this is already in StackConsistency,
          we just have it here for convenience. *)
        intros e UM Ine.
        eapply (stk_cons_non_empty _ SC' ppIde);
          [by rewrite lookup_app_1_eq|done| |done].
        clear -Ine. rewrite /= elem_of_union. right. exact Ine. }
    iIntros "HΦ !>". iSplitR "HΦ".
    { (* re-establish our internal invariant *)
      iNext. iExists Vbx, G', Gb', Gx, T'. by iFrame "SV' ∗". }
    iIntros "_".
    wp_let. wp_op. wp_if. by iApply "HΦ".

  - (* successful pop, commit *)
    destruct CASE as (Lt0 & ISps & ISpp & -> & FRSo &
                      EqGb' & Eqso & Eqco & InpsMb & InppMb & NInMb0 & EqLps).
    destruct EqLps as (eV & Eqps & EqeV & SubeV).
    set ppId := length Gb.(Es).

    (* we know that psId is simulated by an unmatched psIde in the elim stack graph. *)
    destruct (StackProps_unmatched_push_2 (ub:=psId) SP)
      as (psIde & EqTps & [v' (eVps & Eqev' & EqeVps)%list_lookup_fmap_inv'] & UPp).
    { split; [|done]. exists v. by rewrite Eqps /= EqeV ISps. }
    (* also know that psIde has the same value v *)
    destruct (stk_base_stack_map SP _ _ _ _ EqeVps EqTps Eqps) as [Eqvv LeeV].
    rewrite -Eqvv EqeV ISps in Eqev'.
    inversion Eqev'; clear Eqev'; subst v'. rewrite EqeV ISps in Eqvv.
    symmetry in Eqvv.

    have Eqps' : Gb'.(Es) !! psId = Some eV.
    { rewrite EqGb'. by apply lookup_app_l_Some. }
    have InSob': (psId, ppId) ∈ Gb'.(so). { rewrite Eqso. set_solver-. }
    have InCob': (psId, ppId) ∈ Gb'.(com). { rewrite Eqco. set_solver-. }

    set M'' := eVps.(ge_lview).
    destruct LeeV as (LeeVps & ISV & ?).
    specialize (ISV _ Eqvv). simpl in ISV.
    have SubVpsp : eV.(ge_view).(dv_comm) ⊑ Vpp.(dv_comm).
    { destruct (stk_cons_matches _ SCb' _ _ InCob')
        as (_ & eV1 & eV2 & _ & Eq1 & Eq2 & _ & _ & SubV).
      rewrite Eqps' in Eq1. rewrite Eqpp in Eq2.
      apply Some_inj in Eq1 as <-. apply Some_inj in Eq2 as <-. done. }
    have SubVpp : eV.(ge_view).(dv_in) ⊑ Vpp.(dv_comm).
    { destruct (egcons_so _ ECb' _ _ InSob') as (eV1 & eV2 & Eq1 & Eq2 & SubV).
      rewrite Eqps' in Eq1. rewrite Eqpp in Eq2.
      apply Some_inj in Eq1 as <-. apply Some_inj in Eq2 as <-.
      apply ge_le_view in SubV. simpl in SubV. done. }
    have SubVin : eVps.(ge_view).(dv_in) ⊑ Vpp'.(dv_comm).
    { rewrite /= /V'. etrans; [apply LeeVps|exact SubVpp]. }

    assert (GIP := graph_insert_edge_props_base _ _ _ (Pop v) _ _
                      EqeVps SubM EGCs SubVin).
    rewrite -/M'' in GIP.
    destruct GIP as [b' [ppIde M' egV' G' [NEqed Lted] LeG' [Subm' SubeV'] SubM'
                        [Inps' Inpp'] FRpp EGCs']].

    assert (EqG' := graph_insert_edge_eq psIde egV' G b').
    rewrite -/G' -/ppIde in EqG'. destruct EqG' as (_ & EqEs' & EqSo' & EqCo').

    have NI : ∀ e1 e2, (e1, e2) ∈ G.(com) → e1 ≠ ppIde ∧ e2 ≠ ppIde.
    { move => ?? /(gcons_com_included G) [/= ??]. lia. }
    have EqLT : ppIde = length T. { by rewrite (stk_dom_length SP). }
    have EqTpp : T' !! ppIde = Some (inl ppId).
    { rewrite EqLT. by apply list_lookup_middle. }

    have SubVps' : eVps.(ge_view).(dv_comm) ⊑ V'.
    { etrans; [exact ISV|exact SubVpsp]. }
    assert (SC' : StackConsistent G').
    { destruct SC as [SCNZ SCMA SCFN SCME SCNE SCSO SCLIFO SCMO]. constructor.
      - apply stack_positive_value_insert; [|exact SCNZ].
        clear; simpl => ?; by inversion 1.
      - (* 2 *) by apply (stack_matches_value_insert_edge _ _ _ _ _ _ EqeVps Eqvv).
      - (* 3 *)
        clear -UPp SCFN SCSO. rewrite SCSO in UPp.
        by apply (stack_com_functional_insert_edge _ _ _ _ UPp SCFN).
      - (* 4 *) apply stack_unmatched_pop_empty_insert_edge, SCME.
      - (* 5 *) by apply stack_empty_unmatched_push_insert_edge.
      - (* 6 *) by rewrite EqSo' EqCo' SCSO.
      - (* LIFO *)
        apply (stack_LIFO_insert_edge _ _ _ _ _ _ EqeVps Eqvv); [|done..].
        intros u1 o1 oV1 In1 [Ltu1 Lto1] Eqo1 Inu1 InpsIde. destruct (NI _ _ In1).
        rewrite 2!elem_of_union elem_of_singleton.
        intros [InM|[->|InM']]; [|done|]; last first.
        { (* o1 eco psIde. But psIde eco o1, and psIde ≠ o1 ==> contradiction *)
          apply (SCMO _ _ _ EqeVps) in InM'. clear -Lto1 InM'. lia. }
        rewrite -SCSO in In1.
        destruct (StackProps_is_Some_so SP In1) as [[eu1 Eqeu1] [eo1 Eqeo1]].
        have SR := In1. apply (stk_so_sim SP _ _ _ _ Eqeu1 Eqeo1) in SR.
        inversion SR as [ub ob InSob|ux ox (InSox & IU & IO)];
          clear SR; subst eu1 eo1.
        { (* if (u1, o1) from the base stack, we piggyback on the base stack LIFO *)
          have InCob1 : (ub, ob) ∈ Gb'.(com).
          { rewrite -(stk_cons_so_com _ SCb') Eqso. set_solver+InSob. }
          have InCob2 : (psId, ppId) ∈ Gb'.(com).
          { rewrite -(stk_cons_so_com _ SCb') Eqso. set_solver-. }
          have NEqub : ub ≠ psId.
          { clear -InSob FRSo. intros ->. by apply (FRSo _ InSob). }
          destruct (StackProps_is_Some_l_1 SP Eqeo1) as [eVob EqeVob].
          have EqeVob' :=
            prefix_lookup_Some _ _ _ _ EqeVob (graph_sqsubseteq_E _ _ SubGb).
          apply (stk_cons_LIFO _ SCb' _ _ _ _ _ _ _ InCob1 InCob2 NEqub
                  EqeVob' Eqps' Eqpp); simpl.
          - apply (stk_base_stack_logview SP _ _ _ _ Eqeu1 EqTps _ _
                    EqeVps Eqps Inu1).
          - apply SubMb0. apply EL0 in InM as (eo & Eqeo & InMb0).
            rewrite (prefix_lookup_Some _ _ _ _ Eqeo LeT0) in Eqeo1.
            clear -Eqeo1 InMb0. apply Some_inj in Eqeo1 as ->. done.
          - apply (stk_base_stack_logview SP _ _ _ _ EqTps Eqeo1 _ _
                      Eqo1 EqeVob InpsIde). }
        (* If (u1, o1) is an exchange pair, we know that o1 = S u1. With
          psIde < o1, we have psIde ≤ u1. But we also have u1 < psIde
          ==> contradiction *)
        assert (Eqo1' := stk_xchg_consec SP _ _ _ _ Eqeu1 Eqeo1 In1).
        clear -Ltu1 Eqo1' Lto1. lia.
      - clear -SubM' SCMO. by apply graph_insert_xo_eco. }

    (* TODO: dup with push case also *)
    have SP' : StackProps G' Gb' Gx T' true.
    { constructor.
      - by rewrite 2!app_length /= (stk_dom_length SP).
      - by apply (StackProps_inj_insert _ _ FRT), (stk_event_id_map_inj SP).
      - rewrite EqGb'. apply StackProps_dom_l_insert, (stk_event_id_map_dom_l SP).
      - by apply StackProps_dom_r_insert_l, (stk_event_id_map_dom_r SP).
      - intros ?? eV' eVb EqG [EqT|[-> <-%inl_inj]]%lookup_app_1 Eqee.
        + eapply (stk_base_stack_map SP); [|exact EqT|].
          * rewrite lookup_app_l in EqG; [done|].
            by apply (StackProps_is_Some_1 SP), lookup_lt_is_Some in EqT.
          * clear -EqT Eqee EqGb' FRT. rewrite EqGb' in Eqee.
            apply lookup_app_1 in Eqee as [?|[-> <-]]; [done|].
            exfalso. apply FRT. by apply elem_of_list_lookup_2 in EqT.
        + rewrite (stk_dom_length SP) in EqG.
          apply lookup_last_Some_2 in EqG as ->. rewrite Eqpp in Eqee.
          clear -Eqee ISpp LeV0. apply Some_inj in Eqee as <-. done.
      - intros ???? EqG [EqT|[_ Eqr]]%lookup_app_1; [|clear -Eqr; done].
        eapply (stk_xchg_map SP); [|exact EqT].
        rewrite lookup_app_l in EqG; [done|].
        by apply (StackProps_is_Some_1 SP), lookup_lt_is_Some in EqT. 
      - intros ?? [EqT|[_ Eqr]]%lookup_app_1; [|clear -Eqr; done].
        destruct (stk_xchg_push_pop SP _ _ EqT) as (ee2 & e2 & Eqee2 & InSo).
        exists ee2, e2. split ; [by apply lookup_app_l_Some|].
        rewrite EqSo'. set_solver+InSo.
      - intros e1 e2 ee1 ee2 Eq1 Eq2.
        rewrite EqSo' Eqso elem_of_union elem_of_singleton.
        apply lookup_app_1 in Eq1 as [Eq1|[-> <-]]; last first.
        { rewrite -EqLT. split.
          - intros [[? _]%pair_inj|?%gcons_not_in_so_l]; done.
          - clear -Eqps. intros SR. exfalso. inversion SR as [?? InSo|]; clear SR.
            move : InSo. rewrite elem_of_union elem_of_singleton.
            intros [[<- _]%pair_inj|?%gcons_not_in_so_l]; [|done].
            by apply lookup_length_not_Some in Eqps. }
        apply lookup_app_1 in Eq2 as [Eq2|[-> <-]].
        + rewrite (stk_so_sim SP _ _ _ _ Eq1 Eq2). split.
          * intros [[_ Eq']%pair_inj|SR].
            { exfalso. clear -Eq2 Eq' SP. subst e2.
              by apply (StackProps_is_Some_1 SP), lookup_length_not_is_Some in Eq2. }
            { revert SR; clear. apply sum_relation_impl; [|done].
              intros ?? _ _. set_solver. }
          * intros SR. right. revert SR. apply sum_relation_impl; [|done].
            intros eb1 eb2 -> ->. rewrite elem_of_union elem_of_singleton.
            clear -Eq2 FRT. intros [[_ ->]%pair_inj|?]; [|done]. exfalso.
            apply FRT. by apply elem_of_list_lookup_2 in Eq2.
        + rewrite -EqLT. split.
          * intros [[-> _]%pair_inj|?%gcons_not_in_so_r]; [|done].
            rewrite EqTps in Eq1. clear -Eq1. apply Some_inj in Eq1 as <-.
            constructor. set_solver-.
          * clear -SP EqTps Eq1. intros SR. left.
            inversion SR as [?? InSo|]; clear SR. subst ee1.
            f_equal. move : InSo. rewrite elem_of_union elem_of_singleton.
            intros [[-> _]%pair_inj|?%gcons_not_in_so_r]; [|done].
            (* INJ ELIM: stk_so_sim right-to-left *)
            by rewrite -(stk_event_id_map_inj SP _ _ _ EqTps Eq1).
      - (* consecutiveness of exchange pair *)
        intros ee1 ee2 e1 e2 Eqe1 Eqe2.
        rewrite /= elem_of_union elem_of_singleton -/ppId.
        intros [[-> ->]%pair_inj|InG].
        { rewrite EqTpp in Eqe2. clear -Eqe2. by apply Some_inj in Eqe2. }
        rewrite -(stk_cons_so_com _ SC) EqLT in NI. destruct (NI _ _ InG).
        rewrite lookup_app_1_ne in Eqe1; [|done].
        rewrite lookup_app_1_ne in Eqe2; [|done].
        apply (stk_xchg_consec SP _ _ _ _ Eqe1 Eqe2 InG).
      - (* logview of base stack *)
        rewrite EqGb'.
        apply StackProps_stk_logview_insert;
          [apply (stk_dom_length SP)|apply (egcons_logview_closed _ EGCs)
          |apply (stk_event_id_map_dom_l SP)|..|done
          |apply (stk_base_stack_logview SP)].
        clear -SP EL0 SubMb0 LeT0 SubeV Eqps EqeVps EqTps. intros ee1 e1 Eqee1.
        rewrite /= 2!elem_of_union elem_of_singleton. intros [InM|[->|InM]].
        + apply EL0 in InM as (ee' & Eqee' & In').
          rewrite (prefix_lookup_Some _ _ _ _ Eqee' LeT0) in Eqee1.
          apply Some_inj in Eqee1 as ->. by apply SubMb0, In'.
        + exfalso. apply lookup_lt_Some in Eqee1.
          rewrite /ppIde (stk_dom_length SP) in Eqee1. lia.
        + apply SubeV,
            (stk_base_stack_logview SP _ _ _ _ Eqee1 EqTps _ _ EqeVps Eqps InM).
    }

    iMod (graph_master_update _ _ _ LeG' with "Gm") as "[[G1 G2] #Gs']"; [done..|].
    set E' := G'.(Es).
    have LeE' : E ⊑ E' by apply LeG'.

    (* second use of StackViews *)
    iAssert (@{V'} SeenLogview E' M')%I with "[SV]" as "#SL'".
    { rewrite -SeenLogview_union' -SeenLogview_insert'.
      iSplitR; last iSplitL; [..| |done].
      - iDestruct "Gs1'" as "[_ SL]". iApply (view_at_mono with "SL"); [done|].
        apply SeenLogview_map_mono; [|done]. by etrans.
      - by iDestruct ("SV" $! psIde eVps with "[%//]") as "[$ _]". }

    have EL' : ElimStackLocalEvents T' M' Mb'.
    { (* connecting local events *)
      have LeT0' : T0 ⊑ T' by etrans.
      intros e. rewrite 2!elem_of_union elem_of_singleton.
      intros [InM|[->|InM'']].
      - by apply (ElimStackLocalEvents_mono EL0).
      - by exists (inl ppId).
      - have IS := egcons_logview_closed _ EGCs _ _ EqeVps _ InM''.
        apply (StackProps_is_Some _ SP) in IS as [eo Eqeo].
        exists eo. split. { by apply lookup_app_l_Some. }
        destruct eo as [eo|]; [|done].
        apply SubeV, (stk_base_stack_logview SP _ _ _ _ Eqeo EqTps _ _ EqeVps Eqps InM''). }

    iAssert (StackViews γb b G' Gb' T') with "[SV BI]" as "#SV'".
    { iIntros (e eVe ve [[EqeVe|[-> <-]]%lookup_app_1 IS]).
      - iDestruct ("SV" $! e eVe ve with "[%//]") as "[SV EL]". iSplitL "SV".
        + iApply (view_at_mono with "SV"); [done|]. by apply SeenLogview_map_mono.
        + iDestruct "EL" as (Mb) "[SL %EL]". iExists Mb. iSplitL.
          * iApply (view_at_mono' with "SL"); [done|].
            iClear "#". rewrite -(view_at_objective_iff (StackInv _ _ _ _ _)).
            iApply (view_at_mono with "BI"); [reflexivity|].
            apply StackLocalLite_upgrade.
          * iPureIntro. by apply (ElimStackLocalEvents_mono EL).
      - iFrame "SL'". iExists Mb'. rewrite (StackLocalLite_from _ _ _ _ Gb').
        iFrame "SLb'". simpl. by iPureIntro. }

    iAssert (@{V'} graph_snap γg G' M')%I as "#Gs3". { iFrame "Gs' SL'". }
    iAssert (@{V'} StackLocal' N γg s G' M')%I as "#SSL'".
    { iFrame "Gs3". iExists b, x, γsb, γsx, γb, γx, γ. iFrame "MT sbs' sx'".
      iExists Gb', Mb', Gx0, Mx0, T'. by iFrame (EL') "SLb' ELx0' LT' II". }

    iIntros "!>".
    iExists v, V', G', psIde, ppIde, (Push v), (Pop v).
    iExists Vpp', M'.

    iDestruct "BI" as "[B1 B2]". iDestruct "E" as "[E1 E2]".
    iDestruct "oT'" as "[T1 T2]". iSplitL "G1 B1 E1 T1".
    { iFrame "sV3 SSL'". iSplitL.
      - iNext. iExists _,_,_,_,_,_. iExists _,_,_. by iFrame "MT ∗".
      - iPureIntro. split; [done|]. right; right.
        do 11 (split; [done|]). by exists eVps. }
    iIntros "HΦ !>". iSplitR "HΦ".
    { (* re-establish our internal invariant *)
      iNext. iExists Vbx, G', Gb', Gx, T'. by iFrame "SV' ∗". }
    iIntros "_". wp_let. wp_op. rewrite bool_decide_false; [|clear -Lt0; lia].
    wp_if. by iApply "HΦ".
Qed.

(* TODO : this proof is general w.r.t. to try_pop *)
Lemma pop_spec :
  pop_spec' (pop try_pop' ex.(exchange)) StackLocal' StackInv'.
Proof.
  intros N DISJ s tid γg G0 M V.
  iIntros "#sV #SL" (Φ) "AU".
  iLöb as "IH". wp_rec.
  awp_apply (try_pop_spec with "sV SL"); [done..|].
  iApply (aacc_aupd with "AU"); [done|].
  iIntros (G) "QI".
  iAaccIntro with "QI"; first by eauto with iFrame.
  iIntros (v V' G' psId ppId ps pp Vpp M') "(QI & sV' & Local & F & CASE) !>".
  iDestruct "CASE" as "[CASE|[CASE|CASE]]".
  - iLeft. iDestruct "CASE" as %(-> & -> & ->).
    iFrame "QI". iIntros  "AU !> _".
    wp_let. wp_op. wp_if. by iApply ("IH" with "AU").
  - iRight. iClear "IH". iDestruct "CASE" as %[? ?].
    iExists v, V', G', psId, ppId, ps, pp. iExists Vpp, M'.
    iFrame "QI sV' Local F". iSplitL.
    + by iLeft.
    + iIntros "H !> _". subst v.
      wp_let. wp_op. wp_if. by iApply "H".
  - iRight. iClear "IH". iDestruct "CASE" as %[? ?].
    iExists v, V', G', psId, ppId, ps, pp. iExists Vpp, M'.
    iFrame "QI sV' Local F". iSplitL.
    + by iRight.
    + iIntros "H !> _". wp_let. wp_op. rewrite bool_decide_false; [|lia].
      wp_if. by iApply "H".
Qed.
End proof.

Definition elimination_stack_impl Σ
  `{!noprolG Σ, !inG Σ (graphR sevent), !inG Σ (graphR xchg_event),
    !ro_ptstoG Σ, !inG Σ (mono_listR (leibnizO (event_id + event_id)))}
  (stk : basic_stack_spec Σ) (ex : exchanger_piggyback_spec Σ) 
  : basic_stack_spec Σ := {|
    spec_graph.StackInv_Objective := StackInv'_objective stk ex ;
    spec_graph.StackInv_Fractional := StackInv'_fractional stk ex ;
    spec_graph.StackInv_StackConsistent :=
      StackInv'_StackConsistent_instance stk ex ;
    spec_graph.StackInv_graph_master_acc :=
      StackInv'_graph_master_acc_instance stk ex ;
    spec_graph.StackInv_graph_snap := StackInv'_graph_snap_instance stk ex ;
    spec_graph.StackInv_agree := StackInv'_agree_instance stk ex ;

    spec_graph.StackLocal_graph_snap := StackLocal'_graph_snap_instance stk ex ;
    spec_graph.StackLocal_Persistent := StackLocal'_persistent stk ex ;
    spec_graph.StackLocal_union := StackLocal'_union_instance stk ex ;
    spec_graph.StackLocal_upgrade := StackLocal'_upgrade_instance stk ex ;

    spec_graph.StackLocalLite_graph_snap :=
      StackLocalLite'_graph_snap_instance stk ex ;
    spec_graph.StackLocalLite_Persistent := StackLocalLite'_persistent stk ex ;
    spec_graph.StackLocalLite_Timeless := StackLocalLite'_timeless stk ex ;
    spec_graph.StackLocalLite_from := StackLocalLite'_from_instance stk ex ;
    spec_graph.StackLocalLite_to := StackLocalLite'_to_instance stk ex ;
    spec_graph.StackLocalLite_upgrade :=
      StackLocalLite'_upgrade_instance stk ex ;

    spec_graph.new_stack_spec := new_stack_spec stk ex ;
    spec_graph.try_push_spec := try_push_spec stk ex ;
    spec_graph.push_spec := push_spec stk ex ;
    spec_graph.try_pop_spec := try_pop_spec stk ex ;
    spec_graph.pop_spec := pop_spec stk ex ;
  |}.
