From gpfsl.examples Require Import sflib.

From iris.algebra Require Import auth gset gmap agree.
From iris.algebra Require Import lib.mono_list.
From iris.proofmode Require Import tactics.

From gpfsl.base_logic Require Import meta_data.
From gpfsl.examples.algebra Require Import mono_list_list.
From gpfsl.logic Require Import logatom atomics invariants.

From gpfsl.logic Require Import repeat_loop new_delete.
From gpfsl.examples Require Import map_seq loc_helper.

From stdpp Require Import namespaces.
From gpfsl.logic Require Import logatom.
From gpfsl.examples.omo Require Export omo_event omo_history.

Require Import iris.prelude.options.

Notation omoT := (list (event_id * list event_id))%type.
Notation lhb := hb_ord.

(** Pure definitions and lemmas for OMO **)
Section omo.
Context {eventT absStateT : Type}.
Implicit Types
  (omo : omoT)
  (st : absStateT).

Local Open Scope nat_scope.

(* Typeclass for state transition system *)
Class Interpretable eventT absStateT : Type :=
  {
    (* Initial State *)
    init : absStateT;
    (* Given an event and previous abstract state, interpreted result is new abstract state *)
    step : event_id → omo_event eventT → absStateT → absStateT → Prop
  }.

Inductive interp `{Interpretable eventT absStateT} : list (event_id * omo_event eventT) → absStateT → absStateT → Prop :=
| interp_nil : ∀ (st : absStateT), interp [] st st
| interp_snoc : ∀ e eV eeVs st1 st2 st3, interp eeVs st1 st2 → step e eV st2 st3 → interp (eeVs ++ [(e, eV)]) st1 st3
.

Notation history := (history eventT).

(** Index to an event in [omo]. [eidx] *)
Inductive event_idx : Set :=
| ro_event (gen i' : nat) (* [i']-th read-only operation of generation [gen] *)
| wr_event (gen : nat)  (* the write event of generation [gen] *)
.

Definition gen_of eidx :=
  match eidx with
  | ro_event gen _ => gen
  | wr_event gen => gen
  end.

Definition lookup_omo omo eidx : option event_id :=
  match eidx with
  | ro_event gen i => omo.*2 !! gen ≫= (!!) i
  | wr_event gen => omo.*1 !! gen
  end.

(** "Lexicographic" order of [eidx] *)
Inductive eidx_le : ∀ (eidx1 eidx2 : event_idx), Prop :=
| eidx_le_r_r_1 gen1 i1' gen2 i2'
    (LTgen : gen1 < gen2)
    : eidx_le (ro_event gen1 i1') (ro_event gen2 i2')
| eidx_le_r_r_2 gen i1' i2'
    (LEi' : i1' ≤ i2')
    : eidx_le (ro_event gen i1') (ro_event gen i2')
| eidx_le_r_w gen1 i1' gen2
    (LTgen : gen1 < gen2)
    : eidx_le (ro_event gen1 i1') (wr_event gen2)
| eidx_le_w_r gen1 gen2 i2'
    (LTgen : gen1 ≤ gen2)
    : eidx_le (wr_event gen1) (ro_event gen2 i2')
| eidx_le_w_w gen1 gen2
    (LEgen : gen1 ≤ gen2)
    : eidx_le (wr_event gen1) (wr_event gen2)
.

(** local happens-before implies omo-before. *)
Definition lhb_omo (E : history) omo :=
  ∀ eidx1 eidx2 e1 e2 eV2
    (omo_eidx1 : lookup_omo omo eidx1 = Some e1)
    (omo_eidx2 : lookup_omo omo eidx2 = Some e2)
    (EV2 : E !! e2 = Some eV2)
    (IN_EVIEW : e1 ∈ eV2.(eview)),
    eidx_le eidx1 eidx2.

(** Linearization of [omo]. Defined as flattening of omo into an array of event id *)
Definition lin_of_omo omo :=
  concat ((λ '(e, es), e :: es) <$> omo).

(** Insert (append) read-only operation to the generation [gen] of [omo]. *)
Definition omo_insert_r omo gen e := alter (λ '(e', es'), (e', es'++[e])) gen omo.

(** Insert a new write operation at [gen]th generation *)
Definition omo_insert_w omo gen e es := take gen omo ++ (e, es) :: drop gen omo.

(** Insert a new write operation at the back *)
Definition omo_append_w omo e es := omo ++ [(e, es)].

(** Collects only write events of OMO.
    This is widely used in the invariants of libraries. *)
Definition omo_write_op omo := omo.*1.
(** Collects only read-only events of OMO *)
Definition omo_read_op omo := omo.*2.

(* No [Inj] instance because it's partial *)
Definition omo_inj omo :=
  ∀ eidx1 eidx2 e
    (OMO_LOOKUP1 : lookup_omo omo eidx1 = Some e)
    (OMO_LOOKUP2 : lookup_omo omo eidx2 = Some e),
    eidx1 = eidx2.

(* Prefix relation of two `OMO`'s *)
Definition omo_prefix omo1 omo2 :=
  omo_read_op omo1 `prefixes_of` omo_read_op omo2 ∧
  omo_write_op omo1 ⊑ omo_write_op omo2.

(** Convert an [eidx] into an index in [lin]. *)
Definition eidx_to_lin_idx omo eidx :=
  match eidx with
  | ro_event gen i' => length (concat ((λ '(e, es), e :: es) <$> take gen omo)) + S i'
  | wr_event gen => length (concat ((λ '(e, es), e :: es) <$> take gen omo))
  end.

Inductive interp_omo `{Interpretable eventT absStateT} : history → omoT → absStateT → list absStateT → Prop :=
| interp_omo_nil : ∀ E st, interp_omo E [] st []
| interp_omo_snoc :
  ∀ E e es eV omo st1 st2 st3 stlist,
    E !! e = Some eV ∧
    interp_omo E omo st1 stlist ∧
    last (st1 :: stlist) = Some st2 ∧
    step e eV st2 st3 ∧
    Forall (λ e', ∃ eV', E !! e' = Some eV' ∧ step e' eV' st3 st3 ∧ e < e') es →
    interp_omo E (omo ++ [(e, es)]) st1 (stlist ++ [st3])
.

Definition perm_omo (E : history) omo : Prop :=
  lin_of_omo omo ≡ₚ seq 0 (length E).

(* Definition of linearizability in OMO version *)
Inductive Linearizability_omo (E : history) omo stlist `{Interpretable eventT absStateT} : Prop :=
| Linearizability_omo_intro
    (INTERP_OMO : interp_omo E omo init stlist)
    (LHB_OMO : lhb_omo E omo)
    (PERM_OMO : perm_omo E omo)
.

Definition eid_to_event_valid (E : history) (eeVs : list (event_id * omo_event eventT)) : Prop :=
  Forall (λ '(e, eV), E !! e = Some eV) eeVs.

(* Definition of linearizability (in linearizability history specification) *)
Inductive Linearizability E `{Interpretable eventT absStateT} : Prop :=
  | Linearizability_intro xo lin st
      (XO : xo.*1 = seq 0 (length E)) (* xo (execution order): list (event_id * omo_event) *)
      (EEVS_VALID_XO : eid_to_event_valid E xo) (* Checks whether pairing between event_id and omo_event is valid *)
      (LIN_PERM : lin ≡ₚ xo) (* lin: permutation of xo *)
      (LHB_LIN : lhb E lin.*1) (* linearization order satisfies happens-before order *)
      (INTERP_LIN : interp lin init st) (* linearization order is interpretable *)
  .

Section omo_lemmas.
#[global] Instance eidx_eqdec : EqDecision event_idx.
Proof. solve_decision. Qed.

Lemma interp_omo_length E omo st stlist `{Interpretable eventT absStateT}
    (INTERP_OMO : interp_omo E omo st stlist) :
  length omo = length stlist.
Proof.
  generalize dependent stlist. induction omo using rev_ind; intros.
  - inversion INTERP_OMO; [done|]. apply (f_equal length) in H0. rewrite app_length /= in H0. lia.
  - inversion INTERP_OMO; [done|]. destruct H2 as [_ [H2 _]].
    apply app_inj_2 in H0 as [EQ _]; [|done]. subst omo0.
    specialize (IHomo _ H2). rewrite !app_length /=. lia.
Qed.

Lemma interp_app eeVs1 eeVs2 st1 st2 `{Interpretable eventT absStateT} :
  interp (eeVs1 ++ eeVs2) st1 st2 ↔
  ∃ st3, interp eeVs1 st1 st3 ∧ interp eeVs2 st3 st2.
Proof.
  split; intros.
  - revert st2 H0. induction eeVs2 using rev_ind; intros.
    + exists st2. simplify_list_eq. split; [done|]. apply interp_nil.
    + replace (eeVs1 ++ eeVs2 ++ [x]) with ((eeVs1 ++ eeVs2) ++ [x]) in H0; [|by simplify_list_eq].
      inversion H0.
      { apply (f_equal length) in H2. rewrite app_length /= in H2. lia. }
      apply app_inj_2 in H1 as [-> EQ]; [|done]. inversion EQ. subst x st0 st4. clear EQ.
      specialize (IHeeVs2 _ H2) as [st4 [INTERP1 INTERP2]].
      exists st4. split; [done|]. eapply interp_snoc; try done.
  - revert st2 H0. induction eeVs2 using rev_ind; intros.
    + destruct H0 as [st3 [INTERP1 INTERP2]].
      inversion INTERP2; last first.
      { apply (f_equal length) in H0. rewrite app_length /= in H0. lia. }
      subst st st2. simplify_list_eq. done.
    + destruct H0 as [st3 [INTERP1 INTERP2]].
      inversion INTERP2.
      { apply (f_equal length) in H1. rewrite app_length /= in H1. lia. }
      apply app_inj_2 in H0 as [-> EQ]; [|done]. inversion EQ. subst st0 st5 x. clear EQ.
      replace (eeVs1 ++ eeVs2 ++ [(e, eV)]) with ((eeVs1 ++ eeVs2) ++ [(e, eV)]); [|by simplify_list_eq].
      eapply interp_snoc; try done. apply IHeeVs2. by eexists.
Qed.

Lemma interp_omo_app E omo1 omo2 st1 stlist1 stlist2 `{Interpretable eventT absStateT}
    (EQlen : length omo1 = length stlist1) :
  interp_omo E (omo1 ++ omo2) st1 (stlist1 ++ stlist2) ↔
  ∃ st2, interp_omo E omo1 st1 stlist1 ∧ interp_omo E omo2 st2 stlist2 ∧ last (st1 :: stlist1) = Some st2.
Proof.
  split; intros.
  - generalize dependent stlist2. induction omo2 using rev_ind; intros.
    + apply interp_omo_length in H0 as EQlen'.
      rewrite !app_length EQlen /= Nat.add_0_r in EQlen'. destruct stlist2; last first.
      { simpl in EQlen'. clear -EQlen'. lia. }
      simplify_list_eq.
      have [st3 Hst3] : is_Some (last (st1 :: stlist1)) by rewrite last_is_Some.
      exists st3. split_and!; try done. apply interp_omo_nil.
    + apply interp_omo_length in H0 as EQlen'.
      rewrite !app_length EQlen /= in EQlen'.
      destruct stlist2 using rev_ind; [simpl in *;lia|]. clear IHstlist2.
      have EQlen2 : length omo2 = length stlist2.
      { rewrite app_length /= in EQlen'. lia. }
      replace (omo1 ++ omo2 ++ [x]) with ((omo1 ++ omo2) ++ [x]) in H0; [|by simplify_list_eq].
      replace (stlist1 ++ stlist2 ++ [x0]) with ((stlist1 ++ stlist2) ++ [x0]) in H0; [|by simplify_list_eq].
      inversion H0.
      { apply (f_equal length) in H3. rewrite app_length /= in H3. lia. }
      apply app_inj_2 in H1 as [-> EQ1]; [|done]. apply app_inj_2 in H3 as [-> EQ2]; [|done].
      inversion EQ1. inversion EQ2. subst E0 st0 x x0. clear EQ1 EQ2.
      destruct H5 as (H1 & H2 & H3 & H4 & H5).
      specialize (IHomo2 _ H2) as (st5 & INTERP_OMO1 & INTERP_OMO2 & LAST).
      exists st5. split_and!; try done. eapply interp_omo_snoc. split_and!; try done.
      rewrite last_cons. rewrite last_cons last_app in H3.
      destruct (last stlist2) eqn:Heq; [done|].
      rewrite last_cons in LAST. destruct (last stlist1) eqn:Heq';
      by rewrite -H3 -LAST.
  - generalize dependent stlist2. induction omo2 using rev_ind; intros.
    + destruct H0 as (st3 & INTERP_OMO1 & INTERP_OMO2 & LAST).
      inversion INTERP_OMO2; last first.
      { apply (f_equal length) in H0. rewrite app_length /= in H0. lia. }
      subst E0 st stlist2. simplify_list_eq. done.
    + destruct H0 as (st3 & INTERP_OMO1 & INTERP_OMO2 & LAST).
      inversion INTERP_OMO2.
      { apply (f_equal length) in H2. rewrite app_length /= in H2. lia. }
      apply app_inj_2 in H0 as [-> EQ]; [|done]. inversion EQ. subst E0 st0 stlist2 x. rename stlist into stlist2. clear EQ.
      destruct H2 as (H1 & H2 & H3 & H4 & H5).
      have COND : ∃ st', interp_omo E omo1 st1 stlist1 ∧ interp_omo E omo2 st' stlist2 ∧ last (st1 :: stlist1) = Some st'.
      { exists st3. split_and!; try done. }
      specialize (IHomo2 _ COND).
      replace (omo1 ++ omo2 ++ [(e, es)]) with ((omo1 ++ omo2) ++ [(e, es)]); [|by simplify_list_eq].
      replace (stlist1 ++ stlist2 ++ [st4]) with ((stlist1 ++ stlist2) ++ [st4]); [|by simplify_list_eq].
      eapply interp_omo_snoc. split_and!; try done.
      rewrite last_cons last_app. rewrite !last_cons in H3,LAST.
      destruct (last stlist2) eqn:Heq1; [done|].
      destruct (last stlist1) eqn:Heq2;
      by rewrite LAST H3.
Qed.

Lemma interp_app_inv eeVs1 eeVs2 st1 st2 `{Interpretable eventT absStateT} :
  interp (eeVs1 ++ eeVs2) st1 st2 →
  ∃ st3, interp eeVs1 st1 st3 ∧ interp eeVs2 st3 st2.
Proof. by apply interp_app. Qed.

Lemma lookup_omo_ro_event omo gen i :
  lookup_omo omo (ro_event gen i) = omo_read_op omo !! gen ≫= (!!) i.
Proof. done. Qed.

Lemma lookup_omo_inv_r omo gen i e
    (LOOKUP : lookup_omo omo (ro_event gen i) = Some e) :
  ∃ es,
    omo_read_op omo !! gen = Some es ∧
    es !! i = Some e.
Proof.
  rewrite lookup_omo_ro_event in LOOKUP.
  destruct (omo_read_op omo !! gen) eqn:Heq; [|done].
  simpl in LOOKUP. by exists l.
Qed.

Lemma lookup_omo_wr_event omo gen :
  lookup_omo omo (wr_event gen) = omo_write_op omo !! gen.
Proof. done. Qed.

Lemma interp_omo_take E omo st stlist i `{Interpretable eventT absStateT}
    (INTERP_OMO : interp_omo E omo st stlist) :
  interp_omo E (take i omo) st (take i stlist).
Proof.
  destruct (le_lt_dec (length omo) i) as [LE|LT].
  { have EQlen : length omo = length stlist by eapply interp_omo_length.
    rewrite take_ge; [|done]. rewrite take_ge; [|lia]. done. }
  generalize dependent stlist. induction omo using rev_ind; intros; [simpl in *; lia|].
  inversion INTERP_OMO.
  { apply (f_equal length) in H2. rewrite app_length /= in H2. lia. }
  apply app_inj_2 in H0 as [EQ1 EQ2]; [|done].
  inversion EQ2. subst x omo0 st1 stlist E0. clear EQ2. rename stlist0 into stlist.
  destruct (decide (i = length omo)) as [->|NEQ].
  { have EQlen : length (omo ++ [(e, es)]) = length (stlist ++ [st3]) by eapply interp_omo_length.
    rewrite take_app. rewrite !app_length /= in EQlen. replace (length omo) with (length stlist) by lia.
    rewrite take_app. by destruct H2 as [_ [? _]]. }
  rewrite app_length /= in LT.
  have LT' : i < length omo by lia.
  destruct H2 as [_ [H2 _]]. specialize (IHomo LT' _ H2).
  rewrite take_app_le; [|lia].
  have EQlen : length (omo ++ [(e, es)]) = length (stlist ++ [st3]) by eapply interp_omo_length.
  rewrite !app_length /= in EQlen.
  rewrite take_app_le; [|lia]. done.
Qed.

Lemma lookup_omo_event_valid E omo stlist eidx e `{Interpretable eventT absStateT}
    (OMO_GOOD : Linearizability_omo E omo stlist)
    (LOOKUP : lookup_omo omo eidx = Some e) :
  is_Some (E !! e).
Proof.
  destruct OMO_GOOD. destruct eidx.
  - specialize (interp_omo_take _ _ _ _ (S gen) INTERP_OMO) as INTERP_OMO'.
    rewrite lookup_omo_ro_event /omo_read_op list_lookup_fmap in LOOKUP.
    destruct (omo !! gen) eqn:Heq; [|done]. destruct p as [e' es']. simpl in LOOKUP.
    rewrite (take_S_r _ _ (e', es')) in INTERP_OMO'; [|done].
    inversion INTERP_OMO'.
    { apply (f_equal length) in H2. rewrite app_length /= in H2. lia. }
    apply app_inj_2 in H0 as [-> EQ]; [|done]. inversion EQ. subst E0 st1 e0 es. clear EQ H2.
    destruct H4 as (_ & _ & _ & _ & H1).
    rewrite Forall_lookup in H1. specialize (H1 _ _ LOOKUP) as [eV' [H1 _]]. done.
  - specialize (interp_omo_take _ _ _ _ (S gen) INTERP_OMO) as INTERP_OMO'.
    rewrite lookup_omo_wr_event /omo_write_op list_lookup_fmap in LOOKUP.
    destruct (omo !! gen) eqn:Heq; [|done]. destruct p as [e' es']. simpl in LOOKUP. inversion LOOKUP. subst e'.
    rewrite (take_S_r _ _ (e, es')) in INTERP_OMO'; [|done].
    inversion INTERP_OMO'.
    { apply (f_equal length) in H2. rewrite app_length /= in H2. lia. }
    apply app_inj_2 in H0 as [-> EQ]; [|done]. inversion EQ. subst E0 st1 e0 es. clear EQ H2.
    by destruct H4 as [H1 _].
Qed.

Lemma omo_same omo omo' :
  omo = omo' ↔
  omo_write_op omo = omo_write_op omo' ∧
  omo_read_op omo = omo_read_op omo'.
Proof.
  split; intros; [subst omo; done|].
  destruct H as [H1 H2]. generalize dependent omo'. induction omo; intros.
  - by destruct omo'.
  - destruct omo'; try done.
    inversion H1. inversion H2.
    specialize (IHomo _ H3 H5). subst omo. destruct a, p. simpl in H0, H4.
    subst e l. done.
Qed.

Lemma list_lookup_omo_destruct omo gen info :
  omo !! gen = Some info ↔
  omo_write_op omo !! gen = Some info.1 ∧
  omo_read_op omo !! gen = Some info.2.
Proof.
  split; intros.
  - by split; rewrite list_lookup_fmap H.
  - destruct H as [H1 H2]. generalize dependent info. generalize dependent gen. induction omo; intros.
    + done.
    + destruct gen.
      * simpl in H1, H2. simpl. destruct a, info. inversion H1. inversion H2. done.
      * simpl in H1, H2. simpl. by specialize (IHomo _ _ H1 H2).
Qed.

Lemma list_lookup_omo_destruct' omo gen e es :
  omo !! gen = Some (e, es) ↔
  omo_write_op omo !! gen = Some e ∧
  omo_read_op omo !! gen = Some es.
Proof. apply list_lookup_omo_destruct. Qed.

Lemma list_lookup_omo_from_write_op omo gen e :
  omo_write_op omo !! gen = Some e →
  ∃ es, omo !! gen = Some (e, es).
Proof.
  rewrite /omo_write_op. intros.
  have [x Hx] : is_Some (omo !! gen).
  { rewrite lookup_lt_is_Some. apply lookup_lt_Some in H. by rewrite !fmap_length in H. }
  destruct x as [e' es].
  rewrite !list_lookup_fmap Hx in H. inversion H. subst e'.
  by exists es.
Qed.

Lemma list_lookup_omo_from_read_op omo gen es :
  omo_read_op omo !! gen = Some es →
  ∃ e, omo !! gen = Some (e, es).
Proof.
  rewrite /omo_read_op. intros. apply lookup_lt_Some in H as H'.
  rewrite fmap_length in H'. apply lookup_lt_is_Some in H' as [ees Hees].
  destruct ees as [e es'].
  rewrite list_lookup_fmap Hees in H. inversion H. subst es'.
  by eexists.
Qed.

Lemma list_lookup_omo_write_op_agree omo gen e e' es
    (LOOKUP1 : omo !! gen = Some (e, es))
    (LOOKUP2 : omo_write_op omo !! gen = Some e') :
  e = e'.
Proof.
  rewrite /omo_write_op list_lookup_fmap LOOKUP1 in LOOKUP2.
  inversion LOOKUP2. done.
Qed.

Lemma list_lookup_omo_read_op_agree omo gen e es es'
    (LOOKUP1 : omo !! gen = Some (e, es))
    (LOOKUP2 : omo_read_op omo !! gen = Some es') :
  es = es'.
Proof.
  rewrite /omo_read_op list_lookup_fmap LOOKUP1 in LOOKUP2.
  inversion LOOKUP2. done.
Qed.

Lemma omo_write_op_lt_is_Some omo gen :
  is_Some (omo_write_op omo !! gen) ↔ gen < length omo.
Proof. by rewrite /omo_write_op !list_lookup_fmap !fmap_is_Some lookup_lt_is_Some. Qed.

Lemma omo_write_op_lt_Some omo gen e :
  omo_write_op omo !! gen = Some e → gen < length omo.
Proof. by rewrite -omo_write_op_lt_is_Some. Qed.

Lemma omo_read_op_lt_is_Some omo gen :
  is_Some (omo_read_op omo !! gen) ↔ gen < length omo.
Proof. by rewrite /omo_read_op !list_lookup_fmap !fmap_is_Some lookup_lt_is_Some. Qed.

Lemma omo_read_op_lt_Some omo gen es :
  omo_read_op omo !! gen = Some es → gen < length omo.
Proof. by rewrite -omo_read_op_lt_is_Some. Qed.

Lemma lookup_omo_lt_is_Some omo eidx :
  is_Some (lookup_omo omo eidx) → gen_of eidx < length omo.
Proof.
  destruct eidx; intros.
  - simpl in H. destruct (omo !! gen) eqn:Heq.
    + apply lookup_lt_Some in Heq. done.
    + rewrite list_lookup_fmap Heq /= in H. by inversion H.
  - rewrite /= lookup_lt_is_Some fmap_length in H. done.
Qed.

Lemma lookup_omo_lt_Some omo eidx e :
  lookup_omo omo eidx = Some e → gen_of eidx < length omo.
Proof. intros. by apply lookup_omo_lt_is_Some. Qed.

Lemma omo_write_op_length omo :
  length omo = length (omo_write_op omo).
Proof. by rewrite /omo_write_op !fmap_length. Qed.

Lemma omo_read_op_length omo :
  length omo = length (omo_read_op omo).
Proof. by rewrite /omo_read_op !fmap_length. Qed.

Lemma omo_stlist_length E omo stlist `{Interpretable eventT absStateT}
    (OMO_GOOD : Linearizability_omo E omo stlist) :
  length omo = length stlist.
Proof.
  destruct OMO_GOOD. clear LHB_OMO PERM_OMO.
  generalize dependent stlist. induction omo using rev_ind; intros.
  - inversion INTERP_OMO.
    + done.
    + apply (f_equal length) in H0. rewrite app_length /= in H0. lia.
  - inversion INTERP_OMO.
    + done.
    + rewrite !app_length /=.
      destruct H2 as [_ [H2 _]].
      apply app_inj_2 in H0 as [-> _]; [|done].
      specialize (IHomo _ H2). rewrite IHomo. done.
Qed.

Lemma lookup_omo_mono omo1 omo2 eidx e
    (LOOKUP : lookup_omo omo1 eidx = Some e)
    (PREFIX : omo_prefix omo1 omo2) :
  lookup_omo omo2 eidx = Some e.
Proof.
  destruct eidx.
  - destruct PREFIX as [H1 H2].
    destruct (omo_read_op omo1 !! gen) eqn:Heq1; destruct (omo_read_op omo2 !! gen) eqn:Heq2;
    specialize (H1 gen) as H3; rewrite Heq1 Heq2 /= in H3; try done.
    + rewrite lookup_omo_ro_event Heq1 /= in LOOKUP.
      rewrite lookup_omo_ro_event Heq2 /=.
      by eapply prefix_lookup_Some.
    + rewrite lookup_omo_ro_event Heq1 /= in LOOKUP. done.
    + rewrite lookup_omo_ro_event Heq1 /= in LOOKUP. done.
  - destruct PREFIX as [H1 H2].
    rewrite lookup_omo_wr_event in LOOKUP. rewrite lookup_omo_wr_event.
    by eapply prefix_lookup_Some.
Qed.

Lemma omo_prefix_refl omo :
  omo_prefix omo omo.
Proof. done. Qed.

Lemma omo_prefix_trans omo1 omo2 omo3
    (PREFIX1 : omo_prefix omo1 omo2)
    (PREFIX2 : omo_prefix omo2 omo3) :
  omo_prefix omo1 omo3.
Proof.
  destruct PREFIX1 as [SubR1 SubW1].
  destruct PREFIX2 as [SubR2 SubW2].
  split.
  - by transitivity (omo_read_op omo2).
  - by transitivity (omo_write_op omo2).
Qed.

Global Instance omo_prefix_Reflexive : Reflexive omo_prefix := omo_prefix_refl.
Global Instance omo_prefix_Transitive : Transitive omo_prefix := omo_prefix_trans.

Lemma omo_write_op_take omo gen :
  omo_write_op (take gen omo) = take gen (omo_write_op omo).
Proof. by rewrite /omo_write_op !fmap_take. Qed.

Lemma omo_write_op_drop omo gen :
  omo_write_op (drop gen omo) = drop gen (omo_write_op omo).
Proof. by rewrite /omo_write_op !fmap_drop. Qed.

Lemma omo_read_op_take omo gen :
  omo_read_op (take gen omo) = take gen (omo_read_op omo).
Proof. by rewrite /omo_read_op !fmap_take. Qed.

Lemma omo_read_op_drop omo gen :
  omo_read_op (drop gen omo) = drop gen (omo_read_op omo).
Proof. by rewrite /omo_read_op !fmap_drop. Qed.

Lemma lookup_omo_take omo gen eidx
    (LT : gen_of eidx < gen) :
  lookup_omo (take gen omo) eidx = lookup_omo omo eidx.
Proof. by destruct eidx; simpl; rewrite fmap_take lookup_take. Qed.

Lemma lookup_omo_drop omo gen eidx :
  lookup_omo (drop gen omo) eidx
  = match eidx with
    | wr_event gen' => lookup_omo omo (wr_event (gen + gen'))
    | ro_event gen' idx => lookup_omo omo (ro_event (gen + gen') idx)
  end.
Proof. by destruct eidx; simpl; rewrite fmap_drop lookup_drop. Qed.

Lemma omo_prefix_take omo gen :
  omo_prefix (take gen omo) omo.
Proof.
  split.
  - rewrite /prefixes /map_included /map_relation. intros.
    destruct (omo_read_op (take gen omo) !! i) eqn:Heq.
    + apply lookup_lt_Some in Heq as LT. rewrite -omo_read_op_length take_length in LT.
      rewrite /omo_read_op fmap_take lookup_take in Heq; [|lia]. rewrite Heq /=. done.
    + simpl. by destruct (omo_read_op omo !! i).
  - rewrite /omo_write_op fmap_take. apply prefix_take.
Qed.

Lemma lin_of_omo_empty :
  lin_of_omo [] = [].
Proof. done. Qed.

Lemma length_concat_fmap_take_plus_S (f : _ → list event_id) gen1' omo x N
    (GEN1 : omo !! gen1' = Some x) :
  length (concat (f <$> take (gen1' + S N) omo))
  = length (concat (f <$> take gen1' omo)) + (length (f x) + length (concat (f <$> take N (drop (S gen1') omo)))).
Proof.
  apply lookup_lt_Some in GEN1 as LEgen1'.
  rewrite -{1}(take_drop gen1' omo).
  rewrite take_add_app; last first. { rewrite take_length. lia. }
  rewrite fmap_app concat_app app_length.
  rewrite (drop_S _ _ _ GEN1). rewrite firstn_cons fmap_cons /=.
  rewrite app_length. done.
Qed.

Lemma eidx_to_lin_idx_inj omo eidx1 eidx2 e
    (OMO_LOOKUP1 : lookup_omo omo eidx1 = Some e)
    (OMO_LOOKUP2 : lookup_omo omo eidx2 = Some e)
    (EQlin : eidx_to_lin_idx omo eidx1 = eidx_to_lin_idx omo eidx2) :
  eidx1 = eidx2.
Proof.
  unfold eidx_to_lin_idx in *.
  set (f := λ '(e0, es), e0 :: es) in *.
  destruct eidx1 as [gen1 i1|gen1], eidx2 as [gen2 i2|gen2].
  - case (decide (gen1 = gen2)) as [->|NEgen].
    { have EQ : i1 = i2 by lia. subst i1. done. }
    exfalso.
    wlog: gen1 gen2 i1 i2 OMO_LOOKUP1 OMO_LOOKUP2 EQlin NEgen / gen1 < gen2.
    { destruct (le_lt_dec gen1 gen2) as [LE|LT].
      - intros. apply (H gen1 gen2 i1 i2); try done. lia.
      - intros. apply (H gen2 gen1 i2 i1); try done. }
    intros LTgen.
    have [N EQ] : ∃ N, gen2 = gen1 + (S N) by exists (gen2 - gen1 - 1); lia. subst gen2.
    have {}EQlin : length (concat (f <$> take gen1 omo)) + i1 = length (concat (f <$> take (gen1 + S N) omo)) + i2 by lia.
    destruct (omo !! gen1) eqn:Heq; last first.
    { rewrite lookup_omo_ro_event /omo_read_op list_lookup_fmap Heq /= in OMO_LOOKUP1. done. }
    destruct p as [e1 es1].
    erewrite length_concat_fmap_take_plus_S in EQlin; [|done]. simpl in EQlin.
    assert (i1 = S (length es1 + length (concat (f <$> take N (drop (S gen1) omo)))) + i2) as ->; try lia.
    rewrite lookup_omo_ro_event /omo_read_op list_lookup_fmap Heq /= in OMO_LOOKUP1.
    apply lookup_lt_Some in OMO_LOOKUP1. lia.
  - exfalso. destruct (le_lt_dec gen1 gen2) as [LE|LT].
    + have LT : gen1 < gen2 by destruct (decide (gen1 = gen2)) as [<-|NE]; lia.
      destruct (omo !! gen1) eqn:Heq; [|by rewrite lookup_omo_ro_event /omo_read_op list_lookup_fmap Heq /= in OMO_LOOKUP1].
      destruct p as [e1 es1].
      have [N EQ] : ∃ N, gen2 = gen1 + (S N) by exists (gen2 - gen1 - 1); lia. subst gen2.
      erewrite length_concat_fmap_take_plus_S in EQlin; [|done]. simpl in EQlin.
      have EQ : i1 = length es1 + length (concat (f <$> take N (drop (S gen1) omo))) by lia.
      rewrite EQ lookup_omo_ro_event /omo_read_op list_lookup_fmap Heq /= in OMO_LOOKUP1.
      apply lookup_lt_Some in OMO_LOOKUP1. lia.
    + have [N EQ] : ∃ N, gen1 = gen2 + (S N) by exists (gen1 - gen2 - 1); lia. subst gen1.
      destruct (omo !! gen2) eqn:Heq; last first.
      { rewrite lookup_omo_wr_event /omo_write_op list_lookup_fmap Heq /= in OMO_LOOKUP2. done. }
      erewrite length_concat_fmap_take_plus_S in EQlin; [|done]. simpl in EQlin. lia.
  - exfalso. destruct (le_lt_dec gen1 gen2) as [LE|LT].
    + have LT : gen1 < gen2 by destruct (decide (gen1 = gen2)) as [<-|NE]; lia.
      have [N EQ] : ∃ N, gen2 = gen1 + (S N) by exists (gen2 - gen1 - 1); lia. subst gen2.
      destruct (omo !! gen1) eqn:Heq; last first.
      { rewrite lookup_omo_wr_event /omo_write_op list_lookup_fmap Heq /= in OMO_LOOKUP1. done. }
      erewrite length_concat_fmap_take_plus_S in EQlin; [|done]. simpl in EQlin. lia.
    + have [N EQ] : ∃ N, gen1 = gen2 + (S N) by exists (gen1 - gen2 - 1); lia. subst gen1.
      destruct (omo !! gen2) eqn:Heq; last first.
      { rewrite lookup_omo_ro_event /omo_read_op list_lookup_fmap Heq /= in OMO_LOOKUP2. done. }
      destruct p as [e2 es2].
      erewrite length_concat_fmap_take_plus_S in EQlin; [|done]. simpl in EQlin.
      have EQ : i2 = length es2 + length (concat (f <$> take N (drop (S gen2) omo))) by lia.
      rewrite EQ lookup_omo_ro_event /omo_read_op list_lookup_fmap Heq /= in OMO_LOOKUP2.
      apply lookup_lt_Some in OMO_LOOKUP2. lia.
  - destruct (decide (gen1 = gen2)) as [->|NE]; [done|]. exfalso.
    wlog: gen1 gen2 OMO_LOOKUP1 OMO_LOOKUP2 EQlin NE / gen1 < gen2.
    { destruct (le_lt_dec gen1 gen2) as [LE|LT].
      - have LT : gen1 < gen2 by lia. intros. by apply (H gen1 gen2).
      - intros. by apply (H gen2 gen1). }
    intros LT.
    have [N EQ] : ∃ N, gen2 = gen1 + (S N) by exists (gen2 - gen1 - 1); lia. subst gen2.
    destruct (omo !! gen1) eqn:Heq; last first.
    { rewrite lookup_omo_wr_event /omo_write_op list_lookup_fmap Heq /= in OMO_LOOKUP1. done. }
    destruct p as [e1 es1].
    erewrite length_concat_fmap_take_plus_S in EQlin; [|done]. simpl in EQlin. lia.
Qed.

Lemma lin_of_omo_take_drop omo gen :
  lin_of_omo omo = lin_of_omo (take gen omo) ++ lin_of_omo (drop gen omo).
Proof.
  destruct (le_lt_dec (length omo) gen) as [Hgen|Hgen].
  - rewrite take_ge; [|done].
    rewrite drop_ge; [|done].
    by rewrite lin_of_omo_empty app_nil_r.
  - by rewrite /lin_of_omo -concat_app -fmap_app take_drop.
Qed.

Lemma omo_take_drop_lin_singleton omo gen e es
    (LOOKUP : omo !! gen = Some (e, es)) :
  lin_of_omo (drop gen (take (S gen) omo)) = e :: es.
Proof.
  erewrite take_S_r; [|done].
  have Hgen : gen = length (take gen omo).
  { rewrite take_length. apply lookup_lt_Some in LOOKUP. lia. }
  by rewrite {1}Hgen drop_app /lin_of_omo /= app_nil_r.
Qed.

Lemma lin_of_omo_take_S_r omo gen e es
    (LOOKUP : omo !! gen = Some (e, es)) :
  lin_of_omo (take (S gen) omo) = lin_of_omo (take gen omo) ++ (e :: es).
Proof.
  rewrite /lin_of_omo. erewrite take_S_r; [|done]. simplify_list_eq.
  by rewrite concat_app /= app_nil_r.
Qed.

Lemma lin_of_omo_append_w omo e es :
  lin_of_omo (omo_append_w omo e es) = lin_of_omo omo ++ e :: es.
Proof.
  rewrite /lin_of_omo /omo_append_w. simplify_list_eq. by rewrite concat_app /= app_nil_r.
Qed.

Lemma lin_of_omo_insert_w omo gen e es :
  lin_of_omo (omo_insert_w omo gen e es) = lin_of_omo (take gen omo) ++ e :: es ++ lin_of_omo (drop gen omo).
Proof.
  rewrite /lin_of_omo /omo_insert_w /=.
  list_simplifier.
  rewrite concat_app /=.
  list_simplifier.
  done.
Qed.

Lemma lookup_omo_app omo omo' eidx e
    (OMO_LOOKUP : lookup_omo omo eidx = Some e) :
 lookup_omo (omo ++ omo') eidx = Some e.
Proof.
  destruct eidx.
  - rewrite lookup_omo_ro_event /omo_read_op fmap_app. rewrite lookup_omo_ro_event in OMO_LOOKUP.
    destruct (omo_read_op omo !! gen) eqn:Heq; [|done].
    rewrite lookup_app_l; [|by apply lookup_lt_Some in Heq].
    rewrite Heq. done.
  - rewrite lookup_omo_wr_event /omo_write_op fmap_app. rewrite lookup_omo_wr_event in OMO_LOOKUP.
    destruct (omo_write_op omo !! gen) eqn:Heq; [|done].
    rewrite lookup_app_l; [|by apply lookup_lt_Some in Heq].
    rewrite Heq. done.
Qed.

Lemma eidx_to_lin_idx_omo_app omo eidx e e' es'
    (OMO_LOOKUP : lookup_omo omo eidx = Some e) :
  eidx_to_lin_idx omo eidx = eidx_to_lin_idx (omo_append_w omo e' es') eidx.
Proof.
  unfold eidx_to_lin_idx. destruct eidx.
  - rewrite /omo_append_w take_app_le; [done|].
    rewrite lookup_omo_ro_event in OMO_LOOKUP. destruct (omo_read_op omo !! gen) eqn:Heq; [|done].
    apply lookup_lt_Some in Heq. rewrite -omo_read_op_length in Heq. lia.
  - rewrite /omo_append_w take_app_le; [done|].
    rewrite lookup_omo_wr_event in OMO_LOOKUP. destruct (omo_write_op omo !! gen) eqn:Heq; [|done].
    apply lookup_lt_Some in Heq. rewrite -omo_write_op_length in Heq. lia.
Qed.

Lemma lin_of_omo_lookup_lookup_omo omo i e
    (NODUP : NoDup (lin_of_omo omo))
    (LIN_I : lin_of_omo omo !! i = Some e) :
  ∃ eidx,
    i = eidx_to_lin_idx omo eidx ∧
    lookup_omo omo eidx = Some e.
Proof.
  revert i e NODUP LIN_I.
  induction omo using rev_ind; intros; [done|].
  destruct x as [e' es'].
  have H : omo_append_w omo e' es' = omo ++ [(e', es')] by done.
  rewrite -H in NODUP, LIN_I.
  rewrite ->lin_of_omo_append_w,NoDup_app in NODUP. des.
  rewrite lin_of_omo_append_w in LIN_I.
  set len := length (lin_of_omo omo).
  have Hi : i < len ∨ i = len ∨ i > len by lia. des.
  - (* use [i] in IH to get a [eidx] and use it *)
    rewrite lookup_app_l in LIN_I; [|done].
    specialize (IHomo _ _ NODUP LIN_I). des.
    exists eidx. split.
    + erewrite eidx_to_lin_idx_omo_app in IHomo; last done.
      rewrite -H. done.
    + by eapply lookup_omo_app in IHomo0.
  - rewrite list_lookup_middle in LIN_I; [|done]. simplify_eq.
    exists (wr_event (length omo)). list_simplifier. split.
    + subst len. done.
    + by rewrite -!(fmap_length fst) lookup_app_1_eq.
  - rewrite ->lookup_app_r,lookup_cons in LIN_I; [|lia].
    case Esub: (i - len) => [|i']; [lia|]. rewrite -/len Esub in LIN_I.
    have {Esub}Hi : i = len + S i' by lia. subst.
    subst len. unfold lin_of_omo in *. exists (ro_event (length omo) i'). split.
    + rewrite /eidx_to_lin_idx. rewrite take_app_le; [|lia]. rewrite take_ge; [|lia]. done.
    + rewrite -H lookup_omo_ro_event /omo_append_w /omo_read_op fmap_app.
      replace (length omo) with (length omo.*2); [|by rewrite fmap_length].
      rewrite lookup_app_1_eq. done.
Qed.

Lemma lookup_omo_lin_of_omo_lookup omo eidx e
    (OMO_LOOKUP : lookup_omo omo eidx = Some e) :
  lin_of_omo omo !! (eidx_to_lin_idx omo eidx) = Some e.
Proof.
  unfold lin_of_omo, eidx_to_lin_idx.
  set (f := λ '(e0, es), e0 :: es) in *.
  destruct eidx as [gen' i'|gen']; simpl in *.
  - rewrite -{2}(take_drop gen' omo) fmap_app concat_app.
    rewrite lookup_app_r; [|lia].
    replace (length (concat (f <$> take gen' omo)) + S i' - length (concat (f <$> take gen' omo))) with (S i') by lia.
    destruct (omo !! gen') eqn:Heq; last first.
    { rewrite list_lookup_fmap Heq /= in OMO_LOOKUP. done. }
    destruct p as [e' es'].
    rewrite (drop_S _ (e', es')); [|done]. simpl. rewrite lookup_app_l.
    + by rewrite list_lookup_fmap Heq /= in OMO_LOOKUP.
    + rewrite list_lookup_fmap Heq /= in OMO_LOOKUP. by apply lookup_lt_Some in OMO_LOOKUP.
  - rewrite -{2}(take_drop gen' omo) fmap_app concat_app.
    rewrite lookup_app_r; [|lia].
    replace (length (concat (f <$> take gen' omo)) - length (concat (f <$> take gen' omo))) with 0 by lia.
    destruct (omo !! gen') eqn:Heq; last first.
    { rewrite list_lookup_fmap Heq /= in OMO_LOOKUP. done. }
    destruct p as [e' es'].
    rewrite (drop_S _ (e', es')); [|done]. simpl.
    by rewrite list_lookup_fmap Heq /= in OMO_LOOKUP.
Qed.

Lemma event_in_omo (E : history) omo e
    (LIN_PERM : lin_of_omo omo ≡ₚ seq 0 (length E))
    (IS : is_Some (E !! e)) :
  ∃ eidx, lookup_omo omo eidx = Some e.
Proof.
  have NODUP : NoDup (lin_of_omo omo) by by eapply ord_nodup.
  move: IS => /lookup_lt_is_Some /lookup_xo => XO_LOOKUP.
  apply Permutation_sym,Permutation_inj in LIN_PERM as [_ (f & _ & LIN_PERM)].
  specialize (LIN_PERM e). rewrite LIN_PERM in XO_LOOKUP.
  specialize (lin_of_omo_lookup_lookup_omo _ _ _ NODUP XO_LOOKUP). i. des.
  by exists eidx.
Qed.

Lemma logview_in_omo (E : history) omo (M : eView)
    (LIN_PERM : lin_of_omo omo ≡ₚ seq 0 (length E))
    (SubME : set_in_bound M E) :
  set_Forall (λ e, ∃ eidx, lookup_omo omo eidx = Some e) M.
Proof. intros ??. eapply event_in_omo; [done|]. by apply SubME. Qed.

Lemma longer_take i1 i2 (lss : list (list event_id)) (LE: i1 ≤ i2):
    length (concat (take i1 lss))
  ≤ length (concat (take i2 lss)).
Proof.
  apply prefix_length.
  revert lss i2 LE. induction i1; intros; simpl.
  { apply prefix_nil. }
  destruct i2; first lia. destruct lss; first done; simpl.
  apply prefix_app, IHi1; lia.
Qed.

Lemma lin_idx_r_i'_mono omo gen i1' i2' (LEi' : i1' ≤ i2') :
  eidx_to_lin_idx omo (ro_event gen i1') ≤ eidx_to_lin_idx omo (ro_event gen i2').
Proof.
  unfold eidx_to_lin_idx.
  destruct gen; lia.
Qed.

Lemma lin_idx_w_gen_mono omo gen1' gen2' (LEgen : gen1' ≤ gen2') :
  eidx_to_lin_idx omo (wr_event gen1') ≤ eidx_to_lin_idx omo (wr_event gen2').
Proof.
  simpl. do 2 rewrite fmap_take.
  by apply longer_take.
Qed.

Lemma lin_idx_r_w_gen_mono omo gen1 i1' gen2
    (OMO_LOOKUP1 : is_Some (lookup_omo omo (ro_event gen1 i1')))
    (LTgen : gen1 < gen2) :
  eidx_to_lin_idx omo (ro_event gen1 i1') < eidx_to_lin_idx omo (wr_event gen2).
Proof.
  inversion OMO_LOOKUP1 as [e LOOKUP].
  apply lookup_omo_inv_r in LOOKUP as [es [LOOKUP1 LOOKUP2]].
  apply lookup_lt_Some in LOOKUP2; clear e.
  eapply Nat.lt_le_trans; last first.
  { apply lin_idx_w_gen_mono. instantiate (1 := S gen1); lia. }
  unfold eidx_to_lin_idx.
  destruct (omo !! gen1) eqn:Heq; last first.
  { rewrite /omo_read_op list_lookup_fmap Heq /= in LOOKUP1. done. }
  destruct p as [e1 es1]. rewrite (take_S_r _ _ (e1,es1)); [|done].
  rewrite fmap_app concat_app app_length. rewrite app_length /=.
  rewrite list_lookup_fmap Heq /= in LOOKUP1. inversion LOOKUP1. lia.
Qed.

Lemma lin_idx_w_r_gen_mono omo gen1 gen2 i2' (LEgen : gen1 ≤ gen2) :
  eidx_to_lin_idx omo (wr_event gen1) < eidx_to_lin_idx omo (ro_event gen2 i2').
Proof.
  unfold eidx_to_lin_idx. do 2 rewrite fmap_take. eapply Nat.le_lt_trans.
  - apply longer_take. done.
  - lia.
Qed.

Lemma lin_idx_r_gen_mono omo gen1 gen2 i1' i2'
    (OMO_LOOKUP1 : is_Some (lookup_omo omo (ro_event gen1 i1')))
    (LTgen : gen1 < gen2) :
  eidx_to_lin_idx omo (ro_event gen1 i1') < eidx_to_lin_idx omo (ro_event gen2 i2').
Proof.
  eapply Nat.lt_le_trans.
  - by apply lin_idx_r_w_gen_mono.
  - simpl; lia.
Qed.

Lemma omo_extract_eeVs E omo stlist es `{Interpretable eventT absStateT}
    (OMO_GOOD : Linearizability_omo E omo stlist)
    (EIDS_VALID : Forall (λ e, e < length E) es) :
  ∃ eeVs,
    eeVs.*1 = es ∧
    eid_to_event_valid E eeVs.
Proof.
  induction es.
  - exists []. split; try done. unfold eid_to_event_valid. by rewrite Forall_nil.
  - rewrite Forall_cons in EIDS_VALID. destruct EIDS_VALID as [H1 H2].
    specialize (IHes H2) as [eeVs [EQ VALID]].
    rewrite -lookup_lt_is_Some in H1. destruct H1 as [eV Ha].
    exists ((a, eV) :: eeVs). split.
    + rewrite fmap_cons. rewrite EQ. done.
    + unfold eid_to_event_valid. rewrite Forall_cons. done.
Qed.

Lemma omo_write_op_to_eeVs E omo stlist `{Interpretable eventT absStateT}
    (OMO_GOOD : Linearizability_omo E omo stlist) :
  ∃ eeVs,
    eeVs.*1 = omo_write_op omo ∧
    eid_to_event_valid E eeVs.
Proof.
  eapply omo_extract_eeVs; [done|].
  rewrite Forall_lookup. intros. rewrite -lookup_lt_is_Some.
  eapply lookup_omo_event_valid; [done|].
  rewrite -lookup_omo_wr_event in H0. done.
Qed.

Lemma lin_of_omo_to_eeVs E omo stlist `{Interpretable eventT absStateT}
    (OMO_GOOD : Linearizability_omo E omo stlist) :
  ∃ eeVs,
    eeVs.*1 = lin_of_omo omo ∧
    eid_to_event_valid E eeVs.
Proof.
  eapply omo_extract_eeVs; [done|].
  rewrite Forall_lookup. intros. rewrite -lookup_lt_is_Some.
  apply lin_of_omo_lookup_lookup_omo in H0 as [eidx [_ H']].
  - by eapply lookup_omo_event_valid.
  - destruct OMO_GOOD. by eapply ord_nodup.
Qed.

Lemma omo_xo_to_eeVs E omo stlist `{Interpretable eventT absStateT}
    (OMO_GOOD : Linearizability_omo E omo stlist) :
  ∃ eeVs,
    eeVs.*1 = seq 0 (length E) ∧
    eid_to_event_valid E eeVs.
Proof.
  eapply omo_extract_eeVs; [done|].
  rewrite Forall_lookup. intros.
  rewrite lookup_seq in H0. lia.
Qed.

Lemma eid_to_event_valid_agree_from_eid E eeVs eeVs'
    (EEVS_VALID_1 : eid_to_event_valid E eeVs)
    (EEVS_VALID_2 : eid_to_event_valid E eeVs')
    (EID_MATCH : eeVs.*1 = eeVs'.*1) :
  eeVs = eeVs'.
Proof.
  generalize dependent eeVs'. induction eeVs; intros.
  - by destruct eeVs'.
  - destruct eeVs'; try done.
    rewrite !fmap_cons in EID_MATCH. inversion EID_MATCH.
    destruct a, p. simpl in H0. subst e0.
    have [VALID VALID'] : eid_to_event_valid E eeVs ∧ eid_to_event_valid E eeVs'.
    { unfold eid_to_event_valid in *. rewrite !Forall_cons in EEVS_VALID_1, EEVS_VALID_2. by destruct EEVS_VALID_1, EEVS_VALID_2. }
    rewrite /eid_to_event_valid !Forall_cons in EEVS_VALID_1, EEVS_VALID_2.
    destruct EEVS_VALID_1 as [H2 _]. destruct EEVS_VALID_2 as [H3 _].
    rewrite H2 in H3. inversion H3. subst o0.
    specialize (IHeeVs VALID _ VALID' H1). subst eeVs'. done.
Qed.

Lemma eid_to_event_valid_mono_history E E' eeVs
    (SubE : E ⊑ E')
    (EEVS_VALID : eid_to_event_valid E eeVs) :
  eid_to_event_valid E' eeVs.
Proof.
  unfold eid_to_event_valid in *. rewrite Forall_lookup. intros. destruct x as [e eV].
  rewrite Forall_lookup in EEVS_VALID. specialize (EEVS_VALID _ _ H). simpl in EEVS_VALID.
  eapply prefix_lookup_Some; try done.
Qed.

Lemma eid_to_event_valid_mono_history_rev E E' eeVs
    (SubE : E' ⊑ E)
    (EEVS_VALID : eid_to_event_valid E eeVs)
    (EID_VALID : Forall (λ e, is_Some (E' !! e)) eeVs.*1) :
  eid_to_event_valid E' eeVs.
Proof.
  unfold eid_to_event_valid in *. rewrite Forall_lookup. intros. destruct x as [e eV].
  rewrite Forall_lookup in EID_VALID.
  have LOOKUP : eeVs.*1 !! i = Some e by rewrite list_lookup_fmap H.
  specialize (EID_VALID _ _ LOOKUP).
  rewrite Forall_lookup in EEVS_VALID.
  specialize (EEVS_VALID _ _ H). simpl in EEVS_VALID.
  eapply prefix_lookup_inv; try done.
Qed.

Lemma eid_to_event_valid_mono_eeVs E eeVs eeVs'
    (SubEEVS : eeVs ⊑ eeVs')
    (EEVS_VALID : eid_to_event_valid E eeVs') :
  eid_to_event_valid E eeVs.
Proof.
  unfold eid_to_event_valid in *. rewrite Forall_lookup. intros. destruct x as [e eV].
  apply (prefix_lookup_Some _ eeVs') in H; [|done].
  rewrite Forall_lookup in EEVS_VALID. specialize (EEVS_VALID _ _ H). done.
Qed.

Lemma eid_to_event_valid_eeVs_app E eeVs eeVs'
    (EEVS_VALID_1 : eid_to_event_valid E eeVs)
    (EEVS_VALID_2 : eid_to_event_valid E eeVs') :
  eid_to_event_valid E (eeVs ++ eeVs').
Proof. by unfold eid_to_event_valid in *; rewrite Forall_app. Qed.

Lemma eid_to_event_valid_perm E eeVs eeVs'
    (PERM : eeVs ≡ₚ eeVs')
    (EEVS_VALID : eid_to_event_valid E eeVs) :
  eid_to_event_valid E eeVs'.
Proof.
  unfold eid_to_event_valid in *. rewrite Forall_lookup. intros.
  destruct x as [e eV]. symmetry in PERM.
  apply elem_of_list_lookup_2 in H.
  eapply Permutation_in in PERM; last first.
  { rewrite elem_of_list_In in H.  done. }
  rewrite -elem_of_list_In in PERM.
  apply elem_of_list_lookup_1 in PERM as [i' LOOKUP].
  rewrite Forall_lookup in EEVS_VALID. by specialize (EEVS_VALID _ _ LOOKUP).
Qed.

Lemma eid_to_event_valid_perm_from_eid E eeVs eeVs'
    (EEVS_VALID_1 : eid_to_event_valid E eeVs)
    (EEVS_VALID_2 : eid_to_event_valid E eeVs')
    (PERM : eeVs.*1 ≡ₚ eeVs'.*1) :
  eeVs ≡ₚ eeVs'.
Proof.
  generalize dependent eeVs'. induction eeVs; intros.
  - destruct eeVs'; try done. apply Permutation_length in PERM. simpl in PERM. lia.
  - destruct a as [e eV]. rewrite fmap_cons in PERM.
    apply (elem_of_Permutation_proper e) in PERM as ELEM.
    have [eeVs'' PERM'] : ∃ eeVs'', eeVs' ≡ₚ (e, eV) :: eeVs''.
    { simpl in ELEM.
      have ELEM' : e ∈ e :: eeVs.*1 by apply elem_of_list_here.
      rewrite ELEM in ELEM'. apply elem_of_list_lookup_1 in ELEM' as [i Hi].
      apply list_lookup_fmap_inv in Hi as [[e' eV'] [EQ Hi]]. simpl in EQ. subst e'.
      have EQ : eV = eV'.
      { unfold eid_to_event_valid in *. rewrite !Forall_lookup in EEVS_VALID_1, EEVS_VALID_2.
        have LOOKUP : ((e, eV) :: eeVs) !! 0 = Some (e, eV) by done.
        specialize (EEVS_VALID_1 _ _ LOOKUP). specialize (EEVS_VALID_2 _ _ Hi). simpl in *.
        rewrite EEVS_VALID_2 in EEVS_VALID_1. inversion EEVS_VALID_1. done. }
      subst eV'. apply elem_of_list_lookup_2 in Hi. rewrite elem_of_Permutation in Hi. done. }
    have PERM'' : eeVs'.*1 ≡ₚ ((e, eV) :: eeVs'').*1 by eapply fmap_Permutation. rewrite fmap_cons /= in PERM''.
    have H1 : e :: eeVs.*1 ≡ₚ e :: eeVs''.*1 by eapply Permutation_trans.
    apply cons_Permutation_inj_r in H1 as H2.
    have EEVS_VALID_1' : eid_to_event_valid E eeVs.
    { unfold eid_to_event_valid in *. rewrite Forall_cons in EEVS_VALID_1. by destruct EEVS_VALID_1 as [_ ?]. }
    have EEVS_VALID_2' : eid_to_event_valid E eeVs''.
    { unfold eid_to_event_valid in *. rewrite Forall_lookup. intros. destruct x as [e' eV'].
      have IN : (e', eV') ∈ ((e, eV) :: eeVs'').
      { apply (elem_of_list_lookup_2 _ (S i)). simpl. done. }
      rewrite elem_of_list_In in IN. eapply Permutation_in in IN; [|done]. rewrite -elem_of_list_In in IN.
      apply elem_of_list_lookup_1 in IN as [i' Hi']. rewrite Forall_lookup in EEVS_VALID_2.
      specialize (EEVS_VALID_2 _ _ Hi'). done. }
    specialize (IHeeVs EEVS_VALID_1' _ EEVS_VALID_2' H2).
    eapply Permutation_trans; [|done].
    by eapply Permutation_cons.
Qed.

Lemma omo_write_op_init_step E omo stlist e eV st `{Interpretable eventT absStateT}
    (OMO_GOOD : Linearizability_omo E omo stlist)
    (LOOKUP1 : omo_write_op omo !! 0 = Some e)
    (LOOKUP2 : E !! e = Some eV)
    (LOOKUP3 : stlist !! 0 = Some st) :
  step e eV init st.
Proof.
  destruct OMO_GOOD.
  apply (interp_omo_take _ _ _ _ 1) in INTERP_OMO as INTERP_OMO'.
  apply list_lookup_omo_from_write_op in LOOKUP1 as [es LOOKUP1].
  rewrite (take_S_r _ _ (e, es)) in INTERP_OMO'; [|done]. rewrite take_0 in INTERP_OMO'.
  rewrite (take_S_r _ _ st) in INTERP_OMO'; [|done]. rewrite take_0 in INTERP_OMO'.
  inversion INTERP_OMO'. subst E0 st1.
  rewrite -(app_nil_l [(e, es)]) in H0. rewrite -(app_nil_l [st]) in H2.
  apply app_inj_2 in H0; [|done]. destruct H0 as [H0 H1]. inversion H1. subst omo0 e0 es0. clear H1.
  apply app_inj_2 in H2; [|done]. destruct H2 as [H0 H1]. inversion H1. subst stlist0 st3. clear H1.
  destruct H4 as (H1 & H2 & H3 & H4 & H5).
  rewrite LOOKUP2 in H1. inversion H1. subst eV0. inversion H3. subst st2. done.
Qed.

Lemma omo_write_op_step E omo stlist gen e eV st st' `{Interpretable eventT absStateT}
    (OMO_GOOD : Linearizability_omo E omo stlist)
    (LOOKUP1 : omo_write_op omo !! (gen + 1) = Some e)
    (LOOKUP2 : E !! e = Some eV)
    (LOOKUP3 : stlist !! gen = Some st)
    (LOOKUP4 : stlist !! (gen + 1) = Some st') :
  step e eV st st'.
Proof.
  destruct OMO_GOOD.
  apply (interp_omo_take _ _ _ _ (S (gen + 1))) in INTERP_OMO as INTERP_OMO'.
  apply list_lookup_omo_from_write_op in LOOKUP1 as [es LOOKUP1].
  rewrite (take_S_r _ _ (e, es)) in INTERP_OMO'; [|done].
  rewrite (take_S_r _ _ st') in INTERP_OMO'; [|done].
  inversion INTERP_OMO'.
  { apply (f_equal length) in H2. rewrite app_length /= in H2. lia. }
  apply app_inj_2 in H0 as [EQ1 EQ2]; [|done]. inversion EQ2. subst omo0 e0 es0 st1 E0. clear EQ2.
  apply app_inj_2 in H2 as [EQ1 EQ2]; [|done]. inversion EQ2. subst stlist0 st3. clear EQ2.
  destruct H4 as (H1 & H2 & H3 & H4 & _).
  rewrite LOOKUP2 in H1. inversion H1. subst eV0. clear H1.
  rewrite last_cons last_lookup in H3.
  replace (Init.Nat.pred (length (take (gen + 1) stlist))) with (length (take (gen + 1) stlist) - 1)%nat in H3 by lia.
  rewrite lookup_take in H3; last first.
  { rewrite take_length. apply lookup_lt_Some in LOOKUP4. lia. }
  rewrite take_length in H3. replace ((gen + 1) `min` (length stlist) - 1)%nat with gen in H3; last first.
  { apply lookup_lt_Some in LOOKUP4. lia. }
  rewrite LOOKUP3 in H3. inversion H3. subst st2. clear H3. done.
Qed.

Lemma omo_read_op_step E omo stlist gen idx e eV st `{Interpretable eventT absStateT}
    (OMO_GOOD : Linearizability_omo E omo stlist)
    (LOOKUP1 : lookup_omo omo (ro_event gen idx) = Some e)
    (LOOKUP2 : E !! e = Some eV)
    (LOOKUP3 : stlist !! gen = Some st) :
  step e eV st st.
Proof.
  destruct OMO_GOOD.
  apply (interp_omo_take _ _ _ _ (S gen)) in INTERP_OMO as INTERP_OMO'.
  destruct (omo !! gen) eqn:Heq; last first.
  { rewrite lookup_omo_ro_event /omo_read_op list_lookup_fmap Heq /= in LOOKUP1. done. }
  destruct p as [e' es'].
  rewrite lookup_omo_ro_event /omo_read_op list_lookup_fmap Heq /= in LOOKUP1.
  rewrite (take_S_r _ _ (e', es')) in INTERP_OMO'; [|done].
  rewrite (take_S_r _ _ st) in INTERP_OMO'; [|done].
  inversion INTERP_OMO'.
  { apply (f_equal length) in H4. rewrite app_length /= in H4. lia. }
  apply app_inj_2 in H0,H2; try done. destruct H0 as [-> EQ1]. destruct H2 as [-> EQ2].
  inversion EQ1. inversion EQ2. subst E0 st1 e0 es st3. clear EQ1 EQ2.
  destruct H4 as (H1 & H2 & H3 & H4 & H5).
  rewrite Forall_lookup in H5. specialize (H5 _ _ LOOKUP1) as [eV' [LOOKUP2' [STEP _]]].
  rewrite LOOKUP2 in LOOKUP2'. inversion LOOKUP2'. subst eV'. clear LOOKUP2'. done.
Qed.

Lemma omo_insert_r_write_op omo gen e :
  omo_write_op (omo_insert_r omo gen e) = omo_write_op omo.
Proof.
  rewrite /omo_insert_r /omo_write_op.
  rewrite (list_alter_fmap fst
             (λ '(e', es'), (e', es' ++ [e]))
             id
             omo gen); last first.
  { induction omo; [simpl;done|]. constructor; [|done]. destruct a. by simpl. }
  rewrite list_alter_id; [|done]. done.
Qed.

Lemma omo_insert_r_read_op omo gen e :
  omo_read_op (omo_insert_r omo gen e) = alter (λ es' : list event_id, es' ++ [e]) gen (omo_read_op omo).
Proof.
  rewrite /omo_insert_r /omo_read_op.
  rewrite (list_alter_fmap snd
             (λ '(e', es'), (e', es' ++ [e]))
             (λ es', es' ++ [e])
             omo gen); last first.
  { induction omo; [simpl;done|]. constructor; [|done]. destruct a. by simpl. }
  done.
Qed.

Lemma omo_insert_r_length omo gen e :
  length (omo_insert_r omo gen e) = length omo.
Proof. by rewrite /omo_insert_r alter_length. Qed.

Lemma omo_append_w_read_op omo e es :
  omo_read_op (omo_append_w omo e es) = omo_read_op omo ++ [es].
Proof. unfold omo_read_op, omo_append_w. by simplify_list_eq. Qed.

Lemma omo_append_w_write_op omo e es :
  omo_write_op (omo_append_w omo e es) = omo_write_op omo ++ [e].
Proof. unfold omo_write_op, omo_append_w. by simplify_list_eq. Qed.

Lemma omo_append_w_length omo e es :
  length (omo_append_w omo e es) = length omo + 1.
Proof. by rewrite /omo_append_w app_length. Qed.

Lemma omo_insert_w_append_w omo gen e es :
  length omo ≤ gen →
  omo_insert_w omo gen e es = omo_append_w omo e es.
Proof.
  rewrite /omo_insert_w /omo_append_w. intros.
  rewrite take_ge; [|done]. rewrite drop_ge; [|done]. by simplify_list_eq.
Qed.

Lemma omo_insert_w_read_op omo gen e es :
  omo_read_op (omo_insert_w omo gen e es) = take gen (omo_read_op omo) ++ [es] ++ drop gen (omo_read_op omo).
Proof.
  rewrite /omo_insert_w /omo_read_op /=.
  rewrite fmap_app fmap_take !fmap_cons !fmap_drop //=.
Qed.

Lemma omo_insert_w_write_op omo gen e es :
  omo_write_op (omo_insert_w omo gen e es) = take gen (omo_write_op omo) ++ [e] ++ drop gen (omo_write_op omo).
Proof.
  rewrite /omo_insert_w /omo_write_op /=.
  rewrite fmap_app fmap_take !fmap_cons !fmap_drop //=.
Qed.

Lemma omo_insert_w_length omo gen e es :
  length (omo_insert_w omo gen e es) = length omo + 1.
Proof.
  rewrite /omo_insert_w /= app_length cons_length.
  rewrite -{3}(take_drop gen omo) app_length. lia.
Qed.

Lemma lookup_omo_before_insert_r omo eidx gen es e
    (GEN : omo_read_op omo !! gen = Some es) :
  lookup_omo (omo_insert_r omo gen e) eidx =
    if decide (eidx = ro_event gen (length es)) then lookup_omo (omo_insert_r omo gen e) eidx (* Not meaningful in this case *)
    else lookup_omo omo eidx. (* We can know the result of old lookup only if eidx ≠ ro_event gen (length es) *)
Proof.
  destruct (decide (eidx = ro_event gen (length es))) as [->|NEQ]; [done|].
  destruct eidx as [gen' i'|gen'].
  - rewrite !lookup_omo_ro_event omo_insert_r_read_op.
    destruct (decide (gen' = gen)) as [->|NEQ'].
    + rewrite list_lookup_alter GEN /=. destruct (le_lt_dec i' (length es)) as [LE|LT].
      * rewrite lookup_app_l; [done|]. have ? : i' ≠ length es; [|lia]. unfold not. intros. subst i'. done.
      * rewrite lookup_ge_None_2; [|by rewrite app_length /=; lia].
        rewrite lookup_ge_None_2; [done|]. lia.
    + rewrite list_lookup_alter_ne; [|done]. done.
  - rewrite !lookup_omo_wr_event omo_insert_r_write_op. done.
Qed.

Lemma lookup_omo_before_insert_r' omo eidx gen e :
  lookup_omo (omo_insert_r omo gen e) eidx =
    match eidx with
    | wr_event _ => lookup_omo omo eidx
    | ro_event _ _ => lookup_omo (omo_insert_r omo gen e) eidx
    end.
Proof.
  destruct (le_lt_dec (length omo) gen) as [LE|LT].
  { have EQ : omo = omo_insert_r omo gen e.
    { unfold omo_insert_r. replace omo with (omo ++ []); [|by simplify_list_eq].
      rewrite alter_app_r_alt; [|done]. simplify_list_eq.
      have [omo' Homo'] : ∃ omo', omo' = alter (λ '(e', es'), (e', es' ++ [e])) (gen - length omo) [] by eexists.
      have EQ : omo' = [].
      { apply (f_equal length) in Homo'. rewrite alter_length in Homo'. by destruct omo'. }
      rewrite -Homo' EQ. by simplify_list_eq. }
    rewrite -EQ. by destruct eidx. }
  destruct eidx as [gen' i'|gen']; [done|].
  have [[e' es'] LOOKUP] : is_Some (omo !! gen) by rewrite lookup_lt_is_Some.
  rewrite (lookup_omo_before_insert_r _ _ _ es'); [|by rewrite /omo_read_op list_lookup_fmap LOOKUP].
  rewrite decide_False; [|done]. done.
Qed.

Lemma lookup_omo_new_ro_event E omo stlist gen es eidx (e := length E) `{Interpretable eventT absStateT}
    (OMO_GOOD : Linearizability_omo E omo stlist)
    (LOOKUP_ES : omo_read_op omo !! gen = Some es)
    (LOOKUP : lookup_omo (omo_insert_r omo gen e) eidx = Some e) :
  eidx = ro_event gen (length es).
Proof.
  destruct (decide (eidx = ro_event gen (length es))) as [->|NEQ]; [done|exfalso].
  rewrite (lookup_omo_before_insert_r _ _ _ es) in LOOKUP; [|done].
  rewrite decide_False in LOOKUP; [|done].
  eapply lookup_omo_event_valid in LOOKUP; [|done].
  rewrite lookup_lt_is_Some in LOOKUP. subst e. lia.
Qed.

Lemma lookup_omo_before_append_w omo eidx e :
  lookup_omo (omo_append_w omo e []) eidx =
    if decide (eidx = wr_event (length omo)) then lookup_omo (omo_append_w omo e []) eidx (* Not meaningful *)
    else lookup_omo omo eidx. (* We can know the result of old lookup only if eidx ≠ wr_event (length omo) *)
Proof.
  destruct eidx.
  - rewrite decide_False; [|done]. rewrite !lookup_omo_ro_event omo_append_w_read_op.
    destruct (le_lt_dec (length (omo_read_op omo)) gen) as [LE|LT].
    + destruct (decide (gen = length (omo_read_op omo))) as [->|NEQ].
      * rewrite lookup_app_1_eq lookup_ge_None_2; [|lia]. simpl. done.
      * rewrite lookup_ge_None_2; [|rewrite app_length /=;lia]. rewrite lookup_ge_None_2; [|lia]. done.
    + rewrite lookup_app_l; [|done]. done.
  - destruct (decide (gen = (length omo))) as [->|NEQ].
    + rewrite decide_True; [|done]. done.
    + rewrite decide_False; last first.
      { unfold not. intros. inversion H. done. }
      rewrite !lookup_omo_wr_event omo_append_w_write_op.
      destruct (le_lt_dec (length (omo_write_op omo)) gen) as [LE|LT].
      * rewrite lookup_ge_None_2; last first.
        { rewrite omo_write_op_length in NEQ. rewrite app_length /=. lia. }
        rewrite lookup_ge_None_2; [|done]. done.
      * rewrite lookup_app_l; [|done]. done.
Qed.

Lemma lookup_omo_new_wr_event (E : history) omo stlist eidx (e := length E) `{Interpretable eventT absStateT}
    (OMO_GOOD : Linearizability_omo E omo stlist)
    (OMO_LOOKUP : lookup_omo (omo_append_w omo e []) eidx = Some e) :
  eidx = wr_event (length omo).
Proof.
  case (decide (eidx = wr_event (length omo))) as [->|NE]; [done|]. exfalso.
  rewrite lookup_omo_before_append_w decide_False in OMO_LOOKUP; [|done].
  specialize (lookup_omo_event_valid _ _ _ _ _ OMO_GOOD OMO_LOOKUP) as HEe%lookup_lt_is_Some.
  lia.
Qed.

Lemma lookup_omo_before_insert_w omo eidx gen e e'
    (OMO_LOOKUP : lookup_omo (omo_insert_w omo gen e []) eidx = Some e')
    (NEQ : eidx ≠ wr_event gen)
    (GEN_VALID : gen ≤ length omo) :
  ∃ eidx',
    lookup_omo omo eidx' = Some e' ∧
    if decide (gen_of eidx < gen) then eidx' = eidx
    else gen < gen_of eidx ∧ gen_of eidx = gen_of eidx' + 1 ∧ match eidx with
         | ro_event g i => eidx' = ro_event (g - 1) i
         | wr_event g => eidx' = wr_event (g - 1)
    end.
Proof.
  destruct eidx as [gen' i'|gen'].
  - rewrite lookup_omo_ro_event omo_insert_w_read_op in OMO_LOOKUP.
    destruct (le_lt_dec gen gen') as [LE|LT].
    + rewrite lookup_app_r in OMO_LOOKUP; last first.
      { rewrite take_length. lia. }
      have [gen'' Hgen''] : ∃ gen'', gen' - length (take gen (omo_read_op omo)) = S gen''.
      { destruct (gen' - length (take gen (omo_read_op omo))) eqn:Heq.
        - exfalso. simpl in *. done.
        - by eexists. }
      rewrite Hgen'' /= in OMO_LOOKUP.
      exists (ro_event (gen' - 1) i'). split.
      * rewrite lookup_omo_ro_event. rewrite lookup_drop in OMO_LOOKUP.
        rewrite take_length -omo_read_op_length Nat.min_l in Hgen''; [|done].
        replace (gen + gen'') with (gen' - 1) in OMO_LOOKUP; [done|]. lia.
      * rewrite decide_False; [|simpl;lia]. split_and!; simpl; try done; try lia.
        rewrite take_length -omo_read_op_length Nat.min_l in Hgen''; [|lia]. lia.
    + exists (ro_event gen' i'). split.
      * rewrite lookup_app_l in OMO_LOOKUP; last first.
        { rewrite take_length -omo_read_op_length Nat.min_l; [|lia]. lia. }
        rewrite lookup_take in OMO_LOOKUP; [|done]. done.
      * rewrite decide_True; [done|]. simpl. lia.
  - destruct (le_lt_dec gen gen') as [LE|LT].
    + rewrite lookup_omo_wr_event omo_insert_w_write_op lookup_app_r in OMO_LOOKUP; last first.
      { rewrite take_length. lia. }
      have [gen'' Hgen''] : ∃ gen'', gen' - length (take gen (omo_write_op omo)) = S gen''.
      { destruct (gen' - length (take gen (omo_write_op omo))) eqn:Heq.
        - exfalso. rewrite take_length -omo_write_op_length Nat.min_l in Heq; [|done].
          have EQ : gen' = gen by lia. subst gen'. done.
        - by eexists. }
      rewrite Hgen'' /= lookup_drop in OMO_LOOKUP.
      rewrite take_length -omo_write_op_length Nat.min_l in Hgen''; [|done].
      exists (wr_event (gen' - 1)). split.
      * rewrite lookup_omo_wr_event. replace (gen + gen'') with (gen' - 1) in OMO_LOOKUP; [done|]. lia.
      * rewrite decide_False; [|simpl;lia]. split_and!; simpl; try done; try lia.
    + rewrite lookup_omo_wr_event omo_insert_w_write_op lookup_app_l in OMO_LOOKUP; last first.
      { rewrite take_length -omo_write_op_length Nat.min_l; lia. }
      exists (wr_event gen'). split.
      * rewrite lookup_omo_wr_event. rewrite lookup_take in OMO_LOOKUP; [|done]. done.
      * rewrite decide_True; [done|]. simpl. lia.
Qed.

Lemma lookup_omo_new_wr_event' E omo stlist gen eidx (e := length E) `{Interpretable eventT absStateT}
    (OMO_GOOD : Linearizability_omo E omo stlist)
    (LOOKUP : lookup_omo (omo_insert_w omo gen e []) eidx = Some e)
    (GEN_VALID : gen ≤ length omo) :
  eidx = wr_event gen.
Proof.
  destruct (decide (eidx = wr_event gen)) as [->|NEQ]; [done|exfalso].
  apply lookup_omo_before_insert_w in LOOKUP; try done.
  destruct LOOKUP as [eidx' [LOOKUP CASE]].
  eapply lookup_omo_event_valid in LOOKUP; [|done].
  rewrite lookup_lt_is_Some in LOOKUP. subst e. lia.
Qed.

Lemma omo_prefix_lookup_Some omo1 omo2 eidx e
    (PREFIX : omo_prefix omo1 omo2)
    (LOOKUP : lookup_omo omo1 eidx = Some e) :
  lookup_omo omo2 eidx = Some e.
Proof.
  destruct PREFIX as [H1 H2].
  destruct eidx.
  - rewrite lookup_omo_ro_event. rewrite lookup_omo_ro_event in LOOKUP.
    destruct (omo_read_op omo1 !! gen) as [es|] eqn:Heq; [|done]. simpl in LOOKUP.
    specialize (H1 gen). rewrite Heq /= in H1. destruct (omo_read_op omo2 !! gen) as [es'|] eqn:Heq'; [|done].
    simpl. eapply prefix_lookup_Some; try done.
  - rewrite lookup_omo_wr_event. rewrite lookup_omo_wr_event in LOOKUP.
    eapply prefix_lookup_Some; try done.
Qed.

Lemma omo_prefix_lookup_inv omo1 omo2 eidx e
    (LOOKUP : lookup_omo omo2 eidx = Some e)
    (LOOKUP' : is_Some (lookup_omo omo1 eidx))
    (PREFIX : omo_prefix omo1 omo2) :
  lookup_omo omo1 eidx = Some e.
Proof.
  destruct LOOKUP' as [e' LOOKUP'].
  eapply omo_prefix_lookup_Some in LOOKUP' as LOOKUP''; [|done].
  rewrite LOOKUP in LOOKUP''. inversion LOOKUP''. done.
Qed.

Lemma omo_insert_r_prefix omo omo' gen e
    (PREFIX : omo_prefix omo omo') :
  omo_prefix omo (omo_insert_r omo' gen e).
Proof.
  destruct (le_lt_dec (length omo') gen) as [LE|LT].
  { have EQ : omo' = omo_insert_r omo' gen e.
    { unfold omo_insert_r. replace omo' with (omo' ++ []); [|by simplify_list_eq].
      rewrite alter_app_r_alt; [|done]. simplify_list_eq.
      have [omo'' Homo'] : ∃ omo'', omo'' = alter (λ '(e', es'), (e', es' ++ [e])) (gen - length omo') [] by eexists.
      have EQ : omo'' = [].
      { apply (f_equal length) in Homo'. rewrite alter_length in Homo'. by destruct omo''. }
      rewrite -Homo' EQ. by simplify_list_eq. }
    rewrite -EQ. done. }
  rewrite -lookup_lt_is_Some in LT. destruct LT as [[e' es'] Hgen].
  destruct PREFIX as [H1 H2]. split.
  - rewrite /prefixes /map_included /map_relation omo_insert_r_read_op. intros.
    destruct (decide (i = gen)) as [->|NEQ].
    + rewrite list_lookup_alter. rewrite {2}/omo_read_op list_lookup_fmap Hgen /=.
      destruct (omo_read_op omo !! gen) as [es''|] eqn:Heq; [|done].
      specialize (H1 gen). rewrite Heq /omo_read_op list_lookup_fmap Hgen /= in H1. simpl.
      by eapply prefix_app_r.
    + rewrite list_lookup_alter_ne; [|done]. done.
  - rewrite omo_insert_r_write_op. done.
Qed.

Lemma omo_append_w_prefix omo omo' e es
    (PREFIX : omo_prefix omo omo') :
  omo_prefix omo (omo_append_w omo' e es).
Proof.
  destruct PREFIX as [H1 H2]. split.
  - rewrite omo_append_w_read_op /prefixes /map_included /map_relation. intros.
    destruct (le_lt_dec (length (omo_read_op omo')) i) as [LE|LT].
    + rewrite lookup_ge_None_2.
      { by destruct ((omo_read_op omo' ++ [es]) !! i). }
      apply prefix_length in H2. rewrite -!omo_write_op_length in H2.
      rewrite -omo_read_op_length in LE. rewrite -omo_read_op_length. lia.
    + rewrite lookup_app_l; [|done]. done.
  - rewrite omo_append_w_write_op. by eapply prefix_app_r.
Qed.

Lemma omo_insert_w_prefix omo omo' gen e es
    (PREFIX : omo_prefix omo omo')
    (LEgen : length omo ≤ gen) :
  omo_prefix omo (omo_insert_w omo' gen e es).
Proof.
  destruct PREFIX as [H1 H2]. split.
  - rewrite omo_insert_w_read_op /prefixes /map_included /map_relation. intros.
    destruct (le_lt_dec (length (omo_read_op omo)) i) as [LE|LT].
    + rewrite lookup_ge_None_2; [|done].
      by destruct ((take gen (omo_read_op omo') ++ [es] ++ drop gen (omo_read_op omo')) !! i).
    + rewrite lookup_app_l; last first.
      { rewrite take_length -omo_read_op_length. apply prefix_length in H2. rewrite -!omo_write_op_length in H2.
        rewrite -omo_read_op_length in LT. lia. }
      rewrite lookup_take; last first.
      { rewrite -omo_read_op_length in LT. lia. }
      done.
  - rewrite omo_insert_w_write_op.
    destruct H2 as [l H2]. rewrite !H2.
    have EQ : gen = length (omo_write_op omo) + (gen - length (omo_write_op omo)).
    { rewrite omo_write_op_length in LEgen. lia. }
    rewrite {1}EQ take_add_app; [|done]. simplify_list_eq. by eapply prefix_app_r.
Qed.

Lemma lin_perm_omo_inj (E : history) omo
    (LIN_PERM : lin_of_omo omo ≡ₚ seq 0 (length E)) :
  omo_inj omo.
Proof.
  intros ?????.
  (* another way: Using [NoDup (lin_of_omo _ _)]... Is that easier? *)
  apply lookup_omo_lin_of_omo_lookup in OMO_LOOKUP1 as LIN1, OMO_LOOKUP2 as LIN2.
  apply Permutation_inj in LIN_PERM as [_ (f & INJ_f & LIN_PERM)].
  rewrite ->LIN_PERM in LIN1,LIN2.
  apply lookup_lt_Some in LIN1 as LT1, LIN2 as LT2.
  rewrite seq_length in LT1,LT2.
  rewrite ->lookup_xo in LIN1,LIN2; [|done..].
  rewrite -LIN1 in LIN2. injection LIN2 as EQ%(inj f).
  by eapply eidx_to_lin_idx_inj in EQ.
Qed.

Lemma lookup_omo_inj E omo stlist e eidx eidx' `{Interpretable eventT absStateT}
    (OMO_GOOD : Linearizability_omo E omo stlist)
    (LOOKUP1 : lookup_omo omo eidx = Some e)
    (LOOKUP2 : lookup_omo omo eidx' = Some e) :
  eidx = eidx'.
Proof.
  destruct OMO_GOOD. apply lin_perm_omo_inj in PERM_OMO.
  by eapply PERM_OMO.
Qed.

Lemma lookup_omo_surjective E omo stlist e `{Interpretable eventT absStateT}
    (OMO_GOOD : Linearizability_omo E omo stlist)
    (VALID : is_Some (E !! e)) :
  ∃ eidx, lookup_omo omo eidx = Some e.
Proof.
  destruct OMO_GOOD. rewrite lookup_lt_is_Some in VALID.
  have IN : e ∈ seq 0 (length E).
  { eapply (elem_of_list_lookup_2 _ e). rewrite lookup_seq. split; lia. }
  rewrite elem_of_list_In in IN. eapply Permutation_in in IN; [|done]. rewrite -elem_of_list_In in IN.
  apply elem_of_list_lookup_1 in IN as [i Hi].
  apply lin_of_omo_lookup_lookup_omo in Hi as [eidx [_ LOOKUP]]; last first.
  { rewrite NoDup_Permutation_proper; [|done]. by apply NoDup_seq. }
  by eexists.
Qed.

Lemma interp_omo_mono E1 E2 omo st stlist `{Interpretable eventT absStateT}
    (SubE : E1 ⊑ E2)
    (INTERP_OMO : interp_omo E1 omo st stlist) :
  interp_omo E2 omo st stlist.
Proof.
  generalize dependent stlist. induction omo using rev_ind; intros.
  - inversion INTERP_OMO.
    + constructor.
    + apply (f_equal length) in H0. rewrite app_length /= in H0. lia.
  - inversion INTERP_OMO.
    { apply (f_equal length) in H2. rewrite app_length /= in H2. lia. }
    apply app_inj_2 in H0 as [-> EQ1]; [|done]. inversion EQ1. subst E1 st1 stlist x. clear EQ1. rename stlist0 into stlist.
    destruct H2 as (H1 & H2 & H3 & H4 & H5).
    econstructor. split_and!; try done.
    + by eapply prefix_lookup_Some.
    + by eapply IHomo.
    + rewrite Forall_lookup. intros. rewrite Forall_lookup in H5. specialize (H5 _ _ H0) as [eV' (Ha & Hb & Hc)].
      exists eV'. split_and!; try done. by eapply prefix_lookup_Some.
Qed.

Lemma omo_gen_info E omo stlist gen e es `{Interpretable eventT absStateT}
    (OMO_GOOD : Linearizability_omo E omo stlist)
    (LOOKUP : omo !! gen = Some (e, es)) :
  ∃ eV eeVs st,
    eeVs.*1 = omo_write_op omo ∧
    eid_to_event_valid E eeVs ∧
    E !! e = Some eV ∧
    stlist !! gen = Some st ∧
    interp (take (gen + 1) eeVs) init st ∧
    Forall (λ e', ∃ eV', E !! e' = Some eV' ∧ step e' eV' st st ∧ e < e') es.
Proof.
  specialize (omo_write_op_to_eeVs _ _ _ OMO_GOOD) as [eeVs [eeVs_EID eeVs_VALID]].
  inversion OMO_GOOD.
  specialize (interp_omo_take _ _ _ _ (S gen) INTERP_OMO) as INTERP_OMO'.
  specialize (interp_omo_length _ _ _ _ INTERP_OMO) as EQlen.
  rewrite (take_S_r _ _ (e, es)) in INTERP_OMO'; [|done].
  have [st Hst] : is_Some (stlist !! gen) by rewrite lookup_lt_is_Some -EQlen; apply lookup_lt_Some in LOOKUP.
  rewrite (take_S_r _ _ st) in INTERP_OMO'; [|done].
  inversion INTERP_OMO'.
  { apply (f_equal length) in H2. rewrite app_length /= in H2. lia. }
  apply app_inj_2 in H0 as [-> EQ1]; [|done]. apply app_inj_2 in H2 as [-> EQ2]; [|done].
  inversion EQ1. inversion EQ2. subst E0 st1 e0 es0 st3. clear EQ1 EQ2.
  destruct H4 as (H1 & H2 & H3 & H4 & H5).
  exists eV,eeVs,st. split_and!; try done.
  clear H1 H2 H3 H4 H5 INTERP_OMO' eV.
  generalize dependent e. generalize dependent es. generalize dependent st. induction gen; intros.
  - simpl. have LOOKUP' : lookup_omo omo (wr_event 0) = Some e by rewrite lookup_omo_wr_event /omo_write_op list_lookup_fmap LOOKUP.
    eapply lookup_omo_event_valid in LOOKUP' as [eV HeV]; [|done].
    replace (take 1 eeVs) with ([] ++ [(e, eV)]); last first.
    { simplify_list_eq. destruct eeVs.
      - unfold omo_write_op in *. apply (f_equal length) in eeVs_EID. rewrite !fmap_length /= in eeVs_EID.
        apply lookup_lt_Some in LOOKUP. lia.
      - unfold omo_write_op in *. rewrite fmap_cons in eeVs_EID. destruct p as [e' eV'].
        apply (f_equal ((!!) 0)) in eeVs_EID. rewrite list_lookup_fmap LOOKUP /= in eeVs_EID. inversion eeVs_EID. subst e'.
        rewrite /eid_to_event_valid Forall_lookup in eeVs_VALID.
        have COND : ((e, eV') :: eeVs) !! 0 = Some (e, eV') by done.
        specialize (eeVs_VALID _ _ COND). simpl in *. rewrite HeV in eeVs_VALID. inversion eeVs_VALID. subst eV'. done. }
    econstructor; [apply interp_nil|].
    specialize (interp_omo_take _ _ _ _ (S 0) INTERP_OMO) as INTERP_OMO'.
    inversion INTERP_OMO'.
    { apply (f_equal length) in H2. rewrite take_length /= in H2. apply lookup_lt_Some in LOOKUP. destruct (length omo); lia. }
    replace (take 1 omo) with ([] ++ [(e, es)]) in H0; last first.
    { simplify_list_eq. destruct omo; [done|].
      simpl in *. inversion LOOKUP. subst p. done. }
    replace (take 1 stlist) with ([] ++ [st]) in H2; last first.
    { simplify_list_eq. destruct stlist; [done|]. simpl in *. inversion Hst. done. }
    apply app_inj_2 in H0 as [-> EQ1]; [|done]. apply app_inj_2 in H2 as [-> EQ2]; [|done].
    inversion EQ1. inversion EQ2. subst E0 st1 e0 es0 st3. clear EQ1 EQ2.
    destruct H4 as (H1 & H2 & H3 & H4 & _).
    rewrite HeV in H1. inversion H1. subst eV0. clear H1.
    inversion H3. subst st0. clear H3. done.
  - replace (S gen + 1) with (S (gen + 1)) by lia. replace (S gen) with (gen + 1) in Hst, LOOKUP; [|lia].
    have LOOKUP' : lookup_omo omo (wr_event (gen + 1)) = Some e by rewrite lookup_omo_wr_event /omo_write_op list_lookup_fmap LOOKUP.
    eapply lookup_omo_event_valid in LOOKUP' as [eV HeV]; [|done].
    have HeeVs : eeVs !! (gen + 1) = Some (e, eV).
    { apply (f_equal ((!!) (gen + 1))) in eeVs_EID. rewrite /omo_write_op !list_lookup_fmap LOOKUP /= -list_lookup_fmap in eeVs_EID.
      apply list_lookup_fmap_inv in eeVs_EID as [[e' eV'] [EQ HeeVs]]. simpl in EQ. subst e'.
      rewrite /eid_to_event_valid Forall_lookup in eeVs_VALID. specialize (eeVs_VALID _ _ HeeVs). simpl in eeVs_VALID.
      rewrite HeV in eeVs_VALID. inversion eeVs_VALID. done. }
    rewrite (take_S_r _ _ (e, eV)); [|done].
    specialize (interp_omo_take _ _ _ _ (S (gen + 1)) INTERP_OMO) as INTERP_OMO'.
    inversion INTERP_OMO'.
    { apply (f_equal length) in H2. rewrite take_length /= in H2. apply lookup_lt_Some in LOOKUP. destruct (length omo); lia. }
    rewrite (take_S_r _ _ (e, es)) in H0; [|done].
    rewrite (take_S_r _ _ st) in H2; [|done].
    apply app_inj_2 in H0 as [-> EQ1]; [|done]. apply app_inj_2 in H2 as [-> EQ2]; [|done].
    inversion EQ1. inversion EQ2. subst E0 st1 e0 es0 st3. clear EQ1 EQ2.
    destruct H4 as (H1 & H2 & H3 & H4 & _).
    rewrite HeV in H1. inversion H1. subst eV0. clear H1.
    apply lookup_lt_Some in Hst as LENst.
    rewrite last_cons last_lookup take_length Nat.min_l in H3; [|lia].
    replace (Init.Nat.pred (gen + 1)) with gen in H3 by lia.
    rewrite lookup_take in H3; [|lia].
    have [[e' es'] Hees'] : is_Some (omo !! gen) by rewrite lookup_lt_is_Some; lia.
    have [st' Hst'] : is_Some (stlist !! gen) by rewrite lookup_lt_is_Some; lia.
    rewrite Hst' in H3. inversion H3. subst st0. clear H3.
    specialize (IHgen _ Hst' _ _ Hees').
    eapply interp_snoc; done.
Qed.

Lemma omo_gen_info' E omo stlist gen e es eeVs `{Interpretable eventT absStateT}
    (OMO_GOOD : Linearizability_omo E omo stlist)
    (LOOKUP : omo !! gen = Some (e, es))
    (EID_MATCH : eeVs.*1 = omo_write_op omo)
    (EEVS_VALID : eid_to_event_valid E eeVs) :
  ∃ eV st,
    E !! e = Some eV ∧
    stlist !! gen = Some st ∧
    interp (take (gen + 1) eeVs) init st ∧
    Forall (λ e', ∃ eV', E !! e' = Some eV' ∧ step e' eV' st st ∧ e < e') es.
Proof.
  specialize (omo_gen_info _ _ _ _ _ _ OMO_GOOD LOOKUP) as (eV & eeVs' & st & H1 & H2 & H3 & H4 & H5 & H6).
  have EQ : eeVs = eeVs'.
  { eapply eid_to_event_valid_agree_from_eid; try done. by rewrite EID_MATCH H1. }
  subst eeVs'. exists eV, st. split_and!; try done.
Qed.

Lemma omo_interp_full E omo stlist `{Interpretable eventT absStateT}
    (OMO_GOOD : Linearizability_omo E omo stlist) :
  ∃ eeVs st,
    last (init :: stlist) = Some st ∧
    eeVs.*1 = omo_write_op omo ∧
    eid_to_event_valid E eeVs ∧
    interp eeVs init st.
Proof.
  destruct omo using rev_ind.
  - exists [], init. destruct OMO_GOOD. inversion INTERP_OMO; last first.
    { apply (f_equal length) in H0. rewrite app_length /= in H0. lia. }
    subst stlist st E0. split_and!; try done.
    + by apply Forall_nil.
    + apply interp_nil.
  - clear IHomo. destruct x as [e es].
    have LOOKUP : (omo ++ [(e, es)]) !! (length omo) = Some (e, es) by rewrite lookup_app_1_eq.
    specialize (omo_gen_info _ _ _ _ _ _ OMO_GOOD LOOKUP) as (eV & eeVs & st & eeVs_EID & eeVs_VALID & _ & Hst & INTERP & _).
    exists eeVs, st. split_and!; try done.
    + specialize (omo_stlist_length _ _ _ OMO_GOOD) as EQlen.
      rewrite last_cons last_lookup -EQlen app_length /=.
      replace (Init.Nat.pred (length omo + 1)) with (length omo) by lia.
      rewrite Hst. done.
    + rewrite take_ge in INTERP; [done|].
      apply (f_equal length) in eeVs_EID as EQlen.
      rewrite fmap_length -omo_write_op_length app_length /= in EQlen. lia.
Qed.

Lemma omo_interp_full' E omo stlist eeVs `{Interpretable eventT absStateT}
    (OMO_GOOD : Linearizability_omo E omo stlist)
    (EEVS_VALID : eid_to_event_valid E eeVs)
    (ES_MATCH : eeVs.*1 = omo_write_op omo) :
  ∃ st,
    last (init :: stlist) = Some st ∧
    interp eeVs init st.
Proof.
  specialize (omo_interp_full _ _ _ OMO_GOOD) as (eeVs' & st & Hst & eeVs_EID' & eeVs_VALID' & INTERP).
  have EQ : eeVs = eeVs'.
  { eapply eid_to_event_valid_agree_from_eid; try done. by rewrite ES_MATCH eeVs_EID'. }
  subst eeVs'. exists st. split; done.
Qed.

Lemma lin_perm_append_w omo e
    (LIN_PERM : lin_of_omo omo ≡ₚ seq 0 e):
  lin_of_omo (omo_append_w omo e []) ≡ₚ seq 0 (e + 1).
Proof. rewrite seq_app /=. rewrite lin_of_omo_append_w. by apply Permutation_app. Qed.

Lemma lin_perm_insert_w omo gen e
    (LIN_PERM : lin_of_omo omo ≡ₚ seq 0 e):
  lin_of_omo (omo_insert_w omo gen e []) ≡ₚ seq 0 (e + 1).
Proof.
  rewrite seq_app /=. rewrite lin_of_omo_insert_w.
  rewrite app_Permutation_comm app_nil_l.
  list_simplifier.
  have EQ : e :: lin_of_omo (drop gen omo) ++ lin_of_omo (take gen omo) = [e] ++ lin_of_omo (drop gen omo) ++ lin_of_omo (take gen omo) by list_simplifier.
  rewrite EQ app_Permutation_comm.
  apply Permutation_app; [|done].
  by rewrite app_Permutation_comm -lin_of_omo_take_drop.
Qed.

Lemma lin_perm_insert_r omo gen e
    (GEN : (gen < length omo)%nat)
    (LIN_PERM: lin_of_omo omo ≡ₚ seq 0 e) :
  lin_of_omo (omo_insert_r omo gen e) ≡ₚ seq 0 (e + 1).
Proof.
  unfold lin_of_omo, omo_read_op, omo_insert_r in *. simpl in *.
  rewrite -lookup_lt_is_Some in GEN. destruct GEN as [[e' es'] Heq].
  rewrite (alter_take_drop _ omo _ (e', es')); [|done].
  simplify_list_eq.
  rewrite !concat_app concat_cons -(assoc app (e' :: es')) (comm app [e]) (assoc app (e' :: es')).
  rewrite (assoc app (concat ((λ '(e0, es), e0 :: es) <$> take gen omo))).
  rewrite seq_app.
  apply Permutation_app; [|done].
  rewrite -(take_drop gen omo) (drop_S omo (e',es')) in LIN_PERM; [|done].
  simplify_list_eq.
  rewrite !concat_app concat_cons in LIN_PERM.
  done.
Qed.

Lemma lhb_omo_append_w E omo stlist eV `{Interpretable eventT absStateT}
    (OMO_GOOD : Linearizability_omo E omo stlist)
    (EWF : history_wf E) :
  lhb_omo (E ++ [eV]) (omo_append_w omo (length E) []).
Proof.
  inversion OMO_GOOD. unfold lhb_omo. intros.
  set gen' := length omo.
  set eidx := wr_event gen'.
  destruct (decide (eidx = eidx1)) as [<-|NE1];
  destruct (decide (eidx = eidx2)) as [<-|NE2].
  - (* this ∈ this.eview *)
    by apply eidx_le_w_w.
  - (* this ∈ old.eview: old can't contain this *)
    exfalso. subst eidx gen'.
    rewrite lookup_omo_wr_event omo_append_w_write_op omo_write_op_length lookup_app_1_eq in omo_eidx1. inversion omo_eidx1. subst e1.
    rewrite lookup_omo_before_append_w decide_False in omo_eidx2; [|done].
    eapply lookup_omo_event_valid in omo_eidx2; [|done]. rewrite lookup_lt_is_Some in omo_eidx2.
    rewrite lookup_app_l in EV2; [|done].
    specialize (hwf_logview_closed _ EWF _ _ EV2 _ IN_EVIEW) as Hcontra. rewrite /= lookup_lt_is_Some in Hcontra. lia.
  - (* old ∈ this.eview *)
    subst eidx gen'.
    rewrite lookup_omo_wr_event omo_append_w_write_op omo_write_op_length lookup_app_1_eq in omo_eidx2. inversion omo_eidx2. subst e2.
    rewrite lookup_app_1_eq in EV2. inversion EV2. subst eV2. clear omo_eidx2 EV2.
    rewrite lookup_omo_before_append_w decide_False in omo_eidx1; [|done].
    apply lookup_omo_lt_Some in omo_eidx1 as MAXgen.
    destruct eidx1; simpl in MAXgen.
    + apply eidx_le_r_w. lia.
    + apply eidx_le_w_w. lia.
  - (* old ∈ old.eview *)
    rewrite lookup_omo_before_append_w decide_False in omo_eidx1; [|done].
    rewrite lookup_omo_before_append_w decide_False in omo_eidx2; [|done].
    eapply lookup_omo_event_valid in omo_eidx2 as VALID; [|done]. rewrite lookup_lt_is_Some in VALID.
    rewrite lookup_app_l in EV2; [|lia].
    by eapply (LHB_OMO eidx1 eidx2).
Qed.

Lemma lhb_omo_insert_w E omo stlist gen eV (M : eView) `{Interpretable eventT absStateT}
    (OMO_GOOD : Linearizability_omo E omo stlist)
    (EWF : history_wf E)
    (EV_EVIEW : eV.(eview) = {[length E]} ∪ M)
    (MAXgen : ∀ e eidx, e ∈ M → lookup_omo omo eidx = Some e → (gen_of eidx < gen)%nat) :
  lhb_omo (E ++ [eV]) (omo_insert_w omo gen (length E) []).
Proof.
  destruct (le_lt_dec (length omo) gen) as [LE|GEN_VALID].
  { have EQ : omo_insert_w omo gen (length E) [] = omo_append_w omo (length E) [].
    { rewrite /omo_insert_w /omo_append_w take_ge; [|done]. rewrite drop_ge; [|done]. done. }
    rewrite EQ. eapply lhb_omo_append_w; done. }
  inversion OMO_GOOD. unfold lhb_omo. intros.
  set eidx := wr_event gen.
  destruct (decide (eidx = eidx1)) as [<-|NE1];
  destruct (decide (eidx = eidx2)) as [<-|NE2].
  - (* this ∈ this.eview *)
    by apply eidx_le_w_w.
  - (* this ∈ old.eview: old can't contain this *)
    exfalso. subst eidx.
    rewrite lookup_omo_wr_event omo_insert_w_write_op lookup_app_r in omo_eidx1; last first.
    { rewrite take_length -omo_write_op_length. lia. }
    rewrite take_length -omo_write_op_length Nat.min_l in omo_eidx1; [|lia].
    replace (gen - gen) with 0 in omo_eidx1 by lia. simpl in omo_eidx1. inversion omo_eidx1. subst e1. clear omo_eidx1.
    apply lookup_omo_before_insert_w in omo_eidx2 as [eidx2' [Heidx2' CASE]]; [|done|lia].
    eapply lookup_omo_event_valid in Heidx2'; [|done]. rewrite lookup_lt_is_Some in Heidx2'.
    rewrite lookup_app_l in EV2; [|done].
    specialize (hwf_logview_closed _ EWF _ _ EV2 _ IN_EVIEW) as Hcontra. rewrite /= lookup_lt_is_Some in Hcontra. lia.
  - (* old ∈ this.eview *)
    subst eidx.
    rewrite lookup_omo_wr_event omo_insert_w_write_op lookup_app_r in omo_eidx2; last first.
    { rewrite take_length -omo_write_op_length. lia. }
    rewrite take_length -omo_write_op_length Nat.min_l in omo_eidx2; [|lia].
    replace (gen - gen) with 0 in omo_eidx2 by lia. simpl in omo_eidx2. inversion omo_eidx2. subst e2. clear omo_eidx2.
    rewrite lookup_app_1_eq in EV2. inversion EV2. subst eV2. clear EV2.
    apply lookup_omo_before_insert_w in omo_eidx1 as [eidx1' [Heidx1' CASE]]; [|done|lia].
    have IN_EVIEW' : e1 ∈ M.
    { eapply lookup_omo_event_valid in Heidx1'; [|done]. rewrite lookup_lt_is_Some in Heidx1'.
      rewrite EV_EVIEW in IN_EVIEW. clear -Heidx1' IN_EVIEW.
      have ? : e1 ≠ length E by lia. set_solver. }
    specialize (MAXgen _ _ IN_EVIEW' Heidx1').
    destruct (le_lt_dec gen (gen_of eidx1)) as [LE|LT].
    + rewrite decide_False in CASE; [|lia]. destruct CASE as (H1 & H2 & H3).
      destruct eidx1; subst eidx1'; simpl in *.
      * apply eidx_le_r_w. lia.
      * apply eidx_le_w_w. lia.
    + rewrite decide_True in CASE; [|lia]. subst eidx1'. destruct eidx1; simpl in *.
      * apply eidx_le_r_w. lia.
      * apply eidx_le_w_w. lia.
  - (* old ∈ old.eview *)
    apply lookup_omo_before_insert_w in omo_eidx1 as H1; [|done|lia]. destruct H1 as [eidx1' [Heidx1' CASE1]].
    apply lookup_omo_before_insert_w in omo_eidx2 as H2; [|done|lia]. destruct H2 as [eidx2' [Heidx2' CASE2]].
    eapply lookup_omo_event_valid in Heidx2' as VALID; [|done]. rewrite lookup_lt_is_Some in VALID.
    rewrite lookup_app_l in EV2; [|lia].
    specialize (LHB_OMO eidx1' eidx2' _ _ eV2 Heidx1' Heidx2' EV2 IN_EVIEW).
    destruct (le_lt_dec gen (gen_of eidx1)) as [LE1|LT1];
    destruct (le_lt_dec gen (gen_of eidx2)) as [LE2|LT2].
    + rewrite decide_False in CASE1; [|lia]. destruct CASE1 as (LTeidx1 & EQeidx1 & CASE1).
      rewrite decide_False in CASE2; [|lia]. destruct CASE2 as (LTeidx2 & EQeidx2 & CASE2).
      destruct eidx1, eidx2; subst eidx1' eidx2'; simpl in *; inversion LHB_OMO; subst.
      * apply eidx_le_r_r_1. lia.
      * replace gen0 with gen1 by lia. apply eidx_le_r_r_2. lia.
      * apply eidx_le_r_w. lia.
      * apply eidx_le_w_r. lia.
      * apply eidx_le_w_w. lia.
    + rewrite decide_False in CASE1; [|lia]. destruct CASE1 as (LTeidx1 & EQeidx1 & CASE1).
      rewrite decide_True in CASE2; [|lia]. subst eidx2'.
      destruct eidx1, eidx2; subst eidx1'; simpl in *; inversion LHB_OMO; subst; simpl in *; try lia.
    + rewrite decide_True in CASE1; [|lia]. subst eidx1'.
      rewrite decide_False in CASE2; [|lia]. destruct CASE2 as (LTeidx2 & EQeidx2 & CASE2).
      destruct eidx1, eidx2; subst eidx2'; simpl in *; inversion LHB_OMO; subst; simpl in *; try lia.
      * apply eidx_le_r_r_1. lia.
      * apply eidx_le_r_w. lia.
      * apply eidx_le_w_r. lia.
      * apply eidx_le_w_w. lia.
    + rewrite decide_True in CASE1; [|lia]. subst eidx1'.
      rewrite decide_True in CASE2; [|lia]. subst eidx2'. done.
Qed.

Lemma lhb_omo_insert_r E omo stlist gen eV (M : eView) `{Interpretable eventT absStateT}
    (OMO_GOOD : Linearizability_omo E omo stlist)
    (EWF : history_wf E)
    (EV_EVIEW : eV.(eview) = {[length E]} ∪ M)
    (GEN_VALID : (gen < length omo)%nat)
    (MAXgen : ∀ e eidx, e ∈ M → lookup_omo omo eidx = Some e → (gen_of eidx ≤ gen)%nat) :
  lhb_omo (E ++ [eV]) (omo_insert_r omo gen (length E)).
Proof.
  inversion OMO_GOOD. unfold lhb_omo. intros.
  rewrite -lookup_lt_is_Some in GEN_VALID. destruct GEN_VALID as [[e es] Hgen].
  set eidx := ro_event gen (length es).
  destruct (decide (eidx = eidx1)) as [<-|NE1];
  destruct (decide (eidx = eidx2)) as [<-|NE2].
  - (* this ∈ this.eview *)
    apply eidx_le_r_r_2. lia.
  - (* this ∈ old.eview: old can't contain this *)
    exfalso. subst eidx.
    rewrite lookup_omo_ro_event omo_insert_r_read_op list_lookup_alter /omo_read_op list_lookup_fmap Hgen /= lookup_app_1_eq in omo_eidx1.
    inversion omo_eidx1. subst e1. clear omo_eidx1.
    erewrite lookup_omo_before_insert_r in omo_eidx2; [|rewrite /omo_read_op list_lookup_fmap Hgen;done].
    rewrite decide_False in omo_eidx2; [|done].
    eapply lookup_omo_event_valid in omo_eidx2; [|done]. rewrite lookup_lt_is_Some in omo_eidx2.
    rewrite lookup_app_l in EV2; [|lia].
    specialize (hwf_logview_closed _ EWF _ _ EV2 _ IN_EVIEW) as Hcontra. rewrite /= lookup_lt_is_Some in Hcontra. lia.
  - (* old ∈ this.eview *)
    subst eidx.
    rewrite lookup_omo_ro_event omo_insert_r_read_op list_lookup_alter /omo_read_op list_lookup_fmap Hgen /= lookup_app_1_eq in omo_eidx2.
    inversion omo_eidx2. subst e2. clear omo_eidx2.
    erewrite lookup_omo_before_insert_r in omo_eidx1; [|rewrite /omo_read_op list_lookup_fmap Hgen;done].
    rewrite decide_False in omo_eidx1; [|done].
    have IN_EVIEW' : e1 ∈ M.
    { eapply lookup_omo_event_valid in omo_eidx1; [|done]. rewrite lookup_lt_is_Some in omo_eidx1.
      rewrite lookup_app_1_eq in EV2. inversion EV2. subst eV2. clear EV2.
      rewrite EV_EVIEW in IN_EVIEW. clear -omo_eidx1 IN_EVIEW.
      have ? : e1 ≠ length E by lia. set_solver. }
    specialize (MAXgen _ _ IN_EVIEW' omo_eidx1). destruct eidx1; simpl in *.
    + destruct (decide (gen0 = gen)) as [->|NEQ].
      * apply eidx_le_r_r_2. rewrite list_lookup_fmap Hgen /= in omo_eidx1. apply lookup_lt_Some in omo_eidx1. lia.
      * apply eidx_le_r_r_1. lia.
    + apply eidx_le_w_r. lia.
  - (* old ∈ old.eview *)
    erewrite lookup_omo_before_insert_r in omo_eidx1; [|rewrite /omo_read_op list_lookup_fmap Hgen;done].
    erewrite lookup_omo_before_insert_r in omo_eidx2; [|rewrite /omo_read_op list_lookup_fmap Hgen;done].
    rewrite decide_False in omo_eidx1; [|done]. rewrite decide_False in omo_eidx2; [|done].
    eapply lookup_omo_event_valid in omo_eidx2 as VALID; [|done]. rewrite lookup_lt_is_Some in VALID.
    rewrite lookup_app_l in EV2; [|done].
    by eapply (LHB_OMO eidx1 eidx2).
Qed.

Lemma lin_of_omo_preserves_lhb (E : history) omo stlist `{Interpretable eventT absStateT}
    (OMO_GOOD : Linearizability_omo E omo stlist) :
  lhb E (lin_of_omo omo).
Proof.
  inversion OMO_GOOD.
  unfold lhb. intros.
  have [eV1 EV1] : ∃ eV1, E !! e1 = Some eV1 by eapply ord_idx_event.
  have E1' : seq 0 (length E) !! e1 = Some e1 by by eapply lookup_xo, lookup_lt_Some.
  have E2' : seq 0 (length E) !! e2 = Some e2 by by eapply lookup_xo, lookup_lt_Some.
  have NODUP : NoDup (lin_of_omo omo) by eapply ord_nodup.
  exploit (lin_of_omo_lookup_lookup_omo omo i1); [done..|].
  intros (eidx1 & -> & OMO_LOOKUP1).
  exploit (lin_of_omo_lookup_lookup_omo omo i2); [done..|].
  intros (eidx2 & -> & OMO_LOOKUP2).
  exploit (LHB_OMO eidx1 eidx2); [done..|]. intros LE_EIDX. des.

  destruct eidx1 as [gen1 i1'|gen1']; destruct eidx2 as [gen2 i2'|gen2'].
  + (* read op, read op *) inv LE_EIDX.
    * by apply Nat.lt_le_incl,lin_idx_r_gen_mono.
    * simplify_eq. apply lin_idx_r_i'_mono. done.
  + (* read op, _ *) inv LE_EIDX. (* gen1 < gen2' *)
    exploit (lin_idx_r_w_gen_mono omo gen1 i1' gen2'); [done..|lia].
  + (* _, read op *)
    inv LE_EIDX. by apply Nat.lt_le_incl,lin_idx_w_r_gen_mono.
  + (* _, _ *)
    des. inv LE_EIDX.
    apply lin_idx_w_gen_mono. done.
Qed.

Lemma lin_of_omo_preserves_interp_inner (E : history) omo stlist i eeVs1 eeVs2 st `{Interpretable eventT absStateT}
    (OMO_GOOD : Linearizability_omo E omo stlist)
    (EID1 : eeVs1.*1 = lin_of_omo omo)
    (EID2 : eeVs2.*1 = omo_write_op omo)
    (VALID1 : eid_to_event_valid E eeVs1)
    (VALID2 : eid_to_event_valid E eeVs2)
    (HST : (init :: stlist) !! i = Some st)
    (INTERP : interp (take i eeVs2) init st) :
  interp (take (length (lin_of_omo (take i omo))) eeVs1) init st.
Proof.
  rename HST into Hst. generalize dependent st. induction i; intros.
  - unfold lin_of_omo. simpl. rewrite take_0. simpl in Hst. inversion Hst. apply interp_nil.
  - apply omo_stlist_length in OMO_GOOD as EQlen. simpl in Hst.
    have [[e es] Hi] : is_Some (omo !! i).
    { rewrite lookup_lt_is_Some. apply lookup_lt_Some in Hst. lia. }
    have [eV HeeVs2] : ∃ eV, eeVs2 !! i = Some (e, eV).
    { apply (f_equal length) in EID2 as LEN. rewrite fmap_length -omo_write_op_length in LEN.
      have [[e' eV] Hi'] : is_Some (eeVs2 !! i).
      { rewrite lookup_lt_is_Some. apply lookup_lt_Some in Hi. lia. }
      apply (f_equal ((!!) i)) in EID2. rewrite /omo_write_op !list_lookup_fmap Hi Hi' /= in EID2. inversion EID2. subst e'.
      by eexists. }
    inversion OMO_GOOD.
    specialize (omo_gen_info' _ _ _ i _ _ _ OMO_GOOD Hi EID2 VALID2) as (eV' & st' & H1 & H2 & H3 & H4).
    have EQ : eV = eV'.
    { unfold eid_to_event_valid in *. rewrite Forall_lookup in VALID2.
      specialize (VALID2 _ _ HeeVs2). simpl in VALID2. rewrite VALID2 in H1. inversion H1. subst eV'. done. }
    subst eV'. rewrite Hst in H2. inversion H2. subst st'. clear H2.
    have [st' [Hst' INTERP']] : ∃ st', (init :: stlist) !! i = Some st' ∧ interp (take i eeVs2) init st'.
    { destruct i.
      - exists init. split; [done|]. rewrite take_0. apply interp_nil.
      - have [[e' es'] Hi'] : is_Some (omo !! i) by rewrite lookup_lt_is_Some; apply lookup_lt_Some in Hi; lia.
        specialize (omo_gen_info' _ _ _ i _ _ _ OMO_GOOD Hi' EID2 VALID2) as (eV' & st' & H1' & H2' & H3' & H4').
        exists st'. split; [done|]. replace (S i) with (i + 1) by lia. done. }
    specialize (IHi _ Hst' INTERP').

    erewrite lin_of_omo_take_S_r; [|done]. rewrite app_length.
    set idx := length (lin_of_omo (take i omo)).
    rewrite -(take_drop idx eeVs1).
    rewrite take_add_app; last first.
    { rewrite take_length Nat.min_l; [done|]. apply (f_equal length) in EID1. rewrite fmap_length in EID1. rewrite EID1.
      subst idx. unfold lin_of_omo. rewrite -{-1}(take_drop i omo). simplify_list_eq. rewrite concat_app app_length. lia. }
    rewrite interp_app. exists st'. split; [done|]. simpl.

    have [eeVs [EQ1 [EQ2 VALID]]] : ∃ eeVs, take (S (length es)) (drop idx eeVs1) = [(e, eV)] ++ eeVs ∧ eeVs.*1 = es ∧ eid_to_event_valid E eeVs.
    { set eeVs := take (S (length es)) (drop idx eeVs1).
      destruct eeVs eqn:Heq.
      - subst eeVs. apply (f_equal ((!!) 0)) in Heq. rewrite lookup_take in Heq; [|lia].
        rewrite lookup_drop Nat.add_0_r in Heq.
        replace idx with (eidx_to_lin_idx omo (wr_event i)) in Heq; [|done].
        have LOOKUP : lookup_omo omo (wr_event i) = Some e by rewrite lookup_omo_wr_event /omo_write_op list_lookup_fmap Hi.
        apply lookup_omo_lin_of_omo_lookup in LOOKUP. rewrite -EID1 list_lookup_fmap Heq in LOOKUP. done.
      - destruct p as [e' eV']. subst eeVs.
        have [EQ1 EQ2] : e' = e ∧ eV' = eV.
        { apply (f_equal ((!!) 0)) in Heq. rewrite lookup_take /= in Heq; [|lia]. rewrite lookup_drop Nat.add_0_r in Heq.
          have LOOKUP : lookup_omo omo (wr_event i) = Some e by rewrite lookup_omo_wr_event /omo_write_op list_lookup_fmap Hi.
          apply lookup_omo_lin_of_omo_lookup in LOOKUP. rewrite -EID1 list_lookup_fmap Heq in LOOKUP. inversion LOOKUP. subst e'.
          rewrite /eid_to_event_valid Forall_lookup in VALID1. specialize (VALID1 _ _ Heq). simpl in VALID1.
          rewrite VALID1 in H1. inversion H1. done. }
        subst e' eV'.
        have Hl : l.*1 = es.
        { have Heq' : (take (S (length es)) (drop idx eeVs1)).*1 = ((e, eV) :: l).*1 by rewrite Heq.
          rewrite fmap_take fmap_drop fmap_cons EID1 /lin_of_omo in Heq'.
          rewrite -(take_drop i omo) in Heq'. simplify_list_eq. rewrite concat_app drop_app (drop_S _ (e, es)) in Heq'; [|done].
          simplify_list_eq. done. }
        have VALID : eid_to_event_valid E l.
        { rewrite /eid_to_event_valid Forall_lookup. intros i' [e' eV'] Hi'.
          apply (f_equal ((!!) (S i'))) in Heq. rewrite /= Hi' in Heq.
          rewrite lookup_take_Some in Heq. destruct Heq as [Heq LT].
          rewrite lookup_drop in Heq. rewrite /eid_to_event_valid Forall_lookup in VALID1.
          specialize (VALID1 _ _ Heq). simpl in VALID1. done. }
        exists l. simplify_list_eq. done. }

    rewrite EQ1. rewrite interp_app. exists st. split.
    + replace [(e, eV)] with ([] ++ [(e, eV)]); [|by simplify_list_eq]. eapply interp_snoc; [apply interp_nil|].
      specialize (interp_omo_take _ _ _ _ (S i) INTERP_OMO) as INTERP_OMO'.
      rewrite (take_S_r _ _ (e, es)) in INTERP_OMO'; [|done]. inversion INTERP_OMO'.
      { apply (f_equal length) in H5. rewrite app_length /= in H5. lia. }
      rewrite (take_S_r _ _ st) in H5; [|done].
      apply app_inj_2 in H0 as [-> EQ1']; [|done]. apply app_inj_2 in H5 as [-> EQ2']; [|done].
      inversion EQ1'. inversion EQ2'. subst E0 st1 e0 es0 st3. clear EQ1' EQ2'.
      destruct H7 as (H8 & _ & H8' & H8'' & _). rewrite H1 in H8. inversion H8. subst eV0. clear H8.
      rewrite last_cons last_lookup take_length Nat.min_l in H8'; [|apply lookup_lt_Some in Hst;lia].
      replace (Init.Nat.pred i) with (i - 1) in H8' by lia.
      destruct i.
      * inversion Hst'. subst st'. simpl in H8'. inversion H8'. subst st2. done.
      * simpl in Hst'. replace (S i - 1) with i in H8' by lia.
        rewrite lookup_take in H8'; [|lia]. rewrite Hst' in H8'. inversion H8'. done.
    + clear -H4 EQ2 VALID. generalize dependent es. induction eeVs using rev_ind; intros; [apply interp_nil|].
      destruct x as [e' eV']. destruct es using rev_ind.
      { simplify_list_eq. apply (f_equal length) in EQ2. rewrite app_length /= in EQ2. lia. }
      rewrite fmap_app /= in EQ2. apply app_inj_2 in EQ2 as [<- EQ]; [|done]. inversion EQ. subst x. clear EQ.
      rewrite /eid_to_event_valid Forall_app in VALID. destruct VALID as [VALID1 VALID2].
      eapply interp_snoc; [eapply (IHeeVs VALID1 eeVs.*1)|]; try done.
      * rewrite Forall_app in H4. by destruct H4 as [? _].
      * rewrite Forall_lookup in H4.
        have H1 : (eeVs.*1 ++ [e']) !! (length eeVs.*1) = Some e' by rewrite lookup_app_1_eq.
        specialize (H4 _ _ H1) as (eV'' & He' & H4 & _).
        rewrite Forall_singleton in VALID2. rewrite VALID2 in He'. inversion He'. done.
Qed.

Lemma lin_of_omo_preserves_interp (E : history) omo stlist `{Interpretable eventT absStateT}
    (OMO_GOOD : Linearizability_omo E omo stlist) :
  ∃ eeVs st,
    last (init :: stlist) = Some st ∧
    eeVs.*1 = lin_of_omo omo ∧
    eid_to_event_valid E eeVs ∧
    interp eeVs init st.
Proof.
  apply lin_of_omo_to_eeVs in OMO_GOOD as EEVS.
  destruct EEVS as (eeVs & eeVs_EID & eeVs_VALID).
  apply omo_interp_full in OMO_GOOD as EEVS.
  destruct EEVS as (eeVs' & st & Hst & eeVs_EID' & eeVs_VALID' & INTERP).
  exists eeVs, st. split_and!; try done.
  replace eeVs with (take (length (lin_of_omo (take (length omo) omo))) eeVs); last first.
  { rewrite take_ge; [done|]. rewrite take_ge; [|lia]. apply (f_equal length) in eeVs_EID.
    rewrite fmap_length in eeVs_EID. lia. }
  eapply lin_of_omo_preserves_interp_inner; try done.
  - apply omo_stlist_length in OMO_GOOD. rewrite OMO_GOOD. rewrite last_cons last_lookup in Hst. destruct stlist.
    + simpl in *. done.
    + simpl in *. destruct ((a :: stlist) !! length stlist) eqn:Heq; try done.
      apply lookup_ge_None_1 in Heq. simpl in *. lia.
  - rewrite take_ge; [done|]. apply (f_equal length) in eeVs_EID'. rewrite fmap_length -omo_write_op_length in eeVs_EID'. lia.
Qed.

Lemma lin_of_omo_preserves_interp' (E : history) omo stlist eeVs `{Interpretable eventT absStateT}
    (OMO_GOOD : Linearizability_omo E omo stlist)
    (EID_MATCH : eeVs.*1 = lin_of_omo omo)
    (EEVS_VALID : eid_to_event_valid E eeVs) :
  ∃ st,
    last (init :: stlist) = Some st ∧
    interp eeVs init st.
Proof.
  specialize (lin_of_omo_preserves_interp _ _ _ OMO_GOOD) as (eeVs' & st & Hst & eeVs_EID' & eeVs_VALID' & INTERP).
  have EQ : eeVs = eeVs'.
  { eapply eid_to_event_valid_agree_from_eid; try done. by rewrite EID_MATCH eeVs_EID'. }
  subst eeVs'. exists st. split; done.
Qed.

Lemma filter_seq_same P Q (e : nat) `{∀ x, Decision (P x)} `{∀ x, Decision (Q x)}
    (COND_EQUIV : ∀ e', e' < e → (P e' ↔ Q e')) :
  filter P (seq 0 e) = filter Q (seq 0 e).
Proof.
  induction e; first done.
  replace (S e) with (e + 1); last lia.
  rewrite seq_app !filter_app. simpl.
  rewrite IHe; last first.
  { intros. apply COND_EQUIV. lia. }
  replace (filter Q [e]) with (filter P [e]); first done.
  destruct (bool_decide (P e)) eqn:Hp.
  - rewrite bool_decide_eq_true in Hp.
    apply COND_EQUIV in Hp as Hq; last lia.
    rewrite !filter_cons_True; done.
  - rewrite bool_decide_eq_false in Hp.
    rewrite filter_cons_False; last done.
    rewrite COND_EQUIV in Hp; last lia.
    rewrite filter_cons_False; done.
Qed.

Lemma omo_compatible E omo stlist `{Interpretable eventT absStateT}
    (OMO_GOOD : Linearizability_omo E omo stlist) :
  Linearizability E.
Proof.
  specialize (lin_of_omo_preserves_interp _ _ _ OMO_GOOD) as (eeVs & st & LASTst & eeVs_EID & eeVs_VALID & INTERP).
  specialize (omo_xo_to_eeVs _ _ _ OMO_GOOD) as (eeVs' & eeVs'_EID & eeVs'_VALID).
  apply (Linearizability_intro _ eeVs' eeVs st); try done.
  - eapply eid_to_event_valid_perm_from_eid; try done. rewrite eeVs_EID eeVs'_EID. by destruct OMO_GOOD.
  - rewrite eeVs_EID. by eapply lin_of_omo_preserves_lhb.
Qed.

Lemma Linearizability_omo_empty `{Interpretable eventT absStateT} :
  Linearizability_omo [] [] [].
Proof. constructor; try done; constructor. Qed.

Lemma Linearizability_omo_append_w (E : history) omo stlist st st' eV `{Interpretable eventT absStateT}
    (E' := E ++ [eV])
    (e' := length E)
    (omo' := omo_append_w omo e' [])
    (OMO_GOOD : Linearizability_omo E omo stlist)
    (EWF : history_wf E)
    (LASTST : last (init :: stlist) = Some st)
    (INTERP_NEXT : step e' eV st st') :
  Linearizability_omo E' omo' (stlist ++ [st']).
Proof.
  inversion OMO_GOOD. constructor 1.
  - subst omo'. unfold omo_append_w. eapply interp_omo_snoc. split_and!.
    + subst E' e'. by rewrite lookup_app_1_eq.
    + eapply (interp_omo_mono E E'); try done. subst E'. by eapply prefix_app_r.
    + done.
    + done.
    + by apply Forall_nil.
  - eapply lhb_omo_append_w; try done.
  - subst omo' e' E'. rewrite /perm_omo app_length/= .
    eapply lin_perm_append_w. done.
Qed.

Lemma Linearizability_omo_insert_w (E : history) omo stlist st stnew gen eV (M : eView) `{Interpretable eventT absStateT}
    (E' := (E ++ [eV]))
    (e' := length E)
    (omo' := omo_insert_w omo gen e' [])
    (OMO_GOOD : Linearizability_omo E omo stlist)
    (EWF : history_wf E)
    (INTERPGEN : last (init :: take gen stlist) = Some st)
    (INTERP_OMO : interp_omo E' ((e', []) :: (drop gen omo)) st stnew)
    (EGV_EVIEW : eV.(eview) = {[e']} ∪ M)
    (MAXgen : ∀ e eidx, e ∈ M → lookup_omo omo eidx = Some e → (gen_of eidx < gen)%nat) : (* Note the strict inequality here *)
  Linearizability_omo E' omo' (take gen stlist ++ stnew).
Proof.
  inversion OMO_GOOD. constructor 1.
  - subst omo'. unfold omo_insert_w. rewrite interp_omo_app; last first.
    { rewrite !take_length. apply omo_stlist_length in OMO_GOOD as EQlen. lia. }
    exists st. split_and!; try done.
    apply interp_omo_take. eapply interp_omo_mono; [|done]. by eapply prefix_app_r.
  - eapply lhb_omo_insert_w; try done.
  - subst E' omo' e'. rewrite /perm_omo app_length /=. by eapply lin_perm_insert_w.
Qed.

Lemma Linearizability_omo_insert_r (E : history) omo stlist st gen eV (M : eView) `{Interpretable eventT absStateT}
    (E' := E ++ [eV])
    (e' := length E)
    (omo' := omo_insert_r omo gen e')
    (OMO_GOOD : Linearizability_omo E omo stlist)
    (EWF : history_wf E)
    (STGEN : stlist !! gen = Some st)
    (STEP : step e' eV st st)
    (EGV_EVIEW : eV.(eview) = {[e']} ∪ M)
    (MAXgen : ∀ e eidx, e ∈ M → lookup_omo omo eidx = Some e → (gen_of eidx ≤ gen)%nat) :
  Linearizability_omo E' omo' stlist.
Proof.
  have LT : (gen < length omo)%nat.
  { apply lookup_lt_Some in STGEN. apply omo_stlist_length in OMO_GOOD. rewrite OMO_GOOD. done. }
  have [[e es] Hgen] : is_Some (omo !! gen) by rewrite lookup_lt_is_Some.
  inversion OMO_GOOD. constructor 1.
  - subst omo'. unfold omo_insert_r. rewrite -(take_drop gen omo) alter_app_r_alt; [|by rewrite take_length;lia].
    rewrite take_length Nat.min_l; [|lia]. replace (gen - gen) with 0 by lia.
    rewrite -(take_drop gen stlist) (drop_S _ (e, es)); [|done]. simplify_list_eq. rewrite interp_omo_app; last first.
    { rewrite !take_length. apply omo_stlist_length in OMO_GOOD. lia. }
    rewrite -(take_drop gen omo) -(take_drop gen stlist) interp_omo_app in INTERP_OMO; last first.
    { rewrite !take_length. apply omo_stlist_length in OMO_GOOD. lia. }
    destruct INTERP_OMO as (st' & INTERP_OMO1 & INTERP_OMO2 & LAST).
    exists st'. split_and!.
    + eapply interp_omo_mono; [|done]. by eapply prefix_app_r.
    + rewrite (drop_S _ st); [|done].
      have EQ : (e, es ++ [e']) :: drop (S gen) omo = [(e, es ++ [e'])] ++ drop (S gen) omo by simplify_list_eq.
      rewrite EQ. clear EQ.
      replace (st :: drop (S gen) stlist) with ([st] ++ drop (S gen) stlist); [|by simplify_list_eq].
      rewrite interp_omo_app; [|done].
      rewrite (drop_S _ (e, es)) in INTERP_OMO2; [|done]. rewrite (drop_S _  st) in INTERP_OMO2; [|done].
      replace ((e, es) :: drop (S gen) omo) with ([(e, es)] ++ drop (S gen) omo) in INTERP_OMO2; [|by simplify_list_eq].
      replace (st :: drop (S gen) stlist) with ([st] ++ drop (S gen) stlist) in INTERP_OMO2; [|by simplify_list_eq].
      rewrite interp_omo_app in INTERP_OMO2; [|done]. destruct INTERP_OMO2 as (st'' & INTERP_OMO2 & INTERP_OMO2' & LAST').
      inversion LAST'. subst st''. clear LAST'. exists st. split_and!; try done.
      * eapply (interp_omo_mono E E') in INTERP_OMO2 as INTERP_OMO2''; [|by eapply prefix_app_r]. inversion INTERP_OMO2''.
        replace ([(e, es)]) with ([] ++ [(e, es)]) in H0; [|by simplify_list_eq].
        replace ([st]) with ([] ++ [st]) in H2; [|by simplify_list_eq].
        apply app_inj_2 in H0 as [-> EQ1]; [|done]. apply app_inj_2 in H2 as [-> EQ2]; [|done].
        inversion EQ1. inversion EQ2. subst E0 st1 e0 es0 st3. clear EQ1 EQ2.
        destruct H4 as (H1 & H2 & H3 & H4 & H5).
        replace ([(e, es ++ [e'])]) with ([] ++ [(e, es ++ [e'])]); [|by simplify_list_eq].
        replace ([st]) with ([] ++ [st]); [|by simplify_list_eq].
        eapply interp_omo_snoc. split_and!; try done.
        rewrite Forall_app Forall_singleton. split; [done|]. exists eV. split_and!; try done.
        -- subst E' e'. by rewrite lookup_app_1_eq.
        -- subst e'. inversion INTERP_OMO2.
           replace ([(e, es)]) with ([] ++ [(e, es)]) in H0; [|by simplify_list_eq].
           apply app_inj_2 in H0 as [-> EQ]; [|done]. inversion EQ. subst e0 es0.
           destruct H9 as [LOOKUP _]. by apply lookup_lt_Some in LOOKUP.
      * eapply interp_omo_mono; [|done]. by eapply prefix_app_r.
    + done.
  - eapply lhb_omo_insert_r; try done.
  - subst E' omo' e'. rewrite /perm_omo app_length /=. by eapply lin_perm_insert_r.
Qed.

End omo_lemmas.
End omo.
