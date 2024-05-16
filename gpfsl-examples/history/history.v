From gpfsl.examples Require Import sflib.
From iris.algebra Require Import gmap.

From gpfsl.lang Require Import lang.
From gpfsl.examples.event Require Import event.

Require Import iris.prelude.options.

Notation history eventT := (event_list eventT).

Section history.
Context {eventT : Type}.
Implicit Types (E: history eventT) (V: view).

Record history_wf E :=
  mkHistoryWf {
    (* logview includes the event itself *)
    hwf_logview_event :
      ∀ e eV, E !! e = Some eV → e ∈ eV.(ge_lview) ;
    (* logview is closed w.r.t E *)
    hwf_logview_closed :
      ∀ e eV, E !! e = Some eV → set_Forall (λ e', is_Some (E !! e')) eV.(ge_lview) ;
  }.

(** [hb] implies [ord]. *)
Definition hb_ord E (ord : list event_id) :=
  ∀ i1 i2 e1 e2 eV2
    (ORD_i1 : ord !! i1 = Some e1) (ORD_i2 : ord !! i2 = Some e2)
    (EV2 : E !! e2 = Some eV2)
    (IN_LVIEW : e1 ∈ eV2.(ge_lview)),
    (i1 ≤ i2)%nat.

Lemma history_wf_add E eV M
    (e := length E) (E' := E ++ [eV]) (M' := {[e]} ∪ M)
    (WF : history_wf E)
    (SubME : set_Forall (λ e', is_Some (E !! e')) M)
    (LVIEW : eV.(ge_lview) = M') :
  history_wf E'.
Proof.
  have SubM'E' : set_Forall (λ e, is_Some (E' !! e)) M'.
  { intros ? [->%elem_of_singleton|[]%SubME]%elem_of_union; eexists.
    - by rewrite lookup_app_1_eq.
    - eapply prefix_lookup_Some; [done|by eexists]. }
  constructor.
  - intros e' ? EV. case (decide (e' = e)) as [->|NE].
    + apply lookup_last_Some_2 in EV as ->. set_solver.
    + rewrite lookup_app_1_ne in EV; [|done].
      by apply (hwf_logview_event _ WF).
  - intros e' ? EV e'' IN_LVIEW. case (decide (e' = e)) as [->|NE].
    + apply lookup_last_Some_2 in EV as ->.
      rewrite LVIEW in IN_LVIEW. apply (SubM'E' _ IN_LVIEW).
    + rewrite lookup_app_1_ne in EV; [|done].
      specialize (hwf_logview_closed _ WF _ _ EV _ IN_LVIEW) as [? ?].
      eexists. eapply prefix_lookup_Some; [done|by eexists].
Qed.

Lemma history_wf_add_sync E e1 eV1 eV2 M
    (e2 := length E) (E' := E ++ [eV2])
    (M' := M ∪ ({[e2]} ∪ eV1.(ge_lview)))
    (WF : history_wf E)
    (EV1 : E !! e1 = Some eV1)
    (SubME : set_Forall (λ e', is_Some (E !! e')) M)
    (LVIEW : eV2.(ge_lview) = M') :
  history_wf E'.
Proof.
  have SubM1E : set_Forall (λ e, is_Some (E !! e)) eV1.(ge_lview)
    by apply (hwf_logview_closed _ WF _ _ EV1).
  have SubM'E' : set_Forall (λ e, is_Some (E' !! e)) M'.
  { intros ?. rewrite !elem_of_union elem_of_singleton.
    intros [[]%SubME|[->|[]%SubM1E]].
    - eexists. eapply prefix_lookup_Some; [done|by eexists].
    - eexists. apply lookup_app_1_eq.
    - eexists. eapply prefix_lookup_Some; [done|by eexists]. }
  constructor.
  - intros e' ? EV. case (decide (e' = e2)) as [->|NE].
    + apply lookup_last_Some_2 in EV as ->. set_solver.
    + rewrite lookup_app_1_ne in EV; [|done].
      by apply (hwf_logview_event _ WF).
  - intros e' ? EV e'' IN_LVIEW. case (decide (e' = e2)) as [->|NE].
    + apply lookup_last_Some_2 in EV as ->.
      rewrite LVIEW in IN_LVIEW. apply (SubM'E' _ IN_LVIEW).
    + rewrite lookup_app_1_ne in EV; [|done].
      specialize (hwf_logview_closed _ WF _ _ EV _ IN_LVIEW) as [? ?].
      eexists. eapply prefix_lookup_Some; [done|by eexists].
Qed.

Lemma hb_xo_add E eV
    (WF : history_wf E)
    (HB_XO : hb_ord E (seq 0 (length E))) :
  hb_ord (E ++ [eV]) (seq 0 (length (E ++ [eV]))).
Proof.
  unfold hb_ord. rewrite app_length seq_app /=. intros.
  case (decide (i1 = length (seq 0 (length E)))) as [->|NE1];
    [apply lookup_last_Some_2 in ORD_i1 as ->
    |rewrite lookup_app_1_ne in ORD_i1; [|done]; apply lookup_lt_Some in ORD_i1 as LT1;
     rewrite seq_length in LT1; rewrite lookup_xo in ORD_i1; [|done]; injection ORD_i1 as ->];
    (case (decide (i2 = length (seq 0 (length E)))) as [->|NE2];
      [apply lookup_last_Some_2 in ORD_i2 as ->
      |rewrite lookup_app_1_ne in ORD_i2; [|done]; apply lookup_lt_Some in ORD_i2 as LT2;
       rewrite seq_length in LT2; rewrite lookup_xo in ORD_i2; [|done]; injection ORD_i2 as ->]);
      rewrite ->seq_length in * |- *.
  - done.
  - exfalso. rewrite lookup_app_1_ne in EV2; [|done].
    move: (hwf_logview_closed _ WF _ _ EV2 _ IN_LVIEW) => [?].
    by rewrite lookup_ge_None_2.
  - apply lookup_last_Some_2 in EV2 as <-. lia.
  - rewrite lookup_app_l in EV2; [|done].
    eapply (HB_XO e1 e2 e1 e2 eV2); [by rewrite lookup_xo..|done|done].
Qed.

Lemma sublist_lookup {A} (ls1 ls2 : list A) i1 x
    (SUB : ls1 `sublist_of` ls2)
    (LOOKUP : ls1 !! i1 = Some x) :
  ∃ i2, ls2 !! i2 = Some x.
Proof.
  revert i1 LOOKUP. induction SUB; intros; simplify_list_eq.
  - case Ei1: i1 => [|i1']; simplify_list_eq.
    + by exists O.
    + specialize (IHSUB _ LOOKUP) as [i2']. by exists (S i2').
  - specialize (IHSUB _ LOOKUP) as [i2']. by exists (S i2').
Qed.

Lemma hb_ord_cons_inv E e eV ord
    (EV : E !! e = Some eV)
    (HB_ORD : hb_ord E (e :: ord)) :
  « HB_ORD' : hb_ord E ord » ∧
  « NO_REV_HB : Forall (λ e', e' ∉ eV.(ge_lview)) ord » .
Proof.
  split; red; last first.
  { rewrite Forall_lookup. intros i e' E' IN_LVIEW.
    exploit (HB_ORD (S i) O e' e); [done..|lia]. }
  unfold hb_ord in *. intros.
  case (decide (i1 = O)) as [->|?]; first lia.
  case (decide (i2 = O)) as [->|?]; simplify_list_eq.
  - exploit (HB_ORD (S i1) (S O) e1 e2); [done..|lia].
  - exploit (HB_ORD (S i1) (S i2) e1 e2); [done..|lia].
Qed.

Lemma sublist_hb_ord_mono E ord1 ord2
    (SUB : ord1 `sublist_of` ord2)
    (EVs : Forall (λ e, is_Some (E !! e)) ord2)
    (HB_ORD2 : hb_ord E ord2) :
  hb_ord E ord1.
Proof.
  induction SUB as [|e'|e'].
  - done.
  - (* Invert [hb_ord E (x :: l2)] to get relation between [x] and [l2], and
    [hb_ord E l2], which implies [hb_ord E l1] by IH. Then add [x]. *)
    inv EVs. destruct H1 as [eV' EV']. rename H2 into EVs'.
    specialize (hb_ord_cons_inv _ _ _ _ EV' HB_ORD2); i; des.
    rewrite ->Forall_lookup in NO_REV_HB.
    specialize (IHSUB EVs' HB_ORD').
    unfold hb_ord in IHSUB |- *. intros.
    case Ei1: i1 => [|i1']; first lia.
    case Ei2: i2 => [|i2']; simplify_list_eq.
    + rewrite EV' in EV2. simplify_eq.
      specialize (sublist_lookup _ _ _ _ SUB ORD_i1). i; des.
      by exploit NO_REV_HB.
    + exploit (IHSUB i1' i2' e1 e2); simplify_list_eq; [done..|lia].
  - inv EVs. destruct H1 as [eV' EV']. rename H2 into EVs'.
    specialize (hb_ord_cons_inv _ _ _ _ EV' HB_ORD2); i; des.
    specialize (IHSUB EVs' HB_ORD'). done.
Qed.

End history.
