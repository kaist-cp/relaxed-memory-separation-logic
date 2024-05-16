From stdpp Require Import namespaces.

From gpfsl.logic Require Import logatom.
From gpfsl.examples.graph Require Export spec.
From gpfsl.examples.queue Require Export event spec_graph.

Require Import iris.prelude.options.

Local Open Scope Z_scope.

Local Notation graph := (graph qevent).
Implicit Type
  (G : graph) (M : logView)
  (es ds xs : list event_id).

(** This is the strong inverse of [graph_xo_eco]: if e1 is before e2 in the list
  order, the e1 happens-before e2. *)
Definition sequential G es :=
  ∀ i1 i2 e1 e2 eV2
    (EID1 : es !! i1 = Some e1) (EID2 : es !! i2 = Some e2)
    (EV2 : G.(Es) !! e2 = Some eV2)
    (SEQ : (i1 < i2)%nat),
    e1 ∈ eV2.(ge_lview).

(** The dequeue list [ds] matches with the prefix of the enqueue list [es]. *)
Definition matches G es ds := ∀ i d,
    ds !! i = Some d ↔ ∃ e, es !! i = Some e ∧ (e, d) ∈ G.(com).

(** Executed enqueue events [es] sequentially. *)
Inductive Produced G es : Prop :=
| Produced_intro
    (ENQS :
      ∀ i e (Ei : es !! i = Some e),
        ∃ eV v, G.(Es) !! e = Some eV ∧ eV.(ge_event) = Enq v)
    (ENQ_SEQ : sequential G es)
  .

(** Executed dequeue events [ds] sequentially. *)
Inductive Consumed G ds : Prop :=
| Consumed_intro
    (DEQS :
      ∀ i d (Di : ds !! i = Some d),
        ∃ dV v, G.(Es) !! d = Some dV ∧ dV.(ge_event) = Deq v)
    (DEQ_SEQ : sequential G ds) (* NOTE: not necessary for SPSC example *)
  .

(** The list [xs] is of empty dequeues *)
Inductive EmpDeqs G xs : Prop :=
| EmpDeqs_intro
    (EMPS :
      ∀ i x (XI : xs !! i = Some x),
        ∃ xV, G.(Es) !! x = Some xV ∧ xV.(ge_event) = EmpDeq)
  .


(** SPSC queue predicate *)
Definition SPSCInvT Σ : Type :=
  ∀ (γg γed : gname) (q : loc) (G : graph) (es ds : list event_id), vProp Σ.
Definition ProducerT Σ : Type :=
  ∀ (N : namespace) (γg γed : gname) (q : loc)
    (G : graph) (M : logView) (es : list event_id),
    vProp Σ.
Definition ConsumerT Σ : Type :=
  ∀ (N : namespace) (γg γed : gname) (q : loc)
    (G : graph) (M : logView) (ds : list event_id),
    vProp Σ.


(** Operation specs *)

Definition new_queue_spsc_spec' {Σ} `{!noprolG Σ, !inG Σ (graphR qevent)}
  (new_queue : val)
  (Producer : ProducerT Σ) (Consumer : ConsumerT Σ) (SPSCInv : SPSCInvT Σ) : Prop :=
  ∀ N tid,
  {{{ True }}}
    new_queue [] @ tid; ⊤
  {{{ γg γed (q: loc), RET #q;
      Producer N γg γed q ∅ ∅ [] ∗ Consumer N γg γed q ∅ ∅ [] ∗
      SPSCInv γg γed q ∅ [] [] }}}.

Definition enqueue_spsc_spec' {Σ} `{!noprolG Σ, !inG Σ (graphR qevent)}
  (enqueue : val) (Producer : ProducerT Σ) (SPSCInv : SPSCInvT Σ) : Prop :=
  ∀ N (DISJ: N ## histN) (q : loc) tid γg γed
    G1 M es1 (V : view) (v : Z) (POSv : 0 < v),
  ⊒V -∗ Producer N γg γed q G1 M es1 -∗
  <<< ∀ G es ds, ▷ SPSCInv γg γed q G es ds >>>
    enqueue [ #q ; #v] @ tid; ↑N
  <<< ∃ V' G' es' (enqId : event_id) enq Venq M',
      ▷ SPSCInv γg γed q G' es' ds ∗
      ⊒V' ∗ @{V'} Producer N γg γed q G' M' es' ∗
      ⌜ G ⊑ G' ∧ M ⊑ M' ∧ es1 = es ∧
        V ⊑ Venq.(dv_in) ∧ Venq.(dv_wrt) = V' ∧
        is_enqueue enq v ∧
        enqId = length G.(Es) ∧
        G'.(Es) = G.(Es) ++ [mkGraphEvent enq Venq M'] ∧
        es' = es ++ [enqId] ∧
        enqId ∈ M' ∧
        enqId ∉ M ⌝,
      RET #☠, emp >>>
  .

Definition dequeue_spsc_spec' {Σ} `{!noprolG Σ, !inG Σ (graphR qevent)}
  (dequeue : val) (Consumer : ConsumerT Σ) (SPSCInv : SPSCInvT Σ) : Prop :=
  ∀ N (DISJ: N ## histN) (q : loc) tid γg γed
    G1 M ds1 V (i := length ds1),
  ⊒V -∗ Consumer N γg γed q G1 M ds1 -∗
  <<< ∀ G es ds, ▷ SPSCInv γg γed q G es ds >>>
    dequeue [ #q] @ tid; ↑N
  <<< ∃ (v: Z) V' G' ds' enqId deqId enq deq Vdeq M',
      ▷ SPSCInv γg γed q G' es ds' ∗
      ⊒V' ∗ @{V'} Consumer N γg γed q G' M' ds' ∗
      ⌜ G ⊑ G' ∧ M ⊑ M' ∧ ds1 = ds ∧
        V ⊑ Vdeq.(dv_in) ∧ Vdeq.(dv_comm) = V' ∧
        ( (* EMPTY case *)
          (v = 0 ∧ deq = EmpDeq ∧
            deqId = length G.(Es) ∧
            G'.(Es) = G.(Es) ++ [mkGraphEvent deq Vdeq M'] ∧
            ds' = ds ∧
            {[deqId]} ∪ M ⊆ M' ∧ deqId ∉ M ∧
            (* If the consumer got an empty dequeue, then it must have dequeued
            all enqueues that it has seen. *)
            (∀ i' enqId', es !! i' = Some enqId' → enqId' ∈ M' → is_Some (ds !! i')))
        ∨ (* successful case *)
          (0 < v ∧ is_enqueue enq v ∧ is_dequeue deq v ∧
          deqId = length G.(Es) ∧
          G'.(Es) = G.(Es) ++ [mkGraphEvent deq Vdeq M'] ∧
          ds' = ds ++ [deqId] ∧
          es !! i = Some enqId ∧
          enqId ∈ M' ∧ deqId ∈ M' ∧ deqId ∉ M ∧
          ∃ eV, G.(Es) !! enqId = Some eV ∧ eV.(ge_event) = enq ∧ eV.(ge_lview) ⊆ M') ) ⌝,
      RET #v, emp >>>
  .


Record spsc_spec {Σ} `{!noprolG Σ, !inG Σ (graphR qevent)} {QC} := SPSCSpec {
  spsc_core_spec :> spec_graph.core_queue_spec Σ QC;

  (* predicates *)
  Producer : ProducerT Σ;
  Consumer : ConsumerT Σ;
  SPSCInv : SPSCInvT Σ;

  (** predicates properties *)
  SPSCInv_Timeless : ∀ γg γed q G es ds,
    Timeless (SPSCInv γg γed q G es ds);
  SPSCInv_Objective : ∀ γg γed q G es ds,
    Objective (SPSCInv γg γed q G es ds);
  SPSCInv_matches : ∀ γg γed q G es ds,
    SPSCInv γg γed q G es ds ⊢ ⌜ matches G es ds ⌝;
  SPSCInv_QueueInv_acc : ∀ γg γed q G es ds,
    SPSCInv γg γed q G es ds ⊢
      spsc_core_spec.(QueueInv) γg q G ∗
      (spsc_core_spec.(QueueInv) γg q G -∗ SPSCInv γg γed q G es ds);

  Producer_exclusive : ∀ N γg γed q G1 G2 M1 M2 es1 es2,
    Producer N γg γed q G1 M1 es1 -∗ Producer N γg γed q G2 M2 es2 -∗ False ;
  Producer_QueueLocal : ∀ N γg γed q G M es,
    Producer N γg γed q G M es ⊢ spsc_core_spec.(QueueLocal) N γg q G M;
  Producer_Produced : ∀ N γg γed q G M es,
    Producer N γg γed q G M es ⊢ ⌜ Produced G es ⌝;
  Producer_agree : ∀ N γg γed q G G' M es es' ds,
    SPSCInv γg γed q G es ds -∗ Producer N γg γed q G' M es' -∗
    ⌜ es = es' ⌝;

  Consumer_exclusive : ∀ N γg γed q G1 G2 M1 M2 ds1 ds2,
    Consumer N γg γed q G1 M1 ds1 -∗ Consumer N γg γed q G2 M2 ds2 -∗ False ;
  Consumer_QueueLocal : ∀ N γg γed q G M ds,
    Consumer N γg γed q G M ds ⊢ spsc_core_spec.(QueueLocal) N γg q G M;
  Consumer_Consumed : ∀ N γg γed q G M ds,
    Consumer N γg γed q G M ds ⊢ ⌜ Consumed G ds ⌝;
  Consumer_agree : ∀ N γg γed q G G' M es ds ds',
    SPSCInv γg γed q G es ds -∗ Consumer N γg γed q G' M ds' -∗
    ⌜ ds = ds' ⌝;

  (* operations specs *)
  new_queue_spsc_spec : new_queue_spsc_spec' spsc_core_spec.(new_queue) Producer Consumer SPSCInv;
  enqueue_spsc_spec : enqueue_spsc_spec' spsc_core_spec.(enqueue) Producer SPSCInv;
  dequeue_spsc_spec : dequeue_spsc_spec' spsc_core_spec.(dequeue) Consumer SPSCInv;
}.

Arguments spsc_spec _ {_ _} _.

Section properties.
Lemma Produced_mono G G' es (SubGG' : G ⊑ G') :
  Produced G es → Produced G' es.
Proof.
  destruct SubGG'. destruct 1. constructor.
  - intros. specialize (ENQS _ _ Ei) as (eV & v &?&?). exists eV, v.
    split; [by eapply prefix_lookup_Some|done].
  - intros ?????????.
    specialize (ENQS _ _ EID2) as (eV2' & ? & EV2' & ?).
    eapply (ENQ_SEQ i1 i2); [done|done|by eapply prefix_lookup_inv|done].
Qed.

Lemma Consumed_mono G G' ds (SubGG' : G ⊑ G') :
  Consumed G ds → Consumed G' ds.
Proof.
  destruct SubGG'. destruct 1. constructor.
  - intros. specialize (DEQS _ _ Di) as (dV & v &?&?). exists dV, v.
    split; [by eapply prefix_lookup_Some|done].
  - intros ?????????.
    specialize (DEQS _ _ EID2) as (dV2' & ? & DV2' &?).
    eapply (DEQ_SEQ i1 i2); [done|done|by eapply prefix_lookup_inv|done].
Qed.

Lemma EmpDeqs_mono G G' xs (SubGG' : G ⊑ G') :
  EmpDeqs G xs → EmpDeqs G' xs.
Proof.
  destruct SubGG'. destruct 1. constructor.
  - intros. specialize (EMPS _ _ XI) as (xV & ? & ?). exists xV.
    split; [by eapply prefix_lookup_Some|done].
Qed.

Lemma matches_stable G G' es ds (SubGG' : G ⊑ G') (ComG' : G'.(com) = G.(com)) :
  matches G es ds → matches G' es ds.
Proof.
  destruct SubGG'. intros MATCH ??. specialize (MATCH i d). split.
  - move/MATCH => [e][Ei]Com. eauto.
  - move=> [e][Ei]Com. apply MATCH. exists e. split; [done|]. set_solver.
Qed.
End properties.
