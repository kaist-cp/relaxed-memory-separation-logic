(* ACKNOWLEGEMENT: Part of the ghost state construction for this proof is
  inspired by the SC Herlihy-Wing queue proof with Prophecy Variables:
  https://gitlab.mpi-sws.org/iris/examples/-/blob/f84cbf7d88fbf5782238099bda39ff6236fc2b9f/theories/logatom/herlihy_wing_queue/hwq.v *)

From iris.algebra Require Import auth csum gmap agree excl numbers.
From iris.algebra Require Import lib.mono_nat.

From iris.base_logic.lib Require Import mono_nat.
From iris.proofmode Require Import tactics.

From gpfsl.algebra Require Import to_agree.
From gpfsl.logic Require Import logatom atomics invariants.

From gpfsl.logic Require Import
  repeat_loop new_delete atomic_exchange diverge arith.
From gpfsl.examples Require Import map_seq big_op.
From gpfsl.examples.queue Require Import spec_graph code_hw.

Require Import iris.prelude.options.

#[local] Notation back := 0%nat (only parsing).
#[local] Notation buff := 1%nat (only parsing).

#[local] Notation event_list := (event_list qevent).
#[local] Notation graph_event := (graph_event qevent).
#[local] Notation graph := (graph qevent).

Implicit Types (l: loc) (tid: thread_id) (G: graph) (γ: gname) (η: gname).

(* Namespace for our invariants *)
Definition hwqN (N: namespace) (q : loc) := N .@ q.

(* Ghost Construction we need *)
Definition backUR := mono_natUR.

(* a persistent map from enqueued event ids to slots. *)
Definition emapUR := authUR $ agreeMR event_id nat.

Definition prod2UR A B C := prodUR (prodUR A B) C.
Definition prod3UR A B C D := prodUR (prod2UR A B C) D.

Definition oneshotUR :=
  optionUR $ csumR (exclR unitR) (agreeR (leibnizO (view * event_id))).
Definition shot (V : view) (enq : event_id) : oneshotUR :=
  Some $ Cinr $ to_agree (V, enq).
Definition not_shot : oneshotUR := Some $ Cinl $ Excl ().

Definition oagreeUR (A: Type) := (optionUR $ agreeR (leibnizO A)).

Definition per_slotUR :=
  prod3UR
    (oagreeUR (Z * logView))  (* (value, hb set) of the slot *)
    oneshotUR                 (* oneshot of the slot to acquire and enqueue *)
    (oagreeUR view)           (* dequeue view *)
    (oagreeUR gname)          (* name of the slot *)
    .
Definition slotUR := authUR $ gmapUR nat per_slotUR.

Definition hwqR :=
  prod3UR
    (oagreeUR gname) (* name of the back field *)
    backUR           (* to show that back only inscreases *)
    slotUR           (* map of the slot data *)
    emapUR           (* map from events to slots *)
    .

Class hwqG Σ := HwqG {
  hwq_graphG : inG Σ (graphR qevent);
  hwq_queueG : inG Σ hwqR;
}.

Definition hwqΣ : gFunctors :=
  #[GFunctor (graphR qevent); GFunctor hwqR].

Global Instance subG_hwqΣ {Σ} : subG hwqΣ Σ → hwqG Σ.
Proof. solve_inG. Qed.

Lemma Some_option_included {A : cmra} (a : A) (mb : option A) :
  Some a ≼ mb → ∃ b, mb = Some b ∧ Some a ≼ Some b.
Proof.
  destruct mb as [b|].
  - naive_solver.
  - by intros [?|(_ & b & _ & ? & _)]%option_included.
Qed.

Lemma Some_option_included_total `{CmraTotal A} (a : A) (mb : option A) :
  Some a ≼ mb → ∃ b, mb = Some b ∧ a ≼ b.
Proof.
  intros [?|(? & b & ? & -> & ?)]%option_included_total; [done|].
  exists b. by simplify_eq.
Qed.

Lemma Some_prod3UR_included {A B C D : ucmra} (a b : prod3UR A B C D) :
  Some a ≼ Some b →
  Some a.1.1.1 ≼ Some b.1.1.1 ∧
  Some a.1.1.2 ≼ Some b.1.1.2 ∧ Some a.1.2 ≼ Some b.1.2 ∧ Some a.2 ≼ Some b.2.
Proof.
  destruct a as [[[a1 a2] a3] a4]. destruct b as [[[b1 b2] b3] b4]. simpl.
  by intros [[[??]%Some_pair_included ?]%Some_pair_included ?]%Some_pair_included.
Qed.

Lemma Some_agree_included {A : Type} (a : A) (b : oagreeUR A) :
  (Some (to_agree a : agreeR (leibnizO A))) ≼ b → ✓ b →
  b ≡ Some (to_agree a).
Proof.
  intros (b' & -> & IN)%Some_option_included_total [a' Eqa']%to_agree_uninj.
  move : IN. rewrite -{1}Eqa' to_agree_included. inversion 1. subst a'.
  by rewrite Eqa'.
Qed.

Lemma Some_agree_included' {A : Type} (a : A) (b : oagreeUR A) :
  Some (Some (to_agree a : agreeR (leibnizO A))) ≼ Some b → ✓ b →
  b ≡ Some (to_agree a).
Proof. rewrite Some_included_total. apply Some_agree_included. Qed.

Lemma Some_not_shot_included (b : oneshotUR) :
  Some not_shot ≼ Some b → ✓ b → b = not_shot.
Proof.
  rewrite Some_included_total => IN VAL.
  apply Some_option_included in IN as (b' & -> & IN2%Some_included_exclusive);
    [|apply _|done].
  inversion IN2; by simplify_eq.
Qed.

Lemma Some_shot_included (b : oneshotUR) V e :
  Some (shot V e) ≼ Some b → ✓ b → b ≡ shot V e.
Proof.
  rewrite Some_included_total.
  intros (b' & -> & IN%Some_csum_included)%Some_option_included VAL.
  destruct IN as [->|[(?&?&?&_)|(? & b1 & Eq1 & -> & IN)]]; [done|done|..].
  simplify_eq. rewrite /shot. do 2 f_equiv.
  by apply Some_equiv_inj, (Some_agree_included _ _ IN).
Qed.

(* Slot states *)
(* We can do better than Z, but our language doesn't have comparison for
  arbitrary literals, and comparison is needed to check for failures.
  So we restrict the usage of the queue to Z, for now. *)
Definition enqueue_info : Type := (Z * logView) * (view * event_id).
Definition einf_val (ei : enqueue_info) : Z := ei.1.1.
Definition einf_lview (ei : enqueue_info) : logView := ei.1.2.
Definition einf_view (ei : enqueue_info) : view := ei.2.1.
Definition einf_evt (ei : enqueue_info) : event_id := ei.2.2.

Inductive state :=
  | SlotUnused
  | SlotPending (v : Z) (M : logView)
  | SlotEnqueued (enq : enqueue_info)
  | SlotDequeued (enq : enqueue_info) (Vdeq : view).

Implicit Type slots : gmap nat (gname * state).

(* History shapes of locations. *)
Definition toSlotHist0 start (LVs : list view) : absHist :=
  map_seqP start (zip (repeat #0 (length LVs)) LVs).

Definition toSlotHist (s: state) t0 LVs0 t1 LVs1 : absHist :=
  let ζ0 := toSlotHist0 t0 LVs0 in
  match s with
  | SlotUnused | SlotPending _ _ => ζ0
  | SlotEnqueued (v,_,(Ve,_)) => <[t1 := (#v, Ve)]>ζ0
  | SlotDequeued (v,_,(Ve,_)) Vd =>
      (toSlotHist0 (t1 + 1)%positive (Vd :: LVs1)) ∪ <[t1 := (#v, Ve)]>ζ0
  end.

Definition toBackHist (n : nat) start (LVs : list view) : absHist :=
  map_seqP start (zip (LitV ∘ (LitInt ∘ Z.of_nat) <$> seq 0 (S n)) LVs).

Definition get_enqInfo (s : state) : option enqueue_info :=
  match s with
  | SlotUnused | SlotPending _ _ => None
  | SlotEnqueued ei | SlotDequeued ei _ => Some ei
  end.

Definition get_enqInfo_L (L : list (gname * state)) (i : nat) : option enqueue_info :=
  s ← snd <$> L !! i; get_enqInfo s.

Implicit Type (T: gmap event_id nat).
(* Pure Coq properties of the Queue implementation *)
Record QueueProps (sz : nat) (n : nat) (L : list (gname * state)) T G
  : Prop := mkQueueProps {
  qu_len : length L = sz ;
  (* unused slots *)
  qu_unused : ∀ i, (n `min` sz ≤ i < sz)%nat ↔ snd <$> (L !! i) = Some SlotUnused ;
  (* dequeued slots *)
  qu_dequeued :
    ∀ e, (∃ i v V M Vd, snd <$> L !! i = Some $ SlotDequeued (v,M,(V, e)) Vd)
      ↔ e ∈ (elements G.(so)).*1 ;
  (* enqueued slots *)
  qu_enqueued : ∀ e v V, (∃ i M, get_enqInfo_L L i = Some (v,M,(V,e))) ↔
                         (∃ eV, G.(Es) !! e = Some eV ∧ eV.(ge_event) = Enq v ∧
                            eV.(ge_view).(dv_comm) = V) ;
  (* enqueued events *)
  qu_enq_event : ∀ e i, (∃ v M V, get_enqInfo_L L i = Some (v,M,(V,e))) ↔
                        T !! e = Some i ;
  (* enqueue order *)
  qu_enq_ordered :
    ∀ i1 i2 e1 e2 eV2,
      T !! e1 = Some i1 → T !! e2 = Some i2 →
      G.(Es) !! e2 = Some eV2 →
      (* if e1 happens-before e2, then its slot i1 should be before i2's slot i2 *)
      e1 ∈ eV2.(ge_lview) → (i1 ≤ i2)%nat ;
  (* dequeue order *)
  qu_deq_ordered :
    ∀ i1 i2 e1 e2 d2 dV2,
      (* if e1 and e2 are two enqueues where e1's slot i1 is smaller than e2's slot i2 *)
      T !! e1 = Some i1 → T !! e2 = Some i2 → (i1 ≤ i2)%nat →
      (* and d2 is the dequeue of e2 that happens to observe e1 *)
      (e2, d2) ∈ G.(com) →
      G.(Es) !! d2 = Some dV2 → e1 ∈ dV2.(ge_lview) →
      (* then e1 must have been dequeued (FIFO) *)
      ∃ d1, (e1, d1) ∈ G.(com)
      (* this works for strong HWqueue, but not the weak version:
        and d2 must have also observed d1
        ∧ d1 ∈ dV2.(ge_lview) *) ;
}.

Definition enq_map_enqueued T (E : event_list) : Prop :=
  ∀ e, (∃ i, T !! e = Some i) ↔ (∃ eV v, E !! e = Some eV ∧ eV.(ge_event) = Enq v).

Lemma QueueProps_enq_map_enqueued {sz n L T G} :
  QueueProps sz n L T G → enq_map_enqueued T G.(Es).
Proof.
  intros [_ _ _ HENQ1 HENQ2 _ _].
  intros e. split.
  - intros [i (v & M & V & Eqi)%HENQ2].
    destruct (HENQ1 e v V) as [(eV & EqeV & Eqv & ?) _]. { by do 2 eexists. }
    by do 2 eexists.
  - intros (eV & v & Eqe & Eqv).
    destruct (HENQ1 e v eV.(ge_view).(dv_comm)) as [_ (i & M & Eqi)]. { by eexists. }
    exists i. destruct (HENQ2 e i) as [Eq _]. apply Eq. by do 3 eexists.
Qed.

Lemma enq_map_enqueued_mono_inv {T E T' E'} e i :
  enq_map_enqueued T E → enq_map_enqueued T' E' →
  T ⊆ T' → E ⊑ E' →
  is_Some (E !! e) →
  T' !! e = Some i → T !! e = Some i.
Proof.
  intros ENTE ENTE' SubT SubE Ine Eqe.
  apply (map_lookup_subseteq_eq_inv _ _ _ _ SubT Eqe), ENTE.
  destruct (ENTE' e) as [(eV & v & Eqe1 & Eqv) _]. { by exists i. }
  exists eV, v. split; [|done]. apply (prefix_lookup_inv _ _ _ _ Eqe1 Ine SubE).
Qed.

Lemma QueueProps_inj {sz n L T G} :
  QueueProps sz n L T G →
  ∀ i e1 e2, T !! e1 = Some i → T !! e2 = Some i → e1 = e2.
Proof.
  intros [_ _ _  _ HENQ _ _] i e1 e2 Eqi1 Eqi2.
  apply HENQ in Eqi1 as (?&?&?& Eq1). apply HENQ in Eqi2 as (?&?&?& Eq2).
  rewrite Eq1 in Eq2. by inversion Eq2.
Qed.

Lemma get_enqInfo_L_enqueued L i ei :
  snd <$> L !! i = Some $ SlotEnqueued ei →
  get_enqInfo_L L i = Some ei.
Proof. rewrite /get_enqInfo_L. by intros ->. Qed.

Lemma get_enqInfo_L_dequeued L i ei Vd :
  snd <$> L !! i = Some $ SlotDequeued ei Vd →
  get_enqInfo_L L i = Some ei.
Proof. rewrite /get_enqInfo_L. by intros ->. Qed.

Lemma get_enqInfo_L_Some L i ei :
  get_enqInfo_L L i = Some ei ↔
  ∃ γ, L !! i = Some (γ, SlotEnqueued ei)
    ∨ ∃ Vd, L !! i = Some (γ, SlotDequeued ei Vd).
Proof.
  split.
  - intros [? [[[γ s] [Eq ->]]%fmap_Some Eqs]]%bind_Some.
    destruct s as [| |[[v V]]|[[v V]]]; simpl in Eqs; simplify_eq; rewrite Eq;
      simpl; naive_solver.
  - intros (γ & [Eqi|[Vd Eqi]]).
    + eapply get_enqInfo_L_enqueued. by rewrite Eqi.
    + eapply get_enqInfo_L_dequeued. by rewrite Eqi.
Qed.

Lemma get_enqInfo_L_insert_ne L i i' γs' :
  i ≠ i' → get_enqInfo_L (<[i' := γs']>L) i = get_enqInfo_L L i.
Proof. intros NEq. by rewrite /get_enqInfo_L list_lookup_insert_ne. Qed.

Lemma get_enqInfo_L_insert L i γs :
  (i < length L)%nat → get_enqInfo_L (<[i := γs]>L) i = get_enqInfo γs.2.
Proof. intros ?. by rewrite /get_enqInfo_L list_lookup_insert. Qed.

Lemma get_enqInfo_L_insert_dequeue {L i γ v M V e Vd} i' :
  L !! i = Some (γ, SlotEnqueued (v,M,(V,e))) →
  get_enqInfo_L (<[i := (γ, SlotDequeued (v,M,(V,e)) Vd)]>L) i' = get_enqInfo_L L i'.
Proof.
  intros Eqi. case (decide (i' = i)) => [->|?].
  - rewrite get_enqInfo_L_insert /=.
    + symmetry. eapply get_enqInfo_L_enqueued. by rewrite Eqi.
    + move : Eqi. apply lookup_lt_Some.
  - by apply get_enqInfo_L_insert_ne.
Qed.

Lemma toSlotHist0_lookup_Some {t0 LVs t v} (V : view) :
  (toSlotHist0 t0 LVs) !! t = Some (v, V) ↔
  (t0 ≤ t)%positive
  ∧ (Pos.to_nat t - Pos.to_nat t0 < length LVs)%nat
  ∧ v = #0%nat
  ∧ LVs !! (Pos.to_nat t - Pos.to_nat t0)%nat = Some V.
Proof.
  rewrite lookup_map_seqP_Some lookup_zip_with_Some.
  setoid_rewrite repeat_lookup_Some_iff. naive_solver.
Qed.

Lemma toSlotHist0_lookup_None {t0 LVs t} :
  (toSlotHist0 t0 LVs) !! t = None ↔
  (t < t0)%positive ∨ (t0 +p (length LVs) ≤ t)%positive.
Proof. by rewrite lookup_map_seqP_None zip_with_length_r_eq // repeat_length. Qed.

Lemma toSlotHist0_lookup_Some_None {t0 LVs t p} :
  toSlotHist0 t0 LVs !! t = Some p →
  toSlotHist0 t0 LVs !! (t + 1)%positive = None →
  (Pos.to_nat (t + 1)%positive - Pos.to_nat t0)%nat = length LVs
  ∧ (1 ≤ length LVs)%nat.
Proof.
  intros EqS EqN.
  assert (EqL := lookup_map_seqP_last_idx _ _ _ _ EqS EqN).
  destruct p as [v V].
  apply toSlotHist0_lookup_Some in EqS as [Letx0 [on [Eqv Eqt]]].
  have EqL1 :  (1 ≤ length LVs)%nat.
  { clear -Eqt Letx0. apply lookup_lt_Some in Eqt. lia. }
  move : EqL. rewrite zip_with_length_r_eq; [|by rewrite repeat_length].
  rewrite /pos_add_nat; lia.
Qed.

Lemma toSlotHist0_insert_0 {t0 LVs t} V :
  (Pos.to_nat t - Pos.to_nat t0)%nat = length LVs →
  (1 ≤ length LVs)%nat →
  <[t := (#0, V)]>(toSlotHist0 t0 LVs) =
  toSlotHist0 t0 (LVs ++ [V]).
Proof.
  intros Eq ?. apply map_eq.
  intros i. case (decide (i = t)) => [->|?].
  - rewrite lookup_insert. symmetry.
    apply toSlotHist0_lookup_Some. rewrite Eq.
    repeat split; [lia|rewrite app_length /=; lia|apply lookup_app_1_eq].
  - rewrite lookup_insert_ne; [|done].
    destruct (toSlotHist0 t0 LVs !! i) as [[vi Vi]|] eqn:Eqi; rewrite Eqi; symmetry.
    + apply toSlotHist0_lookup_Some in Eqi as (Letn & LtL & -> & Eq1).
      apply toSlotHist0_lookup_Some.
      rewrite (lookup_app_l_Some _ _ _ _ Eq1) app_length /=. naive_solver lia.
    + apply toSlotHist0_lookup_None.
      apply toSlotHist0_lookup_None in Eqi as [?|Eqi]; [by left|right].
      rewrite app_length /=. move : Eqi.
      rewrite Nat.add_1_r pos_add_succ_r_2.
      rewrite (_: t0 +p length LVs = t); [lia|]. rewrite -Eq /pos_add_nat; lia.
Qed.

Lemma toSlotHist0_lookup_Some_None_insert_0 {t0 LVs t p} V :
  toSlotHist0 t0 LVs !! t = Some p →
  toSlotHist0 t0 LVs !! (t + 1)%positive = None →
  <[(t + 1)%positive := (#0, V)]>(toSlotHist0 t0 LVs) =
  toSlotHist0 t0 (LVs ++ [V]).
Proof.
  intros EqS EqN. destruct (toSlotHist0_lookup_Some_None EqS EqN).
  by apply toSlotHist0_insert_0.
Qed.

Lemma toSlotHist0_singleton t0 V0 :
  toSlotHist0 t0 [V0] = {[t0 := (#0, V0)]}.
Proof. done. Qed.

Lemma toSlotHist0_int_only t0 LVs0 :
  int_only_hist (toSlotHist0 t0 LVs0).
Proof.
  intros t v [[v' V] [Eq1 (_&_&->&_)%toSlotHist0_lookup_Some]]%lookup_fmap_Some'.
  simpl in Eq1. subst v. by eexists.
Qed.

Lemma toSlotHist_int_only s t0 LVs0 t1 LVs1 :
  int_only_hist (toSlotHist s t0 LVs0 t1 LVs1).
Proof.
  destruct s as [| |[[v M] [Ve e]]|[[v M] [Ve e]] Vd];
    [apply toSlotHist0_int_only..| |]; simpl.
  - intros t vt. case (decide (t = t1)) => [->|?].
    + rewrite lookup_insert /=. inversion 1. by eexists.
    + rewrite lookup_insert_ne; [|done]. by apply toSlotHist0_int_only.
  - intros t vt [[v' V] [Eq1 Eq2]]%lookup_fmap_Some'.
    simpl in Eq1. subst v'.
    apply lookup_union_Some_raw in Eq2 as [Eq2|[EqN Eq2]].
    + apply (toSlotHist0_int_only (t1+1) (Vd :: LVs1) t). by rewrite Eq2.
    + case (decide (t = t1)) => ?.
      * subst t. rewrite lookup_insert /= in Eq2. inversion Eq2. by eexists.
      * rewrite lookup_insert_ne in Eq2; [|done].
        apply (toSlotHist0_int_only t0 LVs0 t). by rewrite Eq2.
Qed.

Lemma toSlotHist_lookup_Some_None {s t0 LVs0 t1 LVs1 t} {z : Z} {V} :
  (t0 +p length LVs0 ≤ t1)%positive →
  z ≠ 0 →
  toSlotHist s t0 LVs0 t1 LVs1 !! t = Some (#z, V) →
  toSlotHist s t0 LVs0 t1 LVs1 !! (t + 1)%positive = None →
  (t0 +p length LVs0 ≤ t + 1)%positive ∧ t = t1 ∧
  ∃ e M, s = SlotEnqueued (z,M,(V,e)).
Proof.
  destruct s as [| |[[v M] [Ve e]]|[[v M] [Ve e]] Vd]; simpl => Let1 NEq0.
  - intros (_&_&?&_)%toSlotHist0_lookup_Some. by simplify_eq.
  - intros (_&_&?&_)%toSlotHist0_lookup_Some. by simplify_eq.
  - case (decide (t = t1)) => [->|?].
    + rewrite lookup_insert. inversion 1. subst v Ve.
      intros _. split; last split; [lia|done|by do 2 eexists].
    + rewrite lookup_insert_ne; [|done].
      intros (_&_&?&_)%toSlotHist0_lookup_Some. by simplify_eq.
  - intros [(_&_&?&_)%toSlotHist0_lookup_Some|[EqN EqS]]%lookup_union_Some_raw.
    { by simplify_eq. }
    intros [EqN1%toSlotHist0_lookup_None _]%lookup_union_None.
    exfalso. rewrite lookup_insert_ne in EqS.
    + apply toSlotHist0_lookup_Some in EqS as (_&_&?&_). by simplify_eq.
    + intros ->. destruct EqN1 as [EqN1|EqN1]; first by lia.
      rewrite /pos_add_nat /= in EqN1. lia.
Qed.

Lemma toSlotHist_insert_0 {s t0 LVs0 t1 LVs1 t V} Vn :
  toSlotHist s t0 LVs0 t1 LVs1 !! t = Some (#0, V) →
  toSlotHist s t0 LVs0 t1 LVs1 !! (t + 1)%positive = None →
  (t0 +p length LVs0 ≤ t1)%positive →
  (match s with | SlotEnqueued (v,_,_) | SlotDequeued (v,_,_) _ => 0 < v | _ => True end) →
  ∃ LVs0' LVs1' t1',
  (LVs0' = LVs0 ∧ LVs1' = LVs1 ++ [Vn] ∧
    (match s with | SlotDequeued _ Vd => V ∈ Vd :: LVs1 | _ => True end)
    ∨ LVs0' = LVs0 ++ [Vn] ∧ LVs1' = LVs1) ∧
  (t0 +p length LVs0' ≤ t1')%positive ∧
  <[(t + 1)%positive := (#0, Vn)]> (toSlotHist s t0 LVs0 t1 LVs1) =
  toSlotHist s t0 LVs0' t1' LVs1'.
Proof.
  destruct s as [| |[[v M] [Ve e]]|[[v M] [Ve e]] Vd]; simpl; intros EqS EqN Let0 NE0.
  - exists (LVs0 ++ [Vn]), LVs1, (t1 + 1)%positive. split; [naive_solver|].
    split. { rewrite app_length /= Nat.add_1_r pos_add_succ_r_2. lia. }
    by apply (toSlotHist0_lookup_Some_None_insert_0 _ EqS EqN).
  - exists (LVs0 ++ [Vn]), LVs1, (t1 + 1)%positive. split; [naive_solver|].
    split. { rewrite app_length /= Nat.add_1_r pos_add_succ_r_2. lia. }
    by apply (toSlotHist0_lookup_Some_None_insert_0 _ EqS EqN).
  - assert (t ≠ t1).
    { intros ->. rewrite lookup_insert in EqS. inversion EqS. subst v; lia. }
    rewrite lookup_insert_ne in EqS; [|done].
    apply lookup_insert_None in EqN as [EqN ?].
    exists (LVs0 ++ [Vn]), LVs1, t1. split; [naive_solver|]. split.
    + rewrite app_length /= Nat.add_1_r pos_add_succ_r_2.
      destruct (toSlotHist0_lookup_Some_None EqS EqN) as [Le1 Le2].
      assert ((t0 +p length LVs0) = t + 1)%positive as Eq1.
      { rewrite /pos_add_nat. lia. }
      rewrite Eq1. rewrite Eq1 in Let0. lia.
    + rewrite insert_commute; [|done]. f_equal.
      by apply (toSlotHist0_lookup_Some_None_insert_0 _ EqS EqN).
  - apply lookup_union_None in EqN as [EqN1 [EqN2 ?]%lookup_insert_None].
    apply lookup_union_Some_raw in EqS as [EqS|[EqS1 EqS2]].
    { exists LVs0, (LVs1 ++ [Vn]), t1. split; last split; [|done|].
      - left. do 2 (split; [done|]).
        apply toSlotHist0_lookup_Some in EqS as (_ & _ & _ & EqL).
        apply elem_of_list_lookup. by eexists.
      - rewrite insert_union_l. f_equal.
        by apply (toSlotHist0_lookup_Some_None_insert_0 _ EqS EqN1). }
    assert (t ≠ t1).
    { intros ->. rewrite lookup_insert in EqS2. inversion EqS2. subst v; lia. }
    rewrite lookup_insert_ne in EqS2; [|done].
    exists (LVs0 ++ [Vn]), LVs1, t1. split; [naive_solver|]. split.
    + rewrite app_length /= Nat.add_1_r pos_add_succ_r_2.
      destruct (toSlotHist0_lookup_Some_None EqS2 EqN2) as [Le1 Le2].
      assert ((t0 +p length LVs0) = t + 1)%positive as Eq1.
      { rewrite /pos_add_nat. lia. }
      rewrite Eq1. rewrite Eq1 in Let0. lia.
    + rewrite insert_union_r; [|done]. f_equal.
      rewrite insert_commute; [|done]. f_equal.
      by apply (toSlotHist0_lookup_Some_None_insert_0 _ EqS2 EqN2).
Qed.

Lemma toSlotHist_lookup_dequeued_gt {t0 LVs0 t1 LVs1 ei Vd t2 v V} :
  toSlotHist (SlotDequeued ei Vd) t0 LVs0 t1 LVs1 !! t2 = Some (v, V) →
  (t0 +p length LVs0 ≤ t1)%positive →
  (t1 < t2)%positive → V ∈ Vd :: LVs1.
Proof.
  destruct ei as [[ve M][Ve e]]; simpl.
  intros Eq Let1 Ltt1.
  apply lookup_union_Some_raw in Eq as [Eq1|[Eq Eq1]].
  - apply toSlotHist0_lookup_Some in Eq1 as (_ & _ & _ & EqL).
    apply elem_of_list_lookup. by eexists.
  - rewrite lookup_insert_ne in Eq1; [|lia].
    apply toSlotHist0_lookup_Some in Eq1 as (_ & LtL & _).
    apply toSlotHist0_lookup_None in Eq as [Lt21|Lt21]; [lia|].
    rewrite /= /pos_add_nat in Lt21. rewrite /pos_add_nat in Let1. lia.
Qed.

Lemma toBackHist_lookup_Some {n t0 LVs t v} (V : view) :
  (toBackHist n t0 LVs) !! t = Some (v, V) ↔
  (t0 ≤ t)%positive
  ∧ v = #(Pos.to_nat t - Pos.to_nat t0)%nat
  ∧ (Pos.to_nat t - Pos.to_nat t0 < S n)%nat
  ∧ LVs !! (Pos.to_nat t - Pos.to_nat t0)%nat = Some V.
Proof.
  rewrite lookup_map_seqP_Some lookup_zip_with_Some.
  setoid_rewrite list_lookup_fmap. setoid_rewrite fmap_Some.
  setoid_rewrite lookup_seq. simpl. naive_solver.
Qed.

Lemma toBackHist_lookup_None {n t0 LVs t} :
  length LVs = S n →
  toBackHist n t0 LVs !! t = None ↔
  (t < t0)%positive ∨ (t0 +p (length LVs) ≤ t)%positive.
Proof.
  intros EqL. rewrite lookup_map_seqP_None zip_with_length_r_eq; [done|].
  by rewrite fmap_length seq_length.
Qed.

Lemma toBackHist_lookup_Some_None {n t0 LVs t p} :
  length LVs = S n →
  toBackHist n t0 LVs !! t = Some p →
  toBackHist n t0 LVs !! (t + 1)%positive = None →
  (Pos.to_nat (t + 1)%positive - Pos.to_nat t0)%nat = S n.
Proof.
  intros EqLn EqS EqN.
  assert (EqL := lookup_map_seqP_last_idx _ _ _ _ EqS EqN). move : EqL.
  rewrite zip_with_length_r_eq; last by rewrite fmap_length seq_length.
  by rewrite EqLn /pos_add_nat; lia.
Qed.

Lemma toBackHist_int_only n s LVs :
  int_only_hist (toBackHist n s LVs).
Proof.
  intros t v [[v' V] [Eq1 (_ & -> & _)%toBackHist_lookup_Some]]%lookup_fmap_Some'.
  simpl in Eq1. subst v. by eexists.
Qed.

Lemma toBackHist_insert n t0 LVs t V :
  (Pos.to_nat t - Pos.to_nat t0)%nat = S n →
  length LVs = S n →
  <[t := (#(S n), V)]>(toBackHist n t0 LVs) =
  toBackHist (S n) t0 (LVs ++ [V]).
Proof.
  intros Eq1 Eq2. apply map_eq.
  intros i. case (decide (i = t)) => [->|?].
  - rewrite lookup_insert. symmetry.
    apply toBackHist_lookup_Some. split; [lia|]. split; [by do 3 f_equal|].
    split; [lia|]. rewrite Eq1 -Eq2. by apply lookup_app_1_eq.
  - rewrite lookup_insert_ne; [|done].
    destruct (toBackHist n t0 LVs !! i) as [[vi Vi]|] eqn:Eqi;
      rewrite Eqi; symmetry.
    + apply toBackHist_lookup_Some in Eqi as (Letn & -> & ? & Eq3).
      apply toBackHist_lookup_Some. do 2 (split; [done|]).
      split; [lia|]. by apply (lookup_app_l_Some _ _ _ _ Eq3).
    + apply toBackHist_lookup_None. { rewrite app_length /= Eq2. lia. }
      apply toBackHist_lookup_None in Eqi as [?|Eqi]; [by left|right|done].
      rewrite app_length /=. move : Eqi.
      rewrite Nat.add_1_r pos_add_succ_r_2 Eq2.
      rewrite (_: t0 +p S n = t); [lia|]. rewrite -Eq1 /pos_add_nat. lia.
Qed.

Lemma toBackHist_lookup_Some_order {n t0 LVs t1 V1 t2 V2} {v1 v2 : nat} :
  (toBackHist n t0 LVs) !! t1 = Some (#v1, V1) →
  (toBackHist n t0 LVs) !! t2 = Some (#v2, V2) →
  (t1 ≤ t2)%positive → (v1 ≤ v2)%nat.
Proof.
  intros (Get1 & Eqv1 & Lev1 & Eqt1)%toBackHist_lookup_Some
         (Get2 & Eqv2 & Lev2 & Eqt2)%toBackHist_lookup_Some.
  simplify_eq. lia.
Qed.

Local Notation SomeA x := (Some $ to_agree x).

(* Ghost ownership *)
Section ghost.
Context `{!inG Σ hwqR}.
#[local] Notation iProp := (iProp Σ).
#[local] Notation vProp := (vProp Σ).

Definition to_back_value (γb : gname) (n : nat) : hwqR :=
  (SomeA γb, ●MN{#1} n, ε, ε).
Definition to_back_lb    (γb : gname) (n : nat) : hwqR :=
  (SomeA γb, ◯MN n, ε, ε).

(* State of the back field *)
Definition back_value γ γb n  : vProp := ⎡ own γ (to_back_value γb n) ⎤.
Definition back_lb    γ γb n  : vProp := ⎡ own γ (to_back_lb γb n)    ⎤.

#[global] Instance back_lb_persistent γ γb n : Persistent (back_lb γ γb n) := _.

(* State of the slots *)
Definition to_slot_state (s : state) :
  prod2UR
    (oagreeUR (Z * logView)) (* value of the slot *)
    oneshotUR                (* oneshot of the slot to acquire and enqueue *)
    (oagreeUR view)          (* dequeue view *) :=
  match s with
  | SlotUnused                    => (None, not_shot, None)
  | SlotPending v M               => (SomeA (v, M), not_shot , None)
  | SlotEnqueued (v,M,(Ve,e))     => (SomeA (v, M), shot Ve e, None)
  | SlotDequeued (v,M,(Ve,e)) Vd  => (SomeA (v, M), shot Ve e, SomeA Vd)
  end.

Definition to_slot_name γs : oagreeUR gname := SomeA γs.

Definition to_slot (γss : gname * state) : per_slotUR :=
  let '(γs, s) := γss in (to_slot_state s, to_slot_name γs).
Definition to_slots        slots    : slotUR := ● (to_slot <$> slots).
Definition to_enq_slots        T    : emapUR := ● (to_agreeM T).
Definition to_slots_master slots T  : hwqR   := (ε, ε, to_slots slots, to_enq_slots T).

Definition slots_master γ slots T : vProp := ⎡ own γ (to_slots_master slots T) ⎤.

Definition to_enq_slots_snap T  : hwqR := (ε, ε, ε, ◯ (to_agreeM T)).
Definition enq_slots_snap γ T : vProp := ⎡ own γ (to_enq_slots_snap T) ⎤.

(* A witness that the slot i has name γs *)
Definition to_slot_name' i γs : hwqR := (ε, ε : backUR, ◯ {[i := (ε, to_slot_name γs)]}, ε).
Definition slot_name γ (i : nat) (γs : gname) : vProp :=
  ⎡ own (A:=hwqR) γ (to_slot_name' i γs) ⎤.
(* A token needed to reserve the slot i *)
Definition to_slot_reserve_tok i : hwqR := (ε, ε, ◯ {[i := (to_slot_state SlotUnused, ε)]}, ε).
Definition slot_reserve_tok γ (i : nat) : vProp :=
  ⎡ own (A:=hwqR) γ (to_slot_reserve_tok i) ⎤.
(* A token needed to write the value v to slot i *)
Definition to_slot_pending_tok (i : nat) (v : Z) M : hwqR := (ε, ε, ◯ {[i := (to_slot_state (SlotPending v M), ε)]}, ε).
Definition slot_pending_tok γ i v M : vProp :=
  ⎡ own (A:=hwqR) γ (to_slot_pending_tok i v M) ⎤.
(* A witness that the slot i has been enqueued with v *)
Definition to_slot_enqueued (i : nat) (v : Z) M Ve e : hwqR :=
  (ε, ε, ◯ {[i := (to_slot_state (SlotEnqueued (v, M,(Ve,e))), ε)]}, ◯ {[e := to_agree i]}).
Definition slot_enqueued γ (i : nat) (v : Z) M Ve e : vProp :=
  ⎡ own (A:=hwqR) γ (to_slot_enqueued i v M Ve e) ⎤.
(* A witness that the slot i has been dequeued with v *)
Definition to_slot_dequeued (i : nat) (v : Z) M Ve e Vd : hwqR :=
  (ε, ε, ◯ {[i := (to_slot_state (SlotDequeued (v,M,(Ve,e)) Vd), ε)]}, ◯ {[e := to_agree i]}).
Definition slot_dequeued γ (i : nat) (v : Z) M Ve e Vd : vProp :=
  ⎡ own (A:=hwqR) γ (to_slot_dequeued i v M Ve e  Vd) ⎤.

Definition to_slot_pre_enqueued (i : nat) v (M : logView) : hwqR :=
  (ε, ε, ◯ {[i := ((Some $ to_agree (v, M), ε, ε), ε)]}, ε).
Definition slot_pre_enqueued γ (i : nat) (M : logView) : vProp :=
  ∃ v, ⎡ own (A:=hwqR) γ (to_slot_pre_enqueued i v M) ⎤ .

#[global] Instance slot_name_persistent γ i γs : Persistent (slot_name γ i γs).
Proof.
  apply embed_persistent, own_core_persistent, pair_core_id; [|apply _].
  apply pair_core_id; [apply _|].
  by apply auth_frag_core_id, gmap_singleton_core_id, _.
Qed.
#[global] Instance slot_name_timeless γ i γs : Timeless (slot_name γ i γs) := _.
#[global] Instance slot_name_objective γ i γs : Objective (slot_name γ i γs) := _.

#[global] Instance slot_enqueued_persistent γ i v M Ve e :
  Persistent (slot_enqueued γ i v M Ve e).
Proof.
  apply embed_persistent, own_core_persistent, pair_core_id; [|apply _].
  apply pair_core_id; [apply _|].
  by apply auth_frag_core_id, gmap_singleton_core_id, _.
Qed.
#[global] Instance slot_enqueued_timeless γ i v M Ve e :
  Timeless (slot_enqueued γ i v M Ve e) := _.
#[global] Instance slot_enqueued_objective γ i v M Ve e :
  Objective (slot_enqueued γ i v M Ve e) := _.

#[global] Instance slot_dequeued_persistent γ i v M Ve e Vd :
  Persistent (slot_dequeued γ i v M Ve e Vd).
Proof.
  apply embed_persistent, own_core_persistent, pair_core_id; [|apply _].
  apply pair_core_id; [apply _|].
  by apply auth_frag_core_id, gmap_singleton_core_id, _.
Qed.
#[global] Instance slot_dequeued_timeless γ i v M Ve e Vd :
  Timeless (slot_dequeued γ i v M Ve e Vd) := _.
#[global] Instance slot_dequeued_objective γ i v M Ve e Vd :
  Objective (slot_dequeued γ i v M Ve e Vd) := _.

#[global] Instance slot_pre_enqueued_persistent γ i M :
  Persistent (slot_pre_enqueued γ i M) := _.
#[global] Instance slot_pre_enqueued_timeless γ i M :
  Timeless (slot_pre_enqueued γ i M) := _.
#[global] Instance slot_pre_enqueued_objective γ i M :
  Objective (slot_pre_enqueued γ i M) := _.
End ghost.

#[global] Typeclasses Opaque slot_name slot_enqueued slot_dequeued slot_pre_enqueued.


(**** THE INVARIANT AND LOCAL ASSERTIONS -------------------------------------*)
Section Interp.
Context `{!noprolG Σ, !hwqG Σ, !atomicG Σ}.
Local Existing Instances hwq_graphG hwq_queueG.

#[local] Notation iProp := (iProp Σ).
#[local] Notation vProp := (vProp Σ).

(*** LOCAL OBSERVATIONS ----------------------------------------*)

(**** RESOURCES OF SLOTS -----------------------------------------------------*)

(* Asserts the observation of the enqueue event `eid` for value `v`. *)

Definition SeenEnqueueds γ (bf : loc) (n : nat) (E : event_list) T (M : logView) : vProp :=
  ⌜ set_in_bound M E ∧ enq_map_enqueued T E ⌝ ∧
  ∀ e v V lV, ⌜ e ∈ M ∧ E !! e = Some (mkGraphEvent (Enq v) V lV) ⌝ →
  ⊒V.(dv_comm) ∧ @{V.(dv_comm)} SeenLogview E lV ∗
  ∃ (i : nat) γi Mi Vi,
    ⌜ (i ≤ n)%nat ∧ T !! e = Some i ∧ lV = {[e]} ∪ Mi ∧ e ∉ Mi ⌝ ∗
    slot_enqueued γ i v Mi Vi e ∗
    slot_name γ i γi ∗
    ∃ ζi ti, ⌜ ζi !! ti = Some (#v, V.(dv_wrt)) ⌝ ∧
            @{V.(dv_comm)} (bf >> i) sn⊒{γi} ζi.

Definition seen_enqueued (E : event_list) e v V : Prop :=
  ∃ eV : graph_event, E !! e = Some eV ∧
    eV.(ge_event) = Enq v ∧ eV.(ge_view).(dv_wrt) = V.

Definition own_slot γ E T (bf : loc) (i : nat) (γs : gname) (s : state) : vProp :=
  ∃ t0 LVs0 t1 LVs1,
    (bf >> i) at↦{γs} (toSlotHist s t0 LVs0 t1 LVs1)
    ∗ ⌜ (t0 +p length LVs0 ≤ t1)%positive ⌝
    ∗ match s with
      | SlotUnused => slot_reserve_tok γ i
      | SlotEnqueued (v,M,(Ve,e)) =>
          (* requires that the graph observed it *)
          @{Ve} (SeenEnqueueds γ bf i E T ({[e]} ∪ M)) ∧
          ⌜ seen_enqueued E e v Ve ⌝
      | SlotDequeued (v,M,(Ve,e)) Vd =>
          @{Ve} (SeenEnqueueds γ bf i E T ({[e]} ∪ M)) ∧
          ⌜ seen_enqueued E e v Ve ∧ Ve ⊑ Vd ∧ Forall (Vd ⊑.) LVs1 ⌝
          (* TODO: connect dequeue with graph for release info, only for
            strong HW queue *)
      | _ => True
      end.

Definition own_slots γ E T (bf : loc) slots : vProp :=
  [∗ map] i ↦ γss ∈ slots, let '(γs, s) := γss in own_slot γ E T bf i γs s.

(* The one who made the write to the back field releases its local observations
  of enqueues. This is needed for FIFO. *)
Definition seen_pre_enqueued γ bf (E : event_list) T i M : vProp :=
  ⌜ set_in_bound M E ⌝ ∧
  slot_pre_enqueued γ i M ∗
  SeenLogview E M ∗
  SeenEnqueueds γ bf i E T M.

(* In fact, when each slot i is acquired, the local observations of enqueues
  FOR ALL earlier slots are released. *)
Definition SeenPreEnqueued (sz : nat) γ bf (E : event_list) T (LVs : list view) : vProp :=
  [∗ list] i↦V ∈ LVs,
    (∀ i' : nat, ⌜i' < i `min` sz ⌝%nat → @{V} ∃ M, seen_pre_enqueued γ bf E T i' M).

Global Instance SeenPreEnqueued_objective sz γ bf E T LVs :
  Objective (SeenPreEnqueued sz γ bf E T LVs) := _.

Definition own_back sz γ (E : event_list) T (bk bf : loc) γb (n : nat) : vProp :=
  ∃ t0 LVs Vt,
    bk at↦{γb} (toBackHist n t0 (LVs ++ [Vt]))
    ∗ SeenPreEnqueued sz γ bf E T (LVs ++ [Vt])
    ∗ ⌜ length (LVs ++ [Vt]) = S n ∧ Forall (.⊑ Vt) LVs ⌝.

Definition QueueInv_no_exist
    (sz : nat) γ q γb n L T G : vProp :=
    let slots := map_seq 0 L in
    (* ghost state *)
    back_value γ γb n
    ∗ slots_master γ slots T
    (* pure facts constraining the shape of data *)
    ∗ ⌜ QueueProps sz n L T G ⌝
    (* physical data *)
    ∗ ∃ Vb,
      @{Vb} (own_back sz γ G.(Es) T (q >> back) (q >> buff) γb n ∗
             own_slots γ G.(Es) T (q >> buff) slots).

#[global] Instance own_slot_timeless γ E T bf i γs s :
  Timeless (own_slot γ E T bf i γs s).
Proof.
  do 4 apply bi.exist_timeless => ?.
  apply bi.sep_timeless; [apply _|].
  destruct s as [| |[[][]]|[[][]]]; apply _.
Qed.

#[global] Instance own_slots_timeless γ E T bf slots :
  Timeless (own_slots γ E T bf slots).
Proof. apply big_sepM_timeless => ?[??]; apply _. Qed.
#[global] Instance QueueInv_no_exist_timeless sz γ q γb n L T G :
  Timeless (QueueInv_no_exist sz γ q γb n L T G) := _.

Definition QueueBaseInv sz γq q G : vProp :=
  ∃ γb n L T, QueueInv_no_exist sz γq q γb n L T G.

(* Only share the ghost state with the client. *)
Definition QueueInv γg (q : loc) G : vProp :=
  ⌜ WeakQueueConsistent G ⌝ ∗ graph_master γg (1/2) G.

#[global] Instance QueueInv_objective γg q G : Objective (QueueInv γg q G) := _.

(* Our internal invariant keeps all the physical resources, as well as enough
  ghost resources (`QueueInv`) to maintain agreement with the client. *)
Definition QueueInternalInv sz γq γg q : vProp :=
  ∃ G, QueueInv γg q G ∗ QueueBaseInv sz γq q G.

#[global] Instance QueueInternalInv_objective sz γq γg q :
  Objective (QueueInternalInv sz γq γg q) := _.
#[global] Instance QueueInternalInv_timeless sz γq γg q :
  Timeless (QueueInternalInv sz γq γg q) := _.

(*** QueueLocal assertion, specific to this implementation------------------- *)

Definition QueueSeen (sz : nat) γq q G M : vProp :=
  ∃ γb n T,
    back_lb γq γb n
  ∗ enq_slots_snap γq T
  ∗ (∃ ζ, (q >> back) sn⊒{γb} ζ ∧ ⌜ ∃ tb Vb, ζ !! tb = Some (#n, Vb) ⌝)
  (* observation of all slots initialization *)
  ∗ (∃ L, ⌜ length L = sz ⌝ ∗
       [∗ list] i ↦ γ ∈ L, ∃ ζ, slot_name γq i γ
                              ∗ (q >> buff >> i) sn⊒{γ} ζ)
  ∗ SeenEnqueueds γq (q >> buff) (n `min` sz) G.(Es) T M
  .

#[global] Instance QueueSeen_persistent sz γq q G M :
  Persistent (QueueSeen sz γq q G M) := _.

Definition InternInv sz N q γq γg := inv (hwqN N q) (QueueInternalInv sz γq γg q).
Definition QueueLocal sz N γg q G M : vProp :=
  graph_snap γg G M
  ∗ ∃ γq, QueueSeen sz γq q G M
  ∗ InternInv sz N q γq γg.

#[global] Instance QueueLocal_persistent sz N γg q G M :
  Persistent (QueueLocal sz N γg q G M) := _.
End Interp.

Section properties.
Context `{!noprolG Σ, !hwqG Σ, !atomicG Σ}.
Local Existing Instances hwq_graphG hwq_queueG.

#[local] Notation vProp := (vProp Σ).

(** GHOST STATE --------------------------------------------------------------*)
Lemma ghost_alloc γb n γs :
  ⊢ |==> ∃ γ, let slots := map_seq 0%nat ((λ γ, (γ, SlotUnused)) <$> γs) in
              back_value γ γb n
            ∗ slots_master γ slots ∅
            ∗ ([∗ map] i ↦ γss ∈ slots, slot_reserve_tok γ i ∗ slot_name γ i γss.1).
Proof.
  rewrite /slots_master /slot_reserve_tok /slot_name.
  set slots := map_seq 0%nat ((λ γ, (γ, SlotUnused)) <$> γs).
  setoid_rewrite <-embed_sep. setoid_rewrite <-own_op.
  setoid_rewrite <-embed_big_sepM. do 2 setoid_rewrite <-embed_sep.
  setoid_rewrite <-embed_exist.
  setoid_rewrite <-big_opM_own_1. do 2 setoid_rewrite <-own_op.
  iMod (own_alloc (A:=hwqR)) as "$"; [|done].
  rewrite (_ :
    ([^ op map] i ↦ x ∈ slots,
          (ε, ε, ◯ {[i := (to_slot_state SlotUnused, ε)]}, ε)
        ⋅ (ε, ε, ◯ {[i := (ε, to_slot_name x.1)]}, ε) : hwqR)
    ≡ (ε, ε, ◯ [^ op map] i ↦ x ∈ slots,
                  {[i := (to_slot_state SlotUnused, to_slot_name x.1)]}, ε));
    last first.
  { rewrite /slots. move : ((λ γ, (γ, SlotUnused)) <$> γs) 0%nat => l. clear.
    induction l as [|[γ s] l IH] => n; first by rewrite /= !big_opM_empty.
    assert ((map_seq (S n) l : gmap _ _) !! n = None).
    { apply lookup_map_seq_None. by left; lia. }
    rewrite map_seq_cons big_opM_insert; [|done].
    rewrite IH -!pair_op /=. f_equiv; [|by rewrite !left_id].
    rewrite -!auth_frag_op /=. f_equiv. rewrite big_opM_insert; [|done]. f_equiv.
    rewrite singleton_op. f_equiv. }
  split; last first. { rewrite /= !left_id right_id. by apply auth_auth_valid. }
  split.
  { rewrite /= -!pair_op !left_id !right_id /=. split; [done|].
    apply mono_nat_auth_valid. }
  rewrite /= !left_id. apply auth_both_valid_discrete. clear. subst slots.
  move : 0%nat.
  induction γs as [|γ γs IH] => n.
  - by rewrite fmap_nil fmap_empty /= big_opM_empty.
  - assert (EQN: (map_seq (S n) ((λ γ0, (γ0, SlotUnused)) <$> γs) : gmap _ _) !! n = None).
    { apply lookup_map_seq_None. by left; lia. }
     rewrite fmap_cons map_seq_cons fmap_insert big_opM_insert; [|done].
    rewrite insert_singleton_op; last by rewrite lookup_fmap EQN.
    specialize (IH (S n)) as [IH1 IH2]. simpl.
    split.
    + by apply cmra_mono_l.
    + rewrite -insert_singleton_op; last by rewrite lookup_fmap EQN.
      by apply insert_valid.
Qed.

Lemma back_value_update γ γb n n' :
  (n ≤ n')%nat →
  back_value γ γb n ⊢ |==> back_value γ γb n'.
Proof.
  intros Le. iIntros "bv". iMod (own_update with "bv") as "$"; [|done].
  do 2 (apply prod_update; [|done]). apply prod_update; [done|].
  by apply mono_nat_update.
Qed.

Lemma back_value_back_lb_get γ γb n :
  back_value γ γb n ⊢ back_lb γ γb n.
Proof.
  iIntros "bv". iApply (own_mono with "bv").
  do 2 (apply prod_included; split; [|done]).
  apply prod_included; split; [done|]. apply mono_nat_included.
Qed.

Lemma back_lb_get_lb γ γb n n' :
  (n' ≤ n)%nat →
  back_lb γ γb n ⊢ back_lb γ γb n'.
Proof.
  iIntros (Len') "O". iApply (own_mono with "O").
  do 2 (apply pair_included; split; [|done]).
  apply pair_included; split; [done|]. by apply mono_nat_lb_mono.
Qed.

Lemma back_value_back_lb_valid γ γb γb' n n' :
  back_value γ γb n -∗ back_lb γ γb' n' -∗ ⌜ γb = γb' ∧ (n' ≤ n)%nat ⌝.
Proof.
  iIntros "bv bl". iCombine "bv bl" as "bvl".
  iDestruct (own_valid with "bvl") as %[[[VAL1 VAL2%mono_nat_both_valid] _] _].
  iPureIntro. split; [|done].
  move : VAL1. by rewrite /= Some_valid => /to_agree_op_inv_L.
Qed.

Lemma slots_masters_enq_slots_snap_agree γ slots T T' :
  slots_master γ slots T -∗ enq_slots_snap γ T' -∗ ⌜ T' ⊆ T ⌝.
Proof.
  iIntros "SM ES". iCombine "SM ES" as "SM".
  iDestruct (own_valid with "SM")
    as %(_ & [?%(to_agreeM_included T T') ?]%auth_both_valid_discrete).
  by iPureIntro.
Qed.

Lemma slots_masters_enq_slots_snap_fork γ slots T :
  slots_master γ slots T ==∗ slots_master γ slots T ∗ enq_slots_snap γ T.
Proof.
  iIntros "SM". rewrite -embed_sep -own_op -embed_bupd.
  iApply (own_update with "SM").
  apply prod_update; simpl; first by rewrite right_id.
  by apply auth_update_alloc, to_agreeM_local_update.
Qed.

Lemma enq_slots_snap_sub γ slots T T' :
  T' ⊆ T → enq_slots_snap γ T ⊢ enq_slots_snap γ T'.
Proof.
  iIntros (Sub) "SM". iApply (own_mono with "SM").
  apply pair_included; split; [done|].
  by apply auth_frag_mono, to_agreeM_included.
Qed.

Lemma slot_pending_tok_slot_pre_enqueued γ i v M :
  slot_pending_tok γ i v M ⊢ slot_pre_enqueued γ i M.
Proof.
  iIntros "SP". iExists v. iApply (own_mono with "SP").
  apply prod_included; split; [|done].
  apply prod_included; split; [done|].
  apply auth_frag_mono, (singleton_mono (A:=per_slotUR)).
  do 2 (apply prod_included; split; [|done]).
  apply prod_included. split; [done|by apply ucmra_unit_least].
Qed.

Lemma slots_master_slot_name_agree γ slots T i γi :
  slots_master γ slots T -∗ slot_name γ i γi -∗
  ⌜ fst <$> slots !! i = Some γi ⌝.
Proof.
  iIntros "OM Tok". rewrite /slot_name. iCombine "OM Tok" as "OM".
  iDestruct (own_valid with "OM") as %[[_ [INCL VAL]%auth_both_valid_discrete] _].
  iPureIntro.
  apply (singleton_included_l) in INCL
    as [[y1 y4] [Eqy (_ & _ & _ & IN4)%Some_prod3UR_included]].
  move : (VAL i). rewrite {1}Eqy Some_valid => [[_ /= VAL4]].
  apply Some_agree_included' in IN4; [|done]. simpl in IN4.
  move : Eqy. rewrite lookup_fmap fmap_Some_equiv.
  move => [[γs s] [-> [/= _]]]. rewrite IN4.
  intros Eqy%Some_equiv_inj%to_agree_inj. by inversion Eqy.
Qed.

Lemma slots_master_slot_name_agree_L γ L T i γi :
  let slots : gmap _ _ := map_seq 0 L in
  slots_master γ slots T -∗ slot_name γ i γi -∗
  ⌜ fst <$> L !! i = Some γi ⌝.
Proof.
  iIntros (slots) "SLM Gγ".
  iDestruct (slots_master_slot_name_agree with "SLM Gγ")
      as %[[γ'' s'] [Eqγ1 Eqγ2]]%fmap_Some.
  iPureIntro. simpl in Eqγ2. subst γ''. by rewrite -lookup_map_seq_0 Eqγ1.
Qed.

Lemma slots_master_get_pending {γq slots T i γ} v M :
  slots !! i = Some (γ, SlotUnused) →
  slots_master γq slots T -∗ slot_reserve_tok γq i ==∗
  slots_master γq (<[i:=(γ, SlotPending v M)]>slots) T ∗ slot_pending_tok γq i v M.
Proof.
  iIntros (Eqi) "OM Tok". iCombine "OM Tok" as "Tok".
  rewrite -embed_sep -own_op -embed_bupd.
  iApply (own_update with "Tok").
  apply prod_update; simpl; [|done]. apply prod_update; [done|]. simpl.
  apply auth_update. rewrite fmap_insert /=. apply : singleton_local_update.
  - rewrite lookup_fmap Eqi /=; eauto.
  - apply prod_local_update_1.
    apply (prod_local_update_1 ((_ : oagreeUR _), _)).
    apply (prod_local_update_1 (_ : oagreeUR _)).
    by apply (alloc_option_local_update _ (_ : oagreeUR _)).
Qed.

Lemma slots_master_get_pending_L {γq L T i γ} v M :
  L !! i = Some (γ, SlotUnused) →
  let slots := map_seq 0 L in
  slots_master γq slots T -∗ slot_reserve_tok γq i ==∗
  let slots' := map_seq 0 (<[i:=(γ, SlotPending v M)]>L) in
  slots_master γq slots' T ∗ slot_pending_tok γq i v M.
Proof.
  intros Eqi. rewrite map_seq_insert; last by (move : Eqi; apply lookup_lt_Some).
  rewrite Nat.add_0_l. apply slots_master_get_pending. by rewrite lookup_map_seq_0.
Qed.

Lemma slots_master_slot_pending_agree {γ slots T i v M} :
  slots_master γ slots T -∗ slot_pending_tok γ i v M -∗
  ⌜ snd <$> slots !! i = Some (SlotPending v M) ⌝.
Proof.
  iIntros "OM Tok". iCombine "OM Tok" as "OM".
  iDestruct (own_valid with "OM") as %[[_ [INCL VAL]%auth_both_valid_discrete] _].
  iPureIntro.
  apply (singleton_included_l) in INCL
    as [[[[y1 y2] y3] y4] [Eqy (IN1 & IN2 & _)%Some_prod3UR_included]].
  simpl in *.
  move : (VAL i). rewrite {1}Eqy Some_valid => [[[[/= VAL1 VAL2] _] _]].
  apply Some_agree_included' in IN1; [|done].
  apply Some_not_shot_included in IN2; [|done]. subst y2.

  move : Eqy. rewrite IN1 lookup_fmap fmap_Some_equiv.
  move => [[γs s] [-> [/= Eqs _]]]. f_equal. clear -Eqs.
  destruct s as [| |[[][]]|[[][]]]; simpl in Eqs.
  - exfalso. destruct Eqs as [[Eqs _] _]. by inversion Eqs.
  - destruct Eqs as [[Eqs%Some_equiv_inj _] _].
    move : Eqs => /to_agree_inj. by inversion 1.
  - exfalso. destruct Eqs as [[_ Eqs%Some_equiv_inj] _]. by inversion Eqs.
  - exfalso. destruct Eqs as [[_ Eqs%Some_equiv_inj] _]. by inversion Eqs.
Qed.

(* We can prove a more general lemma, but that's too burdensome for me right now. *)
Lemma slots_master_slot_pre_enqueued_agree {γ slots T i γi v M V e} M' :
  slots !! i = Some (γi, SlotEnqueued (v, M, (V, e))) →
  slots_master γ slots T -∗ slot_pre_enqueued γ i M' -∗
  ⌜ M = M' ⌝.
Proof.
  rewrite /slot_pre_enqueued.
  iIntros (Eqi) "SL [%vx SP]". iCombine "SL SP" as "OM".
  iDestruct (own_valid with "OM") as %[[_ [INCL VAL]%auth_both_valid_discrete] _].
  iPureIntro.
  move : INCL => /singleton_included_l.
  move => [y [Eqy /Some_prod3UR_included /= [EqvM _]]].
  move : (VAL i). rewrite {1}Eqy Some_valid => [[[[/= VAL1 _] _] _]].
  apply Some_agree_included' in EqvM; [|done].

  move : Eqy. rewrite lookup_fmap fmap_Some_equiv Eqi /=.
  intros (γs & Eqs & Eqy). inversion Eqs; clear Eqs; subst γs.
  simpl in *.
  move : EqvM. rewrite Eqy /=. intros Eq%Some_equiv_inj.
  move : Eq => /to_agree_inj. by inversion 1.
Qed.

Lemma to_enq_slots_fork T e i :
  T !! e = Some i →
  to_enq_slots T ~~> to_enq_slots T ⋅ ◯ {[e := to_agree i]}.
Proof.
  intros Eqe. apply auth_update_alloc.
  etrans; first by apply to_agreeM_local_update_fork_singleton.
  by rewrite {2}/to_agreeM fmap_insert fmap_empty.
Qed.

Lemma to_enq_slots_insert T e i :
  T !! e = None →
  to_enq_slots T ~~> to_enq_slots (<[e:= i]>T) ⋅ ◯ {[e := to_agree i]}.
Proof.
  intros. apply auth_update_alloc.
  etrans; first by apply to_agreeM_local_update_insert_singleton.
  by rewrite {2}/to_agreeM fmap_insert fmap_empty.
Qed.

Lemma slots_master_set_enqueued {γq slots T i γ v M} e V :
  slots !! i = Some (γ, SlotPending v M) →
  T !! e = None →
  slots_master γq slots T -∗
  slot_pending_tok γq i v M ==∗
  slots_master γq (<[i := (γ, SlotEnqueued (v,M,(V,e)))]>slots) (<[e := i]>T) ∗
  slot_enqueued γq i v M V e.
Proof.
  iIntros (Eqi FRe) "OM Tok". iCombine "OM Tok" as "OM".
  rewrite -embed_sep -own_op -embed_bupd.
  iApply (own_update with "OM"). rewrite right_id.
  apply prod_update; simpl; last by apply to_enq_slots_insert.
  apply prod_update; [done|]. apply auth_update.
  rewrite fmap_insert /=. apply : singleton_local_update.
  - rewrite lookup_fmap Eqi /=; eauto.
  - apply prod_local_update_1,
          (prod_local_update_1 ((_ : oagreeUR _), _)),
          (prod_local_update_2 (_ : oagreeUR _)).
    apply : option_local_update. by apply exclusive_local_update.
Qed.

Lemma slots_master_set_enqueued_L {γq L T i γ v M} e V :
  L !! i = Some (γ, SlotPending v M) →
  T !! e = None →
  let slots := map_seq 0 L in
  slots_master γq slots T -∗
  slot_pending_tok γq i v M ==∗
  let slots' := map_seq 0 (<[i:=(γ, SlotEnqueued (v,M,(V,e)))]>L) in
  slots_master γq slots' (<[e := i]>T) ∗ slot_enqueued γq i v M V e.
Proof.
  intros Eqi EqN. rewrite map_seq_insert; last by (move : Eqi; apply lookup_lt_Some).
  rewrite Nat.add_0_l. apply slots_master_set_enqueued; [|done].
  by rewrite lookup_map_seq_0.
Qed.

Lemma slots_master_slot_enqueued_get_enq {γq slots T i γ v M V e} :
  slots !! i = Some (γ, SlotEnqueued (v,M,(V,e))) →
  T !! e = Some i →
  slots_master γq slots T ==∗
  slots_master γq slots T ∗ slot_enqueued γq i v M V e.
Proof.
  iIntros (Eqi Eqe) "SLM". rewrite -embed_sep -own_op -embed_bupd.
  iApply (own_update with "SLM").
  apply prod_update; simpl; last by apply to_enq_slots_fork.
  apply prod_update; [done|]. apply auth_update_alloc.
  rewrite -{2}(insert_id  _ _ _ Eqi) fmap_insert /= -insert_empty.
  apply : (insert_alloc_local_update (A:=per_slotUR)).
  - rewrite lookup_fmap Eqi /=. eauto.
  - apply : lookup_empty.
  - apply prod_local_update_1. apply prod_local_update; simpl.
    + etrans; first apply core_id_local_update; last (rewrite left_id; by eauto);
        [apply _|done].
    + done.
Qed.

Lemma slots_master_slot_enqueued_get_enq_L {γq L T i γ v M V e} :
  let slots := map_seq 0 L in
  L !! i = Some (γ, SlotEnqueued (v,M,(V,e))) →
  T !! e = Some i →
  slots_master γq slots T ==∗
  slots_master γq slots T ∗ slot_enqueued γq i v M V e.
Proof.
  intros slots Eqi. eapply slots_master_slot_enqueued_get_enq. by rewrite lookup_map_seq_0.
Qed.

Lemma slots_master_slot_enqueued_agree {γ slots T i v M V e} :
  slots_master γ slots T -∗ slot_enqueued γ i v M V e -∗
  ⌜ T !! e = Some i ∧
    (snd <$> slots !! i = Some (SlotEnqueued (v,M,(V,e)))
    ∨ ∃ Vd,  snd <$> slots !! i = Some (SlotDequeued (v,M,(V,e)) Vd)) ⌝.
Proof.
  iIntros "OM Tok". rewrite /slot_enqueued. iCombine "OM Tok" as "OM".
  iDestruct (own_valid with "OM")
    as %[[_ [INCL VAL]%(auth_both_valid_discrete (A:= gmapUR _ per_slotUR))]
            [INT _]%(auth_both_valid_discrete (A:=gmapUR _ (agreeR $ leibnizO _)))].
  iPureIntro.
  apply to_agreeM_singleton_included, map_singleton_subseteq_l in INT.
  split; [done|].

  apply (singleton_included_l) in INCL
    as [[[[y1 y2] y3] y4] [Eqy (IN1 & IN2 & _)%Some_prod3UR_included]].
  simpl in *.
  move : (VAL i). rewrite {1}Eqy Some_valid => [[[[/= VAL1 VAL2] _] _]].
  apply Some_agree_included' in IN1; [|done].
  apply Some_shot_included in IN2; [|done].
  move : Eqy. rewrite IN1 IN2 lookup_fmap fmap_Some_equiv.
  move => [[γs s] [-> [/= Eqs _]]]. f_equal. clear -Eqs.
  destruct s as [| |[[][]]|[[][]]]; simpl in Eqs.
  - exfalso. destruct Eqs as [[Eqs _] _]. by inversion Eqs.
  - exfalso. destruct Eqs as [[_ Eqs%Some_equiv_inj] _]. by inversion Eqs.
  - destruct Eqs as [[Eqv%Some_equiv_inj Eqs%Some_equiv_inj] _].
    left. move : Eqv Eqs => /to_agree_inj ? /Cinr_inj /to_agree_inj ?.
    by simplify_eq.
  - destruct Eqs as [[Eqv%Some_equiv_inj Eqs%Some_equiv_inj] _].
    right. move : Eqv Eqs => /to_agree_inj ? /Cinr_inj /to_agree_inj ?.
    simplify_eq. by eexists.
Qed.

Lemma slots_master_slot_enqueued_agree_L γ L T i v M V e :
  let slots := map_seq 0 L in
  slots_master γ slots T -∗ slot_enqueued γ i v M V e -∗
  ⌜ T !! e = Some i ∧
    (snd <$> L !! i = Some (SlotEnqueued (v,M,(V,e)))
    ∨ ∃ Vd,  snd <$> L !! i = Some (SlotDequeued (v,M,(V,e)) Vd)) ⌝.
Proof.
  iIntros (slots) "SM SE".
  iDestruct (slots_master_slot_enqueued_agree with "SM SE") as %[? CASE].
  iPureIntro. split; [done|].
  destruct CASE as [(? & Eq1 & Eq2)%fmap_Some|
                    [Vd (? & Eq1 & Eq2)%fmap_Some]];
    [left|right; exists Vd]; by rewrite -lookup_map_seq_0 Eq1 Eq2.
Qed.

Lemma slots_master_slot_enqueued_agree_L_get_enqInfo γ L T i v M V e :
  let slots := map_seq 0 L in
  slots_master γ slots T -∗ slot_enqueued γ i v M V e -∗
  ⌜ T !! e = Some i ∧ get_enqInfo_L L i = Some (v,M,(V,e)) ⌝.
Proof.
  iIntros (slots) "SM SE".
  iDestruct (slots_master_slot_enqueued_agree_L with "SM SE")
    as %(? & CASE). iPureIntro; split; [done|].
  destruct CASE as [CASE|[Vd CASE]]; revert CASE.
  - apply get_enqInfo_L_enqueued.
  - apply get_enqInfo_L_dequeued.
Qed.

Lemma slots_master_slot_dequeued_agree γ slots T i v M V e Vd :
  slots_master γ slots T -∗ slot_dequeued γ i v M V e Vd -∗
  ⌜ T !! e = Some i ∧ snd <$> slots !! i = Some (SlotDequeued (v,M,(V,e)) Vd) ⌝.
Proof.
  iIntros "OM Tok". rewrite /slot_dequeued. iCombine "OM Tok" as "OM".
  iDestruct (own_valid with "OM")
    as %[[_ [INCL VAL]%auth_both_valid_discrete] [INT _]%auth_both_valid_discrete].
  iPureIntro.
  apply to_agreeM_singleton_included, map_singleton_subseteq_l in INT.
  split; [done|].
  apply (singleton_included_l) in INCL
    as [[[[y1 y2] y3] y4] [Eqy (IN1 & IN2 & IN3 & _)%Some_prod3UR_included]].
  simpl in *.
  move : (VAL i). rewrite {1}Eqy Some_valid => [[[[/= VAL1 VAL2] VAL3] _]].
  apply Some_agree_included' in IN1; [|done].
  apply Some_shot_included in IN2; [|done].
  apply Some_agree_included' in IN3; [|done].
  move : Eqy. rewrite IN1 IN2 IN3 lookup_fmap fmap_Some_equiv.
  move => [[γs s] [-> [/= Eqs _]]]. f_equal. clear -Eqs.
  destruct s as [| |[[][]]|[[][]]]; simpl in Eqs.
  - exfalso. destruct Eqs as [_ EqVd]. by inversion EqVd.
  - exfalso. destruct Eqs as [_ EqVd]. by inversion EqVd.
  - exfalso. destruct Eqs as [_ EqVd]. by inversion EqVd.
  - destruct Eqs as [[Eqv%Some_equiv_inj Eqs%Some_equiv_inj]
                      EqVd%Some_equiv_inj].
    move : Eqv Eqs EqVd => /to_agree_inj ? /Cinr_inj /to_agree_inj ? /to_agree_inj ?.
    by simplify_eq.
Qed.

Lemma slots_master_set_dequeued {γq slots T i γ v M Ve e} Vd :
  slots !! i = Some (γ, SlotEnqueued (v,M,(Ve,e))) →
  T !! e = Some i →
  slots_master γq slots T ==∗
  slots_master γq (<[i := (γ, SlotDequeued (v,M,(Ve,e)) Vd)]>slots) T ∗
  slot_dequeued γq i v M Ve e Vd.
Proof.
  iIntros (Eqi Eqe) "OM". rewrite -embed_sep -own_op -embed_bupd.
  iApply (own_update with "OM").
  apply prod_update; simpl; last by apply to_enq_slots_fork.
  apply prod_update; [done|]. apply auth_update_alloc.
  rewrite fmap_insert /= -insert_empty. apply : (insert_alloc_local_update (A:=per_slotUR)).
  - rewrite lookup_fmap Eqi /=. eauto.
  - apply : lookup_empty.
  - apply prod_local_update_1. apply prod_local_update; simpl.
    + etrans; first apply core_id_local_update; last (rewrite left_id; by eauto);
        [apply _|done].
    + by apply : alloc_option_local_update.
Qed.

Lemma slots_master_set_dequeued_L {γq L T i γ v M Ve e} Vd :
  L !! i = Some (γ, SlotEnqueued (v,M,(Ve,e))) →
  T !! e = Some i →
  let slots : gmap _ _ := map_seq 0 L in
  slots_master γq slots T ==∗
  let slots' := map_seq 0 (<[i:=(γ, SlotDequeued (v,M,(Ve,e)) Vd)]>L) in
  slots_master γq slots' T ∗
  slot_dequeued γq i v M Ve e Vd.
Proof.
  intros Eqi Eqe. rewrite map_seq_insert; last by (move : Eqi; apply lookup_lt_Some).
  rewrite Nat.add_0_l. apply slots_master_set_dequeued; [|done].
  by rewrite lookup_map_seq_0.
Qed.

Lemma slots_master_slot_dequeued_get_deq {γq slots T i γ v M V e Vd} :
  slots !! i = Some (γ, SlotDequeued (v,M,(V,e)) Vd) →
  T !! e = Some i →
  slots_master γq slots T ==∗
  slots_master γq slots T ∗
  slot_dequeued γq i v M V e Vd.
Proof.
  iIntros (Eqi Eqe) "SLM".
  rewrite -embed_sep -own_op -embed_bupd.
  iApply (own_update with "SLM").
  apply prod_update; simpl; last by apply to_enq_slots_fork.
  apply prod_update; [done|]. apply auth_update_alloc.
  rewrite -{2}(insert_id  _ _ _ Eqi) fmap_insert /= -insert_empty.
  apply : (insert_alloc_local_update (A:=per_slotUR)).
  - rewrite lookup_fmap Eqi /=. eauto.
  - apply : lookup_empty.
  - apply prod_local_update_1. apply prod_local_update; simpl.
    + etrans; first apply core_id_local_update; last (rewrite left_id; by eauto);
        [apply _|done].
    + etrans; first apply core_id_local_update; last (rewrite left_id; by eauto);
        [apply _|done].
Qed.

Lemma slots_master_slot_dequeued_get_deq_L {γq L T i γ v M V e Vd} :
  let slots := map_seq 0 L in
  L !! i = Some (γ, SlotDequeued (v,M,(V,e)) Vd) →
  T !! e = Some i →
  slots_master γq slots T ==∗
  slots_master γq slots T ∗ slot_dequeued γq i v M V e Vd.
Proof.
  intros slots Eqi. eapply slots_master_slot_dequeued_get_deq. by rewrite lookup_map_seq_0.
Qed.

Lemma slot_dequeued_slot_enqueued {γq i v M V e Vd} :
  slot_dequeued γq i v M V e Vd ⊢ slot_enqueued γq i v M V e.
Proof.
  iIntros "SD". rewrite /slot_dequeued /slot_enqueued.
  iApply (own_mono with "SD").
  apply pair_included; split; [|done]. apply pair_included; split; [done|].
  apply auth_frag_mono, singleton_included. right. simpl.
  apply pair_included; split; [|done]. apply pair_included; split; [done|].
  apply option_included. by left.
Qed.

Lemma slots_master_slot_dequeued_get_enq {γq slots T i γ v M V e Vd} :
  slots !! i = Some (γ, SlotDequeued (v,M,(V,e)) Vd) →
  T !! e = Some i →
  slots_master γq slots T ==∗
  slots_master γq slots T ∗ slot_enqueued γq i v M V e.
Proof.
  iIntros (Eqi Eqe) "SLM".
  iMod (slots_master_slot_dequeued_get_deq Eqi with "SLM") as "[$ SD]"; [done|].
  iIntros "!>". iApply (slot_dequeued_slot_enqueued with "SD").
Qed.

Lemma slots_master_slot_dequeued_get_enq_L {γq L T i γ v M V e Vd} :
  L !! i = Some (γ, SlotDequeued (v,M,(V,e)) Vd) →
  T !! e = Some i →
  let slots : gmap _ _ := map_seq 0 L in
  slots_master γq slots T ==∗
  slots_master γq slots T ∗ slot_enqueued γq i v M V e.
Proof.
  intros Eqi Eqe slots. eapply slots_master_slot_dequeued_get_enq; [|done].
  by rewrite lookup_map_seq_0.
Qed.

Lemma QueueBaseInv_unfold_snap sz γq q G γb n :
  QueueBaseInv sz γq q G -∗
  back_lb γq γb n -∗
  ∃ n' L T, QueueInv_no_exist sz γq q γb n' L T G ∗
    ⌜ (n ≤ n')%nat ⌝.
Proof.
  iDestruct 1 as (γb' n' L T) "[bv QI]". iIntros "bl".
  iDestruct (back_value_back_lb_valid with "bv bl") as %[-> ?].
  iExists n', L, T. by iFrame.
Qed.

Lemma SeenEnqueueds_mono {γ bf n E T M} n' E' T' M' :
  (n ≤ n')%nat → E ⊑ E' → T ⊆ T' → M' ⊆ M →
  enq_map_enqueued T' E' →
  SeenEnqueueds γ bf n E T M ⊢ SeenEnqueueds γ bf n' E' T' M'.
Proof.
  iIntros (Len LeE LeT LeM' EqTE') "[(%SubM & %) SE]". iSplit.
  { iPureIntro. split; [|done]. by eapply set_in_bound_mono'. }
  iIntros (e v V lV [InM' Eqe]).
  iDestruct ("SE" $! e v V lV with "[%]") as "($ & SL & SE)".
  { split; [by apply LeM'|]. apply (prefix_lookup_inv _ _ _ _ Eqe); [|done].
    by apply SubM, LeM', InM'. }
  erewrite SeenLogview_map_mono; [iFrame "SL"|eauto..].
  iDestruct "SE" as (i γi Mi Vi (Hi1 & Hi2 & Hi3)) "SE".
  iExists i, γi, Mi, Vi. iFrame "SE". iPureIntro. split; [lia|].
  split; [|done]. move : Hi2 LeT. apply lookup_weaken.
Qed.

Lemma SeenEnqueueds_union {γ bf n E T} M1 M2 :
  SeenEnqueueds γ bf n E T M1 -∗ SeenEnqueueds γ bf n E T M2 -∗
  SeenEnqueueds γ bf n E T (M1 ∪ M2).
Proof.
  iIntros "[%Sub1 SE1] [%Sub2 SE2]".
  destruct Sub1 as [Sub1 EN]. destruct Sub2 as [Sub2 _].
  iSplit. { iPureIntro. split; [|done]. by apply set_in_bound_union. }
  iIntros (e v V lV [[InM1|InM2]%elem_of_union Eqe]).
  - by iApply "SE1".
  - by iApply "SE2".
Qed.

Definition SeenEnqueueds_union' {γ bf n E T} M1 M2 :=
  bi.wand_elim_l' _ _ _ (@SeenEnqueueds_union γ bf n E T M1 M2).

Lemma SeenEnqueueds_singleton {γ bf n E T e v V lV} i γi Mi Vi :
  E !! e = Some (mkGraphEvent (Enq v) V lV) →
  T !! e = Some i →
  enq_map_enqueued T E →
  (i ≤ n)%nat → lV = {[e]} ∪ Mi → e ∉ Mi →
  ⊒V.(dv_comm) ∧
  @{V.(dv_comm)} SeenLogview E lV ∗
  slot_enqueued γ i v Mi Vi e ∗
  slot_name γ i γi ∗
  (∃ ζi ti, ⌜ ζi !! ti = Some (#v, V.(dv_wrt)) ⌝ ∧
            @{V.(dv_comm)} (bf >> i) sn⊒{γi} ζi) ⊢
  SeenEnqueueds γ bf n E T {[e]}.
Proof.
  intros Eqe Eqi EqET Lei EqlV NIe. iIntros "(sV & SL & GE & Gn & sζ)". iSplit.
  { iPureIntro. split; [|done]. intros ? ->%elem_of_singleton. by eexists. }
  iIntros (e' v' V' lV' [->%elem_of_singleton Eqe']).
  rewrite Eqe in Eqe'. inversion Eqe'; clear Eqe'; subst.
  iFrame "sV SL". iExists i, γi, Mi, Vi. by iFrame.
Qed.

Lemma SeenEnqueueds_empty γ bf n E T :
  enq_map_enqueued T E → ⊢ SeenEnqueueds γ bf n E T ∅.
Proof.  intros. iSplit; [done|]. by iIntros (????[]). Qed.

Lemma seen_pre_enqueued_mono {γ bf i M E E' T T'} :
  E ⊑ E' → T ⊆ T' →
  enq_map_enqueued T' E' →
  seen_pre_enqueued γ bf E T i M ⊢ seen_pre_enqueued γ bf E' T' i M.
Proof.
  iIntros (SubE SubT ?) "[%SubM SE]".
  iSplit. { iPureIntro. by eapply set_in_bound_mono. }
  rewrite /seen_pre_enqueued. erewrite SeenLogview_map_mono; [|done..].
  by rewrite SeenEnqueueds_mono.
Qed.

Lemma SeenPreEnqueued_mono {sz γ bf LVs E E' T T'} :
  E ⊑ E' → T ⊆ T' →
  enq_map_enqueued T' E' →
  SeenPreEnqueued sz γ bf E T LVs ⊢ SeenPreEnqueued sz γ bf E' T' LVs.
Proof.
  intros SubE SubT ?. apply big_sepL_mono => i V Eqi.
  iIntros "SE" (i' Le'). iDestruct ("SE" $! i' Le') as (M) "SE".
  iExists M. by rewrite seen_pre_enqueued_mono.
Qed.

Lemma seen_enqueued_mono {e v V E E'} :
  E ⊑ E' → seen_enqueued E e v V → seen_enqueued E' e v V.
Proof.
  intros SubE (eV & ? & ? & ?). exists eV. split; [|done]. by eapply prefix_lookup_Some.
Qed.

Lemma own_back_mono {sz γ bk bf γb n E E' T T'} :
  E ⊑ E' → T ⊆ T' →
  enq_map_enqueued T' E' →
  own_back sz γ E T bk bf γb n ⊢ own_back sz γ E' T' bk bf γb n.
Proof.
  intros SubE SubT ?. iDestruct 1 as (t0 LVs Vt) "(AT & SE & F)".
  iExists t0, LVs, Vt. iFrame. by iApply (SeenPreEnqueued_mono with "SE").
Qed.

Lemma own_slot_mono {γq q i γ s E E' T T'} :
  E ⊑ E' → T ⊆ T' →
  enq_map_enqueued T' E' →
  own_slot γq E T q i γ s ⊢ own_slot γq E' T' q i γ s.
Proof.
  intros SubE SubT ?. iDestruct 1 as (t0 LVs0 t1 LVs1) "[AT oS]".
  iExists t0, LVs0, t1, LVs1. iFrame "AT".
  destruct s as [| |[[][]]|[[][]]]; [by iFrame|done|..];
    (rewrite SeenEnqueueds_mono; eauto).
  - iDestruct "oS" as "($ & $ & %)". iPureIntro; by eapply seen_enqueued_mono.
  - iDestruct "oS" as "($ & $ & [% %])". iPureIntro; split; [|done].
    by eapply seen_enqueued_mono.
Qed.

Lemma own_slots_access {γq E T q L i γ s} :
  L !! i = Some (γ, s) →
  own_slots γq E T q (map_seq 0 L) ⊢
  own_slot γq E T q i γ s
  ∗ (∀ s' E' T', ⌜ E ⊑ E' ∧ T ⊆ T' ∧ enq_map_enqueued T' E' ⌝ -∗
              own_slot γq E' T' q i γ s' -∗
              own_slots γq E' T' q (map_seq 0 (<[i := (γ, s')]>L))).
Proof.
  iIntros (Eqi) "Os".
  have Lt := lookup_lt_Some _ _ _ Eqi.
  rewrite -lookup_map_seq_0 in Eqi.
  iDestruct (big_sepM_lookup_acc_impl_2 _ _ Eqi with "Os") as "[$ Os]".
  iIntros (s' E' T' (SubE & SubT & ?)) "O'".
  rewrite map_seq_insert // Nat.add_0_l. iApply "Os"; [|by iFrame].
  iIntros "!>" (i1 [γ1 s1] _ _). by iApply own_slot_mono.
Qed.

Lemma own_slots_get_pending γq E q L T i γ v M :
  enq_map_enqueued T E →
  L !! i = Some (γ, SlotUnused) →
  let slots := (map_seq 0 L) in
  slots_master γq slots T -∗
  own_slots γq E T q (map_seq 0 L) ==∗
  let slots' := map_seq 0 (<[i := (γ, SlotPending v M)]>L) in
  slots_master γq slots' T ∗ own_slots γq E T q slots' ∗ slot_pending_tok γq i v M.
Proof.
  iIntros (EM Eqi) "OM Os".
  iDestruct (own_slots_access Eqi with "Os") as "[O Os]".
  iDestruct "O" as (t0 LVs0 t1 LVs1) "(AT & F & Tok)".
  iMod (slots_master_get_pending_L v M Eqi with "OM Tok") as "[$ $]".
  iIntros "!>". iApply ("Os" with "[%//]").
  iExists t0, LVs0, t1, LVs1. by iFrame.
Qed.

Lemma SeenPreEnqueued_aggregated {sz γ bf E T LVs i Vi} n0 V0 M0 n V :
  enq_map_enqueued T E →
  LVs !! i = Some Vi →
  set_in_bound M0 E →
  Vi ⊑ V → V0 ⊑ V →
  (n0 ≤ n)%nat → (i ≤ n)%nat →
  SeenPreEnqueued sz γ bf E T LVs ⊢
  @{V} (SeenLogview E M0 ∗ SeenEnqueueds γ bf (n0 `min` sz) E T M0) -∗
  ∃ Mx, ⌜ M0 ⊆ Mx ∧ set_in_bound Mx E ⌝ ∗
        (@{V} (SeenLogview E Mx ∗ SeenEnqueueds γ bf (n `min` sz) E T Mx)) ∗
        (∀ i', ⌜ i' < i `min` sz ⌝%nat →
          ∃ M, ⌜ M ⊆ Mx⌝ ∧ slot_pre_enqueued γ i' M).
Proof.
  iIntros (ET Eqi SubM0 LeVi LeV0 Len0 Lei) "SE #SL".
  rewrite /SeenPreEnqueued.
  iDestruct (big_sepL_lookup _ _ _ _ Eqi with "SE") as "{SE} #SE".
  move : (i `min` sz)%nat (Nat.min_le_compat_r i n sz Lei) => n' Lni.
  iInduction n' as [|n'] "IH".
  { iExists M0. iSplit; [done|].
    rewrite SeenEnqueueds_mono; [iFrame "SL"|lia|done..].
    iIntros (??). exfalso. by lia. }
  iDestruct ("SE" $! n' with "[%]") as (Mn SubMn) "[SMn SLn]"; [lia|].
  iDestruct ("IH" with "[%] []") as (Mx [SubMx SubMx']) "[SMx SLx] {IH}".
  { lia. } { iIntros (i' Lei') "!>". iApply ("SE" with "[%]"). by lia. }
  iExists (Mn ∪ Mx). iSplit; last iSplit.
  - iPureIntro. split; [set_solver|by apply set_in_bound_union].
  - rewrite -SeenLogview_union' -SeenEnqueueds_union'.
    iDestruct "SLn" as "[SL1 SL2]". iDestruct "SMx" as "[SMx1 SMx2]".
    iSplit; [by iFrame "SL1 SMx1"|]. iFrame "SMx2".
    rewrite (@SeenEnqueueds_mono _ _ n' E T Mn); [iFrame "SL2"|lia|done..].
  - iIntros (i' [Lti'| ->]%(Nat.lt_succ_r i')%Nat.le_lteq).
    + iDestruct ("SLx" $! i' with "[%//]") as (M SubM) "SPE".
      iExists M. iFrame "SPE". iPureIntro. set_solver+SubM.
    + iExists Mn. rewrite (view_at_objective_iff (slot_pre_enqueued _ _ _)).
      iFrame "SMn". iPureIntro. set_solver-.
Qed.
End properties.

Section proof.
Context `{!noprolG Σ, !hwqG Σ, !atomicG Σ}.
Local Existing Instances hwq_graphG hwq_queueG.

#[local] Notation iProp := (iProp Σ).
#[local] Notation vProp := (vProp Σ).

Lemma QueueInv_WeakQueueConsistent_instance :
  ∀ γg q G, QueueInv γg q G ⊢ ⌜ WeakQueueConsistent G ⌝.
Proof. by iIntros "* [$ QI]". Qed.

Lemma QueueInv_graph_master_acc_instance :
  ∀ γg q G, QueueInv γg q G ⊢
    graph_master γg (1/2) G ∗
    (graph_master γg (1/2) G -∗ QueueInv γg q G).
Proof. by iIntros "* [$ $] $". Qed.

Lemma QueueLocal_graph_snap_instance sz :
  ∀ N γg q G M, QueueLocal sz N γg q G M ⊢ graph_snap γg G M.
Proof. by iIntros "* [$ _]". Qed.


Lemma new_queue_spec sz :
  new_queue_spec' (new_queue sz) (QueueLocal (Pos.to_nat sz)) QueueInv.
Proof.
  iIntros (N tid Φ) "_ Post".
  wp_lam. wp_op.
  (* allocate back + buffer *)
  wp_apply wp_new; [done..|].
  iIntros (q) "([Hq†|%] & Hq & _)"; [|done].
  rewrite {2}Z2Nat.inj_add; [|lia..].
  rewrite Nat.add_1_r /= Z2Nat.inj_pos own_loc_na_vec_cons.
  iDestruct "Hq" as "[back buff]".

  wp_let. wp_op. rewrite shift_0. wp_write.
  wp_bind (repeat: _)%E.

  (* initialization loop *)
  (* TODO: make a function AllocN with spec *)
  iAssert ((q >> 1) ↦∗{1} repeat #0 0 ∗
           (q >> (1 + 0%nat)) ↦∗{1} repeat #☠ (Pos.to_nat sz - 0))%I
  with "[buff]" as "[HL HR]".
  { rewrite Nat.sub_0_r Nat.add_0_r /= own_loc_na_vec_nil. by iFrame. }
  rewrite -{1}[0%Z]/(Z.of_nat 0).
  move : {1 2 4 6 7}0%nat (Pos2Nat.is_pos sz) => i Lei.
  iLöb as "IH" forall (i Lei). iApply wp_repeat; [done|].

  (* read the counter *)
  wp_op. rewrite shift_0. wp_read. wp_let. wp_op. wp_op.
  (* write to the current slot *)
  rewrite (_: (Pos.to_nat sz - i) = S (Pos.to_nat sz - S i))%nat; last lia.
  rewrite /= own_loc_na_vec_cons.
  iDestruct "HR" as "[Hi HR]".
  rewrite (_: Z.to_nat (1 + i) = S i); last lia.
  wp_write.
  (* increment counter *)
  wp_op. wp_op. rewrite shift_0. wp_write.
  (* compare *)
  wp_op. wp_op.
  case (bool_decide _) eqn:BEq; last first.
  { (* keep looping, use IH. *)
    apply bool_decide_eq_false in BEq.
    iExists false. iSplit; [done|].
    rewrite bool_decide_true; [|done].
    rewrite -(Nat2Z.inj_add _ 1) Nat.add_1_r.
    iIntros "!> !>".
    iApply ("IH" $! (S i) with "[%] Post Hq† back [HL Hi] [HR]");
      [lia|iClear "IH"..].
    - rewrite /= repeat_cons own_loc_na_vec_app
              own_loc_na_vec_singleton repeat_length shift_lblock_assoc. iFrame.
    - rewrite shift_lblock_assoc Nat.add_1_r. iFrame. }
  (* loop done *)
  iClear "IH". apply bool_decide_eq_true in BEq.
  iExists true. iSplit; [done|].
  rewrite bool_decide_false; [|done]. iClear "HR".

  iAssert ((q >> 1) ↦∗{1} repeat #0 (Pos.to_nat sz))%I with "[HL Hi]" as "buff".
  { rewrite (_: Pos.to_nat sz = S i); [|lia].
    rewrite /= repeat_cons own_loc_na_vec_app
            own_loc_na_vec_singleton repeat_length shift_lblock_assoc. iFrame. }

  iIntros "!> !>". wp_seq. wp_op. rewrite shift_0.
  iApply wp_fupd. wp_write.
  clear i Lei BEq.

  iMod (AtomicPtsTo_CON_from_na with "back") as (γb tb0 Vb0) "(sVb0 & sζb & ATb)".

  iAssert (|==> ∃ γs : list gname, ⌜length γs = (Pos.to_nat sz)⌝ ∧
            let slots := map_seq 0%nat ((λ γ, (γ, SlotUnused)) <$> γs) in
            [∗ map] i ↦ γss ∈ slots, let '(γ, s) := γss in
              ∃ t0 V0, ⊒V0 ∗
                (q >> 1 >> i) at↦{γ} (toSlotHist s t0 [V0] t0 []))%I
    with "[buff]" as ">Hslots".
  { move : (Pos.to_nat sz) => n.
    iInduction n as [|n] "IH".
    { iIntros "{buff} !>". iExists []. iSplit; [done|]. done. }
    rewrite /= repeat_cons own_loc_na_vec_app
      own_loc_na_vec_singleton repeat_length shift_lblock_assoc.
    iDestruct "buff" as "[HL Hi]".
    iMod ("IH" with "HL") as (γs EqLs) "Hs {IH}".
    iMod (AtomicPtsTo_CON_from_na with "Hi") as (γ t0 V0) "(sV & sζ & AT)".
    iIntros "!>". iExists (γs ++ [γ]).
    iSplit. { iPureIntro. rewrite app_length /=. lia. }
    rewrite fmap_app /= map_seq_snoc big_sepM_insert; last first.
    { apply lookup_map_seq_None. by right. }
    iFrame "Hs". iExists t0, V0. rewrite /= fmap_length EqLs shift_lblock_assoc.
    by iFrame. }
  iDestruct "Hslots" as (γs EqLs) "Hslots".

  iMod (ghost_alloc γb 0 γs) as (γq) "(bg & SL & Gslots)".
  iDestruct (big_sepM_sep with "Gslots") as "[Gslots Gγs]".
  set L := (λ γ, (γ, SlotUnused)) <$> γs.
  set slots := map_seq 0 L.

  iDestruct (back_value_back_lb_get with "bg") as "#blb".
  iMod (slots_masters_enq_slots_snap_fork with "SL") as "[SL ST]".

  have QC0 := WeakQueueConsistent_empty.
  iMod graph_master_alloc_empty as (γg) "([GM1 GM2] & Gs)".

  assert (QP: QueueProps (Pos.to_nat sz) 0 L ∅ ∅).
  { split.
    - by rewrite /L fmap_length.
    - intros i.
      rewrite /L -list_lookup_fmap -list_fmap_compose
              list_lookup_fmap fmap_Some /= -EqLs -lookup_lt_is_Some.
      split; intros [? []]; [|split; [lia|]]; naive_solver.
    - intros e. rewrite /= elements_empty /= elem_of_nil.
      setoid_rewrite <-list_lookup_fmap. rewrite /L -list_fmap_compose /=.
      setoid_rewrite list_lookup_fmap. setoid_rewrite fmap_Some.
      naive_solver.
    - intros e. setoid_rewrite lookup_nil. setoid_rewrite get_enqInfo_L_Some.
      rewrite /L. setoid_rewrite list_lookup_fmap. setoid_rewrite fmap_Some.
      naive_solver.
    - intros e i. setoid_rewrite lookup_empty. setoid_rewrite get_enqInfo_L_Some.
      rewrite /L. setoid_rewrite list_lookup_fmap. setoid_rewrite fmap_Some.
      naive_solver.
    - done.
    - done. }
  assert (ENQ := QueueProps_enq_map_enqueued QP).

  iAssert (QueueSeen (Pos.to_nat sz) γq q ∅ ∅)%I as "#QS".
  { iExists γb, 0%nat, ∅. iFrame "blb ST". rewrite shift_0.
    iSplitL "sζb"; last iSplitL.
    - iExists _; iFrame. iPureIntro. exists tb0, Vb0. by rewrite lookup_insert.
    - iExists γs. iSplitR; [by iPureIntro|].
      set Ψ : nat → (gname * state) → vProp :=
        (λ i γss, ∃ (ζ : absHist), slot_name γq i γss.1
                      ∗ (q >> 1 >> i) sn⊒{γss.1} ζ)%I.
      iDestruct (big_sepM_sep with "[$Hslots $Gγs]") as "Hslots".
      iPoseProof (big_sepM_map_seq_0_big_sepL _ Ψ with "Hslots") as "P".
      { clear. simpl. iIntros (i [γ s] Eqi) "[AT Gγ]".
        iDestruct "AT" as (t0 V0) "[sV0 AT]".
        iExists _. iFrame "Gγ".
        iDestruct (AtomicPtsTo_AtomicSeen with "AT") as "$". }
      rewrite big_sepL_fmap.
      by iApply (big_sepL_mono with "P").
    - by iApply SeenEnqueueds_empty. }

  iMod (inv_alloc (hwqN N q) _ (QueueInternalInv (Pos.to_nat sz) γq γg q)
          with "[ATb Hslots bg GM1 SL Gslots]") as "#I".
  { iNext. iExists ∅. iFrame "GM1". iSplit; [done|].
    iExists γb, 0%nat, L, ∅. iFrame "bg SL". iSplitR.
    - by iPureIntro.
    - iDestruct (view_at_intro with "[-]") as (Vb) "[InVb P]"; last first.
      { iExists Vb. iExact "P". }
      iSplitL "ATb".
      + iExists tb0, [], Vb0. rewrite /toBackHist /= insert_empty shift_0.
        iFrame "ATb". iSplit; [|done].
        rewrite /SeenPreEnqueued big_sepL_singleton.
        iIntros (i' Le0). exfalso. lia.
      + rewrite /own_slots.
        iDestruct (big_sepM_sep with "[$Hslots $Gslots]") as "HL".
        iApply (big_sepM_mono with "HL").
        iIntros (i [γ s] [_ Eqi]%lookup_map_seq_Some) "[AT Tok]".
        move : Eqi. rewrite Nat.sub_0_r list_lookup_fmap fmap_Some.
        intros (γ' & Eqi & Eq). inversion Eq; clear Eq; subst γ' s.
        iDestruct "AT" as (t0 V0) "[sV0 ATi]".
        iExists t0, [V0], (t0 + 1)%positive, []. iFrame.
        iPureIntro. rewrite /= /pos_add_nat; lia. }

  iIntros "!>". iApply ("Post" $! γg).
  (* QueueInv *)
  iFrame "GM2". iSplit; [|done].
  (* QueueLocal *)
  iSplitL "Gs". { by iApply (graph_snap_empty with "Gs"). }
  iExists _. iFrame "QS I".
Qed.

Lemma atom_enqueue sz :
  enqueue_spec' (enqueue sz) (QueueLocal (Pos.to_nat sz)) QueueInv.
Proof.
  intros N DISJ q tid γg G1 M1 V v Posx.
  iIntros "#sV #(Gs & %γq & QS & QII)" (Φ) "AU".
  iDestruct "QS" as (γb n T0) "(blb & ST0 & (%ζb & sζb & %Hζb) & SS & SE)".
  set E1 := G1.(Es).
  wp_lam. wp_op.

  (* prepare info to be released *)
  iDestruct (bi.persistent_sep_dup with "Gs") as "[_ [_ #PSV]]".
  iDestruct (SeenLogview_closed with "PSV") as %SubD1.
  iCombine "PSV SS SE" as "PSVE".
  iDestruct (view_at_intro_incl with "PSVE sV")
    as (V1) "(sV1 & %LeV & PSV' & SS' & SE') {PSVE}".

  (* use FAA to get a slot. This releases M1. *)
  wp_apply (AtomicSeen_CON_FAA _ _ _ _ _ _ _ ∅ with "sV1 sζb"); [done..|].
  iAuIntro. rewrite /atomic_acc /=.
  (* open the invariant *)
  iInv "QII" as (G2) ">[[%CON GM] QBI]" "Close1".
  iMod (fupd_mask_subseteq (↑histN)) as "Close2"; [solve_ndisj|].

  iDestruct (QueueBaseInv_unfold_snap with "QBI blb") as (n' L T) "[QBI %Len]".
  iDestruct "QBI" as "(bv & SLM & F & %Vb & Ob & OLs)".
  set E2 := G2.(Es).
  iDestruct (graph_master_snap_included with "GM Gs") as %SubG1.
  have SubE1 : E1 ⊑ E2 by apply SubG1.
  iDestruct "Ob" as (tb0 LVb1 Vt1) "(Ob & SLb & %EqLVb1 & %FALVb1)".
  iIntros "!>". iExists Vb, _. iSplitL "Ob".
  { iDestruct (view_at_to_view_join with "Ob") as "$".
    iPureIntro. by apply toBackHist_int_only. }

  iSplit.
  { (* unchanged case *)
    iIntros "[Ob IH]".
    (* close the invariant *)
    iMod "Close2" as "_".
    iMod ("Close1" with "[GM bv SLM F IH Ob SLb OLs]") as "_".
    { iNext. iExists _. iFrame "GM". iSplitR; [done|].
      iExists γb, n', L, T. iFrame "bv SLM F".
      iDestruct (view_join_to_view_at with "Ob") as (Vb') "[sVb' Ob]".
      iExists (Vb ⊔ Vb'). iSplitL "Ob SLb"; last iFrame "OLs".
      iExists tb0, LVb1, Vt1.
      iSplitL "Ob"; last iSplitL "SLb"; [by iFrame..|by iPureIntro]. }
    iIntros "!>". by iFrame "AU". }

  (* changed, incremented *)
  iIntros (tb1 n1 Vr2 Vw2 V2 ζb2' ζb2) "(#sζb2' & Ob & #sV2 & sζVw & ? & F2)".
  (* getting facts about the updated back's history *)
  iDestruct "F" as %QP. assert (ENTE2:=QueueProps_enq_map_enqueued QP).
  destruct QP as [EqL HUN HDEQ HENQ HENQe HEORD HDORD].
  iDestruct "F2" as %(IHζb2 & [Subζb Subζb2'] & Eqtb2 & MAXtb1 &
                      LeV1 & FRtb1 & Eqζb2 & Eqζb2' & LeVr2 & LtVr2 & NLeVr2 & ? & ?).

  assert (Eqtb1' := lookup_weaken _ _ _ _ Eqtb2 Subζb2').
  rewrite Eqζb2 lookup_insert_ne in Eqtb1'; [|clear;lia].
  assert (EqSn' := toBackHist_lookup_Some_None EqLVb1 Eqtb1' FRtb1).
  assert (n1 = Z.of_nat n' ∧ Vr2 = Vt1) as [-> ->].
  { clear -Eqtb1' EqLVb1 EqSn'.
    apply toBackHist_lookup_Some in Eqtb1' as (?&?&?& EqVr2). simplify_eq.
    have Eqtb10 : (Pos.to_nat tb1 - Pos.to_nat tb0)%nat = n' by lia.
    split; [by f_equal|].
    have EqLn : length LVb1 = n'.
    { move : EqLVb1. clear. rewrite app_length /=. lia. }
    move : EqVr2. rewrite Eqtb10 -EqLn lookup_app_r // Nat.sub_diag /=.
    by inversion 1. }

  rewrite -(Nat2Z.inj_add n' 1) Nat.add_1_r
          (toBackHist_insert _ _ _ _ _ EqSn' EqLVb1) in Eqζb2.

  (* update the ghost state *)
  iMod (back_value_update _ _ _ (S n') with "bv") as "bv"; [clear;lia|].
  iDestruct (back_value_back_lb_get with "bv") as "#bl'".

  iDestruct (graph_master_snap with "GM") as "#GS2".

  (* extract the permission if n' < sz *)
  iMod "Close2" as "_".
  iAssert (|={_,⊤ ∖ ∅}=> if decide (n' < Pos.to_nat sz)%nat
                     then slot_pending_tok γq n' v M1
                     else emp)%I
    with "[Close1 GM SLM OLs Ob SLb bv]" as ">Tok".
  { rewrite Eqζb2.
    have EqLVb1' : length LVb1 = n'.
    { move : EqLVb1. clear. rewrite app_length /= Nat.add_1_r. lia. }
    have EqLVb' : length ((LVb1 ++ [Vt1]) ++ [Vw2]) = S (S n').
    { rewrite app_length EqLVb1 /=; clear; lia. }
    have FALVb' : Forall (λ x : view, x ⊑ Vw2) (LVb1 ++ [Vt1]).
    { move : FALVb1. clear -LeVr2. rewrite !Forall_forall.
      move => FA V /elem_of_app [/FA|/elem_of_list_singleton -> //].
      solve_lat. }
    iDestruct (view_join_to_view_at with "Ob") as (Vb') "[sVb' Ob]".
    have SubVb' : Vb ⊑ Vb ⊔ Vb' by clear; solve_lat.

    case decide => [Ltn'|NLtn']; last first.
    { iMod ("Close1" with "[GM bv SLM Ob SLb OLs]") as "_"; [|done].
      iNext. iExists _. iFrame "GM". iSplitR; [done|].
      iExists γb, (S n'), L, T. iFrame "bv SLM". iSplitR.
      - iPureIntro. split; [done| |done..]. clear -HUN NLtn'.
        intros i. rewrite -HUN. apply Nat.nlt_ge in NLtn'.
        by do 2 (rewrite Nat.min_r; [|lia]).
      - iExists (Vb ⊔ Vb'). iSplitR "OLs"; last iFrame "OLs".
        iExists tb0, _, Vw2. iSplitL "Ob"; first by iFrame "Ob".
        iSplitL; [|by iPureIntro].
        iApply (view_at_mono with "SLb"); [done|].
        iIntros "#SE". rewrite {2}/SeenPreEnqueued big_sepL_app big_sepL_singleton.
        iFrame "SE". iIntros (i' Lei').
        rewrite /SeenPreEnqueued big_sepL_app big_sepL_singleton.
        iDestruct "SE" as "[_ SE]". iDestruct ("SE" $! i' with "[%]") as "$".
        clear -EqLVb1 EqLVb1' NLtn' Lei'.
        rewrite EqLVb1 Nat.add_0_r in Lei'. rewrite Nat.add_0_r EqLVb1'. lia. }

    rewrite -EqL in Ltn'.
    destruct (lookup_lt_is_Some_2 _ _ Ltn') as [[γ s] Eqn'].
    destruct (HUN n') as [HUN1 _]. rewrite Eqn' /= in HUN1.
    specialize (HUN1 (ltac:(lia))). inversion HUN1; clear HUN1; subst s.
    set L' := <[n':=(γ, SlotPending v M1)]> L.
    set slots' : gmap _ _ := map_seq 0 L'.
    iAssert (|==> @{Vb} (slots_master γq slots' T
              ∗ own_slots γq E2 T (q >> 1) slots' ∗ slot_pending_tok γq n' v M1))%I
      with "[SLM OLs]" as ">(SLM & OLs & Tok)".
    { rewrite -view_at_bupd -(view_at_objective_iff (slots_master _ _ _) Vb).
      iApply (view_at_mono' with "OLs"); [done|].
      iApply (view_at_mono with "SLM"); [done|]. by apply own_slots_get_pending. }
    rewrite (view_at_objective_iff (slots_master _ _ _))
            (view_at_objective_iff (slot_pending_tok _ _ _ _)).
    iDestruct (slot_pending_tok_slot_pre_enqueued with "Tok") as "#SPE".
    iFrame "Tok".

    iDestruct (slots_masters_enq_slots_snap_agree with "SLM ST0") as %SubT0.
    iAssert (SeenPreEnqueued (Pos.to_nat sz) γq (q >> buff) E2 T ((LVb1 ++ [Vt1]) ++ [Vw2]))%I
      with "[SLb]" as "#SLb'".
    { rewrite (view_at_objective_iff (SeenPreEnqueued _ _ _ _ _ _)).
      rewrite {2}/SeenPreEnqueued big_sepL_app big_sepL_singleton.
      iDestruct "SLb" as "#SLb". iFrame "SLb".
      rewrite Nat.add_0_r app_length /= Nat.add_1_r EqLVb1' (Nat.min_l (S n')); [|lia].
      iIntros (i' [Lti'| ->]%(Nat.lt_succ_r i')%Nat.le_lteq).
      - rewrite /SeenPreEnqueued big_sepL_app big_sepL_singleton EqLVb1'.
        iDestruct "SLb" as "[_ SLb]".
        rewrite Nat.add_0_r (Nat.min_l n'); [|by rewrite -EqL; lia].
        by iDestruct ("SLb" $! i' with "[%//]") as "$".
      - iExists M1. iSplit. { iPureIntro. by eapply set_in_bound_mono. }
        iSplitR; [by iFrame "SPE"|]. iCombine "PSV' SE'" as "SEV'".
        iApply (view_at_mono with "SEV'"); [solve_lat|].
        iIntros "[SL SEs]".
        iDestruct (SeenLogview_map_mono with "SL") as "$"; [done..|].
        iApply (SeenEnqueueds_mono with "SEs"); [lia|done..]. }

    (* finally close the invariant *)
    iMod ("Close1" with "[GM bv SLM Ob OLs]") as "_"; [|done].
    iNext. iExists _. iFrame "GM". iSplitR; [done|].
    iExists γb, (S n'), L', T. iFrame "bv SLM".
    iSplitR; last first.
    { iExists (Vb ⊔ Vb'). iSplitR "OLs"; last iFrame "OLs".
    iExists tb0, _, Vw2. iSplitL "Ob"; first by iFrame "Ob".
    iSplitL;[by iFrame "SLb'"|by iPureIntro]. }

    (* QueueProps *)
    iPureIntro. split; [by rewrite insert_length|..|done|done].
    - clear -HUN Ltn' EqL. apply Nat.le_succ_l in Ltn'.
      rewrite -EqL Nat.min_l; [|done]. intros i. rewrite /L'.
      case (decide (i = n')) => [->|?].
      + rewrite list_lookup_insert; [|lia]. simpl. clear. split; [lia|done].
      + rewrite list_lookup_insert_ne; [|done]. rewrite -HUN -EqL. lia.
    - intros e. rewrite -HDEQ. clear - Ltn' Eqn'. apply exist_proper => i.
      case (decide (i = n')) => ?; [subst i|].
      + rewrite list_lookup_insert /= // Eqn'. naive_solver.
      + by rewrite list_lookup_insert_ne.
    - intros e ve Ve. rewrite -HENQ.
      apply exist_proper => i. apply exist_proper => M.
      case (decide (i = n')) => [->|?].
      + rewrite 2!get_enqInfo_L_Some list_lookup_insert; [|done].
        rewrite Eqn'. clear; naive_solver.
      + by rewrite get_enqInfo_L_insert_ne.
    - intros e i. rewrite -HENQe.
      apply exist_proper => vi. apply exist_proper => Mi. apply exist_proper => Vi.
      case (decide (i = n')) => [->|?].
      + rewrite 2!get_enqInfo_L_Some list_lookup_insert; [|done].
        rewrite Eqn'. clear; naive_solver.
      + by rewrite get_enqInfo_L_insert_ne. } clear Vb.

  iIntros "!> _".
  wp_let. wp_op.
  case (bool_decide _) eqn:BEq; last first.
  { (* failure case, diverge. *)
    iIntros "{#∗%}". wp_if. by iApply (wp_diverge _ _ _ (#_)). }

  rewrite -positive_nat_Z in BEq. apply bool_decide_eq_true, Nat2Z.inj_lt in BEq.
  rewrite decide_True; [|done].
  wp_if. wp_op. wp_op.

  (* open the invariant *)
  iInv "QII" as (G3) ">[[%CON3 GM] QBI]" "Close".
  (* ready to commit, open the AU *)
  iMod "AU" as (G3') "[[_ >GM'] HClose]".

  iDestruct (QueueBaseInv_unfold_snap with "QBI bl'") as (n2 L2 T2) "[QBI %Len2]".
  iDestruct "QBI" as "(bv & SLM & %QP & %Vb & Ob & OLs)".
  assert (ENTE3 := QueueProps_enq_map_enqueued QP).
  destruct QP as [EqL2 HUN2 HDEQ2 HENQ2 HENQe2 HEORD2 HDORD2].

  iDestruct (graph_master_agree with "GM' GM") as %->.
  iDestruct (graph_master_snap_included with "GM GS2") as %SubG2.
  set E3 := G3.(Es). have SubE2 : E2 ⊑ E3 by apply SubG2.
  have SubG13: G1 ⊑ G3 by etrans.
  have SubE13: E1 ⊑ E3 by etrans.

  (* extract ownership of the n' slot *)
  (* TODO: make a lemma *)
  iDestruct (slots_master_slot_pending_agree with "SLM Tok")
    as %[[γn' s'] [Eqn' Eqs']]%fmap_Some. rewrite lookup_map_seq_0 in Eqn'.
  simpl in Eqs'; subst s'.
  rewrite (own_slots_access Eqn'). iDestruct "OLs" as "[On' OLs]".
  iDestruct "On'" as (tn0 LVsn0 tn1 LVsn1) "[On' _]".

  iAssert (∃ ζ, (q >> 1 >> n') sn⊒{γn'} ζ ∗ slot_name γq n' γn')%I
    with "[SLM]" as (ζn') "[#sζn' #Gγn']".
  { clear -BEq Eqn'. iDestruct "SS" as (L EqL) "SS".
    destruct (lookup_lt_is_Some_2 L n') as [γ' Eqn'']. { by rewrite EqL. }
    iDestruct (big_sepL_lookup _ _ _ _ Eqn'' with "SS") as (ζ) "[Gγ sζ]".
    iDestruct (slots_master_slot_name_agree_L with "SLM Gγ") as %Eqγ'.
    rewrite Eqn' /= in Eqγ'. inversion Eqγ'; clear Eqγ'; subst γ'.
    iExists ζ. by iFrame "sζ". }
  rewrite shift_lblock_assoc.
  iDestruct (AtomicPtsTo_AtomicSeen_latest_1 with "On' sζn'") as %Subζn'.
  iDestruct (AtomicSeen_non_empty with "sζn'") as %NEζn'.

  rewrite (_: Z.to_nat (1 + n') = (1 + n')%nat); last lia.
  wp_apply (AtomicSeen_concurrent_write _ _ _ _ _ _ ∅ _ Vb #v
              with "[$sζn' $On' $ sV2]"); [done..|].
  iIntros (t3 V3' V3) "(F & #sV3 & #sζn3 & On')".
  iDestruct "F" as %(MAXt3 & FRt3 & LeV2 & NEqV23 & _ & <-).

  iDestruct (graph_master_consistent with "GM") as %EGCs3.

  have SubM: set_in_bound M1 E3.
  { clear - SubD1 SubE1 SubE2. eapply set_in_bound_mono; [|exact SubD1]. by etrans. }
  set V' := V3.
  have LeV1' : V1 ⊑ V'. { clear -LeV1 LeV2. solve_lat. }
  have bLeV1' : bool_decide (V1 ⊑ V') by eapply bool_decide_unpack; eauto.
  set Venq : dataView := mkDView V1 V' V' bLeV1'.

  assert (GIP:= graph_insert_props_base _ (Enq v) _ Venq SubM EGCs3).
  destruct GIP as [enqId M' enqE G' LeG' SubM' SUB' InenqId NEM1 EGCs'].
  set E' := G'.(Es). have LeE' : E3 ⊑ E' by apply LeG'.

  assert (FRe' : ∀ i e, get_enqInfo_L L2 i = Some e → einf_evt e ≠ enqId).
  { rewrite /einf_evt /= => i e INL2 Eqe.
    destruct e as [[ve Me] [Ve e]].
    destruct (HENQ2 e ve Ve) as [(eV & EqeV & _) _]; [by do 2 eexists|].
    simpl in Eqe. subst e. clear -EqeV. apply lookup_lt_Some in EqeV. lia. }

  have EqNT: T2 !! enqId = None.
  { destruct (T2 !! enqId) as [i|] eqn:Eqi; [|done]. exfalso.
    destruct (HENQe2 enqId i) as [_ (vi & Mi & Vi &Eqei)]; [done|].
    by apply FRe' in Eqei. }
  iDestruct (slots_masters_enq_slots_snap_agree with "SLM ST0") as %SubT0.

  iCombine "GM GM'" as "GM".
  iMod (graph_master_update _ _ _ LeG' EGCs' with "GM") as "([GM GM'] & Gs')".

  iAssert (@{V'} SeenLogview E' M')%I with "[]" as "#SL'".
  { rewrite -SeenLogview_insert'. iSplitL; [|done].
    erewrite SeenLogview_map_mono; [iFrame "PSV'"|done..]. }

  have SE': seen_enqueued E' enqId v V'.
  { exists enqE. split; [|done]. by rewrite lookup_app_1_eq. }

  iMod (slots_master_set_enqueued_L enqId V3 Eqn' EqNT with "SLM Tok")
    as "[SLM GEnq]".
  iMod (slots_masters_enq_slots_snap_fork with "SLM") as "[SLM #ST']".

  set T' := <[enqId:=n']> T2.
  have SubT2 : T2 ⊆ T' by apply insert_subseteq.
  have SubT0' : T0 ⊆ T' by etrans.
  have SubE1' : E1 ⊑ E' by etrans.
  have ENTE' : enq_map_enqueued T' E'.
  { intros e. case (decide (e = enqId)) => [->|?].
    - rewrite lookup_app_1_eq lookup_insert; clear; naive_solver.
    - by rewrite lookup_insert_ne // lookup_app_1_ne. }

  iAssert (@{V'} SeenEnqueueds γq (q >> buff) n' E' T' M')%I with "[GEnq]" as "#SEs".
  { rewrite -SeenEnqueueds_union'. iSplitL.
    - rewrite -(SeenEnqueueds_singleton n' γn');
        [|by rewrite lookup_app_1_eq|by rewrite lookup_insert|eauto..].
      iSplit; [done|]. iSplit. { rewrite view_at_view_at /=. iFrame "SL'". }
      iFrame "GEnq Gγn'".
      iExists _, t3. iSplit; last first.
      + rewrite view_at_view_at shift_lblock_assoc. iFrame "sζn3".
      + iPureIntro. by rewrite lookup_insert.
    - iApply (view_at_mono with "SE'"); [done|].
      by apply SeenEnqueueds_mono; [lia|done..]. }

  iDestruct (view_at_mono_2 _ (Vb ⊔ V3) with "OLs") as "OLs"; [solve_lat|].
  iSpecialize ("OLs" $! (SlotEnqueued (v,M1,(V3,enqId))) E' T' with "[%//] [On']").
  { iExists tn0, LVsn0, t3, []. rewrite shift_lblock_assoc.
    iSplitL "On'"; last iSplitR.
    - by iFrame "On'".
    - iPureIntro. clear -FRt3 MAXt3 NEζn' Subζn'.
      apply lookup_map_seqP_None in FRt3 as [Ltt3|LP].
      + exfalso. apply map_choose in NEζn' as (t & vVt & Eqt).
        apply (lookup_weaken _ _ _ _ Eqt), lookup_map_seqP_Some in Subζn'.
        destruct Subζn' as [Letn0 _].
        specialize (MAXt3 t (ltac:(by eexists))). lia.
      + move : LP. by rewrite zip_with_length_r_eq // repeat_length.
    - iSplit; [|by iPureIntro]. rewrite view_at_view_at. by iFrame "SEs". }

  assert (NI: ∀ e1 e2, (e1, e2) ∈ G'.(com) → e1 ≠ enqId ∧ e2 ≠ enqId).
  { clear. move => ?? /(gcons_com_included G3) [/= ]. lia. }
  have QC' : WeakQueueConsistent G'. {
    destruct CON3 as [CONW CONRel CONAcq [CONNZ CON2 CON3 CON4 CON5 CON6 CON7a CON7b]].
    constructor; [..|constructor].
    - clear -LeV1 LeV2 NEqV23 CONW.
      apply graph_insert_event_is_writing; [done|]. simpl. intros _ ->.
      apply NEqV23. by apply : (anti_symm (⊑)).
    - clear -CONRel. by apply graph_insert_event_is_releasing.
    - clear -CONAcq. apply graph_insert_event_is_acquiring; [done|].
      simpl; intros []; congruence.
    - intros ??? [Eq1|[-> <-]]%lookup_app_1; [by apply (CONNZ _ _ _ Eq1)|].
      clear -Posx. simpl. inversion 1. by subst.
    - intros e d InG'. destruct (NI _ _ InG').
      destruct (CON2 _ _ InG')
        as (LteD & eV & dV & v' & Eqe & Eqd & EqeV & EqdV & LeedV).
      split; [done|]. exists eV, dV, v'.
      split; last split; [by rewrite lookup_app_1_ne..|done].
    - done.
    - intros ?? [?|[-> <-]]%lookup_app_1; [by eapply CON4|done].
    - intros e eV Eqe Empe ee ve eVe Eqee Eqve Inee.
      have NEq: enqId ≠ e.
      { clear -Eqe Empe. move => ?. subst e. rewrite lookup_app_1_eq in Eqe.
        inversion Eqe. by subst eV. }
      rewrite lookup_app_1_ne in Eqe; [|done].
      apply (CON5 _ _ Eqe Empe ee ve eVe); [|done..].
      rewrite lookup_app_1_ne in Eqee; [done|]. intros ->.
      apply (egcons_logview_closed _ EGCs3 _ _ Eqe), lookup_lt_is_Some in Inee.
        clear -Inee. lia.
    - done.
    - clear -CON7a SUB'. by apply graph_insert_xo_eco.
    - intros e1 eV1 v1 e2 d2 eV2 Eqe1 Eqv1 In2.
      destruct (NI _ _ In2). rewrite lookup_app_1_ne; [|done].
      intros Eqe2 IneV2.
      rewrite lookup_app_1_ne in Eqe1; last first.
      { intros ->. apply (egcons_logview_closed _ EGCs3 _ _ Eqe2),
                          lookup_lt_is_Some in IneV2. clear -IneV2. by lia. }
      destruct (CON7b _ _ _ _ _ _ Eqe1 Eqv1 In2 Eqe2 IneV2) as (d1 & In1 & NIdV1).
      exists d1. split; [done|].
      destruct (NI _ _ In1). rewrite lookup_app_1_ne; [|done]. exact NIdV1.
  }

  set L' := (<[n':=(γn', SlotEnqueued (v,M1,(V3, enqId)))]> L2).

  rewrite -EqL2 in BEq.
  iAssert (⌜ enq_map_enqueued T0 E1 ⌝)%I with "[SE]" as %ENTE1.
  { by iDestruct "SE" as "[[_ $] _]". }

  iAssert (⌜ ∀ e0 i0, e0 ∈ M1 → T0 !! e0 = Some i0 → (i0 ≤ n')%nat ⌝)%I
    with "[SLM]" as %MAXsn'.
  { iIntros (e0 i0 In0 Eqi0). iDestruct "SE" as "[_ SE]".
    destruct (ENTE1 e0) as [(eV0 & v0 & Eqi & Eqvi) _]. { by exists i0. }
    iSpecialize ("SE" $! e0 v0 eV0.(ge_view) eV0.(ge_lview) with "[%]").
    { split; [done|]. rewrite Eqi -Eqvi. clear; by destruct eV0. }
    iDestruct "SE" as "(sV0 & SL0 & SE0)".
    iDestruct "SE0" as (i0' γi' Mi' Vi' (Lei' & Eqe0 & ?)) "_". iPureIntro.
    rewrite Eqi0 in Eqe0. inversion Eqe0; subst i0'. lia. }

  have QP' : QueueProps (Pos.to_nat sz) n2 L' T' G'.
  { split.
    - by rewrite insert_length.
    - clear -Len2 HUN2 Eqn' BEq. intros i.
      case (decide (i = n')) => [->|?].
      + rewrite list_lookup_insert //. split; [lia|done].
      + by rewrite /L' list_lookup_insert_ne.
    - intros e. rewrite -HDEQ2. clear -BEq Eqn'. apply exist_proper => i.
      case (decide (i = n')) => ?; [subst i|].
      + rewrite list_lookup_insert /= // Eqn'. naive_solver.
      + by rewrite list_lookup_insert_ne.
    - intros e ve Ve. case (decide (e = enqId)) => Eqe.
      + subst e. rewrite lookup_app_1_eq. split.
        * intros (i & Mi & Eqi). case (decide (i = n')) => ?.
          { subst i. rewrite get_enqInfo_L_insert /= in Eqi; [|done].
            inversion Eqi. subst ve Ve. clear -NEM1; naive_solver. }
          { rewrite get_enqInfo_L_insert_ne in Eqi; [|done].
            clear -Eqi FRe'. exfalso. by apply FRe' in Eqi. }
        * clear -BEq NEM1.
          intros (?&?&Eqv&?).
          simplify_eq. simpl in *. simpl in Eqv; inversion Eqv; clear Eqv; subst ve.
          exists n', M1. by apply get_enqInfo_L_insert.
      + rewrite lookup_app_1_ne; [|done]. rewrite -HENQ2.
        apply exist_proper => i. apply exist_proper => M.
        case (decide (i = n')) => ?.
        * subst i. rewrite get_enqInfo_L_insert /=; [|done].
          rewrite get_enqInfo_L_Some Eqn'. clear -Eqe. naive_solver.
        * by rewrite get_enqInfo_L_insert_ne.
    - intros e i.
      case (decide (e = enqId)) => [->|Eqe].
      + rewrite lookup_insert. case (decide (i = n')) => [->|?].
        * rewrite get_enqInfo_L_insert; [|done]. simpl. clear; naive_solver.
        * rewrite get_enqInfo_L_insert_ne; [|done]. split.
          { by intros (?&?&? &?%FRe'). } { by inversion 1. }
      + rewrite lookup_insert_ne; [|done]. rewrite -HENQe2.
        apply exist_proper => vi. apply exist_proper => Mi. apply exist_proper => Vi.
        case (decide (i = n')) => ?.
        * subst i. rewrite get_enqInfo_L_insert /=; [|done].
          rewrite get_enqInfo_L_Some Eqn'. clear -Eqe. naive_solver.
        * by rewrite get_enqInfo_L_insert_ne.
    - intros i1 i2 e1 e2 eV2 Eqi1 Eqi2.
      case (decide (enqId = e2)) => [?|NEq]; last first.
      { rewrite lookup_app_1_ne; [|done]. intros Eqe2 IneV2.
        rewrite lookup_insert_ne in Eqi2; [|done].
        rewrite lookup_insert_ne in Eqi1.
        + by apply (HEORD2 _ _ _ _ _ Eqi1 Eqi2 Eqe2 IneV2).
        + intros <-. apply (egcons_logview_closed _ EGCs3 _ _ Eqe2),
                           lookup_lt_is_Some in IneV2. clear -IneV2. lia. }
      subst e2. rewrite lookup_app_1_eq => EqeV2.
      inversion EqeV2; clear EqeV2; subst eV2.
      rewrite lookup_insert in Eqi2. inversion Eqi2; clear Eqi2; subst i2.
      rewrite /= elem_of_union elem_of_singleton.
      intros [EqEnq1|InM1].
      { subst e1. rewrite lookup_insert in Eqi1. clear -Eqi1; by inversion Eqi1. }
      rewrite lookup_insert_ne in Eqi1; last by intros <-.
      apply (MAXsn' e1 i1 InM1),
            (enq_map_enqueued_mono_inv _ _ ENTE1 ENTE3 SubT0 SubE13); [|done].
      by apply SubD1, InM1.
    - intros i1 i2 e1 e2 d2 dV2 Eqi1 Eqi2 Lei12 Ind2.
      destruct (NI _ _ Ind2) as [NEq2 ]. rewrite lookup_insert_ne in Eqi2; [|done].
      rewrite lookup_app_1_ne; [|done] => Eqd2 IndV2.
      rewrite lookup_insert_ne in Eqi1; last first.
      { intros <-. apply (egcons_logview_closed _ EGCs3 _ _ Eqd2),
                          lookup_lt_is_Some in IndV2. clear -IndV2. lia. }
      apply (HDORD2 _ _ _ _ _ _ Eqi1 Eqi2 Lei12 Ind2 Eqd2 IndV2). }

  rewrite bi.and_elim_r.
  iMod ("HClose" $! V' G' enqId (Enq v) Venq M' with "[GM' Gs' $sV3]") as "HΦ".
  { (* Public Post *) iFrame (QC') "GM'". iSplitL; last by iPureIntro.
    (* QueueLocal *)
    iFrame "Gs' SL'". iExists γq. iFrame "QII". iExists γb, (S n'), T'.
    iFrame "bl' ST' SS'". iSplitR.
    { iExists ζb2'. iFrame "sζb2'". iPureIntro. move : Eqζb2'. clear.
      rewrite -(Nat2Z.inj_add n' 1) Nat.add_1_r. by do 2 eexists. }
    (* TODO this can be stricter: n' instead of S n' *)
    iApply (view_at_mono with "SEs"); [done|]. rewrite EqL2 in BEq.
    apply SeenEnqueueds_mono; [|done..]. clear -BEq; lia. }
  iIntros "!>".
  (* re-establish the invariant *)
  iMod ("Close" with "[-HΦ]") as "_".
  { iNext. iExists G'. iSplitL "GM". { by iFrame (QC') "GM". }
    iExists γb, n2, _, T'. iFrame "bv SLM". iSplitR; first by iPureIntro.
    iExists (Vb ⊔ V'). iSplitL "Ob"; [|iFrame "OLs"].
    rewrite (own_back_mono LeE' SubT2 ENTE'). by iFrame "Ob". }

  iIntros "!>". by iApply "HΦ".
Qed.

Definition Seen_EnqDeq γq γg bf (Mx : logView) (n : nat) (k : nat) : vProp :=
  ∃ M G T, ⌜ Mx ⊆ M ∧ set_in_bound M G.(Es) ∧
            (* we don't need all of consistency, but whatever *)
            WeakQueueConsistent G ⌝ ∗
    graph_snap γg G M ∗
    enq_slots_snap γq T ∗
    SeenEnqueueds γq bf n G.(Es) T M ∗
    ⌜ ∀ i e, (i < k)%nat → e ∈ M → T !! e = Some i → ∃ d, (*d ∈ M ∧*) (e, d) ∈ G.(com) ⌝.

Lemma atom_dequeue sz b :
  dequeue_spec' (dequeue sz b) (QueueLocal (Pos.to_nat sz)) QueueInv.
Proof.
  intros N DISJ q tid γg G1 M1 V.
  iIntros "#sV #GI" (Φ) "AU".
  iLöb as "IH1".
  wp_rec. wp_op.
  wp_bind (!ᵃᶜ _)%E.

  iDestruct "GI" as "(Gs & %γq & QS & QII)".
  iDestruct "QS" as (γb n T0) "(blb & ST0 & (%ζb & sζb & %Hζb) & SS & SE)".

  (* open the invariant to get the back atomic points-to *)
  iInv "QII" as (G2) ">[[%CON GM] QBI]" "Close".

  iDestruct (QueueBaseInv_unfold_snap with "QBI blb") as (n' L T) "[QBI %Len]".
  iDestruct "QBI" as "(bv & SLM & %QP2 & %Vb & Ob & OLs)".
  assert (ENTE2 := QueueProps_enq_map_enqueued QP2).
  iDestruct (graph_master_snap_included with "GM Gs") as %SubG1.
  set E1 := G1.(Es). set E2 := G2.(Es).
  have SubE1 : E1 ⊑ E2 by apply SubG1.

  iDestruct (graph_master_snap with "GM") as "#Gs2".
  iDestruct (slots_masters_enq_slots_snap_agree with "SLM ST0") as %SubT0.
  iMod (slots_masters_enq_slots_snap_fork with "SLM") as "[SLM #ST]".
  iDestruct (back_value_back_lb_get with "bv") as "#blb'".
  iDestruct "Ob" as (tb0 LVb1 Vt1) "(Ob & #SLb & %EqLVb1 & %FALVb1)".

  (* TODO this may be too early *)
  iDestruct (bi.persistent_sep_dup with "Gs") as "[_ [_ #PSV]]".
  iDestruct (SeenLogview_closed with "PSV") as %SubD1.
  iCombine "SS PSV SE" as "PSVE".
  iDestruct (view_at_intro_incl with "PSVE sV")
    as (V1) "(sV1 & %LeV & SS' & SLE) {PSVE}".

  wp_apply (AtomicSeen_acquire_read with "[$sζb $Ob $sV1]"); [solve_ndisj|].
  iIntros (tb vb V2' V2 ζb2) "(F' & #sV2 & #sζb2' & Ob)".
  iDestruct "F'" as %([Subζb Subζb2] & Eqtb & MAXtb & LeV2').
  iDestruct (view_at_elim with "sV2 sζb2'") as "sζb2".

  (* close the invariant *)
  iMod ("Close" with "[GM bv SLM OLs Ob]") as "_".
  { iNext. iExists _. iFrame "GM". iSplit; [done|].
    iExists γb, n', L, T. iFrame (QP2) "bv SLM".
    iExists (Vb ⊔ V2). iSplitR "OLs"; last by iFrame "OLs".
    iExists tb0, LVb1, Vt1. iFrame "SLb". iFrame. by iPureIntro. }
  rewrite (view_at_objective_iff (SeenPreEnqueued _ _ _ _ _ _)). clear Vb.

  (* get the fact that the value read is a number *)
  assert (Eqtb' := lookup_weaken _ _ _ _ Eqtb Subζb2). assert (Eqtb'2 := Eqtb').
  apply toBackHist_lookup_Some in Eqtb' as (Letb & -> & Lttb & EqV2').
  have Lenb : (n ≤ Pos.to_nat tb - Pos.to_nat tb0)%nat.
  { destruct Hζb as (tbn & Vbn & Eqtbn).
    have Eqtbn2 := lookup_weaken _ (toBackHist n' tb0 (LVb1 ++ [Vt1])) _ _
                                Eqtbn ltac:(by etrans).
    apply (toBackHist_lookup_Some_order Eqtbn2 Eqtb'2), MAXtb. by eexists. }
  clear Eqtb'2.

  iIntros "!>". rewrite -(positive_nat_Z sz).
  wp_apply minimum_spec_nat. wp_let.

  have LeV12 : V1 ⊑ V2 by clear-LeV2'; solve_lat.
  have LeV22 : V2' ⊑ V2 by clear-LeV2'; solve_lat.
  iDestruct (SeenPreEnqueued_aggregated n V1 M1 (Pos.to_nat tb - Pos.to_nat tb0)
              V2 ENTE2 EqV2' with "SLb []")
    as (Mx [SubM1x SubMx]) "[SLx ALLx]"; [|done|done|done|done|..].
  { by eapply set_in_bound_mono. }
  { iApply (view_at_mono with "SLE"); [done|]. iIntros "[SL SEs]".
    iDestruct (SeenLogview_map_mono with "SL") as "$"; [done..|].
    by iApply (SeenEnqueueds_mono with "SEs"). }

  set nx : nat := ((Pos.to_nat tb - Pos.to_nat tb0) `min` Pos.to_nat sz)%nat.
  set k : nat := nx.
  iAssert (Seen_EnqDeq γq γg (q >> buff) Mx nx (nx - k)%nat)%I
    with "[Gs2 SLx]" as "-#SEDa {SLx}".
  { iClear "IH1". rewrite Nat.sub_diag.
    iExists Mx, G2, T. iSplit; [done|]. iFrame "ST".
    iDestruct (view_at_elim with "sV2 SLx") as "[$ SL]".
    iSplitR; last iSplitR.
    - by iDestruct "Gs2" as "[$ _]".
    - iApply (SeenEnqueueds_mono with "SL"); [|done..]. rewrite /nx; lia.
    - iPureIntro. clear. intros ???. exfalso. lia. }

  (* generalize for iLöb *)
  move : (Nat.le_refl k). rewrite {2 3 5}/k. move : k => k Lek.
  wp_lam.
  iLöb as "IH2" forall (k Lek).
  wp_rec. wp_op.

  case_bool_decide as Eqk0.
  { (* internal loop done, jump back to external loop using the IH1. *)
    apply (Nat2Z.inj _ 0) in Eqk0. subst k.
    wp_if. iApply ("IH1" with "AU"). }

  (* loop body : slot is still in range *)
  iClear "IH1". wp_if.
  (* get observation of the slot *)
  have NEqk0 : (k ≠ 0)%nat. { clear -Eqk0; lia. } clear Eqk0.
  wp_op. wp_let. wp_op. wp_op.
  rewrite -Nat2Z.inj_sub; [|done].

  set idx : nat := (nx - k)%nat.
  have Ltidx: (idx < Pos.to_nat sz)%nat. { clear -NEqk0 Lek. subst idx nx. lia. }

  iDestruct "SEDa" as (Mx' Gx Tx (SubMx' & SubMEx' & CONx)) "(Gsx & #STx & SEx' & %SEDx)".
  set Ex := Gx.(Es).
  iAssert (∃ γi ζi, slot_name γq idx γi ∗ (q >> (1 + idx)) sn⊒{γi} ζi
           ∧ ⌜ if (decide (∃ e, e ∈ Mx' ∧ Tx !! e = Some idx))
               then ∃ ti (vi : Z) Vi, ζi !! ti = Some (#vi, Vi) ∧ 0 < vi
              else True ⌝)%I
    with "[SEx']" as (γi ζi) "(#sli & #sζi & %Hζi)".
  { iClear "IH2". case decide => [[e [InMx' Eqe]]|NInMx'].
    - iDestruct "SEx'" as "[[_ %ENTEx] SEx]".
      destruct (ENTEx e) as [(eV & v & EqeV & Eqv) _]. { by exists idx. }
      iSpecialize ("SEx" $! e v eV.(ge_view) eV.(ge_lview) with "[%]").
      { split; [done|]. rewrite EqeV -Eqv. clear; by destruct eV. }
      iDestruct "SEx" as "(sVx & ? & SEx)".
      iDestruct "SEx" as (i γi Mi Vi (Lei & Eqei & EqeVM & NIMi)) "(SEx & SN & sζi)".
      iDestruct "sζi" as (ζi ti Eqti) "sζi".
      rewrite Eqe in Eqei. inversion Eqei; clear Eqei; subst i.
      iDestruct (view_at_elim with "sVx sζi") as "sζi". rewrite shift_lblock_assoc.
      iExists γi, ζi. iFrame "SN sζi". iPureIntro.
      exists ti, v. eexists. split; [done|].
      apply (bsq_cons_enq_non_zero _ CONx e eV v EqeV Eqv).
    - iDestruct "SS" as (L0 EqL0) "SS".
      destruct (lookup_lt_is_Some_2 L0 idx) as [γi Eqγi]; [by rewrite EqL0|].
      iDestruct (big_sepL_lookup _ _ _ _ Eqγi with "SS") as (ζi) "[sli sζi]".
      iExists γi, ζi. rewrite shift_lblock_assoc. by iFrame "sli sζi". }

  iCombine "Gsx SEx'" as "SED".
  iDestruct (view_at_intro_incl with "SED sV2") as (V20) "(#sV20 & %LeV20 & #Gsx & #SED')".
  (* use XCHG to acquire the dequeue item if available in the slot.
    In the strong version, this releases whatever we got from the read of the
    back field earlier, and also what we know locally . *)
  iMod (rel_objectively_intro (⊒∅) tid with "[]") as "HRE".
  { iApply objective_objectively. iApply monPred_in_bot. }
  rewrite (_: Z.to_nat (1 + idx) = (1 + idx)%nat); last lia.
  awp_apply (AtomicSeen_CON_XCHG_int _ _ _ _ _ 0 _ ∅ with "sV20 sζi [HRE]");
    [done|by destruct b..|].
  rewrite /atomic_acc /=.

  (* open the invariant *)
  iInv "QII" as (G3) ">[[%CON3 GM] QBI]" "Close2".
  (* ready to commit, open the AU *)
  iMod "AU" as (G3') "[[_ >GM'] Close1]".
  iDestruct (graph_master_agree with "GM' GM") as %->.
  iDestruct (graph_master_snap_included with "GM Gs2") as %SubG2.
  set E3 := G3.(Es). have SubE2 : E2 ⊑ E3 by apply SubG2.
  have SubG13: G1 ⊑ G3 by etrans.
  have SubE13: E1 ⊑ E3 by etrans.
  iDestruct (QueueBaseInv_unfold_snap with "QBI blb'") as (n2 L2 T2) "[QBI %Len2]".
  iDestruct "QBI" as "(bv & SLM & %QP & %Vb & Ob & OLs)".
  assert (ENTE3 := QueueProps_enq_map_enqueued QP).
  assert (HINJ2 := QueueProps_inj QP).
  destruct QP as [EqL2 HUN2 HDEQ2 HENQ2 HENQe2 HEORD2 HDORD2].

  iDestruct (graph_master_snap_included_2 with "GM Gsx") as %SubGx.
  have SubEx : Ex ⊑ E3 by apply SubGx.
  iDestruct (slots_masters_enq_slots_snap_agree with "SLM STx") as %SubTx.

  (* get the AtomicPtsTo of idx *)
  iDestruct (slots_master_slot_name_agree_L with "SLM sli")
    as %[[γi' si][Eqγi Eq']]%fmap_Some. simpl in Eq'; subst γi'.
  rewrite (own_slots_access Eqγi). iDestruct "OLs" as "[Oi OLs]".
  iDestruct "Oi" as (ti0 LVsi0 ti1 LVsi1) "(Oi & %Fti & OSi)".
  rewrite shift_lblock_assoc.

  iIntros "!>". iExists Vb, _. iSplitL "Oi".
  { iDestruct (view_at_to_view_join with "Oi") as "$".
    iPureIntro. by apply toSlotHist_int_only. }

  iSplit.
  { (* AU cancel (peek) case, nothing changed *)
    iClear "IH2". iIntros "[Oi IH]".
    rewrite bi.and_elim_l.
    iMod ("Close1" with "[$GM' //]") as "$". iFrame "SED".
    (* close the invariant *)
    iMod ("Close2" with "[-]") as "_"; [|done].
    iNext. iExists _. iFrame "GM". iSplitR; [done|].
    iExists γb, n2, L2, T2. iFrame "bv SLM". iSplitR. { by iPureIntro. }
    iDestruct (view_join_to_view_at with "Oi") as (Vb') "[sVb' Oi]".
    iExists (Vb ⊔ Vb'). iSplitL "Ob"; first iFrame "Ob".
    iDestruct (view_at_mono_2 _ (Vb ⊔ Vb') with "OLs") as "OLs"; [solve_lat|].
    iSpecialize ("OLs" $! si E3 with "[%//] [Oi OSi]").
    - iExists ti0, LVsi0, ti1, LVsi1. rewrite shift_lblock_assoc.
      iFrame "Oi OSi". by iPureIntro.
    - rewrite list_insert_id; [|done]. by iFrame "OLs". }

  (* XCHG succeeds *)
  iIntros (ti2 vi2 Vr3 Vw3 V3 ζi2' ζi2) "(sζi2' & Oi & #sV3 & sζiw & %LeVw3 & F2)".
  iDestruct "F2" as %(IHζi2 & [Subζi Subζi2'] & Eqti2 & MAXti2 & LeV2 & FRti2
        & Eqζi2 & Eqti2' & LeVr3' & NEqVrw3 & NLeV3 & NEqV2 & EwVw3).
  have LeVr3 : Vr3 ⊑ V3 by etrans.
  assert (Eqvi2 := lookup_weaken _ _ _ _ Eqti2 Subζi2').
  rewrite Eqζi2 lookup_insert_ne in Eqvi2; last (clear; lia).
  assert (∃ z2 : Z, vi2 = z2) as [z2 ->].
  { assert (Eqvi := toSlotHist_int_only si ti0 LVsi0 ti1 LVsi1 ti2 #vi2).
    rewrite Eqvi2 /= in Eqvi.
    destruct Eqvi as [z Eqz]; [done|]. inversion Eqz. by eexists. }

  iDestruct (graph_master_consistent with "GM") as %EGCs3.
  case (decide (z2 = 0)) => [Eqz2|NEqz2].
  { subst z2.
    (* nothing to commit, retry with internal "loop" using "IH2" *)

    (* preparing for the IH2 *)
    iDestruct (graph_master_snap with "GM") as "#Gs3".
    iMod (slots_masters_enq_slots_snap_fork with "SLM") as "[SLM #ST2]".
    iDestruct (view_at_elim with "sV20 SED'") as "SEx'".
    iDestruct (view_at_elim with "sV20 Gsx") as "Gsx'".
    set M' : logView :=
      match si with
      | SlotUnused (* impossible *) | SlotPending _ _ | SlotEnqueued _ => ∅
      | SlotDequeued (_,M,(_,e)) _ =>
        if (decide (ti1 < ti2)%positive) then {[ e ]} else ∅
      end.
    have EqInM : ∀ e, e ∈ M' →
      (ti1 < ti2)%positive ∧ ∃ v Me Ve Vd, si = SlotDequeued (v,Me,(Ve,e)) Vd.
    { clear; intros e; subst M'.
      destruct si as [| |[[v Me][Ve e']]|[[v Me][Ve e']]Vd]; [done..|].
      case decide => [? /elem_of_singleton <-|//]. naive_solver. }
    iAssert (SeenEnqueueds γq (q >> buff) idx E3 T2 M' ∗ SeenLogview E3 M')%I
      with "[OSi]" as "#[SEx'' SLgM']".
    { iRevert "sV3". iIntros "{#} #sV3". rewrite /M'.
      destruct si as [| |[[v Me][Ve e]]|[[v Me][Ve e]]Vd];
        [(iClear "#∗"; iSplit; iStopProof;
          by [apply SeenEnqueueds_empty|apply SeenLogview_empty])..|].
      case decide => Ltti; last first.
      { iClear "#∗"; iSplit; iStopProof;
          by [apply SeenEnqueueds_empty|apply SeenLogview_empty]. }
      iDestruct "OSi" as "[SE (%SE & %LeVe & %FA)]".
      rewrite view_at_view_at.
      assert (InV3 := toSlotHist_lookup_dequeued_gt Eqvi2 Fti Ltti).
      assert (LeVe': Ve ⊑ V3).
      { etrans; last apply LeVr3. etrans; [exact LeVe|].
        apply elem_of_cons in InV3 as [->|InV3]; [done|].
        rewrite ->Forall_forall in FA. by apply FA. }
      iDestruct (view_at_elim with "[] SE") as "SE".
      { by iApply (monPred_in_mono with "sV3"). } iSplit.
      - iApply (SeenEnqueueds_mono with "SE"); [done..|set_solver-|done].
      - destruct SE as (eV & Eqee & Eqev & EqeV). iDestruct "SE" as "[_ SE]".
        iSpecialize ("SE" $! e v eV.(ge_view) eV.(ge_lview) with "[%]").
        + split; [set_solver-|]. rewrite -Eqev Eqee. clear; by destruct eV.
        + iDestruct "SE" as "(sV & SL & _)".
          iDestruct (view_at_elim with "sV SL") as "SL".
          iApply (SeenLogview_downclosed with "SL").
          by apply elem_of_subseteq_singleton, (egcons_logview_event _ EGCs3 _ _ Eqee).
    }

    (* close the AU *)
    rewrite bi.and_elim_l.
    iMod ("Close1" with "[$GM' //]") as "AU".
    (* now we can close the invariant *)
    iMod ("Close2" with "[-AU]") as "_".
    { iClear "IH2". iNext. iExists _. iFrame "GM". iSplitR; [done|].
      iExists γb, n2, L2, T2. iFrame "bv SLM". iSplitR. { by iPureIntro. }
      iDestruct (view_join_to_view_at with "Oi") as (Vb') "[sVb' Oi]".
      have ? : Vb ⊑ Vb ⊔ Vb' by clear;solve_lat.
      iExists (Vb ⊔ Vb'). iSplitL "Ob"; first iFrame "Ob".
      iDestruct (view_at_mono_2 _ (Vb ⊔ Vb') with "OLs") as "OLs"; [solve_lat|].
      iSpecialize ("OLs" $! si E3 with "[%//] [Oi OSi]").
      - destruct (toSlotHist_insert_0 Vw3 Eqvi2 FRti2 Fti) as
          (LVs0' & LVs1' & t1' & EqLVs & Let1' & EqSH).
        { clear -Eqγi HENQ2 CON3.
          destruct si as [| |[[vi Mi][Vi]]|[[vi Mi][Vi]]]; [done..| |].
          - destruct (HENQ2 e vi Vi) as [(ev & EqeV & Eqev & _) _].
            { exists idx, Mi. apply get_enqInfo_L_enqueued. by rewrite Eqγi. }
            apply (bsq_cons_enq_non_zero _ CON3 _ _ _ EqeV Eqev).
          - destruct (HENQ2 e vi Vi) as [(ev & EqeV & Eqev & _) _].
            { exists idx, Mi. eapply get_enqInfo_L_dequeued. by rewrite Eqγi. }
            apply (bsq_cons_enq_non_zero _ CON3 _ _ _ EqeV Eqev). }
        iExists ti0, LVs0', t1', LVs1'. rewrite shift_lblock_assoc Eqζi2 EqSH.
        iFrame "Oi". iSplitR; first by iPureIntro.
        iApply (view_at_mono with "OSi"); [done|].
        destruct si as [| | |[[ve Me][Ve e]] Vd]; [done..|].
        iIntros "[$ %SE]". iPureIntro. destruct SE as (SE & LeVe & LeVd).
        do 2 (split; [done|]). clear -LeVe LeVd EqLVs LeVr3'.
        destruct EqLVs as [(_ & EqLVs1 & InVr3)|[_ EqLVs1]]; [|by rewrite EqLVs1].
        rewrite EqLVs1. apply Forall_app. split; [done|].
        apply Forall_singleton. etrans; [|exact LeVr3'].
        apply elem_of_cons in InVr3 as [->|InVr3];[done|].
        rewrite ->Forall_forall in LeVd. by apply LeVd.
      - rewrite list_insert_id; [|done]. by iFrame "OLs". }
    iIntros "!> _".
    wp_let. wp_op. wp_if. wp_op.
    have Ge1: (1 ≤ k)%nat by clear -NEqk0; lia.
    rewrite -(Nat2Z.inj_sub _ 1 Ge1).
    (* apply IH2 to continue the internal loop *)
    iApply ("IH2" with "[%] AU").
    { clear -Lek Ge1. lia. } iClear "IH2".

    iAssert (⌜ set_in_bound (Mx' ∪ M') E3 ⌝)%I as %SubMM'.
    { iDestruct "SEx''" as "[[%SubM' _] _]". iPureIntro.
      apply set_in_bound_union; [|done]. by eapply set_in_bound_mono. }

    iExists (Mx' ∪ M'), G3, T2. iFrame "ST2". iSplit; last iSplit; last iSplit.
    { iPureIntro. split; [set_solver+SubMx'|done]. }
    { iDestruct "Gs3" as "[$ _]". rewrite -SeenLogview_union'. iFrame "SLgM'".
      iDestruct "Gsx'" as "[_ SLM]". by iApply (SeenLogview_map_mono with "SLM"). }
    { rewrite -SeenEnqueueds_union'.
      iDestruct (SeenEnqueueds_mono with "SEx'") as "$"; [done..|].
      iApply (SeenEnqueueds_mono with "SEx''"); [clear;lia|done..]. }

    iDestruct "SEx'" as "[[_ %ENTEx] _]".

    iPureIntro.
    intros i e Lti InMe%elem_of_union Eqei.
    destruct InMe as [InM|InM']; last first.
    { apply EqInM in InM'; clear EqInM. clear -InM' Eqγi HDEQ2 CON3.
      destruct InM' as (Ltti1 & v & Me & Ve & Vd & ->).
      destruct (HDEQ2 e) as [Inso _]. rewrite ->elem_of_list_fmap in Inso.
      destruct Inso as [[e' d] [Eqe' Ind%elem_of_elements]].
      - exists idx, v, Ve, Me, Vd. by rewrite Eqγi.
      - simpl in Eqe'; subst e'. exists d. by rewrite -(bsq_cons_so_com _ CON3). }

    have Eqeix : Tx !! e = Some i.
    { apply (enq_map_enqueued_mono_inv _ _ ENTEx ENTE3 SubTx SubEx); [|done].
      by apply SubMEx', InM. }
    have CASEi: (i < idx)%nat ∨ i = idx. { clear -Lti Ge1. lia. } clear Lti.
    destruct CASEi as [Lti| ->].
    { destruct (SEDx i e Lti InM) as (d & InGc); [done|].
      exists d. by apply (graph_sqsubseteq_com _ _ SubGx _ InGc). }

    rewrite decide_True in Hζi; last by exists e.
    destruct Hζi as (ti & vi & Vi & Eqti & Gt0i).
    assert (Eqti' := lookup_weaken ζi ζi2 _ _ Eqti ltac:(by etrans)).
    rewrite Eqζi2 in Eqti'.
    have Leti2 : (ti ≤ ti2)%positive. { apply MAXti2. by eexists. }
    rewrite lookup_insert_ne in Eqti'; [|clear -Leti2; lia].

    apply HENQe2 in Eqei as (vi' & Mi & Vi' & [γi' Eqidx]%get_enqInfo_L_Some).
    rewrite Eqγi in Eqidx.
    destruct Eqidx as [Eqidx|[Vd Eqidx]]; inversion Eqidx; clear Eqidx; subst γi' si.
    - exfalso. simpl in Eqti'. simpl in Eqvi2.
      clear -Eqti' Eqvi2 Gt0i Fti Leti2.
      case (decide (ti = ti1)) => ?; last first.
      { rewrite lookup_insert_ne in Eqti'; [|done].
        apply toSlotHist0_lookup_Some in Eqti' as (_ & _ &  Eq0 & _).
        inversion Eq0; subst vi; lia. }
      subst ti. rewrite lookup_insert in Eqti'.
      inversion Eqti'; clear Eqti'; subst vi' Vi'.
      case (decide (ti1 = ti2)) => ?.
      { subst ti1. rewrite lookup_insert in Eqvi2. inversion Eqvi2; subst vi; lia. }
      rewrite lookup_insert_ne in Eqvi2; [|done].
      apply toSlotHist0_lookup_Some in Eqvi2 as (Lei0 & Lti2 & _).
      rewrite /pos_add_nat in Fti. lia.
    - destruct (HDEQ2 e) as [Ine _]. rewrite ->elem_of_list_fmap in Ine.
      destruct Ine as ([e1 d2] & Eqe1 & Ined1%elem_of_elements).
      { exists idx. do 4 eexists. by rewrite Eqγi. }
      simpl in Eqe1. subst e1. rewrite -(bsq_cons_so_com _ CON3). by exists d2.
  } iClear "IH2".

  destruct (toSlotHist_lookup_Some_None Fti NEqz2 Eqvi2 FRti2)
    as (Leti2 & -> & enqId & Me & ->).
  have Eqeidx : get_enqInfo_L L2 idx = Some (z2, Me, (Vr3, enqId)).
  { eapply get_enqInfo_L_enqueued. by rewrite Eqγi. }
  have EqeT2 : T2 !! enqId = Some idx.
  { apply HENQe2. by do 3 eexists. }

  iDestruct "OSi" as "[#SEs %SE]". assert (SE':=SE).
  destruct SE' as (eV & Eqee & EqeVv & EqeVV). rewrite view_at_view_at.
  iAssert (⌜ eV.(ge_view).(dv_comm) ⊑ Vr3 ∧
            eV.(ge_lview) = {[enqId]} ∪ Me ∧ enqId ∉ Me ⌝ ∧
            @{Vr3} (SeenLogview E3 eV.(ge_lview)))%I
    with "[SLM]" as ((LeVe & EqeVM & NInMe)) "#SLeV".
  { iDestruct "SEs" as "[? SEs']".
    iSpecialize ("SEs'" $! enqId z2 eV.(ge_view) eV.(ge_lview) with "[%]").
    { split; [set_solver-|]. rewrite Eqee -EqeVv. clear; by destruct eV. }
    iDestruct "SEs'" as "(%LeVr & SL & SEs')". iSplitL.
    - iDestruct "SEs'" as (i γi' Mi Vi (Lei & EqT2 & EqeV & NIe)) "[SEs ?]".
      rewrite EqeT2 in EqT2. inversion EqT2; clear EqT2; subst i.
      rewrite (view_at_objective_iff (slot_enqueued _ _ _ _ _ _)).
      iDestruct (slots_master_slot_enqueued_agree_L_get_enqInfo with "SLM SEs") as %[_ Eq2].
      iPureIntro. rewrite Eqeidx in Eq2. clear -LeVr EqeV NIe Eq2.
      inversion Eq2. by subst Vi Mi.
    - rewrite view_at_view_at. iFrame "SL". }
  assert (GtZ := bsq_cons_enq_non_zero _ CON3 _ _ _ Eqee EqeVv).

  have SubM : set_in_bound Mx' E3.
  { clear - SubMEx' SubEx. by eapply set_in_bound_mono. }

  iAssert (⌜ Me ⊆ Mx' ⌝)%I with "[SLM]" as %SubMe.
  { iDestruct ("ALLx" $! idx with "[%]") as (Me' SubMe') "SLMe".
    - clear- NEqk0 Lek. rewrite /idx. lia.
    - iDestruct (slots_master_slot_pre_enqueued_agree with "SLM SLMe") as %Eq.
      + by rewrite lookup_map_seq_0 Eqγi.
      + iPureIntro. rewrite Eq. by etrans. }

  set V' := V3.
  have bLeV2' : bool_decide (V20 ⊑ V') by eapply bool_decide_unpack; eauto.
  set Vdeq : dataView := mkDView V20 V' Vw3 bLeV2'.
  have SubVin : eV.(ge_view).(dv_in) ⊑ Vdeq.(dv_comm) by rewrite dv_in_com /= LeVe.

  assert (GIP := graph_insert_edge_props_base _ _ _ (Deq z2) Mx' Vdeq
                    Eqee SubM EGCs3 SubVin).
  destruct GIP as [b' [deqId M' egV' G' [NEqid _] LeG' [SubM' SubeV'] SUB'
                      [InEnq' InDeq'] FRde EGCs']].
  set Lted := lookup_lt_Some (Es G3) enqId eV Eqee.
  assert (EqG' := graph_insert_edge_eq enqId egV' G3 b').
  rewrite -/deqId -/G' in EqG'. destruct EqG' as (_ & EqEs' & EqSo' & EqCo').
  set E' := G'.(Es).
  have LeE' : E3 ⊑ E' by apply LeG'.

  have SubM1 : M1 ⊑ M'.
  { clear -SubM' SubM1x SubMx'. etrans; [exact SubM1x|]. etrans; [exact SubMx'|done]. }
  have FRMx : deqId ∉ M1. { clear -SubM1x FRde SubMx'. set_solver. }

  have UEq: (∀ id, (enqId, id) ∉ G3.(so)).
  { clear -HDEQ2 HENQe2 EqeT2 Eqγi. intros ed Ine.
    have INenq: enqId ∈ (elements G3.(so)).*1.
    { apply elem_of_list_fmap. exists (enqId, ed). by rewrite elem_of_elements. }
    apply HDEQ2 in INenq as (i' & v' & V' & M' & Vd' & Eqi').
    assert (i' = idx) as ->.
    { apply get_enqInfo_L_dequeued in Eqi'.
      destruct (HENQe2 enqId i') as [Eq1 _]. specialize (Eq1 ltac:(by do 3 eexists)).
      rewrite EqeT2 in Eq1. by inversion Eq1. }
    by rewrite Eqγi in Eqi'. }

  assert (NEdeq: ∀ e' d', (e', d') ∈ G3.(com) → e' ≠ deqId ∧ d' ≠ deqId).
  { clear. move => ?? /gcons_com_included [/=]. lia. }

  assert (FReT : ∀ i e, T2 !! e = Some i → e ≠ deqId).
  { clear -ENTE3. intros i e EqT ->.
    destruct (ENTE3 deqId) as [(eV & v & Eqe & _) _]. { by eexists. }
    apply lookup_lt_Some in Eqe. lia. }
  assert (FRe' : ∀ i e, get_enqInfo_L L2 i = Some e → einf_evt e ≠ deqId).
  { rewrite /einf_evt /= => i e INL2 Eqe. destruct e as [[vi Mi][Vi e]].
    apply (FReT i e); [|done]. apply HENQe2. by do 3 eexists. }

  set L' :=  (<[idx:=(γi, SlotDequeued (z2,Me,(Vr3, enqId)) Vw3)]> L2).

  iDestruct "SED" as "[Gsx' SED]".
  iAssert (⌜enq_map_enqueued Tx Ex⌝)%I with "[SED]" as %ENTEx.
  { by iDestruct "SED" as "[[_ %] _]". }
  (* TODO: might not be needed *)
  have SED: ∀ i e, (i < idx)%nat → T2 !! e = Some i → e ∈ Mx' → ∃ d, (e, d) ∈ Gx.(com).
  { intros i e Lti Eqi Ine.
    apply (SEDx _ _ Lti Ine), (enq_map_enqueued_mono_inv _ _ ENTEx ENTE3 SubTx SubEx);
      [|done]. by apply SubMEx', Ine. }

  have QP' : QueueProps (Pos.to_nat sz) n2 L' T2 G'.
  { rewrite -EqL2 in Ltidx.
    split.
    - by rewrite insert_length.
    - intros i. case (decide (i = idx)) => [->|?].
      + rewrite list_lookup_insert // /= HUN2 Eqγi /=. clear; naive_solver.
      + by rewrite list_lookup_insert_ne.
    - intros e. rewrite EqSo' elements_union_singleton; last by apply UEq.
      rewrite fmap_cons elem_of_cons /= -HDEQ2. clear -Ltidx Eqγi. split.
      + intros (i & vi & Vi & Mi & Vdi & Eqi). case (decide (i = idx)) => ?.
        * subst i. left. rewrite list_lookup_insert /= in Eqi; [|done].
          by simplify_eq.
        * right. rewrite list_lookup_insert_ne in Eqi; [|done].
          by exists i, vi, Vi, Mi, Vdi.
      + intros [->|(i & vi & Vi & Mi & Vdi & Eqi)].
        * exists idx, z2, Vr3, Me, Vw3. by rewrite list_lookup_insert.
        * exists i, vi, Vi, Mi, Vdi. rewrite list_lookup_insert_ne; [done|].
          intros ->. by rewrite Eqγi in Eqi.
    - intros e ve Ve. case (decide (e = deqId)) => Eqe.
      + subst e. rewrite lookup_app_1_eq. split; last by (clear; naive_solver).
        intros (i & Mi & Eqi). rewrite get_enqInfo_L_insert_dequeue in Eqi; [|done].
        exfalso. by apply FRe' in Eqi.
      + rewrite lookup_app_1_ne; [|done]. rewrite -HENQ2.
        apply exist_proper => i. by rewrite get_enqInfo_L_insert_dequeue.
    - intros e i. by rewrite -HENQe2 get_enqInfo_L_insert_dequeue.
    - intros i1 i2 e1 e2 eV2 Eqe1 Eqe2.
      rewrite lookup_app_1_ne; last by apply FReT in Eqe2.
      by apply (HEORD2 _ _ _ _ _ Eqe1 Eqe2).
    - intros i1 i2 e1 e2 d2 dV2 Eqi1 Eqi2 Lei12.
      rewrite EqCo' elem_of_union elem_of_singleton.
      intros [Eqed|InG3]; last first.
      { destruct (NEdeq _ _ InG3) as []. rewrite lookup_app_1_ne; [|done].
        intros Eqd2 IndV2.
        destruct (HDORD2 _ _ _ _ _ _ Eqi1 Eqi2 Lei12 InG3 Eqd2 IndV2) as [d1 InG3'].
        exists d1. rewrite elem_of_union; by right. }
      inversion Eqed as [Eqen2 ]; clear Eqed; subst e2 d2. rewrite lookup_app_1_eq.
      intros EqdV2; inversion EqdV2; clear EqdV2; subst dV2. simpl.
      rewrite EqeT2 in Eqi2. inversion Eqi2; clear Eqi2; subst i2.
      apply Nat.le_lteq in Lei12 as [Lti12| ->]; last first.
      { intros _. exists deqId. rewrite (HINJ2 _ _ _ Eqi1 EqeT2). set_solver-. }
      rewrite /= {1}/M' EqeVM !elem_of_union 2!elem_of_singleton.
      intros [InMx'|[EqD|[EqE|Inenq]]]; [|by apply FReT in Eqi1| |].
      + destruct (SED _ _ Lti12 Eqi1 InMx') as (d1 & InGx1).
        exists d1. clear -InGx1 SubGx. rewrite elem_of_union; right.
        by apply (graph_sqsubseteq_com _ _ SubGx _ InGx1).
      + subst e1. exfalso. rewrite EqeT2 in Eqi1. clear -Lti12 Eqi1.
        inversion Eqi1; subst. lia.
      + destruct (SED _ _ Lti12 Eqi1)  as (d1 & InGx1); [by apply SubMe|].
        exists d1. clear -InGx1 SubGx. rewrite elem_of_union; right.
        by apply (graph_sqsubseteq_com _ _ SubGx _ InGx1). }

  assert (ENTE' := QueueProps_enq_map_enqueued QP').

  iAssert (⌜∀ e v V lV,
            e ∈ eV.(ge_lview) ∧ E' !! e = Some (mkGraphEvent (Enq v) V lV) →
            ∃ i, (i ≤ idx)%nat ∧ T2 !! e = Some i ⌝)%I
    with "[SEs]" as %SEnq.
  { iRevert "SEs". iIntros "{#} SEs". clear -QP' LeE' EqeVM ENTE'.
    rewrite (SeenEnqueueds_mono idx E'); [|done..].
    iDestruct "SEs" as "[%SubM' #SEs]". rewrite -EqeVM.
    iIntros (e v V lV [InM' Eqe]).
    iDestruct ("SEs" $! e v V lV with "[%//]") as "(_ & _ & SE)".
    iDestruct "SE" as (i ? Mi Vi (Lei &?&?&?)) "_". iPureIntro. by eexists. }

  have CON6' : G'.(so) = G'.(com).
  { rewrite EqSo' EqCo'. f_equal. apply (bsq_cons_so_com _ CON3). }
  have CON' : WeakQueueConsistent G'.
  { destruct CON3 as [CONW CONRel CONAcq [CONNZ CON2 [CON3a CON3b] CON4
                      CON5 CON6 CON7a CON7b]].
    constructor;[..|constructor].
    - apply graph_insert_event_is_writing; [done|]. simpl. intros _ ->.
        apply NEqV2. by apply : (anti_symm (⊑)).
    - clear -CONRel. apply graph_insert_event_is_releasing; [done|].
      simpl; intros []; congruence.
    - clear -CONAcq LeVw3. by apply graph_insert_event_is_acquiring.
    - intros ??? [Eq1|[-> <-]]%lookup_app_1; [by apply (CONNZ _ _ _ Eq1)|done].
    - (* 2 *)
      move => e1 e2 /elem_of_union [/elem_of_singleton|InCom].
      + inversion 1. subst e1 e2. split; [done|].
        exists eV. eexists. exists z2.
        rewrite (prefix_lookup_Some _ _ _ _ Eqee LeE')lookup_app_1_eq /= EqeVv /=.
        do 4 (split; [done|]). etrans; [exact LeVe|exact LeVr3].
      + destruct (NEdeq _ _ InCom) as []. do 2 (rewrite lookup_app_1_ne; [|done]).
        by apply CON2.
    - split.
      + (* 3a *)
        intros [e1 d1] [e2 d2]. rewrite 2!elem_of_union 2!elem_of_singleton /=.
        move => [[-> ->]|InG1] [[-> ->]|InG2] //.
        * intros ?. subst e2. exfalso. move : InG2. rewrite -CON6. by apply UEq.
        * intros ?. subst e1. exfalso. move : InG1. rewrite -CON6. by apply UEq.
        * move : InG1 InG2. by apply CON3a.
      + (* 3b *)
        intros [e1 d1] [e2 d2]. rewrite 2!elem_of_union 2!elem_of_singleton /=.
        move => [[-> ->]|InG1] [[-> ->]|InG2] //.
        * intros <-. exfalso. apply gcons_com_included in InG2 as [_ Eql].
          clear -Eql. simpl in Eql; lia.
        * intros ->. exfalso. apply gcons_com_included in InG1 as [_ Eql].
          clear -Eql. simpl in Eql; lia.
        * move : InG1 InG2. by apply CON3b.
    - (* 4 *)
      intros ??. rewrite /= elements_union_singleton; last first.
      { rewrite -CON6. by apply UEq. }
      intros [Eqe|[-> <-]]%lookup_app_1 MB.
      + intros NIne. apply (CON4 _ _ Eqe MB). intros NIn. apply NIne. by right.
      + clear. rewrite /= elem_of_cons. naive_solver.
    - (* 5 *)
      intros e eV' EqeV EqED ee ve eVe Eqe Eqve Inee.
      case (decide (deqId = e)) => ?.
      + subst e. rewrite lookup_app_1_eq in EqeV. inversion EqeV; clear EqeV.
        subst eV'. by exists deqId.
      + rewrite lookup_app_1_ne in EqeV; [|done].
        rewrite lookup_app_1_ne in Eqe; last first.
        { intros ->. apply (egcons_logview_closed _ EGCs3 _ _ EqeV),
                           lookup_lt_is_Some in Inee. clear -Inee; lia. }
        destruct (CON5 _ _ EqeV EqED ee ve eVe Eqe Eqve Inee) as (de & InG4 & In').
        exists de. split; [|done]. set_solver+InG4.
    - (* 6 *) done.
    - (* 7a MO *) clear -CON7a SUB'. by apply graph_insert_xo_eco.
    - (* 7b *)
      intros e1 eV1 v1 e2 d2 eV2 Eqe1 Eqv1. rewrite elem_of_union elem_of_singleton.
      intros [Eq2|In2].
      + inversion Eq2; clear Eq2; subst e2 d2. rewrite lookup_app_1_ne; [|done].
        rewrite Eqee. intros EqeV2; inversion EqeV2; clear EqeV2; subst eV2.
        intros Ine1. rewrite lookup_app_1_ne in Eqe1; last first.
        { intros ->. apply (egcons_logview_closed _ EGCs3 _ _ Eqee),
                            lookup_lt_is_Some in Ine1. clear -Ine1; lia. }
        destruct (SEnq e1 v1 eV1.(ge_view) eV1.(ge_lview)) as (i & Lei & EqTe1).
        { split; [done|]. apply (prefix_lookup_Some E3); [|done]. rewrite Eqe1 -Eqv1.
          clear; by destruct eV1. }
        destruct (qu_deq_ordered _ _ _ _ _ QP' _ _ _ _
                    deqId (mkGraphEvent (Deq z2) Vdeq M')
                    EqTe1 EqeT2 Lei) as (d1 & InG1).
        { set_solver-. }
        { clear; by rewrite lookup_app_1_eq. }
        { rewrite /= /M'. set_solver+Ine1. }
        exists d1. split; [done|].
        intros dV1 Eqd1 NEqe. rewrite lookup_app_1_ne in Eqd1; last first.
        { intros ->. move : InG1. rewrite elem_of_union elem_of_singleton.
          intros [Eq1|[]%NEdeq]; [by inversion Eq1|done]. }
        intros IndV1.
        assert (LE := CON7a _ _ _ Eqd1 IndV1).
        assert (LT: (d1 < deqId)%nat).
        { move : Eqd1. apply lookup_lt_Some. } clear -LE LT. lia.
      + destruct (NEdeq _ _ In2). rewrite lookup_app_1_ne; [|done].
        intros Eqe2 Ine1. rewrite lookup_app_1_ne in Eqe1; last first.
        { intros ->. apply (egcons_logview_closed _ EGCs3 _ _ Eqe2),
                            lookup_lt_is_Some in Ine1. clear -Ine1; lia. }
        destruct (CON7b _ _ _ _ _ _ Eqe1 Eqv1 In2 Eqe2 Ine1) as (d1 & In1 & NIdV1).
        exists d1. split; [set_solver+In1|].
        destruct (NEdeq _ _ In1). rewrite lookup_app_1_ne; [|done]. exact NIdV1.
  }

  iMod (slots_master_set_dequeued_L Vw3 Eqγi EqeT2 with "SLM") as "[SLM sDe]".
  iCombine "GM GM'" as "GM".
  iMod (graph_master_update _ _ _ LeG' EGCs' with "GM") as "([GM GM'] & Gs')".

  assert (LeV22': V2' ⊑ V'). { clear -LeV22 LeV20 LeV2. rewrite /V'. solve_lat. }
  have SubE2' : Ex ⊑ E' by etrans.
  iAssert (@{V'} SeenLogview E' M')%I as "SL'".
  { rewrite -SeenLogview_union' -SeenLogview_insert'.
    iSplitL; last iSplitL; [..|by iFrame "SLeV"|done].
    iApply (view_at_mono with "Gsx"); [done|].
    iIntros "[_ SL]". by iApply (SeenLogview_map_mono with "SL"). }

  iAssert (@{V'} SeenEnqueueds γq (q >> buff) nx E' T2 M')%I with "[SED']" as "#SEs'".
  { rewrite -(SeenEnqueueds_union' Mx') -(SeenEnqueueds_union' {[deqId]}).
    iSplitL "SED'"; last iSplitR.
    - iApply (view_at_mono with "SED'"); [done|by apply SeenEnqueueds_mono].
    - iClear "#"; clear -ENTE'.
      iSplit. { iPureIntro. split; [|done]. intros ? ->%elem_of_singleton.
      rewrite lookup_app_1_eq. by eexists. }
      iIntros (e0 v0 V0 lV0 [In0 Eqe0]). exfalso.
      rewrite ->elem_of_singleton in In0. subst e0.
      rewrite lookup_app_1_eq in Eqe0. by inversion Eqe0.
    - iApply (view_at_mono with "SEs"); [done|].
      apply SeenEnqueueds_mono; [|done..|by rewrite EqeVM|done].
      clear -Lttb. rewrite /idx /nx. lia. }

  iMod (slots_masters_enq_slots_snap_fork with "SLM") as "[SLM #ST2]".

  rewrite bi.and_elim_r.
  iMod ("Close1" $! z2 V' G' enqId deqId (Enq z2) (Deq z2) Vdeq M'
        with "[GM' $sV3 Gs']") as "HΦ".
  { (* QueueInv *)
    iFrame (CON') "GM'". iSplitL; last first.
    { iPureIntro. do 2 (split; [done|]). split. { simpl; solve_lat. }
      split; [done|]. right. do 11 (split; [done|]). by exists eV. }
    (* Private Post *)
    iFrame "Gs' SL'". iExists γq. iFrame "QII".
    iExists γb, (Pos.to_nat tb - Pos.to_nat tb0)%nat, T2. iFrame "ST2". iSplitR.
    { iApply view_at_objective_iff. iApply (back_lb_get_lb with "blb'").
      clear -Lttb; lia. }
    iSplit. { iExists _; iFrame "sζb2'". iPureIntro. clear -Eqtb. by do 2 eexists. }
    iSplit. { iApply (view_at_mono with "SS'"); [|done].
              clear -LeV20 LeV2 LeV2'. rewrite /V'. solve_lat. }
    by  iFrame "SEs'". }

  (* re-establish the invariant *)
  iMod ("Close2" with "[-HΦ]") as "_".
  { iNext. iExists _. iFrame (CON') "GM".
    iExists γb, n2, _, T2. iFrame "bv SLM". iSplitR. { by iPureIntro. }
    iDestruct (view_join_to_view_at with "Oi") as (Vb') "[sVb' Oi]".
    iExists (Vb ⊔ Vb').
    iSplitL "Ob". { rewrite (own_back_mono LeE'); [by iFrame "Ob"|done..]. }

    iDestruct (view_at_mono_2 _ (Vb ⊔ Vb') with "OLs") as "OLs"; [solve_lat|].
    rewrite Eqζi2.
    iApply ("OLs" $! (SlotDequeued (z2, Me, (Vr3, enqId)) Vw3) E' with "[%//] [Oi]").
    iExists ti0, LVsi0, ti1, []. rewrite shift_lblock_assoc. iSplitL "Oi".
    { rewrite /= toSlotHist0_singleton -insert_union_singleton_l. by iFrame "Oi". }
    iSplitR; [by iPureIntro|]. iSplitL; last iPureIntro.
    - iRevert "SEs". iClear "#". rewrite view_at_view_at. iIntros "#SEs".
      iApply (view_at_mono with "SEs"); [done|]. by apply SeenEnqueueds_mono.
    - split; last split; [apply (seen_enqueued_mono LeE' SE)|done|constructor]. }

  iIntros "!> _".
  wp_let. wp_op. rewrite bool_decide_false; [|done].
  wp_if. by iApply "HΦ".
Qed.
End proof.

(** Both weak and strong HW queue implementations satisfy our weak spec, which
  is stronger than Yacovet's weak spec.
  However, unlike Yacovet, we don't have a proof that the strong HW queue has a
  linearization. *)
Definition hwqueue_impl (sz : positive) (b : bool)
  Σ `{!noprolG Σ, !hwqG Σ, !atomicG Σ} :
  weak_queue_spec Σ := {|
    spec_graph.QueueInv_Objective := QueueInv_objective;
    spec_graph.QueueInv_QueueConsistent := QueueInv_WeakQueueConsistent_instance;
    spec_graph.QueueInv_graph_master_acc := QueueInv_graph_master_acc_instance;
    spec_graph.QueueLocal_graph_snap := QueueLocal_graph_snap_instance (Pos.to_nat sz);
    spec_graph.QueueLocal_Persistent := QueueLocal_persistent (Pos.to_nat sz);
    spec_graph.new_queue_spec := new_queue_spec sz;
    spec_graph.enqueue_spec := atom_enqueue sz;
    spec_graph.dequeue_spec := atom_dequeue sz b;
  |}.
