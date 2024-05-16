From iris.algebra Require Import auth gset gmap agree.
From iris.algebra Require Import lib.mono_list.
From iris.algebra.lib Require Import dfrac_agree.
From iris.proofmode Require Import tactics.

From gpfsl.base_logic Require Import meta_data.
From gpfsl.algebra Require Import to_agree.
From gpfsl.logic Require Import logatom atomics invariants.

From gpfsl.examples Require Import list_helper.

From gpfsl.logic Require Import repeat_loop new_delete.
From gpfsl.examples Require Import map_seq.
From gpfsl.examples.queue Require Import spec_abs_graph code_ms.

Require Import iris.prelude.options.

(** Prove that Michael-Scott Queue satisfies the logically atomic, history-based
  specifications *)

#[local] Notation link := 0%nat (only parsing).
#[local] Notation data := 1%nat (only parsing).
#[local] Notation head := 0%nat (only parsing).
#[local] Notation tail := 1%nat (only parsing).

#[local] Notation event_list := (event_list qevent).
#[local] Notation graph_event := (graph_event qevent).
#[local] Notation graph := (graph qevent).

(* a logical node, implemented as the ghost name of the `AtomicPtsto` of the
  location of the node. *)
Definition lnode := gname.
(* a node is a pair (η, n) of the logical name and physical location of the node *)
Definition node : Type := (lnode * loc).

Implicit Types (l: loc) (tid: thread_id) (Q : queue) (G: graph) (γ: gname) (η: lnode) (M: logView).

(* State of the link field: Null or Linked to the node (η,n) *)
Definition LinkState: Type := option node.
#[local] Notation Null := (None : LinkState).
#[local] Notation Linked η n := (Some (η, n) : LinkState).

(**** GHOST STATE CONSTRUCTION -----------------------------------------------*)
(** The CMRA & functor we need. *)
(* a persistent map of from logical nodes to event ids. *)
#[local] Notation msq_qmapUR' := (agreeMR gname event_id).
#[local] Notation msq_qmapUR := (authUR msq_qmapUR').
(* an append-only list of nodes *)
#[local] Notation msq_linkUR := (mono_listUR (leibnizO node)).
#[local] Notation msq_queueR := (prodR (prodUR msq_linkUR msq_linkUR) msq_qmapUR).
(* abstract state *)
#[local] Notation queueR := (dfrac_agreeR (leibnizO queue)).

Class msqueueG Σ := MSQueueG {
  msq_graphG : inG Σ (graphR qevent);
  msq_queueG : inG Σ msq_queueR;
  msq_absG : inG Σ queueR;
}.

Definition msqueueΣ : gFunctors :=
  #[GFunctor (graphR qevent); GFunctor msq_queueR; GFunctor queueR].

Global Instance subG_msqueueΣ {Σ} : subG msqueueΣ Σ → msqueueG Σ.
Proof. solve_inG. Qed.

(**
  + T tracks which logical node points to which enqueue event, in the form of
    η |-> e, which says that η leads to the node that is enqueued as event e.

  + L tracks the linked list itself, including any node that has ever been
    enqueued. L tracks the logical + physical nodes, that is a pair of (η,n)
    where `n` is the physical location of the node, and `η` is the ghost name
    of the atomic ptsto of `n`.

  + D is a prefix of L that only contains nodes that have been dequeued.
*)
Implicit Types (T : gmap lnode event_id) (L D : list node).

(** Namespace for our internal invariant. See `QueueInternalInv`. *)
Definition msqN (N : namespace) (q: loc) := N .@ q.

(** Decidability of whether a logical node `η`:
  - has been observed by an enqueue event set `M` (indirectly through the
    lnode-event_id map `T`);
  - immediately follows `ηs` in L. *)
Definition enqueued_in L T (M : gset event_id) ηs : Prop :=
  ∃ η, η ∈ coimg T M ∧ adjacent_in ηs η (fst <$> L).

Local Instance enqueued_in_dec L T M ηs : Decision (enqueued_in L T M ηs).
Proof. intros. apply set_Exists_dec => η. apply _. Qed.

Lemma enqueued_in_choice L T (M : gset event_id) ηs :
  { η | η ∈ coimg T M ∧ adjacent_in ηs η (fst <$> L) } +
  { ∀ η, η ∈ coimg T M → adjacent_in ηs η (fst <$> L) → False }.
Proof.
  case (decide (enqueued_in L T M ηs)) => [In|NIn].
  - left. apply choice; [solve_decision|done].
  - right. intros η Inη Sub. apply NIn. by exists η.
Qed.

(* The lnode-event_id map is in sync with the event map w.r.t. enqueue events. *)
Definition EM_equiv T (E : event_list) : Prop :=
  ∀ e, (∃ η, T !! η = Some e) ↔ (∃ v, ge_event <$> E !! e = Some $ Enq v).

(* Pure Coq properties of the Queue *)
Record QueueProps Q G T η s D L : Prop := mkQueueProps {
  qu_no_dup : NoDup (((η, s) :: D ++ L).*1) ;
  (* NoDup (CL.*2): this is implied by own_nodes *)
  qu_enqueued : (* T only tracks enqueues *)
    dom T ≡ list_to_set ((D ++ L).*1) ;
  qu_enq_event : EM_equiv T G.(Es) ;
  qu_enq_inj : (* T is also injective *)
    ∀ η1 η2 eid, T !! η1 = Some eid → T !! η2 = Some eid → η1 = η2 ;
  qu_dequeued : (* D only contains nodes that have been dequeued *)
    ∀ η eid, T !! η = Some eid → ((η ∈ D.*1) ↔ eid ∈ (elements G.(so)).*1) ;
  qu_enq_mo_ord :
    ∀ η1 η2 e1 e2, list_before ((D ++ L).*1) η1 η2 → T !! η1 = Some e1 →
    T !! η2 = Some e2 → (e1 ≤ e2)%nat ;
  (* Later enqueues must have observed earlier enqueues. This is a very
    strong synchronization property that may not hold for all queue
    implementations. *)
  qu_enq_hb_ord :
    ∀ η1 η2 e1 e2 eV2, list_before ((D ++ L).*1) η1 η2 →
      T !! η1 = Some e1 → T !! η2 = Some e2 → G.(Es) !! e2 = Some eV2 →
      e1 ∈ eV2.(ge_lview) ;
  qu_abs :
    Forall2 (λ '(v, V) '(η, _), ∃ e eV,
      T !! η = Some e ∧ G.(Es) !! e = Some eV ∧
      eV.(ge_event) = Enq v ∧ eV.(ge_view).(dv_comm) = V) Q L
}.

(** The state of the Head pointer *)
(* History of Head is a contiguous list of writes, because Head is CAS-only *)
Definition toHeadHist' (start : time) (LV : list (loc * view)) : absHist :=
  map_seqP start ((λ lv, (#(LitLoc lv.1),lv.2)) <$> LV).
Definition toHeadHist (start : time) D (Vs : list view) : absHist :=
  toHeadHist' start (zip (snd <$> D) Vs).

Definition SyncEnqueues (E: event_list) M : Prop :=
  ∀ e v V Mv, e ∈ M → E !! e = Some (mkGraphEvent (Enq v) V Mv) → Mv ⊆ M.

(* A bool mask to identify which node has been dequeued *)
Definition dequeue_mask (lenD lenL : nat) : list bool :=
  (repeat true lenD) ++ (repeat false lenL).

(* A next node mask to link the nodes in a list together *)
Definition next_nodes L : list LinkState :=
  match L with
  | [] => []
  | _ :: L' => (Some <$> L') ++ [None]
  end.


Lemma SyncEnqueues_mono E E' M :
  set_in_bound M E → E ⊑ E' → SyncEnqueues E M → SyncEnqueues E' M.
Proof.
  intros SubM SubE SE e v V Mv InM Eqe.
  apply (SE e v V Mv InM), (prefix_lookup_inv _ _ _ _ Eqe); [|done].
  by apply SubM.
Qed.

Lemma SyncEnqueues_union E M1 M2 :
  SyncEnqueues E M1 → SyncEnqueues E M2 → SyncEnqueues E (M1 ∪ M2).
Proof.
  intros SE1 SE2 e v V Mv [InM|InM]%elem_of_union.
  - intros ?%(SE1 _ _ _ _ InM). set_solver.
  - intros ?%(SE2 _ _ _ _ InM). set_solver.
Qed.

Lemma dequeue_mask_length (lenD lenL : nat) :
  length (dequeue_mask lenD lenL) = (lenD + lenL)%nat.
Proof. by rewrite app_length 2!repeat_length. Qed.

Lemma dequeue_mask_append (lenD lenL : nat) :
  dequeue_mask lenD (S lenL) = dequeue_mask lenD lenL ++ [false].
Proof. rewrite /dequeue_mask -app_assoc. f_equal. by apply repeat_cons. Qed.

Lemma dequeue_mask_lookup_Some (lenD lenL : nat) i d :
  dequeue_mask lenD lenL !! i = Some d →
  ((i < lenD)%nat ∧ d = true ∨ (lenD ≤ i < lenD + lenL)%nat ∧ d = false).
Proof.
  intros Eqi.
  have LtL := lookup_lt_Some _ _ _ Eqi.
  rewrite dequeue_mask_length in LtL.
  destruct (Nat.lt_ge_cases i lenD) as [LtD|LeD].
  - left. split; [done|].
    move : Eqi. rewrite /dequeue_mask lookup_app_l.
    + by apply repeat_lookup_Some.
    + by rewrite repeat_length.
  - right. split; [done|].
    move : Eqi. rewrite /dequeue_mask lookup_app_r.
    + by apply repeat_lookup_Some.
    + by rewrite repeat_length.
Qed.

Lemma dequeue_mask_lookup_Some_l (lenD lenL : nat) i d :
  dequeue_mask lenD lenL !! i = Some d → (i < lenD)%nat → d = true.
Proof.
  intros Eqi%dequeue_mask_lookup_Some LtD.
  destruct Eqi as [[]|[[]]]; [done|lia].
Qed.

Lemma dequeue_mask_lookup_Some_r (lenD lenL : nat) i d :
  dequeue_mask lenD lenL !! i = Some d → (lenD ≤ i)%nat → d = false.
Proof.
  intros Eqi%dequeue_mask_lookup_Some LeD.
  destruct Eqi as [[]|[[]]]; [lia|done].
Qed.

Lemma dequeue_mask_lookup_Some' (lenD lenL : nat) i d :
  dequeue_mask lenD lenL !! i = Some d ↔
  (((i < lenD)%nat ∧ d = true ∨ (lenD ≤ i < lenD + lenL)%nat ∧ d = false)).
Proof.
  split; [apply dequeue_mask_lookup_Some|]. intros Eq.
  destruct (lookup_lt_is_Some_2 (dequeue_mask lenD lenL) i) as [d' Eqd'].
  { rewrite dequeue_mask_length. lia. }
  rewrite Eqd'. f_equal.
  destruct Eq as [[]|[[]]]; subst d.
  - eapply dequeue_mask_lookup_Some_l; eauto.
  - eapply dequeue_mask_lookup_Some_r; eauto.
Qed.

Lemma next_nodes_lookup_Some L i n :
  next_nodes L !! i = Some (Some n) ↔ L !! (i+1)%nat = Some n.
Proof.
  destruct L as [|s L]; simpl; [done|].
  rewrite Nat.add_1_r /=.
  case (decide (i < length (Some <$> L))%nat) => EqL.
  - rewrite lookup_app_l // list_lookup_fmap.
    destruct (L !! i); [simpl; naive_solver|done].
  - apply Nat.nlt_ge in EqL.
    rewrite lookup_app_r; [|done].
    rewrite (lookup_ge_None_2 L); [|by rewrite fmap_length in EqL].
    split; [|done].
    by intros ?%elem_of_list_lookup_2%elem_of_list_singleton.
Qed.

Lemma next_nodes_lookup_None L i :
  next_nodes L !! i = Some None → (0 < length L)%nat ∧ i = (length L - 1)%nat.
Proof.
  rewrite /next_nodes. destruct L; [done|].
  rewrite /= Nat.sub_0_r. intros Eqi. split; [lia|].
  move : (lookup_lt_Some _ _ _ Eqi).
  rewrite app_length /= fmap_length Nat.add_1_r => /Nat.lt_succ_r Lti.
  case (decide (length L ≤ i)%nat) => [Le|/Nat.nle_gt Lt].
  - by apply : anti_symm.
  - exfalso.
    rewrite lookup_app_l in Eqi; [|by rewrite fmap_length].
    move : Eqi. rewrite list_lookup_fmap.
    by apply lookup_lt_is_Some_2 in Lt as [? ->].
Qed.

Lemma next_nodes_app_2 L x y :
  ∃ (L' : list LinkState),
    next_nodes ((L ++ [x]) ++ [y]) = (L' ++ [Some y]) ++ [None] ∧
    next_nodes (L ++ [x]) = L' ++ [None] ∧
    length L = length L'.
Proof.
  rewrite /next_nodes. destruct L as [|z L]; simpl.
  - exists []. by simplify_list_eq.
  - exists (Some <$> L ++ [x]). simplify_list_eq.
    by rewrite app_length /= fmap_length Nat.add_1_r.
Qed.

Lemma infos_next_lookup L (dms : list bool) d i ηs :
  let infos := zip (next_nodes L) dms in
    infos !! i = Some (ηs, d) ->
    next_nodes L !! i = Some ηs ∧
    dms !! i = Some d ∧
    if ηs is Some ηn' then L !! (i + 1)%nat = Some ηn' else True.
Proof.
  intros infos Eq.
  apply lookup_zip_with_Some in Eq as (ηs'&d'&Eq&Eq1&Eq2). inversion Eq.
  subst ηs' d'. do 2 (split; [done|]).
  destruct ηs as [ηn'|]; [|done].
  by apply next_nodes_lookup_Some in Eq1.
Qed.

Lemma infos_dequeue ηs s D L η n :
  let CL := (ηs, s) :: D ++ (η, n) :: L in
  let lenD := length D in
  let lenL :=  S (length ((η, n) :: L)) in
  let lenD' := length (D ++ [(η,n)]) in
  let lenL' := S (length L) in
  let infos := zip (next_nodes CL) (dequeue_mask lenD lenL) in
  let infos' := zip (next_nodes CL) (dequeue_mask lenD' lenL') in
  ∀ (EqL: length CL = length infos),
  (∃ η' n', CL !! lenD = Some (η', n')) ∧
  infos !! lenD = Some (Some (η, n), false) ∧
  infos' = <[lenD:=(Some (η, n), true)]> infos.
Proof.
  intros.
  have EqLD' : (lenD' + lenL' = lenD + lenL)%nat.
  { rewrite /lenD' /lenL' /lenD /lenL app_length /=. clear.
    by rewrite Nat.add_1_r Nat.add_succ_comm. }
  have EqLI: length infos = length infos'.
  { rewrite 2!zip_with_length. f_equal. by rewrite 2!dequeue_mask_length. }
  have EqL' : length CL = length infos' by rewrite EqL.
  have Eqη : CL !! length ((ηs, s) :: D) = Some (η,n).
  { rewrite /CL (lookup_app_r (_::_)); [|done]. by rewrite Nat.sub_diag. }
  have LtLCL: (lenD < length CL)%nat.
  { rewrite (app_length (_::_)) /= -Nat.add_succ_r.
    apply Nat.lt_add_pos_r. lia. }
  destruct (lookup_lt_is_Some_2  _ _ LtLCL) as [[η' n'] Eq'].
  split. { by eauto. }
  destruct (lookup_lt_is_Some_2 infos lenD) as [[ηn' d] Eq].
  { by rewrite -EqL. }
  destruct (infos_next_lookup _ _ _ _ _ Eq) as (EqNN & DQM & Eqηn').
  destruct ηn' as [ηn'|]; last first.
  { apply next_nodes_lookup_None in EqNN as [? EqN].
    exfalso. move : EqN. rewrite /CL (app_length (_::_)) /=. lia. }
  have ?: ηn' = (η,n).
  { rewrite /lenD cons_length in Eqη. rewrite Nat.add_1_r Eqη in Eqηn'.
    by inversion Eqηn'. } subst ηn'.
  have ?: d = false.
  { by apply (dequeue_mask_lookup_Some_r _ _ _ _ DQM). } subst d.
  split; [done|].
  have LtD: (lenD < lenD')%nat. { rewrite /lenD /lenD' app_length /=. lia. }
  have DQM' : dequeue_mask lenD' lenL' !! lenD = Some true.
  { destruct (lookup_lt_is_Some_2 (dequeue_mask lenD' lenL') lenD) as [d' Eqd'].
    - rewrite dequeue_mask_length. lia.
    - by rewrite -(dequeue_mask_lookup_Some_l _ _ _ _ Eqd'). }
  have EqIN' : infos' !! lenD = Some (Some (η, n), true).
  { by rewrite lookup_zip_with EqNN DQM' /=. }
  apply list_eq => i.
  case (decide (i = lenD)) => [->|NEq].
  { rewrite list_lookup_insert; [done|by rewrite -EqL]. }
  rewrite list_lookup_insert_ne; [|done].
  destruct (infos !! i) as [ηi|] eqn:Eqηi; last first.
  { apply lookup_ge_None. apply lookup_ge_None in Eqηi. by rewrite -EqLI. }
  apply lookup_zip_with_Some.
  apply lookup_zip_with_Some in Eqηi as (ηs' & d' & -> & EqN & EqD).
  exists ηs', d'. split; [done|]. split ;[done|].
  apply dequeue_mask_lookup_Some'.
  apply dequeue_mask_lookup_Some in EqD as [[Lti ?]|[[Lei Lti] ?]].
  - left. split; [|done]. rewrite /lenD' app_length /=. lia.
  - right. split; [|done]. split; [|by rewrite EqLD'].
    rewrite /lenD' app_length /=. lia.
Qed.


Lemma toHeadHist_lookup_Some DL Vs t0 t v V :
  (toHeadHist t0 DL Vs) !! t = Some (v, V) ↔
  (t0 ≤ t)%positive
  ∧ Vs !! (Pos.to_nat t - Pos.to_nat t0)%nat = Some V
  ∧ ∃ η (l : loc), v = #l ∧ DL !! (Pos.to_nat t - Pos.to_nat t0)%nat = Some (η, l).
Proof.
  rewrite lookup_map_seqP_Some. f_equiv.
  rewrite list_lookup_fmap fmap_Some.
  setoid_rewrite lookup_zip_with_Some.
  setoid_rewrite list_lookup_fmap.
  setoid_rewrite fmap_Some. split.
  - intros [[] [(? & ? & ? & ([] & ? & ?) & ?) ?]]. simpl in *. simplify_eq.
    naive_solver.
  - intros [? (η&l&?&?)]. simplify_eq.
    exists (l,V). naive_solver.
Qed.

Lemma toHeadHist_lookup_None DL Vs t0 t :
  length DL = length Vs →
  (toHeadHist t0 DL Vs) !! t = None ↔
  (t < t0)%positive ∨ (t0 +p (length DL) ≤ t)%positive.
Proof.
  intros EqL.
  by rewrite lookup_map_seqP_None fmap_length zip_with_length_l_eq fmap_length.
Qed.

Lemma toHeadHist_lookup_Some_is_comparable_loc t0 DL Vs t v l1 :
  fst <$> (toHeadHist t0 DL Vs) !! t = Some v →
  ∃ vl : lit, v = #vl ∧ lit_comparable l1 vl.
Proof.
  destruct ((toHeadHist t0 DL Vs) !! t) as [[v' V]|] eqn:Eqv; simpl; [|done].
  intros. simplify_eq.
  apply toHeadHist_lookup_Some in Eqv as (_ & _ & η & l & ? & _).
  subst v. exists l. split; [done|constructor].
Qed.

Lemma toHeadHist_insert t0 L Vs t V η (n : loc) :
  (Pos.to_nat t - Pos.to_nat t0)%nat = length L →
  (1 ≤ length L)%nat →
  length L = length Vs →
  <[t := (#n, V)]>(toHeadHist t0 L Vs) = toHeadHist t0 (L ++ [(η, n)]) (Vs ++ [V]).
Proof.
  intros Eq ? EqL. apply map_eq.
  intros i. case (decide (i = t)) => [->|?].
  - rewrite lookup_insert. symmetry.
    apply toHeadHist_lookup_Some. split; [lia|].
    rewrite Eq !lookup_app_r EqL // Nat.sub_diag /=. naive_solver.
  - rewrite lookup_insert_ne; [|done].
    destruct (toHeadHist t0 L Vs !! i) as [[vi Vi]|] eqn:Eqi; rewrite Eqi; symmetry.
    + apply toHeadHist_lookup_Some in Eqi as (? & Eq1 & η' & n' & -> & Eq2).
      apply toHeadHist_lookup_Some. split; [done|].
      rewrite (lookup_app_l_Some _ _ _ _ Eq1) (lookup_app_l_Some _ _ _ _ Eq2) /=.
      naive_solver.
    + have ?: length (L ++ [(η, n)]) = length (Vs ++ [V])
        by rewrite !app_length /= EqL.
      apply toHeadHist_lookup_None; [done|].
      apply toHeadHist_lookup_None in Eqi; [|done].
      destruct Eqi as [?|Eqi]; [by left|right].
      rewrite app_length /=. move : Eqi.
      rewrite Nat.add_1_r pos_add_succ_r_2.
      rewrite (_: t0 +p length L = t); [lia|]. rewrite -Eq /pos_add_nat; lia.
Qed.


(** * Ghost assertions *)
#[local] Notation LTGhost a := ((ε, a) : msq_queueR).
#[local] Notation LEGhost a := (((a, ε), ε) : msq_queueR).
#[local] Notation LDGhost a := (((ε, a), ε) : msq_queueR).

Section ghost.
Context `{!inG Σ msq_queueR, !inG Σ queueR}.
#[local] Notation iProp := (iProp Σ).
#[local] Notation vProp := (vProp Σ).

(* The logical snapshots of the queue *)
Definition LTM_snap  γq T : iProp := own γq (LTGhost (◯ (to_agreeM T))).
Definition LTM_snapv γq T : vProp := ⎡ LTM_snap γq T ⎤.
Definition LTM_ssnap  γq η e : iProp := LTM_snap γq {[η := e]}.
Definition LTM_ssnapv γq η e : vProp := ⎡ LTM_ssnap γq η e ⎤.

Definition LEL_snap  γq L : iProp :=
  own γq (LEGhost (◯ML (L : listO (leibnizO node)))).
Definition LEL_snapv γq L : vProp := ⎡ LEL_snap γq L ⎤.
Definition LDL_snap  γq D : iProp :=
  own γq (LDGhost (◯ML (D : listO (leibnizO node)))).
Definition LDL_snapv γq D : vProp := ⎡ LDL_snap γq D ⎤.

(* LTM_master and LEL_master track the enqueues *)
Definition LTM_auth T : msq_qmapUR := ● (to_agreeM T) ⋅ ◯ (to_agreeM T).
Definition LTM_master  γq T : iProp := own γq (LTGhost (LTM_auth T)).
Definition LTM_masterv γq T : vProp := ⎡ LTM_master γq T ⎤.
Definition LEL_master  γq L : iProp :=
  own γq (LEGhost (●ML ((L : listO (leibnizO node))))).
Definition LEL_masterv γq L : vProp := ⎡ LEL_master γq L ⎤.

(* LDL_master track the dequeues *)
Definition LDL_master  γq D : iProp :=
  own γq (LDGhost (●ML ((D : listO (leibnizO node))))).
Definition LDL_masterv γq D : vProp := ⎡ LDL_master γq D ⎤.

Definition Queue γa q Q : iProp := own γa (to_frac_agree q (Q : leibnizO queue)).
Definition Queuev γa q Q : vProp := ⎡ Queue γa q Q ⎤.
End ghost.

(** * THE INVARIANT AND LOCAL ASSERTIONS -------------------------------------*)
Section Interp.
Context `{!noprolG Σ, !msqueueG Σ, !atomicG Σ}.
Local Existing Instances msq_graphG msq_queueG msq_absG.

#[local] Notation iProp := (iProp Σ).
#[local] Notation vProp := (vProp Σ).

(** * LOCAL OBSERVATIONS ----------------------------------------*)

(* Asserts the observation of the enqueue event `eid` for value `v`. *)
Definition seen_enqueued_val E eid v V : vProp :=
  ∃ eV : graph_event,
    ⌜ eV.(ge_event) = Enq v ∧ eV.(ge_view).(dv_comm) = V ∧ SyncEnqueues E eV.(ge_lview) ⌝ ∗
    SeenEvent E eid eV.

(* Physical observation of the Link field. *)
Definition link_val η l V (v : lit) : vProp :=
  ∃ V' ζl, ⌜ V' ⊑ V ∧ ∃ t, ζl !! t = Some (#v, V') ⌝ ∧ l sn⊒{η} ζl.
(* Physical observation of Null for Link *)
Definition link_val_0 η l : vProp :=
  ∃ V ζl, ⌜ ∃ t, ζl !! t = Some (#0, V) ⌝ ∧ l sn⊒{η} ζl (* ∗ ⊒V *).

(* Observed that η'
  - has been enqueued with eid, v', and V,
  - and immediately follows η in L. *)
Definition seen_enqueued E T L η V eid η' v' : vProp :=
  ⌜adjacent_in η η' (fst <$> L) ∧ T !! η' = Some eid ⌝ ∗
  seen_enqueued_val E eid v' V.
(* Observed that (η',l')
  - has been enqueued with eid, v', and V,
  - and immediately follows (η,l) in L
  - and has been stored physically in (η,l). *)
Definition SeenLinked E T L η l V eid η' l' v' : vProp :=
  seen_enqueued E T L η V eid η' v' ∗ ⌜ (η,l) ∈ L ∧ (η',l') ∈ L ⌝ ∗ link_val η l V l'.

#[global] Instance SeenLinked_persistent E T L η l V eid η' l'  v' :
  Persistent (SeenLinked E T L η l V eid η' l' v') := _.

(* - If η is head of L (sentinnel node), then logically observes that η ∈ L.
   - Otherwise, physically observes some enqueue event eid for η, and logically
    observes that η immediately follows some η' in L. *)
Definition SeenEnqueuedLink E T L η V : vProp :=
  match L with
  | [] => False
  | (ηs, _) :: _ =>
      if decide (ηs = η) then (⊒V)%I
      else (∃ eid η' v, seen_enqueued E T L η' V eid η v)%I
  end.

#[global] Instance SeenEnqueuedLink_persistent E T L η V :
  Persistent (SeenEnqueuedLink E T L η V).
Proof. destruct L as [|[]]; [apply _|]. simpl. case decide => ?; apply _. Qed.
#[global] Instance SeenEnqueuedLink_timeless E T L η V :
  Timeless (SeenEnqueuedLink E T L η V).
Proof. destruct L as [|[]]; [apply _|]. simpl. case decide => ?; apply _. Qed.

Definition SeenEnqueuedLink_val E T L η l : vProp :=
  ∃ V, SeenEnqueuedLink E T L η V ∗ ⌜(η, l) ∈ L⌝ ∗ link_val η l V 0.
#[global] Instance SeenEnqueuedLink_val_persistent E T L η l :
  Persistent (SeenEnqueuedLink_val E T L η l) := _.
#[global] Instance SeenEnqueuedLink_val_timeless E T L η l :
  Timeless (SeenEnqueuedLink_val E T L η l) := _.

(** Observation of an event set `M`: any enqueue event should have been
  observed as some node being linked in the list. *)
(* TODO: we may also need observation for dequeue event. *)
Definition SeenLinked_logview
  L T E M : vProp :=
  (* Define what it means to have observed the logical view M *)
  ∀ e v V Mv, ⌜ e ∈ M ∧ E !! e = Some (mkGraphEvent (Enq v) V Mv) ⌝ →
    ∃ η' l' η l,
    (* proof of the observation of the enqueue *)
    SeenLinked E T L η' l' V.(dv_comm) e η l v.

(* For any event e with physical view V and logical view Mv, V should support
  the observation of Mv for enqueue events. *)
Definition QueueViews L T E : vProp :=
  ∀ e ev V Mv, ⌜ E !! e = Some (mkGraphEvent ev V Mv) ⌝ →
    (* the physical view V observed the logical view Mv *)
    @{V.(dv_comm)} SeenLinked_logview L T E Mv.

#[global] Instance QueueViews_persistent L T E :
  Persistent (QueueViews L T E) := _.
#[global] Instance QueueViews_objective L T E :
  Objective (QueueViews L T E) := _.

(**** RESOURCES OF NODES -----------------------------------------------------*)

(*** History of the Link field, and resources attached to it.
  - If Link is Null, the history is the singleton of ζ0.
  - If Link is Linked η1 l1, then the history is ζ0 appended (at t0+1) with
    (η1, l1). The resources attached are:
    + an observation that (η1,l1) has been enqueued with eiq, v1, V
    + (η1,l1) has been initialized to Null
    + if it has not been dequeued, the non-atomic ptsto of its Data field.
*)
Definition LinkRes E T η l (deq : bool) (s : LinkState) t0 V0 ζ : vProp :=
  let ζ0 : absHist := {[t0 := (#0, V0)]} in
  match s with
  (* Null *)
  | None => ⌜ζ = ζ0⌝
  (* Linked η1 l1 *)
  | Some (η1,l1) =>
      ∃ V eid (v1 : Z),
      (* CAS only: there are only two events t0 and t0 + 1 *)
      ⌜ζ = <[(t0 + 1)%positive := (#l1, V)]> ζ0⌝
      (* The following is basically
        [SeenLinked em L η l V eid η1 l1 ∗ link_val η1 l1 V 0]
        WITHOUT (1) the part about L and (2) the part [link_val η l V l1].
        - (2) is already acquired when the reader of [l] acquires this state
          [Linked η1 l1]
        - (1) is set up in the full invariant [QueueInternalInv], where (η1,l1)
          here immediately follows (η, l) in the authoritative L. *)
      ∗ ⌜ T !! η1 = Some eid ⌝
      ∗ @{V}(seen_enqueued_val E eid v1 V
              ∗ link_val η1 l1 V 0
              ∗ if deq then emp else (l1 >> data) ↦ #v1)
  end.
(* The full resource for a node also includes the AtomicPtsto of the Link field. *)
Definition Link E T η l (deq : bool) (s : LinkState) : vProp :=
  ∃ t0 V0 ζ, l at↦{η} ζ ∗ LinkRes E T η l deq s t0 V0 ζ.

#[global] Instance LinkRes_timeless E T η l d s t0 V0 ζ :
  Timeless (LinkRes E T η l d s t0 V0 ζ).
Proof.
  rewrite /LinkRes. destruct s; [|apply _]. destruct n. destruct d; apply _.
Qed.
#[global] Instance LinkRes_persistent E T η l s t0 V0 ζ :
  Persistent (LinkRes E T η l true s t0 V0 ζ).
Proof. rewrite /LinkRes. destruct s; [|apply _]. destruct n. apply _. Qed.
#[global] Instance LinkRes_objective E T η l d s t0 V0 ζ :
  Objective (LinkRes E T η l d s t0 V0 ζ).
Proof. rewrite /LinkRes. destruct s; [|apply _]. destruct n. apply _. Qed.

#[global] Instance Link_timeless E T η l d s : Timeless (Link E T η l d s) := _.

(** Setting up the list *)

(* All nodes of the list CL *)
Definition own_nodes E T η0 s0 (D L : list node) : vProp :=
  let CL := (η0, s0) :: D ++ L in
  let lenD := length D in let lenL := S (length L) in
  let infos := zip (next_nodes CL) (dequeue_mask lenD lenL) in
  [∗ list] ηl ; ld ∈ CL ; infos,
  let '(η, l) := ηl in let '(ηl', d) := ld in Link E T η l d ηl'.

(*** THE INVARIANT -----------------------------------------------------------*)

Definition SeenDequeueds γg γ D : vProp :=
  LDL_snapv γ D ∗
  ∃ G T (M : list event_id),
    graph_snap γg G (list_to_set M) ∗
    LTM_snapv γ T ∗
    [∗ list] η;d ∈ D.*1;M, ⌜ ∃ e : event_id, T !! η = Some e ∧ (e, d) ∈ G.(com) ⌝ .

(* Resources of Head: observation of the nodes, as Head's history only contains
  locations that have been dequeued. *)
Definition Head γg γ E T D (Vs : list view) : vProp :=
  [∗ list] k ↦ ηx;V ∈ D;Vs,
    @{V} (SeenEnqueuedLink_val E T D ηx.1 ηx.2 ∗
          if k is O then emp else ∃ D', SeenDequeueds γg γ (D' ++ [ηx])).

#[global] Instance Head_persistent γg γ E T D Vs : Persistent (Head γg γ E T D Vs).
Proof. apply big_sepL2_persistent. intros [|]; apply _. Qed.
#[global] Instance Head_timeless γg γ E T D Vs : Timeless (Head γg γ E T D Vs).
Proof. apply big_sepL2_timeless. intros [|]; apply _. Qed.

(* History and resource of the Tail pointer *)
(* The history of Tail has arbitrary shape, because it can contain racing writes.
  The only useful information is that it only contains locations, and that each
  write comes with an observation of that location. *)
(* This implementation allows Tail to be lagging behind the actual Tail.
  If we want the Tail to point to the actual Tail, we also need to use CASes
  only for the Tail. *)
Definition Tail E T L (ζl : absHist) : vProp :=
  ∀ t v V, ⌜ζl !! t = Some (v, V)⌝ →
    ∃ x, ⌜v = #(LitLoc x)⌝ ∗ ∃ η, @{V} SeenEnqueuedLink_val E T L η x.

#[global] Instance Tail_persistent E T L ζ : Persistent (Tail E T L ζ) := _.
#[global] Instance Tail_timeless E T L ζ : Timeless (Tail E T L ζ) := _.

(*** QueueInv assertion, specific to this implementation--------------------- *)

(* Locs of the Queue: Head, Tail, and nodes *)
Definition QueueLocs γg γ q E γh γl η0 s0 D L T : vProp :=
  let CL := (η0, s0) :: D ++ L in
  let DL := (η0, s0) :: D in
  (* Head *)
  (∃ t0 Vs, (q >> head) at↦{γh} (toHeadHist t0 DL Vs) ∗ Head γg γ E T DL Vs)
  (* Tail *)
  ∗ (∃ ζl, (q >> tail) at↦{γl} ζl ∗ Tail E T CL ζl)
  (* Nodes *)
  ∗ own_nodes E T η0 s0 D L
  .

(** Internal invariant, specific to this implementation. *)
Definition QueueInv_no_exist γg q Q G γ γh γl η0 s0 D L T : vProp :=
  (* (η0, s0) : sentinnel node, D: dequeued nodes, L: remaining nodes *)
  let CL := (η0, s0) :: D ++ L in
  let DL := (η0, s0) :: D in
  (* LEL_master tracks the complete list *)
  LEL_masterv γ CL ∗
  (* LDL_master tracks the dequeued list *)
  LDL_masterv γ D ∗
  (* LTM_master connects the logical enqueues and the event graph *)
  LTM_masterv γ T ∗
  ⌜ QueueProps Q G T η0 s0 D L ⌝
  (* Observations of queue events' views *)
  ∗ QueueViews CL T G.(Es)
  (* Locs of the queue *)
  ∗ ∃ Vb, @{Vb} QueueLocs γg γ q G.(Es) γh γl η0 s0 D L T.

#[global] Instance own_nodes_timeless E T η s D L :
  Timeless (own_nodes E T η s D L).
Proof. apply big_sepL2_timeless => _ [??] [??]. apply _. Qed.
#[global] Instance QueueInv_no_exist_timeless γg q Q G γ γh γl η0 s0 D L T :
  Timeless (QueueInv_no_exist γg q Q G γ γh γl η0 s0 D L T) := _.

Definition QueueBaseInv γ γh γl γg q Q G : vProp :=
  ∃ η0 s0 D L T, QueueInv_no_exist γg q Q G γ γh γl η0 s0 D L T.

(* Only share the ghost state with the client. *)
Definition QueueInv γg (q : loc) Q G : vProp :=
  ⌜ StrongQueueConsistent G ⌝ ∗ graph_master γg (1/2) G
  ∗ (∃ γa : gname, meta q nroot γa ∗ Queuev γa (1/2) Q).

#[global] Instance QueueInv_objective γg q Q G : Objective (QueueInv γg q Q G) := _.

(* Our internal invariant keeps all the physical resources, as well as enough
  ghost resources (`QueueInv`) to maintain agreement with the client. *)
Definition QueueInternalInv γ γh γl γg q : vProp :=
  ∃ Q G, QueueInv γg q Q G ∗ QueueBaseInv γ γh γl γg q Q G.

#[global] Instance QueueInternalInv_objective γ γh γl γg q :
  Objective (QueueInternalInv γ γh γl γg q) := _.
#[global] Instance QueueInternalInv_timeless γ γh γl γg q :
  Timeless (QueueInternalInv γ γh γl γg q) := _.

(*** QueueLocal assertion, specific to this implementation------------------- *)

Definition HeadSeen q γh D : vProp :=
  ∃ t0 Vs, (q >> head) sn⊒{γh} (toHeadHist t0 D Vs)
          ∗ [∗ list] ηx ∈ D, link_val_0 ηx.1 ηx.2.

Global Instance HeadSeen_persistent q γh D : Persistent (HeadSeen q γh D) := _.

Definition QueueSeen γ γh γl q G M : vProp :=
  ∃ ηs s D L D' T, ⌜ D' ⊑ D ⌝
  ∗ HeadSeen q γh ((ηs,s) :: D')
  ∗ (∃ ζl, (q >> tail) sn⊒{γl} ζl)
  ∗ let CL := (ηs,s) :: D ++ L in
    LEL_snapv γ CL ∗ LDL_snapv γ D ∗ LTM_snapv γ T
    (* some of QueueProps, only here for convenience *)
    ∗ ⌜ NoDup CL.*1
      ∧ dom T ≡ list_to_set ((D ++ L).*1)
      ∧ EM_equiv T G.(Es)
      ∧ (∀ η1 η2 eid, T !! η1 = Some eid → T !! η2 = Some eid → η1 = η2)
      ∧ (∀ η eid, T !! η = Some eid → (η ∈ D.*1 ↔ eid ∈ (elements G.(so)).*1))
      ∧ SyncEnqueues G.(Es) M ⌝
    ∗ SeenLinked_logview CL T G.(Es) M
    ∗ SeenLogview G.(Es) M
  .

#[global] Instance QueueSeen_persistent γ γh γl q G M :
  Persistent (QueueSeen γ γh γl q G M) := _.

Definition InternInv N γ γh γl γg q := inv (msqN N q) (QueueInternalInv γ γh γl γg q).
Definition QueueLocal N γg q G logV : vProp :=
  graph_snap γg G logV
  ∗ ∃ γ γh γl, QueueSeen γ γh γl q G logV
  ∗ InternInv N γ γh γl γg q.

#[global] Instance QueueLocal_persistent N γg q G M :
  Persistent (QueueLocal N γg q G M) := _.

(*** Lots and lots of properties for the local assertions and invariants.-----*)

Lemma link_val_0_0 η l V : link_val η l V 0 ⊢ link_val_0 η l.
Proof. iDestruct 1 as (?? [? Eq]) "SN". iExists _, _. iFrame (Eq) "SN". Qed.

(* Various seen enqueued observations. *)
Lemma seen_enqueued_val_sync_logview E e v V eV :
  E !! e = Some eV →
  seen_enqueued_val E e v V ⊢ @{V} SeenLogview E eV.(ge_lview).
Proof. iDestruct 1 as (? [? [??]]) "(% & ? & _)". simplify_eq. by iFrame. Qed.

Lemma SeenLinked_seen_logview E T L η' l' V e η l v eV :
  E !! e = Some eV →
  SeenLinked E T L η' l' V e η l v ⊢ @{V} SeenLogview E eV.(ge_lview).
Proof.
  iIntros (EqE) "[[_ H] _]". by iApply (seen_enqueued_val_sync_logview with "H").
Qed.

Lemma seen_enqueued_val_seen_view E eid v V :
  seen_enqueued_val E eid v V ⊢ ⊒V.
Proof. iDestruct 1 as (? [_ [Eq ?]]) "(_ & _ & ?)". by rewrite Eq. Qed.
Lemma seen_enqueued_seen_view E T L η V eid η' v' :
  seen_enqueued E T L η V eid η' v' ⊢ ⊒V.
Proof. iDestruct 1 as "[_ ?]". by rewrite seen_enqueued_val_seen_view. Qed.

Lemma seen_enqueued_val_map_mono E E' V eid v (SUB: E ⊑ E') :
  seen_enqueued_val E eid v V ⊢ seen_enqueued_val E' eid v V.
Proof.
  iDestruct 1 as (eV (?&?&?)) "SE".
  iExists eV. iDestruct (SeenEvent_mono with "SE") as "#$"; [done|].
  iDestruct "SE" as "(_ & SL & _)". rewrite SeenLogview_closed.
  iDestruct "SL" as %Sub. iPureIntro. do 2 (split; [done|]).
  eapply SyncEnqueues_mono; eauto.
Qed.

Lemma seen_enqueued_list_mono E T L L' η V eid η' v' (SUB: L ⊑ L') :
  seen_enqueued E T L η V eid η' v' ⊢ seen_enqueued E T L' η V eid η' v'.
Proof. iIntros "[? $]". by rewrite SUB. Qed.
Lemma seen_enqueued_emap_mono E E' T L η V eid η' v' (SUB: E ⊑ E') :
  seen_enqueued E T L η V eid η' v' ⊢ seen_enqueued E' T L η V eid η' v'.
Proof. iIntros "[$ ?]". by rewrite seen_enqueued_val_map_mono. Qed.
Lemma seen_enqueued_tmap_mono E T T' L η V eid η' v' (SUB: T ⊆ T') :
  seen_enqueued E T L η V eid η' v' ⊢ seen_enqueued E T' L η V eid η' v'.
Proof. iIntros "[[%%] $] !%". split; [done|]. by eapply lookup_weaken. Qed.
Lemma seen_enqueued_mono E E' T T' L L' η V eid η' v'
  (SUB1: E ⊑ E') (SUB2 : T ⊆ T') (SUB3: L ⊑ L') :
  seen_enqueued E T L η V eid η' v' ⊢ seen_enqueued E' T' L' η V eid η' v'.
Proof.
  rewrite seen_enqueued_emap_mono // seen_enqueued_tmap_mono //.
  by apply seen_enqueued_list_mono.
Qed.

Lemma SeenLinked_list_mono E T L L' η l V eid η' l' v' (SUB: L ⊑ L') :
  SeenLinked E T L η l V eid η' l' v' ⊢ SeenLinked E T L' η l V eid η' l' v'.
Proof.
  iIntros "(? & ? & $)". rewrite seen_enqueued_list_mono // SUB. by iFrame.
Qed.
Lemma SeenLinked_emap_mono E E' T L η l V eid η' l' v' (SUB: E ⊑ E') :
  SeenLinked E T L η l V eid η' l' v' ⊢ SeenLinked E' T L η l V eid η' l' v'.
Proof. iIntros "[? $]". by rewrite seen_enqueued_emap_mono. Qed.
Lemma SeenLinked_tmap_mono E T T' L η l V eid η' l' v' (SUB: T ⊆ T') :
  SeenLinked E T L η l V eid η' l' v' ⊢ SeenLinked E T' L η l V eid η' l' v'.
Proof. iIntros "[? $]". by rewrite seen_enqueued_tmap_mono. Qed.
Lemma SeenLinked_mono E E' T T' L L' η l V eid η' l' v'
  (SUB1: E ⊑ E') (SUB2: T ⊆ T') (SUB3: L ⊑ L') :
  SeenLinked E T L η l V eid η' l' v' ⊢ SeenLinked E' T' L' η l V eid η' l' v'.
Proof. rewrite SeenLinked_emap_mono // SeenLinked_tmap_mono // SeenLinked_list_mono //. Qed.

Lemma SeenEnqueuedLink_seen_view E T L η V :
  SeenEnqueuedLink E T L η V ⊢ ⊒V.
Proof.
  destruct L as [|[]]; simpl.
  - by iDestruct 1 as %?.
  - case decide => ?; [done|].
    iDestruct 1 as (???) "?". by rewrite seen_enqueued_seen_view.
Qed.

Lemma SeenEnqueuedLink_mono E E' T T' L L' η V :
  E ⊑ E' → T ⊆ T' → L ⊑ L' →
  SeenEnqueuedLink E T L η V ⊢ SeenEnqueuedLink E' T' L' η V.
Proof.
  iIntros (S1 S2 S3) "SE". rewrite /SeenEnqueuedLink.
  destruct L as [|[ηs s] L]; [done|].
  destruct L' as [|n' L']. { by apply prefix_nil_not in S3. }
  have ?:= prefix_cons_inv_1 _ _ _ _ S3. subst n'.
  have ?:= prefix_cons_inv_2 _ _ _ _ S3.
  case decide => ?; [done|].
  iDestruct "SE" as (eid η' v) "SE".
  iExists eid, η', v. by iApply (seen_enqueued_mono with "SE").
Qed.

Lemma SeenEnqueuedLink_val_mono E E' T T' L L' η l :
  E ⊑ E' → T ⊆ T' → L ⊑ L' →
  SeenEnqueuedLink_val E T L η l ⊢ SeenEnqueuedLink_val E' T' L' η l.
Proof.
  iIntros (S1 S2 S3). iDestruct 1 as (V) "(SE & % & SN)".
  iExists V. rewrite SeenEnqueuedLink_mono //. iFrame.
  iPureIntro. by eapply elem_of_list_prefix.
Qed.

Lemma SeenLinked_logview_mono L L' T T' E E' M :
  L ⊑ L' → T ⊆ T' → E ⊑ E' → set_in_bound M E →
  SeenLinked_logview L T E M ⊢ SeenLinked_logview L' T' E' M.
Proof.
  iIntros (SL ST SE InD) "SL". iIntros (e v V M' [InM Eqe]).
  iDestruct ("SL" $! e v V with "[%]") as (η' l' η l) "Seen".
  { split; [done|]. specialize (InD _ InM). by eapply prefix_lookup_inv. }
  iExists η', l', η, l. by iApply (SeenLinked_mono with "Seen").
Qed.

(* Link resources *)
Lemma LinkRes_unfold E T η l d s t0 V0 ζ :
  LinkRes E T η l d s t0 V0 ζ ⊣⊢
    ⌜ s = Null ∧ ζ = {[ t0 := (#0, V0)]} ⌝
  ∨ ∃ η1 l1 V1 eid v1,
    ⌜ s = Linked η1 l1
      ∧ ζ = <[(t0 + 1)%positive:=(#l1, V1)]> {[ t0 := (#0, V0)]}
      ∧ T !! η1 = Some eid ⌝
    ∗ @{V1} (seen_enqueued_val E eid v1 V1
              ∗ link_val η1 l1 V1 0
              ∗ (if d then emp else (l1 >> 1) ↦{1} #v1)).
Proof.
  rewrite /LinkRes. destruct s as [[η1 l1]|]; iSplit.
  - iDestruct 1 as (V1 eid v1 F1 F2) "?".
    iRight. iExists η1, l1, V1, eid, v1. eauto.
  - iIntros "[[% _]|H]"; [done|]. iDestruct "H" as (η2 l2 V1 eid v1 (?&?&?)) "?".
    simplify_eq. iExists V1, eid, v1. by eauto.
  - iIntros (?). by iLeft.
  - iIntros "[[%%]|H]"; [done|]. by iDestruct "H" as (????? [? _]) "_".
Qed.
Lemma LinkRes_case_pure E T η l d s t0 V0 ζ :
  LinkRes E T η l d s t0 V0 ζ ⊢
  ⌜ s = Null ∧ ζ = {[ t0 := (#0, V0)]}
  ∨ ∃ η1 l1 V1 eid, s = Linked η1 l1
    ∧ ζ = <[(t0 + 1)%positive:=(#l1, V1)]> {[ t0 := (#0, V0)]}
    ∧ T !! η1 = Some eid ⌝.
Proof.
  rewrite LinkRes_unfold.
  iIntros "[%|H]"; [by iLeft|iRight].
  iDestruct "H" as (η1 l1 V1 eid ? (?&?&?)) "_". iPureIntro. subst.
  by exists η1, l1, V1, eid.
Qed.

Lemma LinkRes_emap_mono E E' T η l d s t0 V0 ζ :
  E ⊑ E' → LinkRes E T η l d s t0 V0 ζ ⊢ LinkRes E' T η l d s t0 V0 ζ.
Proof.
  iIntros (SubE'). rewrite /LinkRes. destruct s as [[]|]; [|done].
  iDestruct 1 as (V eid v1) "(F & F' & SE & LV & ?)".
  iExists V, eid, v1. iFrame. by rewrite seen_enqueued_val_map_mono.
Qed.
Lemma LinkRes_tmap_mono E T T' η l d s t0 V0 ζ :
  T ⊆ T' → LinkRes E T η l d s t0 V0 ζ ⊢ LinkRes E T' η l d s t0 V0 ζ.
Proof.
  iIntros (SubE'). rewrite /LinkRes. destruct s as [[]|]; [|done].
  iDestruct 1 as (V eid v1) "(F & % & ? & ? & ?)".
  iExists V, eid, v1. iFrame. iPureIntro. by eapply lookup_weaken.
Qed.
Lemma LinkRes_mono E E' T T' η l d s t0 V0 ζ :
  E ⊑ E' → T ⊆ T' → LinkRes E T η l d s t0 V0 ζ ⊢ LinkRes E' T' η l d s t0 V0 ζ.
Proof.
  intros S1 S2. rewrite LinkRes_emap_mono; last exact S1.
  rewrite LinkRes_tmap_mono; last exact S2. done.
Qed.

Lemma Link_map_mono E E' T T' η l d s :
  E ⊑ E' → T ⊆ T' → Link E T η l d s ⊢ Link E' T' η l d s.
Proof.
  iIntros (S1 S2). iDestruct 1 as (t0 V0 ζ) "[AT LR]".
  iExists t0, V0, ζ. iFrame "AT". by rewrite LinkRes_mono.
Qed.

Lemma LinkRes_dup E T η l d s t0 V0 ζ :
  LinkRes E T η l d s t0 V0 ζ ⊢ LinkRes E T η l true s t0 V0 ζ.
Proof.
  rewrite /LinkRes. destruct s; [|done]. destruct n.
  iDestruct 1 as (V eid v1) "(F & F' & ? & ? & ?)".
  iExists V, eid, v1. by iFrame.
Qed.

(* Needed for CAS:
  any value in a history of the Link field is comparable to 0. *)
Lemma LinkRes_comparable_0 E T η l d s t0 V0 ζ :
  LinkRes E T η l d s t0 V0 ζ ⊢
  ⌜∀ t v, fst <$> ζ !! t = Some v → ∃ vl : lit, v = #vl ∧ lit_comparable 0 vl⌝.
Proof.
  rewrite LinkRes_case_pure. iPureIntro.
  intros CASE t v [[v1 V1] [<- Eq]]%lookup_fmap_Some'. simpl.
  destruct CASE as [[-> ->]|(η1 & l1 & V1' & eid & -> & -> & _)].
  - apply lookup_singleton_Some in Eq as []. simplify_eq.
    exists 0. split; [done|constructor].
  - case (decide (t = (t0 + 1)%positive)) => ?.
    + subst. rewrite lookup_insert in Eq. simplify_eq.
      exists l1. split; [done|constructor].
    + rewrite lookup_insert_ne // in Eq.
      apply lookup_singleton_Some in Eq as []. simplify_eq.
      exists 0. split; [done|constructor].
Qed.

(* Nodes resources *)
Lemma own_nodes_map_mono E E' T T' η s D L :
  E ⊑ E' → T ⊆ T' → own_nodes E T η s D L ⊢ own_nodes E' T' η s D L.
Proof. intros. apply big_sepL2_mono => i [??] [??] ??. by apply Link_map_mono. Qed.

Lemma own_nodes_access E T η0 s0 D L η n :
  let CL := (η0, s0) :: D ++ L in
  let lenD := length D in
  let lenL := S (length L) in
  let infos := zip (next_nodes CL) (dequeue_mask lenD lenL) in
  (η,n) ∈ CL →
  own_nodes E T η0 s0 D L ⊢
  ∃ d ηs i,
    ⌜ CL !! i = Some (η, n) ∧ infos !! i = Some (ηs, d) ⌝ ∗
    Link E T η n d ηs ∗
    ( (* return as is *)
      (Link E T η n d ηs -∗ own_nodes E T η0 s0 D L) ∧
      (* append *)
      (∀ E' T' η' n', ⌜ ηs = None ∧ i = (length CL - 1)%nat ∧ E ⊑ E' ∧ T ⊆ T'⌝ →
        Link E' T' η n d (Some (η', n')) -∗
        Link E' T' η' n' false None -∗
        own_nodes E' T' η0 s0 D (L ++ [(η', n')]))
    ).
Proof.
  iIntros (CL lenD lenL infos Inη) "Ns". rewrite /own_nodes.
  iDestruct (big_sepL2_length with "Ns") as %EqL.
  destruct (elem_of_list_lookup_1 _ _ Inη) as [i Eqη].
  destruct (lookup_lt_is_Some_2 infos i) as [[ηs d] Eq].
  { rewrite -EqL. by apply (lookup_lt_Some _ _ _ Eqη). }
  iExists d, ηs, i. iSplit; [done|].
  iDestruct (big_sepL2_delete' _ _ _ _ _ _ Eqη Eq with "Ns") as "[Linkη Ns]".
  iFrame "Linkη".
  iSplit.
  - iIntros "Linkη". iCombine "Linkη" "Ns" as "Ns".
    by rewrite -(big_sepL2_delete' _ _ _ _ _ _ Eqη Eq).
  - iIntros (E' T' η' n' (? & Eqi & SubE & SubT)) "Lη Lη'". subst ηs.
    assert (∃ L, CL = L ++ [((η, n))]) as [L' EqCL].
    { apply lookup_last_Some. by rewrite -Eqi. }
    rewrite /infos EqCL.
    rewrite (_: (η0, s0) :: D ++ L ++ [(η', n')] = (L' ++ [(η, n)]) ++ [(η', n')]);
      last first.
    { clear -EqCL. rewrite -EqCL. by simplify_list_eq. }
    destruct (next_nodes_app_2 L' (η, n) (η', n')) as (LS' & Eq1' & Eq2' & EqLLS').
    rewrite Eq1' Eq2'.
    assert (EqLCL: length CL = (lenD + lenL)%nat).
    { by rewrite /CL (app_length (_::_)) /= /lenD /lenL Nat.add_succ_r. }
    assert (Eqi' : i = (lenD + lenL - 1)%nat).
    { by rewrite Eqi EqLCL. }
    assert (∃ Ld, (dequeue_mask lenD lenL) = Ld ++ [d]) as [Ld EqLd].
    { apply lookup_last_Some. rewrite dequeue_mask_length -Eqi'.
      clear -Eq. apply lookup_zip_with_Some in Eq as (?&?&?&_&?).
      by simplify_eq. }
    rewrite app_length Nat.add_1_r dequeue_mask_append EqLd.
    have EqLSd: length LS' = length Ld.
    { have EqL1 : S (length Ld) = (lenD + lenL)%nat.
      { by rewrite -dequeue_mask_length EqLd app_length /= Nat.add_1_r. }
      have EqL2 : S (length LS') = length CL.
      { by rewrite EqCL app_length /= Nat.add_1_r EqLLS'. }
      clear -EqL1 EqL2 EqLCL. move : EqL2. rewrite EqLCL -EqL1. lia. }
    rewrite zip_with_app // /= zip_with_app; last first.
    { clear -EqLSd. rewrite 2!app_length /=. lia. }
    rewrite zip_with_app // /=.
    rewrite big_sepL2_app_same_length; last by right.
    rewrite big_sepL2_app_same_length; last by right.
    rewrite big_sepL2_app_same_length; last by right.
    iDestruct "Ns" as "[Ns _]". iSplitR "Lη'"; first iSplitL "Ns".
    + iApply (big_sepL2_mono with "Ns").
      iIntros (j [η1 n1] [η2 n2] Eq1 Eq2) "Link".
      iSpecialize ("Link" with "[%]").
      { clear -EqCL Eqi Eq1. intros ?. subst j.
        move : Eqi. rewrite EqCL app_length /= Nat.add_sub => ?. subst i.
        apply lookup_lt_Some in Eq1. lia. }
      by iApply (Link_map_mono with "Link").
    + simpl. by iFrame "Lη".
    + simpl. by iFrame "Lη'".
Qed.

Lemma Link_dequeue E T η' n' η n :
  Link E T η' n' false (Some (η, n)) ⊢
  Link E T η' n' true (Some (η, n)) ∗
  ∃ eid eV v, ⌜ T !! η = Some eid ∧ E !! eid = Some eV ∧ ge_event eV = Enq v ⌝ ∗
  @{eV.(ge_view).(dv_comm)}(n >> data) ↦{1} #v.
Proof.
  rewrite /Link. iDestruct 1 as (t0 V0 ζ) "[AT LR]".
  iDestruct "LR" as (V e v) "(#F1 & #F2 & #SE & LV & NA)".
  iSplitR "NA".
  - iExists t0, V0, ζ. iFrame. iExists V, e, v. by iFrame "#∗".
  - rewrite /seen_enqueued_val /SeenEvent.
    iDestruct "SE" as (eV (Eqv & <- & SE) EqE) "SE". iDestruct "F2" as %EqT.
    iExists e, eV, v. iSplit; [done|]. by iFrame "NA".
Qed.

Lemma own_nodes_dequeue E T ηs s D L η n :
  own_nodes E T ηs s D ((η, n) :: L) ⊢
    own_nodes E T ηs s (D ++ [(η, n)]) L ∗
    ∃ eid eV v, ⌜ T !! η = Some eid ∧ E !! eid = Some eV ∧ ge_event eV = Enq v ⌝ ∗
    @{eV.(ge_view).(dv_comm)}(n >> data) ↦{1} #v.
Proof.
  iIntros "Ns". rewrite /own_nodes.
  set CL := (ηs, s) :: D ++ (η, n) :: L.
  rewrite (_ : ((ηs, s) :: (D ++ [(η, n)]) ++ L) = CL); last first.
  { clear. rewrite /CL. by simplify_list_eq. }
  set lenD := length D.
  set lenL :=  S (length ((η, n) :: L)).
  set lenD' := length (D ++ [(η,n)]).
  set lenL' := S (length L).
  set infos := zip (next_nodes CL) (dequeue_mask lenD lenL).
  set infos' := zip (next_nodes CL) (dequeue_mask lenD' lenL').

  iDestruct (big_sepL2_length with "Ns") as %EqL.
  destruct (infos_dequeue ηs s D L η n EqL) as ((η' & n' & Eq') & Eq & EqIN).
  rewrite (big_sepL2_insert_acc _ _ _ _ _ _ Eq' Eq) Link_dequeue.
  iDestruct "Ns" as "[[Link $] Ns]".
  rewrite /CL -{3}(list_insert_id _ _ _ Eq') /infos' EqIN.
  iApply ("Ns" with "[Link]"). simpl. by iFrame.
Qed.

Lemma own_nodes_own_loc_prim' E T ηs s D L η n :
  (η, n) ∈ (ηs, s) :: D ++ L →
  own_nodes E T ηs s D L ⊢ ∃ C, n p↦{1} C.
Proof.
  iIntros (Inη) "Ns". rewrite (own_nodes_access _ _ _ _ _ _ η n Inη).
  iDestruct "Ns" as (d2 ηs2 i Eq) "[L _]".
  iDestruct "L" as (t0 V0 ζ0) "[AT _]". by iApply AtomicPtsTo_own_loc_prim.
Qed.

Lemma own_nodes_own_loc_prim E T ηs s D L Vb η n :
  (η, n) ∈ (ηs, s) :: D ++ L →
  @{Vb} own_nodes E T ηs s D L ⊢ ∃ q C, ▷ <subj> n p↦{q} C.
Proof.
  intros Inη. rewrite (own_nodes_own_loc_prim') //.
  iDestruct 1 as (C) "AT".
  rewrite view_at_subjectively. iExists _, _. iNext. iFrame "AT".
Qed.

Lemma own_nodes_inj_2 E T ηs s D L :
  let CL := (ηs, s) :: D ++ L in
  own_nodes E T ηs s D L ⊢
  ⌜ ∀ n η η', (η, n) ∈ CL → (η', n) ∈ CL → η = η'⌝.
Proof.
  intros CL.
  set lenD := length D.
  set lenL := S (length L).
  set infos := zip (next_nodes CL) (dequeue_mask lenD lenL).
  iIntros "Ns" (n η η' [i Eqi]%elem_of_list_lookup_1 [j Eqj]%elem_of_list_lookup_1).
  case (decide (i = j)) => [?|NEq].
  { subst i. rewrite Eqi in Eqj. by inversion Eqj. }
  iExFalso.
  iDestruct (big_sepL2_length with "Ns") as %EqL.
  destruct (lookup_lt_is_Some_2 infos i) as [[η1 d1] Eq1].
  { rewrite -EqL. by apply (lookup_lt_Some _ _ _ Eqi). }
  destruct (lookup_lt_is_Some_2 infos j) as [[η2 d2] Eq2].
  { rewrite -EqL. by apply (lookup_lt_Some _ _ _ Eqj). }
  rewrite /own_nodes.
  iDestruct (big_sepL2_delete' _ _ _ _ _ _ Eqi Eq1 with "Ns") as "[Li Ns]".
  iDestruct (big_sepL2_delete' _ _ _ _ _ _ Eqj Eq2 with "Ns") as "[Lj Ns]".
  iSpecialize ("Lj" with "[%//]").
  iDestruct "Li" as (???) "[ATi _]".
  iDestruct "Lj" as (???) "[ATj _]".
  by iDestruct (AtomicPtsTo_exclusive with "ATi ATj") as %?.
Qed.

Lemma own_nodes_inj_2' E T ηs s D L Vb :
  let CL := (ηs, s) :: D ++ L in
  @{Vb} own_nodes E T ηs s D L ⊢
  ⌜ ∀ n η η', (η, n) ∈ CL → (η', n) ∈ CL → η = η'⌝.
Proof. intros. rewrite own_nodes_inj_2. by iDestruct 1 as %?. Qed.

(* Head *)
Lemma Head_mono γg γ E E' T T' D Vs (S1 : E ⊑ E') (S2 : T ⊆ T') :
  Head γg γ E T D Vs ⊢ Head γg γ E' T' D Vs.
Proof.
  apply big_sepL2_mono.
  intros i [η n] V EqD EqVs. simpl.
  by rewrite SeenEnqueuedLink_val_mono.
Qed.

Lemma Head_lookup_Some γg γ E T D Vs t0 t v V :
  (toHeadHist t0 D Vs) !! t = Some (v, V) →
  Head γg γ E T D Vs ⊢
    ∃ η (l : loc),
    ⌜(t0 ≤ t)%positive
      ∧ Vs !! (Pos.to_nat t - Pos.to_nat t0)%nat = Some V
      ∧ v = #l
      ∧ D !! (Pos.to_nat t - Pos.to_nat t0)%nat = Some (η, l)⌝ ∗
    @{V} (SeenEnqueuedLink_val E T D η l ∗
          if bool_decide (t = t0) then emp else ∃ D', SeenDequeueds γg γ (D' ++ [(η,l)])).
Proof.
  iIntros ((Le & EqV & η & l & ? & EqD)%toHeadHist_lookup_Some) "H".
  subst v. iExists η, l. iSplit; [done|].
  rewrite /Head (big_sepL2_lookup _ _ _ _ _ _ EqD EqV) /=.
  iDestruct "H" as "[$ H]". case_match.
  - rewrite bool_decide_true //. lia.
  - rewrite bool_decide_false //. lia.
Qed.

Lemma Head_append γg γ E T D Vs η n V :
  Head γg γ E T D Vs ∗
  @{V} (SeenEnqueuedLink_val E T (D ++ [(η, n)]) η n
        ∗ if length D is O then emp else ∃ D', SeenDequeueds γg γ (D' ++ [(η,n)])) ⊢
  Head γg γ E T (D ++ [(η,n)]) (Vs ++ [V]).
Proof.
  rewrite /Head (big_sepL2_app_same_length _ D [(η,n)] Vs [V]);
    [|right; by simpl].
  iIntros "[H SE]". iSplitL "H".
  - iApply (big_sepL2_mono with "H"). intros. simpl.
    rewrite SeenEnqueuedLink_val_mono; eauto. by eexists.
  - rewrite big_sepL2_singleton /=. iDestruct "SE" as "[$ SD]".
    case_match; [done|]. by rewrite Nat.add_0_r.
Qed.

(* Tail *)
Lemma Tail_mono E E' T T' L L' ζ (S1 : E ⊑ E') (S2 : T ⊆ T') (S3 : L ⊑ L') :
  Tail E T L ζ ⊢ Tail E' T' L' ζ.
Proof.
  iIntros "T" (t v V Eqt).
  iDestruct ("T" $! t v V Eqt) as (x Eq η) "SE".
  iExists x. iSplit; [done|]. iExists η.
  by rewrite SeenEnqueuedLink_val_mono.
Qed.

Lemma Tail_insert E T CL ζl t η l V :
  Tail E T CL ζl ∗
  @{V} SeenEnqueuedLink_val E T CL η l ⊢
  Tail E T CL (<[t := (#l, V)]> ζl).
Proof.
  iIntros "[Tls SE]".
  rewrite /Tail.
  iIntros (t' v' V'). case (decide (t' = t)) => [->|?].
  - rewrite lookup_insert. iIntros (?). simplify_eq.
    iExists l. iSplit; [done|]. iExists η. iFrame.
  - by rewrite lookup_insert_ne.
Qed.
End Interp.

#[global] Typeclasses Opaque SeenEnqueuedLink_val SeenEnqueuedLink Head Tail HeadSeen.
Arguments SeenEnqueuedLink : simpl never.

(*** Lots and lots of ghost properties ---------------------------------------*)
Section ghost_rules.
Context `{!inG Σ msq_queueR}.
#[local] Notation iProp := (iProp Σ).
#[local] Notation vProp := (vProp Σ).

Lemma Maps_master_alloc CL D T :
  ⊢ |==> ∃ γ, LEL_master γ CL ∗ LDL_master γ D ∗ LTM_master γ T.
Proof.
  do 2 setoid_rewrite <-own_op. apply own_alloc.
  rewrite /= -!pair_op /= !left_id !right_id !pair_valid.
  split; [split; apply mono_list_auth_valid|].
  apply auth_both_valid_discrete. split; [done|apply to_agreeM_valid].
Qed.

(* lnode-event_id map T *)
Lemma LTM_master_snap_included γ T T' :
  LTM_master γ T -∗ LTM_snap γ T' -∗ ⌜T' ⊆ T⌝.
Proof.
  iIntros "[o1 ?] o2".
  iCombine "o1 o2" gives %[_ [INCL _]%auth_both_valid_discrete].
  iPureIntro. by move : INCL => /to_agreeM_included.
Qed.
Lemma LTM_master_ssnap_lookup γ T η eid :
  LTM_master γ T -∗ LTM_ssnap γ η eid -∗ ⌜T !! η = Some eid⌝.
Proof.
  iIntros "LTm VMs". by iDestruct (LTM_master_snap_included with "LTm VMs")
                        as %SUB%map_singleton_subseteq_l.
Qed.

Lemma LTM_snap_sub γ T T' (Le: T ⊆ T') : LTM_snap γ T' ⊢ LTM_snap γ T.
Proof.
  apply own_mono, prod_included. split; [done|]. simpl.
  by apply auth_frag_mono, to_agreeM_included.
Qed.
Lemma LTM_master_fork γ T : LTM_master γ T ⊢ LTM_snap γ T.
Proof. by iIntros "[? $]". Qed.

Lemma LTM_update' γ T T' (SUB: T ⊆ T') :
  LTM_master γ T ==∗ LTM_master γ T'.
Proof.
  apply own_update, prod_update; [done|]. simpl.
  by apply auth_update, to_agreeM_local_update.
Qed.
Lemma LTM_update γ T T' (SUB: T ⊆ T') :
  LTM_master γ T ==∗ LTM_master γ T' ∗ LTM_snap γ T'.
Proof.
  iIntros "T". iMod (LTM_update' _ _ _ SUB with "T") as "T".
  iDestruct (LTM_master_fork with "T") as "#$". by iFrame.
Qed.
Lemma LTM_update_insert γ T η eid (FR: η ∉ dom T):
  LTM_master γ T ==∗ LTM_master γ (<[η := eid]>T) ∗ LTM_ssnap γ η eid.
Proof.
  iIntros "LTm".
  iMod (LTM_update with "LTm") as "[$ Snap]".
  { by apply insert_subseteq, (not_elem_of_dom (D:= gset lnode)). }
  iIntros "!>". iApply (LTM_snap_sub with "Snap").
  by apply insert_mono, gmap_subseteq_empty.
Qed.

(* Authoritative complete list L *)
Lemma LEL_master_snap_included γ L L' :
  LEL_master γ L -∗ LEL_snap γ L' -∗ ⌜L' ⊑ L⌝.
Proof.
  iIntros "o1 o2". by iDestruct (own_valid_2 with "o1 o2")
                        as %[[?%mono_list_both_valid_L _] _].
Qed.

Lemma LEL_snap_sub γ L L' (Le: L ⊑ L') : LEL_snap γ L' ⊢ LEL_snap γ L.
Proof.
  apply own_mono, prod_included. split; [|done].
  apply prod_included. split; [|done]. simpl. by apply mono_list_lb_mono.
Qed.
Lemma LEL_master_fork γ L :
  LEL_master γ L ⊢ LEL_snap γ L.
Proof.
  apply own_mono, prod_included. split; [|done].
  apply prod_included. split; [|done]. simpl. by apply mono_list_included.
Qed.

Lemma LEL_update' γ L L' (SUB: L ⊑ L') :
  LEL_master γ L ==∗ LEL_master γ L'.
Proof.
  apply own_update, prod_update; [|done]. apply prod_update; [|done]. simpl.
  by apply mono_list_update.
Qed.
Lemma LEL_update γ L L' (SUB: L ⊑ L') :
  LEL_master γ L ==∗ LEL_master γ L' ∗ LEL_snap γ L'.
Proof.
  iIntros "L". iMod (LEL_update' _ _ _ SUB with "L") as "L".
  iDestruct (LEL_master_fork with "L") as "#$". by iFrame.
Qed.
Lemma LEL_update_app γ L L':
  LEL_master γ L ==∗ LEL_master γ (L ++ L') ∗ LEL_snap γ (L ++ L').
Proof.
  apply LEL_update. rewrite -{1}(app_nil_r L). by apply prefix_app, prefix_nil.
Qed.

(* Dequeued list D *)
Lemma LDL_master_snap_included γ D D' :
  LDL_master γ D -∗ LDL_snap γ D' -∗ ⌜D' ⊑ D⌝.
Proof.
  iIntros "o1 o2". by iDestruct (own_valid_2 with "o1 o2")
                        as %[[_ ?%mono_list_both_valid_L] _].
Qed.

Lemma LDL_snap_sub γ D D' (Le: D ⊑ D') : LDL_snap γ D' ⊢ LDL_snap γ D.
Proof.
  apply own_mono, prod_included. split; [|done].
  apply prod_included. split; [done|]. simpl. by apply mono_list_lb_mono.
Qed.
Lemma LDL_master_fork γ D :
  LDL_master γ D ⊢ LDL_snap γ D.
Proof.
  apply own_mono, prod_included. split; [|done].
  apply prod_included. split; [done|]. simpl. by apply mono_list_included.
Qed.

Lemma LDL_update' γ D D' (SUB: D ⊑ D') :
  LDL_master γ D ==∗ LDL_master γ D'.
Proof.
  apply own_update, prod_update; [|done]. apply prod_update; [done|]. simpl.
  by apply mono_list_update.
Qed.
Lemma LDL_update γ D D' (SUB: D ⊑ D') :
  LDL_master γ D ==∗ LDL_master γ D' ∗ LDL_snap γ D'.
Proof.
  iIntros "D". iMod (LDL_update' _ _ _ SUB with "D") as "D".
  iDestruct (LDL_master_fork with "D") as "#$". by iFrame.
Qed.
Lemma LDL_update_app γ D D':
  LDL_master γ D ==∗ LDL_master γ (D ++ D') ∗ LDL_snap γ (D ++ D').
Proof.
  apply LDL_update. rewrite -{1}(app_nil_r D). by apply prefix_app, prefix_nil.
Qed.

End ghost_rules.

Section irc_proof.
Context `{!noprolG Σ, !msqueueG Σ, !atomicG Σ}.
Local Existing Instances msq_graphG msq_queueG msq_absG.
#[local] Notation iProp := (iProp Σ).
#[local] Notation vProp := (vProp Σ).
Lemma QueueBaseInv_unfold_snap' γg q Q G γ γh γl CL :
  QueueBaseInv γ γh γl γg q Q G -∗
  LEL_snapv γ CL -∗
  ∃ η s D L T, QueueInv_no_exist γg q Q G γ γh γl η s D L T ∗
    ⌜ CL ⊑ (η, s) :: D ++ L ⌝.
Proof.
  iDestruct 1 as (η s D L T) "(LEL & QI)". iIntros "LS".
  iExists η, s, D, L, T.
  iDestruct (LEL_master_snap_included with "LEL LS") as %LeCL.
  iSplit; [|done]. by iFrame.
Qed.

Lemma QueueBaseInv_unfold_snap γg q Q G γ γh γl η s D0 L0 :
  QueueBaseInv γ γh γl γg q Q G -∗
  let CL0 := (η, s) :: D0 ++ L0 in
  LEL_snapv γ CL0 -∗
  ∃ D L T, QueueInv_no_exist γg q Q G γ γh γl η s D L T ∗
    ⌜ CL0 ⊑ (η, s) :: D ++ L ∧ D0 ++ L0 ⊑ D ++ L ⌝.
Proof.
  iIntros "QI LEL".
  iDestruct (QueueBaseInv_unfold_snap' with "QI LEL") as (η0 s0 D L T) "[QI %LeCL]".
  have ? := prefix_cons_inv_1 _ _ _ _ LeCL. simplify_eq.
  have ? := prefix_cons_inv_2 _ _ _ _ LeCL.
  iExists D, L, T.
  iSplit; [|done]. by iFrame.
Qed.

Lemma QueueBaseInv_unfold_snap_2 γg q Q G γ γh γl η s D0 L0 T0 :
  QueueBaseInv γ γh γl γg q Q G -∗
  let CL0 := (η, s) :: D0 ++ L0 in
  LEL_snapv γ CL0 -∗
  LTM_snapv γ T0 -∗
  ∃ D L T, QueueInv_no_exist γg q Q G γ γh γl η s D L T ∗
    ⌜ CL0 ⊑ (η, s) :: D ++ L ∧ D0 ++ L0 ⊑ D ++ L ∧ T0 ⊆ T ⌝.
Proof.
  iIntros "QI LEL LTM".
  iDestruct (QueueBaseInv_unfold_snap with "QI LEL") as (D L T) "[QI [% %]]".
  iExists D, L, T.
  iDestruct "QI" as "(LEL & LD & LT & R)".
  iDestruct (LTM_master_snap_included with "LT LTM") as %?. by iFrame.
Qed.

Lemma QueueInv_no_exist_snapshot γg q Q G γ γh γl η s D L T :
  QueueInv_no_exist γg q Q G γ γh γl η s D L T ⊢
    LEL_snapv γ ((η,s) :: D ++ L) ∗
    LDL_snapv γ D ∗
    LTM_snapv γ T.
Proof.
  iDestruct 1 as "(LEL & LD & LT & ?)".
  iDestruct (LEL_master_fork with "LEL") as "$".
  iDestruct (LDL_master_fork with "LD") as "$".
  by iDestruct (LTM_master_fork with "LT") as "$".
Qed.

Lemma QueueInv_no_exist_QueueLocs_access γg q Q G γ γh γl η s D L T :
  let E := G.(Es) in
  QueueInv_no_exist γg q Q G γ γh γl η s D L T -∗
  ∃ Vb, @{Vb} QueueLocs γg γ q E γh γl η s D L T
      ∗ (∀ Vb, @{Vb} QueueLocs γg γ q E γh γl η s D L T -∗
              QueueInv_no_exist γg q Q G γ γh γl η s D L T).
Proof.
  iIntros "(LEL & LD & LT & F & QV & QL)".
  iDestruct "QL" as (Vb) "QL".
  iExists Vb. iFrame "QL". iIntros (Vb') "QL". iFrame. by iExists Vb'.
Qed.

Lemma QueueInv_no_exist_tail_access γg q Q G γ γh γl η s D L T :
  let E := G.(Es) in
  QueueInv_no_exist γg q Q G γ γh γl η s D L T -∗
  (∃ Vb (ζl : absHist),
    @{Vb} ((q >> tail) at↦{γl} ζl ∗ Tail E T ((η,s) :: D ++ L) ζl) ∗
    (∀ Vb' ζl',
      @{Vb'} ((q >> tail) at↦{γl} ζl' ∗ Tail E T ((η,s) :: D ++ L) ζl') -∗
      QueueInv_no_exist γg q Q G γ γh γl η s D L T)).
Proof.
  intros E. rewrite ->QueueInv_no_exist_QueueLocs_access.
  iDestruct 1 as (Vb) "[(H & T & Ns) Close]".
  iDestruct "T" as (ζl) "[T Tls]".
  iExists Vb, ζl. iFrame "T Tls". iIntros (Vb' ζl') "Ts".
  iApply ("Close" $! (Vb' ⊔ Vb)).
  iSplitL "H"; last iSplitR "Ns"; [|iExists ζl'|]; by iFrame.
Qed.

Lemma QueueInv_no_exist_tail_immut_access γg q Q G γ γh γl η s D L T :
  let E := G.(Es) in
  QueueInv_no_exist γg q Q G γ γh γl η s D L T -∗
  ∃ Vb (ζl : absHist),
    @{Vb} ((q >> tail) at↦{γl} ζl ∗ Tail E T ((η,s) :: D ++ L) ζl) ∗
    (∀ Vb', @{Vb'} (q >> tail) at↦{γl} ζl -∗
      QueueInv_no_exist γg q Q G γ γh γl η s D L T).
Proof.
  intros E. rewrite ->QueueInv_no_exist_tail_access.
  iDestruct 1 as (Vb ζl) "[[T #Tls] Close]".
  iExists Vb, ζl. iFrame "T Tls".
  iIntros (Vb') "T". iApply ("Close" $! (Vb' ⊔ Vb)). by iFrame "#∗".
Qed.

Lemma QueueInv_no_exist_head_immut_access γg q Q G γ γh γl η s D L T :
  let DL := (η, s) :: D in let E := G.(Es) in
  QueueInv_no_exist γg q Q G γ γh γl η s D L T -∗
  (∃ Vb t0 Vs,
    @{Vb} ((q >> head) at↦{γh} toHeadHist t0 DL Vs ∗ Head γg γ E T DL Vs) ∗
    (∀ Vb', @{Vb'} ((q >> head) at↦{γh} toHeadHist t0 DL Vs) -∗
      QueueInv_no_exist γg q Q G γ γh γl η s D L T)).
Proof.
  intros DL E. rewrite ->QueueInv_no_exist_QueueLocs_access.
  iDestruct 1 as (Vb) "[[H TNs] Close]".
  iDestruct "H" as (t0 Vs) "[H #Hs]".
  iExists Vb, t0, Vs. iFrame "#∗". iIntros (Vb') "H".
  iApply ("Close" $! (Vb' ⊔ Vb)). iFrame. iExists t0, Vs. by iFrame "#∗".
Qed.

Lemma QueueInv_agree γg q Q G Q' G' :
  QueueInv γg q Q G -∗ QueueInv γg q Q' G' -∗ ⌜ G' = G ∧ Q' = Q ⌝.
Proof.
  iIntros "(_ & GM & %γa & MS & QA) (_ & GM' & %γa' & MS' & QA')".
  iDestruct (meta_agree with "MS MS'") as %<-.
  iDestruct (graph_master_agree with "GM GM'") as %<-.
  iCombine "QA QA'" gives %[_ <-]%frac_agree_op_valid_L. done.
Qed.

Lemma QueueInv_consistent γg q Q G :
  QueueInv γg q Q G ⊢ ⌜ StrongQueueConsistent G ∧ eventgraph_consistent G ⌝.
Proof.
  iIntros "(% & GM & ?)". by iDestruct (graph_master_consistent with "GM") as %?.
Qed.

Lemma QueueInv_graph_snap_included γg q Q G G' M' :
  QueueInv γg q Q G -∗ graph_snap γg G' M' -∗ ⌜ G' ⊑ G ⌝.
Proof. iIntros "(_ & GM & _)". iApply (graph_master_snap_included with "GM"). Qed.

Lemma QueueInv_graph_snap_included_2 γg q Q G G' M' V' :
  QueueInv γg q Q G -∗ @{V'} graph_snap γg G' M' -∗ ⌜ G' ⊑ G ⌝.
Proof. iIntros "(_ & GM & _)". iApply (graph_master_snap_included_2 with "GM"). Qed.


Lemma QueueInv_graph_snap γg q Q G :
  QueueInv γg q Q G -∗ graph_snap γg G ∅.
Proof. iIntros "(_ & GM & _)". iApply (graph_master_snap with "GM"). Qed.

Lemma QueueInv_update γg q Q G Q' G' :
  G ⊑ G' → eventgraph_consistent G' → StrongQueueConsistent G' →
  QueueInv γg q Q G -∗ QueueInv γg q Q G ==∗
  QueueInv γg q Q' G' ∗ QueueInv γg q Q' G' ∗ graph_gsnapv γg G'.
Proof.
  iIntros (LeG' EGCs' SC') "(_ & GM & %γa & MS & QA) (_ & GM' & %γa' & MS' & QA')".
  iDestruct (meta_agree with "MS MS'") as %<-.
  iCombine "GM GM'" as "GM".
  iMod (graph_master_update _ _ G' LeG' EGCs' with "GM") as "([$ $] & #$)".
  iFrame (SC').
  iMod (own_update_2 _ _ _ (to_frac_agree (1/2) (Q' : leibnizO queue) ⋅
                            to_frac_agree (1/2) (Q' : leibnizO queue))
          with "QA' QA") as "[QA QA']".
  { rewrite -!frac_agree_op Qp.half_half. by apply cmra_update_exclusive. }
  iIntros "!>". iSplitL "QA MS"; iExists γa; iFrame.
Qed.

Lemma find_tail_spec N (DISJ : N ## histN) γg γ γh γl q tid :
  {{{ (∃ ζl, (q >> tail) sn⊒{γl} ζl) ∗ InternInv N γ γh γl γg q }}}
      find_tail [ #q] @ tid; ⊤
  {{{ (n : lit), RET #n;
      ⌜n = 0⌝ ∨ (∃ l : loc, ⌜n = l⌝ ∧ ∃ η' G T L,
                  graph_snap γg G ∅ ∗ LTM_snapv γ T ∗ LEL_snapv γ L ∗
                  SeenEnqueuedLink_val G.(Es) T L η' (l >> link)) }}}.
Proof.
  iIntros (Φ) "[oT #QII] Post". iDestruct "oT" as (ζl) "oT".

  wp_lam. wp_op. wp_bind (!ᵃᶜ _)%E.

  (* prepare to read tail, by getting the atomic ptsto the tail invariant. *)
  iInv "QII" as (Q0 G0) ">[(QC & GM & QA) QBI]" "Close".
  iDestruct "QBI" as (η0 s0 D0 L0 T0) "QBI".
  set E0 := G0.(Es).
  set CL0 := (η0, s0) :: D0 ++ L0.

  (* get a snapshot *)
  iDestruct (graph_master_snap with "GM") as "#GS0".
  iDestruct (QueueInv_no_exist_snapshot with "QBI") as "#(LS & _ & LTs)".

  (* get Tail *)
  iDestruct (QueueInv_no_exist_tail_immut_access with "QBI")
    as (Vb ζl0) "[[T Tls] QIC]".
  iDestruct (monPred_in_intro True%I with "[//]") as (Vl) "[InVl _]".
  (* ready to read *)
  wp_apply (AtomicSeen_acquire_read with "[$oT $T $InVl]"); first solve_ndisj.

  iIntros (tl' vl' V' V'' ζ'') "(#F' & #InV'' & Snζ1 & T)".
  iDestruct (view_at_elim with "InV'' Snζ1") as "#Snζ''".

  (* close the invariant *)
  iMod ("Close" with "[T QC QA GM QIC]") as "_".
  { iIntros "{#} !>". iExists _, _. iFrame "QC QA GM".
    iExists _, _, _, _, _. by iApply "QIC". }

  (* extract read value *)
  iDestruct "F'" as %([_ Subζ''] & Eqtl' & _ & LeVl).
  iAssert (∃ n : loc, ⌜vl' = #n⌝ ∗ ∃ η, SeenEnqueuedLink_val E0 T0 CL0 η n)%I
    with "[Tls]" as (n ? η) "SE".
  { rewrite /Tail.
    iDestruct ("Tls" $! tl' vl' V' with "[%]") as (n Eqn η) "SE".
    - by eapply lookup_weaken.
    - iExists n. iFrame (Eqn). iExists η. rewrite view_at_view_at.
      iApply (view_at_elim with "[] SE").
      iApply (monPred_in_mono with "InV''"). simpl; by solve_lat. }
  subst vl'.
  rewrite (bi.persistent_sep_dup (SeenEnqueuedLink_val _ _ _ _ _)).
  iDestruct "SE" as "[SE' SE]".
  rewrite {3}/SeenEnqueuedLink_val. iDestruct "SE" as (Vη) "[_ SNη]".
  iDestruct "SNη" as (Inη Vη' ζlη) "[_ SNη]".

  iClear "InVl". clear Vη' ζl Vl LeVl Subζ'' ζl0 Vb.
  iIntros "!>".
  wp_let. wp_op. rewrite shift_0. wp_bind (!ᵃᶜ _)%E.

  (* prepare to read η, open the invariant again... *)
  iInv "QII" as (Q1 G1) ">[(QC & GM & QA) QBI]" "Close".
  iDestruct (QueueBaseInv_unfold_snap with "QBI LS")
    as (D1 L1 T1) "[QBI [%LeCL %LeDL]]".

  (* get another snapshot *)
  iDestruct (graph_master_snap with "GM") as "#GS1".
  iDestruct (QueueInv_no_exist_snapshot with "QBI") as "#(LS1 & _ & LT1)".

  (* get permission of η *)
  set E1 := G1.(Es).
  set CL1 := (η0, s0) :: D1 ++ L1.
  set infos1 := zip (next_nodes CL1)
                    (dequeue_mask (length ((η0, s0) :: D1)) (length L1)).

  iDestruct "QBI" as "(LEL & LDL & LT & F & QV & QLs)".
  iDestruct "QLs" as (Vb) "(H & T & Ns)".
  rewrite (own_nodes_access _ _ _ _ _ _ η n); last first.
  { by apply (elem_of_list_prefix _ _ _ LeCL Inη). }
  iDestruct "Ns" as (d ηs i [Eqη Eqd]) "[Linkη Ns]".
  iDestruct "Linkη" as (t1 V1 ζ1) "[ATη S1]".
  rewrite (view_at_objective_iff (LinkRes _ _ _ _ _ _ _ _ _)).
  (* ready to read *)
  wp_apply (AtomicSeen_acquire_read with "[$SNη $ATη $InV'']"); first solve_ndisj.

  iIntros (tn' vn' Vn1 V3 ζn') "(F3 & #sV3 & #SNη' & ATη)".

  (* get a copy *)
  iDestruct (LinkRes_dup with "S1") as "#Pη".

  (* re-establish the invariant *)
  iMod ("Close" with "[-F3 SNη' Post SE']") as "_".
  { iNext. iExists _, _. iFrame "QC QA GM". iExists η0, s0, D1, L1, T1.
    iFrame "LEL LDL LT F QV". iClear "#". iExists (Vb ⊔ V3). iFrame "H T".
    (* return resources *)
    rewrite bi.and_elim_l. iApply (view_at_mono_2 with "Ns"); [solve_lat|].
    iExists _, _, _. by iFrame. } clear Vb.

  iIntros "!>". wp_let.
  iDestruct "F3" as %([Subζlη Subζn'] & Eqtn' & MAXn' & LeV'').
  assert (Eqtn1 := lookup_weaken  _ _ _ _ Eqtn' Subζn').

  case (decide (tn' = t1)) => [Eqt1|NEqt1].
  - (* reads 0 from n', returning n as the found tail *)
    subst tn'.
    iAssert (⌜vn' = #0 ∧ Vn1 = V1⌝)%I with "[Pη]" as "{Pη} [-> ->]".
    { rewrite LinkRes_case_pure. iDestruct "Pη" as %CASE. iPureIntro.
      destruct CASE as [[-> ->]|(?&?&?&?&->&->&_)].
      - rewrite lookup_insert in Eqtn1. clear -Eqtn1. by inversion Eqtn1.
      - rewrite lookup_insert_ne in Eqtn1; last lia.
        rewrite lookup_insert in Eqtn1. clear -Eqtn1. by inversion Eqtn1. }
    wp_op. wp_if.

    (* finishing *)
    iApply "Post". iRight. iExists n. iSplit ;[done|]. rewrite shift_0.
    iExists η, _, _, _. by iFrame "GS0 LS LTs SE'".

  - (* reads non-null, reset tail *)
    (* get the fact that the read value is non-null *)
    rewrite LinkRes_unfold. iDestruct "Pη" as "[Eq|Pη]".
    { iDestruct "Eq" as %[-> ->]. exfalso. clear -Eqtn1 NEqt1.
      by apply lookup_singleton_Some in Eqtn1 as []. }
    iDestruct "Pη" as (η1 l1 Vv1 eid v1 (?&?&Eqη1)) "Pη". subst ηs ζ1.
    assert (tn' = (t1 + 1)%positive).
    { case (decide (tn' = (t1 + 1)%positive)) => [//|?].
      rewrite lookup_insert_ne // in Eqtn1.
      by apply lookup_singleton_Some in Eqtn1 as [? _]. } subst tn'.
    rewrite lookup_insert in Eqtn1. inversion Eqtn1. subst vn' Vn1. clear Eqtn1.
    iDestruct (view_at_elim with "[] Pη") as "(SEv1 & LVη1 & _) {SNη' Pη}".
    { iApply (monPred_in_mono with "sV3"). simpl. clear -LeV''. solve_lat. }

    have Eqi1 : CL1 !! (i + 1)%nat = Some (η1, l1).
    { by apply infos_next_lookup in Eqd as (?&?&?). } clear Eqd infos1.
    have ADJ : adjacent_in η η1 CL1.*1.
    { exists i. by rewrite 2!list_lookup_fmap Eqη Eqi1. }

    wp_op. wp_if. wp_op. wp_bind (_ <-ʳᵉˡ _)%E.

    iAssert (SeenEnqueuedLink_val E1 T1 CL1 η1 l1)%I with "[]" as "SL1".
    { rewrite /SeenEnqueuedLink_val /SeenEnqueuedLink /=.
      iExists Vv1. iFrame "LVη1". iSplit.
      - case decide => ?. { iApply (seen_enqueued_val_seen_view with "SEv1"). }
        iExists eid, η, v1.
        iDestruct (seen_enqueued_val_map_mono with "SEv1") as "$"; done.
      - iPureIntro. apply elem_of_list_lookup. by eexists. }

    iDestruct (view_at_intro with "SL1") as (Vl') "[InVl' SL']".

    (* prepare to reset tail *)
    iInv "QII" as (Q2 G2) ">[GMA QBI]" "Close".
    iDestruct (QueueBaseInv_unfold_snap_2 with "QBI LS1 LT1")
      as (D2 L2 T2) "[QBI LE]". iDestruct "LE" as %(LeCL1 & LeDL1 & LeLT).
    set E2 := G2.(Es).
    iDestruct (QueueInv_graph_snap_included with "GMA GS1") as %SUBE'.
    have SUBE: E1 ⊑ E2 by apply SUBE'. clear SUBE'.
    (* get Tail *)
    iDestruct (QueueInv_no_exist_tail_access with "QBI") as (Vb ζl0) "[[T Tls] QIC]".

    wp_apply (AtomicSeen_concurrent_write _ _ _ _ _ _ ∅ _ _ #l1
                with "[$Snζ'' $T $InVl']"); [done|solve_ndisj|done|..].

    iIntros (tl V4 V4') "(F4 & #sV4 & _ & T')".
    iDestruct "F4" as %(? & FRtl & LeVl' & ? & ? & ->).

    (* close the invariant *)
    iMod ("Close" with "[-Post]") as "_".
    { iNext. iExists _, _. iFrame "GMA". iExists _, _, D2, L2, T2.
      have ? : Vb ⊑ Vb ⊔ V4 by clear; solve_lat.
      iApply ("QIC" with "[$T' Tls]").
      rewrite -Tail_insert. iSplitL "Tls"; [by iFrame|]. (* TODO frame instance *)
      rewrite view_at_view_at. iApply (view_at_mono with "SL'"); [done|].
      by apply (SeenEnqueuedLink_val_mono E1 E2 T1 T2). }

    (* finishing *)
    iIntros "!>". wp_seq. iApply "Post". by iLeft.
Qed.

Lemma find_tail_repeat_spec N (DISJ: N ## histN) γ γh γl γg q tid :
  {{{ (∃ ζl, (q >> tail) sn⊒{γl} ζl) ∗ InternInv N γ γh γl γg q }}}
      (repeat: (find_tail [ #q])) @ tid; ⊤
  {{{ (l : loc), RET #l;
        ∃ η' G T L,
        graph_snap γg G ∅ ∗ LTM_snapv γ T ∗ LEL_snapv γ L ∗
        SeenEnqueuedLink_val G.(Es) T L η' (l >> link) }}}.
Proof.
  iIntros (Φ) "#T Post".
  iLöb as "IH". wp_rec.
  wp_apply (find_tail_spec with "T"); [done|].
  iIntros (n) "[%|P]".
  - subst n. wp_let. wp_op. wp_if. by iApply ("IH" with "Post").
  - iClear "#". iDestruct "P" as (l ?) "P".
    subst n. wp_let. wp_op. wp_if. by iApply "Post".
Qed.

End irc_proof.

Section proof.
Context `{!noprolG Σ, !msqueueG Σ, !atomicG Σ}.
Local Existing Instances msq_graphG msq_queueG msq_absG.

#[local] Notation iProp := (iProp Σ).
#[local] Notation vProp := (vProp Σ).

Lemma QueueInv_StrongQueueConsistent_instance :
  ∀ γg q Q G, QueueInv γg q Q G ⊢ ⌜ StrongQueueConsistent G ⌝.
Proof. by iIntros "* [$ QI]". Qed.

Lemma QueueInv_graph_master_acc_instance :
  ∀ γg q Q G, QueueInv γg q Q G ⊢
    graph_master γg (1/2) G ∗
    (graph_master γg (1/2) G -∗ QueueInv γg q Q G).
Proof. by iIntros "* ($ & $ & $) $". Qed.

Lemma QueueLocal_graph_snap_instance :
  ∀ N γg q G M, QueueLocal N γg q G M ⊢ graph_snap γg G M.
Proof. by iIntros "* [$ _]". Qed.

Lemma new_queue_spec :
  new_queue_spec' new_queue QueueLocal QueueInv.
Proof.
  iIntros (N tid Φ) "_ Post".
  wp_lam.
  (* allocate first node *)
  wp_apply wp_new; [done..|].
  iIntros (s) "([Hs†|%] & Hs & Hms)"; [|done].
  wp_let. wp_op. rewrite shift_0. rewrite own_loc_na_vec_singleton.

  (* initialize the sentinnel node *)
  wp_write.
  iMod (AtomicPtsTo_CON_from_na with "Hs") as (ηs ts Vs) "(#sVs & #SNs & ATs)".
  (* allocate ghost graphs *)
  iMod (Maps_master_alloc [(ηs,s)] [] ∅) as (γ) "(LELm & LDLm & LTm)".
  iDestruct (LEL_master_fork with "LELm") as "#LELs".
  iDestruct (LDL_master_fork with "LDLm") as "#LDLs".
  iDestruct (LTM_master_fork with "LTm") as "#LTs".
  iMod (own_alloc (to_frac_agree 1 ([] : leibnizO queue))) as (γa) "QA"; [done|].
  rewrite -{2}Qp.half_half (frac_agree_op (1/2) (1/2)).
  iDestruct "QA" as "[QA1 QA2]".
  iMod graph_master_alloc_empty as (γg) "([GM1 GM2] & #Gs)".

  iAssert (link_val ηs s Vs 0) as "#LVs0".
  { iExists Vs, _. iFrame "SNs". iPureIntro. split; [done|].
    exists ts. by apply lookup_singleton. }
  iAssert (SeenEnqueuedLink_val ∅ ∅ [(ηs, s)] ηs s)%I as "SNs0".
  { rewrite /SeenEnqueuedLink_val /SeenEnqueuedLink.
    iExists Vs. rewrite decide_True //. iFrame "sVs LVs0".
    iPureIntro; by apply elem_of_list_singleton. }

  (* allocate head & tail *)
  wp_apply wp_new; [done..|]. iIntros (q) "([Hq†|%] & Hq & Hmq & _)"; [|done].
  rewrite own_loc_na_vec_cons own_loc_na_vec_singleton.
  iDestruct "Hq" as "[Hh Ht]".
  wp_let. wp_op. rewrite shift_0.

  (* initialize head *)
  wp_write.
  iMod (AtomicPtsTo_CON_from_na_rel with "SNs0 Hh") (* publish SNs0 with Head *)
    as (γh th Vh) "(#sVh & #SNs1 & SNh & ATh)".

  wp_op. iApply wp_fupd.
  (* initialize tail *)
  wp_write.
  iMod (AtomicPtsTo_CON_from_na_rel with "sVh Ht")
    as (γl tl Vl) "(sVt & %LeVhl & SNt & ATt)".

  iMod (meta_set _ _ γa nroot with "Hmq") as "#Hmq"; [done|].

  have QC0 := StrongQueueConsistent_empty.

  iMod (inv_alloc (msqN N q) _ (QueueInternalInv γ γh γl γg q)
           with "[ATs ATh ATt QA1 GM1 LELm LDLm LTm]") as "#I".
  { iNext. iExists [], ∅. iFrame (QC0) "GM1".
    iSplitL "QA1". { iExists _. iFrame "Hmq QA1". }
    iExists ηs, s, [], [], ∅. iFrame "LELm LDLm LTm". iSplit; last iSplitL "".
    { iPureIntro. split;
        [by apply NoDup_singleton|done|intros ?; naive_solver|done..]. }
    { by iIntros (??????[]). }
    iDestruct (view_at_intro with "[-]") as (Vb) "[InVb P]"; last first.
    { iExists Vb. iExact "P". }
    iSplitL "ATh"; last iSplitL "ATt".
    - iExists th, [Vh]. rewrite shift_0.
      rewrite /toHeadHist /toHeadHist' /Head /= insert_empty.
      by iFrame "ATh SNs1".
    - iExists _. iFrame "ATt". rewrite /Tail.
      iIntros (t v V [<- ?]%lookup_singleton_Some). simplify_eq.
      iExists s. iSplit; [done|]. iExists _. by iFrame "SNs1".
    - rewrite /own_nodes /=. iSplit; [|done]. iExists _, _, _. by iFrame "ATs". }

  iIntros "!>". iApply ("Post" $! γg).
  iSplitL "SNh SNt".
  - (* QueueLocal *)
    iSplitL "Gs". { by iApply (graph_snap_empty with "Gs"). }
    iExists γ, γh, γl. iFrame "I". iExists ηs, s, [], [], [], ∅. simpl.
    iSplit; [done|]. iFrame "LELs LDLs LTs".
    iSplitL "SNh"; last iSplitL "SNt"; last iSplit; last iSplit.
    + iExists th, [Vh]. rewrite shift_0.
      rewrite /toHeadHist /toHeadHist' /= insert_empty. iFrame "SNh".
      iSplit; [|done]. by iApply (link_val_0_0 with "LVs0").
    + by iExists _.
    + iPureIntro. split; last split; last split;
          [by apply NoDup_singleton|done|intros ?; naive_solver|done..].
    + by iIntros (???? [??]).
    + by rewrite -SeenLogview_empty.
  - (* QueueInv *) iFrame (QC0) "GM2". iExists _. iFrame "Hmq QA2".
Qed.

Lemma try_enq_spec :
  try_enq_spec' try_enq QueueLocal QueueInv.
Proof.
  intros N DISJ q tid γg G1 M V v Posx.
  iIntros "#sV #[Gs QSI]" (Φ) "AU". iDestruct "QSI" as (γ γh γl) "[QS QII]".
  iDestruct "QS" as (ηs s D1 L1 D0 T1 SubD0)
    "(Hl & Tl & LS1 & LD1 & LT1 & F & LSeen & LSync)".
  iDestruct "F" as %(ND11 & DT1 & CDT1 & InjT1 & ET1 & SYE1).
  set E1 := G1.(Es).
  (* allocate a node *)
  wp_lam. wp_apply (wp_new with "[//]"); [done..|].
  iIntros (n) "([H†|%] & Hn & Hmn)"; [|done].
  iDestruct (own_loc_na_vec_cons with "Hn") as "[oL oD]".
  rewrite own_loc_na_vec_singleton.

  (* write data and link *)
  wp_let. wp_op. wp_write. wp_op. rewrite !shift_0. wp_write.

  (* repeat loop to find tail *)
  wp_apply (find_tail_repeat_spec with "[$Tl $QII]"); [done|].

  (* found tail is (η',l') *)
  iIntros (l'). iDestruct 1 as (η' G' T' L') "#(Eη' & Tη' & Lη' & SNη')".
  rewrite shift_0 /SeenEnqueuedLink_val. iDestruct "SNη'" as (V0) "[SLη' SNη']".
  iDestruct (SeenEnqueuedLink_seen_view with "SLη'") as "#sV0".
  iDestruct "SNη'" as (InL' V0' ζl0) "[(%LeV0 & %t0 & %EqV0) SNη']".
  set E' := G'.(Es).

  wp_let. wp_op. rewrite shift_0.
  (* CAS to replace l' link *)
  wp_bind (CAS _ _ _ _ _ _)%E.

  (* open invariant *)
  iInv "QII" as (Q2 G2) ">[GMA QBI]" "Close".
  iDestruct (QueueBaseInv_unfold_snap_2 with "QBI LS1 LT1") as (D2 L2 T2) "[QBI LE]".
  iDestruct "LE" as %(LeCL1 & LeDL1 & LeT1).

  (* open ghost *)
  iMod "AU" as (Q2' G2') "[>GMA' HClose]".
  set E2 := G2.(Es).
  iDestruct (QueueInv_agree with "GMA GMA'") as %[-> ->].
  iDestruct (QueueInv_graph_snap_included with "GMA Gs") as %InG1.
  have InE1 : E1 ⊑ E2 by apply InG1.
  iDestruct (QueueInv_consistent with "GMA") as %[CON EGCs].
  iDestruct (QueueInv_graph_snap_included with "GMA Eη'") as %InGη.
  have InEη' : E' ⊑ E2 by apply InGη. clear InGη.

  iDestruct "QBI" as "(LM & LD & LTm & %QP & Views & QLs)".
  iDestruct "QLs" as (Vb) "(H & T & Ns)".
  assert (QP0 := QP). destruct QP as [ND21 DT CDT InjT ET MONO ORD ABS].

  iAssert (⌜ set_in_bound M E1 ⌝)%I with "[]" as %SubD1.
  { iDestruct "Gs" as "[_ SL1]". by iApply (SeenLogview_closed with "SL1"). }

  iDestruct (LDL_master_snap_included with "LD LD1") as %InLD1.
  iDestruct (LEL_master_snap_included with "LM Lη'") as %LeL'.
  iDestruct (LTM_master_snap_included with "LTm Tη'") as %LeT'.

  set CL1 := (ηs, s) :: D1 ++ L1.
  set CL2 := (ηs, s) :: D2 ++ L2.

  iDestruct (SeenLinked_logview_mono _ CL2 _ T2 _ E2 with "LSeen") as "LSeen'";
    [done..|].
  iDestruct (SeenLogview_map_mono _ E2 with "LSync") as "PSV"; [done..|].

  rewrite (own_nodes_access _ _ _ _ _ _ η' l'); last first.
  { by apply (elem_of_list_prefix _ _ _ LeL' InL'). }
  iDestruct "Ns" as (d' ηl1 i' [Eqi' Eqd']) "[Linkη' Ns]".
  iDestruct "Linkη'" as (t1 V1 ζ1) "[ATη' S1]".
  rewrite (view_at_objective_iff (LinkRes _ _ _ _ _ _ _ _ _)).
  iDestruct (LinkRes_comparable_0 with "S1") as %COMP0.

  iCombine "oL oD" as "CHUNK".
  iCombine "CHUNK PSV LSeen' Hl Tl" as "CHUNK {PSV LSeen LSync LSeen'}".
  (* use Vs as the current view, which is at least both V and V0 *)
  iDestruct (view_at_intro_incl _ (V ⊔ V0) with "CHUNK []")
    as (Vs) "(#InVs & %LeV & oLD & #PSV & #LSeen' & #Hl' & #Tl') {sV sV0}".
  { rewrite -monPred_in_view_op. by iFrame "sV sV0". }
  wp_apply (AtomicSeen_CON_CAS_int l' η' ζl0 ζ1 _ _ _ 0 #n tid ∅ Vs Vb
              with "[$SNη' $ATη' $InVs]"); [done..|solve_ndisj| |done|].
  { intros ???; apply COMP0. }

  iIntros (b t' v' Vr V'' ζ'' ζn) "(Fn & #SnV'' & #SNη'' & ATη' & CASE)".
  iDestruct "Fn" as %([SUB0 SUB''] & Eqt' & MAXt' & LeVs).

  have LeVV'' : V ⊑ V''. { clear -LeVs LeV. solve_lat. }
  have bLeVV'' : bool_decide (V ⊑ V'') by eapply bool_decide_unpack; eauto.
  set Venq : dataView := mkDView V V'' V'' bLeVV''.

  iDestruct "CASE" as "[[F _]|[F InV]]".
  { (* CAS failed *)
    iDestruct "F" as %(-> & NEq & ->).

    iDestruct (QueueInv_graph_snap with "GMA") as "#Gs'".
    iDestruct (LEL_master_fork with "LM") as "#Ls'".
    iDestruct (LDL_master_fork with "LD") as "#LD'".
    iDestruct (LTM_master_fork with "LTm") as "#LTs'".

    assert (SYE2 := SyncEnqueues_mono _ _ _ SubD1 InE1 SYE1).
    (* Close without updating. TODO: can be more a interesting FAIL *)
    rewrite bi.and_elim_r.
    iMod ("HClose" $! false V'' Q2 G2 dummy_eid dummy_qevt Venq M
            with "[$GMA' $SnV'']") as "HΦ {Gs' Ls' LD' LTs'}".
    { iSplitL; [|by iPureIntro]. iSplit.
      { iDestruct "Gs'" as "[$ _]". iFrame "PSV". }
      iExists γ, γh, γl. iFrame "QII". iExists ηs, s, D2, L2, D0, T2.
      iSplit. { iPureIntro. by etrans. }
      iFrame "Hl' Tl' Ls' LD' LTs'". iSplit; [done|]. iFrame "LSeen' PSV". }
    iIntros "!>".
    (* Close the invariant *)
    iMod ("Close" with "[-H† oLD HΦ]") as "_".
    { iNext. iExists Q2, G2. iFrame "GMA".
      iExists ηs, s, D2, L2, T2. iFrame "LM LD LTm Views". iSplitR; [done|].
      iExists (Vb ⊔ V''). iFrame "H T". iClear "#". rewrite bi.and_elim_l.
      (* return resources *)
      iApply (view_at_mono_2 with "Ns"); [solve_lat|].
      iExists _, _, _. by iFrame. }

    iIntros "!>". wp_if.
    iDestruct (view_at_elim with "InVs oLD") as "[oL oD]".
    wp_apply (wp_delete _ tid 2 _ [ #0; #v] with "[H† oL oD]"); [done|done|..].
    { rewrite own_loc_na_vec_cons own_loc_na_vec_singleton. iFrame "oL oD".
      iLeft. by iFrame. }
    iIntros "_ {#}". wp_seq. by iApply "HΦ".
  }

  (* CAS succeeds. *)
  iDestruct "F" as %[-> ->].
  iDestruct "InV" as (Vw (FRt & Eqζn & Eqζ'' & LeVr1 & ? & ? & NEqV'' & EqVw))
    "[_ %LeVr2]". simpl in EqVw. subst Vw. clear COMP0.

  assert (Eqtn' := lookup_weaken _ _ t' (#0, Vr) Eqt' SUB'').
  rewrite LinkRes_case_pure.
  iDestruct "S1" as %[[-> ->]|(?&?&?&?&->&->&_)]; last first.
  { exfalso. clear -Eqd' Eqt' Eqtn' FRt Eqζ'' Eqζn. subst ζn.
    rewrite lookup_insert_ne in Eqtn'; last lia.
    case (decide (t' = (t1 + 1)%positive)) => ?.
    + subst t'. rewrite lookup_insert in Eqtn'. by inversion Eqtn'.
    + rewrite lookup_insert_ne // in Eqtn'.
      apply lookup_singleton_Some in Eqtn' as []. simplify_eq.
      by rewrite lookup_insert in FRt. } clear FRt.
  rewrite Eqζn lookup_insert_ne in Eqtn'; last lia.
  apply lookup_singleton_Some in Eqtn' as [-> Eq'].
  inversion Eq'. clear Eq'. subst V1.

  assert (EQi': i' = (length CL2 - 1)%nat).
  { clear -Eqd'. apply lookup_zip_with_Some in Eqd' as (x & b & ? & Eq1 & Eq2).
    simplify_eq. by apply next_nodes_lookup_None in Eq1 as []. }

  assert (t0 = t' ∧ V0' = Vr) as [-> ->].
  { clear -SUB0 SUB'' EqV0 Eqζn.
    apply (lookup_weaken _ ζn) in EqV0; last by etrans.
    subst ζn.
    case (decide (t0 = (t' + 1)%positive)) => ?.
    - exfalso. subst t0. rewrite lookup_insert in EqV0. by simplify_eq.
    - rewrite lookup_insert_ne // in EqV0.
      apply lookup_singleton_Some in EqV0 as []. by simplify_eq. }

  (* initialize atomic for n *)
  iDestruct "oLD" as "[oL oD]".
  rewrite (AtomicPtsTo_CON_from_na_cofinite_rel
            n #0 (list_to_set CL2.*1) ((n >> 1) ↦{1} #v)%I).
  iMod ("oD" with "oL") as (η tn Vn FRη) "(%LeVn & oD & #SNn & ATn)".
  rewrite ->elem_of_list_to_set in FRη. rewrite view_at_view_at.

  set Mη' : gset event_id :=
    if T2 !! η' is Some e'
    then if E2 !! e' is Some eV' then eV'.(ge_lview) else ∅
    else ∅.

  set Q2' := Q2 ++ [(v, Venq.(dv_wrt))].
  set enqId := length G2.(Es).
  set Ms' := Mη' ∪ {[enqId]}.
  set M' := M ⊔ Ms'.
  set enqE := mkGraphEvent (Enq v) Venq M'.
  set G2' : graph := graph_insert_event enqE G2.

  assert (GIPE := graph_insert_event_eq enqE G2). rewrite -/G2' in GIPE.
  destruct GIPE as (LeG' & EqGs' & EqSo' & EqCo').
  set E2' := G2'.(Es).
  set T2' := <[η:=enqId]> T2.
  set CL2' := (ηs, s) :: D2 ++ L2 ++ [(η,n)].
  have SubE2': E2 ⊑ E2' by apply LeG'.
  have SubM' : M ⊑ M' by clear; solve_lat.
  have Inenq : enqId ∈ M' by clear; set_solver.

  have Subη' : set_in_bound Mη' E2.
  { rewrite /Mη'.
    destruct (T2 !! η') as [e'|] eqn:Eqe'; [|done].
    destruct (CDT e') as [[v' Eqv'] _]. { by exists η'. }
    destruct (E2 !! e') as [eV'|] eqn:Eqm'; [|done].
    by apply (egcons_logview_closed _ EGCs _ _ Eqm'). }
  have FReη' : enqId ∉ Mη'.
  { clear -Subη'. intros Lt%Subη'%lookup_lt_is_Some. rewrite /enqId /E2 /= in Lt. lia. }
  have SubM : set_in_bound M E2. { by eapply set_in_bound_mono; [|exact SubD1]. }
  have FReM : enqId ∉ M. { clear -SubM. intros ?%SubM%lookup_lt_is_Some. subst E2. lia. }
  have Sub': set_in_bound M' E2'.
  { apply set_in_bound_union; last apply set_in_bound_union.
    - by eapply set_in_bound_mono.
    - by eapply set_in_bound_mono.
    - intros ? ->%elem_of_singleton. rewrite lookup_app_1_eq. by eexists. }

  have EGCs' : eventgraph_consistent G2'.
  { constructor.
    - move => e1 e2 InGF.
      destruct (egcons_so _ EGCs _ _ InGF) as (eV1 & eV2 & Eq1 & Eq2 & Le12).
      destruct (gcons_so_included G2 _ InGF) as [In1 In2].
      exists eV1, eV2.
      split; last split; last done; rewrite lookup_app_1_ne //.
      + clear -In1. intros ->. simpl in In1. lia.
      + clear -In2. intros ->. simpl in In2. lia.
    - move => e eV. case (decide (enqId = e)) => ?.
      + subst e. rewrite lookup_app_1_eq => [[<-//]].
      + rewrite lookup_app_1_ne; [apply EGCs|done].
    - intros e' eV'. case (decide (enqId = e')) => ?.
      + subst e'. rewrite lookup_app_1_eq => [[<-//]].
      + rewrite lookup_app_1_ne; [|done] =>/(egcons_logview_closed _ EGCs).
        by apply set_in_bound_mono. }

  have FRηT: η ∉ dom T2.
  { rewrite DT elem_of_list_to_set => ?. apply FRη. by right. }
  have SubT2: T2 ⊆ T2'.
  { by apply insert_subseteq, (not_elem_of_dom (D:=gset gname)). }
  have EqCL2' : CL2' = CL2 ++ [(η, n)].
  { clear. by simplify_list_eq. }
  have SubCL2 : CL2 ⊑ CL2' by eexists.

  assert (∃ L'', L' = (ηs, s) :: L'') as [L'' ->].
  { clear -InL' LeL'.
    destruct L'; first by apply not_elem_of_nil in InL'.
    apply prefix_cons_inv_1 in LeL'. subst n. by eexists. }

  have LeE2': E' ⊑ E2' by etrans.
  iAssert (@{V''} SeenLogview E2' Mη' ∧ ⌜ SyncEnqueues E2' Mη' ⌝)%I
    with "[]" as "[#PSMη' %SYMη']".
  { rewrite /Mη'.
    destruct (T2 !! η') as [e|] eqn:Eqη'; last by rewrite -SeenLogview_empty.
    have ?: η' ≠ ηs.
    { clear -Eqη' DT ND21. intros ?. subst η'.
      rewrite fmap_cons in ND21. apply NoDup_cons in ND21 as [NIN _].
      apply NIN. apply (elem_of_list_to_set (C:=gset _)). rewrite -DT.
      move : Eqη'. apply elem_of_dom_2. }
    rewrite /SeenEnqueuedLink decide_False; last done.
    iDestruct "SLη'" as (e' η0 v0 [Eq1' Eq2'] eV' (Eqev & EqeV & SYE') EqeV2') "[PSV' _]".
    assert (Eqe' := lookup_weaken _ _ _ _ Eq2' LeT').
    rewrite Eqη' in Eqe'. inversion Eqe'; clear Eqe'; subst e'.
    assert (EqeV' := prefix_lookup_Some _ _ _ _ EqeV2' InEη'). rewrite EqeV' EqeV. iSplit.
    - iApply (view_at_mono with "PSV'").
      + clear -LeV LeVs. solve_lat.
      + by apply SeenLogview_map_mono.
    - rewrite (SeenLogview_closed E'). iDestruct "PSV'" as %Closed.
      iPureIntro. move : SYE'. by apply SyncEnqueues_mono. }

  iAssert (@{V''} SeenLogview E2' M')%I with "[]" as "#PSV'".
  { rewrite /M' -2!SeenLogview_union'. iSplit; last iSplit.
    - iApply (view_at_mono with "PSV"); [done|].
      by apply SeenLogview_map_mono.
    - iFrame "PSMη'".
    - rewrite -SeenLogview_singleton; [|by rewrite lookup_app_1_eq]. done. }

  have SYE' : SyncEnqueues E2' M'. {
    intros ex vx Vx lVx. rewrite !elem_of_union elem_of_singleton.
    intros [InM|[InM'| ->]].
    - intros Eq'. etrans; first apply (SYE1 ex vx Vx lVx InM); [|done].
      apply (prefix_lookup_inv _ E2'); [done|apply SubD1, InM|by etrans].
    - intros Sub%(SYMη' _ _ _ _ InM'). etrans; [exact Sub|set_solver-].
    - rewrite lookup_app_1_eq. by inversion 1. }

  iAssert (@{V''} seen_enqueued_val E2' enqId v V'')%I with "[]" as "#SEV2'".
  { iExists enqE. iFrame "PSV'".
    iSplit; last iSplit; iPureIntro; [done|by rewrite lookup_app_1_eq|done]. }
  iAssert (@{V''} link_val η' l' V'' n)%I with "[]" as "#LVη'".
  { iExists V'', _. iFrame "SNη''".
    iPureIntro. split; [done|]. by exists (t' + 1)%positive. }
  iAssert (@{V''} SeenLinked E2' T2' CL2' η' l' V'' enqId η n v)%I with "[]"
    as "#SLη".
  { have EqCL1 : CL2' !! (length CL2 - 1 + 1)%nat = Some (η,n).
    { rewrite EqCL2' lookup_app_r.
      + rewrite Nat.sub_add; last by (clear; simpl; lia).
        by rewrite Nat.sub_diag.
      + rewrite Nat.sub_add //. clear; simpl; lia. }
    have EqCL2 : CL2' !! (length CL2 - 1)%nat = Some (η',l').
    { rewrite EqCL2' lookup_app_l.
      + by rewrite -EQi'. + clear; simpl; lia. }
    iSplitL ""; [iSplitL ""|iFrame "LVη'"]; [|iFrame "SEV2'"|]; iPureIntro; split.
    - exists (length CL2 - 1)%nat. by rewrite 2!list_lookup_fmap EqCL1 EqCL2.
    - by rewrite lookup_insert.
    - move : EqCL2. apply elem_of_list_lookup_2.
    - move : EqCL1. apply elem_of_list_lookup_2. }

  iAssert (∀ e, ⌜ e ∈ Mη' ⌝ → ∃ e' eV',
            ⌜ E2 !! e' = Some eV' ∧ eV'.(ge_view).(dv_comm) = V0 ∧
              SyncEnqueues E' eV'.(ge_lview) ∧
              Mη' = eV'.(ge_lview) ⌝
            ∗ @{V0} SeenLogview E' eV'.(ge_lview))%I with "[SLη']" as "#Inη'".
  { iIntros (e Ine). rewrite /Mη' in Ine.
    have ?: η' ≠ ηs.
    { clear -Ine DT ND21. intros ?. subst η'.
      move : Ine. rewrite (_ : T2 !! ηs = None); first done.
      apply (not_elem_of_dom (D:=gset lnode)). rewrite DT elem_of_list_to_set.
      rewrite fmap_cons in ND21. by apply NoDup_cons in ND21 as []. }
    rewrite /SeenEnqueuedLink decide_False; last done.
    iDestruct "SLη'" as (e' η0 v0 [Eq1' Eq2'] eV' (Eqev & EqeV & SYE) EqeV2') "[PSV'' _]".
    iExists e', eV'. rewrite EqeV. iFrame "PSV''". iPureIntro.
    assert (Eqe' := lookup_weaken _ _ _ _ Eq2' LeT').
    assert (EqeV' := prefix_lookup_Some _ _ _ _ EqeV2' InEη').
    do 3 (split; [done|]). by rewrite /Mη' Eqe' EqeV'. }

  iAssert (@{V''} SeenLinked_logview CL2' T2' E2' M')%I
    with "[Views]" as "#LSn'".
  { iIntros (e2 v2 V2 lV2 [Ine2 Enqe2]).
    move : Ine2. rewrite !elem_of_union elem_of_singleton.
    intros [Ine2|[Ine2|?]].
    - have NEq2 : enqId ≠ e2.
      { intros <-. apply SubD1, lookup_lt_is_Some in Ine2. clear -InE1 Ine2.
        apply prefix_length in InE1. subst enqId E1 E2. lia. }
      rewrite lookup_app_1_ne in Enqe2; [|done].
      iDestruct ("LSeen'" $! e2 with "[//]") as (η0 l0 η1 l1) "SL".
      iExists η0, l0, η1, l1.
      clear -SubE2' SubT2 SubCL2 LeVs.
      iApply (view_at_mono with "SL"); [done|]. by apply SeenLinked_mono.
    - have NEqe2: enqId ≠ e2.
      { intros <-. apply Subη', lookup_lt_is_Some in Ine2.
        clear -Ine2. subst enqId E2; lia. }
      rewrite lookup_app_1_ne in Enqe2; [|done].
      iSpecialize ("Inη'" $! e2 with "[%//]").
      iDestruct "Inη'" as (e' eV' (EqeV' & EqeVV' & SYE &->)) "_".
      iDestruct ("Views" $! e' eV'.(ge_event) eV'.(ge_view) eV'.(ge_lview)
                  with "[%]") as "SL2".
      { clear -EqeV'. by destruct eV'. } rewrite EqeVV'.
      iDestruct ("SL2" $! e2 v2 V2 lV2 with "[%//]") as "SL2".
      iApply (view_at_mono with "SL2"). { clear -LeV LeVs; solve_lat. }
      iDestruct 1 as (ηx lx ηy ly) "H". iExists ηx, lx, ηy, ly.
      clear -SubE2' SubT2 SubCL2.
      by iApply (SeenLinked_mono E2 E2' T2 T2' CL2 CL2' with "H").
    - subst e2. rewrite lookup_app_1_eq /= in Enqe2. inversion Enqe2.
      subst v2 V2 lV2. clear Enqe2.
      iExists η', l', η, n. iFrame "SLη". }

  have ND21' : NoDup CL2'.*1.
  { clear -FRη ND21 EqCL2'. rewrite EqCL2' fmap_app.
    apply NoDup_app. split; [done|]. split; [|apply NoDup_singleton].
    intros η' ? Eq%elem_of_list_singleton. simpl in Eq. subst η'. by apply FRη. }
  have DT' : dom T2' ≡ list_to_set (D2 ++ L2 ++ [(η,n)]).*1.
  { by rewrite dom_insert DT app_assoc (fmap_app _ (D2 ++ L2)) /=
                (list_to_set_app_L (D2 ++ L2).*1) /= right_id_L comm_L. }
  have CDT' : EM_equiv T2' E2'.
  { intros e. case (decide (enqId = e)) => ?.
    - subst e. clear. rewrite lookup_app_1_eq. split; intros.
      + naive_solver. + exists η; by rewrite lookup_insert.
    - rewrite lookup_app_1_ne; [|done]. split; intros Eq.
      * apply CDT. destruct Eq as [η0 Eq]. exists η0.
        have ?: η0 ≠ η.
        { intros ?. subst η0.
          rewrite lookup_insert in Eq. by inversion Eq. }
        by rewrite lookup_insert_ne in Eq.
      * apply CDT in Eq as [η0 Eq]. exists η0. rewrite lookup_insert_ne //.
        intros ?. subst η0. by eapply FRηT, elem_of_dom_2. }
  have ET' :
    ∀ η0 (e : event_id), T2' !! η0 = Some e → η0 ∈ D2.*1 ↔ e ∈ (elements G2'.(so)).*1.
  { intros η0 e Eqe. case (decide (η0 = η)) => ?.
    - subst η0. rewrite lookup_insert in Eqe. inversion Eqe. subst e.
      split; intros InD; exfalso.
      + apply FRη. rewrite /CL2 fmap_cons fmap_app elem_of_cons elem_of_app.
        by right; left.
      + apply elem_of_list_fmap in InD as [[x y] InD]. simpl in InD.
        destruct InD as [? [InG _]%elem_of_elements%gcons_so_included]. subst x.
        clear -InG. simpl in InG. lia.
    - move : Eqe. rewrite lookup_insert_ne //. by apply ET. }
  have InjT' :
    ∀ η1 η2 (e : event_id), T2' !! η1 = Some e → T2' !! η2 = Some e → η1 = η2.
  { intros η1 η2 e.
    case (decide (η1 = η)) => ?;
      [subst η1; rewrite lookup_insert => [[<-]]| rewrite lookup_insert_ne//];
      (case (decide (η2 = η)) => ?;
        [subst η2; rewrite lookup_insert //|rewrite lookup_insert_ne //]).
    - intros Eqη. exfalso.
      destruct (CDT enqId) as [[v2 Eq2] _]. { by exists η2. } clear -Eq2.
      apply list_lookup_fmap_inv' in Eq2 as (? &? & Eqe%lookup_lt_Some). lia.
    - intros Eqη. inversion 1; subst e. exfalso.
      destruct (CDT enqId) as [[v2 Eq2] _]. { by exists η1. } clear -Eq2.
      apply list_lookup_fmap_inv' in Eq2 as (? &? & Eqe%lookup_lt_Some). lia.
    - apply InjT. }
  have MONO' : ∀ η1 η2 (e1 e2: event_id),
    list_before (D2 ++ L2 ++ [(η,n)]).*1 η1 η2 →
    T2' !! η1 = Some e1 → T2' !! η2 = Some e2 → (e1 ≤ e2)%nat.
  { intros η1 η2 e1 e2 LB.
    case (decide (η = η1)) => [?|NEq1];
      [subst η1; rewrite lookup_insert => [[<-]]
      |rewrite lookup_insert_ne; last done];
      (case (decide (η = η2)) => [?|NEq2];
        [subst η2; rewrite lookup_insert|rewrite lookup_insert_ne; last done]).
    - by move => [<-].
    - clear -FRη NEq2 LB. exfalso.
      destruct LB as (i & j & ([η' n'] & ? & Eqi)%list_lookup_fmap_inv &
                              ([η2' n2] & ? & Eqj)%list_lookup_fmap_inv & Leij).
      simplify_eq.
      rewrite app_assoc in Eqi, Eqj.
      apply lookup_app_Some in Eqi as [Eqi|[LTi Eqi]].
      { apply FRη. rewrite fmap_cons /=. right. apply elem_of_list_lookup.
        exists i. by rewrite list_lookup_fmap Eqi. }
      have ? : i = length (D2 ++ L2).
      { clear -LTi Eqi. apply lookup_lt_Some in Eqi. simpl in Eqi.
        apply Nat.lt_sub_lt_add_r in Eqi.
        rewrite Nat.lt_succ_r in Eqi.
        by apply : (anti_symm (le)). } subst i.
      rewrite lookup_app_r in Eqj; [|done].
      have ? : j = length (D2 ++ L2).
      { apply lookup_lt_Some in Eqj. simpl in Eqj. by lia. } subst j.
      rewrite /= Nat.sub_diag /= in Eqj. by inversion Eqj.
    - move => Eq1 [<-]. apply Nat.lt_le_incl.
      destruct (CDT e1) as [[v1 Eqv1] _]. { by exists η1. }
      by apply list_lookup_fmap_inv' in Eqv1 as (? &? & Eqe%lookup_lt_Some).
    - intros EqT1 EqT2. apply (MONO η1 η2); [|done..].
      clear -LB NEq1 NEq2.
      destruct LB as (i & j & ([η' n'] & ? & Eqi)%list_lookup_fmap_inv &
                              ([η2' n2] & ? & Eqj)%list_lookup_fmap_inv & Leij).
      simplify_eq. simpl in *.
      exists i, j. rewrite app_assoc in Eqi, Eqj.
      repeat split; [..|done].
      + rewrite list_lookup_fmap -(lookup_app_l _ [(η,n)]); [by rewrite Eqi|].
        have LTi : (i ≤ length (D2 ++ L2))%nat.
        { apply Nat.lt_succ_r. apply lookup_lt_Some in Eqi.
          rewrite app_length /= in Eqi. by rewrite Nat.add_1_r in Eqi. }
        apply Nat.lt_eq_cases in LTi as [|LTi]; [done|]. exfalso.
        subst i. rewrite lookup_app_r in Eqi; [|done].
        rewrite /= Nat.sub_diag /= in Eqi. by inversion Eqi.
      + rewrite list_lookup_fmap -(lookup_app_l _ [(η,n)]); [by rewrite Eqj|].
        have LTj : (j ≤ length (D2 ++ L2))%nat.
        { apply Nat.lt_succ_r. apply lookup_lt_Some in Eqj.
          rewrite app_length /= in Eqj. by rewrite Nat.add_1_r in Eqj. }
        apply Nat.lt_eq_cases in LTj as [|LTj]; [done|]. exfalso.
        subst j. rewrite lookup_app_r in Eqj; [|done].
        rewrite /= Nat.sub_diag /= in Eqj. by inversion Eqj. }
  have ORD' : ∀ η1 η2 e1 e2 eV2, list_before (D2 ++ L2 ++ [(η,n)]).*1 η1 η2 →
              T2' !! η1 = Some e1 → T2' !! η2 = Some e2 →
              E2' !! e2 = Some eV2 → e1 ∈ eV2.(ge_lview).
  { intros η1 η2 e1 e2 eV2 LB.
    (* TODO: dups with MONO' *)
    case (decide (η = η1)) => [?|NEq1];
      [subst η1; rewrite lookup_insert => [[<-]]
      |rewrite lookup_insert_ne; last done];
      (case (decide (η = η2)) => [?|NEq2];
        [subst η2; rewrite lookup_insert|rewrite lookup_insert_ne; last done]).
    - move => [<-]. by rewrite lookup_app_1_eq => [[<-]].
    - clear -FRη NEq2 LB. exfalso.
      destruct LB as (i & j & ([η1 n1] & ? & Eqi)%list_lookup_fmap_inv &
                              ([η2' n2] & ? & Eqj)%list_lookup_fmap_inv & Leij).
      simplify_eq.
      rewrite app_assoc in Eqi, Eqj.
      apply lookup_app_Some in Eqi as [Eqi|[LTi Eqi]].
      { apply FRη. rewrite fmap_cons /=. right. apply elem_of_list_lookup.
        exists i. by rewrite list_lookup_fmap Eqi. }
      have ? : i = length (D2 ++ L2).
      { clear -LTi Eqi. apply lookup_lt_Some in Eqi. simpl in Eqi.
        apply Nat.lt_sub_lt_add_r in Eqi.
        rewrite Nat.lt_succ_r in Eqi.
        by apply : (anti_symm (le)). } subst i.
      rewrite lookup_app_r in Eqj; [|done].
      have ? : j = length (D2 ++ L2).
      { apply lookup_lt_Some in Eqj. simpl in Eqj. by lia. } subst j.
      rewrite /= Nat.sub_diag /= in Eqj. by inversion Eqj.
    - move => Eq1 [<-]. rewrite lookup_app_1_eq => [[<- /=]].
      rewrite app_assoc in LB.
      have LB': list_before (D2 ++ L2).*1 η1 η'.
      { clear -LB NEq1 Eqi' EQi'.
        destruct LB as (i & j & ([ηi ni] & ? & Eqi)%list_lookup_fmap_inv &
                                ([η2' n2] & ? & Eqj)%list_lookup_fmap_inv & Leij).
        simplify_eq.
        have LTi := lookup_lt_Some _ _ _ Eqi.
        rewrite app_length Nat.add_1_r in LTi.
        rewrite Nat.lt_succ_r in LTi.
        apply Nat.lt_eq_cases in LTi as [LTi|Eqij].
        - rewrite lookup_app_l in Eqi; [|done].
          have Le1 : (1 ≤ length (D2 ++ L2))%nat.
          { destruct (D2 ++ L2); [done|simpl; by lia]. }
          exists i, (length (D2 ++ L2) - 1)%nat.
          rewrite !list_lookup_fmap Eqi /=. repeat split.
          + rewrite (lookup_app_r [(_,_)]) /= Nat.sub_0_r in Eqi'.
            * by rewrite Eqi'.
            * done.
          + by apply Nat.le_add_le_sub_l, Nat.le_succ_l.
        - exfalso. rewrite Eqij lookup_app_r in Eqi; [|done].
          rewrite Nat.sub_diag /= in Eqi. by inversion Eqi.
      }
      assert (∃ e', T2 !! η' = Some e') as [e' Eqe'].
      { apply (elem_of_dom (D:=gset lnode)).
        rewrite DT elem_of_list_to_set.
        (* TODO: list_before elem_of *)
        clear -LB'. destruct LB' as (_ & j & _ & ? & _).
        by eapply elem_of_list_lookup_2. }
      rewrite /M' /Ms' /Mη' Eqe'.
      destruct (CDT e') as [[v' Eqm'] _]. { by exists η'. }
      apply list_lookup_fmap_inv' in Eqm' as (? & _ & EqeV'). rewrite EqeV'.
      have Ine1 := ORD _ _ _ _ _ LB' Eq1 Eqe' EqeV'. clear -Ine1. set_solver.
    - intros EqT1 EqT2 Eqm. rewrite lookup_app_1_ne in Eqm; last first.
      { intros ?. subst e2.
        destruct (CDT enqId) as [[v2 Eq2] _]. { by exists η2. } clear -Eq2.
        apply list_lookup_fmap_inv' in Eq2 as (? & _ & ?%lookup_lt_Some). lia. }
      apply (ORD η1 η2 e1 e2); [|done..].
      clear -LB NEq1 NEq2.
      destruct LB as (i & j & ([η1' n1] & ? & Eqi)%list_lookup_fmap_inv &
                              ([η2' n2] & ? & Eqj)%list_lookup_fmap_inv & Leij).
      simplify_eq.
      exists i, j. rewrite app_assoc in Eqi, Eqj.
      (* TODO: duplicated proofs *)
      repeat split; [..|done].
      + rewrite list_lookup_fmap -(lookup_app_l _ [(η,n)]); [by rewrite Eqi|].
        have LTi : (i ≤ length (D2 ++ L2))%nat.
        { apply Nat.lt_succ_r.
          apply lookup_lt_Some in Eqi.
          by rewrite app_length /= Nat.add_1_r in Eqi. }
        apply Nat.lt_eq_cases in LTi as [|LTi]; [done|]. exfalso.
        subst i. rewrite lookup_app_r in Eqi; [|done].
        rewrite /= Nat.sub_diag /= in Eqi. by inversion Eqi.
      + rewrite list_lookup_fmap -(lookup_app_l _ [(η,n)]); [by rewrite Eqj|].
        have LTj : (j ≤ length (D2 ++ L2))%nat.
        { apply Nat.lt_succ_r.
          apply lookup_lt_Some in Eqj.
          by rewrite app_length /= Nat.add_1_r in Eqj. }
        apply Nat.lt_eq_cases in LTj as [|LTj]; [done|]. exfalso.
        subst j. rewrite lookup_app_r in Eqj; [|done].
        rewrite /= Nat.sub_diag /= in Eqj. by inversion Eqj.
  }

  have ABS' : Forall2 (λ '(v, V) '(η, _), ∃ e eV,
      T2' !! η = Some e ∧ G2'.(Es) !! e = Some eV ∧
      eV.(ge_event) = Enq v ∧ eV.(ge_view).(dv_comm) = V) Q2' (L2 ++ [(η,n)]).
  { apply Forall2_app.
    - eapply Forall2_impl; [done|]. intros [? ?] [? ?] (e & eV & ? & ? & ? & ?).
      exists e, eV. split_and!; [by eapply lookup_weaken|by eapply prefix_lookup_Some|done..].
    - constructor; [|constructor]. exists enqId, enqE.
      split_and!; [by apply lookup_insert|by apply lookup_app_1_eq|done..]. }

  have LeV'' : V ⊑ V''. { clear -LeVs LeV. by solve_lat. }
  assert (NI: ∀ e1 e2, (e1, e2) ∈ G2'.(com) → e1 ≠ enqId ∧ e2 ≠ enqId).
  { clear. move => ?? /(gcons_com_included G2) [/=]. lia. }
  have CON' : StrongQueueConsistent G2'.
  { destruct CON as [CONRA [CONw _ _ CON] CON7b].
    have CONRA' : graph_event_is_relacq G2'.(Es) (λ _, True).
    { clear -CONRA. by apply graph_insert_event_is_relacq. }
    have FIFO' : queue_FIFO_strong G2'.
    { (* 7b *)
      intros e1 v1 eV1 e2 d2 Eqe1 Eqv1 InG2 Le12.
      rewrite lookup_app_1_ne in Eqe1.
      + apply (CON7b _ _ _ _ _ Eqe1 Eqv1 InG2 Le12).
      + intros ->. rewrite EqCo' in InG2.
        apply (Nat.lt_irrefl enqId), (Nat.le_lt_trans _ e2 _ Le12),
              (gcons_com_included _ _ InG2). }
    constructor; [done| |done]. constructor.
    { clear -LeV LeVs NEqV'' CONw. apply graph_insert_event_is_writing; [done|].
      simpl. intros _ ->. apply NEqV''. apply : (anti_symm (⊑)); [done|solve_lat]. }
    { by apply graph_event_is_relacq_releasing_True. }
    { by apply graph_event_is_relacq_acquiring_True. }
    destruct CON as [CON0 CON2 CON3 CON4 CON5 CON6 CON7a _].
    have EC' : graph_xo_eco G2'.(Es).
    { (* 7a *)
      intros e1 e2 eV2 [Eq1|[-> <-]]%lookup_app_1.
      + by apply CON7a.
      + move => /= /Sub'. clear. intros Lt%lookup_lt_is_Some.
        rewrite app_length /= in Lt. lia. }
    constructor; [..|done|].
    - (* 1 *)
      intros ??? [Eq1|[-> <-]]%lookup_app_1; [by apply (CON0 _ _ _ Eq1)|].
      by move => /= [<-//].
    - (* 2 *)
      intros e1 e2 InG. destruct (NI _ _ InG).
      do 2 (rewrite lookup_app_1_ne; [|done]). by apply CON2.
    - (* 3a 3b *) done.
    - (* 4 *) intros ?? [?|[-> <-]]%lookup_app_1; [by eapply CON4|done].
    - (* 5 *)
      intros e eV Eqe Empe ee ve eVe Eqee Eqve Inee.
      have NEq: enqId ≠ e.
      { clear -Eqe Empe. intros <-. rewrite lookup_app_1_eq in Eqe.
        inversion Eqe. by subst eV. }
      rewrite lookup_app_1_ne in Eqe;[|done].
      apply (CON5 _ _ Eqe Empe ee ve eVe); [|done..].
      rewrite lookup_app_1_ne in Eqee; [done|].
      intros ->. apply (egcons_logview_closed _ EGCs _ _ Eqe),
                        lookup_lt_is_Some in Inee. clear -Inee. lia.
    - (* 6 *) done.
    - (* 7a *) by apply queue_FIFO_strong_FIFO. }

  iMod (QueueInv_update _ _ _ _ Q2' G2' LeG' EGCs' CON' with "GMA GMA'")
    as "(GMA & GMA' & #Gs')".
  iMod (LTM_update_insert _ _ η enqId FRηT with "LTm") as "[LTm' #LTs']".
  iMod (LEL_update_app _ _ [(η,n)] with "LM") as "[LM #LS']". rewrite -EqCL2'.
  iDestruct (LDL_master_fork with "LD") as "#LD'".
  iDestruct (LTM_master_fork with "LTm'") as "#LT'".

  (* COMMIT the AU *)
  rewrite bi.and_elim_r.
  iAssert (@{V''} graph_snap γg G2' M')%I as "#GS2'". { iFrame "Gs' PSV'". }
  iMod ("HClose" $! true V'' Q2' G2' enqId (Enq v) Venq M' with "[$GMA' $SnV'']")
    as "HΦ".
  { (* Public Post *)
    iSplitL; last by iPureIntro.
    (* QueueLocal *)
    iSplit. { iFrame "GS2'". }
    iExists γ, γh, γl. iFrame "QII". iExists ηs, s, D2, (L2 ++ [(η,n)]), D0, T2'.
    iSplit. { iPureIntro. by etrans. }
    iFrame "LS' LD' LT'". iSplitR. { iFrame "Hl'". } iSplitR. { iFrame "Tl'". }
    iSplit; [by iPureIntro|]. iSplitR; [iFrame "LSn'"|iFrame "PSV'"]. }
  iIntros "!>".
  (* close the invariant *)
  iMod ("Close" with "[Views H T Ns ATη' ATn oD GMA LTm' LM LD]") as "_".
  { iNext. iExists Q2', G2'. iFrame "GMA".
    iExists ηs, s, D2, (L2 ++ [(η, n)]), T2'. iFrame "LM LD LTm'".
    iSplit; [done|]. iSplitL "Views".
    { (* QueueViews *)
      iIntros (e1 ev1 V1 lV1 Eqe1).
      case (decide (e1 = enqId)) => ?.
      + subst e1. rewrite lookup_app_1_eq in Eqe1. inversion Eqe1. by iFrame "LSn'".
      + rewrite lookup_app_1_ne in Eqe1; [|done].
        iSpecialize ("Views" $! e1 ev1 V1 lV1 Eqe1).
        iApply (view_at_mono with "Views"); [done|].
        apply SeenLinked_logview_mono; [done..|].
        revert Eqe1. by apply (egcons_logview_closed _ EGCs). }
    iExists (Vb ⊔ V''). iSplitL "H"; last iSplitL "T".
    - (* Head : Head mono *)
      iClear "#". clear -SubE2' SubT2.
      iApply (view_at_mono with "H"); [solve_lat|].
      iDestruct 1 as (t0 Vs0) "[H Hs]".
      iExists t0, Vs0. iFrame "H". by iApply (Head_mono with "Hs").
    - (* Tail : Tail mono *)
      iClear "#". clear -SubE2' SubT2 SubCL2.
      iApply (view_at_mono with "T"); [solve_lat|].
      iDestruct 1 as (ζl) "[T Ts]".
      iExists ζl. iFrame "T". by iApply (Tail_mono with "Ts").
    - (* own_nodes append *)
      rewrite bi.and_elim_r.
      iSpecialize ("Ns" $! E2' T2' η n with "[%//]").
      iApply (view_at_mono_2 with "Ns [ATη' oD] [ATn]"); [solve_lat|..].
      { iExists t', Vr, _. iFrame "ATη'". rewrite /LinkRes.
        iExists V'', enqId, v. iSplit; last iSplit.
        - by iPureIntro.
        - iPureIntro. by rewrite lookup_insert.
        - rewrite view_at_view_at. iSplitL ""; first by iFrame "SEV2'". iSplit.
          + iExists Vn, _. iFrame "SNn". iPureIntro.
            split; [clear -LeVn LeVs; solve_lat|].
            exists tn. by rewrite lookup_insert.
          + destruct d'; [done|]. iFrame "oD". }
      rewrite /Link. iExists tn, Vn, _. iFrame "ATn". by iPureIntro. }

  iClear "Gs LS1 LD1 LT1". clear Vb.
  iIntros "!>".

  wp_if. wp_op.

  (* update tail *)
  wp_bind (_ <-ʳᵉˡ _)%E.
  (* prepare to reset tail *)
  iInv "QII" as (Q3 G3) ">[GMA QBI]" "Close".
  iDestruct (QueueBaseInv_unfold_snap_2 with "QBI LS' LT'") as (D3 L3 T3) "[QBI LE]".
  iDestruct "LE" as %(LeCL3 & LeDL3 & LeLT3).

  iDestruct (QueueInv_graph_snap_included_2 with "GMA GS2'") as %SUB.
  (* get Tail *)
  iDestruct (QueueInv_no_exist_tail_access with "QBI") as (Vb ζl1) "[[T Tls] QIC]".
  iDestruct "Tl" as (ζl'') "Snζ''".

  wp_apply (AtomicSeen_concurrent_write _ _ _ _ _ _ ∅ _ _ #n
              with "[$Snζ'' $T $SnV'']"); [done|solve_ndisj|done|..].

  iIntros (tl V4 V4') "(F4 & #sV4 & _ & T')".
  iDestruct "F4" as %(? & FRtl & LeVl' & ? & ? & ->).

  have NEqη : ηs ≠ η.
  { clear -FRη. intros ?. subst η. apply FRη. rewrite fmap_cons. by left. }

  (* close the invariant *)
  iMod ("Close" with "[-HΦ H†]") as "_".
  { iNext. iExists _, _. iFrame "GMA".
    iExists _, _, D3, L3, T3.
    iApply ("QIC" $! (Vb ⊔ V4) (<[tl:=(#n, V4)]> ζl1) with "[T' Tls]").
    have ? : Vb ⊑ Vb ⊔ V4 by clear; solve_lat.
    rewrite -Tail_insert. iSplitL "T'"; last iSplitL "Tls"; [by iFrame..|].
    rewrite view_at_view_at. iExists V''. iSplit; last iSplit.
    + rewrite {2}/SeenEnqueuedLink decide_False; last done.
      iDestruct "SLη" as "[SLη LVη]".
      iExists enqId, η', v. iApply (view_at_mono with "SLη"); [done|].
      apply seen_enqueued_mono; eauto; apply SUB.
    + iPureIntro. apply (elem_of_list_prefix _ _ _ LeCL3). right.
      do 2 (rewrite elem_of_app; right). by rewrite elem_of_list_singleton.
    + clear -LeVs LeVl' LeVn.
      iExists Vn, {[tn := (#0, Vn)]}. iSplit.
      { iPureIntro. split; [solve_lat|]. exists tn. by rewrite lookup_insert. }
      iApply (view_at_mono_2 with "SNn"). solve_lat. }

  (* finishing *)
  iIntros "!>". wp_seq. by iApply "HΦ".
Qed.

Lemma enqueue_spec :
  enqueue_spec' enqueue QueueLocal QueueInv.
Proof.
  intros N DISJ q tid γg G1 M V v Posx.
  iIntros "#sV #Gs" (Φ) "AU".
  iLöb as "IH". wp_rec.
  awp_apply (try_enq_spec with "sV Gs"); [eauto..|].
  iApply (aacc_aupd with "AU"); [done|].
  iIntros (Q G) "QI".
  iAaccIntro with "QI"; first by eauto with iFrame.
  iIntros (b V' Q' G' enqId enq Venq M') "QI !>".
  destruct b.
  - iRight. iExists V', Q', G', enqId, enq, Venq, M'. iFrame "QI".
    iIntros "H !> _". wp_if. by iApply "H".
  - iLeft. iDestruct "QI" as "(QI & sV' & Local & Le)".
    iDestruct "Le" as %(?&?&?&?&?&?).
    subst Q' G'. iFrame "QI". iIntros "AU !> _".
    wp_if. by iApply ("IH" with "AU").
Qed.

Lemma try_deq_spec :
  try_deq_spec' try_deq QueueLocal QueueInv.
Proof.
  intros N DISJ q tid γg G1 M V.
  iIntros "#sV #[Gs QSI]" (Φ) "AU".
  iDestruct "QSI" as (γ γh γl) "[QS QII]".
  iDestruct "QS" as (ηs s D1 L1 D0 T1 SubD0)
    "(Hl & Tl & LS1 & LD1 & LT1 & F & LSeen & LSync)".
  iDestruct "F" as %(ND11 & DT1 & CDT1 & InjT1 & ET1 & SYE1).
  rewrite /HeadSeen. iDestruct "Hl" as (th0 Vs0) "[SH Hs]".

  wp_lam. wp_op. rewrite -[Z.to_nat 0]/(0%nat).
  wp_bind (!ᵃᶜ #(q >> head))%E.

  iInv "QII" as (Q2 G2) ">[GMA QBI]" "Close".
  iDestruct (QueueBaseInv_unfold_snap_2 with "QBI LS1 LT1") as (D2 L2 T2) "[QBI LE]".
  iDestruct "LE" as %(LeCL1 & LeDL1 & LeT1).
  iAssert (⌜ QueueProps Q2 G2 T2 ηs s D2 L2 ⌝)%I with "[QBI]" as %QP2.
  { iClear "#". iDestruct "QBI" as "(?&?&?&$&?)". }

  (* get a snapshot *)
  iDestruct (QueueInv_graph_snap with "GMA") as "#GS2".
  iDestruct (QueueInv_no_exist_snapshot with "QBI") as "#(LS2 & LD2 & LT2)".

  (* get Head *)
  iDestruct (QueueInv_no_exist_head_immut_access with "QBI")
    as (Vb th1 Vs1) "[[ATh Hs'] QIC]".
  (* read Head *)
  wp_apply (AtomicSeen_acquire_read with "[$SH $ATh $sV]"); [solve_ndisj|].
  iIntros (th2 vh2 V2 V2' ζh') "(F & #sV2 & SH1 & ATh)".
  iDestruct (view_at_elim with "sV2 SH1") as "#SH' {SH1}".

  (* close the invariant *)
  iMod ("Close" with "[ATh GMA QIC]") as "_".
  { iNext. iExists _, _. iFrame "GMA".
    iExists _, _, _, _, _. iApply ("QIC" with "ATh"). }

  (* extract read value *)
  iDestruct "F" as %([SubH1 SubH2] & Eqth2 & _ & LeV2).
  set E2 := G2.(Es).
  iAssert (∃ η2 (n2 : loc) (i : nat),
            ⌜ th2 = th1 +p i ∧ vh2 = #n2 ∧
              ((ηs, s) :: D2) !! i = Some (η2, n2) ∧ Vs1 !! i = Some V2 ⌝ ∗
            @{V2} (SeenEnqueuedLink_val E2 T2 ((ηs, s) :: D2) η2 n2 ∗
                  if i is O then emp
                  else ∃ D', SeenDequeueds γg γ (D' ++ [(η2, n2)])))%I
    with "[Hs']" as (η2 n2 i (->&->&Eqη2&EqV2)) "[Hn2 SD2]".
  { set Eqth2' := lookup_weaken _ _ _ _ Eqth2 SubH2.
    apply lookup_map_seqP_Some in Eqth2'
      as [Leth2 [[n2 V'] [Eq' Eqth2'%lookup_zip_with_Some]]%list_lookup_fmap_inv].
    simpl in Eq'. inversion Eq'. subst vh2 V'. clear Eq'.
    destruct Eqth2' as (n2' & V' & Eq' & Eq1%list_lookup_fmap_inv & Eq2).
    inversion Eq'. subst n2' V'. clear Eq'.
    destruct Eq1 as ([η2 n2'] & Eq' & Eq1). simpl in Eq'. subst n2'.
    iExists η2, n2, _. iSplit.
    { iPureIntro. split; [|done]. clear -Leth2. rewrite /pos_add_nat. by lia. }
    rewrite /Head (big_sepL2_lookup _ _ _ _ _ _ Eq1 Eq2) /=.
    rewrite view_at_view_at. by iFrame "Hs'". }

  iDestruct (view_at_elim with "[] Hn2") as "SEn2".
  { iApply (monPred_in_mono with "sV2"). simpl. clear -LeV2. solve_lat. }

  set CL1 := (ηs, s) :: D1 ++ L1.
  set CL2 := (ηs, s) :: D2 ++ L2.
  (* Use the latest observation of n2 to read *)
  iAssert (∃ (v2 : lit) Vv2, link_val η2 n2 Vv2 v2 ∗
          ⌜ if enqueued_in_choice CL1 T1 M η2 is inleft _
            then ∃ l' : loc, v2 = l' else v2 = 0 ⌝)%I
    with "[SEn2]" as (v2 Vv2) "[LVn2 %Fn2]".
  { destruct (enqueued_in_choice CL1 T1 M η2) as [[η1 [Ine ADJ1]]|NI];
      last first.
    { rewrite /SeenEnqueuedLink_val. iDestruct "SEn2" as (V0) "(SE&_&LV0)".
      iExists 0, V0. by iFrame "LV0". }
    apply coimg_correct in Ine as (e & Ine & EqT1η).
    destruct (CDT1 e) as [[v1 ([ee Ve lVe] & Eq' & Eqv1)%list_lookup_fmap_inv'] _].
    { by exists η1. } simpl in Eq'. subst ee.
    iSpecialize ("LSeen" $! e v1 Ve lVe with "[//]").
    iDestruct "LSeen" as (η' l' η'' l'') "([[%ADJ2 %EqT] SEV1] & [%In' _] & LV1)".
    iExists l'', Ve.(dv_comm).
    have ? : η'' = η1 by apply (InjT1 _ _ _ EqT EqT1η).
    subst η''. clear EqT.
    have ?:= adjacent_in_NoDup_inj_l _ _ _ _ ND11 ADJ1 ADJ2. subst η'.
    assert (In2 : CL2 !! i = Some (η2, n2)).
    { by apply (lookup_app_l_Some (_ :: _)). }
    assert (l' = n2).
    { clear -ND11 LeCL1 In2 In' QP2.
      move : In'. rewrite /CL1 LeCL1 => /elem_of_list_lookup [i' In'].
      assert (i = i').
      { apply (NoDup_lookup _ _ _ η2 (qu_no_dup _ _ _ _ _ _ _ QP2));
          rewrite list_lookup_fmap.
        - by rewrite In2. - by rewrite In'. } subst i'.
      rewrite In2 in In'. by inversion In'. }
    subst l'. iFrame "LV1". iPureIntro. by exists l''. }
  iDestruct "LVn2" as (Vn2 ζn2 [LeVn2 Eqv2]) "#Sn2".

  (* use ζn2 to read n2 *)
  iIntros "!>". wp_let. wp_op. rewrite (shift_0 n2).
  wp_bind (!ᵃᶜ_)%E.
  (* prepare to read η2, open the invariant again... *)
  clear Vb.

  iInv "QII" as (Q3 G3) ">[GMA QBI]" "Close".
  iDestruct (QueueBaseInv_unfold_snap_2 with "QBI LS2 LT2") as (D3 L3 T3) "[QBI LE]".
  iDestruct "LE" as %(LeCL2 & LeDL2 & LeT2).

  (* get a snapshot *)
  iDestruct (QueueInv_graph_snap with "GMA") as "#GS3".
  iDestruct (QueueInv_no_exist_snapshot with "QBI") as "#(LS3 & LD3 & LT3)".

  (* get permission of η2 *)
  set CL3 := (ηs, s) :: D3 ++ L3.
  set infos3 := zip (next_nodes CL3)
                    (dequeue_mask (length ((ηs, s) :: D3)) (length L3)).

  iDestruct "QBI" as "(LEL & LDL & LT & %QP3 & QV & QLs)".
  iDestruct "QLs" as (Vb) "(H & T & Ns)".
  rewrite (own_nodes_access _ _ _ _ _ _ η2 n2); last first.
  { apply (elem_of_list_prefix _ _ _ LeCL2), (elem_of_app (_::_)).
    left. move : Eqη2. by apply elem_of_list_lookup_2. }
  iDestruct "Ns" as (d ηs' i2 [Eqη Eqd]) "[Linkη Ns]".
  iDestruct "Linkη" as (t1 V1 ζ1) "[ATη S1]".
  rewrite (view_at_objective_iff (LinkRes _ _ _ _ _ _ _ _ _)).

  iDestruct (QueueInv_graph_snap_included with "GMA Gs") as %SubG1.
  set E1 := G1.(Es). set E3 := G3.(Es).
  have SubE1 : E1 ⊑ E3 by apply SubG1.
  iDestruct (LTM_master_snap_included with "LT LT1") as %SubT1.
  iDestruct (LEL_master_snap_included with "LEL LS1") as %SubL1.
  iDestruct (LDL_master_snap_included with "LDL LD2") as %SubLD2.
  iAssert (⌜ set_in_bound M E1 ⌝)%I with "[]" as %SubD1.
  { iDestruct "Gs" as "[_ SL1]". iApply (SeenLogview_closed with "SL1"). }

  iAssert (SeenLinked_logview CL3 T3 E3 M)%I with "[]" as "SL3".
  { by iApply (SeenLinked_logview_mono CL1 CL3 T1 T3 E1 E3 with "LSeen"). }
  iCombine "LSync SL3 SH Hs Tl" as "PSL {SL3}".
  iDestruct (view_at_intro_incl with "PSL sV2")
    as (V3) "(#sV3 & %LeV2' & PSV & SL3 & SHa & Hsa & Tl') {PSL}".
  (* ready to read *)
  wp_apply (AtomicSeen_acquire_read with "[$Sn2 $ATη $sV3]"); first solve_ndisj.

  iIntros (tn2 vn2 Vn2' V4 ζn2') "(F3 & #sV4 & #Sn2' & ATη)".
  (* get a copy *)
  iDestruct (LinkRes_dup with "S1") as "#Pη".

  iDestruct "F3" as %([Subζη2 Subζn2'] & Eqtn2 & MAXn2 & LeV3').
  have Eqtn1 : ζ1 !! tn2 = Some (vn2, Vn2') by eapply lookup_weaken.

  have SubM: set_in_bound M E3.
  { clear - SubD1 SubE1. by eapply set_in_bound_mono. }

  case (decide (tn2 = t1)) => [Eqt1|NEqt1].
  { (* EMPTY CASE: Nothing to pop *)
    subst tn2.

    have PSV : ∀ e v eV, E1 !! e = Some eV → eV.(ge_event) = Enq v →
                e ∈ M → eV.(ge_lview) ⊑ M.
    { intros e v eV Eqe Eqv InM. apply (SYE1 e v eV.(ge_view) eV.(ge_lview) InM).
      rewrite Eqe -Eqv. clear; by destruct eV. }

    iAssert (⌜ vn2 = #0 ∧ Vn2' = V1 ⌝)%I with "[Pη]" as %[-> ->].
    { rewrite /LinkRes. destruct ηs' as [[]|].
      - iDestruct "Pη" as (????) "_". iPureIntro. subst ζ1.
        rewrite lookup_insert_ne in Eqtn1; last lia.
        rewrite lookup_insert in Eqtn1. clear -Eqtn1. by inversion Eqtn1.
      - iDestruct "Pη" as %?. iPureIntro. subst ζ1.
        rewrite lookup_insert in Eqtn1. clear -Eqtn1. by inversion Eqtn1. }
    iAssert (⌜ ∀ t' v' V', ζn2 !! t' = Some (v', V') → v' = #0 ⌝)%I
      with "[Pη]" as "%Eqvn2 {Pη}".
    { iIntros (t' v' V' Eq').
      have Ltt1 : (t' ≤ t1)%positive. { apply MAXn2. by eexists. }
      have Subζn21: ζn2 ⊆ ζ1 by etrans.
      set Eq'' := lookup_weaken _ _ _ _ Eq' Subζn21.
      rewrite /LinkRes.
      destruct ηs' as [[]|].
      - iDestruct "Pη" as (????) "_". iPureIntro. subst ζ1.
        clear -Eq'' Ltt1. move : Eq''. rewrite lookup_insert_ne.
        + rewrite lookup_singleton_Some. intros [_ ?]. by simplify_eq.
        + intros ?. subst t'. by lia.
      - iDestruct "Pη" as %?. iPureIntro. subst ζ1.
        move : Eq''. rewrite lookup_singleton_Some. intros [_ ?]. by simplify_eq. }

    iDestruct (QueueInv_consistent with "GMA") as %[CON EGCs3].

    (* Get dequeue observations *)
    iAssert (∃ (Me : list event_id) De Te,
              ⌜ set_in_bound (list_to_set Me) E3 ∧
                (i = 0%nat ∧ Me = [] ∨
                (0 < i)%nat ∧ De ++ [(η2, n2)] ⊑ D3 ∧ Te ⊆ T3 ∧
                  length (De.*1 ++[η2]) = length Me ∧
                  ∀ i η d, (De.*1 ++[η2]) !! i = Some η → Me !! i = Some d →
                    ∃ e, Te !! η = Some e ∧ (e, d) ∈ G3.(com)) ⌝ ∗
              @{V2} (graph_snap γg G3 (list_to_set Me)))%I
      with "[GMA LDL LT SD2]" as (Me De Te [SubMe CASEe]) "#SLMe".
    { iRevert "GS3". iIntros "{# %} #GS3".
      destruct i as [|i].
      { iExists [], [], ∅. rewrite list_to_set_nil. iFrame "GS3".
        iPureIntro. split; [|done]. split; [done|by left]. }
      (* non-empty dequeue observations *)
      iDestruct "SD2" as (De) "[LD' SD2]".
      iDestruct "SD2" as (Ge Te Me) "(Gse & LTe & He)".
      rewrite 3!view_at_objective_iff. clear.
      iDestruct (QueueInv_graph_snap_included_2 with "GMA Gse") as %LeGe.
      iExists Me, De, Te. iSplit.
      - iDestruct "Gse" as "[_ SL]". rewrite SeenLogview_closed.
        iDestruct "SL" as %Closed.
        iDestruct (LDL_master_snap_included with "LDL LD'") as %?.
        iDestruct (LTM_master_snap_included with "LT LTe") as %?.
        rewrite fmap_app. iDestruct (big_sepL2_length with "He") as %EqL.
        iDestruct (big_sepL2_pure_1 with "He") as %FL. iPureIntro. split.
        + eapply set_in_bound_mono; [apply LeGe|eauto].
        + right. split; [clear; lia|]. do 3 (split; [done|]).
          intros k η d Eq1 Eq2. destruct (FL _ _ _ Eq1 Eq2) as (e & EqTe & InGe).
          exists e. split; [done|]. by apply LeGe.
      - rewrite -(view_at_objective_iff (graph_snap γg G3 ∅) V2).
        iCombine "GS3 Gse" as "Gs". iApply (view_at_mono with "Gs"); [done|].
        iIntros "(Gs1 & Gs2)". by iApply (graph_snap_mono with "Gs1 Gs2"). }

    set Me' := list_to_set Me.
    have SubMMe : set_in_bound (M ∪ Me') E3.
    { clear -SubMe SubM. by apply set_in_bound_union. }

    have DEQMe': ∀ de, de ∈ Me' →
      ∃ dVe ve, E3 !! de = Some dVe ∧ dVe.(ge_event) = Deq ve.
    { clear -CASEe SubMe CON. intros de Inde.
      destruct CASEe as [[-> ->]|(Gti & LeDe & LeTe & EQL & InG3)].
      { exfalso. move : Inde. rewrite /Me' list_to_set_nil. apply not_elem_of_empty. }
      apply elem_of_list_to_set, elem_of_list_lookup in Inde as [j Eqde].
      destruct (lookup_lt_is_Some_2 (De.*1 ++ [η2]) j) as [η Eqη].
      { rewrite EQL. apply (lookup_lt_Some _ _ _ Eqde). }
      destruct (InG3 _ _ _ Eqη Eqde) as (e & Eqe & InG3c).
      destruct (bsq_cons_matches _ CON _ _ InG3c)
        as (? & eV & dV & ve & ? & EqdVe & ? & ? & ?). by exists dV, ve. }

    (* Commit AU with an EMPTY event, commiting point is the read. *)
    set V' := V4.
    have LeV34 : V3 ⊑ V'. { clear -LeV3'. rewrite /V'. solve_lat. }
    have LeVV' : V ⊑ V'. { clear -LeV34 LeV2' LeV2. by solve_lat. }
    have bLeVV' : bool_decide (V ⊑ V') by eapply bool_decide_unpack; eauto.
    set Vdeq := mkDView V V4 V4 bLeVV'.

    assert (GIP:= graph_insert_props_base _ EmpDeq _ Vdeq SubMMe EGCs3).
    destruct GIP as [deqId M' egV' G' LeG' SubM' SUB' Inde NInde EGCs'].
    set E' := G'.(Es). have LeE' : E3 ⊑ E' by apply LeG'.
    have SubMM' : M ⊑ M'. { by set_solver-. }
    have SubMe' : {[deqId]} ∪ M ⊆ M'. { set_solver-. }
    have FRde : deqId ∉ M. { set_solver+NInde. }

    iDestruct (LDL_master_snap_included with "LDL LD1") as %SubLD1.
    destruct QP3 as [ND DT CDT InjT ET MONO ORD ABS].

    assert (NI: ∀ e1 e2, (e1, e2) ∈ G'.(com) → e1 ≠ deqId ∧ e2 ≠ deqId).
    { move => ?? /(gcons_com_included G3) [/=]. lia. }
    have CON' : StrongQueueConsistent G'.
    { destruct CON as [CONRA [CONw _ _ CON] CON7b].
      have CONRA' : graph_event_is_relacq G'.(Es) (λ _, True).
      { clear -CONRA. by apply graph_insert_event_is_relacq. }
      have FIFO' : queue_FIFO_strong G'.
      { (* 7b *)
        intros e1 v1 eV1 e2 d2 Eqe1 Eqv1 InG2 Le12.
        rewrite lookup_app_1_ne in Eqe1.
        + apply (CON7b _ _ _ _ _ Eqe1 Eqv1 InG2 Le12).
        + intros ->. rewrite /= in InG2.
          apply (Nat.lt_irrefl deqId), (Nat.le_lt_trans _ e2 _ Le12),
                (gcons_com_included _ _ InG2). }
      constructor; [done| |done]. constructor.
      { clear -CONw. by apply graph_insert_event_is_writing. }
      { by apply graph_event_is_relacq_releasing_True. }
      { by apply graph_event_is_relacq_acquiring_True. }
      destruct CON as [CON1 CON2 CON3 CON4 CON5 CON6 CON7a _].
      have EC' : graph_xo_eco G'.(Es).
      { (* 7a *)
        intros e1 e2 eV2 [Eq1|[-> <-]]%lookup_app_1.
        + by apply CON7a.
        + rewrite /= elem_of_union !elem_of_singleton.
          intros [?|Inm]; [by subst e1|].
          apply Nat.lt_le_incl, lookup_lt_is_Some, SubMMe, Inm. }
      constructor; [..|done|].
      - (* 1 *)
        intros e0 eV0 v0 [Eq1|[-> <-]]%lookup_app_1;
          [by apply (CON1 _ _ _ Eq1)|done].
      - (* 2 *)
        intros e1 d2 In1. destruct (NI _ _ In1).
        do 2 (rewrite lookup_app_1_ne; [|done]). by apply CON2.
      - (* 3 *) done.
      - (* 4 *) intros ?? [?|[-> <-]]%lookup_app_1; [by eapply CON4|done].
      - (* 5 *)
        intros e eV' EqeV EqED ee ve eVe Eqee Eqve Inee.
        have NEqee: deqId ≠ ee.
        { intros <-. rewrite lookup_app_1_eq in Eqee.
          clear -Eqee Eqve. inversion Eqee. by subst eVe. }
        rewrite lookup_app_1_ne in Eqee; [|done].
        case (decide (deqId = e)) => ?; last first.
        (* Step 1: if e is not the new event we added, use the old Consistency.
          If e is deqId, we have to prove that we don't locally observe an
          unmatched enqueue. *)
        { (* Case: old Consistency *)
          rewrite lookup_app_1_ne in EqeV; last done.
          apply (CON5 _ _ EqeV EqED _ _ _ Eqee Eqve Inee). }
        (* Case: the deqId we added *)
        subst e. rewrite lookup_app_1_eq in EqeV. inversion EqeV; clear EqeV EqED.
        subst eV'. move : Inee. rewrite /= !elem_of_union elem_of_singleton.
        move => [//|[InM|InMe]]; last first.
        { exfalso. clear -DEQMe' Eqee Eqve InMe.
          apply DEQMe' in InMe as (eVe' & ? & Eqee' & Eqev).
          rewrite Eqee in Eqee'. congruence. }
        (* we know that ee is an enqueued with the logical node ηe *)
        set InE1 := (SubD1 _ InM).
        assert (Eqee' := prefix_lookup_inv _ _ _ _ Eqee InE1 SubE1).
        destruct (CDT1 ee) as [_ [ηe Eqηe1]]. { rewrite Eqee' /= Eqve. by exists ve. }
        have Eqηe : T3 !! ηe = Some ee
          by apply (lookup_weaken _ _ _ _ Eqηe1 SubT1).
        have INL1 : ηe ∈ (D1 ++ L1).*1.
        { apply (elem_of_list_to_set (C:=gset _)). rewrite -DT1.
          apply elem_of_dom. by exists ee. }
        destruct (elem_of_list_lookup_1 _ _ INL1) as [ie Eqie].
        have LeDL13: (D1 ++ L1).*1 ⊑ (D3 ++ L3).*1.
        { apply fmap_prefix. by etrans. }

        (* Step 2: if the node ηe is not after the node η2 that we read from,
          we know that, because η2 is dequeued, we also observe the dequeue of ηe. *)
        case (decide (i ≤ ie)%nat) => [InD1e|/Nat.nle_gt NIN]; last first.
        { destruct CASEe as [[Eq0 EqMe]|(Gt0 & LeDe & LeTe & EqL & DEQ)].
          { clear - NIN Eq0. exfalso. subst i. lia. }
          have Eqη2e: (De ++ [(η2, n2)]) !! length De = Some (η2, n2).
          { clear. by rewrite lookup_app_r // Nat.sub_diag. }
          assert (Eqi : i = S $ length De).
          { rewrite app_comm_cons fmap_app in ND. apply NoDup_app in ND as [ND _].
            apply (NoDup_lookup _ i (S $ length De) η2 ND).
            - rewrite list_lookup_fmap (prefix_lookup_Some _ _ _ _ Eqη2); [done|].
              by apply prefix_cons.
            - by rewrite list_lookup_fmap lookup_cons
                         (prefix_lookup_Some _ _ _ _ Eqη2e LeDe). }
          have Eqie': (De ++ [(η2, n2)]).*1 !! ie = Some ηe.
          { apply (prefix_lookup_inv _ _ _ _ (prefix_lookup_Some _ _ _ _ Eqie LeDL13)).
            - apply lookup_lt_is_Some. rewrite fmap_app /= app_length fmap_length /=.
              clear -NIN Eqi. lia.
            - destruct LeDe as [De' EqDe'].
              rewrite EqDe' (fmap_app _ _ L3) (fmap_app _ _ De') -app_assoc. by eexists. }
          rewrite fmap_app /= in Eqie'.
          destruct (lookup_lt_is_Some_2 Me ie) as [de Eqde].
          { rewrite -EqL. by apply (lookup_lt_Some _ _ _ Eqie'). }
          destruct (DEQ _ _ _ Eqie' Eqde) as (ee' & Eqeee & InG3).
          rewrite (lookup_weaken _ _ _ _ Eqeee LeTe) in Eqηe.
          inversion Eqηe; clear Eqηe; subst ee'.
          exists de. split; [done|]. rewrite /M' 2!elem_of_union. right; right.
          apply elem_of_list_to_set. move : Eqde. apply elem_of_list_lookup_2. }
        (* Otherwise, if the node ηe is after η2 that we read from, it's a
          contradiction because we cannot have observed the enqueue of ηe
          and at the same time read 0 from n2 (of η2). *)
        (* Step 3: the location (η2,n2) that we read from Head must be in D2
          and D3, and ηe is after that, so there must be a node η' that
          immediately follows η2 and is not after ηe. *)
        have LtLen: (i < S ie)%nat by lia.
        have EqieDL1: CL1.*1 !! S ie = Some ηe.
        { by rewrite /CL1 fmap_cons. }
        have EqjsDL1: CL1 !! i = Some (η2, n2).
        { have EqDL2 : CL2 !! i = Some (η2, n2).
          { rewrite /CL2 app_comm_cons. by apply lookup_app_l_Some. }
          destruct LeCL1 as [L2' EqL2'].
          rewrite /CL2 EqL2' /CL1 app_comm_cons lookup_app_l in EqDL2; [done|].
          clear -EqieDL1 LtLen. apply lookup_lt_Some in EqieDL1.
          rewrite fmap_length in EqieDL1. etrans; [apply LtLen|exact EqieDL1]. }
        have EqjsDL1' : CL1.*1 !! i = Some η2 by rewrite list_lookup_fmap EqjsDL1.
        destruct (lookup_strict_subseq _ _ _ _ _ EqjsDL1' EqieDL1 LtLen)
          as (η' & jη' & SSη' & Eqjη' & Lejη').
        have Eq0: jη' ≠ 0%nat.
        { clear -SSη' Eqjη' ND11. destruct SSη' as (L2 & L3 & Eq23).
          intros ?. subst jη'. rewrite /= in Eqjη'. simplify_eq.
          destruct L2 as [|η0 L2]; simplify_list_eq.
          - apply NoDup_cons in ND11 as [ND1 _]. apply ND1.
            rewrite (_: D1.*1 ++ L1.*1 = η2 :: L3) //. by left.
          - apply NoDup_cons in ND11 as [ND1 _].  apply ND1.
            rewrite (_: D1.*1 ++ L1.*1 = L2 ++ η2 :: η0 :: L3) //.
            rewrite elem_of_app. right. right. by left. }
        have Le1jη' : (1 ≤ jη')%nat by lia. clear Eq0.
        have EqDL1' : (D1 ++ L1).*1 !! (jη' - 1)%nat = Some η'.
        { clear -Eqjη' Le1jη'.
          rewrite list_lookup_fmap (lookup_app_r [_] (D1 ++ L1)) /= // in Eqjη'.
          by rewrite list_lookup_fmap. }
        (* η' is not after ηe *)
        have LBη': list_before (D3 ++ L3).*1 η' ηe.
        { exists (jη' - 1)%nat, ie. repeat split.
          - apply (prefix_lookup_Some _ _ _ _ EqDL1'), LeDL13.
          - apply (prefix_lookup_Some _ _ _ _ Eqie), LeDL13.
          - clear -Lejη' Le1jη'. simpl in Lejη'. by apply Nat.le_sub_le_add_l. }

        (* Step 5: by synchronization of enqueues, we know that the enqueue of
          ηe must have observed the enqueue of η', so we must have observed
          η' in M as well: η' ∈ M. *)
        assert (is_Some (T1 !! η')) as [e' Eqe1'].
        { apply (elem_of_dom (D:=gset _)). rewrite DT1 elem_of_list_to_set.
          move : EqDL1'. apply elem_of_list_lookup_2. }
        have Eqe' : T3 !! η' = Some e' by apply (lookup_weaken _ _ _ _ Eqe1' SubT1).
        assert (IneV1 := ORD _ _ _ _ _ LBη' Eqe' Eqηe Eqee).
        have Ine' := (PSV _ _ _ Eqee' Eqve InM _ IneV1).
        have InCIT1: η' ∈ coimg T1 M. { by apply coimg_correct; exists e'. }
        move : Fn2.
        (* Step 6: now we ask if η2 has been observed in M?
          - if it has been observed in M, then, knowing that we have also
            observed η' later in M, we cannot read null for n2 =>
            contradiction.
          - if we have not observed η2 in M, then we cannot have observed
            anything after η2 like η' or ηe in M => contradiction. *)
        destruct (enqueued_in_choice CL1 T1 M η2) as [SM|NSM].
        + clear -Eqv2 Eqvn2. intros [l' ?]. subst v2.
          destruct Eqv2 as [? ?%Eqvn2]. by simplify_eq.
        + intros _. exfalso. by apply (NSM _ InCIT1), strict_subseq_adjacent_in.
      - (* 6 *) done.
      - (* 7a *) by apply queue_FIFO_strong_FIFO. }

    have CDT' : EM_equiv T3 E'.
    { intros e. rewrite CDT. split; intros [v Eqv].
      - exists v. rewrite lookup_app_1_ne; [done|].
        clear -Eqv. intros ->.
        apply list_lookup_fmap_inv' in Eqv as (? & _ & ?%lookup_lt_Some). lia.
      - have ?: deqId ≠ e.
        { intros ?. subst e. rewrite lookup_app_1_eq /= in Eqv. by inversion Eqv. }
        rewrite lookup_app_1_ne in Eqv; [by exists v|done]. }
    have ORD': ∀ η1 η2 e1 e2 eV2, list_before (D3 ++ L3).*1 η1 η2 →
        T3 !! η1 = Some e1 → T3 !! η2 = Some e2 → E' !! e2 = Some eV2 →
        e1 ∈ eV2.(ge_lview).
    { intros η1 η2' e1 e2 eV2 LB EqT1 EqT2 EqEV2. apply (ORD _ _ _ _ _ LB EqT1 EqT2).
      rewrite lookup_app_1_ne in EqEV2; [done|]. intros ?. subst e2.
      destruct (CDT deqId) as [[vd Eqv] _]. { by exists η2'. } clear -Eqv.
      apply list_lookup_fmap_inv' in Eqv as (? & _ & ?%lookup_lt_Some). lia. }

    have ABS' : Forall2 (λ '(v, V) '(η, _), ∃ e eV,
        T3 !! η = Some e ∧ G'.(Es) !! e = Some eV ∧
        eV.(ge_event) = Enq v ∧ eV.(ge_view).(dv_comm) = V) Q3 L3.
    { eapply Forall2_impl; [done|]. intros [? ?] [? ?] (e & eV & ? & ? & ? & ?).
      exists e, eV. split_and!; [done|by eapply prefix_lookup_Some|done..]. }

    iAssert (@{V'} SeenLinked_logview CL3 T3 E' M')%I with "[]" as "#SL3'".
    { iIntros (e0 v0 V0 lV0 [InM Eqv]).
      have NEqid: deqId ≠ e0.
      { intros <-. rewrite lookup_app_1_eq /= in Eqv. by inversion Eqv. }
      rewrite lookup_app_1_ne in Eqv; [|done].
      have Ine0: e0 ∈ M.
      { move : InM => /elem_of_union [/elem_of_singleton?|/elem_of_union [//|]].
        - by subst.
        - clear -DEQMe' Eqv. intros (?&?&Eq1&Eq2)%DEQMe'.
          rewrite Eq1 in Eqv. inversion Eqv; clear Eqv; by subst. }
      iDestruct ("SL3" $! e0 v0 V0 lV0 with "[%//]") as (η' l' η l) "SL3'".
      iExists η', l', η, l. iApply (view_at_mono with "SL3'"); [done|].
      by apply (SeenLinked_emap_mono E3 E' T3). }

    iAssert (@{V'} SeenLogview E' M')%I with "[]" as "#PSV'".
    { iRevert "SLMe PSV". iIntros "{#} [_ #SLMe] #PSV".
      clear -SubE1 LeE' SubMM' LeV3' LeV2 LeV2'.
      rewrite -2!SeenLogview_union'. iSplit; last iSplit.
      - rewrite -SeenLogview_singleton; [|by rewrite lookup_app_1_eq]. done.
      - iApply (view_at_mono with "PSV"); [rewrite /V'; solve_lat|].
        apply SeenLogview_map_mono; [by etrans|done].
      - iApply (view_at_mono with "SLMe"); [rewrite /V'; solve_lat|].
        by apply SeenLogview_map_mono. }

    (* open the AU *)
    iMod "AU" as (Q3' G3') "[>GMA' HClose]".
    iDestruct (QueueInv_agree with "GMA GMA'") as %[-> ->].
    iMod (QueueInv_update _ _ _ _ Q3 _ LeG' EGCs' CON' with "GMA GMA'")
      as "(GMA & GMA' & Gs')".

    have SYE' : SyncEnqueues E' M'. {
      intros ex vx Vx lVx. rewrite !elem_of_union elem_of_singleton.
      intros [->| [InM|InM]].
      - rewrite lookup_app_1_eq. by inversion 1.
      - intros Eq'. etrans; first apply (SYE1 ex vx Vx lVx InM); [|done].
        apply (prefix_lookup_inv _ E'); [done| |by etrans]. by apply SubD1, InM.
      - clear -DEQMe' InM LeE'. apply DEQMe' in InM as (dVe & ve & Eqex & Eqvx).
        rewrite (prefix_lookup_Some _ _ _ _ Eqex LeE'). inversion 1. by subst. }

    (* COMMIT EmpDeq *)
    rewrite bi.and_elim_r.
    iMod ("HClose" $! 0 V' Q3 G' dummy_eid deqId dummy_qevt EmpDeq ∅ Vdeq M'
          with "[$GMA Gs' $sV4]") as "HΦ".
    { (* Public Post *)
      iSplitL "Gs'"; last first.
      { iPureIntro. do 4 (split ;[done|]). by right; left. }
      (* Private Post *)
      iSplitL "Gs'". { iFrame "Gs' PSV'". }
      iExists γ, γh, γl. iFrame "QII". iExists ηs, s, D3, L3, D0, T3.
      iSplit. { iPureIntro. by etrans. }
      iSplitL "". { iExists _, _. by iFrame "SHa Hsa". }
      iFrame "Tl' LS3 LD3 LT3". iSplit; [by iPureIntro|]. iFrame "SL3' PSV'". }

    (* re-establish the invariant *)
    iMod ("Close" with "[-HΦ]") as "_".
    { iNext. iExists Q3, G'. iFrame "GMA'".
      iExists ηs, s, D3, L3, T3. iFrame "LEL LDL LT".
      iSplitL ""; [done|]. iSplitL "QV".
      { rewrite /QueueViews. iIntros (e0 ev0 V0 lV0).
        case (decide (e0 = deqId)) => [->|?].
        - rewrite lookup_app_1_eq. iIntros (Eq). inversion Eq. clear Eq.
          subst ev0 V0 lV0. by iFrame "SL3'".
        - iClear "#". rewrite lookup_app_1_ne; last done.
          iIntros (Eq). iDestruct ("QV" $! e0 ev0 V0 lV0 Eq) as "SL".
          rewrite (SeenLinked_logview_mono CL3 CL3 T3 T3 E3 E'); eauto.
          by apply (egcons_logview_closed _ EGCs3 _ _ Eq). }
      iExists (Vb ⊔ V').
      have ? : Vb ⊑ Vb ⊔ V' by clear;solve_lat.
      iSplitL "H"; last iSplitL "T".
      { iApply (view_at_mono with "H"); [done|].
        iDestruct 1 as (t0 Vs') "[H Hs]". iExists t0, Vs'.
        iFrame "H". by iApply (Head_mono with "Hs"). }
      { iApply (view_at_mono with "T"); [done|].
        iDestruct 1 as (ζl) "[T Ts]". iExists ζl.
        iFrame "T". by iApply (Tail_mono E3 E' T3 T3 with "Ts"). }
      iClear "#". rewrite bi.and_elim_l.
      (* return resources *)
      iDestruct (view_at_mono_2 with "Ns [S1 ATη]") as "Ns";
        [solve_lat|iExists _, _, _; by iFrame|].
      by rewrite (own_nodes_map_mono E3 E' T3 T3); eauto. }

    (* finishinGmpDeq case *)
    iIntros "!>". wp_let. wp_op. wp_if. by iApply "HΦ". }

  (* re-establish the invariant *)
  iMod ("Close" with "[-AU SD2]") as "_".
  { iNext. iExists _, _. iFrame "GMA".
    iExists ηs, s, D3, L3, T3. iFrame "LEL LDL LT QV". iSplitR; [done|].
    iExists (Vb ⊔ V4). iFrame "H T". iClear "#". rewrite bi.and_elim_l.
    (* return resources *)
    iApply (view_at_mono_2 with "Ns"); [solve_lat|].
    iExists _, _, _. by iFrame. } clear Vb.

  iIntros "!>".
  (* read non-zero *)
  rewrite LinkRes_unfold. iDestruct "Pη" as "[Pη|Pη]".
  { clear -Eqtn1 NEqt1. iDestruct "Pη" as %Eqζ. exfalso. destruct Eqζ as [-> ->].
    apply lookup_singleton_Some in Eqtn1 as []. by subst tn2. }
  iDestruct "Pη" as (η2' n2' V' en2 ve2 (-> & Eqζ1 & Eqη2')) "Hη2'".
  case (decide (tn2 = (t1 + 1)%positive)) => ?; last first.
  { exfalso. rewrite Eqζ1 lookup_insert_ne in Eqtn1; [|done].
    apply lookup_singleton_Some in Eqtn1 as []. by subst tn2. } subst tn2.
  assert (vn2 = #n2' ∧ V' = Vn2') as [-> ->].
  { rewrite Eqζ1 lookup_insert in Eqtn1. by inversion Eqtn1. }
  iDestruct (view_at_elim with "[] Hη2'") as "(SEe2 & LVn2' & _)".
  { iApply (monPred_in_mono with "sV4"). simpl. solve_lat. }

  wp_let. wp_op. wp_if. wp_op. wp_bind (CAS _ _ _ _ _ _)%E.

  (* prepare the CAS *)
  iInv "QII" as (Q4 G4) ">[GMA QBI]" "Close".
  iMod "AU" as (Q4' G4') "[>GMA' HClose]".
  iDestruct (QueueInv_agree with "GMA GMA'") as %[-> ->].
  iDestruct (QueueBaseInv_unfold_snap_2 with "QBI LS3 LT3") as (D4 L4 T4) "[QBI LE]".
  iDestruct "LE" as %(LeCL3 & LeDL3 & LeT3).

  (* get a snapshot *)
  iDestruct (QueueInv_graph_snap with "GMA") as "#GS4".
  iDestruct (QueueInv_no_exist_snapshot with "QBI") as "#(LS4 & LD4 & LT4)".

  (* get permission of Head and n2' *)
  set CL4 := (ηs, s) :: D4 ++ L4.
  set infos4 := zip (next_nodes CL4)
                    (dequeue_mask (length ((ηs, s) :: D4)) (length L4)).

  iDestruct "QBI" as "(LEL & LDL & LT & %QP4 & QV & QLs)".
  iDestruct "QLs" as (Vb) "(H & T & Ns)".
  iDestruct "H" as (th3 Vs3) "(ATh & Hs3)".

  iDestruct (LDL_master_snap_included with "LDL LD3") as %SubLD3.
  iDestruct (LDL_master_snap_included with "LDL LD1") as %SubLD14.
  iDestruct (QueueInv_graph_snap_included with "GMA GS3") as %SubG3.
  set E4 := G4.(Es). have SubE3: E3 ⊑ E4 by apply SubG3.
  have SubG14: G1 ⊑ G4 by etrans.
  have SubE14: E1 ⊑ E4 by etrans.
  have SubCL14: CL1 ⊑ CL4 by etrans.
  have SubT14: T1 ⊆ T4 by etrans.

  iAssert (SeenLinked_logview CL4 T4 E4 M)%I with "[]" as "SL4'".
  { by iApply (SeenLinked_logview_mono CL1 CL4 T1 T4 E1 E4 with "LSeen"). }

  iCombine "LVn2' SEe2 SL4'" as "SEL {SL4' LVn2' SEe2}".
  iDestruct (view_at_intro_incl with "SEL sV4")
    as (V5) "(#sV5 & %LeV4 & LVn2' & SEe2 & SL4)".

  wp_apply (AtomicSeen_CON_CAS_live_loc _ _ _ _ _ _ _ n2 #n2' _ ∅ with "[$SH' $ATh $sV5]"); [done..| |done|].
  { intros ???. by apply toHeadHist_lookup_Some_is_comparable_loc. }

  iIntros (b th4 v4 Vr4 V5' ζh4' ζh4) "(F5 & #sV5' & SH4' & ATh & CASE)".
  iDestruct "F5" as %([Sub41 Sub42] & Eq4' & MAXth4 & LeV5).
  have SubV35' : V3 ⊑ V5' by solve_lat.
  have SubV5 : V ⊑ V5 by solve_lat.
  have SubV5' : V ⊑ V5' by etrans.
  have bSubV5': bool_decide (V ⊑ V5') by eapply bool_decide_unpack; eauto.
  set Vdeq := mkDView V V5' V5' bSubV5'.

  iDestruct "CASE" as "[[Eq HVr]|[Eq HVw]]".
  { (* CAS failure *)
    iDestruct "Eq" as %(? & LNE & Eq4). subst b.
    (* Commit AU with no updates to finish.
      TODO: we can actually commit a FAIL event, commiting point is the CAS. *)
    have SY4 : SyncEnqueues E4 M. { move : SYE1. by apply SyncEnqueues_mono. }
    iAssert (@{V5'} SeenLogview E4 M)%I with "[]" as "SL5".
    { iApply (view_at_mono with "PSV"); [done|]. by apply SeenLogview_map_mono. }
    (* close the AU *)
    rewrite bi.and_elim_r.
    iMod ("HClose" $! (-1) V5' Q4 G4 dummy_eid dummy_eid dummy_qevt dummy_qevt
                      ∅ Vdeq M with "[$GMA' $sV5']") as "HΦ".
    { iSplitL; last first. { iPureIntro. do 4 (split; [done|]). by left. }
      (* Private Post *)
      iSplitL "". { iDestruct "GS4" as "[$ _]". iFrame "SL5". }
      iExists γ, γh, γl. iFrame "QII".
      iExists ηs, s, D4, L4, D0, T4. iSplit. { iPureIntro. by etrans. }
      iSplitL "". { iExists _, _. by iFrame "SHa Hsa". }
      iFrame "Tl' LS4 LD4 LT4". iSplit.
      { iPureIntro. clear -QP4 SY4. by destruct QP4. }
      iFrame "SL4 SL5". }
    iIntros "!>".
    (* close the invariant *)
    iMod ("Close" with "[-HΦ]") as "_".
    { iNext. iExists _, _. iFrame "GMA".
      iExists ηs, s, D4, L4, T4. iFrame "LEL LDL LT QV". iSplit; [by iPureIntro|].
      iExists (Vb ⊔ V5'). iFrame "T Ns".
      iExists _, _. rewrite Eq4. by iFrame "ATh Hs3". } clear Vb.

    (* finish CAS fail case *)
    iIntros "!>". wp_if. by iApply "HΦ". }

  (* successful dequeue *)
  iDestruct "Eq" as %[-> ->].
  iDestruct "HVw" as (Vw (Eqth4' & Eqζh4 & Eqζh4' & _ & ? & ? & NEqV5' & ->)) "[_ %LeVr4]".
  iAssert (⌜ length ((ηs, s) :: D4) = length Vs3 ⌝)%I with "[Hs3]" as %EqL3.
  { iIntros "{# %}". rewrite /Head big_sepL2_length. by iDestruct "Hs3" as %?. }
  have EqTH: toHeadHist th3 ((ηs, s) :: D4) Vs3 !! th4 = Some (#n2, Vr4).
  { set Eq2 := (lookup_weaken _ _ _ _ Eq4' Sub42).
    move : Eq2. rewrite Eqζh4. clear. rewrite lookup_insert_ne; [done|lia]. }
  iDestruct (own_nodes_inj_2' E4 T4 ηs s D4 L4 with "Ns") as %INJ2.
  have Eqth34: (Pos.to_nat th4 - Pos.to_nat th3)%nat = (length ((ηs, s) :: D4) - 1)%nat.
  { set Eq2 := lookup_map_seqP_last_idx' _ _ _ _ EqTH Eqth4'.
    move : Eq2. by rewrite fmap_length zip_with_length_l_eq fmap_length. }
  have Eqn2 : ((ηs, s) :: D4) !! (length ((ηs, s) :: D4) - 1)%nat = Some (η2, n2).
  { apply toHeadHist_lookup_Some in EqTH as (_ & _ & η'' & l'' & Eq & Eq').
    inversion Eq. clear Eq. subst l''. rewrite -Eqth34 (_: η2 = η''); [done|].
    apply (INJ2 n2).
    - apply (elem_of_list_prefix _ _ _ LeCL3).
      move : Eqη. apply elem_of_list_lookup_2.
    - rewrite (elem_of_app ((ηs, s) :: D4)). left. move : Eq'.
      apply elem_of_list_lookup_2. }

  (* we know that D2 = D3 = D4 *)
  have ?: i2 = i.
  { apply (NoDup_lookup _ _ _ η2 (qu_no_dup _ _ _ _ _ _ _ QP3)).
    - by rewrite list_lookup_fmap Eqη.
    - rewrite list_lookup_fmap (prefix_lookup_Some CL2 _ _ (η2,n2)) //.
      by apply (lookup_app_l_Some _ _ _ _ Eqη2). } subst i2.
  have Eqi2: i = (length ((ηs, s) :: D4) - 1)%nat.
  { apply (NoDup_lookup _ _ _ η2 (qu_no_dup _ _ _ _ _ _ _ QP4)).
    - by rewrite list_lookup_fmap (prefix_lookup_Some _ _ _ _ Eqη LeCL3).
    - by rewrite list_lookup_fmap (lookup_app_l_Some _ _ _ _ Eqn2). }
  assert (D4 = D2 ∧ D3 = D2) as [].
  { clear -Eqi2 Eqη2 SubLD2 SubLD3. subst i.
    apply lookup_lt_Some, Nat.lt_sub_lt_add_l in Eqη2. rewrite Nat.lt_succ_r in Eqη2.
    simpl in Eqη2. apply le_S_n in Eqη2.
    have Sub24 : D2 ⊑ D4 by etrans.
    have ? := prefix_length_eq _ _ Sub24 Eqη2. subst D4.
    split; [done|]. by apply : (anti_symm (⊑)). } subst D4 D3.

  clear SubLD2 SubLD3. apply list_sqsubseteq_app_inv in LeDL3.
  apply infos_next_lookup in Eqd as (Eqnn2 & Eqd2 & Eqn2').
  assert (∃ L3', L3 = (η2', n2') :: L3') as [L3' ?].
  { move : Eqn2'. clear -Eqi2.
    rewrite (lookup_app_r (_::_)).
    - rewrite Eqi2 (_: _ - _ + _ - _ = 0)%nat.
      + destruct L3 as [|[]]; simpl; [done|].
        inversion 1. by eexists.
      + by rewrite /= Nat.sub_0_r Nat.add_1_r Nat.sub_diag.
    - rewrite Eqi2 Nat.sub_add; [done|simpl; lia]. } subst L3.

  (* V2 = Vr4, but we probably don't need it. *)
  iDestruct (QueueInv_consistent with "GMA") as %[CON EGCs].

  iDestruct "SEe2" as (eV (Eqve2 & EqvV2 & SYeV)) "SE".
  iAssert (⌜E3 !! en2 = Some eV ∧ set_in_bound eV.(ge_lview) E3 ⌝ ∗
            @{Vn2'} SeenLogview E3 (ge_lview eV))%I
    with "[]" as ([EqeV3 SubeV3]) "#PSV2".
  { iDestruct "SE" as (Eq3) "[SE' _]". rewrite EqvV2 view_at_view_at.
    iFrame "SE'". rewrite (SeenLogview_closed E3). iDestruct "SE'" as %?.
    by iPureIntro. }
  assert (EEq := prefix_lookup_Some _ _ _ _ EqeV3 SubE3).

  destruct QP4 as [ND DT CDT InjT ET MONO ORD ABS].

  set enqId := en2.
  set D' := D2 ++ [(η2', n2')].

  assert (Eqη24 := lookup_weaken _ _ _ _ Eqη2' LeT3).
  have UEq: (∀ id, (enqId, id) ∉ G4.(so)).
  { clear -ND ET Eqη24 LeDL3.
    intros deq Indeq. specialize (ET _ _ Eqη24) as [_ ET2].
    rewrite fmap_cons fmap_app in ND.
    apply (NoDup_app (_::_)) in ND as [_ [ND2 _]]. apply (ND2 η2').
    - right. apply ET2, elem_of_list_fmap.
      exists (enqId, deq). split; [done|]. by apply elem_of_elements.
    - apply elem_of_list_fmap. exists (η2', n2').
      split; [done|]. rewrite -LeDL3. by left. }

  (* we know that 0 < ve2 *)
  assert (NZ := bsq_cons_enq_non_zero _ CON _ _ _ EEq Eqve2).
  assert (SubeV := egcons_logview_closed _ EGCs _ _ EEq).
  have SubM4: set_in_bound M E4. { clear -SubM SubE3. by eapply set_in_bound_mono. }

  set V' := V5'.
  have SubVn2' : Vn2' ⊑ V'. { clear -LeV3' LeV4 LeV5. rewrite /V'. solve_lat. }
  have SubVeV : eV.(ge_view).(dv_comm) ⊑ V'. { rewrite EqvV2. exact SubVn2'. }
  have SubVin : eV.(ge_view).(dv_in) ⊑ Vdeq.(dv_comm) by rewrite dv_in_com EqvV2.

  assert (GIP := graph_insert_edge_props_base _ _ _ (Deq ve2) M Vdeq
                                              EEq SubM4 EGCs SubVin).
  destruct GIP as [b' [deqId M' egV' G' [NEqid _] LeG' [SubM' SubeV'] SUB'
                      [InEnq' InDeq'] FRde EGCs']].
  set Lted := lookup_lt_Some (Es G4) en2 eV EEq.
  assert (EqG' := graph_insert_edge_eq enqId egV' G4 b').
  rewrite -/G' in EqG'. destruct EqG' as (_ & EqEs' & EqSo' & EqCo').
  set E' := G'.(Es).
  have LeE' : E4 ⊑ E' by apply LeG'.
  assert (NI: ∀ e1 e2, (e1, e2) ∈ G4.(com) → e1 ≠ deqId ∧ e2 ≠ deqId).
  { clear. move => ?? /gcons_com_included [/=]. lia. }

  assert (∃ L4', L4 = (η2', n2') :: L4') as [L4' EqL4].
  { clear -LeDL3. destruct L4 as [|? L4'].
    - destruct LeDL3 as []. simplify_list_eq.
    - exists L4'. apply prefix_cons_inv_1 in LeDL3. by subst. }
  assert (∃ Q4', Q4 = (ve2, (eV.(ge_view).(dv_comm))) :: Q4') as [Q4' EqQ4].
  { clear -ABS EqL4 Eqη24 EEq Eqve2. subst L4.
    apply Forall2_cons_inv_r in ABS as ([? ?] & Q4' & (? & ? & ? & ? & Eqve2' & ?) & _ & ->) .
    exists Q4'. f_equal. simplify_map_eq. rewrite Eqve2' in Eqve2. by injection Eqve2 as ->. }

  have CON' : StrongQueueConsistent G'.
  { destruct CON as [CONRA [CONw _ _ [CON0 CON2 [CON3a CON3b] CON4 CON5 CON6 CON7a _]] CON7b].
    have CONRA' : graph_event_is_relacq G'.(Es) (λ _, True).
    { clear -CONRA. by apply graph_insert_event_is_relacq. }
    have FIFO' : queue_FIFO_strong G'.
    { (* 7b *)
      intros e1 v1 eV1 e2 d2 Eqe1 Eqv1.
      rewrite EqCo' elem_of_union elem_of_singleton.
      intros [Eq2|InG4].
      + inversion Eq2; clear Eq2; subst e2 d2.
        assert (e1 ≠ deqId).
        { clear -Eqe1 Eqv1. intros ->. rewrite lookup_app_1_eq in Eqe1.
          inversion Eqe1. by subst eV1. }
        rewrite lookup_app_1_ne in Eqe1; [|done]. intros LE1.
        destruct (CDT e1)  as [_ [ηe1 Eqη1]]. { exists v1. by rewrite Eqe1 /= Eqv1. }
        case (decide (ηe1 ∈ D2.*1)) as [InD2|NInD2].
        { (* must have been dequeued? easy *)
          apply (ET _ _ Eqη1), elem_of_list_fmap in InD2
            as [[e1' d1] [Eqe1' Ine1%elem_of_elements]].
          simpl in Eqe1'; subst e1'. rewrite CON6 in Ine1.
          exists d1. split; [|set_solver+Ine1].
          by apply Nat.lt_le_incl, (gcons_com_included _ _ Ine1). }
        (* not dequeued? must be enqId *)
        have InL4 : ηe1 ∈ L4.*1.
        { apply (elem_of_dom_2 (D:=gset _)), (DT ηe1) in Eqη1.
          move : Eqη1. rewrite elem_of_list_to_set fmap_app elem_of_app.
          set_solver+NInD2. }
        have LB: list_before (D2 ++ L4).*1 η2' ηe1.
        { apply elem_of_list_lookup in InL4 as [i1 Eqi1].
          exists (length D2), ((length D2) + i1)%nat. rewrite fmap_app.
          have ? : (length D2 <= length D2 + i1)%nat by lia.
          split; last split; [..|done].
          - rewrite EqL4 lookup_app_r; [|clear; by rewrite fmap_length].
            by rewrite fmap_length Nat.sub_diag /=.
          - rewrite lookup_app_r; [|by rewrite fmap_length].
            by rewrite fmap_length Nat.add_comm Nat.add_sub. }
        (* TODO: ORD is implied by MONO *)
        assert (LE2 := MONO _ _ _ _ LB Eqη24 Eqη1).
        have Eq2 : e1 = enqId. { clear -LE1 LE2. by apply : anti_symm. }
        subst e1. exists deqId. split; [done|set_solver-].
      + intros Le12. rewrite lookup_app_1_ne in Eqe1.
        * destruct (CON7b _ _ _ _ _ Eqe1 Eqv1 InG4 Le12) as (d1 & Led12 & InG42).
          exists d1. split; [done|]. set_solver+InG42.
        * intros ->.
          apply (Nat.lt_irrefl deqId), (Nat.le_lt_trans _ e2 _ Le12),
                (gcons_com_included _ _ InG4). }
    constructor; [done| |done]. constructor.
    { clear -SubV5 LeV5 NEqV5' CONw.
      apply graph_insert_event_is_writing; [done|]. simpl. intros _ ->.
      apply NEqV5'. apply : (anti_symm (⊑)); [done|solve_lat]. }
    { by apply graph_event_is_relacq_releasing_True. }
    { by apply graph_event_is_relacq_acquiring_True. }
    have EC' : graph_xo_eco G'.(Es).
    { (* 7a *)
      intros e1 e2 eV2 [Eq1|[-> <-]]%lookup_app_1.
      + by apply CON7a.
      + rewrite !elem_of_union !elem_of_singleton.
        intros [Inm|[?|InlV]]; [|by subst e1|];
          apply Nat.lt_le_incl, lookup_lt_is_Some.
        * by apply SubM4, Inm.
        * by apply (egcons_logview_closed _ EGCs _ _ EEq _ InlV). }
    have FP' : functional_pair G'.(com).
    { split.
      + (* 3a *)
        intros [e1 d1] [e2 d2]. rewrite 2!elem_of_union 2!elem_of_singleton /=.
        move => [[-> ->]|InG1] [[-> ->]|InG2] //.
        * intros ?. subst e2. exfalso. move : InG2. rewrite -CON6. by apply UEq.
        * intros ?. subst e1. exfalso. move : InG1. rewrite -CON6. by apply UEq.
        * move : InG1 InG2. by apply CON3a.
      + (* 3b *)
        intros [e1 d1] [e2 d2]. rewrite 2!elem_of_union 2!elem_of_singleton /=.
        move => [[-> ->]|InG1] [[-> ->]|InG2]; [done|..].
        * apply NI in InG2 as [_ InG2]. clear -InG2. by intros <-.
        * apply NI in InG1 as [_ InG1]. clear -InG1. by intros ->.
        * move : InG1 InG2. by apply CON3b. }
    constructor; [| |done|..|done|].
    - (* 0 *)
      intros ??? [Eq1|[-> <-]]%lookup_app_1; [apply (CON0 _ _ _ Eq1)|done].
    - (* 2 *)
      move => e1 e2 /elem_of_union [/elem_of_singleton|InCom].
      + inversion 1. subst e1 e2. split; [done|].
        exists eV. eexists. exists ve2.
        by rewrite (prefix_lookup_Some _ _ _ _ EEq LeE') lookup_app_1_eq /= Eqve2.
      + destruct (NI _ _ InCom). do 2 (rewrite lookup_app_1_ne; [|done]).
        by apply CON2.
    - (* 4 *)
      intros ??. rewrite /= elements_union_singleton; last first.
      { rewrite -CON6. by apply UEq. }
      intros [Eqe|[-> <-]]%lookup_app_1 MB.
      + intros NIne. apply (CON4 _ _ Eqe MB). intros NIn. apply NIne. by right.
      + clear. rewrite /= elem_of_cons. naive_solver.
    - (* 5 *)
      intros e eV' EqeV EqED ee ve eVe Eqee Eqve Inee.
      case (decide (deqId = e)) => ?.
      + subst e. rewrite lookup_app_1_eq in EqeV. inversion EqeV; clear EqeV.
        subst eV'. by exists deqId.
      + rewrite lookup_app_1_ne in EqeV; [|done].
        rewrite lookup_app_1_ne in Eqee; last first.
        { intros ->. apply (egcons_logview_closed _ EGCs _ _ EqeV),
                            lookup_lt_is_Some in Inee. clear -Inee. lia. }
        destruct (CON5 _ _ EqeV EqED ee ve eVe Eqee Eqve Inee) as (de & InG4 & In').
        exists de. split; [|done]. set_solver+InG4.
    - (* 6 *) by rewrite /G' /= CON6.
    - (* 7b *) by apply queue_FIFO_strong_FIFO. }

  have ET': ∀ η eid, T4 !! η = Some eid → η ∈ D'.*1 ↔ eid ∈ (elements G'.(so)).*1.
  { intros η eid EqTη. specialize (ET _ _ EqTη).
    rewrite /D' fmap_app elem_of_app elem_of_list_singleton /=.
    rewrite elements_union_singleton /=; last by apply UEq.
    rewrite elem_of_cons. clear -ET EqTη Eqη24 InjT.
    split; intros [CA|CA].
    - right. by apply ET.
    - left. subst η2'. rewrite EqTη in Eqη24. by inversion Eqη24.
    - right. subst eid. by apply (InjT _ _ _ EqTη Eqη24).
    - left. by apply ET. }
  have CDT' : EM_equiv T4 E'.
  { intros e. rewrite CDT. split; intros [v Eqv].
    - exists v. rewrite lookup_app_1_ne; [done|]. clear -Eqv. intros ->.
      apply list_lookup_fmap_inv' in Eqv as (? & _ & ?%lookup_lt_Some). lia.
    - have ?: deqId ≠ e.
      { intros <-. rewrite lookup_app_1_eq /= in Eqv. by inversion Eqv. }
      rewrite lookup_app_1_ne in Eqv; [by exists v|done]. }
  have ORD': ∀ η1 η2 e1 e2 eV2, list_before (D2 ++ L4).*1 η1 η2 →
      T4 !! η1 = Some e1 → T4 !! η2 = Some e2 → E' !! e2 = Some eV2 →
      e1 ∈ eV2.(ge_lview).
  { intros η1 η22 e1 e2 eV2 LB EqT1 EqT2 EqEV2.
    apply (ORD _ _ _ _ _ LB EqT1 EqT2).
    rewrite lookup_app_1_ne in EqEV2; [done|]. intros ->.
    destruct (CDT deqId) as [[vd Eqv] _]. { by exists η22. } clear -Eqv.
    apply list_lookup_fmap_inv' in Eqv as (? & _ & ?%lookup_lt_Some). lia. }

  have ABS' : Forall2 (λ '(v, V) '(η, _), ∃ e eV,
      T4 !! η = Some e ∧ Es G' !! e = Some eV ∧
      eV.(ge_event) = Enq v ∧ eV.(ge_view).(dv_comm) = V) Q4' L4'.
  { subst Q4 L4. inversion ABS. subst. eapply Forall2_impl; [done|].
    intros [? ?] [? ?] (e' & eV' & ? & ? & ? & ?). exists e', eV'.
    split_and!; [done|by eapply prefix_lookup_Some|done..]. }

  have EqCL4' :
    (ηs, s) :: D2 ++ (η2', n2') :: L4' = (ηs, s) :: (D2 ++ [(η2', n2')]) ++ L4'.
  { clear. by simplify_list_eq. }
  have EqDL4 : D2 ++ (η2', n2') :: L4' = (D2 ++ [(η2', n2')]) ++ L4'.
  { clear. by simplify_list_eq. }

  subst L4. rewrite own_nodes_dequeue.
  iDestruct "Ns" as "[Ns NA]".
  iAssert (@{Vn2'} (n2' >> data) ↦{1} #ve2)%I with "[NA]" as "NA".
  { iClear "#". clear -Eqη24 EEq EqvV2 Eqve2.
    iDestruct "NA" as (e' eV' v' (EqT' & EqE' & Eqv')) "NA".
    rewrite Eqη24 in EqT'. inversion EqT'. clear EqT'. subst e'.
    rewrite EEq in EqE'. simplify_eq. rewrite Eqve2 in Eqv'.
    simplify_eq. by rewrite view_at_view_at. }
  have InEnq : enqId ∈ eV.(ge_lview) by apply (egcons_logview_event _ EGCs _ _ EEq).
  iAssert (@{V'} SeenLinked_logview CL4 T4 E' M')%I
            with "[QV]" as "#SL4'".
  { iIntros (e0 v0 V0 lV0 [InM Eqv]).
    have NDeq: deqId ≠ e0.
    { intros <-.  rewrite lookup_app_1_eq /= in Eqv. by inversion Eqv. }
    rewrite lookup_app_1_ne in Eqv; [|done].
    move : InM. rewrite !elem_of_union !elem_of_singleton.
    intros [InM|[?|IneV]]; [|by subst e0|].
    - iSpecialize ("SL4" $! e0 v0 V0 lV0 with "[%//]").
      iApply (view_at_mono with "SL4"); [done|].
      iDestruct 1 as (η' l' η l) "SL". iExists _, _, _, _.
      by iApply (SeenLinked_emap_mono _ _ _ _ _ _ _ _ _ _ _ LeE' with "SL").
    - iClear "#".
      iSpecialize ("QV" $! enqId eV.(ge_event) eV.(ge_view) eV.(ge_lview)
                      with "[%]"); [rewrite EEq; by destruct eV|].
      iSpecialize ("QV" $! e0 with "[%//]").
      iApply (view_at_mono with "QV"); [done|].
      iDestruct 1 as (η' l' η l) "SL". iExists _, _, _, _.
      by iApply (SeenLinked_emap_mono _ _ _ _ _ _ _ _ _ _ _ LeE' with "SL"). }

  have SubE3': E3 ⊑ E' by etrans.
  have SubE1': E1 ⊑ E' by etrans.
  iAssert (@{V'} SeenLogview E' M')%I with "[]" as "#PSV'".
  { iRevert "PSV PSV2". iIntros "{#} #PSV #PSV2".
    rewrite -2!SeenLogview_union'. iSplit; last iSplit.
    - iApply (view_at_mono with "PSV"); [done|]. by apply SeenLogview_map_mono.
    - rewrite -SeenLogview_singleton; [|by rewrite lookup_app_1_eq]. done.
    - iApply (view_at_mono with "PSV2"); [done|].
      by apply SeenLogview_map_mono. }

  iMod (QueueInv_update _ _ _ _ Q4' _ LeG' EGCs' CON' with "GMA GMA'")
    as "(GMA & GMA' & #Gs')".
  iMod (LDL_update_app _ _ [(η2', n2')] with "LDL") as "[LDL #LDL']".

  iAssert (@{V2} SeenDequeueds γg γ D2)%I with "[SD2 LDL]" as "{SD2} #SD2".
  { rewrite /= Nat.sub_0_r in Eqi2. iFrame "LD4". destruct i as [|i].
    - symmetry in Eqi2. apply nil_length_inv in Eqi2. subst D2.
      iExists G4, T4, []. rewrite list_to_set_nil big_sepL2_nil.
      iFrame "LT4". iDestruct "GS4" as "[$ _]". by rewrite -SeenLogview_empty.
    - rewrite lookup_cons (_: i = length D2 - 1)%nat in Eqη2; last first.
      { clear -Eqi2. rewrite -Eqi2. lia. }
      destruct (lookup_last_Some  _ _ Eqη2) as [D2' EqD2]. iClear "#".
      iDestruct "SD2" as (D20) "[LD20 SD2]". rewrite view_at_objective_iff.
      iDestruct (LDL_master_snap_included with "LDL LD20") as %LED2.
      rewrite EqD2 in LED2.
      assert (D20 = D2') as ->. {
        clear -ND EqD2 LED2.
        move : ND. rewrite fmap_cons NoDup_cons. move => [_].
        rewrite (app_assoc _ [_]) fmap_app NoDup_app.
        move => [ND _]. move : ND. rewrite EqD2 -app_assoc !fmap_app /= => ND.
        destruct LED2 as [D22 EqD2']. rewrite -2!app_assoc in EqD2'.
        destruct (NoDup_app_mid_inj _ [η2'] (D20.*1) (D22.*1) _ ND) as [Eq1 Eq2].
        { clear -EqD2'.
          have Eq': (D2' ++ [(η2, n2)] ++ [(η2', n2')]).*1
                      = (D20 ++ [(η2, n2)] ++ D22).*1. { by f_equal. }
          move : Eq'. by rewrite !fmap_app. }
        have EqL1 := take_app D2' ([(η2, n2)] ++ [(η2', n2')]).
        have EqL2 := take_app D20 ([(η2, n2)] ++ D22).
        rewrite EqD2' (_: length D2' = length D20) in EqL1.
        - by rewrite EqL1 in EqL2.
        - by rewrite -(fmap_length fst D2') -(fmap_length fst D20) Eq1. }
      rewrite -EqD2. iFrame. }

  iAssert (@{V'} SeenDequeueds γg γ (D2 ++ [(η2', n2')]))%I with "[GMA LT]" as "#SD'".
  { iDestruct (view_at_mono_2 _ V' with "SD2") as "[_ SD2']".
    { clear -LeV2 LeV2' SubV35'. rewrite /V'. solve_lat. }
    iDestruct "SD2'" as (G20 T20 M20) "(Gs20 & LT20 & H20)".
    iDestruct (QueueInv_graph_snap_included_2 with "GMA Gs20") as %LeG20.
    iDestruct (LTM_master_snap_included with "LT [$LT20]") as %LeT20.
    iFrame "LDL'". iExists G', T4, (M20 ++ [deqId]). iFrame "LT4".
    rewrite list_to_set_app_L fmap_app. iSplit.
    - iFrame "Gs'". rewrite /= right_id_L -SeenLogview_union'. iSplit.
      + iApply (view_at_mono with "Gs20"); [done|].
        iIntros "[_ SL]". iApply (SeenLogview_map_mono with "SL"); [apply LeG20|done].
      + iClear "#". rewrite -SeenLogview_singleton; [|by rewrite lookup_app_1_eq]. done.
    - rewrite /= big_sepL2_app_same_length; last by right. iSplit.
      + iApply (view_at_mono with "H20"); [done|]. apply big_sepL2_mono.
        intros k ηk ek ? ?. iPureIntro. intros (dk & Eqd & Ind). exists dk. split.
        * apply (lookup_weaken _ _ _ _ Eqd LeT20).
        * by apply (graph_sqsubseteq_com _ _ LeG20).
      + rewrite big_sepL2_singleton. iPureIntro. exists en2. split; [done|].
        set_solver-. }

  have SYE' : SyncEnqueues E' eV.(ge_lview).
  { move : SYeV. by  apply SyncEnqueues_mono. }
  have SYE'' : SyncEnqueues E' M'.
  { apply SyncEnqueues_union; last apply SyncEnqueues_union; [..|done].
    - move : SYE1. by apply SyncEnqueues_mono.
    - clear. intros ???? ->%elem_of_singleton. rewrite lookup_app_1_eq. by inversion 1. }

  (* close the AU *)
  rewrite bi.and_elim_r.
  iMod ("HClose" $! ve2 V' Q4' G' enqId deqId (Enq ve2) (Deq ve2) eV.(ge_view) Vdeq M'
        with "[$GMA' $sV5' Gs']") as "HΦ".
  { (* QueueInv *)
    iSplitL "Gs'"; last first.
    { iPureIntro. do 4 (split; [done|]).
      right. right. do 12 (split; [done|]). by exists eV. }
    (* Private Post *)
    iSplitL "Gs'". { iFrame "Gs' PSV'". }
    iExists γ, γh, γl. iFrame "QII". iExists ηs, s, D', L4', D0, T4. rewrite -EqCL4'.
    iFrame "LS4 LDL' LT4". iSplitR; last iSplitR; last iSplitR; last iSplitR.
    - iPureIntro. rewrite SubD0 SubLD14. clear. by eexists.
    - iExists _, _. by iFrame "SHa Hsa".
    - iFrame "Tl'".
    - iPureIntro. by rewrite (_: D' ++ L4' = D2 ++ (η2', n2') :: L4').
    - iFrame "SL4' PSV'". }
  iIntros "!>".
  (* re-establish the invariant *)
  iMod ("Close" with "[-HΦ NA]") as "_".
  { iNext. iExists Q4', G'. iFrame "GMA".
    iExists ηs, s, (D2 ++ [(η2', n2')]), L4', T4.
    rewrite /QueueInv_no_exist EqCL4'. iFrame "LEL LDL LT". iSplitL "".
    { iPureIntro. constructor; try done; [by rewrite -EqCL4'|by rewrite -EqDL4..]. }
    iSplitL "QV".
    { iIntros (e0 ev0 V0 lV0). case (decide (e0 = deqId)) => [->|?].
      - rewrite lookup_app_1_eq. iIntros (Eq). inversion Eq. clear Eq.
        subst ev0 V0 lV0. rewrite -EqCL4'. by iFrame "SL4'".
      - iClear "#". rewrite lookup_app_1_ne; last done.
        iIntros (Eq). iDestruct ("QV" $! e0 ev0 V0 lV0 Eq) as "SL".
        rewrite SeenLinked_logview_mono; eauto.
        by apply (egcons_logview_closed _ EGCs _ _ Eq). }
    iExists (Vb ⊔ V').
    have ? : Vb ⊑ Vb ⊔ V' by clear;solve_lat.
    iSplitL "ATh Hs3"; last iSplitL "T".
    { rewrite Eqζh4. iExists th3, (Vs3 ++ [V']).
      have LeL' : (1 ≤ length ((ηs, s) :: D2))%nat by clear; simpl; lia.
      rewrite (toHeadHist_insert _ _ _ _ _ η2'); [| |done|done]; last first.
      { clear -LeL' Eqth34 EqTH.
        apply toHeadHist_lookup_Some in EqTH as [? _].
        rewrite Pos2Nat.inj_add Nat.add_sub_swap; [|lia].
        by rewrite Eqth34 Nat.sub_add. }
      iFrame "ATh".
      rewrite -(Head_append _ _ _ _ ((ηs, s) :: D2)). iSplitL "Hs3"; last iSplitR.
      - iApply (view_at_mono with "Hs3"); [done|].
        by apply (Head_mono _ _ E4 E' T4 T4).
      - rewrite view_at_view_at. iExists Vn2'. iSplit; last iSplit.
        + iApply (view_at_mono with "SE"); [done|]. iIntros "SE".
          rewrite /SeenEnqueuedLink decide_False; last first.
          { clear -ND. move : ND. rewrite (fmap_app _ (_::_) (_::_)) NoDup_app.
            intros (_ & NIN & _). intros ?. subst η2'.
            apply (NIN ηs); simpl; by left. }
          iExists enqId, η2, ve2. iSplit.
          { iPureIntro. clear -Eqn2 Eqη24. split; [|done].
            exists (length ((ηs, s) :: D2) - 1)%nat. rewrite 2!list_lookup_fmap.
            split.
            - rewrite (lookup_app_l (_::_)); [|simpl; lia]. by rewrite Eqn2.
            - rewrite Nat.sub_add; [|simpl; lia].
              rewrite (lookup_app_r (_::_)); [|simpl; lia].
              by rewrite Nat.sub_diag. }
          iExists eV. iSplit; [by iPureIntro|].
          by iApply (SeenEvent_mono with "SE").
        + iPureIntro. clear. rewrite elem_of_app. right.
          by rewrite elem_of_list_singleton.
        + by iFrame "LVn2'".
      - rewrite /= view_at_view_at. iExists D2. iFrame "SD'". }
    { iApply (view_at_mono with "T"); [done|].
      iDestruct 1 as (ζl) "[T Ts]". iExists ζl.
      iFrame "T". by iApply (Tail_mono with "Ts"). } iClear "#".
    iApply (view_at_mono with "Ns"); [done|]. by apply own_nodes_map_mono. }

  (* finish CAS successful case *)
  iIntros "!>". wp_if. wp_op.
  iDestruct (view_at_elim with "[] NA") as "NA".
  { by iApply (monPred_in_mono with "sV5'"). }
  wp_read. by iApply "HΦ". (* leaking data field *)
Qed.

Lemma dequeue_spec :
  dequeue_spec' dequeue QueueLocal QueueInv.
Proof.
  intros N DISJ q tid γg G1 M V. iIntros "#sV #Gs" (Φ) "AU".
  iLöb as "IH". wp_rec.
  awp_apply (try_deq_spec with "sV Gs"); [done|].
  iApply (aacc_aupd with "AU"); [done|].
  iIntros (Q G) "QI".
  iAaccIntro with "QI"; first by eauto with iFrame.
  iIntros (x V' Q' G' enqId deqId enq deq Venq Vdeq M') "QI !>".
  iDestruct "QI" as "(QI & sV' & Local & F)".
  iDestruct "F" as %(?&?&?&?&[CASE|CASE]).
  - destruct CASE as (?&?&?). subst Q' G'. iLeft.
    iFrame "QI". iIntros "AU !> _".
    wp_let. wp_op. rewrite bool_decide_false; last lia.
    wp_if. by iApply ("IH" with "AU").
  - iRight.
    iExists x, V', Q', G'. iExists enqId, deqId, enq, deq, Venq, Vdeq, M'.
    iFrame "QI sV' Local". iSplit; [done|]. iIntros "H !> _".
    wp_let. wp_op. rewrite bool_decide_true.
    + wp_if. by iApply "H".
    + destruct CASE as [[_ [? _]]|[_ [? _]]]; lia.
Qed.

End proof.
