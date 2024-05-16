From iris.bi Require Import fractional.
From iris.algebra Require Import excl auth.
From iris.proofmode Require Import tactics.

From gpfsl.algebra Require Import to_agree.
From gpfsl.base_logic Require Import meta_data.
From gpfsl.logic Require Import logatom atomics invariants.

From gpfsl.logic Require Import new_delete.
From gpfsl.logic Require Import proofmode.

From gpfsl.examples Require Import uniq_token map_seq loc_helper.
From gpfsl.examples.exchanger Require Import spec_graph spec_graph_piggyback code.

Require Import iris.prelude.options.

Local Arguments lookup_weaken {_ _ _ _ _ _ _ _}.

#[local] Notation hole := 0%nat (only parsing).
#[local] Notation data := 1%nat (only parsing).

#[local] Notation event_list := (event_list xchg_event).
#[local] Notation graph_event := (graph_event xchg_event).
#[local] Notation graph := (graph xchg_event).

Implicit Types (tid : thread_id) (γ : gname) (x : loc).
Implicit Types (G : graph) (E : event_list).
Implicit Types (N : namespace).

(** Namespace for our internal invariants. *)
Definition xchgN N := N .@ "xchg".
Definition offN N := N .@ "offer".

(* CMRA we need *)
(* a persistent map of from main offers to its info *)
Definition offer_info : Type := gname * gname.

Implicit Types (T : gmap loc offer_info).

#[local] Notation xchg_mapUR' := (agreeMR loc offer_info).
#[local] Notation xchg_mapUR := (authUR xchg_mapUR').

Class xchgG Σ := XChgG {
  xchg_graphG : inG Σ (graphR xchg_event) ;
  xchg_uniqTokG : uniqTokG Σ;
  xchg_mapG : inG Σ xchg_mapUR;
}.
Local Existing Instance xchg_graphG.
Definition xchgΣ : gFunctors :=
  #[GFunctor (graphR xchg_event);
    GFunctor (exclR unitO);
    GFunctor xchg_mapUR ].

Global Instance subG_xchgΣ {Σ} : subG xchgΣ Σ → xchgG Σ.
Proof. solve_inG. Qed.

(** History of the exchange *)
Definition toXChgHist (start : time) (LVs : list (option loc * view)) : absHist :=
  map_seqP start ((λ olv, (#(oloc_to_lit olv.1), olv.2)) <$> LVs).

(** State of the offer *)
Inductive OfferState :=
  | OfferMatching
  | OfferCancelled
  | OfferAccepted (l : loc)
  | OfferAcked (l : loc)
  .

Global Instance OfferState_inhabited : Inhabited OfferState := populate OfferMatching.

Definition offer_hist (s : OfferState) t0 V0 V1 ζ : Prop :=
  let ζ0 : absHist := {[t0 := (#MATCHING, V0)]} in
  match s with
  | OfferMatching => ζ = ζ0
  | OfferCancelled => ζ = <[(t0 + 1)%positive := (#CANCELLED, V1)]> ζ0
  | OfferAccepted l2 | OfferAcked l2 => ζ = <[(t0 + 1)%positive := (#l2, V1)]> ζ0
  end.

Section interp.
Context `{!noprolG Σ, !xchgG Σ, !atomicG Σ}.

Local Existing Instances xchg_graphG xchg_uniqTokG xchg_mapG.

#[local] Notation iProp := (iProp Σ).
#[local] Notation vProp := (vProp Σ).

Implicit Types (EI : bool → vProp).

(* Ghost assertions *)
Definition LTM_snap  γe T : iProp := own (A:=xchg_mapUR) γe (◯ (to_agreeM T)).
Definition LTM_snapv γe T : vProp := ⎡ LTM_snap γe T ⎤.
Definition LTM_ssnap  γe l i : iProp := LTM_snap γe {[l := i]}.
Definition LTM_ssnapv γe l i : vProp := ⎡ LTM_ssnap γe l i ⎤.

Definition LTM_master  γe T : iProp := own (A:=xchg_mapUR) γe (● (to_agreeM T)).
Definition LTM_masterv γe T : vProp := ⎡ LTM_master γe T ⎤.

(** Public inv : Only share the ghost state with the client. *)
Definition ExchangerInv (γg : gname) (q : frac) G : vProp :=
  (* ⌜ ExchangerConsistent G ∧ eventgraph_consistent G ⌝ ∗ *)
  graph_gmasterv γg (q/2) G.

#[global] Instance ExchangerInv_objective γg q G :
  Objective (ExchangerInv γg q G) := _.

#[global] Instance ExchangerInv_fractional γg G :
  Fractional (λ q, ExchangerInv γg q G).
Proof.
  intros p q. rewrite /ExchangerInv -!embed_sep Qp.div_add_distr.
  apply embed_proper. iSplit.
  - iIntros "[$ $]".
  - iIntros "[G1 G2]". iSplitL "G1"; by iFrame.
Qed.

#[global] Instance ExchangerInv_AsFractional γg q G :
  AsFractional (ExchangerInv γg q G) (λ q, ExchangerInv γg q G) q.
Proof. constructor; [done|apply _]. Qed.

Definition ExchangerSeen γx x : vProp :=
  ∃ ζx, x sn⊒{γx} ζx.

#[global] Instance ExchangerSeen_persistent γx x :
  Persistent (ExchangerSeen γx x) := _.

(** AU needed for helping with committing the exchange *)
(* TODO: this can be dealt with sufficiently with just the difference between
  ExchangerLocal and ExchangerLocalLite *)
(* FIXME: AU notation doesn't parse. *)
Definition exchange_AU_atomic_post' γx γg x G1 M Vin1 v1 b1 b2 : exchange_postT :=
  (λ G V' G' exId1 exId2 v2 Vex1 Vex2 M',
      ▷ ExchangerInv γg 1%Qp G' ∗
      ⊒V' ∗
      ⌜ G ⊑ G' ∧ M ⊑ M' ∧
        Vex1.(dv_in) = Vin1 ∧ Vex1.(dv_comm) = V' ∧
        exId1 = length G.(Es) ∧
        G'.(Es) = G.(Es) ++ [mkGraphEvent (Exchange v1 v2) Vex1 M'] ∧
        exId1 ∈ M' ∧ exId1 ∉ M ⌝ ∗
      ( ⌜ (* CANCELLED case *)
          v2 = CANCELLED ∧ G'.(so) = G.(so) ∧ G'.(com) = G.(com) ∧
          eventgraph_consistent G' ∧ ExchangerConsistent G' ∧
          b1 = true ⌝ ∧
          @{V'} (graph_snap γg G' M' ∗ ExchangerSeen γx x)
        ∨ (* SUCCESS case *)
        ⌜ 0 ≤ v2 ∧
          (length G1.(Es) ≤ exId2)%nat ∧
          exId2 ∈ M' ∧ exId2 ∉ M ∧ exId1 ≠ exId2
          (* This fixes the order in which the AUs are committed.
            TODO: generalize so that the client can pick the order *)
          ∧ (v1 ≠ v2 → v1 > v2 ↔ (exId1 < exId2)%nat)
          ∧ b1 = false ⌝ ∗
          ( (* if my event comes in later *)
            ⌜ (exId2 < exId1)%nat ∧ b2 = false ∧
              G.(Es) !! exId2 = Some (mkGraphEvent (Exchange v2 v1) Vex2 M') ∧
              G'.(so) = {[ (exId1, exId2); (exId2, exId1) ]} ∪ G.(so) ∧
              G'.(com) = {[ (exId1, exId2); (exId2, exId1) ]} ∪ G.(com) ∧
              exId1 ∉ (elements G.(so)).*1 ∧ exId2 ∉ (elements G.(so)).*1 ∧
              eventgraph_consistent G' ∧ ExchangerConsistent G' ⌝ ∗
              @{V'} (graph_snap γg G' M' ∗ ExchangerSeen γx x)
            (* else if my event comes in earlier *)
            ∨ ⌜ (exId1 < exId2)%nat ∧ b2 = true ∧
                G'.(so) = G.(so) ∧ G'.(com) = G.(com) ⌝ ∗
              @{V'} (graph_snap γg G' (M' ∖ {[exId2]}) ∗ ExchangerSeen γx x)))
    )%I.

Definition exchange_priv_post' γx γg x v1 (Q : Z → vProp) : exchange_postT :=
  (λ G V' G' exId1 exId2 v2 Vex1 Vex2 M',
    (⌜ 0 ≤ v2 ∧ (exId1 < exId2)%nat ⌝ → ∃ G'',
      ⌜ G' ⊑ G'' ∧
        exId2 = length G'.(Es) ∧
        G''.(Es) = G'.(Es) ++ [mkGraphEvent (Exchange v2 v1) Vex2 M'] ∧
        G''.(so) = {[ (exId1, exId2); (exId2, exId1) ]} ∪ G.(so) ∧
        G''.(com) = {[ (exId1, exId2); (exId2, exId1) ]} ∪ G.(com) ∧
        exId1 ∉ (elements G'.(so)).*1 ∧ exId2 ∉ (elements G'.(so)).*1 ⌝ ∗
    @{V'}(graph_snap γg G'' M' ∗ ExchangerSeen γx x)) -∗ Q v2
  )%I.

Definition exchange_AU_proof' (EI : bool → vProp) (N : namespace)
  γx γg x G1 M Vin1 v1
  (Q : _ → vProp)
  {TA' TB' : tele} (α' : TA' → vProp) (β' Φ' : TA' → TB' → vProp)
  : vProp :=
    atomic_update_proof EI (⊤ ∖ ↑N) (↑histN)
      α' β' Φ'
      (tele_app (TT:= [tele _]) (exchange_AU_atomic_pre ExchangerInv γg))
      (λ b1 b2,
        (tele_app (TT:= [tele _])
        (λ G, tele_app (TT:= [tele _ _ _ _ _ _ _ _])
        (exchange_AU_atomic_post' γx γg x G1 M Vin1 v1 b1 b2 G))))
      (tele_app (TT:= [tele _])
        (λ G, tele_app (TT:= [tele _ _ _ _ _ _ _ _])
        (exchange_priv_post' γx γg x v1 Q G)))
  .

Definition offer_res
  o γk (P : vProp) (Q: Z → vProp) (v1 : Z) V0 V1 (s : OfferState) : vProp :=
  match s with
  | OfferMatching => @{V0} ((o >> data) ↦ #v1 ∗ P)
  | OfferAccepted l2 => @{V1} (∃ v2 : Z, (l2 >> data) ↦ #v2 ∗ Q v2)
  | _ => UTok γk
  end
  .

#[global] Instance offer_res_Objective o γk P Q v1 V0 V1 s :
  Objective (offer_res o γk P Q v1 V0 V1 s).
Proof. destruct s; apply _. Qed.

(* Offer inv keeps the full writer permission, so that everyone can only CAS
  using this invariant. *)
Definition offer_rep (o : loc) γo γk v1 t0 V0 P Q : vProp :=
  ∃ s ζo V1, ⌜ offer_hist s t0 V0 V1 ζo ∧ 0 ≤ v1 ⌝ ∗
             (∃ Vo, @{Vo} o sw⊒{γo} ζo) ∗
             offer_res o γk P Q v1 V0 V1 s.

(* Invariant of offer, created by the helpee.
  We use invariant to have agreement on P Q; otherwise we would need saved predicate!
  (where laters wouldn't be a problem, but ghost names are.) *)
Definition offer_inv EI N γx γg x o γo γk t0 V0 : vProp :=
  ∃ v P Q, inv (offN N) (offer_rep o γo γk v t0 V0 P Q) ∗
  ∃ M1 Vin1,
    @{V0} (
      ⊒Vin1 ∗ (* store the Vin of the helpee *)
      ∃ G1, graph_snap γg G1 M1 ∗
      ∃ (TA' TB' : tele) (α' : TA' → vProp) (β' Φ' : TA' → TB' → vProp),
      □ (P -∗ atomic_update (⊤ ∖ ↑N) (↑histN) α' β' Φ') ∗
      □ (exchange_AU_proof' EI N γx γg x G1 M1 Vin1 v Q α' β' Φ')
    ).

(* Main offer is created by the helpee and write to the exchange.
  A helper will just offer a match on a main offer. *)
Definition main_offer EI N γx γg x T o V : vProp :=
  ∃ γo γk,
    ⌜ T !! o = Some (γo, γk) ⌝ ∗      (* meta-data *)
    (∃ ζo, @{V} o sn⊒{γo} ζo) ∗       (* atomic observation *)
    (∃ ζ, o sw↦{γo} ζ) ∗             (* atomic ownership *)
    ∃ t0 V0, ⌜ V0 ⊑ V ⌝ ∗
      offer_inv EI N γx γg x o γo γk t0 V0 (* offer invariant *)
      .

Definition main_offers EI N γx γg x T (os : list (loc * view)) : vProp :=
  [∗ list] oV ∈ os, let '(o, V) := oV in main_offer EI N γx γg x T o V.

Definition xchg_locs EI N γx γg x T LVs os : vProp :=
  (∃ t0, let ζx := (toXChgHist t0 LVs) in x at↦{γx} ζx) ∗
  main_offers EI N γx γg x T os ∗
  ⌜ filter (is_Some ∘ fst) LVs = (λ p, (Some p.1, p.2)) <$>os ∧
    dom T ≡ list_to_set (os.*1)⌝.

Definition ExchangerBaseInv_no_exist
  EI N γg x G γt γx LVs os T : vProp :=
  LTM_masterv γt T ∗
  ∃ Vb, @{Vb} xchg_locs EI N γx γg x T LVs os
  .

Definition ExchangerBaseInv EI N γt γx γg x G : vProp :=
  ∃ LVs os T, ExchangerBaseInv_no_exist EI N γg x G γt γx LVs os T.

(* Our internal invariant keeps all the physical resources, as well as enough
  ghost resources (`ExchangerInv`) to maintain agreement with the client. *)
Definition ExchangerInternalInv EI N γt γx γg x : vProp :=
  ∃ G, ⌜ ExchangerConsistent G ∧ eventgraph_consistent G ⌝ ∗
         ExchangerInv γg 1 G ∗ ExchangerBaseInv EI N γt γx γg x G.

#[global] Instance ExchangerInternalInv_objective EI N γt γx γg x :
  Objective (ExchangerInternalInv EI N γt γx γg x) := _.

Definition InternInv EI N γt γx γg x :=
  inv (xchgN N) (ExchangerInternalInv EI N γt γx γg x).

(** ExchangerLocal assertion, specific to this implementation---------------- *)
Definition ExchangerLocalLite γg x G logV : vProp :=
  graph_snap γg G logV
  ∗ ∃ (γt γx : gname), ExchangerSeen γx x
  ∗ meta x nroot (γt,γx).

#[global] Instance ExchangerLocalLite_persistent γg x G M :
  Persistent (ExchangerLocalLite γg x G M) := _.
#[global] Instance ExchangerLocalLite_timeless γg x G M :
  Timeless (ExchangerLocalLite γg x G M) := _.

Definition ExchangerLocal EI N γg x G logV : vProp :=
  graph_snap γg G logV
  ∗ ∃ (γt γx : gname), ExchangerSeen γx x
  ∗ meta x nroot (γt,γx)
  ∗ InternInv EI N γt γx γg x.

#[global] Instance ExchangerLocal_persistent EI N γg x G M :
  Persistent (ExchangerLocal EI N γg x G M) := _.
End interp.

(** Properties of history *)
Lemma toXChgHist_lookup_Some t0 LVs t v V :
  toXChgHist t0 LVs !! t = Some (v, V) ↔
  (t0 ≤ t)%positive
  ∧ ∃ on, v = #(oloc_to_lit on)
  ∧ LVs !! (Pos.to_nat t - Pos.to_nat t0)%nat = Some (on, V).
Proof.
  rewrite lookup_map_seqP_Some. f_equiv.
  rewrite list_lookup_fmap fmap_Some. split.
  - intros ([] & ? & ?). simplify_eq. naive_solver.
  - intros (on & -> & ?). exists (on, V). naive_solver.
Qed.

Lemma toXChgHist_lookup_Some' {t0 LVs t v V} :
  toXChgHist t0 LVs !! t = Some (v, V) →
  ∃ on, v = #(oloc_to_lit on) ∧ (on, V) ∈ LVs.
Proof.
  rewrite toXChgHist_lookup_Some.
  intros (_ & on & Eq & Eql). exists on. split; [done|].
  revert Eql. apply elem_of_list_lookup_2.
Qed.

Lemma toXChgHist_lookup_Some_loc {t0 LVs t} {l : loc} {V} :
  toXChgHist t0 LVs !! t = Some (#l, V) → (Some l, V) ∈ LVs.
Proof.
  intros (on & Eq & In)%toXChgHist_lookup_Some'. by destruct on; simplify_eq.
Qed.

Lemma toXChgHist_lookup_None {t0 LVs t} :
  toXChgHist t0 LVs !! t = None ↔
  (t < t0)%positive ∨ (t0 +p (length LVs) ≤ t)%positive.
Proof. by rewrite lookup_map_seqP_None fmap_length. Qed.

Lemma toXChgHist_lookup_Some_None {t0 LVs t p} :
  toXChgHist t0 LVs !! t = Some p →
  toXChgHist t0 LVs !! (t + 1)%positive = None →
  (Pos.to_nat (t + 1)%positive - Pos.to_nat t0)%nat = length LVs ∧ (1 ≤ length LVs)%nat.
Proof.
  intros EqS EqN.
  assert (EqL := lookup_map_seqP_last_idx _ _ _ _ EqS EqN).
  destruct p as [v V].
  apply toXChgHist_lookup_Some in EqS as [Letx0 [on [Eqv Eqt]]].
  have EqL1 :  (1 ≤ length LVs)%nat.
  { clear -Eqt Letx0. apply lookup_lt_Some in Eqt. lia. }
  move : EqL. rewrite fmap_length /pos_add_nat; lia.
Qed.

Lemma toXChgHist_comparable_nullable_loc {LVs t0 t v} (on : option loc) :
  fst <$> toXChgHist t0 LVs !! t = Some v →
  ∃ vl : lit, v = #vl ∧ lit_comparable (oloc_to_lit on) vl.
Proof.
  rewrite -lookup_fmap lookup_fmap_Some.
  move => [[? V] [/=-> /toXChgHist_lookup_Some'[on' [-> _]]]].
  exists (oloc_to_lit on'). split; [done|].
  destruct on, on'; constructor.
Qed.

Lemma toXChgHist_comparable_0 t0 LVs :
  ∀ t v, fst <$> toXChgHist t0 LVs !! t = Some v →
  ∃ vl : lit, v = #vl ∧ lit_comparable 0 vl.
Proof. intros ??. by apply (toXChgHist_comparable_nullable_loc None). Qed.

Lemma toXChgHist_comparable_loc t0 LVs (l : loc):
  ∀ t v, fst <$> toXChgHist t0 LVs !! t = Some v →
  ∃ vl : lit, v = #vl ∧ lit_comparable l vl.
Proof. intros ??. by apply (toXChgHist_comparable_nullable_loc (Some l)). Qed.

Lemma toXChgHist_insert t0 LVs t on V :
  (Pos.to_nat t - Pos.to_nat t0)%nat = length LVs →
  (1 ≤ length LVs)%nat →
  <[t := (#(oloc_to_lit on), V)]>(toXChgHist t0 LVs) =
  toXChgHist t0 (LVs ++ [(on, V)]).
Proof.
  intros Eq ?. apply map_eq.
  intros i. case (decide (i = t)) => [->|?].
  - rewrite lookup_insert. symmetry.
    apply toXChgHist_lookup_Some. split; [lia|].
    rewrite Eq !lookup_app_r // Nat.sub_diag /=. naive_solver.
  - rewrite lookup_insert_ne; [|done].
    destruct (toXChgHist t0 LVs !! i) as [[vi Vi]|] eqn:Eqi; rewrite Eqi; symmetry.
    + apply toXChgHist_lookup_Some in Eqi as (Letn & on' & -> & Eq1).
      apply toXChgHist_lookup_Some. split; [done|].
      exists on'. split; [done|]. by apply (lookup_app_l_Some _ _ _ _ Eq1).
    + apply toXChgHist_lookup_None.
      apply toXChgHist_lookup_None in Eqi as [?|Eqi]; [by left|right].
      rewrite app_length /=. move : Eqi.
      rewrite Nat.add_1_r pos_add_succ_r_2.
      rewrite (_: t0 +p length LVs = t); [lia|]. rewrite -Eq /pos_add_nat; lia.
Qed.

Lemma toXChgHist_insert_next_fresh {t0 LVs t p} on V  :
  toXChgHist t0 LVs !! t = Some p →
  toXChgHist t0 LVs !! (t + 1)%positive = None →
  <[(t + 1)%positive := (#(oloc_to_lit on), V)]>(toXChgHist t0 LVs) =
  toXChgHist t0 (LVs ++ [(on, V)]).
Proof.
  intros EqS EqN. destruct (toXChgHist_lookup_Some_None EqS EqN).
  by apply toXChgHist_insert.
Qed.

Lemma filter_is_Some_fst_in
  {LVs : list (option loc * view)} {os : list (loc * view)} {l V} :
  filter (is_Some ∘ fst) LVs = (λ p : loc * view, (Some p.1, p.2)) <$> os →
  (Some l, V) ∈ LVs → (l, V) ∈ os.
Proof.
  intros Eqso InlV.
  assert (Inl2 : (Some l, V) ∈ (λ p, (Some p.1, p.2)) <$> os).
  { rewrite -Eqso elem_of_list_filter. split; [clear; eauto|done]. }
  apply elem_of_list_fmap in Inl2 as ([] & Eql2 & ?).
  simpl in Eql2. by inversion Eql2.
Qed.

Lemma filter_is_Some_None (LVs : list (option loc * view)) :
  (∀ o V, (o, V) ∈ LVs → o = None) →
  filter (is_Some ∘ fst) LVs = [].
Proof.
  intros oV. apply filter_nil_iff, Forall_forall => [[o V] /oV ->].
  by inversion 1.
Qed.

Lemma filter_is_Some_app_None (LVs : list (option loc * view)) V :
  filter (is_Some ∘ fst) (LVs ++ [(None,V)]) = filter (is_Some ∘ fst) LVs.
Proof.
  rewrite filter_app (filter_is_Some_None [(_,_)]).
  - by rewrite app_nil_r.
  - intros ?? Eq%elem_of_list_singleton. by inversion Eq.
Qed.

(** Properties of OfferState *)
(* Needed for CAS: any value in a history of the offer is comparable to 0. *)
Lemma offer_hist_comparable_0 {s t0 V0 V1 ζ} :
  offer_hist s t0 V0 V1 ζ →
  (∀ t v, fst <$> ζ !! t = Some v → ∃ vl : lit, v = #vl ∧ lit_comparable 0 vl).
Proof.
  intros OH t v ([v2 V2] & Eq1 & Eqt)%lookup_fmap_Some'. simpl in Eq1. subst v2.
  destruct s as [| |l|l]; simpl in OH; subst ζ.
  - apply lookup_singleton_Some in Eqt as [-> Eqt]. inversion Eqt. subst.
    exists 0. split; [done|constructor].
  - assert (Eqv: v = #0 ∨ v = #CANCELLED).
    { apply lookup_insert_Some in Eqt as [[_ Eq1]|[_ Eq1%lookup_singleton_Some]];
        naive_solver. }
    destruct Eqv; subst v; eexists; (split;[done|constructor]).
  - assert (Eqv: v = #0 ∨ v = #l).
    { apply lookup_insert_Some in Eqt as [[_ Eq1]|[_ Eq1%lookup_singleton_Some]];
        naive_solver. }
    destruct Eqv; subst v; eexists; (split;[done|constructor]).
  - assert (Eqv: v = #0 ∨ v = #l).
    { apply lookup_insert_Some in Eqt as [[_ Eq1]|[_ Eq1%lookup_singleton_Some]];
        naive_solver. }
    destruct Eqv; subst v; eexists; (split;[done|constructor]).
Qed.

Lemma offer_hist_lookup_0 {s t0 V0 V1 ζ} :
  offer_hist s t0 V0 V1 ζ →
  ∀ t' V', ζ !! t' = Some (#MATCHING, V') ↔ t' = t0 ∧ V' = V0.
Proof.
  intros OF t' V'; destruct s; simpl in OF; subst ζ;
    [rewrite lookup_singleton_Some; naive_solver|..];
    (rewrite lookup_insert_Some lookup_singleton_Some;
      split; [naive_solver|]; intros [-> ->];
      right; split; [lia|naive_solver]).
Qed.

Lemma offer_hist_lookup_n0 {s t0 V0 V1 ζ} :
  offer_hist s t0 V0 V1 ζ →
  ∀ t' (v' : lit) V',
    ζ !! t' = Some (#v', V') → v' ≠ MATCHING →
    s ≠ OfferMatching ∧ t' = (t0 + 1)%positive ∧ V' = V1.
Proof.
  intros OF t' v' V'. destruct s; simpl in OF; subst ζ;
    [rewrite lookup_singleton_Some; naive_solver|..];
    rewrite lookup_insert_Some lookup_singleton_Some; naive_solver.
Qed.

Lemma offer_hist_lookup_cancelled {s t0 V0 V1 ζ} :
  offer_hist s t0 V0 V1 ζ →
  ∀ t' V',
    ζ !! t' = Some (#CANCELLED, V') →
    s = OfferCancelled ∧ t' = (t0 + 1)%positive ∧ V' = V1.
Proof.
  intros OF t' V'. destruct s; simpl in OF; subst ζ;
    [rewrite lookup_singleton_Some; naive_solver|..];
    rewrite lookup_insert_Some lookup_singleton_Some; naive_solver.
Qed.

Lemma offer_hist_lookup_matched {s t0 V0 V1 ζ} :
  offer_hist s t0 V0 V1 ζ →
  ∀ t' (l' : loc) V',
    ζ !! t' = Some (#l', V') →
    (s = OfferAccepted l' ∨ s = OfferAcked l') ∧ t' = (t0 + 1)%positive ∧ V' = V1.
Proof.
  intros OF t' l' V'. destruct s; simpl in OF; subst ζ;
    [rewrite lookup_singleton_Some; naive_solver|..];
    rewrite lookup_insert_Some lookup_singleton_Some; naive_solver.
Qed.

(** Graph insertions *)
Lemma exchange_cancel_graph_insert
  G v (M : logView) (V : dataView) :
  V.(dv_comm) ⊑ V.(dv_wrt) →
  ExchangerConsistent G →
  let e := length G.(Es) in
  let eV := Exchange v CANCELLED in
  let egV := mkGraphEvent eV V ({[e]} ⊔ M) in
  let G' := graph_insert_event egV G in
  ExchangerConsistent G'.
Proof.
  intros ? [CONDv CON2a CON2b [CON3a CON3b] CON4 CON5].
  intros e eV egV G'.
  constructor; [ |done|..|done| |done].
  - (* DView *) by apply graph_insert_event_is_releasing.
  - (* 2b *)
    intros e1 e2 (? & eV1 & eV2 & ve1 & ve2 & Eq1 & Eq2 & ?)%CON2b.
    split; [done|].
    exists eV1, eV2, ve1, ve2. split; last split; [..|done].
    + by eapply lookup_app_l_Some.
    + by eapply lookup_app_l_Some.
  - (* 4 *)
    intros e0 eV0. case (decide (e = e0)) => ?.
    + subst e0. rewrite lookup_app_1_eq. inversion 1. subst eV0.
      intros ?. by exists v.
    + rewrite lookup_app_1_ne; [by apply CON4|done].
Qed.

Lemma exchange_commit_graph_insert
  (b : bool) G v1 v2 (M1 M2 : logView) (V1 V2 : dataView) :
  V1.(dv_comm) ⊑ V1.(dv_wrt) → V2.(dv_comm) ⊑ V2.(dv_wrt) →
  V1.(dv_in) ⊏ V2.(dv_comm) → V2.(dv_in) ⊏ V1.(dv_comm) →
  0 ≤ v1 → 0 ≤ v2 →
  ExchangerConsistent G →
  let emi := length G.(Es) in let emx := S (length G.(Es)) in
  let M' := {[emi;emx]} ∪ (if b then M1 else M2) ∪ (if b then M2 else M1) in
  let Ev1 := (Exchange v1 v2) in
  let Ev2 := (Exchange v2 v1) in
  let Emi := mkGraphEvent (if b then Ev1 else Ev2) (if b then V1 else V2) M' in
  let Emx := mkGraphEvent (if b then Ev2 else Ev1) (if b then V2 else V1) M' in
  let G' := graph_insert2 Emi Emx G in
  ExchangerConsistent G'.
Proof.
  intros LeV11 LeV22 LtV12 LtV21 Pos1 Pos2.
  intros [CONDv [CON2a1 CON2a2] CON2b [CON3a CON3b] CON4 CON5].
  intros emi emx M' Ev1 Ev2 Emi Emx G'.
  have NEq12 : emi ≠ emx by lia.
  have NIne12 : (emi, emx) ∉ G.(com). { move => /gcons_com_included [/=]. lia. }
  have NIne21 : (emx, emi) ∉ G.(com). { move => /gcons_com_included [/=]. lia. }
  have Eqe12 : (emi = S emx ∨ emx = S emi) by lia.
  have EqEs' : G'.(Es) = (G.(Es) ++ [Emi]) ++ [Emx] by apply (app_assoc _ [_] [_]).
  have Eqemx : emx = length (Es G ++ [Emi]). { rewrite app_length /=. lia. }
  constructor; [|split| |split|..].
  - (* DView *) rewrite /= (app_assoc _ [_]). clear -LeV11 LeV22 CONDv.
    apply graph_insert_event_is_releasing;
      [apply graph_insert_event_is_releasing|]; [done|..]; by destruct b.
  - (* 2a1 *)
    intros i j. rewrite /= elem_of_union CON2a1. clear. set_solver.
  - (* 2a2 *)
    intros e. clear -CON2a2 NEq12. specialize (CON2a2 e). rewrite elem_of_union.
    set_solver.
  - (* 2b *)
    intros i j. rewrite !elem_of_union !elem_of_singleton.
    rewrite -/emi -/emx.
    intros [[Eq|Eq]|(? & eVi & eVj & ve1 & ve2 & Eq1 & Eq2 & ?)%CON2b].
    + rewrite EqEs'. inversion Eq. subst i j. split; [done|].
      do 2 eexists. exists (if b then v1 else v2), (if b then v2 else v1).
      split; [by rewrite lookup_app_1_ne; [rewrite lookup_app_1_eq|by rewrite -Eqemx]|].
      split; [by rewrite Eqemx lookup_app_1_eq|]; destruct b; done.
    + rewrite EqEs'. inversion Eq. subst i j. split; [clear -Eqe12; naive_solver|].
      do 2 eexists. exists (if b then v2 else v1), (if b then v1 else v2).
      split; [by rewrite Eqemx lookup_app_1_eq|].
      split; [by rewrite lookup_app_1_ne; [rewrite Eqemx lookup_app_1_eq|by rewrite -Eqemx]|].
      destruct b; done.
    + split; [done|]. exists eVi, eVj, ve1, ve2.
      split; last split; [..|done]; by apply lookup_app_l_Some.
  - (* 3a *)
    intros [] []. rewrite !elem_of_union !elem_of_singleton.
    intros [[->| ->]|In1] [[->| ->]|In2]; simpl; auto.
    + move : In2 => /gcons_com_included [/=]. clear ; lia.
    + move : In2 => /gcons_com_included [/=]. clear ; lia.
    + move : In1 => /gcons_com_included [/=]. clear ; lia.
    + move : In1 => /gcons_com_included [/=]. clear ; lia.
    + apply (CON3a _ _ In1 In2).
  - (* 3b *)
    intros [] []. rewrite !elem_of_union !elem_of_singleton.
    intros [[->| ->]|In1] [[->| ->]|In2]; simpl; auto.
    + move : In2 => /gcons_com_included [/=]. clear ; lia.
    + move : In2 => /gcons_com_included [/=]. clear ; lia.
    + move : In1 => /gcons_com_included [/=]. clear ; lia.
    + move : In1 => /gcons_com_included [/=]. clear ; lia.
    + apply (CON3b _ _ In1 In2).
  - (* 4 *)
    intros e eV EqeV NIG'.
    have NIG : e ∉ (elements G.(com)).*1. { clear -NIG'. set_solver. }
    have ? : e ≠ emi. {
      clear -NIG'. intros => ?. subst e. simpl in NIG'.
      apply NIG', elem_of_list_fmap. exists (emi, emx). set_solver. }
    have ? : e ≠ emx. {
      clear -NIG'. intros => ?. subst e. simpl in NIG'.
      apply NIG', elem_of_list_fmap. exists (emx, emi). set_solver. }
    revert EqeV NIG. rewrite EqEs'.
    do 2 (rewrite lookup_app_1_ne; [|lia]).
    apply CON4.
  - by rewrite /= CON5.
Qed.

Section interp_props.
Context `{!noprolG Σ, !xchgG Σ, !atomicG Σ}.

Local Existing Instances xchg_graphG xchg_uniqTokG xchg_mapG.

#[local] Notation iProp := (iProp Σ).
#[local] Notation vProp := (vProp Σ).

Implicit Types (EI : bool → vProp).

(** * PROPERTIES OF ASSERTIONS -------------------------------------------------*)

(** * Ghost state rules *)
Lemma LTM_master_alloc T :
  ⊢ |==> ∃ γt, LTM_master γt T.
Proof. by apply own_alloc, auth_auth_valid, to_agreeM_valid. Qed.

Lemma LTM_master_snap_included γ T T' :
  LTM_master γ T -∗ LTM_snap γ T' -∗ ⌜T' ⊆ T⌝.
Proof.
  iIntros "o1 o2".
  iCombine "o1 o2" gives %[INCL ?]%auth_both_valid_discrete.
  iPureIntro. by move : INCL => /= /to_agreeM_included.
Qed.
Lemma LTM_master_ssnap_lookup γ M l i :
  LTM_master γ M -∗ LTM_ssnap γ l i -∗ ⌜ M !! l = Some i ⌝.
Proof.
  iIntros "LTm VMs". by iDestruct (LTM_master_snap_included with "LTm VMs")
                        as %SUB%map_singleton_subseteq_l.
Qed.
Lemma LTM_update γ T T' (SUB: T ⊆ T'):
  LTM_master γ T ==∗ LTM_master γ T' ∗ LTM_snap γ T'.
Proof.
  rewrite -own_op.
  by apply own_update, auth_update_alloc, to_agreeM_local_update.
Qed.
Lemma LTM_snap_sub γ T T' (Le: T ⊆ T') : LTM_snap γ T' ⊢ LTM_snap γ T.
Proof.
  by apply own_mono, auth_frag_mono, to_agreeM_included.
Qed.
Lemma LTM_update_insert γ T l i (FR: l ∉ dom T):
  LTM_master γ T ==∗ LTM_master γ (<[l := i]>T) ∗ LTM_ssnap γ l i.
Proof.
  iIntros "LTm".
  iMod (LTM_update with "LTm") as "[$ Snap]".
  { by apply insert_subseteq, (not_elem_of_dom (D:= gset _)). }
  iIntros "!>". iApply (LTM_snap_sub with "Snap").
  by apply insert_mono, gmap_subseteq_empty.
Qed.
Lemma LTM_master_fork γ T :
  LTM_master γ T ==∗ LTM_master γ T ∗ LTM_snap γ T.
Proof. by apply LTM_update. Qed.

(** * ExchangerInv *)
(* TODO: we should not go under graph_master *)
Lemma ExchangerInv_agree γg q G q' G' :
  ExchangerInv γg q G -∗ ExchangerInv γg q' G' -∗ ⌜ G' = G ⌝.
Proof.
  iIntros "G1 G2". by iDestruct (ghost_graph_master_agree with "G1 G2") as %?.
Qed.

Lemma ExchangerInv_graph_master γg q G :
  ⌜eventgraph_consistent G⌝ ∗ ExchangerInv γg q G
  ⊣⊢ graph_master γg (q/2) G.
Proof. rewrite /graph_master. iSplit; by iIntros "[$ $]". Qed.

Lemma ExchangerInv_graph_master' γg q G :
  ⌜eventgraph_consistent G⌝ ∗ ExchangerInv γg q G ⊢ graph_master γg (q/2) G.
Proof. by rewrite ExchangerInv_graph_master. Qed.

Lemma ExchangerInv_graph_master_agree γg q G q' G' :
  graph_master γg q G -∗ ExchangerInv γg q' G' -∗
  ⌜ G' = G ⌝ ∗ graph_master γg q G ∗ graph_master γg (q'/2) G.
Proof.
  rewrite -ExchangerInv_graph_master /graph_master.
  iIntros "[G1 #F] G2".
  iDestruct (ExchangerInv_agree _ (2 * q)%Qp with "[G1] G2") as %->.
  { rewrite /ExchangerInv -{2}(Qp.mul_1_r 2) Qp.div_mul_cancel_l Qp.div_1. iFrame. }
  rewrite /ExchangerInv. by iFrame "F G1 G2".
Qed.

(** * Accessors *)
Lemma ExchangerBaseInv_unfold_snap EI N γg γt γx x G T0 :
  ExchangerBaseInv EI N γt γx γg x G -∗
  LTM_snapv γt T0 -∗
  ∃ LVs os T, ExchangerBaseInv_no_exist EI N γg x G γt γx LVs os T ∗ ⌜ T0 ⊆ T ⌝.
Proof.
  iDestruct 1 as (???) "(LTm & Locs)". iIntros "LTs". iExists _, _, _.
  iDestruct (LTM_master_snap_included with "LTm LTs") as %?. by iFrame.
Qed.

Lemma main_offer_own_loc_prim EI N γx γg x T n V :
  main_offer EI N γx γg x T n V ⊢ ∃ C : cell, n p↦{1} C.
Proof.
  iDestruct 1 as (γ ? _) "(_ & [%ζi Oi] & _)".
  by iApply (AtomicPtsTo_own_loc_prim with "Oi").
Qed.

Lemma main_offers_app EI N γx γg x T os1 os2 :
  main_offers EI N γx γg x T (os1 ++ os2) ⊣⊢
  main_offers EI N γx γg x T os1 ∗ main_offers EI N γx γg x T os2.
Proof. by apply big_sepL_app. Qed.

Lemma main_offers_map_mono {EI N γx γg x T T' os} :
  T ⊆ T' → main_offers EI N γx γg x T os ⊢ main_offers EI N γx γg x T' os.
Proof.
  intros ?. apply big_sepL_mono => i [o V] Eqi.
  iDestruct 1 as (γo γk Eqo) "I".
  iExists γo, γk. iFrame. iPureIntro. by apply (lookup_weaken Eqo).
Qed.

Lemma main_offers_access {EI N γx γg x T os o V} :
  (o, V) ∈ os →
  main_offers EI N γx γg x T os ⊢
  main_offer EI N γx γg x T o V ∗
  (main_offer EI N γx γg x T o V -∗ main_offers EI N γx γg x T os).
Proof.
  intros [i Eqi]%elem_of_list_lookup.
  iIntros "Offs". by iApply (big_sepL_lookup_acc _ _ _ _ Eqi with "Offs").
Qed.

Lemma main_offers_own_loc_prim {EI N γx γg x T os o V} :
  (o, V) ∈ os → main_offers EI N γx γg x T os ⊢ ∃ C : cell, o p↦{1} C.
Proof.
  iIntros (Ino) "Off".
  iDestruct (main_offers_access Ino with "Off") as "[Off _]".
  iApply (main_offer_own_loc_prim with "Off").
Qed.

Lemma main_offer_disjoint EI N γx γg x T os V1 l q C V2 :
  @{V1} main_offers EI N γx γg x T os -∗ @{V2} l p↦{q} C -∗ ⌜l ∉ os.*1⌝.
Proof.
  iIntros "Hl Hl'" (([l' Vl] & Eql & Inos)%elem_of_list_fmap).
  simpl in Eql. subst l'. rewrite (main_offers_own_loc_prim Inos).
  iDestruct "Hl" as (C') "Hl".
  iAssert (@{V1 ⊔ V2} (l p↦{1 + q} C'))%I with "[-]" as "O".
  { iApply (view_at_mono' with "Hl'"); [solve_lat|].
    iApply (view_at_mono with "Hl"); [solve_lat|].
    apply own_loc_prim_combine. }
  rewrite own_loc_prim_frac_1. by iDestruct "O" as %Lt%Qp.not_add_le_l.
Qed.
End interp_props.

Section proof.
Context `{!noprolG Σ, !xchgG Σ, !atomicG Σ}.

#[local] Notation iProp := (iProp Σ).
#[local] Notation vProp := (vProp Σ).

Local Existing Instances xchg_graphG xchg_uniqTokG xchg_mapG.

Lemma ExchangerInv_ExchangerConsistent_instance :
  ∀ EI, ExchangerInv_ExchangerConsistent_piggyback (ExchangerLocal EI) ExchangerInv.
Proof.
  iIntros (EI N γg x q G G' M') "GE [? EL]".
  iDestruct "EL" as (γt γx) "(ES & MT & II)".
  iInv "II" as (G0) "(>[%F1 %F2] & >GE0 & II)" "HClose".
  iDestruct (ExchangerInv_agree with "GE GE0") as %->. iFrame "GE".
  iMod ("HClose" with "[GE0 II]") as "_"; [|done].
  iNext. iExists G. by iFrame "GE0 II".
Qed.

Lemma ExchangerInv_graph_master_acc_instance :
  ExchangerInv_graph_master_acc' ExchangerInv.
Proof.
  iIntros "* [I F]".
  iDestruct (ExchangerInv_graph_master' with "[$F $I]") as "G".
  iExists _. iFrame "G". rewrite -ExchangerInv_graph_master.
  iIntros "[_ $]".
Qed.

Lemma ExchangerInv_graph_snap_instance :
  ExchangerInv_graph_snap' ExchangerInv.
Proof.
  iIntros "* G [G' _]".
  by iDestruct (ghost_graph_master_snap_included with "G G'") as %?.
Qed.

Lemma ExchangerLocal_graph_snap_instance :
  ∀ EI N, ExchangerLocal_graph_snap' (ExchangerLocal EI N).
Proof. by iIntros "* [$ _]". Qed.

Lemma ExchangerLocalLite_graph_snap_instance :
  ExchangerLocal_graph_snap' ExchangerLocalLite.
Proof. by iIntros "* [$ _]". Qed.

Lemma ExchangerLocalLite_from_instance :
  ∀ EI N, ExchangerLocal_from' (ExchangerLocal EI N) ExchangerLocalLite.
Proof.
  iIntros "* [$ EL]". iDestruct "EL" as (γt γx) "(ES & MT & II)".
  iExists γt, γx. iFrame.
Qed.
Lemma ExchangerLocalLite_to_instance :
  ∀ EI N, ExchangerLocal_to' (ExchangerLocal EI N) ExchangerLocalLite.
Proof.
  iIntros "* [$ EL] [_ EL']". iDestruct "EL" as (γt γx) "[ES #MT]".
  iExists γt, γx. iFrame.
  iDestruct "EL'" as (γt' γx') "(_ & MT' & II)".
  iDestruct (meta_agree with "MT MT'") as %[<- <-]%pair_inj.
  by iFrame.
Qed.

Lemma ExchangerLocalLite_upgrade_instance :
  ExchangerLocal_upgrade' ExchangerLocalLite ExchangerInv.
Proof.
  iIntros "* GM [Gs $]".
  iDestruct (ghost_graph_master_snap_included with "GM [Gs]") as %?.
  { by iDestruct "Gs" as "[$ _]". }
  iApply (graph_snap_mono _ _ ∅ with "[GM] Gs"); [done|].
  (* TODO: lemma *)
  iDestruct (ghost_graph_master_snap with "GM") as "$".
  by iApply SeenLogview_empty.
Qed.

Lemma ExchangerLocal_upgrade_instance :
  ∀ EI N, ExchangerLocal_upgrade' (ExchangerLocal EI N) ExchangerInv.
Proof.
  iIntros "* EI #EL".
  iDestruct (ExchangerLocalLite_from_instance with "EL") as "-#ELL".
  iDestruct (ExchangerLocalLite_upgrade_instance with "EI ELL") as "ELL".
  iApply (ExchangerLocalLite_to_instance with "ELL EL").
Qed.

Lemma ExchangerLocal_union_instance :
  ∀ EI, ExchangerLocal_union' (ExchangerLocal EI) ExchangerInv.
Proof.
  iIntros "* [EI1 EI2] EL1 EL2".
  iDestruct (ExchangerLocal_upgrade_instance with "EI1 EL1") as "[Gs1 EL1']".
  iDestruct (ExchangerLocal_upgrade_instance with "EI2 EL2") as "[Gs2 _]".
  iDestruct (graph_snap_union with "Gs1 Gs2") as "$". iFrame "EL1'".
Qed.

Lemma new_exchanger_spec :
  new_exchanger_piggyback_spec' ExchangerLocal ExchangerInv new_exchanger.
Proof.
  iIntros (tid Φ) "_ Post".
  wp_lam.
  (* allocate x *)
  wp_apply wp_new; [done..|].
  iIntros (x) "([H†|%] & Hs & Hm & _)"; [|done].
  wp_let.
  (* initialize x as null, and create protocol *)
  rewrite own_loc_na_vec_singleton.
  iApply wp_fupd.
  wp_write.
  iMod (AtomicPtsTo_CON_from_na with "Hs") as (γx t0 V0) "(sV0 & #xN & xA)".

  iMod (LTM_master_alloc ∅) as (γt) "LTm".
  iMod (LTM_master_fork with "LTm") as "[LTm #LTs]".
  iMod graph_master_alloc_empty as (γg) "[[GM1 GM2] Gs]".
  iMod (meta_set _ _ (γt, γx) nroot with "Hm") as "#Hm"; [done|].

  have EC := ExchangerConsistent_empty.

  iApply ("Post" $! γg).
  iSplitL "GM2".
  - (* ExchangerInv *)
    by iDestruct (ExchangerInv_graph_master with "GM2") as "[% $]".
  - iIntros "!>" (E EI N).
    iMod (inv_alloc (xchgN N) _ (ExchangerInternalInv EI N γt γx γg x)
          with "[xA GM1 LTm]") as "#I".
    { iNext. iExists ∅.
      iDestruct (ExchangerInv_graph_master with "GM1") as "[% $]". iSplit; [done|].
      iExists [(None,V0)], [], ∅. iFrame "LTm".
      iDestruct (view_at_intro with "xA") as (Vb) "[InVb xA]".
      iExists Vb. iSplitL; last iSplitL.
      - iExists _. iFrame "xA".
      - by rewrite /main_offers /=.
      - by iPureIntro. }
    (* ExchangerLocal *)
    iDestruct (graph_snap_empty with "Gs") as "$".
    iExists γt, γx. rewrite shift_0. iFrame "Hm I". iExists _. by iFrame "xN".
Qed.

Lemma exchange_spec :
  exchange_piggyback_spec' ExchangerLocal ExchangerInv exchange.
Proof.
  intros EI OBJ N DISJ x tid γg G1 M V v1 Posv1.
  iIntros "#sV #(Gs & ES) #EXI" (Φ TA' TB' α' β' Φ') "Pr AU".
  iDestruct (bi.persistent_sep_dup with "Pr") as "[#Pr AU']".
  iDestruct "ES" as (γt γx) "(ES & MT & EII)".
  iDestruct "ES" as (ζx0) "xN".
  set E1 := G1.(Es).

  (* allocate an offer *)
  wp_lam. wp_apply (wp_new with "[//]"); [done..|].
  iIntros (m) "([H†|%] & Hm & _)"; [|done].
  iDestruct (own_loc_na_vec_cons with "Hm") as "[mL mD]".
  rewrite own_loc_na_vec_singleton.

  (* write hole as Null *)
  wp_let. wp_op. rewrite shift_0. wp_write.
  (* write data with v1 *)
  wp_op. wp_write.

  (* prepare to CAS to make an offer *)
  wp_bind (casʳᵉˡ(_, _, _))%E.

  (* open invariant *)
  iInv "EII" as (G2) "(>%CON2 & GM & EBI)" "Close".
  iDestruct "EBI" as (LVs2 os2 T2) "(LTm & Locs)".
  iDestruct "Locs" as (Vb) "([%tx0 >xA] & Offs & >[%Eqos2 %EqD2])".

  (* Prepare resources that we may release at the right view *)
  iCombine "mL mD" as "mLD". iCombine "AU' AU mLD sV Gs xN" as "Hm".
  iDestruct (view_at_intro_incl with "Hm sV") as (V1) "(#sV1 & %LeVV1 & AU' & AU & Hm & GE)".

  (* prepare for rlx CASes later *)
  iMod (rel_objectively_intro (⊒∅) tid with "[]") as "#HRE".
  { iApply objective_objectively. iApply monPred_in_bot. }

  (* finally, CAS to make the offer *)
  wp_apply (AtomicSeen_CON_CAS_int x γx ζx0 _ _ _ _ 0 #m tid ∅ V1 Vb
              with "[$xN $xA $sV1]"); [done..|solve_ndisj| |done|].
  { intros ???. by apply toXChgHist_comparable_0. }

  iIntros (b tx1 vx1 Vr2 V2 ζx2' ζx2) "(F & #sV2 & xN2' & xA & CASE)".
  iDestruct "F" as %([Subζx0 Subζx2'] & Eqtx1 & _ & LeV1).
  iDestruct (view_at_elim with "sV2 xN2'") as "#xN2 {xN2'}".

  iDestruct "CASE" as "[[F _]|[F HVw]]".
  - (* CAS fails, there may be an offer *)
    iDestruct "F" as %(-> & _ & ->).
    (* close the invariant *)
    iMod ("Close" with "[GM LTm xA Offs]") as "_".
    { iNext. iExists _. iFrame "GM". iSplit; [done|].
      iExists _, _, _. iFrame "LTm". iExists (Vb ⊔ V2).
      iSplitL "xA". { iExists _; by iFrame "xA". }
      iFrame "Offs". by iPureIntro. } clear Vb tx0 Subζx0 Subζx2' Eqtx1.

    iIntros "!>". wp_if.
    (* Prepare to read if the offer is there *)
    wp_bind (!ᵃᶜ _)%E.

    (* open invariant *)
    iInv "EXI" as "XI" "CloseX".
    iInv "EII" as (G3) "(>[%CON3 %EGCs] & GM & EBI)" "Close".
    iDestruct "EBI" as (LVs3 os3 T3) "(LTm & Locs)".
    iDestruct "Locs" as (Vb) "([%tx0 >xA] & Offs)".

    (* read acquire the offer *)
    wp_apply (AtomicSeen_acquire_read with "[$xN2 $xA $sV2]"); first solve_ndisj.
    iIntros (tx3 vx3 V3' V3 ζx3') "(F & #sV3 & #xN3 & xA)".
    iDestruct "F" as %([Subζx23' Subζx3'] & Eqtx3 & _ & LeV2).
    apply (lookup_weaken Eqtx3), toXChgHist_lookup_Some' in Subζx3'
      as (on & -> & InLVs3).

    iDestruct (monPred_in_mono _ V3' with "sV3") as "#sV3'".
    { simpl; clear -LeV2; solve_lat. }

    (* make a snapshot *)
    iMod (LTM_master_fork with "LTm") as "[LTm #LT3]".

    destruct on as [l2|]; last first.
    { (* read Null, the offer is already taken by someone else, fail completely *)
      (* CANCEL_CASE 2 : COMMIT with CANCELLED event *)
      iDestruct (view_at_elim with "sV1 AU") as "AU".
      iMod ("Pr" $! true true with "AU XI") as (G3') "[>GM' HClose]".

      iDestruct (ExchangerInv_agree with "GM GM'") as %->.
      iDestruct (ExchangerInv_graph_master' with "[$GM //]") as "GM".
      iDestruct (ExchangerInv_graph_master' with "[$GM' //]") as "GM'".
      iDestruct (graph_master_snap_included with "GM Gs") as %SubG1.
      set E3 := G3.(Es).
      have SubE1 : E1 ⊑ E3 by apply SubG1.

      set V' := V3.
      have LeVV' : V ⊑ V'. { clear -LeV1 LeVV1 LeV2. rewrite /V'. by solve_lat. }
      have bLeVV' : bool_decide (V ⊑ V') by eapply bool_decide_unpack; eauto.
      set Vex1 := mkDView V V' V' bLeVV'.
      set ExE := Exchange v1 CANCELLED.

      iDestruct (bi.persistent_sep_dup with "Gs") as "[_ [_ PSV]]".
      iDestruct (SeenLogview_closed with "PSV") as "%SubD1 {PSV}".
      have SubM: set_in_bound M E3.
      { clear - SubD1 SubE1. by eapply set_in_bound_mono. }

      assert (GIP:= graph_insert_props_base _ ExE _ Vex1 SubM EGCs).
      destruct GIP as [xchgId M' egV' G' LeG' SubM' SUB' InId FRGe1 EGCs'].
      have CON' : ExchangerConsistent G' by apply exchange_cancel_graph_insert.
      set E' := G'.(Es).
      have LeE' : E3 ⊑ E' by apply LeG'.

      iCombine "GM GM'" as "GM".
      iMod (graph_master_update _ _ _ LeG' EGCs' with "GM") as "[[GM GM'] Gs']".

      have LeV1' : V1 ⊑ V'. { clear -LeV1 LeV2. rewrite /V'. solve_lat. }
      iAssert (@{V'} SeenLogview E' M')%I with "[GE]" as "#SL".
      { iDestruct "GE" as "(_ & [_ SL] & _)".
        rewrite -SeenLogview_insert'. iSplitL; [|done].
        erewrite SeenLogview_map_mono; [iFrame "SL"|done..]. }

      iAssert (@{V'} graph_snap γg G' M')%I as "#Gss'". { iFrame "Gs' SL". }
      rewrite bi.and_elim_r.
      iMod ("HClose" $! V' G' xchgId xchgId CANCELLED Vex1 Vex1 M'
                      with "[GM' Gs' $sV3]") as "[HΦ XI]".
      { (* Public Post *)
        iDestruct (ExchangerInv_graph_master with "GM'") as "[_ $]".
        iSplitR; [by iPureIntro|]. iLeft. iSplitR; [by iPureIntro|].
        (* ExchangerLocal *)
        iFrame "Gss'". iExists _, _. iFrame "MT EII". iExists _; by iFrame "xN3". }

      (* close invariant *)
      iMod ("Close" with "[GM LTm Offs xA]") as "_".
      { iNext. iExists G'. iSplit; [done|].
        iDestruct (ExchangerInv_graph_master with "GM") as "[_ $]".
        iExists _, _, _. iFrame "LTm". iExists (Vb ⊔ V3).
        iSplitL "xA". - iExists _; iFrame "xA". - by iFrame "Offs". } clear Vb tx0.
      iIntros "!>". iMod ("CloseX" with "XI") as "_".

      (* finish this CANCELLED case *)
      iIntros "!>". wp_let. wp_op. wp_if.
      iDestruct (view_at_elim with "sV1 Hm") as "Hm".
      (* cleaning up *)
      wp_apply (wp_delete _ tid 2 _ [ #0; #v1] with "[H† Hm]"); [done|done|..].
      { rewrite own_loc_na_vec_cons own_loc_na_vec_singleton. iFrame "Hm".
        iLeft. by iFrame. }
      iIntros "_". wp_seq. iApply "HΦ". clear; by iIntros ([]).
      (* End CANCEL_CASE 2 *)
    }

    simpl in Eqtx3.
    (* do not commit yet, close invariant *)
    (* but before that ... extract the observation of the offer that is l2 *)
    iDestruct "Offs" as "(Offs & %Eqos3 & %EqD3)".
    apply (filter_is_Some_fst_in Eqos3) in InLVs3.
    rewrite (main_offers_access InLVs3).
    iDestruct "Offs" as "[Off Offs]".
    iDestruct "Off" as (γl2 γk2 EqTl2) "(#l2N0 & l2A & l2I)".
    iDestruct "l2I" as (t0 V0 LeV0) "#HIl2".

    (* now we can close invariant *)
    iMod ("Close" with "[GM LTm Offs xA l2A]") as "_".
    { iNext. iExists _. iFrame "GM". iSplit; [done|].
      iExists _, _, _. iFrame "LTm". iExists (Vb ⊔ V3).
      iSplitL "xA". { iExists _; iFrame "xA". } iSplitL; [|by iPureIntro].
      iApply (view_at_mono_2 with "Offs"); [solve_lat|].
      iExists _, _. iSplit; [by iPureIntro|]. iSplitR; [by iFrame "l2N0"|].
      iFrame "l2A". iExists _, _. iSplit; [by iPureIntro|]. iFrame "HIl2". }
    iIntros "!>". iMod ("CloseX" with "XI") as "_".

    iDestruct "l2N0" as (ζl2') "l2N0". rewrite view_at_view_at.
    iDestruct (view_at_elim with "sV3' l2N0") as "l2N {l2N0}".
    iDestruct "HIl2" as (v2 P Q) "[l2I (%M2 & %Vin2 & %LeVin2 & AU2)]".
    rewrite view_at_view_at view_at_objective_iff. clear Vb tx0.

    simpl. iIntros "!>". wp_let. wp_op. wp_if. wp_op. rewrite shift_0.

    (* Prepare to CAS to match the offer by l2 *)
    wp_bind (casʳᵉˡ(_, _, _))%E.

    (* open invariant *)
    iInv "EXI" as "XI" "CloseX". clear EGCs.
    iInv "EII" as (G4) "(>[%CON4 %EGCs] & GM & EBI)" "Close".
    rewrite ExchangerBaseInv_unfold_snap.
    iDestruct ("EBI" with "[$LT3]") as (LVs4 os4 T4) "[(LTm & Locs) >%LeT3]".
    iDestruct "Locs" as (Vb) "([%tx0 >xA] & Offs & >[%Eqos4 %EqD4])".

    (* TODO: accessor. get the AtomicPtsTo of l2 *)
    iDestruct (AtomicPtsTo_AtomicSeen_latest with "xA xN3") as %Inos4.
    apply (lookup_weaken Eqtx3), toXChgHist_lookup_Some_loc,
          (filter_is_Some_fst_in Eqos4) in Inos4.
    rewrite (main_offers_access Inos4).
    iDestruct "Offs" as "[l2O Offs]".
    iDestruct "l2O" as (γl2' γk2') "(>%EqTl2' & l2N' & l2A & l2I')".
    assert (γl2' = γl2 ∧ γk2' = γk2) as [-> ->].
    { apply (lookup_weaken_inv _ _ _ _ _ EqTl2 LeT3) in EqTl2'.
      clear -EqTl2'. by inversion EqTl2'. }
    iDestruct "l2A" as (ζl2) ">l2A".

    (* open the l2 offer invariant *)
    iInv "l2I" as (s ζl0 V1') "(>[%OHl2 %Posv2] & [%Vlo >l2C] & OR)" "Close2".
    iDestruct (AtomicPtsTo_SWriter_agree with "l2A l2C") as %<-.
    (* actual CAS to match the offer *)
    wp_apply (AtomicSWriter_CAS_int l2 γl2 _ _ _ _ _ _ 0 #m tid ∅ V3 Vb
                with "[$l2N $l2A $l2C $sV3]"); [done..|solve_ndisj| |done|].
    { intros ???. eapply offer_hist_comparable_0; eauto. }

    iIntros (b tl2' vl2' Vr4 V4 ζl2x ζl2x') "(F & #sV4 & l2N2 & [l2A l2C] & CASE)".
    iDestruct "F" as %([Subζl2'' Subζl2x] & Eqtl2' & _ (* MAXtl2' *) & LeV3).

    (* If fail to match the offer, commit CANCELLED.
       If succeed, we should get an AU from the offerer. Between this AU and our
       own AU, we have a choice to execute which one first. *)
    (* prepare some facts *)
    iDestruct (ExchangerInv_graph_master' with "[$GM //]") as "GM".
    iDestruct (graph_master_snap_included with "GM Gs") as %SubG1.
    set E4 := G4.(Es).
    have SubE1 : E1 ⊑ E4 by apply SubG1.
    iDestruct (bi.persistent_sep_dup with "Gs") as "(_ & _ & PSV)".
    iDestruct (SeenLogview_closed with "PSV") as "%SubD1 {PSV}".
    have SubM: set_in_bound M E4.
    { clear - SubD1 SubE1. by eapply set_in_bound_mono. }

    set V' := V4.
    have LeV1' : V1 ⊑ V'. { clear -LeV1 LeV3 LeV2. rewrite /V'. solve_lat. }
    have LeVV' : V ⊑ V'. { clear -LeVV1 LeV1'. rewrite /V'. by solve_lat. }
    have bLeVV' : bool_decide (V ⊑ V') by eapply bool_decide_unpack; eauto.
    set Vex1 := mkDView V V' V' bLeVV'.

    iDestruct "CASE" as "[[Eq sVr4]|[Eq HVw]]".
    { (* CAS failed, cannot match offer. *)
      iDestruct "Eq" as %(-> & _ & ->).
      (* CANCEL_CASE 3 : COMMIT with CANCELLED *)
      set ExE := Exchange v1 CANCELLED.
      assert (GIP:= graph_insert_props_base _ ExE _ Vex1 SubM EGCs).
      destruct GIP as [xchgId M' egV' G' LeG' SubM' SUB' InId FRGe1 EGCs'].
      set E' := G'.(Es).
      have LeE' : E4 ⊑ E' by apply LeG'.

      have CON' : ExchangerConsistent G'.
      { by apply exchange_cancel_graph_insert. }

      iDestruct (view_at_elim with "sV1 AU") as "AU".
      iMod ("Pr" $! true true with "AU XI") as (G4') "[>GM' HClose]".

      iDestruct (ExchangerInv_graph_master_agree with "GM GM'")
        as "(%Eq & GM & GM')". subst G4'.
      iCombine "GM GM'" as "GM".
      iMod (graph_master_update _ _ _ LeG' EGCs' with "GM") as "[[GM GM'] Gs']".

      (* TODO: duplicates with other CANCELLED case *)
      iAssert (@{V'} SeenLogview E' M')%I with "[GE]" as "#SL".
      { iDestruct "GE" as "(_ & [_ SL] & _)".
        rewrite -SeenLogview_insert'. iSplitL; [|done].
        erewrite SeenLogview_map_mono; [iFrame "SL"|done..]. }

      iAssert (@{V'} graph_snap γg G' M')%I as "#Gss'". { iFrame "Gs' SL". }
      (* COMMIT the AU *)
      rewrite bi.and_elim_r.
      iMod ("HClose" $! V' G' xchgId xchgId CANCELLED Vex1 Vex1 M'
                      with "[GM' Gs' $sV4]") as "[HΦ XI]".
      { (* Public Post *)
        iDestruct (ExchangerInv_graph_master with "GM'") as "[_ $]".
        iSplitR; [by iPureIntro|]. iLeft. iSplitR; [by iPureIntro|].
        (* ExchangerLocal *)
        iFrame "Gss'". iExists _, _. iFrame "MT EII". iExists _; by iFrame "xN3". }

      (* close the offer invariant *)
      iMod ("Close2" with "[l2C OR]") as "_".
      { iNext. iExists s, ζl2, _. iSplit; [by iPureIntro|].
        iFrame "OR". iExists _; by iFrame "l2C". }
      iIntros "!>".
      (* close invariant *)
      iMod ("Close" with "[GM LTm Offs xA l2A l2N' l2I']") as "_".
      { iNext. iExists _.
        iDestruct (ExchangerInv_graph_master with "GM") as "[_ $]". iSplit; [done|].
        iExists LVs4, _, _. iFrame "LTm". iExists (Vb ⊔ V').
        iSplitL "xA". { iExists _; by iFrame "xA". } iSplitL; [|by iPureIntro].
        iApply (view_at_mono_2 with "Offs"); [solve_lat|].
        iExists γl2, γk2. iSplitR; [by iPureIntro|]. iFrame "l2N'".
        iSplitL "l2A". { iExists _; by iFrame "l2A". }
        by iFrame "l2I'". } clear Vb tx0.

      iIntros "!>". iMod ("CloseX" with "XI") as "_".
      (* finish this CANCELLED case *)
      iIntros "!>". wp_let.
      (* CAS to reset *)
      wp_bind (casʳˡˣ(_,_,_))%E.
      (* open the invariant *)
      iInv "EII" as (G5) "(EC & GM & EBI)" "Close".
      iDestruct "EBI" as (LVs5 os5 T5) "(LTm & Locs)".
      iDestruct "Locs" as (Vb) "([%tx0 >xA] & Offs & >[%Eqos5 %EqD5])".

      (* TODO: lemma *)
      iDestruct (view_at_elim with "sV3 xN3") as "xN3'".
      iDestruct (AtomicPtsTo_AtomicSeen_latest_1 with "xA xN3'") as %Inos5.
      apply (lookup_weaken Eqtx3), toXChgHist_lookup_Some_loc,
            (filter_is_Some_fst_in Eqos5) in Inos5.
      (* TODO: slow *)
      wp_apply (AtomicSeen_CON_CAS_live_loc x γx _ _ _ _ _ l2 #0
                  _ ∅ V4 Vb
                with "[$xN3' $xA $sV4]"); [done..|solve_ndisj| |done|].
      { intros ???. by apply toXChgHist_comparable_loc. }

      iIntros (b t' v' Vr5 V5 ζx5' ζx) "(F & sV5 & xN5 & xA & CASE)".

      (* close the invariant *)
      iMod ("Close" with "[EC GM LTm Offs xA F CASE]") as "_".
      { iNext. iExists _. iFrame "EC GM".
        iDestruct "CASE" as "[[Eq sVr5]|[Eq HVw]]".
        - iDestruct "Eq" as %(-> & ? & ->).
          iExists LVs5, os5, T5. iFrame "LTm". iExists (Vb ⊔ V5).
          iSplitL "xA". { iExists _. iFrame "xA". }
          iSplitL "Offs"; [by iFrame "Offs"|by iPureIntro].
        - iDestruct "Eq" as %[-> ->].
          iDestruct "HVw" as (Vw (Frt' & Eqt' & Eqt'' & LeVr5w & _)) "_".
          iDestruct "F" as %([_ Subζx5'] & Eqt5' & _).
          assert (Eqζx : ζx = toXChgHist tx0 (LVs5 ++ [(None,Vw)])).
          { move : Subζx5' => /(lookup_weaken Eqt5').
            rewrite Eqt' lookup_insert_ne; [|clear;lia]. clear -Frt'.
            intros Eqt. revert Eqt Frt'.
            by apply (toXChgHist_insert_next_fresh None). }
          iExists (LVs5 ++ [(None,Vw)]), os5, T5. iFrame "LTm".
          iExists (Vb ⊔ V5). iSplitL "xA"; last iSplitL "Offs".
          + rewrite Eqζx. iExists _; iFrame "xA".
          + by iFrame "Offs".
          + iPureIntro. by rewrite filter_is_Some_app_None. } clear Vb.

      iIntros "!>". wp_seq. wp_if.
      (* cleaning up *)
      iDestruct (view_at_elim with "sV1 Hm") as "Hm".
      wp_apply (wp_delete _ tid 2 _ [ #0; #v1] with "[H† Hm]"); [done|done|..].
      { rewrite own_loc_na_vec_cons own_loc_na_vec_singleton. iFrame "Hm".
        iLeft. by iFrame. }
      iIntros "_". wp_seq. iApply "HΦ". clear; by iIntros ([]).
      (* End CANCEL_CASE 3 *) }

    (* CAS succeeded, offer matched *)
    iDestruct "Eq" as %[-> ->].
    iDestruct "HVw" as (Vw (FRtl2 & Eqtl21 & Eqtl22 & LeV0w & ? &
                            NEqVr4 & NEqV3 & LeVw)) "[l2Nx _]".

    (* TODO separate lemma *)
    apply (lookup_weaken Eqtl2') in Subζl2x.
    rewrite Eqtl21 lookup_insert_ne in Subζl2x; [|clear;lia].
    eapply offer_hist_lookup_0 in Subζl2x; [|exact OHl2].
    destruct Subζl2x as [-> ->].
    assert (s = OfferMatching) as ->.
    { clear -FRtl2 OHl2.
      destruct s; simpl in OHl2; subst ζl2; [done|exfalso..];
        by rewrite lookup_insert in FRtl2. }

    (* We should get an AU from the offerer here *)
    iDestruct "OR" as "[l2D HP]". iDestruct "AU2" as (G02) "[Gs2 AU2]".
    iDestruct "AU2" as (TA2' TB2' α2' β2' Φ2') "[AU2 AU2']".
    iSpecialize ("AU2" with "HP").

    iDestruct "Hm" as "[mO mD]".
    iDestruct (graph_master_snap_included_2 with "GM Gs2") as %SubG02.
    set E02 := G02.(Es).
    have SubE02 : E02 ⊑ E4 by apply SubG02.
    iAssert (⌜ set_in_bound M2 E02 ⌝)%I with "[]" as %SubM2.
    { iDestruct "Gs2" as "[_ PV]". clear. rewrite SeenLogview_closed.
      by iDestruct "PV" as %?. }
    have SubM24: set_in_bound M2 E4 by eapply set_in_bound_mono.

    have LeV0V' : V0 ⊑ V'. { clear -LeV0 LeV3 LeV2. rewrite /V'. solve_lat. }
    have LeVV2 : Vin2 ⊑ V'. { clear -LeVin2 LeV0V'. rewrite /V'. by solve_lat. }
    have LtVV' : V ⊏ V'.
    { apply strict_spec_alt. split; [done|]. clear -LeVV1 LeV1 LeV2 LeV3 NEqV3.
      have LeVV3: V ⊑ V3 by solve_lat. clear LeVV1 LeV1 LeV2.
      subst V'. intros ->. apply NEqV3. by apply : anti_symm. }
    have LtVV2 : Vin2 ⊏ V'.
    { apply strict_spec_alt. split; [done|].
      clear -LeVin2 NEqVr4. intros ->. by apply NEqVr4. }

    have bLeVV2 : bool_decide (Vin2 ⊑ V') by eapply bool_decide_unpack; eauto.
    set Vex2 := mkDView Vin2 V' V' bLeVV2.
    set ExE1 := Exchange v1 v2.
    set ExE2 := Exchange v2 v1.
    set bv : bool := bool_decide (v2 < v1).

    (* final graph, with two new events *)
    assert (GIP:= graph_insert2_props_choice bv _ ExE1 ExE2 M M2 Vex1 Vex2
                  SubM SubM24 EGCs ltac:(done) ltac:(done)).
    destruct GIP as [xchgmin xchgmax M'' Evmin Evmax G'' LeG'' [SubM2' SubM1']
                      SUB' [InMx1 InMx2] [NEqx12 LtX12] [FRx1 FRx2] EGCs''].
    set xchg1 := if bv then xchgmin else xchgmax.
    set xchg2 := if bv then xchgmax else xchgmin.
    set E'' := G''.(Es).
    have LeE'' : E4 ⊑ E'' by apply LeG''.

    have CON' : ExchangerConsistent G''.
    { apply (exchange_commit_graph_insert bv G4 v1 v2 M M2 Vex1 Vex2
                      ltac:(done) ltac:(done) LtVV' LtVV2 Posv1 Posv2 CON4). }

    have ORD1: (v1 > v2 ↔ (xchg1 < xchg2)%nat).
    { clear -LtX12. destruct bv eqn:Eqbv.
      - apply bool_decide_eq_true_1 in Eqbv. split; [done|lia].
      - apply bool_decide_eq_false_1 in Eqbv. split; lia. }
    have ORD2: v2 ≠ v1 → (v2 > v1 ↔ (xchg2 < xchg1)%nat).
    { clear -LtX12 NEqx12. intros ?. destruct bv eqn:Eqbv.
      - apply bool_decide_eq_true_1 in Eqbv. split; lia.
      - apply bool_decide_eq_false_1 in Eqbv. split; lia. }

    (* Intermediate inconsistent graph (G'), only registering the smaller event. *)
    set G' := graph_insert_event Evmin G4. set E' := G'.(Es).
    (* Some properties of the intermediate inconsistent graph. TODO: lemma *)
    destruct (graph_insert_event_eq Evmin G4) as (LeG' & EqG' & Eqso' & Eqco').
    rewrite -/G'' in LeG'.
    have LeE' : E4 ⊑ E' by apply LeG'.
    have EqE'' : E'' = E' ++ [Evmax].
    { by rewrite /E'' /E' /= (app_assoc _ [_] [_]). }
    have EqE' : E' = E4 ++ [Evmin]. { done. }
    have Eqxmx : xchgmax = length E'. { rewrite /= app_length /=. clear; lia. }
    have FRGmx4 : (length E4 ≤ xchgmax)%nat. { clear -LtX12. subst E4. simpl. lia. }
    have LeL14 : (length E1 <= length E4)%nat by apply prefix_length, SubG1.
    have LeL024 : (length E02 <= length E4)%nat by apply prefix_length, SubG02.
    have FRGmx1 : (length E1 ≤ xchgmax)%nat. { etrans; [apply LeL14|apply FRGmx4]. }
    have FRGmx02 : (length E02 ≤ xchgmax)%nat. { etrans; [apply LeL024|apply FRGmx4]. }
    have FRGmi02 : (length E02 ≤ xchgmin)%nat. { etrans; [apply LeL024|done]. }
    assert (length E1 ≤ xchg1 ∧ length E1 ≤ xchg2)%nat as [FRG11 FRG12].
    { clear -FRGmx1 LeL14. by destruct bv. }
    assert (length E02 ≤ xchg1 ∧ length E02 ≤ xchg2)%nat as [FRG021 FRG022].
    { clear -FRGmx02 FRGmi02. by destruct bv. }

    have NInSo1 : xchgmin ∉ (elements (so G4)).*1.
    { intros ([e1 e2] & Eq1 & [Lt1 ]%elem_of_elements%gcons_so_included)%elem_of_list_fmap.
      simpl in Eq1. subst e1. clear -Lt1. simpl in Lt1. lia. }
    have NInSo2 : xchgmax ∉ (elements (so G4)).*1.
    { intros ([e1 e2] & Eq1 & [Lt1]%elem_of_elements%gcons_so_included)%elem_of_list_fmap.
      simpl in Eq1. subst e1. clear -Lt1. simpl in Lt1. lia. }
    assert (xchg1 ∉ M ∧ xchg1 ∉ M2) as [NInM1 NInM21].
    { clear -FRx1 FRx2. destruct bv; set_solver. }
    assert (xchg2 ∉ M ∧ xchg2 ∉ M2) as [NInM2 NInM22].
    { clear -FRx1 FRx2. destruct bv; set_solver. }

    have EqGs'' : G''.(Es) = G'.(Es) ++ [Evmax]. { clear; by simplify_list_eq. }
    have Eqso'' : so G'' = {[(xchgmin, xchgmax); (xchgmax, xchgmin)]} ∪ so G'. { done. }
    have Eqco'' : com G'' = {[(xchgmin, xchgmax); (xchgmax, xchgmin)]} ∪ com G'. { done. }
    have LeG'2 : G' ⊑ G''.
    { constructor; simpl; [|set_solver-..]. rewrite (app_assoc _ [_] [_]). by eexists. }
    have LeE'2 : E' ⊑ E'' by apply LeG'2.

    set M' := {[xchgmin]} ∪ (if bv then M else M2) ∪ (if bv then M2 else M).
    have EqM' : M' = M'' ∖ {[xchgmax]}.
    { revert NEqx12 FRx2. clear. destruct bv; set_solver. }
    have EqM'': M'' = {[xchgmax]} ∪ M'.
    { rewrite EqM'. by apply union_difference_singleton_L. }

    iAssert (@{V'} SeenLogview E' M')%I with "[GE]" as "#SL'".
    { iDestruct "GE" as "(_ & [_ SL] & _)". iDestruct "Gs2" as "[_ SL2]".
      iAssert (@{V'} SeenLogview E' M)%I with "[SL]" as "SL'".
      { iApply (view_at_mono with "SL"); [done|].
        apply SeenLogview_map_mono; [by etrans|done]. }
      iAssert (@{V'} SeenLogview E' M2)%I with "[]" as "SL2'".
      { iApply (view_at_mono with "SL2"); [done|].
        apply SeenLogview_map_mono; [by etrans|done]. }
      rewrite -2!SeenLogview_union'. iSplit; [iSplit|].
      - iIntros "{# %}". rewrite -SeenLogview_singleton_insert.
        iPureIntro; simpl; by destruct bv.
      - destruct bv; [iFrame "SL'"| iFrame "SL2'"].
      - destruct bv; [iFrame "SL2'"| iFrame "SL'"]. }

    iAssert (@{V'} SeenLogview E'' M'')%I with "[GE]" as "#SL''".
    { rewrite EqM'' -SeenLogview_union'. iSplit.
      - iClear "#"; clear -EqE'' Eqxmx.
        rewrite -SeenLogview_singleton; last first.
        + by rewrite EqE'' Eqxmx lookup_app_1_eq.
        + iPureIntro; clear; simpl; by destruct bv.
      - iApply (view_at_mono with "SL'"); [done|]. by apply SeenLogview_map_mono. }

    (* COMMITING both AUs in some order decided by the boolean bv. *)
    iAssert (|={_}=>
              @{V'} (▷ EI true ∗ graph_master γg (1/2) G'' ∗ Q v1 ∗ Φ #v2))%I
      with "[GM XI AU AU' AU2 AU2']" as ">(XI & GM & HQ & HΦ)".
    { (* TODO: annoying clean up of the context. *)
      rewrite -view_at_fupd.
      iCombine "AU2 AU2'" as "AU2". iCombine "AU AU'" as "AU".
      iApply (view_at_mono' with "AU2"); [done|].
      iApply (view_at_mono' with "AU"); [done|].
      rewrite -(view_at_view_at (SeenLogview E' M') V' V').
      rewrite -(view_at_view_at (SeenLogview E'' M'') V' V').
      rewrite -(view_at_view_at (x sn⊒{γx} ζx3') V3 V').
      iCombine "EII MT XI GM" as "EMXG".
      iDestruct (view_at_objective_iff _ V' with "EMXG") as "EMXG".
      iAssert (@{V'} ⊒V')%I as "sV'". { by iPureIntro. }
      iCombine "SL' SL'' xN3 sV' EMXG" as "SL".
      iApply (view_at_mono with "SL"); [done|].
      iIntros "(#SL' & #SL'' & #xN & #sV' & #EII & #MT & XI & GM)
               [AU AU'] [AU2 #AU2']".
      (* decide which AU to commit first *)
      destruct bv eqn:Eqbv.
      - (* v2 < v1, commit v1's AU first *)
        have NLtX12: ¬ (xchg2 < xchg1)%nat. { clear -LtX12; lia. }
        iMod ("AU'" $! false true with "AU XI") as (G4') "[>GM' HClose]".
        iDestruct (ExchangerInv_graph_master with "GM") as "[_ GM]".
        iDestruct (ghost_graph_master_agree with "GM' GM") as %->.
        iCombine "GM' GM" as "GM".
        iMod (ghost_graph_update γg _ G' LeG' with "GM") as "[GM GM']".
        iDestruct (ghost_graph_master_snap with "GM") as "#Gs'".

        iAssert (@{V'} ExchangerSeen γx x)%I as "#ES".
        { iExists _; iFrame "xN". }
        iAssert (@{V'} graph_snap γg G' M')%I with "[Gs']" as "#Obs'".
        { iFrame "Gs' SL'". }
        iAssert (@{V'} ExchangerLocal EI N γg x G' M')%I with "[]" as "#EL'".
        { iFrame "Obs'". iExists γt, γx. by iFrame "ES MT EII". }

        rewrite bi.and_elim_r.
        iMod ("HClose" $! V' G' xchg1 xchg2 v2 Vex1 Vex2 M''
                        with "[GM' $sV']") as "[HΦ XI]".
        { iFrame "GM'". iSplitR; [by iPureIntro|]. iRight.
          iSplit; [by iPureIntro|]. iRight. rewrite -EqM'. by iFrame "EL'". }
        (* then v2's AU *)
        iMod ("AU2'" $! false false with "AU2 XI") as (G4') "[>GM' HClose]".
        iDestruct (ghost_graph_master_agree with "GM' GM") as %->.
        iCombine "GM' GM" as "GM".
        iMod (ghost_graph_update γg _ G'' LeG'2 with "GM") as "[GM GM']".
        iDestruct (ghost_graph_master_snap with "GM") as "#Gs''".

        iAssert (@{V'} graph_snap γg G'' M'')%I with "[]" as "#Obs''".
        { iFrame "Gs'' SL''". }
        iAssert (@{V'} ExchangerLocal EI N γg x G'' M'')%I with "[]" as "#EL''".
        { iFrame "Obs''". iExists γt, γx. by iFrame "ES MT EII". }

        rewrite bi.and_elim_r.
        iMod ("HClose" $! V' G'' xchg2 xchg1 v1 Vex2 Vex1 M''
                        with "[GM']") as "[HQ XI]".
        { iFrame "GM' sV'". iSplitR; [by iPureIntro|]. iRight.
          iSplit; [by iPureIntro|]. iLeft. iFrame "Obs'' ES".
          iPureIntro. do 2 (split; [done|]).
          split; last split; last split; last split; [..|done|done].
          - by rewrite lookup_app_1_eq. - set_solver+Eqso''. - set_solver+Eqco''. }

        iSpecialize ("HQ" with "[]").
        { clear -NLtX12. by iIntros ([_ ?]). }
        iSpecialize ("HΦ" with "[]").
        { iIntros "_". iExists G''. iFrame "EL''". by iPureIntro. }
        iIntros "!>". iFrame "XI HQ HΦ". rewrite -ExchangerInv_graph_master.
        by iFrame (EGCs'') "GM EM".
      - (* v1 < v2, commit v2's AU first *)
        have NLtX12: ¬ (xchg1 < xchg2)%nat. { clear -LtX12; lia. }
        (* TODO: dup with the previous case *)
        iMod ("AU2'" $! false true with "AU2 XI") as (G4') "[>GM' HClose]".
        iDestruct (ExchangerInv_graph_master with "GM") as "[_ GM]".
        iDestruct (ghost_graph_master_agree with "GM' GM") as %->.
        iCombine "GM' GM" as "GM".
        iMod (ghost_graph_update γg _ G' LeG' with "GM") as "[GM GM']".
        iDestruct (ghost_graph_master_snap with "GM") as "#Gs'".

        iAssert (@{V'} ExchangerSeen γx x)%I as "#ES".
        { iExists _; iFrame "xN". }
        iAssert (@{V'} graph_snap γg G' M')%I with "[]" as "#Obs'".
        { iFrame "Gs' SL'". }

        rewrite bi.and_elim_r.
        iMod ("HClose" $! V' G' xchg2 xchg1 v1 Vex2 Vex1 M''
                        with "[GM' $sV']") as "[HQ XI]".
        { iFrame "GM'". iSplitR; [by iPureIntro|]. iRight.
          iSplit; [by iPureIntro|]. iRight. rewrite -EqM'. by iFrame "Obs' ES". }
        (* then v1's AU *)
        iMod ("AU'" $! false false with "AU XI") as (G4') "[>GM' HClose]".
        iDestruct (ghost_graph_master_agree with "GM' GM") as %->.
        iCombine "GM' GM" as "GM".
        iMod (ghost_graph_update γg _ G'' LeG'2 with "GM") as "[GM GM']".
        iDestruct (ghost_graph_master_snap with "GM") as "#Gs''".

        iAssert (@{V'} graph_snap γg G'' M'')%I with "[]" as "#Obs''".
        { iFrame "Gs'' SL''". }
        iAssert (@{V'} ExchangerLocal EI N γg x G'' M'')%I with "[]" as "#EL''".
        { iFrame "Obs''". iExists γt, γx. by iFrame "ES MT EII". }

        rewrite bi.and_elim_r.
        iMod ("HClose" $! V' G'' xchg1 xchg2 v2 Vex1 Vex2 M''
                        with "[GM']") as "[HΦ XI]".
        { iFrame "GM' sV'". iSplitR; [by iPureIntro|]. iRight.
          iSplit; [by iPureIntro|]. iLeft. iFrame "EL''".
          iPureIntro. do 2 (split; [done|]).
          split; last split; last split; last split; [..|done|done].
          - by rewrite lookup_app_1_eq. - set_solver+Eqso''. - set_solver+Eqco''. }

        iSpecialize ("HΦ" with "[]").
        { clear -NLtX12. by iIntros ([_ ?]). }
        iSpecialize ("HQ" with "[]").
        { iIntros "_". iExists G''. iFrame "Obs'' ES". by iPureIntro. }
        iIntros "!>". iFrame "XI HQ HΦ". rewrite -ExchangerInv_graph_master.
        by iFrame (EGCs'') "GM EM".
    }

    rewrite (view_at_objective_iff (graph_master _ _ _))
            (view_at_objective_iff (▷ EI _)).

    assert (OH': offer_hist (OfferAccepted m) t0 V0 Vw ζl2x').
    { simpl in OHl2. by rewrite /= Eqtl21 OHl2. }

    iMod ("Close2" with "[l2C HQ mD]") as "_".
    { iNext. iExists (OfferAccepted m), ζl2x', Vw. iSplitR; last iSplitL "l2C".
      - by iPureIntro.
      - iExists _. iFrame "l2C".
      - simpl. iExists v1. iFrame "mD HQ". }

    iIntros "!>".
    iMod ("Close" with "[GM LTm Offs xA l2A l2N' l2I']") as "_ {l2N2 l2Nx}".
    { iNext. iExists _.
      iDestruct (ExchangerInv_graph_master with "GM") as "[_ $]". iSplit; [done|].
      iExists LVs4, os4, T4. iFrame "LTm". iExists (Vb ⊔ V').
      iSplitL "xA". { iExists _; by iFrame "xA". } iSplitL; [|by iPureIntro].
      iApply (view_at_mono_2 with "Offs"); [solve_lat|].
      iExists γl2, γk2. iSplit; [by iPureIntro|].
      iSplitL "l2N'"; last iSplitL "l2A".
      - by iFrame "l2N'". - iExists _; iFrame "l2A".
      - by iFrame "l2I'". } clear Vb tx0.
    iIntros "!>". iMod ("CloseX" with "XI") as "_".
    iIntros "!>". wp_let.

    (* CAS to reset *)
    wp_bind (casʳˡˣ(_,_,_))%E.
    (* open the invariant *)
    iInv "EII" as (G5) "(EC & GM & EBI)" "Close".
    rewrite ExchangerBaseInv_unfold_snap.
    iDestruct ("EBI" with "[$LT3]") as (LVs5 os5 T5) "[(LTm & Locs) _]".
    iDestruct "Locs" as (Vb) "([%tx0 >xA] & Offs & >[%Eqos5 %EqD5])".

    (* TODO: lemma *)
    iDestruct (view_at_elim with "sV3 xN3") as "xN3'".
    iDestruct (AtomicPtsTo_AtomicSeen_latest_1 with "xA xN3'") as %Inos5.
    apply (lookup_weaken Eqtx3), toXChgHist_lookup_Some_loc,
          (filter_is_Some_fst_in Eqos5) in Inos5.
    (* TODO: slow *)
    wp_apply (AtomicSeen_CON_CAS_live_loc x γx _ _ _ _ _ l2 #0
                _ ∅ V4 Vb
              with "[$xN3' $xA $sV4]"); [done..|solve_ndisj| |done|].
    { intros ???. by apply toXChgHist_comparable_loc. }

    iIntros (b t' v' Vr5 V5 ζx5' ζx) "(F & sV5 & xN5 & xA & CASE)".

    (* close the invariant *)
    iMod ("Close" with "[EC GM LTm Offs xA F CASE]") as "_".
    { iNext. iExists _. iFrame "EC GM".
      iDestruct "CASE" as "[[Eq sVr5]|[Eq HVw]]".
      - iDestruct "Eq" as %(-> & ? & ->).
        iExists LVs5, os5, T5. iFrame "LTm".
        iExists (Vb ⊔ V5). iSplitL "xA". { iExists _. iFrame "xA". }
        iSplitL "Offs"; [by iFrame "Offs"|by iPureIntro].
      - iDestruct "Eq" as %[-> ->].
        iDestruct "HVw" as (Vw' (Frt' & Eqt' & Eqt'' & LeVr5w & _)) "_".
        iDestruct "F" as %([_ Subζx5'] & Eqt5' & _).
        assert (Eqζx : ζx = toXChgHist tx0 (LVs5 ++ [(None,Vw')])).
        { move : Subζx5' => /(lookup_weaken Eqt5').
          rewrite Eqt' lookup_insert_ne; [|clear;lia]. clear -Frt'.
          intros Eqt. revert Eqt Frt'.
          by apply (toXChgHist_insert_next_fresh None). }
        iExists (LVs5 ++ [(None,Vw')]), os5, T5. iFrame "LTm".
        iExists (Vb ⊔ V5). iSplitL "xA"; last iSplitL "Offs".
        + rewrite Eqζx. iExists _; iFrame "xA".
        + by iFrame "Offs".
        + iPureIntro. by rewrite filter_is_Some_app_None. } clear Vb tx0.

    iIntros "!>". wp_seq. wp_if. wp_op.
    iDestruct (monPred_in_mono _ _ LeV0 with "sV3'") as "#sV0".
    iDestruct (view_at_elim with "sV0 l2D") as "l2D".
    wp_read. by iApply (view_at_elim with "sV4 HΦ").

  - (* CAS succeeds *)
    iDestruct "F" as %[-> ->]. iDestruct "HVw" as (Vw F) "#[sVw HVw]".
    destruct F as (FRtx1 & Eqζx2 & Eqtx1' & LeVr2 & NEqVr2 & NLeVr2 & NEqV12 & LeV2w).

    have LeVV2 : V ⊑ V2. { clear -LeV1 LeVV1. by solve_lat. }
    have bLeVV2 : bool_decide (V ⊑ V2) by eapply bool_decide_unpack; eauto.
    (* V2 is the commit view, Vw the message view *)
    set Vex1 := mkDView V V2 Vw bLeVV2.

    set LVs' := LVs2 ++ [(Some m, Vw)].
    set os' := os2 ++ [(m, Vw)].

    (* initialize the hole *)
    iDestruct "Hm" as "[mL mD]".
    (* we revert the resources we need from V1 down back to V0, this is sound
      because under the hood V0 = V1. *)
    iCombine "mD GE AU AU'" as "mDAU".
    rewrite (AtomicPtsTo_CON_from_na_rel m #0 ((m >> 1) ↦{1} #v1 ∗ _)%I).
    iMod ("mDAU" with "mL") as (γm t0 V0 LeV0) "(mDAU & #mN & mA)".
    rewrite view_at_view_at. iDestruct "mDAU" as "(mD & #GE & AU & AU')".
    rewrite (AtomicPtsTo_CON_to_SW m). iMod "mA" as "[mA mC]".
    (* my token *)
    iMod UTok_alloc as (γk) "Tok".

    (* allocate the offer inv *)
    iAssert (@{V0} □ exchange_AU_proof' EI N γx γg x G1 M V v1 (λ v2, Φ #v2) α' β' Φ')%I
      with "[AU']" as "AU'".
    { rewrite -(view_at_objective_iff (InternInv _ _ _ _ _ _) V0).
      rewrite -(view_at_objective_iff (meta _ _ _) V0).
      iCombine "AU' EII MT" as "AEM".
      iApply (view_at_mono with "AEM"); [done|].
      iIntros "(#AU & #EII & #MT) !>" (b1 b2) "AU' XI".
      iSpecialize ("AU" $! b1 b2 with "AU' XI").
      iAuIntro. iApply (aacc_aupd_commit with "AU"); [done|].
      iIntros (G) "EI".
      iAaccIntro with "EI"; first by eauto with iFrame.
      iIntros (V' G' xchg1 xchg2 v2 Vex1' Vex2' M') "(EI & sV' & HF & CASE) !>".
      iExists V', G', xchg1, xchg2. iExists v2, Vex1', Vex2', M'. iFrame.
      iSplitL.
      - iDestruct "CASE" as "[(F & Gs & ?)|[F CASE]]".
        + iLeft. iSplit; [done|]. iFrame "Gs". iExists _, _. by iFrame "∗ MT EII".
        + iRight. iFrame "F".
          iDestruct "CASE" as "[CASE|CASE]"; [iLeft|iRight];
            iDestruct "CASE" as "($ & $ & S)"; iExists _, _; by iFrame "S MT EII".
      - iIntros "[HΦ $] !> HP". iApply "HΦ". iIntros "Hv".
        iDestruct ("HP" with "Hv") as (G'') "(F & Gs & SL)".
        iExists G''. iFrame "F Gs". iExists _, _. by iFrame "SL MT EII". }

    set AU' : vProp := atomic_update (⊤ ∖ ↑N) (↑histN) α' β' Φ'.
    iMod (inv_alloc (offN N) _ (offer_rep m γm γk v1 t0 V0 AU' _)
            with "[mD mC AU]") as "#mOI".
    { iNext. iExists OfferMatching, _, V0. iSplitR; [by iPureIntro|].
      iSplitL "mC". { iExists _; iFrame "mC". }
      simpl. iFrame "mD AU". }
    iAssert (offer_inv EI N γx γg x m γm γk t0 V0) with "[GE AU']" as "#OI".
    { iExists _, _, _. iFrame "mOI". iExists M, V.
      iDestruct "GE" as "($ & Gs' & _)". iExists _. iFrame "Gs'".
      iExists TA', TB', α', β', Φ'. iFrame "AU'".
      iApply view_at_at. iIntros "!> $". }

    iAssert (⌜m ∉ dom T2⌝)%I with "[Offs mA]" as %FRm.
    { clear -EqD2. rewrite AtomicPtsTo_own_loc_prim.
      iDestruct "mA" as (C) "mC".
      iDestruct (main_offer_disjoint with "Offs mC") as %NInos2.
      iPureIntro. by rewrite EqD2 elem_of_list_to_set. }

    (* update T *)
    set T' : gmap loc offer_info := <[m:=(γm, γk)]> T2.
    have SubT2: T2 ⊆ T'.
    { by apply insert_subseteq, (not_elem_of_dom (D:= gset _)). }
    iMod (LTM_update _ T2 T' with "LTm") as "[LTm LT']"; [done|].

    (* close invariant *)
    iMod ("Close" with "[GM LTm Offs xA mA]") as "_".
    { iNext. iExists _. iFrame "GM". iSplit; [done|].
      iExists LVs', os', T'. iFrame "LTm". iExists (Vb ⊔ V2).
      iSplitL "xA"; last iSplitL.
      - move : Subζx2' => /(lookup_weaken Eqtx1).
        rewrite Eqζx2 lookup_insert_ne; [|clear;lia].
        intros Eqt1. rewrite (toXChgHist_insert_next_fresh (Some m) _ Eqt1 FRtx1).
        iExists tx0. iFrame "xA".
      - rewrite main_offers_app (main_offers_map_mono SubT2).
        iFrame "Offs". rewrite /main_offers big_sepL_singleton.
        iExists γm , γk.
        have LeV1w : V1 ⊑ Vw. { clear -LeV1 LeV2w. solve_lat. }
        have LeV0w : V0 ⊑ Vw. { clear -LeV0 LeV1w. solve_lat. }
        iSplitR; last iSplitR; last iSplitL "mA".
        + iPureIntro. by rewrite lookup_insert.
        + clear -LeV1w. iExists _. rewrite view_at_view_at. by iFrame "mN".
        + iExists _; iFrame "mA".
        + iExists t0, V0. iSplitR; [by iPureIntro|by iFrame "OI"].
      - iPureIntro. rewrite filter_app Eqos2 2!fmap_app dom_insert list_to_set_app.
        split; [done|clear -EqD2;set_solver]. } clear tx0 FRtx1 Eqζx2 Vb.

    iIntros "!>". wp_if. wp_op.
    rewrite shift_0.
    (* CAS to try to cancel *)
    (* Commit CANCELLED if succeeds *)
    wp_bind (casʳˡˣ(_,_,_))%E.

    iDestruct (view_at_elim with "sV1 mN") as "mN'".

    (* open invariant *)
    iInv "EXI" as "XI" "CloseX".
    iInv "EII" as (G3) "(>[%CON3 %EGCs] & GM & EBI)" "Close".
    rewrite ExchangerBaseInv_unfold_snap.
    iDestruct ("EBI" with "[$LT']") as (LVs3 os3 T3) "[(LTm & Locs) >%LeT']".
    iDestruct "Locs" as (Vb) "([%tx0 >xA] & Offs & >[%Eqos3 %EqD3])".

    (* TODO accessor. get the AtomicPtsTo of m *)
    iDestruct (AtomicPtsTo_AtomicSeen_latest_1 with "xA xN2") as %Inos3.
    apply (lookup_weaken Eqtx1'), toXChgHist_lookup_Some_loc,
          (filter_is_Some_fst_in Eqos3) in Inos3.
    rewrite (main_offers_access Inos3).
    iDestruct "Offs" as "[mO Offs]".
    iDestruct "mO" as (γm' γk') "(>%EqTm' & Obs & [%ζm >mA] & Off)".
    assert (γm' = γm ∧ γk' = γk) as [-> ->].
    { clear -EqTm' LeT'.
      eapply lookup_weaken_inv in EqTm';
        [..|exact LeT']; [|by rewrite lookup_insert]. by inversion EqTm'. }
    (* open the offer invariant *)
    iInv "mOI" as "HIm" "Close2".
    iDestruct "HIm" as (s ζl0 Vl2) "(>[%OHm _] & [%VmC >mC] & OR)".
    iDestruct (AtomicPtsTo_SWriter_agree with "mA mC") as %<-.

    wp_apply (AtomicSWriter_CAS_int m γm _ _ _ _ _ _ 0 #CANCELLED tid ∅ V2 Vb
              with "[$mN' $mA $mC $sV2]"); [done..|solve_ndisj| | |].
    { intros ???. by eapply offer_hist_comparable_0. }
    { simpl. by iFrame "HRE". }

    iIntros (b tm' vm' Vr3 V3 ζm'' ζm') "(F & #sV3 & mN3 & [mA mC] & CASE)".
    iDestruct "F" as %(Subζm'' &Eqtm' & _ & LeV2).

    iMod (LTM_master_fork with "LTm") as "[LTm #LT3]".

    iDestruct "CASE" as "[[Eq sVr3]|[Eq Hw]]"; last first.
    { (* CAS succeeds. Offer cancelled. We get back the AU *)
      iDestruct "Eq" as %[-> ->].
      iDestruct "Hw" as (Vw' (FRtm' & Eqtm1' & Eqtm'' & LeVr3 &
                              NEqVr3 & NLeVr3 & NEqV2 & _)) "_".

      iAssert (⌜s = OfferMatching ∧ ζm = {[t0 := (#0, V0)]} ∧ tm' = t0 ∧ Vr3 = V0⌝)%I
        with "[Tok OR]" as %(-> & -> & -> & ->).
      { iClear "#". destruct Subζm'' as [_ Subζm''].
        destruct s; simpl in OHm.
        - iPureIntro. do 2 (split; [done|]).
          move : Subζm'' => /(lookup_weaken Eqtm').
          rewrite Eqtm1' OHm lookup_insert_ne; [|clear;lia].
          clear. rewrite lookup_singleton_Some. intros []. by simplify_eq.
        - simpl. by iDestruct (UTok_unique with "Tok OR") as %?.
        - exfalso. move : Subζm'' => /(lookup_weaken Eqtm').
          rewrite Eqtm1' lookup_insert_ne; [|clear;lia]. clear -FRtm' OHm.
          subst ζm. apply lookup_insert_None in FRtm' as [_ NEq].
          rewrite lookup_insert_Some.
          intros [[_ Eq]|[_ [? _]%lookup_singleton_Some]];
            [by inversion Eq|by subst].
        - simpl. by iDestruct (UTok_unique with "Tok OR") as %?. }

      simpl. iDestruct "OR" as "[mD AU]".
      iDestruct (monPred_in_mono _ _ LeV0 with "sV1") as "#sV0".
      iDestruct (view_at_elim with "sV0 AU") as "AU".

      iMod ("Close2" with "[Tok mC]") as "_".
      { iNext. iExists OfferCancelled, ζm', Vw'. iSplitR; [by iPureIntro|].
        iSplitL "mC". { iExists _; iFrame "mC". }
        simpl. by iFrame "Tok". }

      (* CANCEL_CASE 1 : Now commit CANCELLED. *)
      iIntros "!>".
      iDestruct (ExchangerInv_graph_master' with "[$GM //]") as "GM".
      iDestruct (graph_master_snap_included with "GM Gs") as %SubG1.

      set E3 := G3.(Es).
      have SubE1 : E1 ⊑ E3 by apply SubG1.
      set V' := V3.
      have LeVV' : V ⊑ V'. { clear -LeV1 LeVV1 LeV2. rewrite /V'. by solve_lat. }
      have bLeVV' : bool_decide (V ⊑ V') by eapply bool_decide_unpack; eauto.
      set Vex1' := mkDView V V' V' bLeVV'.
      set ExE := Exchange v1 CANCELLED.
      iDestruct (bi.persistent_sep_dup with "Gs") as "[_ [_ PV]]".
      iDestruct (SeenLogview_closed with "PV") as "%SubD1 {PV}".
      have SubM: set_in_bound M E3.
      { clear - SubD1 SubE1. by eapply set_in_bound_mono. }
      assert (GIP:= graph_insert_props_base _ ExE _ Vex1' SubM EGCs).
      destruct GIP as [xchgId M' egV' G' LeG' SubM' SUB' InId FRGe1 EGCs'].
      set E' := G'.(Es).
      have LeE' : E3 ⊑ E' by apply LeG'.
      have CON' : ExchangerConsistent G' by apply exchange_cancel_graph_insert.

      iMod ("Pr" $! true true with "AU XI") as (G3') "[>GM' HClose]".
      iDestruct (ExchangerInv_graph_master_agree with "GM GM'")
        as "(-> & GM & GM')".

      iCombine "GM GM'" as "GM".
      iMod (graph_master_update _ _ _ LeG' EGCs' with "GM") as "[[GM GM'] Gs']".

      have LeV0V' : V0 ⊑ V'. { clear -LeV0 LeV1 LeV2. rewrite /V'. solve_lat. }
      (* TODO: duplicates *)
      iAssert (@{V'} SeenLogview E' M')%I with "[GE]" as "#SL".
      { iDestruct "GE" as "(_ & [_ SL] & _)".
        rewrite -SeenLogview_insert'. iSplitL; [|done].
        erewrite SeenLogview_map_mono; [iFrame "SL"|done..]. }

      iAssert (@{V'} graph_snap γg G' M')%I with "[Gs']" as "#Gss' {Gs'}".
      { iFrame "Gs' SL". }

      rewrite bi.and_elim_r.
      iMod ("HClose" $! V' G' xchgId xchgId CANCELLED Vex1' Vex1' M'
                      with "[GM' $sV3]") as "[HΦ XI]".
      { (* Public Post *)
        iDestruct (ExchangerInv_graph_master with "GM'") as "[_ $]".
        iSplitR; [by iPureIntro|]. iLeft.
        iSplitR; [by iPureIntro|]. iFrame "Gss'".
        iExists _, _. iFrame "MT EII".
        iExists _. iDestruct "GE" as "(_ & _ & $)". }

      (* close the invariant by switching to CANCELLED *)
      iMod ("Close" with "[GM LTm xA mA Obs Off Offs]") as "_".
      { iNext. iExists _.
        iDestruct (ExchangerInv_graph_master with "GM") as "[_ $]".
        iSplit; [done|]. iExists _, os3, _. iFrame "LTm".
        iExists (Vb ⊔ V'). iSplitL "xA". { iExists _. by iFrame "xA". }
        iSplitL; [|by iPureIntro].
        iApply (view_at_mono_2 with "Offs"); [solve_lat|].
        iExists γm, γk. iSplit; [by iPureIntro|].
        iSplitL "Obs"; last iSplitL "mA".
        - by iFrame "Obs". - iExists _; iFrame "mA". - iFrame "Off". }

      iIntros "!>". iMod ("CloseX" with "XI") as "_".

      (* Complete this CANCELLED case *)
      iIntros "!>". wp_if. iApply "HΦ". by iIntros "{#∗%}" ([]).
      (* End CANCEL_CASE 1 *) }

    (* CAS failed. Our offer was matched. *)
    iDestruct "Eq" as %(-> & NEqvm' & ->).

    iAssert (⌜ ∃ l2, s = OfferAccepted l2 ∧
              vm' = l2 ∧ tm' = (t0 + 1)%positive ∧ Vr3 = Vl2 ⌝)%I
      with "[Tok OR]" as %(l2 & -> & -> & -> & ->).
    { iClear "#". clear -NEqvm' OHm Subζm'' Eqtm'.
      destruct Subζm'' as [_ Subζm''].
      apply (lookup_weaken  Eqtm') in Subζm''.
      destruct s; simpl in OHm.
      - exfalso. subst ζm.
        apply lookup_singleton_Some in Subζm'' as []. simplify_eq.
        by inversion NEqvm'.
      - simpl. by iDestruct (UTok_unique with "Tok OR") as %?.
      - iPureIntro. exists l. split; [done|]. subst ζm.
        move : Subζm''. rewrite lookup_insert_Some lookup_singleton_Some.
        intros [[]|(_&_&?)]; simplify_eq; [done|]. by inversion NEqvm'.
      - simpl. by iDestruct (UTok_unique with "Tok OR") as %?. }

    simpl. simpl in OHm.
    (* finishing *)
    (* close the offer invariant *)
    iMod ("Close2" with "[mC Tok]") as "_".
    { iNext. iExists (OfferAcked l2), ζm, Vl2. iSplitR; [by iPureIntro|].
      iSplitL "mC". { iExists _; iFrame "mC". }
      simpl. by iFrame "Tok". } clear VmC.
    iIntros "!>".
    (* close the invariant by switching to OfferAcked *)
    iMod ("Close" with "[GM LTm Obs xA mA Off Offs]") as "_".
    { iNext. iExists _. iFrame "GM". iSplit; [done|].
      iExists LVs3, os3, T3. iFrame "LTm".
      iExists (Vb ⊔ V3). iSplitL "xA". { iExists _. by iFrame "xA". }
      iSplit; [|by iPureIntro].
      iApply (view_at_mono_2 with "Offs"); [solve_lat|].
      iExists γm, γk. iSplit; [by iPureIntro|].
      iSplitL "Obs"; last iSplitL "mA".
      - by iFrame "Obs". - iExists _. iFrame "mA". - iFrame "Off". } clear Vb tx0.

    iIntros "!>". iMod ("CloseX" with "XI") as "_".

    iIntros "!>". wp_if. wp_op. rewrite shift_0.
    wp_bind (!ᵃᶜ_)%E. (* we're going to read l2 *)

    iDestruct (view_at_elim with "sV3 mN3") as "mN3". iDestruct "mN3" as "#mN3".
    (* open invariant *)
    iInv "EII" as (G4) "(>%CON4 & GM & EBI)" "Close".
    rewrite ExchangerBaseInv_unfold_snap.
    (* TODO accessor lemma of m *)
    iDestruct ("EBI" with "[$LT3]") as (LVs4 os4 T4) "[(LTm & Locs) >%LeT3]".
    iDestruct "Locs" as (Vb) "([%tx0 >xA] & Offs & >[%Eqos4  %EqD])".

    (* TODO: lemma. get the AtomicPtsTo of m *)
    iDestruct (AtomicPtsTo_AtomicSeen_latest_1 with "xA xN2") as %Inos4.
    apply (lookup_weaken  Eqtx1'), toXChgHist_lookup_Some_loc,
          (filter_is_Some_fst_in Eqos4) in Inos4.
    rewrite (main_offers_access Inos4).
    iDestruct "Offs" as "[mO Offs]".
    iDestruct "mO" as (γm' γk') "(>%EqTm4 & Obs & [%ζm4 >mA] & Off)".
    assert (γm' = γm ∧ γk' = γk) as [-> ->].
    { clear -EqTm4 LeT3 EqTm'.
      apply (lookup_weaken_inv _ _ _ _ _ EqTm' LeT3) in EqTm4.
      by inversion EqTm4. }
    iDestruct (AtomicPtsTo_AtomicSeen_latest_1 with "mA mN3") as %Subζm4.

    wp_apply (AtomicSeen_acquire_read with "[$mN3 $mA $sV3]"); [solve_ndisj|].
    iIntros (t' v' V4' V4 ζh') "(F & sV4 & mN4 & mA)".
    iDestruct "F" as %([Subh1 Subh2] & Eqt' & MAXt' & LeV3).

    (* open the offer invariant to learn agreement *)
    iInv "mOI" as "HIm" "Close2".
    iDestruct "HIm" as (s ζl0 Vl2') "(>[%OH4 _] & [%VmC >mC] & OR')".
    iDestruct (AtomicPtsTo_SWriter_agree with "mA mC") as %<-.
    iMod ("Close2" with "[mC OR']") as "_".
    { iNext. iExists s, _, Vl2'. iFrame "OR'".
      iSplitR; [by iPureIntro|iExists _; iFrame "mC"]. }

    (* we know the shape of ζm4 *)
    assert (ζm4 = {[(t0 + 1)%positive := (#l2, Vl2); t0 := (#0, V0)]}) as Eq4.
    { apply (lookup_weaken Eqtm'),
            (offer_hist_lookup_matched OH4) in Subζm4.
      clear -OH4 Subζm4. destruct Subζm4 as (CASE & _ & <-).
      destruct CASE; by subst s. } clear OH4 VmC Vl2' s.

    (* close the invariant *)
    iMod ("Close" with "[GM LTm Obs xA mA Offs Off]") as "_".
    { iNext. iExists _. iFrame "GM". iSplit; [done|].
      iExists LVs4, os4, T4. iFrame "LTm".
      iExists (Vb ⊔ V4). iSplitL "xA". { iExists _. by iFrame "xA". }
      iSplit; [|by iPureIntro].
      iApply (view_at_mono_2 with "Offs"); [solve_lat|].
      iExists γm, γk. iSplit; [by iPureIntro|].
      iSplitL "Obs"; last iSplitL "mA".
      - by iFrame "Obs". - iExists _; by iFrame "mA". - iFrame "Off". } clear Vb.

    (* now we know that we must have read l2. *)
    assert (t' = (t0 + 1)%positive ∧ v' = #l2 ∧ V4' = Vl2) as (-> & -> & ->).
    { apply (lookup_weaken Eqt') in Subh2.
      have Get' : (t0 + 1 ≤ t')%positive. { apply MAXt'. by eexists. }
      clear -Eq4 Subh2 Get'. subst ζm4.
      move : Subh2. rewrite lookup_insert_Some lookup_singleton_Some.
      intros [[]|(_&?&_)]; [by simplify_eq|subst; by lia]. }

    iIntros "!>". wp_let. wp_op.
    iDestruct (view_at_elim with "[sV4] OR") as (v2) "[l2D HΦ]".
    { iApply (monPred_in_mono with "sV4"). simpl. clear -LeV3. solve_lat. }
    wp_read. iFrame "HΦ".
Qed.
End proof.

Definition exchanger_impl
  Σ `{!noprolG Σ, !xchgG Σ, !atomicG Σ} :
  exchanger_piggyback_spec Σ := {|
  spec_graph_piggyback.ExchangerInv_ExchangerConsistent :=
    ExchangerInv_ExchangerConsistent_instance;
  spec_graph_piggyback.ExchangerInv_graph_master_acc :=
    ExchangerInv_graph_master_acc_instance;
  spec_graph_piggyback.ExchangerInv_graph_snap :=
    ExchangerInv_graph_snap_instance;
  spec_graph_piggyback.ExchangerInv_agree := ExchangerInv_agree;

  spec_graph_piggyback.ExchangerLocal_graph_snap :=
    ExchangerLocal_graph_snap_instance;
  spec_graph_piggyback.ExchangerLocal_upgrade :=
    ExchangerLocal_upgrade_instance;
  spec_graph_piggyback.ExchangerLocal_union :=
    ExchangerLocal_union_instance;

  spec_graph_piggyback.ExchangerLocalLite_graph_snap :=
    ExchangerLocalLite_graph_snap_instance;
  spec_graph_piggyback.ExchangerLocalLite_from :=
    ExchangerLocalLite_from_instance;
  spec_graph_piggyback.ExchangerLocalLite_to :=
    ExchangerLocalLite_to_instance;
  spec_graph_piggyback.ExchangerLocalLite_upgrade :=
    ExchangerLocalLite_upgrade_instance;

  spec_graph_piggyback.new_exchanger_spec := new_exchanger_spec;
  spec_graph_piggyback.exchange_spec := exchange_spec;
|}.
