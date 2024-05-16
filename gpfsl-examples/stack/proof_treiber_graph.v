From iris.bi Require Import lib.fractional.
From iris.algebra Require Import auth gset gmap agree proofmode_classes.
From iris.proofmode Require Import tactics.

From gpfsl.algebra Require Import to_agree.
From gpfsl.base_logic Require Import meta_data.
From gpfsl.logic Require Import logatom atomics invariants.

From gpfsl.logic Require Import repeat_loop new_delete.
From gpfsl.examples Require Import map_seq loc_helper.
From gpfsl.examples.stack Require Import spec_graph code_treiber.

Require Import iris.prelude.options.

(** Prove that Treiber stack satisfies the logically atomic, history-based
  specifications *)

#[local] Notation next := 0%nat (only parsing).
#[local] Notation data := 1%nat (only parsing).

#[local] Notation graph := (graph sevent).
#[local] Notation event_list := (event_list sevent).
#[local] Notation graph_event := (graph_event sevent).

Implicit Types (T : gmap loc event_id) (S : list loc) (M : logView).
Implicit Types (s n: loc) (tid: thread_id) (G: graph) (ζ : absHist) (γ: gname).

(* The loc-event_id map is in sync with the event map w.r.t. push events. *)
Definition EM_equiv T (E : event_list) : Prop :=
  ∀ e, (∃ n, T !! n = Some e) ↔ (∃ v, ge_event <$> E !! e = Some $ Push v).

Definition popped_nodes T S : gset loc := dom T ∖ list_to_set S.

(** * Pure Coq properties of the Stack *)
Record StackProps G T S
  : Prop := mkStackProps {
  (* T track whatever that has been in the stack, while S is the current stack *)
  stk_sub : list_to_set S ⊆ dom T ;
  (* The following two properties are already included in [StackBaseInv] (see below). *)
  stk_em :
    (* T contains only Push events *)
    EM_equiv T G.(Es) ;
  stk_inj_1 :
    (* T is injective w.r.t the event_id.
      This is a strong condition that doesn't support reusing locations. *)
    gmap_inj T ;
  stk_popped :
    (* Popped item must be in T but not S *)
    ∀ n e, T !! n = Some e → (n ∈ popped_nodes T S ↔ e ∈ (elements G.(so)).*1) ;
  stk_unpop_1 :
    (* Unpopped items should be ordered LIFO *)
    ∀ n1 n2 e1 e2, list_before S n1 n2 →
      T !! n1 = Some e1 → T !! n2 = Some e2 → (e2 ≤ e1)%nat ;
  stk_unpop_2 :
    (* Unpopped items should be well-bracketted w.r.t. popped items *)
    ∀ n e, n ∈ S → T !! n = Some e → ∀ ps pp, (ps, pp) ∈ G.(so) →
      (* any push-pop pair is either before or after the elements in the stack*)
      ((ps ≤ e ∧ pp ≤ e) ∨ (e ≤ ps ∧ e ≤ pp))%nat ;
}.

(**** GHOST STATE CONSTRUCTION -----------------------------------------------*)
(** The CMRA & functor we need. *)

#[local] Notation tstk_mapUR' := (gmapUR loc (agreeR (leibnizO event_id))).
#[local] Notation tstk_mapUR := (authUR tstk_mapUR').

Class tstackG Σ := TStackG {
  tstk_graphG : inG Σ (graphR sevent) ;
  (* a persistent map of from logical nodes to event ids and locations. *)
  tstk_stackG : inG Σ tstk_mapUR ;
}.
Local Existing Instances tstk_graphG.

Definition tstackΣ : gFunctors :=
  #[GFunctor (graphR sevent); GFunctor tstk_mapUR].

Global Instance subG_tstackΣ {Σ} : subG tstackΣ Σ → tstackG Σ.
Proof. solve_inG. Qed.

Section ghost.
Context `{!inG Σ tstk_mapUR}.
#[local] Notation iProp := (iProp Σ).
#[local] Notation vProp := (vProp Σ).

(* The logical snapshots of the stack *)
Definition LTM_snap  γ T : iProp := own γ (◯ (to_agree <$> T) : tstk_mapUR).
Definition LTM_snapv γ T : vProp := ⎡ LTM_snap γ T ⎤.
Definition LTM_ssnap  γ n e : iProp := LTM_snap γ {[n := e]}.
Definition LTM_ssnapv γ n e : vProp := ⎡ LTM_ssnap γ n e ⎤.

Definition LTM_auth q T : tstk_mapUR := ●{#q} (to_agreeM T) ⋅ ◯ (to_agreeM T).
Definition LTM_master  γ q T : iProp := own γ (LTM_auth q T).
Definition LTM_masterv γ q T : vProp := ⎡ LTM_master γ q T ⎤.
End ghost.
#[global] Typeclasses Opaque LTM_auth.

(** Namespace for our internal invariant. See `StackInternalInv`. *)
Definition tstackN (N : namespace) (s : loc) := N .@ s.

Definition toHeadHist (start : time) (LVs : list (option loc * view)) : absHist :=
  map_seqP start ((λ olv, (#(oloc_to_lit olv.1), olv.2)) <$> LVs).

Definition HeadValues T (LVs : list (option loc * view)) : Prop :=
  (* only contains locations or null *)
  ∀ n, (Some n) ∈ LVs.*1 ↔ n ∈ dom T.

Definition HeadUnpopped S ζ : Prop :=
  ∀ t n, n ∈ S → fst <$> ζ !! t = Some #n →
    ∀ t', (t ≤ t')%positive → fst <$> ζ !! t' = Some #null → False.

Definition PushHistory (E : event_list) (LVs : list (option loc * view)) : Prop :=
  ∀ e eV (v : Z), E !! e = Some eV → eV.(ge_event) = Push v →
    ∃ n : loc, (Some n, eV.(ge_view).(dv_wrt)) ∈ LVs.

Definition StackTopView (LVs : list (option loc * view)) (Vh : view) : Prop :=
  ∀ V, V ∈ LVs.*2 → V ⊑ Vh.

Definition SeenPushed T ζ M : Prop :=
  ∀ e (n : loc), e ∈ M → T !! n = Some e → ∃ t, fst <$> ζ !! t = Some #n.

Definition next_nodes S : list (option loc) :=
  match S with
  | [] => []
  | _ :: S' => (Some <$> S') ++ [None]
  end.

Lemma next_nodes_length S : length (next_nodes S) = length S.
Proof. destruct S; [done|]. rewrite /= app_length fmap_length /=. lia. Qed.

Lemma next_nodes_cons n S :
  next_nodes (n :: S) = hd_error S :: next_nodes S.
Proof. rewrite /=. by destruct S as [|n' S]. Qed.

Lemma toHeadHist_lookup_Some t0 LVs t v V :
  toHeadHist t0 LVs !! t = Some (v, V) ↔
  (t0 ≤ t)%positive
  ∧ ∃ on, v = #(oloc_to_lit on)
  ∧ LVs !! (Pos.to_nat t - Pos.to_nat t0)%nat = Some (on, V).
Proof.
  rewrite lookup_map_seqP_Some. f_equiv.
  rewrite list_lookup_fmap fmap_Some. split.
  - intros ([] & ? & ?). simplify_eq. naive_solver.
  - intros (on & -> & ?). exists (on, V). naive_solver.
Qed.

Lemma toHeadHist_lookup_None t0 LVs t :
  (toHeadHist t0 LVs) !! t = None ↔
  (t < t0)%positive ∨ (t0 +p (length LVs) ≤ t)%positive.
Proof. by rewrite lookup_map_seqP_None fmap_length. Qed.

Lemma toHeadHist_lookup_Some_is_comparable_nullable_loc LVs t0 t v V (on : option loc) :
  toHeadHist t0 LVs !! t = Some (v, V) →
  ∃ vl : lit, v = #vl ∧ lit_comparable (oloc_to_lit on) vl.
Proof.
  rewrite toHeadHist_lookup_Some. intros (? & on' & -> & _).
  exists (oloc_to_lit on'). split; [done|].
  destruct on, on'; constructor.
Qed.

Lemma toHeadHist_insert t0 LVs t on V  :
  (Pos.to_nat t - Pos.to_nat t0)%nat = length LVs →
  (1 ≤ length LVs)%nat →
  <[t := (#(oloc_to_lit on), V)]>(toHeadHist t0 LVs) =
  toHeadHist t0 (LVs ++ [(on, V)]).
Proof.
  intros Eq ?. apply map_eq.
  intros i. case (decide (i = t)) => [->|?].
  - rewrite lookup_insert. symmetry.
    apply toHeadHist_lookup_Some. split; [lia|].
    rewrite Eq !lookup_app_r // Nat.sub_diag /=. naive_solver.
  - rewrite lookup_insert_ne; [|done].
    destruct (toHeadHist t0 LVs !! i) as [[vi Vi]|] eqn:Eqi; rewrite Eqi; symmetry.
    + apply toHeadHist_lookup_Some in Eqi as (Letn & on' & -> & Eq1).
      apply toHeadHist_lookup_Some. split; [done|].
      exists on'. split; [done|]. by apply (lookup_app_l_Some _ _ _ _ Eq1).
    + apply toHeadHist_lookup_None.
      apply toHeadHist_lookup_None in Eqi as [?|Eqi]; [by left|right].
      rewrite app_length /=. move : Eqi.
      rewrite Nat.add_1_r pos_add_succ_r_2.
      rewrite (_: t0 +p length LVs = t); [lia|]. rewrite -Eq /pos_add_nat; lia.
Qed.

Lemma SeenPushed_hist_mono T ζ ζ' M :
  ζ ⊆ ζ' → SeenPushed T ζ M → SeenPushed T ζ' M.
Proof.
  intros Subζ SP e n InV InT.
  destruct (SP _ _ InV InT) as [t Eqt].
  exists t. move : Eqt. rewrite lookup_fmap_Some'.
  intros ([v V] & Eq & Eq1). simpl in Eq. subst v.
  by rewrite (lookup_weaken _ _ _ _ Eq1 Subζ).
Qed.

Lemma SeenPushed_map_mono T T' ζ M :
  (∀ e n, e ∈ M → T' !! n = Some e → T !! n = Some e) →
  T ⊆ T' → SeenPushed T ζ M → SeenPushed T' ζ M.
Proof.
  intros In SubT SP e n InV InT. by apply (SP _ _ InV), In.
Qed.

Lemma SeenPushed_mono E E' T T' ζ ζ' M :
  EM_equiv T E → EM_equiv T' E' →
  gmap_inj T' →
  set_in_bound M E →
  E ⊑ E' → T ⊆ T' → ζ ⊆ ζ' →
  SeenPushed T ζ M → SeenPushed T' ζ' M.
Proof.
  intros ET ET' INJ Sub SubE SubT Subζ' SP.
  eapply (SeenPushed_hist_mono _ _ _ _ Subζ').
  revert SP. apply SeenPushed_map_mono; [|done].
  intros e' n' In' Eq'.
  assert (Sube':= Sub _ In').
  destruct (ET' e') as [[v' Eqv'] _]. { by exists n'. }
  move : Eqv' => /list_lookup_fmap_inv' [eV' [Eqv' Eqe']].
  assert (Eqe := prefix_lookup_inv _ _ _ _ Eqe' Sube' SubE).
  destruct (ET e') as [_ [n'' ETx]]. { exists v'. by rewrite Eqe /= Eqv'. }
  assert (Eqn := INJ _ _ _ Eq' (lookup_weaken _ _ _ _ ETx SubT)).
  by subst n''.
Qed.

Lemma SeenPushed_union T ζ M1 M2 :
  SeenPushed T ζ M1 → SeenPushed T ζ M2 → SeenPushed T ζ (M1 ∪ M2).
Proof. by intros SP1 SP2 e n [Ine|Ine]%elem_of_union; [apply SP1|apply SP2]. Qed.

Lemma SeenPushed_union_2 T ζ1 ζ2 M1 M2 :
  ζ1 ∪ ζ2 = ζ2 ∪ ζ1 →
  SeenPushed T ζ1 M1 → SeenPushed T ζ2 M2 → SeenPushed T (ζ1 ∪ ζ2) (M1 ∪ M2).
Proof.
  intros EqU SP1 SP2 e n [Ine|Ine]%elem_of_union Eqn.
  - destruct (SP1 _ _ Ine Eqn) as [t Eqt].
    exists t. apply lookup_fmap_Some' in Eqt as (nl & Eq1 & Eqt).
    apply lookup_fmap_Some'. exists nl. split; [done|].
    by apply lookup_union_Some_l.
  - destruct (SP2 _ _ Ine Eqn) as [t Eqt].
    exists t. apply lookup_fmap_Some' in Eqt as (nl & Eq1 & Eqt).
    apply lookup_fmap_Some'. exists nl. split; [done|].
    rewrite EqU. by apply lookup_union_Some_l.
Qed.

Lemma EM_equiv_union E T1 T2 :
  EM_equiv T1 E → EM_equiv T2 E → EM_equiv (T1 ∪ T2) E.
Proof.
  intros EM1 EM2 e. split.
  - intros [n [EqT|[EqTN EqT]]%lookup_union_Some_raw].
    + apply EM1. by eexists.
    + apply EM2. by eexists.
  - intros [n EqT]%EM1. exists n. by apply lookup_union_Some_l.
Qed.

(**** THE INVARIANT AND LOCAL ASSERTIONS -------------------------------------*)
Section Interp.
Context `{!noprolG Σ, !tstackG Σ, !atomicG Σ}.
Local Existing Instances tstk_graphG tstk_stackG.

#[local] Notation iProp := (iProp Σ).
#[local] Notation vProp := (vProp Σ).

Definition seen_pushed E eid v : vProp :=
  ∃ eV : graph_event, ⌜ eV.(ge_event) = Push v⌝ ∗ ⊒(eV.(ge_view).(dv_wrt)) ∗
    SeenEvent E eid eV.

Definition in_sloc E T n (on' : option loc) : vProp :=
  ∃ (v : Z) e,
    ⌜ T !! n = Some e ⌝
    ∗ (∃ q, (n >> next) ↦{q} #(oloc_to_lit on'))
    ∗ (n >> data) ↦ #v
    (* ∗ ⎡ † n … 2 ⎤ *) (* needed for garbage collection *)
    ∗ seen_pushed E e v
  .

Definition in_slocs E T S : vProp :=
  [∗ list] n ; on' ∈ S ; (next_nodes S), in_sloc E T n on'.

Definition all_slocs (LVs : list (option loc * view)) : vProp :=
  (* TODO: use read-only atomic points-to [ROPtsTo] here instead of fractions. *)
  [∗ list] onV ∈ LVs,
    if onV is (Some n, V)
    then (∃ q on, @{V} (n >> next) ↦{q} #(oloc_to_lit on))%I
         (* ∗ ⎡ † n … 2 ⎤ *) (* needed for garbage collection *)
    else emp%I
    .

#[global] Instance all_slocs_objective LVs : Objective (all_slocs LVs).
Proof. apply big_sepL_objective => _ [[n|] V]; apply _. Qed.
#[global] Instance all_slocs_timeless LVs : Timeless (all_slocs LVs).
Proof. apply big_sepL_timeless => _ [[n|] V]; apply _. Qed.

(* Locs of the Stack: Head, popped nodes, and nodes *)
Definition StackLocs_no_exist s (E : event_list) γh T S t0 LVs Vh : vProp :=
  (* needed for garbage collection *)
  (* ⎡ † s … 1 ⎤ ∗ *)
  (* top of the stack is also top of the head's history *)
  let vh := (hd_error S) in
  let LVs' := (LVs ++ [(vh,Vh)]) in
  let ζh := (toHeadHist t0 LVs') in
  s at↦{γh} ζh
  ∗ ⌜ HeadValues T LVs' ∧ HeadUnpopped S ζh
    ∧ PushHistory E LVs' ∧ StackTopView LVs' Vh ⌝
  (* anything that is ever in the stack nodes *)
  ∗ all_slocs LVs'
  (* the actual stack: all resources are at the top's write view *)
  ∗ @{Vh} in_slocs E T S
  .

Definition StackLocs s E γh T S : vProp :=
  ∃ t0 LVs Vh, StackLocs_no_exist s E γh T S t0 LVs Vh.

Definition SeenHead γh s T M : vProp :=
  ∃ ζ, s sn⊒{γh} ζ ∗ ⌜SeenPushed T ζ M⌝.

Definition StackViews γh s (E : event_list) T : vProp :=
  ∀ e v V M, ⌜ E !! e = Some (mkGraphEvent (Push v) V M) ⌝ →
    (* the physical view V observed the logical view M *)
    @{V.(dv_comm)} SeenHead γh s T M.

(** * Internal invariant, specific to this implementation. *)
Definition StackInv_no_exist s G γ γh T S : vProp :=
  ⌜ StackProps G T S ⌝
  (* Observations of stack push events' views *)
  ∗ StackViews γh s G.(Es) T
  (* Locs of the stack *)
  ∗ ∃ Vb, @{Vb} StackLocs s G.(Es) γh T S
  .

#[global] Instance StackInv_no_exist_timeless s G γ γh T S :
  Timeless (StackInv_no_exist s G γ γh T S) := _.

Definition StackBaseInv γ γh s G T : vProp :=
  ∃ S, StackInv_no_exist s G γ γh T S.

(* Only share the ghost state with the client.
  This carries some properties of T so that they are available without the
  internal invariant StackInternalInv *)
Definition StackInv' γg s q G γ T : vProp :=
  ⌜ ExtendedStackConsistent G ⌝ ∗ graph_master γg (q/2) G ∗
  ∃ (γh : gname), ⌜ EM_equiv T G.(Es) ∧ gmap_inj T ⌝ ∗
    meta s nroot (γ,γh) ∗
    (* LTM_master connects the logical enqueues and the event graph *)
    LTM_masterv γ (q/2)%Qp T.
Definition StackInv γg s q G : vProp :=
  ∃ γ T, StackInv' γg s q G γ T.

#[global] Instance StackInv_objective γg s q G :
  Objective (StackInv γg s q G) := _.

(* Our internal invariant keeps all the physical resources, as well as enough
  ghost resources (`StackInv`) to maintain agreement with the client. *)
Definition StackInternalInv γ γh γg s : vProp :=
  ∃ G T, StackInv' γg s 1%Qp G γ T ∗ StackBaseInv γ γh s G T.

#[global] Instance StackInternalInv_objective γ γh γg s :
  Objective (StackInternalInv γ γh γg s) := _.
#[global] Instance StackInternalInv_timeless γ γh γg s :
  Timeless (StackInternalInv γ γh γg s) := _.

(** * StackLocal assertion, specific to this implementation------------------- *)

Definition StackSeen γ γh s G M : vProp :=
  ∃ T,
    LTM_snapv γ T
    ∗ SeenHead γh s T M
    ∗ ⌜ EM_equiv T G.(Es) ⌝
  .

#[global] Instance StackSeen_persistent γ γh s G M :
  Persistent (StackSeen γ γh s G M) := _.

Definition StackLocalLite γg s G M : vProp :=
  graph_snap γg G M
  ∗ ∃ γ γh, StackSeen γ γh s G M
  ∗ meta s nroot (γ,γh).

#[global] Instance StackLocalLite_persistent γg s G M :
  Persistent (StackLocalLite γg s G M) := _.
#[global] Instance StackLocalLite_timeless γg s G M :
  Timeless (StackLocalLite γg s G M) := _.

Definition InternInv N γ γh γg s := inv (tstackN N s) (StackInternalInv γ γh γg s).

Definition StackLocal N γg s G M : vProp :=
  graph_snap γg G M
  ∗ ∃ γ γh, StackSeen γ γh s G M
  ∗ meta s nroot (γ,γh)
  ∗ InternInv N γ γh γg s.

#[global] Instance StackLocal_persistent N γg s G M :
  Persistent (StackLocal N γg s G M) := _.

(** * Ghost rules *)
Lemma LT_alloc T : ⊢ |==> ∃ γ, LTM_master γ 1 T.
Proof.
  apply own_alloc, auth_both_valid_discrete.
  split; [done|]. by apply to_agreeM_valid.
Qed.

Lemma LTM_master_snap_included γ q T T' :
  LTM_master γ q T -∗ LTM_snap γ T' -∗ ⌜T' ⊆ T⌝.
Proof.
  rewrite /LTM_master /LTM_auth.
  iIntros "[o1 ?] o2".
  iCombine "o1 o2" gives %(_ & INCL & _)%auth_both_dfrac_valid_discrete.
  iPureIntro. by move : INCL => /to_agreeM_included.
Qed.
Lemma LTM_master_ssnap_lookup γ q T n eid :
  LTM_master γ q T -∗ LTM_ssnap γ n eid -∗ ⌜T !! n = Some eid⌝.
Proof.
  iIntros "LTm VMs". by iDestruct (LTM_master_snap_included with "LTm VMs")
                        as %SUB%map_singleton_subseteq_l.
Qed.

Lemma LTM_auth_frac_op q1 q2 T :
  LTM_auth (q1 + q2) T ≡ LTM_auth q1 T ⋅ LTM_auth q2 T.
Proof.
  rewrite /LTM_auth.
  rewrite (comm _ (●{#q2} _)) -!assoc (assoc _ (◯ _)).
  by rewrite -core_id_dup (comm _ (◯ _)) assoc -auth_auth_dfrac_op.
Qed.

Global Instance LTM_auth_frac_is_op q q1 q2 T :
  IsOp q q1 q2 → IsOp' (LTM_auth q T) (LTM_auth q1 T) (LTM_auth q2 T).
Proof. rewrite /LTM_auth /IsOp' /IsOp => ->. by rewrite -LTM_auth_frac_op. Qed.

Lemma LTM_master_fork γ q T :
  LTM_master γ q T -∗ LTM_snap γ T.
Proof. by apply own_mono, auth_frag_included. Qed.

Lemma LTM_snap_sub γ T T' (Le: T ⊆ T') : LTM_snap γ T' ⊢ LTM_snap γ T.
Proof. by apply own_mono, auth_frag_mono, to_agreeM_included. Qed.

Lemma LTM_snap_union γ T T' :
  LTM_snap γ T -∗ LTM_snap γ T' -∗ LTM_snap γ (T ∪ T').
Proof.
  iIntros "L1 L2". iCombine "L1 L2" as "L".
  iDestruct (own_valid with "L") as %VAL. move : VAL => /auth_frag_valid VAL.
  by rewrite to_agreeM_op_valid.
Qed.
Lemma LTM_snap_union_eq γ T T' :
  LTM_snap γ T -∗ LTM_snap γ T' -∗ ⌜ T ∪ T' = T' ∪ T ⌝.
Proof.
  iIntros "L1 L2". iCombine "L1 L2" as "L".
  iDestruct (own_valid with "L") as %VAL. move : VAL => /auth_frag_valid VAL.
  iPureIntro. by apply to_agreeM_valid_union.
Qed.

Lemma LTM_master_agree γ q1 q2 T1 T2 :
  LTM_master γ q1 T1 -∗ LTM_master γ q2 T2 -∗ ⌜ T1 = T2 ⌝.
Proof.
  iIntros "T1 T2". rewrite /LTM_master /LTM_auth.
  iCombine "T1 T2" gives %VAL. iPureIntro.
  move : VAL.
  rewrite (comm _ (●{#q2} _)) -!assoc (assoc _ (◯ _)).
  rewrite -auth_frag_op (comm _ (◯ _)) assoc.
  by move => /cmra_valid_op_l
      /auth_auth_dfrac_op_valid [_ [/to_agreeM_agree ? ?]].
Qed.

(** Updates *)
Lemma LTM_update' γ T T' (SUB: T ⊆ T'):
  LTM_master γ 1 T ==∗ LTM_master γ 1 T'.
Proof. by apply own_update, auth_update, to_agreeM_local_update. Qed.
Lemma LTM_update γ T T' (SUB: T ⊆ T'):
  LTM_master γ 1 T ==∗ LTM_master γ 1 T' ∗ LTM_snap γ T'.
Proof.
  iIntros "oT". iMod (LTM_update' with "oT") as "oT"; [done|].
  iIntros "!>". iDestruct (LTM_master_fork with "oT") as "#$". by iFrame.
Qed.

Lemma LTM_update_insert γ T n eid (FR: n ∉ dom T):
  LTM_master γ 1 T ==∗ LTM_master γ 1 (<[n := eid]>T) ∗ LTM_ssnap γ n eid.
Proof.
  iIntros "LTm".
  iMod (LTM_update with "LTm") as "[$ Snap]".
  { by apply insert_subseteq, (not_elem_of_dom (D:= gset _)). }
  iIntros "!>". iApply (LTM_snap_sub with "Snap").
  by apply insert_mono, gmap_subseteq_empty.
Qed.

(** * Properties of assertions *)
Lemma SeenHead_mono E E' T T' M γh s :
  EM_equiv T E → EM_equiv T' E' →
  gmap_inj T' →
  set_in_bound M E →
  E ⊑ E' → T ⊆ T' →
  SeenHead γh s T M ⊢ SeenHead γh s T' M.
Proof.
  intros ET ET' INJ Sub SubE SubT. iDestruct 1 as (ζ) "[sH %SP]".
  iExists ζ. iFrame. iPureIntro.
  revert SP. by apply (SeenPushed_mono _ _ _ _ _ _ _ ET ET' INJ Sub SubE SubT).
Qed.

Lemma SeenHead_union γh s (E E1 E2 : event_list) T T1 T2 M1 M2 :
  gmap_inj T →
  EM_equiv T E →
  EM_equiv T1 E1 → EM_equiv T2 E2 →
  set_in_bound M1 E1 → set_in_bound M2 E2 →
  E1 ⊑ E → E2 ⊑ E → T1 ⊆ T → T2 ⊆ T →
  SeenHead γh s T1 M1 -∗ SeenHead γh s T2 M2 -∗ SeenHead γh s T (M1 ∪ M2).
Proof.
  intros INJ EM EM1 EM2 SM1 SM2 ????.
  iDestruct 1 as (ζ1) "[S1 %SP1]". iDestruct 1 as (ζ2) "[S2 %SP2]".
  iDestruct (AtomicSeen_union_equiv_1 with "S1 S2") as %EqU.
  iExists (ζ1 ∪ ζ2). iSplitL.
  - iApply (AtomicSeen_join with "S1 S2").
  - iPureIntro. apply SeenPushed_union_2; [done|..].
    + eapply (SeenPushed_mono _ _ T1); eauto.
    + eapply (SeenPushed_mono _ _ T2); eauto.
Qed.

Lemma StackInv'_map_snap_incl {γg s q G γ T T0} :
  StackInv' γg s q G γ T -∗
  LTM_snapv γ T0 -∗ ⌜ T0 ⊆ T ⌝.
Proof.
  iDestruct 1 as (SC) "(G & %γh & F & MT & LT)". iIntros "LTm".
  by iDestruct (LTM_master_snap_included with "LT LTm") as %?.
Qed.

Lemma StackInv'_graph_snap_incl {γg s q G γ T G' M'} :
  StackInv' γg s q G γ T -∗
  graph_snap γg G' M' -∗ ⌜ G' ⊑ G ⌝.
Proof.
  iDestruct 1 as (SC) "(G & ?)". iIntros "Gs".
  by iDestruct (graph_master_snap_included with "G Gs") as %?.
Qed.

Lemma StackInv'_snapshot {γg s q G γ T} :
  StackInv' γg s q G γ T -∗
  ⌜ ExtendedStackConsistent G ∧ eventgraph_consistent G ⌝ ∗
  LTM_snapv γ T ∗ graph_snap γg G ∅.
Proof.
  iDestruct 1 as (SC) "(G & %γh & F & MT & LT)".
  iDestruct (graph_master_consistent with "G") as %?.
  iDestruct (graph_master_snap with "G") as "$".
  iDestruct (LTM_master_fork with "LT") as "$".
  done.
Qed.

Lemma StackInv'_agree γg s q G γ T q' G' γ' T' :
  StackInv' γg s q G γ T -∗ StackInv' γg s q' G' γ' T' -∗
  ⌜ γ' = γ ∧ G' = G ∧ T' = T ⌝.
Proof.
  iDestruct 1 as (_) "(G & %γh & _ & MT & LT)".
  iDestruct 1 as (_) "(G' & %γh' & _ & MT' & LT')".
  iDestruct (meta_agree with "MT MT'") as %[<- <-]%pair_inj.
  iDestruct (graph_master_agree with "G G'") as %<-.
  iDestruct (LTM_master_agree with "LT LT'") as %<-.
  done.
Qed.

Instance StackInv'_fractional γg s G γ T :
  Fractional (λ q, StackInv' γg s q G γ T).
Proof.
  intros p q. iSplit.
  - iDestruct 1 as (SC) "(G & %γh & %EM & #MT & oT)".
    rewrite Qp.div_add_distr.
    iDestruct "G" as "[Gp Gq]". iDestruct "oT" as "[oTp oTq]".
    iSplitL "Gp oTp"; iFrame (SC) "∗"; iExists γh; iFrame (EM) "#".
  - iIntros "[S1 S2]".
    iDestruct "S1" as (SC) "(Gp & %γh & %EM & #MT & oT)".
    iDestruct "S2" as (_) "(Gq & %_ & _ & _ & oT')".
    iCombine "Gp Gq" as "G". iCombine "oT oT'" as "oT".
    rewrite -Qp.div_add_distr.
    iFrame (SC) "G". iExists γh. iFrame (EM) "MT oT".
Qed.

#[global] Instance StackInv_fractional γg s G :
  Fractional (λ q, StackInv γg s q G).
Proof.
  intros p q. iSplit.
  - iDestruct 1 as (γ T) "S".
    iDestruct (StackInv'_fractional with "S") as "[S1 S2]".
    iSplitL "S1"; iExists γ, T; iFrame.
  - iIntros "[S1 S2]".
    iDestruct "S1" as (γ T) "S1". iDestruct "S2" as (γ2 T2) "S2".
    iDestruct (StackInv'_agree with "S1 S2") as %(-> & _ & ->).
    iExists γ, T. iApply StackInv'_fractional. iFrame.
Qed.
#[global] Instance StackInv_asfractional γg s q G :
  AsFractional (StackInv γg s q G) (λ q, StackInv γg s q G) q.
Proof. constructor; [done|apply _]. Qed.

Lemma StackInv'_update γg s G γ T G' T' :
  eventgraph_consistent G' → ExtendedStackConsistent G' →
  G ⊑ G' → T ⊆ T' → EM_equiv T' G'.(Es) → gmap_inj T' →
  StackInv' γg s 1%Qp G γ T -∗ StackInv' γg s 1%Qp G γ T ==∗
  StackInv' γg s 1%Qp G' γ T' ∗ StackInv' γg s 1%Qp G' γ T'.
Proof.
  intros EGCs' SC' LeG' LeT' EM' INJ'.
  iDestruct 1 as (_) "(G1 & %γh & _ & #MT & oT1)".
  iDestruct 1 as (_) "(G2 & %_ & _ & _ & oT2)".
  iCombine "G1 G2" as "G". iCombine "oT1 oT2" as "oT".
  iMod (graph_master_update _ _ _ LeG' EGCs' with "G") as "([G1 G2] & _)".
  iMod (LTM_update _ _ _ LeT' with "oT") as "[[oT1 oT2] #LT']".
  iIntros "!>". iFrame (SC') "G1 G2". iSplitL "oT1"; iExists γh; by iFrame "#∗".
Qed.

Lemma StackInv_no_exist_StackProps s G γ γh T S :
  StackInv_no_exist s G γ γh T S ⊢ ⌜ StackProps G T S ⌝.
Proof. by iIntros "[$ _]". Qed.

Lemma StackInv_no_exist_StackLocs_access s G γ γh T S :
  StackInv_no_exist s G γ γh T S -∗
  ∃ Vb, @{Vb} StackLocs s G.(Es) γh T S
      ∗ (∀ Vb, @{Vb} StackLocs s G.(Es) γh T S -∗ StackInv_no_exist s G γ γh T S).
Proof.
  iIntros "(F & SV & SL)". iDestruct "SL" as (Vb) "SL".
  iExists Vb. iFrame "SL". iIntros (Vb') "SL". iFrame. by iExists Vb'.
Qed.

Lemma StackLocs_no_exist_head_immut_access s E γh T S t0 LVs Vh :
  StackLocs_no_exist s E γh T S t0 LVs Vh -∗
    let vh := (hd_error S) in
    let LVs' := (LVs ++ [(vh,Vh)]) in
    let ζh := toHeadHist t0 LVs' in
    s at↦{γh} ζh ∗
    ⌜ HeadValues T LVs' ∧ HeadUnpopped S ζh
      ∧ PushHistory E LVs' ∧ StackTopView LVs' Vh ⌝ ∗
    (s at↦{γh} toHeadHist t0 LVs' -∗ StackLocs_no_exist s E γh T S t0 LVs Vh).
Proof.
  iIntros "(H & #Hs & As & Is)". eauto with iFrame.
Qed.

Lemma all_slocs_node_next_access LVs n Vn :
  (Some n, Vn) ∈ LVs →
  all_slocs LVs -∗ all_slocs LVs ∗ ∃ q on, @{Vn} (n >> 0) ↦{q} #(oloc_to_lit on).
Proof.
  iIntros ([i Inn]%elem_of_list_lookup) "As".
  rewrite {1}/all_slocs (big_sepL_lookup_acc _ _ _ _ Inn).
  iDestruct "As" as "[Ns Close]".
  iDestruct "Ns" as (q on) "[N1 N2]". iSplitL "N1 Close".
  - iApply "Close". eauto with iFrame.
  - eauto with iFrame.
Qed.

Lemma all_slocs_node_access_prim t0 LVs t (l' : loc) Vb :
  fst <$> toHeadHist t0 LVs !! t = Some #l' →
  @{Vb} all_slocs LVs ⊢ ∃ (q' : Qp) (C' : cell), ▷ <subj> l' p↦{q'} C'.
Proof.
  intros ([] & Eq' & (? & on & Eq & Eq2)%toHeadHist_lookup_Some)%lookup_fmap_Some'.
  simpl in Eq'. subst v.
  assert (on = Some l') as ->.
  { clear -Eq. destruct on; by inversion Eq. } clear Eq.
  apply elem_of_list_lookup_2 in Eq2.
  rewrite (all_slocs_node_next_access _ _ _ Eq2).
  iIntros "[As En]". iDestruct "En" as (q' on) "En". iExists _.
  by rewrite view_at_view_at (shift_0 l') own_loc_na_view_at_own_loc_prim_subjectively.
Qed.

Lemma all_slocs_app LVs LVs' :
  all_slocs (LVs ++ LVs') ⊣⊢ all_slocs LVs ∗ all_slocs LVs'.
Proof. by rewrite /all_slocs -big_sepL_app. Qed.

Lemma in_slocs_node_access E T S i n :
  S !! i = Some n →
  in_slocs E T S -∗
    in_slocs E T S
    ∗ ∃ on q, ⌜next_nodes S !! i = Some on ⌝ ∧ (n >> next) ↦{q} #(oloc_to_lit on).
Proof.
  iIntros (Eqn) "Is".
  destruct (lookup_lt_is_Some_2 (next_nodes S) i) as [on Eqon].
  { move : Eqn. rewrite next_nodes_length. by apply lookup_lt_Some. }
  rewrite {1}/in_slocs (big_sepL2_lookup_acc _ _ _ _ _ _ Eqn Eqon).
  iDestruct "Is" as "[Ns Close]".
  iDestruct "Ns" as (v e EqT) "[Hn Hd]". iDestruct "Hn" as (q) "[Hn1 Hn2]".
  iSplitR "Hn2".
  - iApply "Close". iExists v, e. eauto with iFrame.
  - eauto with iFrame.
Qed.

Lemma in_slocs_optional_head_access E T S :
  in_slocs E T S -∗
    in_slocs E T S
    ∗ if (hd_error S) is Some n
      then ∃ on q, ⌜ next_nodes S !! 0%nat = Some on ⌝ ∧ (n >> next) ↦{q} #(oloc_to_lit on)
      else emp
    .
Proof.
  destruct S as [|n S]; [eauto|]. iIntros "Is".
  iDestruct (in_slocs_node_access _ _ _ 0%nat n with "Is") as "[$ $]". done.
Qed.

Lemma StackLocs_no_exist_node_next_access s E γh T S t0 LVs Vh n Vn:
  let vh := (hd_error S) in
  (Some n, Vn) ∈ (LVs ++ [(vh,Vh)]) →
  StackLocs_no_exist s E γh T S t0 LVs Vh -∗
    StackLocs_no_exist s E γh T S t0 LVs Vh
    ∗ ∃ q on, @{Vn} (n >> 0) ↦{q} #(oloc_to_lit on).
Proof.
  iIntros (vh Inn) "($ & $ & As & $)". by iApply all_slocs_node_next_access.
Qed.

Lemma in_sloc_map_mono E E' T n on :
  E ⊑ E' → in_sloc E T n on ⊢ in_sloc E' T n on.
Proof.
  intros Sub. iDestruct 1 as (v e EqT) "(?&?&SP)".
  iExists v, e. iFrame (EqT) "∗". iDestruct "SP" as (eV Eq) "[sV SE]".
  iExists eV. iFrame (Eq) "sV". by rewrite SeenEvent_mono.
Qed.
Lemma in_slocs_map_mono E E' T S :
  E ⊑ E' → in_slocs E T S ⊢ in_slocs E' T S.
Proof. intros Sub. apply big_sepL2_mono. intros. by apply in_sloc_map_mono. Qed.

Lemma in_sloc_map_mono' E T T' n on :
  T ⊆ T' → in_sloc E T n on ⊢ in_sloc E T' n on.
Proof.
  intros Sub. iDestruct 1 as (v e EqT) "(?&?&SP)".
  iExists v, e. assert (EqT' := lookup_weaken _ _ _ _ EqT Sub).
  iFrame (EqT') "∗".
Qed.
Lemma in_slocs_map_mono' E T T' S :
  T ⊆ T' → in_slocs E T S ⊢ in_slocs E T' S.
Proof. intros Sub. apply big_sepL2_mono. intros. by apply in_sloc_map_mono'. Qed.

Lemma in_slocs_mono E E' T T' S :
  E ⊑ E' → T ⊆ T' → in_slocs E T S ⊢ in_slocs E' T' S.
Proof.
  intros Sub1 Sub2. etrans; by [apply in_slocs_map_mono|apply in_slocs_map_mono'].
Qed.

Lemma in_sloc_cons E T n S :
  in_slocs E T (n :: S) ⊣⊢
  in_sloc E T n (hd_error S) ∗ in_slocs E T S .
Proof. rewrite /in_slocs next_nodes_cons big_sepL2_cons. by eauto. Qed.

Lemma in_slocs_NoDup E T S :
  in_slocs E T S ⊢ ⌜ NoDup S ⌝.
Proof.
  rewrite NoDup_alt.
  iIntros "Is" (i j n Eqi Eqj).
  case (decide (i = j)) => [?|NEq].
  { subst i. rewrite Eqi in Eqj. by inversion Eqj. }
  iExFalso.
  iDestruct (big_sepL2_length with "Is") as %EqL.
  destruct (lookup_lt_is_Some_2 (next_nodes S) i) as [o1 Eq1].
  { rewrite -EqL. by apply (lookup_lt_Some _ _ _ Eqi). }
  destruct (lookup_lt_is_Some_2 (next_nodes S) j) as [o2 Eq2].
  { rewrite -EqL. by apply (lookup_lt_Some _ _ _ Eqj). }
  iDestruct (big_sepL2_delete' _ _ _ _ _ _ Eqi Eq1 with "Is") as "[Li Is]".
  iDestruct (big_sepL2_delete' _ _ _ _ _ _ Eqj Eq2 with "Is") as "[Lj _]".
  iSpecialize ("Lj" with "[%//]").
  iDestruct "Li" as (???) "(? & H1 & ?)".
  iDestruct "Lj" as (???) "(? & H2 & ?)".
  iDestruct (own_loc_na_combine with "H1 H2") as "H".
  by iDestruct (own_loc_na_frac_1 with "H") as %?.
Qed.

Lemma StackSeen_union γ γh s G M M' q T :
  EM_equiv T G.(Es) →
  gmap_inj T →
  set_in_bound M G.(Es) → set_in_bound M' G.(Es) →
  LTM_masterv γ q T -∗
  StackSeen γ γh s G M -∗ StackSeen γ γh s G M' -∗ StackSeen γ γh s G (M ∪ M').
Proof.
  intros EM INJ SM SM'. iIntros "oT".
  iDestruct 1 as (T1) "(LT1 & SH1 & %EM1)".
  iDestruct 1 as (T2) "(LT2 & SH2 & %EM2)".
  iDestruct (LTM_master_fork with "oT") as "#LT".
  iDestruct (LTM_master_snap_included with "oT LT1") as %?.
  iDestruct (LTM_master_snap_included with "oT LT2") as %?.
  iExists T. iFrame (EM) "LT".
  iApply (SeenHead_union with "SH1 SH2"); eauto.
Qed.

End Interp.

Section proof.
Context `{!noprolG Σ, !tstackG Σ, !atomicG Σ}.
Local Existing Instances tstk_graphG tstk_stackG.

#[local] Notation iProp := (iProp Σ).
#[local] Notation vProp := (vProp Σ).

Lemma StackInv_ExtendedStackConsistent_instance :
  ∀ γg s q G, StackInv γg s q G ⊢ ⌜ ExtendedStackConsistent G ⌝.
Proof. intros. by iDestruct 1 as (???) "?". Qed.

Lemma StackInv_graph_master_acc_instance :
  ∀ γg s q G, StackInv γg s q G ⊢
    ∃ q', graph_master γg q' G ∗ (graph_master γg q' G -∗ StackInv γg s q G).
Proof.
  intros. iDestruct 1 as (γ T SC) "[? ?]". iExists _. iFrame.
  iIntros "G". iExists γ, T. by iFrame.
Qed.

Lemma StackInv_graph_snap_instance :
  ∀ γg s q G G' M',
    StackInv γg s q G -∗ graph_snap γg G' M' -∗ ⌜ G' ⊑ G ⌝.
Proof.
  intros. iDestruct 1 as (γ T SC) "[G ?]". iIntros "G'".
  by iDestruct (graph_master_snap_included with "G G'") as %?.
Qed.

Lemma StackInv_agree_instance :
  ∀ γg s q G q' G',
    StackInv γg s q G -∗ StackInv γg s q' G' -∗ ⌜ G' = G ⌝.
Proof.
  iDestruct 1 as (γ T _) "[G1 _]". iDestruct 1 as (γ' T' _) "[G2 _]".
  by iDestruct (graph_master_agree with "G1 G2") as %?.
Qed.

Lemma StackLocal_graph_snap_instance :
  ∀ N γg s G M, StackLocal N γg s G M ⊢ graph_snap γg G M.
Proof. by iIntros "* [$ _]". Qed.

Lemma StackLocalLite_graph_snap_instance :
  ∀ γg s G M, StackLocalLite γg s G M ⊢ graph_snap γg G M.
Proof. by iIntros "* [$ _]". Qed.

Lemma StackLocalLite_from_instance :
  ∀ N γg s G M, StackLocal N γg s G M ⊢ StackLocalLite γg s G M.
Proof.
  iIntros "* [$ SL]". iDestruct "SL" as (γ γh) "(SS & MT & II)".
  iExists γ, γh. by iFrame.
Qed.

Lemma StackLocalLite_to_instance :
  ∀ N γg s G' M' G M,
    StackLocalLite γg s G M -∗ StackLocal N γg s G' M' -∗ StackLocal N γg s G M.
Proof.
  iIntros "* [$ SL] [_ SL']".
  iDestruct "SL" as (γ γh) "(SS & MT)".
  iDestruct "SL'" as (γ' γh') "(_ & MT' & II)".
  iDestruct (meta_agree with "MT MT'") as %[<- <-]%pair_inj.
  iExists γ, γh. by iFrame.
Qed.

Lemma StackLocalLite_upgrade_instance :
  ∀ γg s q G' G M,
    StackInv γg s q G' -∗ StackLocalLite γg s G M -∗ StackLocalLite γg s G' M.
Proof.
  iIntros "* SI [Gs SS]". iDestruct "SS" as (γ γh) "[SS #MT]".
  iDestruct "SI" as (γ' T' SC) "[SI ST]".
  iDestruct (graph_snap_upgrade with "SI Gs") as "#$".
  iExists γ, γh. iFrame "MT".

  iDestruct (graph_master_snap_included with "SI Gs") as %LeG.
  iDestruct "Gs" as "[_ Gs]". iDestruct (SeenLogview_closed with "Gs") as %SubM.

  iDestruct "ST" as (γh' [EM' INJ]) "[MT' oT]".
  iDestruct (meta_agree with "MT MT'") as %[<- <-]%pair_inj.
  iDestruct "SS" as (T) "(LT & SH & %EM)".
  iDestruct (LTM_master_snap_included with "oT LT") as %LeT.
  iDestruct (LTM_master_fork with "oT") as "#LT'".
  iExists T'. iFrame (EM') "LT'".
  iApply (SeenHead_mono with "SH"); eauto. by apply LeG.
Qed.

Lemma StackLocal_upgrade_instance :
  ∀ N γg s q G' G M,
    StackInv γg s q G' -∗ StackLocal N γg s G M -∗ StackLocal N γg s G' M.
Proof.
  iIntros "* SI #SL".
  iDestruct (StackLocalLite_from_instance with "SL") as "-#SLL".
  iDestruct (StackLocalLite_upgrade_instance with "SI SLL") as "SLL".
  iApply (StackLocalLite_to_instance with "SLL SL").
Qed.

Lemma StackLocal_union_instance :
  ∀ N γg s q G G1 G2 M1 M2,
    StackInv γg s q G -∗ StackLocal N γg s G1 M1 -∗ StackLocal N γg s G2 M2 -∗
    StackLocal N γg s G (M1 ∪ M2).
Proof.
  iIntros "* SI SL1 SL2".
  iDestruct (StackLocal_upgrade_instance with "SI SL1") as "{SL1} #[Gs1 SL1]".
  iDestruct (StackLocal_upgrade_instance with "SI SL2") as "{SL2} #[Gs2 SL2]".
  iDestruct (graph_snap_union with "Gs1 Gs2") as "$".
  iDestruct "SL1" as (γ γh) "(SS1 & MT1 & II)".
  iDestruct "SL2" as (γ2 γh2) "(SS2 & MT2 & _)".
  iDestruct (meta_agree with "MT1 MT2") as %[<- <-]%pair_inj.
  iExists γ, γh. iFrame "MT1 II".
  iDestruct "SI" as (γ2 T SC) "[G SL]".
  iDestruct "SL" as (γh' [EM INJ]) "[MT' oT]".
  iDestruct (meta_agree with "MT1 MT'") as %[<- <-]%pair_inj.
  iDestruct "Gs1" as "[_ Gs1]". iDestruct (SeenLogview_closed with "Gs1") as %?.
  iDestruct "Gs2" as "[_ Gs2]". iDestruct (SeenLogview_closed with "Gs2") as %?.
  by iApply (StackSeen_union with "oT SS1 SS2").
Qed.

Lemma new_stack_spec :
  new_stack_spec' new_tstack StackLocal StackInv.
Proof.
  iIntros (N tid Φ) "_ Post".
  wp_lam.
  (* allocate head *)
  wp_apply wp_new; [done..|].
  iIntros (s) "([H†|%] & Hs & Hms & _)"; [|done].
  wp_let.
  (* initialize head as null, and create protocol *)
  rewrite own_loc_na_vec_singleton.
  iApply wp_fupd.
  wp_write.
  iMod (AtomicPtsTo_CON_from_na with "Hs") as (γh t0 V0) "(sV0 & sN & sA)".

  (* allocate ghost graphs *)
  iMod (LT_alloc ∅) as (γ) "[LTm1 LTm2]".
  iDestruct (LTM_master_fork with "LTm1") as "#LTs".
  iMod graph_master_alloc_empty as (γg) "([GM1 GM2] & Gs)".

  have SC0 := ExtendedStackConsistent_empty.

  rewrite shift_0.
  iMod (meta_set _ _ (γ, γh) nroot with "Hms") as "#Hms"; [done|].

  have EM0 : EM_equiv ∅ []. { intros ?. naive_solver. }
  have INJ0 : gmap_inj (∅ : gmap loc event_id). { by intros ????. }

  iAssert (StackInv' γg s 1%Qp ∅ γ ∅ ∗ StackInv' γg s 1%Qp ∅ γ ∅)%I
    with "[LTm1 LTm2 GM1 GM2]" as "[SI1 SI2]".
  { iSplitL "LTm1 GM1"; rewrite /StackInv; iFrame (SC0) "∗";
      iExists γh; iFrame "Hms ∗"; by iPureIntro. }
  iMod (inv_alloc (tstackN N s) _ (StackInternalInv γ γh γg s)
          with "[sA SI1]") as "#I".
  { iNext. iExists ∅, ∅. iFrame "SI1".
    iExists []. iSplit. { iPureIntro. by constructor. }
    iDestruct (view_at_intro with "sA") as (V1) "[sV1 sA]".
    iSplitL "". { by iIntros (?????). }
    iExists V1. iExists t0, [], V0. simpl.
    iSplitL "sA"; last iSplitR; last iSplitL.
    - rewrite /toHeadHist /= insert_empty. by iFrame.
    - iPureIntro. split; last split; last split.
      + intros ?. by rewrite /= elem_of_list_singleton dom_empty.
      + by intros ?? ?%not_elem_of_nil.
      + done.
      + intros ?([]&?&?%elem_of_list_singleton)%elem_of_list_fmap. by simplify_eq.
    - by rewrite /all_slocs /=.
    - by rewrite /in_slocs /=. }

  iIntros "!>". iApply ("Post" $! γg).
  iSplitL "Gs sN"; last (by iExists γ, ∅; iFrame "SI2").
  iSplitL "Gs". { by iApply (graph_snap_empty with "Gs"). }
  iExists γ, γh. iFrame "I Hms". iExists ∅. iFrame "LTs". iSplitL "sN".
  - iExists _. by iFrame.
  - iPureIntro. intros ?; naive_solver.
Qed.

Lemma atom_try_push_internal :
  ∀ N (DISJ: N ## histN) s tid γg G0 M V (v : Z) (Posv: 0 < v) (n : loc),
  (* G1 is a snapshot of the graph, locally observed by M *)
  ⊒V -∗ StackLocal N γg s G0 M -∗
  (n >> next) ↦ - -∗ (n >> data) ↦ #v -∗
  (* PUBLIC PRE *)
  <<< ∀ G, ▷ StackInv γg s 1%Qp G >>>
    try_push_internal [ #s ; #n] @ tid; ↑N
  <<< ∃ (b : bool) V' G' (psId : event_id) ps Vpush M',
      (* PUBLIC POST *)
      ▷ StackInv γg s 1%Qp G' ∗
      ⊒V' ∗ @{V'} StackLocal N γg s G' M' ∗
      (⌜ (* FAIL_RACE case *)
        b = false ∧ G' = G ∧ M' = M ⌝ ∗
        (n >> next) ↦ - ∗ (n >> data) ↦ #v
      ∨
      ⌜ b = true ∧ G ⊑ G' ∧ M ⊑ M' ∧
        Vpush.(dv_in) = V ∧ Vpush.(dv_comm) = V' ∧
        (* Vpush ⊑ V' ∧ *) (* << only works if push is also acquiring *)
        (* ps is a new push event with which G' strictly extends G *)
        is_push ps v ∧
        psId = length G.(Es) ∧
        G'.(Es) = G.(Es) ++ [mkGraphEvent ps Vpush M'] ∧
        G'.(so) = G.(so) ∧ G'.(com) = G.(com) ∧
        psId ∈ M' ∧ psId ∉ M ⌝),
      (* RETURN VALUE AT COMMITTING POINT *)
      RET #b, emp >>>
  .
Proof.
  intros. iIntros "#sV #[Gs SS] Hn Hd" (Φ) "AU".
  iDestruct "SS" as (γ γh) "(SS & MTs & SII)".
  set E0 := G0.(Es).

  (* prepare to read head *)
  iDestruct "SS" as (T0) "(LT0 & (%ζh0 & sH0 & %SH0) & %ET0)".

  wp_lam. wp_bind (!ʳˡˣ _)%E.

  (* open the invariant *)
  iInv "SII" as (G1 T1) ">[SI [%S1 SBI]]" "Close".

  (* get Head *)
  iDestruct (StackInv_no_exist_StackLocs_access with "SBI") as (Vb) "[SL SLC]".
  iDestruct "SL" as (th0 LVs0 Vh0) "SL".
  rewrite StackLocs_no_exist_head_immut_access.
  iDestruct "SL" as "(H & [%HV0 %HUP0] & SIC)".
  (* ready to read *)
  wp_apply (AtomicSeen_relaxed_read with "[$sH0 $H $sV]"); first solve_ndisj.

  iIntros (th1 vh1 V0 V1 ζh0') "(Subζ & #sV1 & _ & #sH1 & H)".
  iDestruct "Subζ" as %([Subζh0 Subζh0'] & Eqth1 & _ & LeV').
  assert (Eqth1' := lookup_weaken _ _ _ _ Eqth1 Subζh0').

  iAssert (graph_snap γg G0 M) as "[_ PSV]". { by iFrame "Gs". }
  iDestruct (SeenLogview_closed with "PSV") as %SubM0.

  (* close the invariant *)
  iSpecialize ("SLC" $! (Vb ⊔ V1) with "[SIC H]").
  { iExists _, _, _. iApply (view_at_mono_2 with "SIC H"). solve_lat. }
  iMod ("Close" with "[SI SLC]") as "_".
  { iIntros "{#} !>". iExists _, _. iFrame "SI". iExists _. iFrame "SLC". }

  (* check what we just read *)
  assert (EqH := Eqth1').
  apply toHeadHist_lookup_Some in EqH as (_ & on' & -> & EqLVs0).

  (* set n's link to what we read from Head *)
  iIntros "!>". wp_let. wp_op.
  iDestruct "Hn" as (vn0) "Hn".
  wp_write.

  (* prepare to CAS on Head to push *)
  clear Vb.
  (* open the invariant *)
  iInv "SII" as (G2 T2) ">[SI [%S2 SBI]]" "Close".
  set E2 := G2.(Es).

  iDestruct (StackInv'_snapshot with "SI") as ([SC2 EGCs2]) "#[LT2 GS2]".
  iDestruct (StackInv'_graph_snap_incl with "SI Gs") as %LeG2.
  have LeE2 : E0 ⊑ E2 by apply LeG2.
  iDestruct (StackInv'_map_snap_incl with "SI LT0") as %LeT02.

  iDestruct "SBI" as "(%SP2 & #SV & SL)".
  iDestruct "SL" as (Vb t02 LVs2 Vh2) "(H & H2 & As & Is)".
  iDestruct "H2" as %(HV2 & HUP2 & PH2 & STV2).

  iCombine "Hn Hd" as "Hnd". iCombine "Hnd PSV" as "CHUNK".
  iDestruct (view_at_intro_incl with "CHUNK sV1")
    as (V1') "(#sV1' & %LeV1 & [Hnd #PSVA])".

  iDestruct (view_at_elim with "sV1 sH1") as "sH1'".
  iDestruct (AtomicPtsTo_AtomicSeen_latest_1 with "H sH1'") as %Subζ0.

  (* CAS with possible pointer comparison *)
  wp_apply (AtomicSeen_CON_CAS _ _ _ _ _ _ _ (oloc_to_lit on') #n _ ∅
              with "[$sH1' $H $sV1']"); [done|done|done|solve_ndisj|..].
  { intros t' v' NE. rewrite lookup_fmap_Some'.
    intros ([] & <- & ?). by eapply toHeadHist_lookup_Some_is_comparable_nullable_loc. }
  { done. }

  iIntros (b t' v' Vr V2 ζ2 ζn) "(F & #sV2 & #sH2 & H & CASE)".
  iDestruct "F" as %([Subζh02 Subζ2] & Eqt' & MAXt' & LeV1').

  iDestruct "CASE" as "[[F sVr]|[F sVw]]".
  { (* fail CAS *)
    iDestruct "F" as %(-> & NEq & ->).
    iMod "AU" as (G2') "[>SI' HClose]".
    iDestruct "SI'" as (γ' T2') "SI'".
    iDestruct (StackInv'_agree with "SI SI'") as %(-> & -> & ->).

    rewrite bi.and_elim_r.
    have bLeVV : bool_decide (V ⊑ V) by eapply bool_decide_unpack; eauto.
    set Vps := mkDView V V V bLeVV.

    iAssert (@{V2} StackLocal N γg s G2 M)%I as "SL'".
    { iSplit.
      - (* TODO variant of graph_snap_mono *)
        iDestruct "GS2" as "[$ _]". iApply (view_at_mono with "PSVA"); [done|].
        by apply SeenLogview_map_mono.
      - iExists γ, γh. iFrame "MTs SII". iExists T2. iFrame "LT2". iSplitL.
        + iExists _. iFrame "sH2". iPureIntro.
          apply (SeenPushed_mono E0 E2 T0 T2 ζh0 _ _ ET0);
            [apply SP2|apply SP2|done..|by etrans|done].
        + iPureIntro. by apply SP2. }

    iMod ("HClose" $! false V2 G2 dummy_eid dummy_sevt Vps M
          with "[SI' $sV2 Hnd SL']") as "HΦ".
    { (* Public Post *)
      iSplitL "SI'". { iExists γ, T2. by iFrame. }
      iFrame "SL'". iLeft. iSplit; [done|].
      iDestruct (view_at_elim with "sV1' Hnd") as "[Hn $]". iExists _. iFrame "Hn". }

    iMod ("Close" with "[SI H As Is]") as "_".
    { iNext. iExists G2, T2. iFrame "SI". iExists S2. iFrame "SV".
      iSplit; [done|]. iExists (Vb ⊔ V2), _, LVs2, Vh2. iFrame. by iPureIntro. }

    iIntros "!>". by iApply "HΦ". }

  (* successful CAS *)
  iDestruct "F" as %[-> ->].
  iDestruct "sVw" as (Vw (FRt & Eqζn & Eqt'' & LeVr & SLeVr & NLeVr & NEqV1' & LeV1w))
                     "#[sHVw sVw]".
  iDestruct "Hnd" as "[Hn Hd]".

  assert (Eqt2 := lookup_weaken _ _ _ _ Eqt' Subζ2).
  rewrite Eqζn lookup_insert_ne in Eqt2; last by (clear; lia).
  apply toHeadHist_lookup_Some in Eqt2 as (Let02 & on & Eqon & Eqn2).
  assert (on = on') as ->.
  { clear -Eqon. by destruct on, on'; inversion Eqon. } clear Eqon.

  assert (EqL: (Pos.to_nat t' - Pos.to_nat t02)%nat = length LVs2).
  { assert (LtL := lookup_lt_Some _ _ _ Eqn2).
    clear -FRt Let02 LtL.
    apply toHeadHist_lookup_None in FRt as [?|Let']; first (exfalso; lia).
    apply : (anti_symm (le)).
    - clear -LtL. rewrite app_length /= in LtL. lia.
    - clear LtL. rewrite app_length /= /pos_add_nat in Let'; lia. }
  rewrite EqL in Eqn2.
  assert (Vh2 = Vr ∧ on' = hd_error S2) as [-> ->].
  { clear -Eqn2. apply lookup_last_Some_2 in Eqn2. by inversion Eqn2. }

  have SubM: set_in_bound M E2.
  { clear -SubM0 LeE2. by eapply set_in_bound_mono. }

  set V' := Vw.
  have LeVV2 : V ⊑ V2. { clear- LeV' LeV1 LeV1'. solve_lat. }
  have bLeVV2 : bool_decide (V ⊑ V2) by eapply bool_decide_unpack; eauto.
  set Vps := mkDView V V2 Vw bLeVV2.

  assert (GIP:= graph_insert_props_base _ (Push v) _ Vps SubM EGCs2).
  destruct GIP as [psId M' egV' G' LeG' SubM' SUB' Inps NInps EGCs'].
  set T' := <[n := psId]> T2.
  set S' := n :: S2.
  have LeG0 : G0 ⊑ G' by etrans.

  iAssert (⌜ n ∉ dom T2 ⌝)%I with "[As Hn]" as %FRnT.
  { iIntros "{#}" (InT2). destruct (HV2 n) as [_ In2].
    specialize (In2 InT2). apply elem_of_list_fmap in In2 as ([n' Vn] & Eq & In2).
    simpl in Eq. subst n'.
    rewrite (all_slocs_node_next_access _ _ _ In2). clear.
    iDestruct "As" as "[_ Hn']". iDestruct "Hn'" as (q' on) "Hn'".
    iDestruct (view_at_intro with "Hn") as (V') "[_ Hn]".
    rewrite !view_at_view_at.
    iAssert (@{V1' ⊔ Vn} (n >> 0) ↦{q'+1} #(oloc_to_lit on))%I with "[-]" as "Hn".
    { rewrite -own_loc_na_combine'. by iFrame. }
    rewrite own_loc_na_frac_1. by iDestruct "Hn" as %VAL%frac_valid%Qp.not_add_le_r. }
  have LeT2: T2 ⊆ T'.
  { by apply insert_subseteq, (not_elem_of_dom (D:=gset _)). }
  have NInCD: psId ∉ codom T2.
  { rewrite codom_correct => [[n' InT]].
    (* TODO: clean up things like this *)
    destruct (stk_em _ _ _ SP2 psId) as [[v' Eqv] _]. { by exists n'. }
    move : Eqv => /list_lookup_fmap_inv' [? [?]]. intros ?%lookup_lt_Some. lia. }

  have SC' : ExtendedStackConsistent G'.
  { destruct SC2 as [SC2DPP SC2DPPO SC2DPO
                    [SC2NZ SC2MA SC2FN SC2EM SC2NE SC2SO SC2LIFO SC2MO] SC2LIFOb].
    constructor; [| | |constructor|..]; [| | | | |done| | |done| | |].
    - clear -SC2DPP LeV1w. by apply graph_insert_event_is_releasing.
    - clear -PH2 SC2DPPO SC2DPP STV2 NLeVr.
      intros e1 e2 eV1 eV2 v1 v2
             [Eq1|[-> <-]]%lookup_app_1 [Eq2|[-> <-]]%lookup_app_1.
      + by apply SC2DPPO.
      + intros Eqv1. inversion 1. subst v2. intros ?.
        destruct (PH2 _ _ _ Eq1 Eqv1) as [n' Inn'].
        have LeVrn': eV1.(ge_view).(dv_wrt) ⊑ Vr.
        { clear -Inn' STV2. apply STV2, elem_of_list_fmap.
          eexists. split; [|exact Inn']. done. }
        specialize (SC2DPP _ _ Eq1 (ltac:(by eexists))).
        clear -SC2DPP LeVrn' NLeVr. intros LeV2. apply NLeVr. solve_lat.
      + intros _ _ ? _. apply lookup_lt_Some in Eq2. lia.
      + intros _ _ ? _. lia.
    - clear -SC2DPO. apply graph_insert_event_is_acquiring; [done|].
      clear; simpl; intros []; congruence.
    - apply stack_positive_value_insert; [|exact SC2NZ].
      clear -Posv. simpl => v'. inversion 1; by subst v'.
    - apply stack_matches_value_insert, SC2MA.
    - apply stack_unmatched_pop_empty_insert; [|exact SC2EM].
      clear; left; by eexists.
    - apply stack_empty_unmatched_push_insert; [done| |exact SC2NE].
      simpl; clear; by inversion 1.
    - apply stack_LIFO_insert, SC2LIFO.
    - clear -SC2MO SUB'. by apply graph_insert_xo_eco.
    - apply stack_LIFO_empty_insert; [done|exact SC2LIFOb]. }

  assert (NInn: n ∉ S2).
  { intros Inn. by apply FRnT, (stk_sub _ _ _ SP2), elem_of_list_to_set. }
  have SP' : StackProps G' T' S'.
  { destruct SP2 as [SP2SB SP2ET SP2INJ SP2PP SP2ORD1 SP2ORD2].
    constructor.
    - clear -SP2SB. rewrite list_to_set_cons dom_insert. set_solver.
    - intros e. case (decide (e = psId)) => [->|NEq].
      + rewrite lookup_app_1_eq /=. split; [clear; naive_solver|].
        intros _. exists n. by rewrite lookup_insert.
      + rewrite lookup_app_1_ne; [|done]. rewrite -SP2ET. clear -NEq FRnT.
        split; intros [n' Eqn']; exists n'.
        * assert (Eqn:= Eqn'). rewrite lookup_insert_ne in Eqn'; [done|].
          intros <-. rewrite lookup_insert in Eqn. by inversion Eqn.
        * rewrite lookup_insert_ne; [done|].
          intros <-. apply FRnT. move : Eqn'. by apply elem_of_dom_2.
    - intros n1 n2 e.
      case (decide (n1 = n)) => [->|?];
        [rewrite lookup_insert|rewrite lookup_insert_ne; last done];
        (case (decide (n2 = n)) => [->|?];
          [rewrite lookup_insert|rewrite lookup_insert_ne; last done]);
        [done|..|apply SP2INJ].
      + inversion 1. subst e. intros InT. exfalso. apply NInCD, codom_correct. by exists n2.
      + intros InT. inversion 1. subst e. exfalso. apply NInCD, codom_correct. by exists n1.
    - intros n0 e0.
      rewrite /popped_nodes list_to_set_cons dom_insert_L difference_union_distr_l_L.
      rewrite subseteq_empty_difference_L; [|set_solver-].
      rewrite left_id_L difference_union_distr_r_L difference_disjoint_L;
        [|clear -FRnT; set_solver].
      rewrite comm_L subseteq_intersection_1_L; [|set_solver-].
      case (decide (n0 = n)) => [->|NEqn].
      + rewrite lookup_insert. inversion 1. subst e0. split.
        * clear -FRnT. by intros []%elem_of_difference.
        * intros ([u o] & Eq & Ine%elem_of_elements)%elem_of_list_fmap.
          exfalso. simpl in Eq. subst u. clear -Ine.
          destruct (gcons_so_included G2 _ Ine). simpl in *. lia.
      + rewrite lookup_insert_ne; [|done]. by apply SP2PP.
    - clear -SP2ORD1 SP2ET NInn EGCs2 FRnT.
      intros n1 n2 e1 e2 (i1 & i2 & Eqi1 & Eqi2 & Le12).
      destruct i1 as [|i1].
      { simpl in Eqi1. inversion Eqi1. subst n1. rewrite lookup_insert.
        inversion 1. subst e1. case (decide (n2 = n)) => [->|?].
        - rewrite lookup_insert. by inversion 1.
        - rewrite lookup_insert_ne; [|done]. intros InT2.
          apply Nat.lt_le_incl, lookup_lt_is_Some.
          destruct (SP2ET e2) as [[? [? [_ ?]]%list_lookup_fmap_inv'] _]; by eexists. }
      rewrite (lookup_app_r [_]) in Eqi1; [|clear; simpl; lia].
      rewrite (lookup_app_r [_]) in Eqi2; [|clear -Le12; simpl; lia].
      rewrite lookup_insert_ne; last first.
      { intros <-. apply NInn. move : Eqi1. by apply elem_of_list_lookup_2. }
      rewrite lookup_insert_ne; last first.
      { intros <-. apply NInn. move : Eqi2. by apply elem_of_list_lookup_2. }
      apply SP2ORD1. do 2 eexists. do 2 (split; [done|]). clear -Le12. simpl. lia.
    - intros n0 e0 [->|InS2]%elem_of_cons.
      + rewrite lookup_insert. inversion 1. subst e0.
        move => ?? /(gcons_so_included G2) [/=??]. left; lia.
      + rewrite lookup_insert_ne; [by apply SP2ORD2|]. intros <-. by apply NInn.
  }

  set E' := G'.(Es).
  have LeE' : E2 ⊑ E' by apply LeG'.

  iAssert (@{Vps.(dv_comm)} SeenLogview E' M')%I with "[]" as "#PSV'".
  { rewrite -SeenLogview_insert'. iSplitL; [|done].
    erewrite SeenLogview_map_mono; [iFrame "PSVA"|done..]. }

  iAssert (@{V'} SeenEvent E' psId egV')%I with "[]" as "-#SYE".
  { iSplit; last iSplit; [..|by iPureIntro].
    - iPureIntro. by rewrite lookup_app_1_eq.
    - rewrite /= view_at_view_at. iApply "PSV'". }

  iCombine "Hn Hd" as "Hnd".
  set LVs' := (LVs2 ++ [(hd_error S2,Vr)]) ++ [(Some n, Vw)].
  iAssert (@{Vb ⊔ V2} (all_slocs LVs' ∗ @{Vw} in_slocs E' T' S'))%I
    with "[As Is Hnd SYE]" as "[As Is]".
  { iDestruct (view_at_mono_2 _ Vw with "Hnd") as "[[Hn1 Hn2] Hd] {#}";
      [solve_lat|]. iSplitL "As Hn1".
    - rewrite(all_slocs_app (_ ++ _)). iSplitL "As"; [by iFrame "As"|].
      rewrite /all_slocs /=. iSplitL; [|done]. iExists _, (hd_error S2).
      rewrite view_at_view_at /=. iFrame "Hn1".
    - rewrite 2!view_at_view_at (in_sloc_cons E'). iSplitR "Is".
      + iExists v, psId. rewrite /= /in_sloc.
        iSplit. { iPureIntro. by rewrite lookup_insert. }
        iSplitL "Hn2". { iExists _. by iFrame "Hn2". }
        iFrame "Hd". iExists egV'. iSplit; [by iPureIntro|]. by iFrame.
      + rewrite (in_slocs_mono E2 E' T2 T'); [|done..]. by iFrame. }

  have SH' : SeenPushed T' ζ2 M'.
  { intros e0 n0. rewrite elem_of_union elem_of_singleton.
    intros [?|Ine].
    - subst e0. clear -NInCD Eqt''. case (decide (n0 = n)) => [->|?].
      + intros _. exists (t' + 1)%positive. by rewrite Eqt''.
      + rewrite lookup_insert_ne; [|done]. clear -NInCD. intros EqT2.
        exfalso. apply NInCD, codom_correct. by eexists.
    - intros Eqn0. assert (Eqn0' := Eqn0).
      rewrite lookup_insert_ne in Eqn0'.
      + revert Ine Eqn0'.
        apply (SeenPushed_mono E0 E2 T0 T2 ζh0 ζ2 M);
          [done|apply SP2|apply SP2|done..|by etrans|done].
      + clear -Ine Eqn0 NInps. intros <-. rewrite lookup_insert in Eqn0.
        inversion Eqn0. by subst e0. }

  iMod "AU" as (G2') "[>SI' HClose]".
  iDestruct "SI'" as (γ' T2') "SI'".
  iDestruct (StackInv'_agree with "SI SI'") as %(-> & -> & ->).

  iMod (StackInv'_update _ _ _ _ _ G' T' EGCs' SC' LeG' LeT2 with "SI SI'")
    as "[SI SI']"; [apply SP'..|].
  iDestruct (StackInv'_snapshot with "SI") as (_) "#[LT' [Gs' _]]".

  have LeVV' : V ⊑ V'. { clear -LeVV2 LeV1w. rewrite /V'. by solve_lat. }

  iAssert (@{V2} StackLocal N γg s G' M')%I with "[]" as "-#SL'".
  { iFrame "Gs' PSV'". iExists γ, γh. iFrame "MTs SII". iExists T'. iFrame "LT'".
    iSplitL; [|by iPureIntro; apply SP']. iExists ζ2. iFrame "sH2". by iPureIntro. }

  rewrite bi.and_elim_r.
  iMod ("HClose" $! true V2 G' psId (Push v) Vps M' with "[SI' $sV2 $SL']") as "HΦ".
  { iSplitL "SI'". - by iExists γ, T'. - by iRight. }

  (* re-establish the invariant *)
  iMod ("Close" with "[-HΦ]") as "_".
  { iNext. iExists G', T'. iFrame "SI". iExists S'. iSplit; [done|]. iSplitL "".
    - iIntros (e' v' Ve lVe [Eq1|[_ Eq1]]%lookup_app_1).
      + iSpecialize ("SV" with "[%//]"). iApply (view_at_mono with "SV"); [done|].
        apply (SeenHead_mono E2 E'); [apply SP2|apply SP'|apply SP'|..|done|done].
        by apply (egcons_logview_closed _ EGCs2 _ _ Eq1).
      + inversion Eq1; clear Eq1; subst v' Ve lVe.
        iExists ζ2. iSplitL ""; [iFrame "sH2"|by iPureIntro].
    - iExists (Vb ⊔ V2).
      assert (Eqζh2' : toHeadHist t02 LVs' =
              <[(t' + 1)%positive:=(#n, Vw)]> (toHeadHist t02 (LVs2 ++ [(hd_error S2, Vr)]))).
      { symmetry. apply (toHeadHist_insert _ _ _ (Some n)).
        - clear -Let02 EqL. rewrite app_length /=. lia.
        - clear. rewrite app_length /=. lia. }
      rewrite Eqζn -Eqζh2'. iExists t02, _, Vw. iSplitL "H". { iFrame "H". }
      iSplitR; last first. { iSplitL "As"; [by iFrame "As"|by iFrame "Is"]. }
      (* show that n is the latest write *)
      iPureIntro. split; last split; last split.
      + intros n0. rewrite dom_insert fmap_app elem_of_app HV2 /=
                      elem_of_list_singleton elem_of_union elem_of_singleton.
        clear. naive_solver.
      + intros t0 n0 In0%elem_of_cons. rewrite /= -/LVs' Eqζh2'.
        case (decide (t0 = (t' + 1)%positive)) => [->|Neqt0].
        * rewrite lookup_insert /=. inversion 1. subst n0.
          intros t1 [Ltt1|<-]%Pos.lt_eq_cases; last first.
          { rewrite lookup_insert /=. by inversion 1. }
          rewrite lookup_insert_ne; [|clear -Ltt1; lia].
          rewrite lookup_fmap_Some' => [[[n1 Vn1] [Eq Eqt1]]].
          simpl in Eq. subst n1.
          apply toHeadHist_lookup_Some in Eqt1 as (Let1' & on & Eq & Eqt1%lookup_lt_Some).
          rewrite app_length /= -EqL in Eqt1. clear - Eqt1 Ltt1 Let1' Let02. lia.
        * rewrite lookup_insert_ne; [|done]. intros Int0.
          intros t1 Let1. case (decide (t1 = (t' + 1))%positive) => [->|?].
          { rewrite lookup_insert /=. by inversion 1. }
          rewrite lookup_insert_ne; [|done].
          revert Let1. apply (HUP2 t0 n0); [|done]. destruct In0 as [->|]; [|done].
          exfalso. apply FRnT, HV2, elem_of_list_fmap.
          apply lookup_fmap_Some' in Int0 as ([vn1 Vn1] & Eq1 & Eqt0).
          simpl in Eq1; subst vn1.
          apply toHeadHist_lookup_Some in Eqt0 as (_ & on & Eqn & Eqtn).
          assert (on = Some n) as ->. { clear -Eqn. by destruct on; inversion Eqn. }
          exists (Some n, Vn1). split; [done|].
          move : Eqtn. by apply elem_of_list_lookup_2.
      + clear -PH2. intros e1 eV1 v1 [Eqe1|[-> <-]]%lookup_app_1 Eqv1.
        * destruct (PH2 _ _ _ Eqe1 Eqv1) as [n1 Inn1].
          exists n1. rewrite elem_of_app. by left.
        * exists n. simpl. rewrite elem_of_app elem_of_list_singleton. by right.
      + clear -STV2 LeVr.
        intros V. rewrite fmap_app elem_of_app /= elem_of_list_singleton.
        intros [?%STV2| ->];[solve_lat|done].
  }

  iIntros "!>". by iApply "HΦ".
Qed.

(* TODO: this proof is abstract w.r.t. the details of try_push_internal *)
Lemma atom_try_push :
  try_push_spec' try_push StackLocal StackInv.
Proof.
  intros N DISJ s tid γg G0 M V v Posv. iIntros "#sV #Gs" (Φ) "AU".

  wp_lam.
  (* allocate node *)
  wp_apply wp_new; [done..|].
  iIntros (n) "([H†|%] & Hn & Hmn)"; [|done].

  (* initialize n's data as v *)
  rewrite own_loc_na_vec_cons own_loc_na_vec_singleton.
  iDestruct "Hn" as "[Hn Hd]".
  wp_let. wp_op. wp_write.

  awp_apply (atom_try_push_internal with "sV Gs [Hn] Hd"); [eauto..|].
  { rewrite shift_0. by iExists _. }

  iApply (aacc_aupd with "AU"); [done|].
  iIntros (G) "QI".
  iAaccIntro with "QI"; first by eauto with iFrame.
  iIntros (b V' G' psId ps Vps M') "(QI & sV' & SL & CASE) !>". iRight.
  iExists b, V', G', psId, ps, Vps, M'. iFrame "QI sV' SL".
  iDestruct "CASE" as "[(F & Hn & Hd)|F]".
  - iDestruct "F" as %(-> & -> & ->). iSplit. { by iLeft. }
    iIntros "HΦ !> _". wp_if.
    (* cleaning up *)
    iDestruct "Hn" as (v') "Hn".
    wp_apply (wp_delete _ tid 2 _ [ v'; #v] with "[H† Hn Hd]"); [done|done|..].
    { rewrite own_loc_na_vec_cons own_loc_na_vec_singleton.
      rewrite shift_0. iFrame "Hn Hd". iLeft. by iFrame. }
    iIntros "_". wp_seq. by iApply "HΦ".
  - iSplit. { by iRight. } iDestruct "F" as %[-> F].
    iIntros "HΦ !> _". wp_if. by iApply "HΦ".
Qed.

(* TODO: this proof is abstract w.r.t. the details of try_push_internal *)
Lemma atom_push_internal :
  ∀ N (DISJ: N ## histN) s tid γg G0 M V (v : Z) (Posv: 0 < v) (n : loc),
  (* G1 is a snapshot of the graph, locally observed by M *)
  ⊒V -∗ StackLocal N γg s G0 M -∗
  (n >> next) ↦ - -∗ (n >> data) ↦ #v -∗
  (* PUBLIC PRE *)
  <<< ∀ G, ▷ StackInv γg s 1%Qp G >>>
    push_internal [ #s ; #n] @ tid; ↑N
  <<< ∃ V' G' (psId : event_id) ps Vpush M',
      (* PUBLIC POST *)
      ▷ StackInv γg s 1%Qp G' ∗
      ⊒V' ∗ @{V'} StackLocal N γg s G' M' ∗
      ⌜ G ⊑ G' ∧ M ⊑ M' ∧
        Vpush.(dv_in) = V ∧ Vpush.(dv_comm) = V' ∧
        (* Vpush ⊑ V' ∧ *) (* << only works if push is also acquiring *)
        (* ps is a new push event with which G' strictly extends G *)
        is_push ps v ∧
        psId = length G.(Es) ∧
        G'.(Es) = G.(Es) ++ [mkGraphEvent ps Vpush M'] ∧
        G'.(so) = G.(so) ∧ G'.(com) = G.(com) ∧
        psId ∈ M' ∧ psId ∉ M ⌝,
      (* RETURN VALUE AT COMMITTING POINT *)
      RET #☠, emp >>>
  .
Proof.
  intros. iIntros "#sV #Gs Hn Hd" (Φ) "AU".
  iLöb as "IH".

  wp_rec.
  awp_apply (atom_try_push_internal with "sV Gs Hn Hd"); [done..|].
  iApply (aacc_aupd with "AU"); [done|].
  iIntros (G) "QI".
  iAaccIntro with "QI"; first by eauto with iFrame.
  iIntros (b V' G' psId ps Vps M') "(QI & sV' & SL & CASE) !>".
  iDestruct "CASE" as "[(F & Hn & Hd)|F]".
  - iDestruct "F" as %(-> & -> & ->).
    iLeft. iFrame "QI". iIntros "AU !> _".
    wp_if. by iApply ("IH" with "Hn Hd AU").
  - iRight.
    iExists V', G', psId, ps, Vps, M'.
    iFrame "QI sV' SL". iDestruct "F" as %[-> F]. iSplit; [done|].
    iIntros "HΦ !> _". wp_if. by iApply "HΦ".
Qed.

Lemma atom_push :
  push_spec' push StackLocal StackInv.
Proof.
  intros N DISJ s tid γg G0 M V v Posv. iIntros "sV Gs" (Φ) "AU".
  wp_lam.
  (* allocate node *)
  wp_apply wp_new; [done..|].
  iIntros (n) "([H†|%] & Hn & Hmn)"; [|done].

  (* initialize n's data as v *)
  rewrite own_loc_na_vec_cons own_loc_na_vec_singleton.
  iDestruct "Hn" as "[Hn Hd]".
  wp_let. wp_op. wp_write.

  wp_apply (atom_push_internal with "sV Gs [Hn] Hd AU"); [eauto..|].
  rewrite shift_0. by iExists _.
Qed.

Lemma atom_try_pop :
  try_pop_spec' try_pop StackLocal StackInv.
Proof.
  intros N DISJ s tid γg G0 M V. iIntros "#sV #[Gs SS]" (Φ) "AU".
  iDestruct "SS" as (γ γh) "(SS & MTs & SII)".
  iDestruct "SS" as (T0) "(LTs & (%ζh0 & sH0 & %SH0) & %ET0)".
  set E0 := G0.(Es).

  wp_lam. wp_bind (!ᵃᶜ _)%E.

  (* open the invariant *)
  iInv "SII" as (G1 T1) ">[SI [%S1 SBI]]" "Close".
  (* get a snapshot *)
  iDestruct (StackInv'_map_snap_incl with "SI LTs") as %LeT0.
  iDestruct (StackInv'_graph_snap_incl with "SI Gs") as %LeG0.
  iDestruct (StackInv'_snapshot with "SI") as ([SC1 EGCs1]) "#[LT1 GS0]".
  iDestruct (StackInv_no_exist_StackProps with "SBI") as %SP1.
  set E1 := G1.(Es).
  have LeE0 : E0 ⊑ E1 by apply LeG0.

  (* get Head *)
  iDestruct (StackInv_no_exist_StackLocs_access with "SBI") as (Vb) "[SL SLC]".
  iDestruct "SL" as (th0 LVs0 Vh0) "SL".
  rewrite StackLocs_no_exist_head_immut_access.
  iDestruct "SL" as "(H & H0 & SIC)".
  iDestruct "H0" as %(HV0 & HUP0 & PH0 & STV0).

  iAssert (graph_snap γg G0 M) as "[_ PSV]". { by iFrame "Gs". }
  iDestruct (SeenLogview_closed with "PSV") as %SubM0.
  iCombine "sH0 PSV" as "PSV'".
  iDestruct (view_at_intro_incl with "PSV' sV")
    as (V0) "(sV0 & %LeVV0 & sH0' & PSV0) {PSV'}".

  (* ready to read *)
  wp_apply (AtomicSeen_acquire_read with "[$sH0 $H $sV0]"); first solve_ndisj.

  iIntros (th1 vh1 V1' V1 ζh0') "(Subζ & #sV1 & #sH1 & H)".
  iDestruct "Subζ" as %([Subζh0 Subζh0'] & Eqth1 & MAXth1 & LeV').
  assert (Eqth1' := lookup_weaken _ _ _ _ Eqth1 Subζh0').

  iAssert (@{Vb ⊔ V1} StackLocs_no_exist s E1 γh T1 S1 th0 LVs0 Vh0)%I
    with "[SIC H]" as "SL".
  { iApply (view_at_mono_2 with "SIC H"). clear; solve_lat. }

  assert (EqH := Eqth1').
  apply toHeadHist_lookup_Some in EqH as (Leth0 & on & -> & EqLVs0).
  destruct on as [n|]; last first.
  { (* EMPTY POP *)
    iSpecialize ("SLC" $! (Vb ⊔ V1) with "[SL]").
    { iExists _, _, _. iFrame "SL". }
    have SubM1 : set_in_bound M E1.
    { clear -SubM0 LeE0. by eapply set_in_bound_mono. }

    (* Commit AU with an EMPTY event, commiting point is the read. *)
    set V' := V1.
    have LeVV': V ⊑ V' by rewrite /V'; solve_lat.
    have bLeVV' : bool_decide (V ⊑ V') by eapply bool_decide_unpack; eauto.
    set Vpp := mkDView V V' V' bLeVV'.

    assert (GIP:= graph_insert_props_base _ EmpPop _ Vpp SubM1 EGCs1).
    destruct GIP as [ppId M' egV' G' LeG' SubM' SUB' Inpp NInpp EGCs'].
    have LeG0' : G0 ⊑ G' by etrans.
    set E' := G'.(Es).
    have LeE0' : E0 ⊑ E' by apply LeG0'.

    have SC' : ExtendedStackConsistent G'.
    { have NI : ∀ e1 e2, (e1, e2) ∈ G'.(com) → e1 ≠ ppId ∧ e2 ≠ ppId.
      { move => ?? /(gcons_com_included G1) [/= ??]. lia. }
      destruct SC1 as [SC1PS SC1PSO SC1PP
                        [SC1NZ SC1MA SC1FN SC1EM SC1NE SC1SO SC1LIFO SC1MO]
                        SC1LIFOb].
      constructor; [| | |constructor|..]; [| | | | |done| | |done| | |].
      - clear -SC1PS. by apply graph_insert_event_is_releasing.
      - intros e1 e2 eV1 eV2 v1 v2
          [Eq1|[-> <-]]%lookup_app_1; [|clear; by inversion 1].
        intros [Eq2|[-> <-]]%lookup_app_1; [|clear; intros _; by inversion 1].
        by apply SC1PSO.
      - clear -SC1PP. apply graph_insert_event_is_acquiring; [done|].
        clear; simpl; intros []; congruence.
      - apply stack_positive_value_insert; [|exact SC1NZ]. clear; done.
      - apply stack_matches_value_insert, SC1MA.
      - apply stack_unmatched_pop_empty_insert; [|exact SC1EM]. by right.
      - (* Step 1: if e is not the new event we added, use the old Consistency. *)
        apply stack_empty_unmatched_push_insert; [done| |exact SC1NE].
        (* Case: the ppId we added, we have to prove that we don't locally
          observe an unmatched push. *)
        intros _ u. rewrite elem_of_union elem_of_singleton => [[->|InM]].
        { intros [[v Eqp] _]. rewrite lookup_app_1_eq /= in Eqp. by inversion Eqp. }
        intros UM'.
        (* Step 2: assume that u is an unmatched push in G' M', we know
          that it is in M (≠ ppId) and is also unmatched in G0 M. *)
        have Equ0: is_Some (E0!! u) by apply SubM0.
        assert (UM0 := unmatched_push_mono _ _ _ LeG0' Equ0 UM').
        destruct UM0 as [[nu EqTu]%ET0 _].
        destruct (SH0 _ _ InM EqTu) as [tu Eqtu].
        (* Step 3: we know that the read value #null from Head must be later than u *)
        move : Eqtu. rewrite lookup_fmap_Some'.
        intros ([vu' Vu] & Eq & Eqtu). simpl in Eq. subst vu'.
        have Leth1: (tu ≤ th1)%positive. { apply MAXth1. by eexists. }
        (* Step 4: we also know that u as an unpopped element cannot have a
          #null value at a later timestamp => contradiction *)
        case (decide (nu ∈ S1)) => [InS|NInS]; last first.
        { have Equ1: is_Some (E1!! u) by apply SubM1.
          assert (UM1 := unmatched_push_mono _ _ _ LeG' Equ1 UM').
          destruct UM1 as [_ NSO1].
          assert (EqTu1 := lookup_weaken _ _ _ _ EqTu LeT0).
          assert (IN := stk_popped _ _ S1 SP1 _ _ EqTu1).
          destruct IN as [IN _]. move : IN.
          rewrite /popped_nodes elem_of_difference elem_of_list_to_set
                  elem_of_list_fmap => IN.
          destruct IN as ([u' p'] & Eq' & Inp').
          { split; [|done]. move : EqTu1. by apply elem_of_dom_2. }
          simpl in Eq'. subst u'. apply (NSO1 p'). move : Inp'. by rewrite elem_of_elements. }
        move : (HUP0 tu nu InS).
        rewrite (lookup_weaken ζh0 _ tu (#nu,Vu)); [..|done|by etrans].
        rewrite /= => HU. apply (HU eq_refl _ Leth1). by rewrite Eqth1' /=.
      - apply stack_LIFO_insert, SC1LIFO.
      - clear -SC1MO SUB'. by apply graph_insert_xo_eco.
      - apply stack_LIFO_empty_insert; [done|exact SC1LIFOb]. }

    have SP' : StackProps G' T1 S1.
    { destruct SP1 as [SP1SB SP1ET SP1INJ SP1PP SP1ORD1 SP1ORD2].
      constructor; [done| |done..].
      intros e. rewrite SP1ET. case (decide (e = ppId)) => [->|?].
      - rewrite lookup_app_1_eq (lookup_ge_None_2 E1); [clear; naive_solver|done].
      - by rewrite lookup_app_1_ne. }

    iMod "AU" as (G1') "[>SI' HClose]".
    iDestruct "SI'" as (γ' T1') "SI'".
    iDestruct (StackInv'_agree with "SI SI'") as %(-> & -> & ->).

    iMod (StackInv'_update _ _ _ _ _ G' T1 EGCs' SC' LeG' with "SI SI'")
      as "[SI SI']"; [done|apply SP'..|].
    iDestruct (StackInv'_snapshot with "SI") as (_) "#[_ [Gs' _]]".

    have LeV0Vp: V0 ⊑ dv_comm Vpp. { rewrite /= /V'; solve_lat. }
    iAssert (@{Vpp.(dv_comm)} SeenLogview E' M')%I with "[]" as "#PSV'".
    { rewrite -SeenLogview_insert'. iSplitL; [|done].
      iApply (view_at_mono with "PSV0"); [done|]. by apply SeenLogview_map_mono. }

    iAssert (@{V'} StackLocal N γg s G' M')%I with "[Gs']" as "-#SL'".
    { iFrame "Gs' PSV'".
      iExists γ, γh. iFrame "MTs SII". iExists T1. iFrame "LT1". iSplitL "".
      + iExists _. iFrame "sH1". iPureIntro.
        intros e n. rewrite elem_of_union elem_of_singleton => [[->|Ine]].
        * intros EqT. exfalso.
          destruct (stk_em _ _ _ SP1 ppId) as [[ve Eqve] _]. { by exists n. }
          move : Eqve => /list_lookup_fmap_inv' [? [?]].
          intros ?%lookup_lt_Some. lia.
        * revert Ine.
          eapply (SeenPushed_mono E0 E1 T0 T1 ζh0 _ M ET0);
                  [apply SP1|apply SP1|done..].
      + iPureIntro. apply SP'. }

    (* COMMIT EmpPop *)
    rewrite bi.and_elim_r.
    iMod ("HClose" $! 0 V' G' dummy_eid ppId dummy_sevt EmpPop Vpp M'
          with "[SI' $sV1 $SL']") as "HΦ".
    { (* Public Post *)
      iSplitL "SI'". { iExists γ, T1. iFrame "SI'". }
      iSplit; [..|by iPureIntro|].
      iPureIntro. right; left. do 8 (split; [done|]).
      intros e UM Ine.
      eapply (stk_cons_non_empty _ (exstk_cons_basic _ SC') ppId);
                        [by rewrite lookup_app_1_eq|done| |done].
      clear -Ine. rewrite /= elem_of_union. right. exact Ine. }

    (* re-establish the invariant *)
    iMod ("Close" with "[-HΦ]") as "_".
    { iNext. iExists G', T1. iFrame "SI". iExists S1.
      iDestruct "SLC" as "(%&SV&SLs)". iSplit; [done|]. iSplitL "SV".
      { (* ppId is not a push *)
        iIntros "{# %}" (???? [?|[_ ?]]%lookup_app_1); [by iApply "SV"|done]. }
      iDestruct "SLs" as (Vb') "SLs".
      iExists Vb'. clear -LeG'.
      iDestruct "SLs" as (t0 LVs Vh) "(? & F & ? & SLs)".
      iExists t0, LVs, Vh. iFrame. iSplitR "SLs"; last first.
      { rewrite in_slocs_map_mono; [iFrame "SLs"|apply LeG']. }
      iDestruct "F" as %(HV1 & HU1 & PH1 & STV1). iPureIntro.
      do 2 (split; [done|]). split; [|done].
      intros ??? [?|[_ <-]]%lookup_app_1; [by eapply PH1|done]. }

    (* finishing EmpDeq case *)
    iIntros "!>". wp_let. wp_op. wp_if. by iApply "HΦ".
  }

  (* possibly non-empty, do not commit yet *)
  (* but we acquire a fraction of `n >> next` to read *)
  rewrite (StackLocs_no_exist_node_next_access _ _ _ _ _ _ _ _ n V1'); last first.
  { move : EqLVs0. apply elem_of_list_lookup_2. }
  iDestruct "SL" as "[SL oN]".

  (* close the invariant *)
  iSpecialize ("SLC" $! (Vb ⊔ V1) with "[SL]").
  { iExists _, _, _. iFrame "SL". }
  iMod ("Close" with "[SI SLC]") as "_".
  { iIntros "{#} !>". iExists _, _. iFrame "SI". iExists _. iFrame "SLC". }
  iIntros "!>". simpl. wp_let. wp_op. wp_if. wp_op.

  (* read `n >> next` non-atomically *)
  iDestruct "oN" as (q on') "oN". rewrite view_at_view_at.
  iDestruct (view_at_elim with "[] oN") as "oN".
  { iApply (monPred_in_mono with "sV1"). simpl. solve_lat. }
  wp_read. wp_let.

  wp_bind (casᵃᶜ(_,_,_))%E.
  clear Vb.
  (* open the invariant *)
  iInv "SII" as (G2 T2) ">[SI [%S2 SBI]]" "Close".
  set E2 := G2.(Es).
  iMod "AU" as (G2') "[>SI' HClose]".
  iDestruct "SI'" as (γ' T2') "SI'".
  iDestruct (StackInv'_agree with "SI SI'") as %(-> & -> & ->).

  iDestruct (StackInv'_snapshot with "SI") as ([SC2 EGCs2]) "#[LT2 GS2]".
  iDestruct (StackInv'_graph_snap_incl with "SI GS0") as %LeG1.
  iDestruct (StackInv'_map_snap_incl with "SI LT1") as %LeT1.

  iDestruct "SBI" as "(%SP2 & #SV & SL)".
  iDestruct "SL" as (Vb t02 LVs2 Vh2) "(H & H2 & As & Is)".
  iDestruct "H2" as %(HV2 & HUP2 & PH2 & STV2).
  have LeT02: T0 ⊆ T2 by etrans.

  have LeG02 : G0 ⊑ G2 by etrans.
  have LeE02 : E0 ⊑ E2 by apply LeG02.
  have SubM: set_in_bound M E2.
  { clear - SubM0 LeE02. by eapply set_in_bound_mono. }

  iMod (rel_objectively_intro (⊒∅) tid with "[]") as "HRE".
  { iApply objective_objectively. iApply monPred_in_bot. }

  iDestruct (view_at_elim with "sV1 sH1") as "sH1'".
  set Pr : vProp :=
    ((n >> next) ↦{q} #(oloc_to_lit on')
    ∗ @{Vb} all_slocs (LVs2 ++ [(hd_error S2, Vh2)]))%I.
  wp_apply (AtomicSeen_CON_CAS_live_loc _ _ _ _ _ _ _ n #(oloc_to_lit on') _ ∅
              with "[$sH1' $H $sV1 HRE]"); [done|done|done|solve_ndisj|..].
  { intros t v NE. rewrite lookup_fmap_Some'.
    intros ([] & <- & ?).
    by eapply (toHeadHist_lookup_Some_is_comparable_nullable_loc _ _ _ _ _ (Some n)). }
  { simpl. iFrame "HRE". }

  iIntros (b t' v' V2 V2' ζh2'' ζh2) "(F & #sV2' & #sH2 & H & CASE)".
  iDestruct "F" as %([Subζh0'' Subζh2''] & Eqt' & MAXt' & LeV1). clear Pr.

  have LeVV2' : V ⊑ V2'. { clear -LeV1 LeVV0 LeV'. by solve_lat. }
  have bLeVV2' : bool_decide (V ⊑ V2') by eapply bool_decide_unpack; eauto.

  iDestruct "CASE" as "[[(%&%&%) HV2]|([%%] & CASE)]".
  { (* FAIL_RACE case *)
    (* COMMIT with no change *)
    subst b ζh2.

    rewrite bi.and_elim_r.
    set Vpp := mkDView V V2' V2' bLeVV2'.

    iAssert (@{V2'} StackLocal N γg s G2 M)%I with "[Gs]" as "SL'".
    { iSplit.
      - (* TODO variant of graph_snap_mono *)
        iDestruct "GS2" as "[$ _]". iApply (view_at_mono with "PSV0").
        + clear -LeV' LeV1. solve_lat.
        + by apply SeenLogview_map_mono.
      - iExists γ, γh. iFrame "MTs SII". iExists T2. iFrame "LT2". iSplitL "".
        + iExists _. iFrame "sH1". iPureIntro.
          apply (SeenPushed_mono E0 E2 T0 T2 ζh0 _ _ ET0); [apply SP2|apply SP2|done..].
        + iPureIntro. by apply SP2. }

    iMod ("HClose" $! FAIL_RACE V2' G2 dummy_eid dummy_eid
                      dummy_sevt dummy_sevt Vpp M with "[SI' $sV2' $SL']") as "HΦ".
    { iSplitL.
      - iExists γ, T2. iFrame "SI'".
      - iPureIntro. split; [done|by left]. }
    iIntros "!>".
    iMod ("Close" with "[SI H As Is]") as "_".
    { iNext. iExists G2, T2. iFrame "SI". iExists S2. iFrame "SV".
      iSplit; [done|]. iExists (Vb ⊔ V2'), _, LVs2, Vh2. by iFrame. }
    iIntros "!>". wp_if. by iApply "HΦ".
  }

  subst b v'.
  iDestruct "CASE" as (Vw (FRt & Eqζh2 & Eqt2 & LeV2 & _)) "[_ %LeV2']".
  have LeV22: V2 ⊑ V2' by etrans.

  rewrite (view_at_view_at _ Vh2 Vb).
  iAssert (⌜ NoDup S2 ⌝)%I with "[Is]" as %NDS2.
  { rewrite in_slocs_NoDup. by iDestruct "Is" as %?. }

  have Eqt2': toHeadHist t02 (LVs2 ++ [(hd_error S2, Vh2)]) !! t' = Some (#n, V2).
  { eapply lookup_weaken in Eqt'; [|apply Subζh2''].
    rewrite Eqζh2 lookup_insert_ne in Eqt'; [done|lia]. }

  apply toHeadHist_lookup_Some in Eqt2' as (Let02 & on & Eqon & Eqn2).
  assert (on = Some n) as ->.
  { clear -Eqon. by destruct on; inversion Eqon. } clear Eqon.

  assert (EqL: (Pos.to_nat t' - Pos.to_nat t02)%nat = length LVs2).
  { assert (LtL := lookup_lt_Some _ _ _ Eqn2).
    clear -FRt Let02 LtL.
    apply toHeadHist_lookup_None in FRt as [?|Let']; first (exfalso; lia).
    apply : (anti_symm (le)).
    - clear -LtL. rewrite app_length /= in LtL. lia.
    - clear LtL.
      rewrite app_length /= /pos_add_nat in Let'; lia. }
  rewrite EqL in Eqn2.
  assert (Vh2 = V2 ∧ ∃ S2', S2 = n :: S2') as (-> & S2' & ->).
  { clear -Eqn2. apply lookup_last_Some_2 in Eqn2. inversion Eqn2 as [Eq1].
    split; [done|]. destruct S2; inversion Eq1. by eexists. }

  (* get the location *)
  rewrite in_sloc_cons in_slocs_optional_head_access.
  iDestruct "Is" as "(Hn & Is & HSh)".
  iDestruct "Hn" as (vn epn EqTn) "(Hnn & Hnd & Hepn)".

  iAssert (⊒V2)%I with "[]" as "#sV2". { by iApply (monPred_in_mono with  "sV2'"). }
  iAssert (⌜on' = hd_error S2'⌝)%I with "[Hnn oN ]" as %->.
  { clear. iDestruct (view_at_elim with "sV2 Hnn") as (q') "Hnn".
    iDestruct (own_loc_na_agree with "oN Hnn") as %Eq. iPureIntro.
    inversion Eq as [Eq']. by apply oloc_to_lit_inj in Eq'. }

  iAssert (@{Vb} all_slocs ((LVs2 ++ [(Some n, V2)]) ++ [(hd_error S2', Vw)]))%I
    with "[Hnn HSh As]" as "As".
  { rewrite {2}/all_slocs big_sepL_app big_sepL_singleton.
    iSplitL "As"; [by iFrame|].
    destruct S2' as [|n' S2''] eqn:Eqn'; [eauto|]; simpl.
    iDestruct "HSh" as (on'' q' EqS) "H".
    iExists q', on''. rewrite view_at_view_at. by iFrame "H". }

  destruct SP2 as [SP2SB SP2ET SP2INJ SP2PP SP2ORD1 SP2ORD2].

  set psId := epn.

  have UPp: (∀ id, (psId, id) ∉ G2.(so)).
  { intros pp Inpp. specialize (SP2PP _ _ EqTn) as [_ PP]. move : PP.
    rewrite elem_of_list_fmap /popped_nodes elem_of_difference elem_of_list_to_set.
    destruct 1 as [? NIn].
    { exists (psId, pp). split; [done|]. by rewrite elem_of_elements. }
    apply NIn. by left. }

  iDestruct "Hepn" as (eV Eqvp) "[%LeVW Hepn]".
  iDestruct "Hepn" as (Eqep) "[#SE %SubeV]".
  rewrite view_at_view_at.
  assert (SubeV2 := egcons_logview_closed _ EGCs2 _ _ Eqep).

  destruct SC2 as [SC2PS SC2PSO SC2PP
                    [SC2NZ SC2MA SC2FN SC2EM SC2NE SC2SO SC2LIFO SC2MO] SC2LIFOb].
  (* we know that 0 < vn *)
  assert (NZ := SC2NZ _ _ _ Eqep Eqvp).

  set V' := Vw.
  set Vpp := mkDView V V2' V' bLeVV2'.
  set M'' := eV.(ge_lview).
  have SubVin : eV.(ge_view).(dv_in) ⊑ Vpp.(dv_comm).
  { simpl. clear -LeV22 SubeV. rewrite dv_in_com. solve_lat. }
  have SubVeV : eV.(ge_view).(dv_comm) ⊑ V'. { solve_lat. }
  assert (GIP := graph_insert_edge_props_base _ _ _ (Pop vn) M Vpp
                    Eqep SubM EGCs2 SubVin).
  rewrite -/M'' in GIP.
  destruct GIP as [b [ppId M' egV' G' [NEqed Lted] LeG' [Subm' SubeV'] SubM'
                      [Inps' Inpp'] FRpp EGCs']].
  assert (EqG' := graph_insert_edge_eq psId egV' G2 b).
  rewrite -/G' in EqG'. destruct EqG' as (_ & EqEs' & EqSo' & EqCo').

  have SC' : ExtendedStackConsistent G'.
  { have NI : ∀ e1 e2, (e1, e2) ∈ G2.(com) → e1 ≠ ppId ∧ e2 ≠ ppId.
    { move => ?? /(gcons_com_included G2) [/= ??]. lia. }
    constructor; [| | |constructor|..].
    - clear -SC2PS. apply graph_insert_event_is_releasing; [done|].
      clear; simpl; intros []; congruence.
    - intros e1 e2 eV1 eV2 v1 v2
        [Eq1|[-> <-]]%lookup_app_1; [|clear; by inversion 1].
      intros [Eq2|[-> <-]]%lookup_app_1; [|clear; intros _; by inversion 1].
      by apply SC2PSO.
    - clear -SC2PP LeV2'. by apply graph_insert_event_is_acquiring.
    - apply stack_positive_value_insert; [|exact SC2NZ].
      clear; simpl; intros ?; inversion 1.
    - (* 2 *)
      apply (stack_matches_value_insert_edge _ _ _ _ _ _ Eqep Eqvp); [done| |done].
      simpl. clear -SubeV LeV22. solve_lat.
    - (* 3 *) clear -UPp SC2FN SC2SO. rewrite SC2SO in UPp.
      by apply (stack_com_functional_insert_edge _ _ _ _ UPp SC2FN).
    - (* 4 *) apply stack_unmatched_pop_empty_insert_edge, SC2EM.
    - (* 5 *) by apply stack_empty_unmatched_push_insert_edge.
    - by rewrite /G' /= SC2SO.
    - (* LIFO *)
      apply (stack_LIFO_insert_edge _ _ _ _ _ _ Eqep Eqvp); [|done..].
      clear -SP2ORD2 SC2SO SC2MO Eqep EqTn NI.
      intros u1 o1 _ In1 [Ltu1 Lto1] _ _ _. destruct (NI _ _ In1).
      rewrite 2!elem_of_union elem_of_singleton.
      intros [InM|[->|InM']]; [|done|].
      * (* psId is still in the stack, so it cannot get in between u1 and o1 *)
        rewrite -SC2SO in In1.
        destruct (SP2ORD2 _ _ (ltac:(by left)) EqTn _ _ In1) as [[]|[]]; lia.
      * (* psId < o1   ∧   o1 ≤ psId => contradiction *)
        apply (SC2MO _ _ _ Eqep) in InM'. lia.
    - clear -SubM' SC2MO. by apply graph_insert_xo_eco.
    - intros u1 o1 oV1 u2 uV2. rewrite elem_of_union elem_of_singleton.
      intros [Equo1|In1].
      + inversion Equo1; clear Equo1; subst u1 o1.
        rewrite lookup_app_1_eq. intros EqoV1; inversion EqoV1; clear EqoV1; subst oV1.
        simpl. intros Equ2 InuV2 InM' UM'.
        have NEpp: u2 ≠ ppId.
        { clear -UM'. intros ->. destruct UM' as [[v Eqv] _].
          by rewrite lookup_app_1_eq in Eqv. }
        rewrite lookup_app_1_ne in Equ2; [|done].
        assert (unmatched_push G2 u2) as [[v2 Eqv2] NInG2].
        { move : UM'. apply unmatched_push_mono; [done..|by eexists]. }
        destruct (SP2ET u2) as [_ [n2 EqTn2]]. { by exists v2. }
        have InS : n2 ∈ n :: S2'.
        { case (decide (n2 ∈ (n :: S2'))) => NInS; [done|]. exfalso.
          have InPP : n2 ∈ popped_nodes T2 (n :: S2').
          { rewrite /popped_nodes. apply elem_of_difference. split.
            - move : EqTn2. apply elem_of_dom_2.
            - by rewrite elem_of_list_to_set. }
          apply (SP2PP _ _ EqTn2), elem_of_list_fmap in InPP as [[u2' p2] [Equ2' InG2]].
          simpl in Equ2'. subst u2'. apply (NInG2 p2), elem_of_elements, InG2. }
        have LB: list_before (n :: S2') n n2.
        { apply elem_of_list_lookup in InS as [i2 Eqi2].
          exists 0%nat, i2. split; last split; [done..|clear;lia]. }
        assert (LE1 := SP2ORD1 _ _ _ _ LB EqTn EqTn2).
        assert (LE2 := SC2MO _ _ _ Equ2 InuV2).
        assert (Eqpu2: u2 = psId). { clear -LE1 LE2. by  apply : (anti_symm Nat.le). }
        clear -UM' Eqpu2 EqSo'. destruct UM' as [_ UM']. apply (UM' ppId).
        subst u2. rewrite EqSo'. set_solver-.
      + destruct (NI _ _ In1). rewrite lookup_app_1_ne; [|done].
        intros Eqo1 Equ2 InuV2 InoV1 UM.
        rewrite lookup_app_1_ne in Equ2; last first.
        { intros ->. apply (egcons_logview_closed _ EGCs2 _ _ Eqo1),
                            lookup_lt_is_Some in InoV1. lia. }
        apply (SC2LIFOb _ _ _ _ _ In1 Eqo1 Equ2 InuV2 InoV1).
        apply (unmatched_push_mono _ G' _ LeG'); [by eexists|done]. }

  have SP' : StackProps G' T2 S2'.
  { constructor.
    - etrans; last apply SP2SB. simpl. set_solver-.
    - intros e. rewrite SP2ET. case (decide (e = ppId)) => [->|?].
      + rewrite lookup_app_1_eq (lookup_ge_None_2 E2); [clear; naive_solver|done].
      + by rewrite lookup_app_1_ne.
    - done.
    - intros n' e' Eqn'. rewrite /= elements_union_singleton; last by apply UPp.
      rewrite fmap_cons elem_of_cons.
      specialize (SP2PP _ _ Eqn'). rewrite <-SP2PP.
      rewrite /popped_nodes list_to_set_cons
              difference_union_distr_r_L elem_of_intersection. split.
      + intros Inn'. case (decide (n' = n)) => NEq.
        * subst n'. left. clear -EqTn Eqn'. rewrite EqTn in Eqn'. by inversion Eqn'.
        * right. split; [|done]. apply elem_of_difference. clear -NEq Eqn'.
          rewrite elem_of_singleton. split; [|done].
          move : Eqn'. by apply elem_of_dom_2.
      + intros [->|[]]; [|done]. simpl in Eqn'.
        assert (Eq:=SP2INJ _ _ _ Eqn' EqTn). subst n'.
        apply elem_of_difference. split.
        * move : Eqn'. by apply elem_of_dom_2.
        * clear -NDS2. rewrite elem_of_list_to_set. by apply NoDup_cons in NDS2 as [].
    - intros n1 n2 e1 e2 LB. apply SP2ORD1.
      apply (list_before_suffix _ _ _ _ LB). clear. by exists [n].
    - intros n' e' In' Eqn' ps pp. rewrite elem_of_union elem_of_singleton.
      intros [Eq|InG2].
      + inversion Eq. clear Eq. subst pp ps. right. split.
        * apply (SP2ORD1 n n'); [|done..].
          apply elem_of_list_lookup in In' as [i Eqi].
          exists 0%nat, (S i). simpl. do 2 (split; [done|]). lia.
        *  apply Nat.lt_le_incl, lookup_lt_is_Some.
          destruct (SP2ET e') as [[? [? [_ ?]]%list_lookup_fmap_inv'] _]; by eexists.
      + revert InG2. apply (SP2ORD2 n'); [by right|done]. }

  set E' := G'.(Es).
  have LeE' : E2 ⊑ E' by apply LeG'.
  iAssert (@{Vpp.(dv_comm)} SeenLogview E' M')%I with "[]" as "-#SNL".
  { rewrite -SeenLogview_union' -SeenLogview_insert'.
    iSplitL; last iSplitL; [..|by iFrame "SE"|done].
    iApply (view_at_mono with "PSV0").
    - simpl. clear -LeV' LeV1. solve_lat.
    - apply SeenLogview_map_mono; [by etrans|done]. }

  iAssert (⊒V')%I with "[]" as "#sV'". { by iApply (monPred_in_mono with "sV2'"). }

  iAssert (@{V2'} SeenHead γh s T2 M')%I with "[]" as "-#SH'".
  { iDestruct ("SV" $! psId vn eV.(ge_view) eV.(ge_lview) with "[%]") as "SVPP".
    { clear - Eqep Eqvp. rewrite -Eqvp. by destruct eV. }
    iDestruct "SVPP" as (ζhe) "[sHe %SHe]".
    iExists (ζh0 ∪ ζhe). iSplit.
    { rewrite -AtomicSeen_join'. iFrame "sHe".
      iApply (view_at_mono with "sH0'"); [|done]. clear -LeV' LeV1. solve_lat. }
    iDestruct (AtomicSeen_union_equiv with "sH0' sHe") as %Eqζ.
    iPureIntro.
    assert (SH2: SeenPushed T2 (ζh0 ∪ ζhe) M).
    { move : SH0. apply (SeenPushed_mono E0 E2); [done..|apply map_union_subseteq_l]. }
    assert (SH2': SeenPushed T2 (ζh0 ∪ ζhe) M'').
    { move : SHe. apply SeenPushed_hist_mono. rewrite Eqζ. apply map_union_subseteq_l.  }
    apply SeenPushed_union; [done|]. apply SeenPushed_union; [|done].
    intros e' n' ->%elem_of_singleton Eqn'. exfalso. clear -Eqn' SP2ET.
    destruct (SP2ET ppId) as [[? Eqv] _]. { by exists n'. }
    move : Eqv => /list_lookup_fmap_inv' [? [?]]. intros ?%lookup_lt_Some. lia. }

  (* update the graph *)
  iMod (StackInv'_update _ _ _ _ _ G' T2 EGCs' SC' LeG' with "SI SI'")
      as "[SI SI']"; [done|apply SP'..|].
  iDestruct (StackInv'_snapshot with "SI") as (_) "#[_ [Gs' _]]".

  iAssert (@{V2'} StackLocal N γg s G' M')%I with "[Gs' SNL SH']" as "SL'".
  { iFrame "Gs' SNL". iExists γ, γh. iFrame "MTs SII". iExists T2.
    iFrame "LT2 SH'". iPureIntro. apply SP'. }
  rewrite bi.and_elim_r.
  iMod ("HClose" $! vn V2' G' psId ppId (Push vn) (Pop vn) Vpp M'
        with "[SI' $sV2' $SL']") as "HΦ".
  { iSplitL "SI'". { iExists γ, T2. by iFrame. }
    iPureIntro. split; [done|]. right; right.
    do 11 (split; [done|]). by exists eV. }
  iIntros "!>".
  (* re-establish the invariant *)
  iMod ("Close" with "[SI H Is As]") as "_".
  { iNext. iExists G', T2. iFrame "SI". iExists S2'. iSplit; [done|].
    iSplitL "".
    { (* ppId is not a push *)
      clear. iIntros (???? [?|[_ ?]]%lookup_app_1); [by iApply "SV"|done]. }
    set LVs' := (LVs2 ++ [(Some n, V2)]).
    have EQH : toHeadHist t02 (LVs' ++ [(hd_error S2', Vw)]) =
      <[(t' + 1)%positive:=(#(oloc_to_lit (hd_error S2')), Vw)]> (toHeadHist t02 LVs').
    { rewrite toHeadHist_insert; [done|..].
      - clear -EqL Let02. rewrite app_length /= -EqL. lia.
      - clear. rewrite app_length /=. lia. }
    iExists (Vb ⊔ V2'), t02, LVs', Vw. iSplitL "H".
    { rewrite Eqζh2 -EQH. by iFrame "H". }
    iFrame "As". iSplit; last first.
    { rewrite (view_at_view_at _ Vw). rewrite (in_slocs_map_mono _ E'); [|done].
      by iFrame "Is". }
    iPureIntro; split; last split; last split.
    - intros l. rewrite fmap_app elem_of_app /= elem_of_list_singleton HV2.
      split; [|clear; naive_solver]. move => [//|InS2'].
      apply SP2SB, elem_of_list_to_set. right.
      clear -InS2'. destruct S2'; simplify_list_eq. by left.
    - rewrite EQH. intros t0 n0 In0 Eq0 t0' Let'.
      case (decide (t0' = (t' + 1)%positive)) => [->|NEq].
      { rewrite lookup_insert /=. clear -In0.
        destruct S2'; [by apply not_elem_of_nil in In0|]. simpl. by inversion 1. }
      rewrite lookup_insert_ne; [|done].
      move : Eq0.
      case (decide (t0 = (t' + 1)%positive)) => ?; [subst t0|].
      + rewrite lookup_insert /=. intros _.
        apply (HUP2 t' n); [by left| |clear -Let'; lia].
        assert (HL := lookup_weaken _ _ _ _ Eqt' Subζh2'').
        rewrite Eqζh2 lookup_insert_ne in HL; [|clear; lia].
        by rewrite HL.
      + rewrite lookup_insert_ne; [|done].
        intros Eqt0. apply (HUP2 t0 n0); [by right|done..].
    - clear -PH2. intros e1 eV1 v1 [Eq1|[-> <-]]%lookup_app_1.
      + move => /(PH2 _ _ _ Eq1) [n1 ?]. exists n1. rewrite elem_of_app. by left.
      + intros Eqv1. exists n. rewrite elem_of_app elem_of_list_singleton. by right.
    - clear -STV2 LeV2.
      intros V. rewrite fmap_app elem_of_app /= elem_of_list_singleton.
      intros [?%STV2| ->];[solve_lat|done]. }

  (* finish CAS successful case *)
  iIntros "!>". wp_if. wp_op.
  iDestruct (view_at_elim with "sV2 Hnd") as "Hnd".
  wp_read. by iApply "HΦ". (* leaking data field *)
Qed.

Lemma atom_pop :
  pop_spec' pop StackLocal StackInv.
Proof.
  intros N DISJ s tid γg G1 M V. iIntros "#sV #Gs" (Φ) "AU".
  iLöb as "IH".

  wp_rec.
  awp_apply (atom_try_pop with "sV Gs"); [eauto..|].
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

Definition treiber_stack_impl Σ
  `{!noprolG Σ, !tstackG Σ, !atomicG Σ} : extended_stack_spec Σ := {|
    spec_graph.StackInv_Objective := StackInv_objective ;
    spec_graph.StackInv_Fractional := StackInv_fractional ;
    spec_graph.StackInv_StackConsistent := StackInv_ExtendedStackConsistent_instance ;
    spec_graph.StackInv_graph_master_acc := StackInv_graph_master_acc_instance ;
    spec_graph.StackInv_graph_snap := StackInv_graph_snap_instance ;
    spec_graph.StackInv_agree := StackInv_agree_instance ;

    spec_graph.StackLocal_graph_snap := StackLocal_graph_snap_instance ;
    spec_graph.StackLocal_Persistent := StackLocal_persistent ;
    spec_graph.StackLocal_union := StackLocal_union_instance ;
    spec_graph.StackLocal_upgrade := StackLocal_upgrade_instance ;

    spec_graph.StackLocalLite_graph_snap := StackLocalLite_graph_snap_instance ;
    spec_graph.StackLocalLite_Persistent := StackLocalLite_persistent ;
    spec_graph.StackLocalLite_Timeless := StackLocalLite_timeless ;
    spec_graph.StackLocalLite_from := StackLocalLite_from_instance ;
    spec_graph.StackLocalLite_to := StackLocalLite_to_instance ;
    spec_graph.StackLocalLite_upgrade := StackLocalLite_upgrade_instance ;

    spec_graph.new_stack_spec := new_stack_spec;
    spec_graph.try_push_spec := atom_try_push ;
    spec_graph.push_spec := atom_push ;
    spec_graph.try_pop_spec := atom_try_pop ;
    spec_graph.pop_spec := atom_pop ;
  |}.
