From stdpp Require Import namespaces.
From iris.bi Require Import lib.fractional.

From gpfsl.logic Require Import logatom.
From gpfsl.examples.graph Require Export spec.
From gpfsl.examples.stack Require Export event.

Require Import iris.prelude.options.

Local Open Scope Z_scope.

Local Notation graph := (graph sevent).
Local Notation event_list := (event_list sevent).

Implicit Types (G : graph) (E : event_list) (M : logView) (N : namespace).

Definition unmatched_push G eid : Prop :=
  (∃ v : Z, ge_event <$> (G.(Es) !! eid) = Some (Push v)) ∧
    (∀ id, (eid, id) ∉ G.(so)).

(** Stack predicates *)
Local Notation EMPTY := 0 (only parsing).
Local Notation FAIL_RACE := (-1) (only parsing).

(* TODO: generalize these types for graph specs *)
Definition StackLocalT Σ : Type :=
  gname → loc → graph → logView → vProp Σ.
Definition StackLocalNT Σ : Type :=
  namespace → StackLocalT Σ.
Definition StackInvT Σ : Type :=
  gname → loc → frac → graph → vProp Σ.

Definition new_stack_spec' {Σ} `{!noprolG Σ, !inG Σ (graphR sevent)}
  (new_stack : val) (StackLocal : StackLocalNT Σ) (StackInv : StackInvT Σ) : Prop :=
  ∀ N tid,
  {{{ True }}}
    new_stack [] @ tid; ⊤
  {{{ γg (s: loc), RET #s; StackLocal N γg s ∅ ∅ ∗ StackInv γg s 1%Qp ∅ }}}.

Definition try_push_spec' {Σ} `{!noprolG Σ, !inG Σ (graphR sevent)}
  (try_push : val) (StackLocal : StackLocalNT Σ) (StackInv : StackInvT Σ) : Prop :=
  ∀ N (DISJ: N ## histN) (s: loc) tid γg G1 M (V : view) (v : Z) (Posx: 0 < v),
  (* PRIVATE PRE *)
  (* G1 is a snapshot of the graph, locally observed by M *)
  ⊒V -∗ StackLocal N γg s G1 M -∗
  (* PUBLIC PRE *)
  <<< ∀ G, ▷ StackInv γg s 1%Qp G >>>
    try_push [ #s ; #v] @ tid; ↑N
  <<< ∃ (b: bool) V' G' (psId : event_id) ps Vpush M',
      (* PUBLIC POST *)
      ▷ StackInv γg s 1%Qp G' ∗
      ⊒V' ∗ @{V'} StackLocal N γg s G' M' ∗
      ⌜ (* FAIL_RACE case *)
        (b = false ∧ G' = G ∧ M' = M)
      ∨ (* successful case *)
      ( b = true ∧ G ⊑ G' ∧ M ⊑ M' ∧
        Vpush.(dv_in) = V ∧ Vpush.(dv_comm) = V' ∧
        (* Vpush.(dv_wrt) = V' ∧ *) (* << only works if the push is also acquiring *)
        (* ps is a new push event with which G' strictly extends G *)
        is_push ps v ∧
        psId = length G.(Es) ∧
        G'.(Es) = G.(Es) ++ [mkGraphEvent ps Vpush M'] ∧
        G'.(so) = G.(so) ∧ G'.(com) = G.(com) ∧
        psId ∈ M' ∧ psId ∉ M ) ⌝,
      (* RETURN VALUE AT COMMITTING POINT *)
      RET #b, emp >>>
  .

Definition push_spec' {Σ} `{!noprolG Σ, !inG Σ (graphR sevent)}
  (push : val) (StackLocal : StackLocalNT Σ) (StackInv : StackInvT Σ) : Prop :=
  ∀ N (DISJ: N ## histN) (s: loc) tid γg G1 M (V : view) (v : Z) (Posx: 0 < v),
  (* PRIVATE PRE *)
  (* G1 is a snapshot of the graph, locally observed by M *)
  ⊒V -∗ StackLocal N γg s G1 M -∗
  (* PUBLIC PRE *)
  <<< ∀ G, ▷ StackInv γg s 1%Qp G >>>
    push [ #s ; #v] @ tid; ↑N
  <<< ∃ V' G' (psId : event_id) ps Vpush M',
      (* PUBLIC POST *)
      ▷ StackInv γg s 1%Qp G' ∗
      ⊒V' ∗ @{V'} StackLocal N γg s G' M' ∗
      ⌜ G ⊑ G' ∧ M ⊑ M' ∧
        Vpush.(dv_in) = V ∧ Vpush.(dv_comm) = V' ∧
        (* Vpush.(dv_wrt) = V' ∧ *) (* << only works if the push is also acquiring *)
        (* ps is a new push event with which G' strictly extends G *)
        is_push ps v ∧
        psId = length G.(Es) ∧
        G'.(Es) = G.(Es) ++ [mkGraphEvent ps Vpush M'] ∧
        G'.(so) = G.(so) ∧ G'.(com) = G.(com) ∧
        psId ∈ M' ∧ psId ∉ M ⌝,
      (* RETURN VALUE AT COMMITTING POINT *)
      RET #☠, emp >>>
  .

Definition try_pop_spec' {Σ} `{!noprolG Σ, !inG Σ (graphR sevent)}
  (try_pop : val) (StackLocal : StackLocalNT Σ) (StackInv : StackInvT Σ) : Prop :=
  ∀ N (DISJ: N ## histN) (s: loc) tid γg G1 M V,
  (* PRIVATE PRE *)
  ⊒V -∗ StackLocal N γg s G1 M -∗
  (* PUBLIC PRE *)
  <<< ∀ G, ▷ StackInv γg s 1%Qp G >>>
    try_pop [ #s] @ tid; ↑N
  <<< ∃ (v: Z) V' G' (psId ppId : event_id) ps pp Vpp M',
      (* PUBLIC POST *)
      ▷ StackInv γg s 1%Qp G' ∗
      ⊒V' ∗ @{V'} StackLocal N γg s G' M' ∗
      ⌜ G ⊑ G' ∧ M ⊑ M' ∧
        (* the view after should acquire the view of pop *)
        Vpp.(dv_in) = V ∧ Vpp.(dv_comm) = V'
        (* V ⊑ Vpp.(dv_wrt) ∧ *) (* << only works if pop is releasing *) ⌝ ∗
      ⌜ (* FAIL_RACE case *)
        (v = FAIL_RACE ∧ G' = G ∧ M' = M)
      ∨ (* EMPTY case *)
        ( v = EMPTY ∧ pp = EmpPop ∧
          ppId = length G.(Es) ∧
          G'.(Es) = G.(Es) ++ [mkGraphEvent pp Vpp M'] ∧
          G'.(so) = G.(so) ∧ G'.(com) = G.(com) ∧
          M' = {[ ppId ]} ∪ M ∧ ppId ∉ M ∧
          (* coming from StackConsistent. We have it here for convenience. *)
          (∀ psId, unmatched_push G' psId → psId ∉ M) )
      ∨ (* successful case *)
        ( 0 < v ∧ is_push ps v ∧ is_pop pp v ∧
          ppId = length G.(Es) ∧
          (∀ id, (psId, id) ∉ G.(so)) ∧
          G'.(Es) = G.(Es) ++ [mkGraphEvent pp Vpp M'] ∧
          G'.(so) = {[(psId, ppId)]} ∪ G.(so) ∧
          G'.(com) = {[(psId, ppId)]} ∪ G.(com) ∧
          psId ∈ M' ∧ ppId ∈ M' ∧ ppId ∉ M ∧
          ∃ eV, G.(Es) !! psId = Some eV ∧ eV.(ge_event) = ps ∧ eV.(ge_lview) ⊆ M') ⌝ ,
      (* RETURN VALUE AT COMMITTING POINT *)
      RET #v, emp >>>
  .

Definition pop_spec' {Σ} `{!noprolG Σ, !inG Σ (graphR sevent)}
  (pop : val) (StackLocal : StackLocalNT Σ) (StackInv : StackInvT Σ) : Prop :=
  ∀ N (DISJ: N ## histN) (s: loc) tid γg G1 M V,
  (* PRIVATE PRE *)
  ⊒V -∗ StackLocal N γg s G1 M -∗
  (* PUBLIC PRE *)
  <<< ∀ G, ▷ StackInv γg s 1%Qp G >>>
    pop [ #s] @ tid; ↑N
  <<< ∃ (v: Z) V' G' (psId ppId : event_id) ps pp Vpp M',
      (* PUBLIC POST *)
      ▷ StackInv γg s 1%Qp G' ∗
      ⊒V' ∗ @{V'} StackLocal N γg s G' M' ∗
      ⌜ G ⊑ G' ∧ M ⊑ M' ∧
        (* the view after should acquire the view of pop *)
        Vpp.(dv_in) = V ∧ Vpp.(dv_comm) = V'
        (* V ⊑ Vpp.(dv_wrt) ∧ *) (* << only works if pop is releasing *) ⌝ ∗
      ⌜ (* EMPTY case *)
        ( v = 0 ∧ pp = EmpPop ∧
          ppId = length G.(Es) ∧
          G'.(Es) = G.(Es) ++ [mkGraphEvent pp Vpp M'] ∧
          G'.(so) = G.(so) ∧ G'.(com) = G.(com) ∧
          M' = {[ ppId ]} ∪ M ∧ ppId ∉ M ∧
          (* coming from StackConsistent. We have it here for convenience. *)
          (∀ psId, unmatched_push G' psId → psId ∉ M) )
      ∨ (* successful case *)
        ( 0 < v ∧ is_push ps v ∧ is_pop pp v ∧
          ppId = length G.(Es) ∧
          (∀ id, (psId, id) ∉ G.(so)) ∧
          G'.(Es) = G.(Es) ++ [mkGraphEvent pp Vpp M'] ∧
          G'.(so) = {[(psId, ppId)]} ∪ G.(so) ∧
          G'.(com) = {[(psId, ppId)]} ∪ G.(com) ∧
          psId ∈ M' ∧ ppId ∈ M' ∧ ppId ∉ M ∧
          ∃ eV, G.(Es) !! psId = Some eV ∧ eV.(ge_event) = ps ∧ eV.(ge_lview) ⊆ M') ⌝ ,
      (* RETURN VALUE AT COMMITTING POINT *)
      RET #v, emp >>>
  .

Record stack_spec {Σ} `{!noprolG Σ, !inG Σ (graphR sevent)}
  {StackConsistent : graph → Prop} := StackSpec {
  (** operations *)
  new_stack : val;
  try_push : val;
  push : val;
  try_pop : val;
  pop : val;

  (** predicates *)
  StackLocal : StackLocalNT Σ;
  StackLocalLite : StackLocalT Σ;
  StackInv : StackInvT Σ;

  (** predicates properties *)
  StackInv_Objective : ∀ γg s q G, Objective (StackInv γg s q G) ;
  StackInv_Timeless : ∀ γg s q G, Timeless (StackInv γg s q G) ;
  (* TODO: one might want exclusiveness for StackInv *)
  StackInv_Fractional : ∀ γg s G, Fractional (λ q, StackInv γg s q G) ;
  StackInv_AsFractional : ∀ γg s q G,
    AsFractional (StackInv γg s q G) (λ q, StackInv γg s q G) q ;

  StackInv_StackConsistent : ∀ γg s q G, StackInv γg s q G ⊢ ⌜ StackConsistent G ⌝ ;
  StackInv_graph_master_acc :
    ∀ γg s q G, StackInv γg s q G ⊢
      ∃ q', graph_master γg q' G ∗ (graph_master γg q' G -∗ StackInv γg s q G) ;
  StackInv_graph_snap :
    ∀ γg s q G G' M',
      StackInv γg s q G -∗ graph_snap γg G' M' -∗ ⌜ G' ⊑ G ⌝;
  StackInv_agree :
    ∀ γg s q G q' G',
      StackInv γg s q G -∗ StackInv γg s q' G' -∗ ⌜ G' = G ⌝;

  StackLocal_Persistent :
    ∀ N γg s G M, Persistent (StackLocal N γg s G M) ;
  StackLocal_graph_snap :
    ∀ N  γg s G M, StackLocal N γg s G M ⊢ graph_snap γg G M ;
  StackLocal_union :
    ∀ N γg s q G G1 G2 M1 M2,
      StackInv γg s q G -∗ StackLocal N γg s G1 M1 -∗ StackLocal N γg s G2 M2 -∗
      StackLocal N γg s G (M1 ∪ M2) ;
  StackLocal_upgrade :
    ∀ N γg s q G' G M,
      StackInv γg s q G' -∗ StackLocal N γg s G M -∗ StackLocal N γg s G' M ;

  (* StackLocalLite is the light version of StackLocal that is Timeless *)
  StackLocalLite_Timeless :
    ∀ γg s G M, Timeless (StackLocalLite γg s G M) ;
  StackLocalLite_Persistent :
    ∀ γg s G M, Persistent (StackLocalLite γg s G M) ;
  StackLocalLite_from :
    ∀ N γg s G M, StackLocal N γg s G M ⊢ StackLocalLite γg s G M ;
  StackLocalLite_to :
    ∀ N γg s G' M' G M,
      StackLocalLite γg s G M -∗ StackLocal N γg s G' M' -∗ StackLocal N γg s G M ;
  StackLocalLite_graph_snap :
    ∀ γg s G M, StackLocalLite γg s G M ⊢ graph_snap γg G M ;
  StackLocalLite_upgrade :
    ∀ γg s q G' G M,
      StackInv γg s q G' -∗ StackLocalLite γg s G M -∗ StackLocalLite γg s G' M ;

  (* operations specs *)
  new_stack_spec : new_stack_spec' new_stack StackLocal StackInv;
  try_push_spec : try_push_spec' try_push StackLocal StackInv;
  push_spec : push_spec' push StackLocal StackInv;
  try_pop_spec : try_pop_spec' try_pop StackLocal StackInv;
  pop_spec : pop_spec' pop StackLocal StackInv;
}.

Arguments stack_spec _ {_ _} _.

(* push is releasing *)
Definition stack_push_releasing E : Prop :=
  graph_event_is_releasing E (λ eg, ∃ v, eg = Push v).
(* pop is acquiring *)
Definition stack_pop_acquiring E : Prop :=
  graph_event_is_acquiring E (λ eg, ∃ v, eg = Pop v).
(* only push positive values *)
Definition stack_positive_value E : Prop :=
  ∀ e eV (v: Z), E !! e = Some eV → eV.(ge_event) = Push v → 0 < v.
(* pushes are ordered by CASes *)
Definition stack_push_CAS_order E : Prop :=
  ∀ e1 e2 eV1 eV2 (v1 v2 : Z),
    E !! e1 = Some eV1 → E !! e2 = Some eV2 →
    is_push eV1.(ge_event) v1 →
    is_push eV2.(ge_event) v2 →
    (e1 < e2)%nat →
    ¬ eV2.(ge_view).(dv_comm) ⊑ eV1.(ge_view).(dv_comm).

(** (2) com relates matching push and pop events *)
Definition stack_matches_value G : Prop :=
  ∀ e d, (e, d) ∈ G.(com) → (e < d)%nat ∧
    ∃ eV dV (v : Z), G.(Es) !! e = Some eV ∧ G.(Es) !! d = Some dV ∧
      eV.(ge_event) = Push v ∧ dV.(ge_event) = Pop v ∧
      (* so is synchronizing at commit points. *)
      eV.(ge_view).(dv_comm) ⊑ dV.(ge_view).(dv_comm).

(** (4) every unmatched pop returns empty *)
Definition stack_unmatched_pop_empty G : Prop :=
  ∀ e eV, G.(Es) !! e = Some eV →
    is_maybe_pop eV.(ge_event) →
    e ∉ (elements G.(com)).*2 →
    eV.(ge_event) = EmpPop.

(** (5) a pop with a previous unmatched push cannot return empty. *)
Definition stack_empty_unmatched_push G : Prop :=
  ∀ o oV, G.(Es) !! o = Some oV → oV.(ge_event) = EmpPop →
    ∀ u, u ∈ oV.(ge_lview) → ¬ unmatched_push G u.

(* If u1 (push1) happens-before u2 (push2), and o1 (pop1) happens-before
    o2 (pop2), then u2 cannot happen-before o1, because if that were the case,
    by LIFO, o1 cannot happen-before o2.
    This is well-bracketted. The possible cases are :
    - [u1 o1] [u2 o2]
    - [u1 [u2 o2] o1]
    The impossible case that is mentioned here: [u1 [u2 o1] o2]. *)
Definition stack_LIFO G : Prop :=
  ∀ u1 o1 oV1 u2 o2 uV2 oV2,
    (u1, o1) ∈ G.(com) → (u2, o2) ∈ G.(com) →
    u1 ≠ u2 → (* e1 and e2 are distinct *)
    G.(Es) !! o1 = Some oV1 → G.(Es) !! u2 = Some uV2 → G.(Es) !! o2 = Some oV2 →
    u1 ∈ uV2.(ge_lview) → (* u1 happens-before u2 *)
    o1 ∈ oV2.(ge_lview) → (* o1 happens-before o2 *)
    u2 ∉ oV1.(ge_lview) (* u2 doesn't happen-before o1. Stronger: o1 happens-before u1. *)
    .

(* Unpopped item u2 cannot be in between push-pop pairs (u1,o1).
  That is, it cannot be the case that [u1 [u2] o1]. *)
Definition stack_LIFO_empty G : Prop :=
  ∀ u1 o1 oV1 u2 uV2,
    (u1, o1) ∈ G.(com) →
    G.(Es) !! o1 = Some oV1 → G.(Es) !! u2 = Some uV2 →
    u1 ∈ uV2.(ge_lview) → (* u1 happens-before u2 *)
    u2 ∈ oV1.(ge_lview) → (* u2 happen-before o1 *)
    ¬ unmatched_push G u2.


(** * Basic Consistency *)
(* This is as close as possible to Yacovet's Stack Consistency (§5.4).
  Note that Yacovet also includes a Weak Stack Spec (§5.5) that only has
  [try_push] and [try_pop] operations, but not [push] and [pop] operations.
  The consistency condition of the Weak Stack Spec also does NOT include the
  condition (5) below for empty pops. We do NOT encode the Weak Stack Spec here. *)
Record StackConsistent G : Prop := mkStackConsistent {
  (* The first one is our side condition *)
  stk_cons_ps_non_zero : (* 0 is used for Empty Pop *) stack_positive_value G.(Es) ;

  (* (1) at most 1 Constructor event: we currently don't have initialization events *)
  stk_cons_matches :
  (* (2) There can only be so edges between matching Pushs and Pops *)
    stack_matches_value G ;
  stk_cons_com_functional :
  (* (3) com and com^-1 are functional: *)
    functional_pair G.(com) ;
  stk_cons_empty_pop :
  (* (4) every unmatched pop returns empty: *)
    stack_unmatched_pop_empty G ;
  stk_cons_non_empty :
  (* (5) a pop with a previous unmatched push cannot return empty.
    So our Pop result depends on whether our current view includes an unmatched Push *)
    stack_empty_unmatched_push G ;
  stk_cons_so_com :
  (* (6) so and com agree *)
    G.(so) = G.(com) ;
  stk_cons_LIFO :
  (* (7) pushed values cannot be popped out of order *)
    stack_LIFO G ;

  (* The last one prevents circles in eco : eco ⊆ xo *)
  stk_cons_mo_hb : graph_xo_eco G.(Es) ;
}.

(** ExtendedStackConsistency adds more physical/logical order information. *)
Record ExtendedStackConsistent G : Prop := mkExtendedStackConsistent {
  exstk_cons_dview_push : (* push is releasing *) stack_push_releasing G.(Es) ;
  exstk_cons_dview_push_order : (* pushes are ordered by CAS *) stack_push_CAS_order G.(Es) ;
  exstk_cons_dview_pop : (* pop is acquiring *) stack_pop_acquiring G.(Es) ;

  (* (1)-(7) Stack spec from POPL'19 Library Correctness paper *)
  exstk_cons_basic :> StackConsistent G ;

  (* The last one is our strengthening that holds for stronger implementation. *)
  exstk_cons_LIFO_b :
    stack_LIFO_empty G ;
}.

Definition basic_stack_spec Σ `{!noprolG Σ, !inG Σ (graphR sevent)}
  := stack_spec Σ StackConsistent.

Definition extended_stack_spec Σ `{!noprolG Σ, !inG Σ (graphR sevent)}
  := stack_spec Σ ExtendedStackConsistent.

Program Definition extended_to_basic_stack_spec
  Σ `{!noprolG Σ, !inG Σ (graphR sevent)}
  (stk : extended_stack_spec Σ) : basic_stack_spec Σ := {|
    StackInv_Objective := stk.(StackInv_Objective) ;
    StackInv_Timeless  := stk.(StackInv_Timeless) ;
    StackInv_Fractional := stk.(StackInv_Fractional) ;
    StackInv_AsFractional := stk.(StackInv_AsFractional) ;

    StackInv_graph_master_acc := stk.(StackInv_graph_master_acc) ;
    StackInv_graph_snap := stk.(StackInv_graph_snap) ;
    StackInv_agree := stk.(StackInv_agree) ;

    StackLocal_Persistent := stk.(StackLocal_Persistent) ;
    StackLocal_graph_snap := stk.(StackLocal_graph_snap) ;
    StackLocal_union := stk.(StackLocal_union) ;
    StackLocal_upgrade := stk.(StackLocal_upgrade) ;

    (* StackLocalLite is the light version of StackLocal that is Timeless *)
    StackLocalLite_Timeless := stk.(StackLocalLite_Timeless) ;
    StackLocalLite_Persistent := stk.(StackLocalLite_Persistent) ;
    StackLocalLite_from := stk.(StackLocalLite_from) ;
    StackLocalLite_to := stk.(StackLocalLite_to) ;
    StackLocalLite_graph_snap := stk.(StackLocalLite_graph_snap) ;
    StackLocalLite_upgrade := stk.(StackLocalLite_upgrade) ;

    (* operations specs *)
    new_stack_spec := stk.(new_stack_spec) ;
    try_push_spec := stk.(try_push_spec) ;
    push_spec := stk.(push_spec) ;
    try_pop_spec := stk.(try_pop_spec) ;
    pop_spec := stk.(pop_spec) ;
  |}.
Next Obligation.
  iIntros "* SI".
  by iDestruct (StackInv_StackConsistent with "SI") as%?%exstk_cons_basic.
Qed.

(** Some properties *)
Lemma unmatched_push_mono G G' eid :
  G ⊑ G' → is_Some (G.(Es) !! eid) → unmatched_push G' eid → unmatched_push G eid.
Proof.
  intros LeG' [? Eq] [[v Eq'] FA].
  destruct (G'.(Es) !! eid) as [[? V]|] eqn:Eq''; [|done]. simpl in Eq'.
  rewrite (prefix_lookup_Some _ _ _ _ Eq) in Eq''; [|apply LeG']. simplify_eq.
  split.
  - exists v. by rewrite Eq.
  - intros e' ?. apply (FA e'); by apply LeG'.
Qed.

Lemma StackConsistent_empty : StackConsistent ∅.
Proof. done. Qed.

Lemma ExtendedStackConsistent_empty : ExtendedStackConsistent ∅.
Proof. done. Qed.


Lemma stack_positive_value_insert E eV :
  (∀ v', eV.(ge_event) = Push v' → 0 < v') →
  stack_positive_value E → stack_positive_value (E ++ [eV]).
Proof.
  intros Posv SE e eV' v' [Eq1|[-> <-]]%lookup_app_1; [by eapply SE|by apply Posv].
Qed.

Lemma stack_matches_value_insert G egV :
  let G' := graph_insert_event egV G in
  stack_matches_value G → stack_matches_value G'.
Proof.
  intros G' SM e d InC.
  set e' := length G.(Es).
  have NI: ∀ e1 e2, (e1, e2) ∈ G'.(com) → e1 ≠ e' ∧ e2 ≠ e'.
  { move => ?? /(gcons_com_included G) [/= ??]. lia. }
  destruct (NI _ _ InC). do 2 (rewrite lookup_app_1_ne; [|done]). by apply SM.
Qed.

Lemma stack_unmatched_pop_empty_insert G egV :
  let G' := graph_insert_event egV G in
  ((∃ v, egV.(ge_event) = Push v) ∨ egV.(ge_event) = EmpPop) →
  stack_unmatched_pop_empty G → stack_unmatched_pop_empty G'.
Proof.
  intros G' EM SE.
  intros ?? [?|[-> <-]]%lookup_app_1; [by eapply SE|].
  by destruct EM as [[? ->]| ->].
Qed.

Lemma stack_empty_unmatched_push_insert G egV :
  let G' := graph_insert_event egV G in
  eventgraph_consistent G →
  (egV.(ge_event) = EmpPop → ∀ u, u ∈ egV.(ge_lview) → ¬ unmatched_push G' u) →
  stack_empty_unmatched_push G → stack_empty_unmatched_push G'.
Proof.
  intros G' EGCs UU SU o oV [Eqo|[-> <-]]%lookup_app_1; [|done].
  intros EqP u Inu UM'. apply (SU _ _ Eqo EqP u Inu).
  revert UM'. apply unmatched_push_mono; [apply graph_insert_event_eq|].
  by apply (egcons_logview_closed _ EGCs _ _ Eqo _ Inu).
Qed.

Lemma stack_LIFO_insert G egV :
  let G' := graph_insert_event egV G in
  stack_LIFO G → stack_LIFO G'.
Proof.
  intros G' LF.
  set e' := length G.(Es).
  have NI: ∀ e1 e2, (e1, e2) ∈ G.(com) → e1 ≠ e' ∧ e2 ≠ e'.
  { move => ?? /(gcons_com_included G) [/= ??]. lia. }
  intros u1 o1 oV1 u2 o2 uV2 oV2 In1 In2.
  destruct (NI _ _ In1), (NI _ _ In2).
  do 3 (rewrite lookup_app_1_ne; [|done]). by apply LF.
Qed.

Lemma stack_LIFO_empty_insert G egV :
  let G' := graph_insert_event egV G in
  eventgraph_consistent G →
  stack_LIFO_empty G → stack_LIFO_empty G'.
Proof.
  intros G' EGCs LF.
  set e' := length G.(Es).
  have NI: ∀ e1 e2, (e1, e2) ∈ G.(com) → e1 ≠ e' ∧ e2 ≠ e'.
  { move => ?? /(gcons_com_included G) [/= ??]. lia. }
  intros u1 o1 oV1 u2 uV2 In1. destruct (NI _ _ In1).
  rewrite lookup_app_1_ne; [|done]. intros Eqo1 Equ2 InuV2 InoV1 UM.
  rewrite lookup_app_1_ne in Equ2; last first.
  { intros ->.
    apply (egcons_logview_closed _ EGCs _ _ Eqo1), lookup_lt_is_Some in InoV1.
    lia. }
  apply (LF _ _ _ _ _ In1 Eqo1 Equ2 InuV2 InoV1).
  apply (unmatched_push_mono _ G'); [apply graph_insert_event_eq|by eexists|done].
Qed.


Lemma stack_matches_value_insert_edge G e1 egV
  (Lt: bool_decide (e1 < length G.(Es))%nat) eV v :
  let G' := graph_insert_edge e1 egV G Lt in
  G.(Es) !! e1 = Some eV → eV.(ge_event) = Push v → egV.(ge_event) = Pop v →
  eV.(ge_view).(dv_comm) ⊑ egV.(ge_view).(dv_comm) →
  stack_matches_value G → stack_matches_value G'.
Proof.
  intros G' Eqe1 Eqps Eqpp LeV SM e d.
  set e' := length G.(Es).
  have NI: ∀ e1 e2, (e1, e2) ∈ G.(com) → e1 ≠ e' ∧ e2 ≠ e'.
  { move => ?? /(gcons_com_included G) [/= ??]. lia. }
  rewrite elem_of_union elem_of_singleton => [[[-> ->]|InG]].
  - split. { clear -Lt. by apply bool_decide_unpack in Lt. }
    exists eV, egV, v. split; last split; [..|done].
    + by apply lookup_app_l_Some.
    + by apply lookup_app_1_eq.
  - destruct (NI _ _ InG). do 2 (rewrite lookup_app_1_ne; [|done]). by apply SM.
Qed.

Lemma stack_unmatched_pop_empty_insert_edge G e1 egV
  (Lt: bool_decide (e1 < length G.(Es))%nat) :
  let G' := graph_insert_edge e1 egV G Lt in
  stack_unmatched_pop_empty G → stack_unmatched_pop_empty G'.
Proof.
  intros G' EM.
  intros ??. rewrite /= elements_union_singleton; last first.
  { move => /(gcons_com_included G) [_ /=]. lia. }
  intros [Eqe|[-> <-]]%lookup_app_1 MB.
  - intros NIne. apply (EM _ _ Eqe MB). intros NIn. apply NIne. by right.
  - rewrite /= elem_of_cons. clear; naive_solver.
Qed.

Lemma stack_empty_unmatched_push_insert_edge G e1 egV
  (Lt: bool_decide (e1 < length G.(Es))%nat) :
  let G' := graph_insert_edge e1 egV G Lt in
  eventgraph_consistent G →
  egV.(ge_event) ≠ EmpPop →
  stack_empty_unmatched_push G → stack_empty_unmatched_push G'.
Proof.
  intros G' EGCs NE SU o oV [Eqo|[-> <-]]%lookup_app_1; [|done].
  intros EqP u Inu UM'. apply (SU _ _ Eqo EqP u Inu).
  revert UM'. apply unmatched_push_mono; [apply graph_insert_edge_eq|].
  by apply (egcons_logview_closed _ EGCs _ _ Eqo _ Inu).
Qed.

Lemma stack_com_functional_insert_edge G e egV
  (Lt: bool_decide (e < length G.(Es))%nat) :
  let G' := graph_insert_edge e egV G Lt in
  (∀ id, (e, id) ∉ G.(com)) →
  functional_pair G.(com) → functional_pair G'.(com).
Proof.
  intros G' UPp CO.
  set e' := length G.(Es).
  have NI: ∀ e1 e2, (e1, e2) ∈ G.(com) → e1 ≠ e' ∧ e2 ≠ e'.
  { move => ?? /(gcons_com_included G) [/= ??]. lia. }
  split.
  - intros [e1 d1] [e2 d2]. rewrite 2!elem_of_union 2!elem_of_singleton /=.
    move => [[-> ->]|InG1] [[-> ->]|InG2] //.
    + intros ?. subst e2. exfalso. move : InG2. by apply UPp.
    + intros ?. subst e1. exfalso. move : InG1. by apply UPp.
    + move : InG1 InG2. by apply CO.
  - (* 3b *)
    intros [e1 d1] [e2 d2]. rewrite 2!elem_of_union 2!elem_of_singleton /=.
    move => [[-> ->]|InG1] [[-> ->]|InG2] //.
    + intros ?. subst d2. exfalso. move : (NI _ _ InG2). clear; lia.
    + intros ?. subst d1. exfalso. move : (NI _ _ InG1). clear; lia.
    + move : InG1 InG2. by apply CO.
Qed.

Lemma stack_LIFO_insert_edge G e egV
  (Lt: bool_decide (e < length G.(Es))%nat) eV v :
  let G' := graph_insert_edge e egV G Lt in
  G.(Es) !! e = Some eV → eV.(ge_event) = Push v →
  (∀ u1 o1 oV1, (u1, o1) ∈ G.(com) → (u1 < e < o1)%nat →
    G.(Es) !! o1 = Some oV1 →
    u1 ∈ eV.(ge_lview) → e ∈ oV1.(ge_lview) → o1 ∈ egV.(ge_lview) → False) →
  eventgraph_consistent G → graph_xo_eco G.(Es) → stack_matches_value G →
  stack_LIFO G → stack_LIFO G'.
Proof.
  intros G' Eqe Eqv LF' EGCs MO MA LF u1 o1 oV1 u2 o2 uV2 oV2.
  rewrite 2!elem_of_union 2!elem_of_singleton.
  intros In1 In2 NEqu Eqo1 Equ2 Eqo2.
  set e' := length G.(Es).
  have NI: ∀ e1 e2, (e1, e2) ∈ G.(com) → e1 ≠ e' ∧ e2 ≠ e'.
  { move => ?? /(gcons_com_included G) [/= ??]. lia. }
  have NEqe' : e ≠ e'.
  { clear -Lt. apply bool_decide_unpack in Lt. intros ->. lia. }
  destruct In1 as [Eq1|In1]; [apply pair_inj in Eq1 as [-> ->]|];
    (destruct In2 as [Eq2|In2]; [apply pair_inj in Eq2 as [-> ->]|]); [done|..].
  - rewrite lookup_app_1_eq in Eqo1. inversion Eqo1. clear Eqo1. subst oV1.
    destruct (NI _ _ In2). rewrite lookup_app_1_ne in Eqo2; [|done].
    intros _ Lt'%(egcons_logview_closed _ EGCs _ _ Eqo2)%lookup_lt_is_Some _.
    clear -Lt'; lia.
  - rewrite lookup_app_1_ne in Eqo1; [|apply (NI _ _ In1)].
    rewrite lookup_app_1_eq in Eqo2. apply Some_inj in Eqo2 as <-.
    rewrite lookup_app_1_ne in Equ2; [|done].
    rewrite Eqe in Equ2. apply Some_inj in Equ2 as <-.
    intros Inu1 InM Ino1.
    assert (Leu1 := MO _ _ _ Eqe Inu1). assert (Leo1 := MO _ _ _ Eqo1 Ino1).
    assert (NEqo1: e ≠ o1).
    { clear -MA Eqe Eqv In1. intros <-.
      specialize (MA _ _ In1) as [_ (_ & dV1 & v' & _ & EqdV1 & _ & Eqv' & _)].
      rewrite Eqe in EqdV1. apply Some_inj in EqdV1 as <-.
      by rewrite Eqv in Eqv'. }
    apply (LF' _ _ oV1 In1); [ |done..]. split; lia.
  - destruct (NI _ _ In1), (NI _ _ In2).
    rewrite lookup_app_1_ne in Eqo1; [|done].
    rewrite lookup_app_1_ne in Equ2; [|done].
    rewrite lookup_app_1_ne in Eqo2; [|done].
    revert In1 In2 NEqu Eqo1 Equ2 Eqo2. by apply LF.
Qed.
