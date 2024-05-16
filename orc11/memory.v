From stdpp Require Export gmap finite tactics sorting.
From orc11 Require Export view value.

Require Import stdpp.options.

Section Memory.

  Context `{!LocFacts loc} `{CVAL: Countable VAL}.

  Notation val := (@val VAL).
  Notation view := (@view loc _).
  Implicit Types (V: view).

  (** Base messages do not have loc and to fields *)
  Record baseMessage :=
    mkBMes { mval : val;
             mrel : option view; }.

  Global Instance baseMessage_inhabited: Inhabited baseMessage
    := populate (mkBMes AVal None).
  Definition _bMsg_to_tuple (m : baseMessage) : _
      := (mval m, mrel m).
  Definition _tuple_to_bMsg (m : _) : baseMessage :=
    match m with
    | (v, R) => mkBMes v R
    end.

  Global Instance baseMsg_dec_eq : EqDecision baseMessage.
  Proof using All. solve_decision. Qed.

  Global Instance baseMsg_countable : Countable baseMessage.
  Proof. refine (inj_countable _bMsg_to_tuple (Some ∘ _tuple_to_bMsg) _); by intros []. Qed.

  Record baseMessage_le m1 m2 :=
    mkbMsgSqSubsetEq {
      bMsg_sqsubseteq_mval  : m1.(mval) = m2.(mval)  ;
      bMsg_sqsubseteq_mrel  : m1.(mrel) ⊑ m2.(mrel);
    }.

  Global Instance baseMessage_sqsubseteq : SqSubsetEq baseMessage := baseMessage_le.

  Global Instance baseMessage_sqsubseteq_po :
    PartialOrder ((⊑) : SqSubsetEq baseMessage).
  Proof.
    constructor; [constructor|]; [done|..].
    - intros [][][] [][]. simpl in *.
      constructor; [by subst|by etrans].
    - intros [][] [][]. simpl in *. subst.
      f_equal. by apply : (anti_symm (⊑)).
  Qed.


  (* ======================================================================== *)
  (** Cells are containers of messages per location,
      defined as maps from time to base messages *)
  Notation cell := (gmap time baseMessage) (only parsing).

  Implicit Types (t: time) (l: loc) (m: baseMessage) (C: cell).

  (* Extension on Cell that ONLY extends views *)
  (* This is different from the cell extension that adds new messages *)
  (* Cell le is use to prove that the machine behavior is monotone w.r.t. views *)
  Definition cell_le C1 C2 :=
    ∀ (t : time),
      option_Forall2 (A:=baseMessage) (⊑) (C1 !! t) (C2 !! t).
  (* We do not declare an SqSubsetEq instance for cells, because it
     would conflict with the default one from gmap. *)

  Global Instance cell_le_partial_order : PartialOrder cell_le.
  Proof.
    constructor; [constructor|].
    - intros ??. by destruct lookup; constructor.
    - intros ??? H1 H2 t. specialize (H1 t).
      destruct (H2 t); inversion_clear H1; constructor. by etrans.
    - intros ?? H1 H2. apply map_eq=>t.
      eapply (anti_symm (⊑)); [generalize (H1 t)|generalize (H2 t)];
        by do 2 case: (_!!t)=>[?|]; inversion 1.
  Qed.

  Lemma cell_le_non_empty (C1 C2: cell) (LE: cell_le C1 C2): C1 ≠ ∅ ↔ C2 ≠ ∅.
  Proof.
    split => NE;
    destruct (map_choose _ NE) as [te [me Eqe]];
    move : (LE te); rewrite Eqe; inversion 1 as [?? Eq1 Eq2 Eq3|] => EQ; by subst.
  Qed.

  Lemma cell_le_singleton (C: cell) t m (LE: cell_le {[t := m]} C):
    ∃ m', C = {[t := m']}.
  Proof.
    move : (LE t). rewrite lookup_singleton. inversion 1 as [? m'|]; subst.
    exists m'. apply map_eq => t'.
    case (decide (t' = t)) => [->|?].
    - by rewrite lookup_insert.
    - move : (LE t'). do 2 (rewrite lookup_insert_ne ; last done).
      rewrite lookup_empty. by inversion 1.
  Qed.

  Lemma cell_le_dom (C1 C2: cell) (LE: cell_le C1 C2):
    dom C1 ≡ dom C2.
  Proof.
    move => t. rewrite 2!elem_of_dom. specialize (LE t).
    split; move => [? Eq]; rewrite Eq in LE; inversion LE; by eexists.
  Qed.

  (** Cell operations *)
  (* CELL ADDINS ------------------------------------------------------------ *)
  Inductive cell_addins to m C: cell → Prop :=
    CellAddIns (DISJ: C !! to = None) : cell_addins to m C (<[to := m]> C).
  Lemma lookup_cell_addins_fresh to m C C'
    (ADD: cell_addins to m C C') :
    C !! to = None.
  Proof. by inversion ADD. Qed.

  Lemma lookup_cell_addins_new to m C C' (ADD: cell_addins to m C C') :
    C' !! to = Some m.
  Proof. inversion ADD. by rewrite lookup_insert. Qed.

  Lemma lookup_cell_addins_old_eq t t' m C C'
    (ADD: cell_addins t m C C') (NEq: t ≠ t'):
    C !! t' = C' !! t'.
  Proof. inversion ADD. by rewrite lookup_insert_ne. Qed.

  Lemma cell_addins_subset t m C C' (ADD: cell_addins t m C C'):
    C ⊆ C'.
  Proof.
    inversion ADD. move => t'.
    case (decide (t' = t)) => [->|?];
      [rewrite lookup_insert DISJ //|rewrite lookup_insert_ne //; by case lookup].
  Qed.


  (** Cell deallocation ----------------------------------------------------- *)

  Definition cell_max (C: cell) := gmap_top (flip (⊑)) C.

  Definition cell_min (C: cell) := gmap_top (⊑) C.

  Definition cell_deallocated (C: cell) : Prop :=
    match cell_max C with
    | None => False
    | Some (_,m) => m.(mval) = DVal
    end.

  Global Instance cell_deallocated_dec: ∀ C, Decision (cell_deallocated C).
  Proof using All.
    move => C. rewrite /cell_deallocated. destruct (cell_max C); solve_decision.
  Qed.

  Lemma cell_deallocated_correct1 C:
    cell_deallocated C →
    ∃ (t: time) m,
        C !! t = Some m
     ∧ m.(mval) = DVal
     ∧ ∀ (t': time), t' ∈ (dom C) → (t' ≤ t)%positive.
  Proof.
    rewrite /cell_deallocated.
    destruct (cell_max C) eqn:Heqo; last done.
    case_match => Eqv.
    eexists. eexists. repeat split; eauto.
    - apply (gmap_top_lookup (flip (⊑))). by eauto.
    - apply (gmap_top_top _ _ _ _ Heqo).
  Qed.

  Lemma cell_deallocated_correct2 C:
    (∃ (t: time) m,
        C !! t = Some m
     ∧ m.(mval) = DVal
     ∧ ∀ (t': time), t' ∈ (dom C) → (t' ≤ t)%positive)
     → cell_deallocated C.
  Proof.
    rewrite /cell_deallocated /cell_max.
    move => [t [m [In [Eq1 Max]]]].
    by rewrite (gmap_top_inv (flip (⊑)) t m).
  Qed.

  Lemma cell_deallocated_neg_insert t m C
    (ALLOC: ¬ cell_deallocated C)
    (ND: m.(mval) ≠ DVal) :
    ¬ cell_deallocated (<[t := m]> C).
  Proof.
    move => /cell_deallocated_correct1 [t' [m' [Eqm' [EqD MAX]]]].
    move : Eqm'.
    case (decide (t' = t)) => [Eq|NEq];
      [subst t'; rewrite lookup_insert|rewrite lookup_insert_ne; last done].
    - inversion 1. by subst.
    - move => In. apply ALLOC.
      apply cell_deallocated_correct2.
      exists t', m'. repeat split; auto.
      move => ??. apply MAX. rewrite dom_insert elem_of_union. by right.
  Qed.

  Lemma cell_deallocated_neg_singleton t m
    (ND: m.(mval) ≠ DVal):
    ¬ cell_deallocated {[t := m]}.
  Proof.
    move => /cell_deallocated_correct1
            [? [? [/lookup_singleton_Some [_ ?] [? _]]]].
    by subst.
  Qed.

  Lemma cell_deallocated_singleton t m
    (ND: m.(mval) = DVal):
    cell_deallocated {[t := m]}.
  Proof.
    apply cell_deallocated_correct2. exists t, m.
    rewrite lookup_insert. repeat split; first done.
    move => t'. by rewrite dom_singleton elem_of_singleton => ->.
  Qed.

  (** Allocation invariant for cells ---------------------------------------- *)
  Definition cell_alloc_inv C :=
    ∀ t m, (C !! t = Some m ∧ m.(mval) = AVal) ↔ cell_min C = Some (t, m).

  Lemma cell_addins_alloc_min t m C C' tm mm
    (ADD: cell_addins t m C C')
    (EQ: cell_min C = Some (tm,mm))
    (Le: (tm ≤ t)%positive):
    cell_min C' = Some (tm,mm).
  Proof.
    inversion_clear ADD.
    apply (gmap_top_insert_ne_old _ _ _ _ _ _ EQ); last done.
    move => ?. subst tm.
    apply gmap_top_lookup in EQ; eauto with typeclass_instances.
    by rewrite EQ in DISJ.
  Qed.

   Lemma cell_addins_alloc_min_2 t m C C' tm mm
    (ADD: cell_addins t m C C')
    (EQ: cell_min C = Some (tm,mm))
    (Le: (tm ≤ t)%positive):
    cell_min C' = cell_min C.
  Proof.
    rewrite EQ. apply (cell_addins_alloc_min _ _ _ _ _ _ ADD EQ Le).
  Qed.

  Lemma cell_addins_alloc_empty t m C'
    (ADD: cell_addins t m ∅ C') (ISA: m.(mval) = AVal) :
    cell_alloc_inv C'.
  Proof.
    inversion ADD. rewrite insert_empty.
    move => t' m'. rewrite /cell_min gmap_top_singleton lookup_singleton_Some.
    naive_solver.
  Qed.

  Lemma cell_addins_alloc_inv t m C C'
    (ADD: cell_addins t m C C')
    (AINV: cell_alloc_inv C)
    (EQ: ∃ t', is_Some (C !! t') ∧ (t' ≤ t)%positive)
    (NAV: m.(mval) ≠ AVal) :
    cell_alloc_inv C'.
  Proof.
    destruct EQ as [t' [[m' Eqt'] Le']].
    destruct (gmap_top_nonempty_2 Pos.le _ _ C Eqt') as [tm [mm Eqmm]].
    have Le: (tm ≤ t)%positive.
    { etrans; last apply Le'.
      apply (gmap_top_top _ _ _ _ Eqmm), elem_of_dom. by eexists. }
    have Eqmm2: cell_min C' = cell_min C
      by apply (cell_addins_alloc_min_2 _ _ _ _ _ _ ADD Eqmm).
    move => t0 m0.
    rewrite Eqmm2 -AINV. inversion ADD. subst.
    case (decide (t0 = t)) => [Eq|NEq];
      [rewrite Eq lookup_insert|by rewrite lookup_insert_ne].
    split; first by move => [[<-] ?]. rewrite DISJ => [[//]].
  Qed.


  Lemma cell_le_alloc_inv_min (C1 C2: cell) (LE: cell_le C1 C2):
    (∀ t m, C1 !! t = Some m ∧ mval m = AVal → cell_min C1 = Some (t, m)) ↔
    (∀ t m, C2 !! t = Some m ∧ mval m = AVal → cell_min C2 = Some (t, m)).
  Proof.
    have DOM := cell_le_dom _ _ LE.
    split => AINV t m; specialize (LE t);
    move => [Eqt Eqv];
    rewrite /cell_le Eqt in LE; inversion LE as [m1 m2 Le Eq1 Eq2|]; subst;
    inversion Le as [Eqv2 _]; rewrite Eqv in Eqv2;
    apply gmap_top_inv; eauto with typeclass_instances.
    - have MIN : cell_min C1 = Some (t, m1) by apply AINV.
      move => ?. rewrite -DOM.
      by apply (gmap_top_top _ _ _ _ MIN).
    - have MIN : cell_min C2 = Some (t, m2) by apply AINV.
      move => ?. rewrite DOM.
      by apply (gmap_top_top _ _ _ _ MIN).
  Qed.

  Lemma cell_le_alloc_inv (C1 C2: cell) (LE: cell_le C1 C2):
    cell_alloc_inv C1 ↔ cell_alloc_inv C2.
  Proof.
    have DOM := cell_le_dom _ _ LE.
    split => AINV t m; specialize (LE t);
      rewrite gmap_top_equiv; split; move => [Eqt Hv]; (split; [done|]);
      rewrite /cell_le Eqt in LE; inversion LE as [m1 m2 Le Eq1 Eq2|]; subst;
      inversion Le as [Eqv _].
    - rewrite Hv in Eqv. move => ?. rewrite -DOM.
      have MIN : cell_min C1 = Some (t, m1) by apply AINV.
      by apply (gmap_top_top _ _ _ _ MIN).
    - rewrite -Eqv.
      have MIN : cell_min C1 = Some (t, m1).
      { apply gmap_top_inv; eauto with typeclass_instances.
        move => ?. rewrite DOM. by apply Hv. }
      by apply AINV in MIN as [??].
    - rewrite Hv in Eqv. move => ?. rewrite DOM.
      have MIN : cell_min C2 = Some (t, m2) by apply AINV.
      by apply (gmap_top_top _ _ _ _ MIN).
    - rewrite Eqv.
      have MIN : cell_min C2 = Some (t, m2).
      { apply gmap_top_inv; eauto with typeclass_instances.
        move => ?. rewrite -DOM. by apply Hv. }
      by apply AINV in MIN as [??].
  Qed.


  (** Deallocation invariant for cells -------------------------------------- *)
  Definition cell_dealloc_inv C :=
    ∀ t m, C !! t = Some m → m.(mval) = DVal → cell_max C = Some (t,m).

  Lemma cell_addins_nDVal_dealloc_inv t m C C'
    (ADD: cell_addins t m C C')
    (EQ: ∀ t m, C !! t = Some m → m.(mval) ≠ DVal)
    (NDV: m.(mval) ≠ DVal) :
    cell_dealloc_inv C'.
  Proof.
    inversion_clear ADD.
    move => t' m'.
    case (decide (t' = t)) => [->|NEq];
      [rewrite lookup_insert|rewrite lookup_insert_ne; last done];
      [by move => [<-]|by move => /EQ].
  Qed.

  Lemma cell_addins_dealloc_inv t m C C'
    (ADD: cell_addins t m C C')
    (EQ: ∀ t' m', C !! t' = Some m' → m'.(mval) ≠ DVal ∧ (t' < t)%positive) :
    cell_dealloc_inv C'.
  Proof using All.
    inversion_clear ADD.
    move => t0 m0.
     case (decide (t0 = t)) => [->|NEq];
      [rewrite lookup_insert|rewrite lookup_insert_ne; last done];
      [move => [<-] EqD|by move => /EQ []].
    case (decide (C = ∅)) => [->|NEMP];
      first by (apply gmap_top_singleton; eauto with typeclass_instances).
    apply (gmap_top_nonempty (flip (⊑))) in NEMP as [tm [mm Eqmm]].
    apply (gmap_top_insert_new _ _ _ _ _ _ Eqmm).
    apply gmap_top_lookup, EQ in Eqmm as [_ Lt]; eauto with typeclass_instances.
    by apply Pos.lt_le_incl.
  Qed.

  Lemma cell_le_alloc_inv_max (C1 C2: cell) (LE: cell_le C1 C2):
    (∀ t m, C1 !! t = Some m ∧ mval m = DVal → cell_max C1 = Some (t, m)) ↔
    (∀ t m, C2 !! t = Some m ∧ mval m = DVal → cell_max C2 = Some (t, m)).
  Proof.
    have DOM := cell_le_dom _ _ LE.
    split => AINV t m; specialize (LE t);
    move => [Eqt Eqv];
    rewrite /cell_le Eqt in LE; inversion LE as [m1 m2 Le Eq1 Eq2|]; subst;
    inversion Le as [Eqv2 _]; rewrite Eqv in Eqv2;
    apply gmap_top_inv; eauto with typeclass_instances.
    - have MIN : cell_max C1 = Some (t, m1) by apply AINV.
      move => ?. rewrite -DOM.
      by apply (gmap_top_top _ _ _ _ MIN).
    - have MIN : cell_max C2 = Some (t, m2) by apply AINV.
      move => ?. rewrite DOM.
      by apply (gmap_top_top _ _ _ _ MIN).
  Qed.

  (* ======================================================================== *)
  (** Memory are maps from locations to cells.
      To preserve leibniz equality, however, we represent them as maps from
      (loc * time) to baseMessage. *)
  Definition memory := gmap (loc * time) baseMessage.

  Implicit Types (M: memory).

  (** Lookup cells from memory *)
  Definition memory_cell_lookup (l : loc) (M : memory) : cell :=
    default ∅ (gmap_curry M !! l).
  Notation "M !!c l" := (memory_cell_lookup l M) (at level 20) : stdpp_scope.

  Global Instance memory_loc_dom : Dom memory (gset loc) :=
    λ M, dom (gmap_curry M).

  Lemma memory_lookup_cell M l t :
    M !! (l,t) = (M !!c l) !! t.
  Proof.
    rewrite /memory_cell_lookup -lookup_gmap_curry.
    case: (gmap_curry M !! l)=>//.
  Qed.

  Lemma memory_loc_not_elem_of_dom l M :
    l ∉ dom M ↔ M !!c l = ∅.
  Proof.
    rewrite /dom /memory_loc_dom elem_of_dom -eq_None_not_Some map_eq_iff
            lookup_gmap_curry_None. apply forall_proper=>t.
    by rewrite memory_lookup_cell lookup_empty.
  Qed.

  Lemma memory_loc_elem_of_dom l M :
    l ∈ dom M ↔ M !!c l ≠ ∅.
  Proof.
    rewrite -memory_loc_not_elem_of_dom. split; [by auto|]. by apply dec_stable.
  Qed.

  (** Insert cells to memory  *)
  Global Instance memory_cell_insert : Insert loc cell memory :=
    λ l C M, gmap_uncurry (<[l:=C]>(gmap_curry M)).

  Lemma memory_uncurry_lookup_insert l C M (NE: C ≠ ∅) :
    gmap_curry (<[l:=C]>M) !! l = Some C.
  Proof.
    rewrite /insert /memory_cell_insert /=.
    rewrite gmap_curry_uncurry_non_empty.
    - by rewrite lookup_insert.
    - move => i x.
      case (decide (i = l)) => [->|?].
      + by rewrite lookup_insert => [[<-]].
      + rewrite lookup_insert_ne; last done. by apply gmap_curry_non_empty.
  Qed.

  Lemma memory_uncurry_lookup_insert_ne l l' C M (NE: l ≠ l') (NE2: C ≠ ∅):
    gmap_curry (<[l:=C]>M) !! l' = gmap_curry M !! l'.
  Proof.
    rewrite /insert /memory_cell_insert /=.
    rewrite gmap_curry_uncurry_non_empty.
    - by rewrite lookup_insert_ne.
    - move => i x.
      case (decide (i = l)) => [->|?].
      + by rewrite lookup_insert => [[<-]].
      + rewrite lookup_insert_ne; last done. by apply gmap_curry_non_empty.
  Qed.

  Lemma memory_cell_lookup_insert l C M :
    <[l:=C]>M !!c l = C.
  Proof.
    apply map_eq=>t. rewrite -memory_lookup_cell lookup_gmap_uncurry lookup_insert //.
  Qed.

  Lemma memory_cell_lookup_insert_ne l l' C M :
    l ≠ l' → <[l:=C]>M !!c l' = M !!c l'.
  Proof.
    intros Hll'. apply map_eq=>t.
    rewrite -!memory_lookup_cell lookup_gmap_uncurry lookup_insert_ne //
            lookup_gmap_curry //.
  Qed.

  Lemma memory_cell_insert_insert l C C' M:
    <[l:=C]>(<[l:=C']>M) = <[l:=C]>M.
  Proof.
    apply map_eq=> [[l' t]].
    rewrite !memory_lookup_cell.
    case (decide (l' = l)) => [->|?];
      [by rewrite 2!memory_cell_lookup_insert|
        by do 3 (rewrite memory_cell_lookup_insert_ne; last done)].
  Qed.

  (** Memory closedness *)
  Global Instance closed_view : ElemOf view memory := λ V M,
    ∀ l (t: time), V !!w l = Some t
        → ∃ m (t' : time), (t ≤ t')%positive ∧ M !! (l,t') = Some m.

  Lemma closed_view_memory_fresh_insert_mono l t m (V: view) M
    (In: V ∈ M) (FRESH: M !! (l,t) = None) :
    V ∈ <[l:= <[t:= m]>(M !!c l)]> M.
  Proof.
    move => l' t'; setoid_rewrite memory_lookup_cell;
      (case (decide (l'=l)) => [->|?]); move => Eqt'.
    - rewrite memory_cell_lookup_insert.
      apply In in Eqt'.
      destruct Eqt' as [m' [to' [Eqt' Eql']]].
      exists m', to'. split; first done.
      rewrite lookup_insert_ne; first by rewrite -memory_lookup_cell.
      move => ?. subst to'. by rewrite FRESH in Eql'.
    - rewrite memory_cell_lookup_insert_ne; last done.
      setoid_rewrite <- memory_lookup_cell. by apply In.
  Qed.

  Definition closed_view_opt' (oV: option view) M : Prop :=
    from_option (.∈ M) True oV.

  Global Instance closed_view_opt : ElemOf (option view) memory := closed_view_opt'.

  Lemma closed_view_memory_None V (M: memory) l
    (EMPTY: M !!c l = ∅) (CLOSED: V ∈ M) :
    V !! l = None.
  Proof.
    destruct (V !! l) as [t|] eqn:EqV; last done.
    move/(view_lookup_wp _ _): EqV => EqV.
    apply CLOSED in EqV as (? & ? & _ & Eq).
    by rewrite memory_lookup_cell EMPTY in Eq.
  Qed.

  Definition closed_mem M : Prop :=
    ∀ l to m, M !! (l,to) = Some m → m.(mrel) ∈ M.

  Lemma join_closed_view V1 V2 M (C1: V1 ∈ M) (C2: V2 ∈ M) :
    V1 ⊔ V2 ∈ M.
  Proof.
    move => l to /(view_lookup_of_wp _ _) [[????] [<-]].
    rewrite lookup_union_with.
    move Eq1: (V1 !! l) => [t1|]; move Eq2: (V2 !! l) => [t2|];
    [move => []; cbn..|done].
    - rewrite /join /lat_join /=. case_decide; intros; simplify_eq.
      + by apply C2; simplify_view.
      + by apply C1; simplify_view.
    - intros; simplify_eq. by eapply C1; simplify_view.
    - intros; simplify_eq. by eapply C2; simplify_view.
  Qed.

  Lemma join_opt_closed_view
    (V1 V2: option view) M (C1: V1 ∈ M) (C2: V2 ∈ M) :
    (V1 : option_Lat _) ⊔ V2 ∈ M.
  Proof. destruct V1, V2; auto. by apply join_closed_view. Qed.

  (** Proper instances *)
  Global Instance closed_view_downclosed:
    Proper ((@sqsubseteq view _) ==> (@eq memory) ==> flip impl) (∈).
  Proof.
    move => V1 V2 Sqsubseteq M1 M2 -> In l t Eq2.
    move : Sqsubseteq => /(_ l). move/(view_sqsubseteq _ _ _) => [].
    rewrite Eq2.
    move HT2: (V2 !!w l) => [to|]; cbn; last done.
    cbn => Le.
    destruct (In _ _ HT2) as [m [to' [Le' Eq]]].
    exists m, to'. split=>//. etrans; [apply Le|done].
  Qed.

  Global Instance opt_closed_view_downclosed:
    Proper ((@sqsubseteq (option view) _) ==> (@eq memory) ==> flip impl) (∈).
  Proof.
    move => [?|] [?|] Sqsubseteq ??-> // In.
    eapply (closed_view_downclosed _ _ Sqsubseteq _ _ eq_refl In).
  Qed.

  (* Extension on memory that ONLY extends views *)
  Definition memory_le M1 M2 :=
    ∀ (l : loc),
      option_Forall2 (A:=cell) (cell_le) (gmap_curry M1 !! l) (gmap_curry M2 !! l).
  (* We do not declare an SqSubsetEq instance for memory, because it
     would conflict with the default one from gmap. *)

  Global Instance memory_le_partial_order : PartialOrder memory_le.
  Proof.
    constructor; [constructor|].
    - intros ??. by destruct lookup; constructor.
    - intros ??? H1 H2 l. specialize (H1 l).
      destruct (H2 l); inversion_clear H1; constructor. by etrans.
    - intros ?? H1 H2. apply map_eq=>-[l t].
      rewrite -2!lookup_gmap_curry. f_equal.
      specialize (H1 l). destruct (H2 l); inversion_clear H1; [|done].
      f_equal. by eapply (anti_symm (cell_le)).
  Qed.

  Lemma memory_le_insert_mono M1 M2 l C (LE: memory_le M1 M2) (NE: C ≠ ∅) :
    memory_le (<[l := C]> M1) (<[l := C]> M2).
  Proof.
    move => l'.
    case (decide (l' = l)) => [->|?].
    - by do 2 (rewrite memory_uncurry_lookup_insert; last done).
    - do 2 (rewrite memory_uncurry_lookup_insert_ne; [|done..]). by apply LE.
  Qed.

  Lemma memory_le_lookup_empty M1 M2 l (LE: memory_le M1 M2):
    M1 !!c l = ∅ ↔ M2 !!c l = ∅.
  Proof.
    rewrite /memory_cell_lookup. specialize (LE l).
    destruct (gmap_curry M1 !! l) as [C|] eqn:Eq => /=;
      inversion LE as [? ? NE'|]; last done.
    apply gmap_curry_non_empty in Eq. split; first done.
    by apply (cell_le_non_empty _ _ NE') in Eq.
  Qed.

  Lemma memory_le_lookup_pair M1 M2 l t
    (LE: memory_le M1 M2) :
    (M1 !! (l, t) : option baseMessage) ⊑ M2 !! (l, t).
  Proof.
    specialize (LE l).
    rewrite 2!memory_lookup_cell /memory_cell_lookup.
    destruct (gmap_curry M1 !! l) as [C1|] eqn:Eq1; simpl; last done.
    inversion LE as [? C2 LE'|]. simpl.
    specialize (LE' t). by inversion LE'.
  Qed.

  Lemma memory_le_lookup_pair_2 M1 M2 l t
    (LE: memory_le M1 M2) :
    option_Forall2 (⊑) (M1 !! (l, t) : option baseMessage) (M2 !! (l, t)).
  Proof.
    specialize (LE l).
    rewrite 2!memory_lookup_cell /memory_cell_lookup.
    destruct (gmap_curry M1 !! l) as [C1|] eqn:Eq1;
      destruct (gmap_curry M2 !! l) as [C2|] eqn:Eq2; simpl;
      by inversion LE.
  Qed.

  Lemma memory_le_closed_timenap M1 M2 V
    (LE: memory_le M1 M2):
    V ∈ M1 ↔ V ∈ M2.
  Proof.
    split; move => IN l t /IN [m [t' [Le Eq]]];
    have Le2 := memory_le_lookup_pair_2 _ _ l t' LE;
    rewrite Eq in Le2; inversion Le2; subst;
    by do 2 eexists.
  Qed.

  Lemma memory_le_cell_lookup M1 M2 :
    memory_le M1 M2 ↔
    ∀ l, cell_le (default ∅ (gmap_curry M1 !! l))
            (default ∅ (gmap_curry M2 !! l)).
  Proof.
    split => LE; move => l; specialize (LE l).
    - destruct (gmap_curry M1 !! l) as [C1|]; by inversion LE.
    - destruct (gmap_curry M1 !! l) as [C1|] eqn:EqC1.
      + apply gmap_curry_non_empty in EqC1. simpl in LE.
        destruct (gmap_curry M2 !! l) as [C2|] eqn:EqC2; first by constructor.
        exfalso. by apply (cell_le_non_empty _ _ LE) in EqC1.
      + destruct (gmap_curry M2 !! l) as [C2|] eqn:EqC2; last by constructor.
        apply gmap_curry_non_empty in EqC2.
        exfalso. by apply (cell_le_non_empty _ _ LE) in EqC2.
  Qed.


  Lemma memory_cell_lookup_non_empty M l:
    M !!c l ≠ ∅ ↔ is_Some (gmap_curry M !! l).
  Proof.
    rewrite /memory_cell_lookup.
    destruct (gmap_curry M !! l) as [?|] eqn:Eq; rewrite /= is_Some_alt; [|done].
    by apply gmap_curry_non_empty in Eq.
  Qed.

  Lemma memory_cell_lookup_empty M l:
    M !!c l = ∅ ↔ l ∉ dom M.
  Proof.
    rewrite /memory_cell_lookup (not_elem_of_dom (D:=gset _) (M:=gmap loc)).
    destruct (gmap_curry M !! l) as [?|] eqn:Eq;
      [by apply gmap_curry_non_empty in Eq|done].
  Qed.


  (** Actual message *)
  Record message :=
    mkMsg {
      mloc : loc;
      mto: time;
      mbase : baseMessage;
    }.

  Notation "'<' x → v @ t , R >" :=
  (mkMsg x t (mkBMes v R))
    (at level 20, format "< x → v  @  t ,  R >",
     x at level 21, v at level 21, t at level 21, R at level 21).

  Implicit Type (𝑚: message). (* U1D45A *)

  Record message_le 𝑚1 𝑚2 := {
    message_sqsubseteq_loc : 𝑚1.(mloc)  = 𝑚2.(mloc);
    message_sqsubseteq_to  : 𝑚1.(mto)   = 𝑚2.(mto);
    message_sqsubseteq_base: 𝑚1.(mbase) ⊑ 𝑚2.(mbase);
  }.

  Global Instance message_sqsubseteq : SqSubsetEq message := message_le.

  Global Instance message_sqsubseteq_po :
    PartialOrder ((⊑) : SqSubsetEq message).
  Proof.
    constructor; [constructor|]; [done|..].
    - intros [][][] [???] [???]. simpl in *.
      constructor; [by subst|by subst|by etrans].
    - intros [][] [??Le1][??Le2]. simpl in *. subst.
      f_equal. by apply : (anti_symm (⊑)).
  Qed.

  (** Memory wellformedness *)
  Global Instance message_wf : Wellformed message :=
    λ 𝑚, ∀ V, 𝑚.(mbase).(mrel) = Some V → Some 𝑚.(mto) = V !!w 𝑚.(mloc).

  Definition loc_cell_wf l C := ∀ to m, C !! to = Some m → Wf (mkMsg l to m).

  Record mem_wf' M := {
    mem_wf_closed : closed_mem M;
    mem_wf_loc_cell : ∀ l, loc_cell_wf l (M !!c l);
  }.

  Global Instance mem_wf : Wellformed memory := mem_wf'.

  Lemma mem_insert_max_singleton_wf M l t m
    (WF: Wf M) (WFm: Wf (mkMsg l t m))
    (CLOSED: m.(mrel) ∈ <[l := {[t:=m]}]> M)
    (MAX: ∀ t', is_Some (M !! (l,t')) → (t' < t)%positive) :
    Wf (<[l := {[t:=m]}]> M).
  Proof.
    constructor; move => l1; [move => t1 m1; rewrite memory_lookup_cell|..];
      (case (decide (l1 = l)) => [->|?];
        [rewrite memory_cell_lookup_insert
          |rewrite memory_cell_lookup_insert_ne; last done]);
      [..|by apply WF].
    - by move => /lookup_singleton_Some [? <-].
    - rewrite -memory_lookup_cell => Eq.
      destruct (m1.(mrel)) as [V|] eqn:EQV; last done.
      have INM: V ∈ M.
      { change (Some V ∈ M). rewrite -EQV. by eapply WF. }
      move => l2 t2 Eq2. setoid_rewrite memory_lookup_cell.
      have EE := INM _ _ Eq2.
      case (decide (l2 = l)) => ?;
        [subst l2; rewrite memory_cell_lookup_insert|
          rewrite memory_cell_lookup_insert_ne; last done].
      + exists m,t. split; last by rewrite lookup_insert.
        destruct EE as (?&?&Le&Eq'). etrans; first apply Le.
        apply Pos.lt_le_incl. apply MAX. by eexists.
      + by setoid_rewrite <- memory_lookup_cell.
    - move => ?? /lookup_singleton_Some [<- <-] //.
  Qed.

  Global Instance message_ElemOf : ElemOf message memory :=
    λ 𝑚 M, M !! (mloc 𝑚, mto 𝑚) = Some (mbase 𝑚).

  Global Instance msg_elem_wf_pre : @WellformedPreserving memory _ message _ (∋).
  Proof.
    constructor. move => ?? In WF.
    apply WF. rewrite -memory_lookup_cell. apply In.
  Qed.


  (** Memory alloc/dealloc -------------------------------------------------- *)
  Definition mem_deallocated M : gset loc :=
    filter (λ l, cell_deallocated (M !!c l)) (dom M).

  Lemma mem_deallocated_sub M :
    mem_deallocated M ⊆ dom M.
  Proof. set_solver. Qed.

  Lemma mem_deallocated_correct1 M l:
    l ∈ mem_deallocated M → cell_deallocated (M !!c l).
  Proof. set_solver. Qed.

  Lemma mem_deallocated_correct2 M l:
    cell_deallocated (M !!c l) → l ∈ mem_deallocated M.
  Proof.
    move=>HM. move : (HM). intros (t & ? & EQ & _)%cell_deallocated_correct1.
    rewrite -memory_lookup_cell -lookup_gmap_curry in EQ.
    rewrite elem_of_filter /dom /memory_loc_dom elem_of_dom.
    destruct lookup; by eauto.
  Qed.

  Record alloc_inv M := {
    alloc_inv_min_alloc : ∀ l, cell_alloc_inv (M !!c l);
    alloc_inv_max_dealloc : ∀ l, cell_dealloc_inv (M !!c l);
  }.

  Global Program Instance memory_state : StateFacts loc memory :=
    {| state_dealloc := mem_deallocated; |}.
  Next Obligation. intros. by apply mem_deallocated_sub. Defined.

  (* M ↩{A} 𝑚 *)
  Inductive memory_addins 𝑚 : memory → memory → Prop :=
    MemAddIns M C'
      (ADD: cell_addins (mto 𝑚) (mbase 𝑚) (M !!c (mloc 𝑚)) C')
      : memory_addins 𝑚 M (<[(mloc 𝑚) := C']> M).

  Lemma lookup_mem_first_eq l t C M:
    (<[l:= C]> M) !! (l,t) = C !! t.
  Proof. by rewrite lookup_gmap_uncurry lookup_insert. Qed.

  Lemma lookup_mem_first_ne l l' t C M (NEq: l ≠ l'):
    (<[l:= C]> M) !! (l',t) = M !! (l',t).
  Proof. by rewrite lookup_gmap_uncurry lookup_insert_ne ?lookup_gmap_curry. Qed.

  (* MEM ADDINS ------------------------------------------------------------- *)
  Lemma memory_addins_eq (M1 M2: memory) 𝑚
    (ADD: memory_addins 𝑚 M1 M2) :
    M2 = <[(mloc 𝑚) := (<[(mto 𝑚) := (mbase 𝑚) ]> (M1 !!c 𝑚.(mloc)))]> M1.
  Proof. inversion ADD. subst. by inversion ADD0. Qed.

  Lemma memory_addins_update 𝑚 M1 M2
    (ADD: memory_addins 𝑚 M1 M2) :
    M2 !!c mloc 𝑚 = <[mto 𝑚:=mbase 𝑚]> (M1 !!c 𝑚.(mloc)).
  Proof. rewrite (memory_addins_eq _ _ _ ADD) memory_cell_lookup_insert //. Qed.

  Lemma lookup_mem_addins_old_first_eq M1 M2 𝑚 l
    (ADD: memory_addins 𝑚 M1 M2) (NEq: l ≠ mloc 𝑚)
    : M1 !!c l = M2 !!c l.
  Proof. inversion ADD. by rewrite memory_cell_lookup_insert_ne. Qed.

  Lemma lookup_mem_addins_old_eq M1 M2 𝑚 l t
    (ADD: memory_addins 𝑚 M1 M2) (NEq: (l,t) ≠ (mloc 𝑚, mto 𝑚))
    : M1 !! (l,t) = M2 !! (l,t).
  Proof.
    inversion ADD. subst.
    case (decide (l = mloc 𝑚)) => [?|?]; last by rewrite lookup_mem_first_ne.
    subst l. rewrite lookup_mem_first_eq.
    inversion ADD0. rewrite lookup_insert_ne -?memory_lookup_cell //.
    congruence.
  Qed.

  Lemma lookup_mem_addins_fresh M1 M2 𝑚
    (ADD: memory_addins 𝑚 M1 M2)
    : M1 !! (mloc 𝑚, mto 𝑚) = None.
  Proof.
    rewrite memory_lookup_cell. inversion ADD. subst.
    eapply lookup_cell_addins_fresh; eauto; apply _.
  Qed.

  Lemma lookup_mem_addins_new M1 M2 𝑚
    (ADD: memory_addins 𝑚 M1 M2)
    : M2 !! (mloc 𝑚, mto 𝑚) = Some (mbase 𝑚).
  Proof.
    inversion ADD. rewrite lookup_mem_first_eq. by eapply lookup_cell_addins_new.
  Qed.

  Lemma lookup_mem_addins_old l t m M1 M2 𝑚
    (HL: M1 !! (l,t) = Some m)
    (ADD: memory_addins 𝑚 M1 M2):
    M2 !! (l,t) = Some m.
  Proof.
    case (decide ((l,t) = (mloc 𝑚,mto 𝑚))) => [Eq1|?].
    - inversion Eq1. subst l t.
      by rewrite (lookup_mem_addins_fresh _ _ _ ADD) in HL.
    - rewrite -HL. symmetry. by eapply lookup_mem_addins_old_eq.
  Qed.

  Lemma closed_view_addins_mono V M1 M2 𝑚
    (C1: V ∈ M1) (ADD: memory_addins 𝑚 M1 M2) :
    V ∈ M2.
  Proof.
    move => ?? /C1 [m [to [? Eq]]]. exists m, to. split; first by auto.
    eapply lookup_mem_addins_old in Eq; eauto.
  Qed.

  Lemma opt_closed_view_addins_mono (V : option view) M1 M2 𝑚
    (C1: V ∈ M1) (ADD: memory_addins 𝑚 M1 M2) :
    V ∈ M2.
  Proof. destruct V; [by eapply closed_view_addins_mono|done]. Qed.

  Lemma closed_mem_addins M1 M2 𝑚
    (WF: closed_mem M1) (ADD: memory_addins 𝑚 M1 M2) (CLOSED: 𝑚.(mbase).(mrel) ∈ M2) :
    closed_mem M2.
  Proof.
    move => l t m Eq.
    case (decide ((l, t) = (mloc 𝑚, mto 𝑚))) => [Eq1|NEq].
    - rewrite Eq1 (lookup_mem_addins_new _ _ _ ADD) in Eq.
      inversion Eq. by subst m.
    - rewrite -(lookup_mem_addins_old_eq _ _ _ _ _ ADD NEq) in Eq.
      eapply opt_closed_view_addins_mono; eauto.
  Qed.

  Lemma wf_mem_addins M1 M2 𝑚
    (mWF: Wf 𝑚) (CLOSED: 𝑚.(mbase).(mrel) ∈ M2)
    (ADD: memory_addins 𝑚 M1 M2) (WF: Wf M1):
    Wf M2.
  Proof.
    constructor.
    - eapply closed_mem_addins; eauto. apply WF.
    - move => l t m.
      case (decide (l = mloc 𝑚)) => [->|NEq].
      + case (decide (t = mto 𝑚)) => [->|NEq].
        * rewrite -memory_lookup_cell (lookup_mem_addins_new _ _ _ ADD)=>[[<-]].
          by destruct 𝑚.
        * move => Eq.
          assert (H2: M1 !! (mloc 𝑚, t) = Some m).
          { rewrite (lookup_mem_addins_old_eq _ _ _ _ _ ADD); last congruence.
            by rewrite memory_lookup_cell. }
          rewrite memory_lookup_cell in H2. by eapply WF.
      + rewrite -(lookup_mem_addins_old_first_eq _ _ _ _ ADD NEq). by apply WF.
  Qed.

  Lemma memory_addins_subset (P M1 M2 : memory) 𝑚
    (ADD: memory_addins 𝑚 M1 M2)
    (SUB: P ⊆ M1) :
    P ⊆ M2.
  Proof.
    etrans; first by apply SUB.
    move => [l t]. case Eq : (M1 !! (l,t))=> [m|].
    + by rewrite (lookup_mem_addins_old _ _ _ _ _ _ Eq ADD).
    + by case (M2 !! (l, t)).
  Qed.


  (** Allocation and Deallocation invariants for memory --------------------- *)

  Definition allocated l M := ∀ t m, M !! (l, t) = Some m → mval m ≠ DVal.

  Lemma allocated_cell_deallocated l M
    (ALLOC: ¬ cell_deallocated (M !!c l))
    (AINV: alloc_inv M):
    allocated l M.
  Proof.
    move => t m Eqm EqD. apply ALLOC. rewrite memory_lookup_cell in Eqm.
    have EqM: cell_max (M !!c l) = Some (t, m) by eapply alloc_inv_max_dealloc.
    by rewrite /cell_deallocated EqM.
  Qed.

  Lemma allocated_cell_deallocated_inv l M
    (ALLOC: allocated l M)
    (AINV: alloc_inv M):
    ¬ cell_deallocated (M !!c l).
  Proof.
    move => /cell_deallocated_correct1 [t [m [Eqm [Eqv _]]]].
    apply (ALLOC t m); last done. by rewrite memory_lookup_cell.
  Qed.

  Lemma memory_addins_AVal_alloc_inv 𝑚 M1 M2
    (ADD: memory_addins 𝑚 M1 M2)
    (NOTAD: 𝑚.(mbase).(mval) = AVal)
    (FRESH: M1 !!c 𝑚.(mloc) = ∅)
    (AINV: alloc_inv M1) :
    alloc_inv M2.
  Proof.
    inversion_clear ADD. subst. rewrite FRESH /= in ADD0.
    assert (C' ≠ ∅). { inversion ADD0. apply insert_non_empty. }
    constructor => l0 C0;
      (case (decide (l0 = 𝑚.(mloc))) => [->|NEq];
        [rewrite memory_cell_lookup_insert // |
         rewrite memory_cell_lookup_insert_ne //; by apply AINV]).
    - eapply cell_addins_alloc_empty; eauto.
    - eapply cell_addins_nDVal_dealloc_inv; eauto. by rewrite NOTAD.
  Qed.

  Lemma memory_addins_VVal_alloc 𝑚 M1 M2
    (ADD: memory_addins 𝑚 M1 M2)
    (ISVAL: isval 𝑚.(mbase).(mval))
    (ALLOC: allocated 𝑚.(mloc) M1)
    (LALL: ∃ t', is_Some ( M1 !! (𝑚.(mloc), t')) ∧ (t' <= 𝑚.(mto))%positive)
    (AINV: alloc_inv M1) :
    alloc_inv M2.
  Proof.
    inversion_clear ADD. subst. destruct LALL as [t' [[m' Eqm'] Le']].
    constructor; intros l;
      (case (decide (l = 𝑚.(mloc))) => [->|NEq];
        [rewrite memory_cell_lookup_insert // |
         rewrite memory_cell_lookup_insert_ne //; by apply AINV]).
    - apply (cell_addins_alloc_inv _ _ _ _ ADD0);
        [by eapply AINV|..|by inversion ISVAL].
      eexists. split; last exact Le'. rewrite -memory_lookup_cell. by eexists.
    - apply (cell_addins_nDVal_dealloc_inv _ _ _ _ ADD0); last by inversion ISVAL.
      move => t m Eqt. apply (ALLOC t). by rewrite memory_lookup_cell.
  Qed.

  Lemma memory_addins_nAVal_alloc 𝑚 M1 M2
    (ADD: memory_addins 𝑚 M1 M2)
    (NOTAD: 𝑚.(mbase).(mval) ≠ AVal)
    (ALLOC: ∀ t' m', M1 !! (𝑚.(mloc), t') = Some m' →
              mval m' ≠ DVal ∧ (t' < 𝑚.(mto))%positive)
    (LALL: ∃ t', is_Some (M1 !! (𝑚.(mloc), t')))
    (AINV: alloc_inv M1) :
    alloc_inv M2.
  Proof using All.
    inversion_clear ADD. destruct LALL as [t' [m' Eqm']].
    constructor; intros l;
      (case (decide (l = 𝑚.(mloc))) => [->|NEq];
        [rewrite memory_cell_lookup_insert // |
         rewrite memory_cell_lookup_insert_ne //; by apply AINV]).
    - apply (cell_addins_alloc_inv _ _ _ _ ADD0);
        [by eapply AINV|..|done].
      eexists. rewrite -memory_lookup_cell. split; first by eexists.
      apply Pos.lt_le_incl. by apply (ALLOC _ m').
    - apply (cell_addins_dealloc_inv _ _ _ _ ADD0).
      move => t0 m0 ?. apply (ALLOC t0). by rewrite memory_lookup_cell.
  Qed.

  (** Memory writes --------------------------------------------------------- *)
  (* M -{𝑚}-> M' *)
  Inductive memory_write M1 𝑚 M2: Prop :=
    | MemWrite
        (MEM: memory_addins 𝑚 M1 M2)
        (mWF: Wf 𝑚) (CLOSED: 𝑚.(mbase).(mrel) ∈ M2)
        (ISVAL: isval (𝑚.(mbase).(mval)))
        (ALLOC: allocated 𝑚.(mloc) M1)
        (LALL: ∃ t', is_Some (M1 !! (𝑚.(mloc), t')) ∧ (t' ≤ 𝑚.(mto))%positive)
    .

  Lemma memory_write_wf M1 𝑚 M2
     (WRITE: memory_write M1 𝑚 M2) (WF: Wf M1):
     Wf M2.
  Proof. inversion WRITE. by eapply wf_mem_addins. Qed.

  Lemma memory_write_alloc_inv M1 𝑚 M2
    (WRITE: memory_write M1 𝑚 M2)
    (AINV: alloc_inv M1):
    alloc_inv M2.
  Proof. inversion WRITE. by apply (memory_addins_VVal_alloc _ _ _ MEM). Qed.

  Lemma memory_write_addins_fresh M1 𝑚 M2
    (WRITE: memory_write M1 𝑚 M2) :
    M1 !! (𝑚.(mloc), 𝑚.(mto)) = None.
  Proof. inversion WRITE. by eapply lookup_mem_addins_fresh. Qed.

  Lemma memory_write_addins_eq M1 𝑚 M2
    (WRITE: memory_write M1 𝑚 M2) :
    M2 = <[mloc 𝑚:=<[mto 𝑚:=mbase 𝑚]> (M1 !!c mloc 𝑚)]> M1.
  Proof. inversion WRITE. by eapply memory_addins_eq. Qed.

  Lemma memory_write_new M1 𝑚 M2
    (WRITE: memory_write M1 𝑚 M2) :
    M2 !! (mloc 𝑚, mto 𝑚) = Some (mbase 𝑚).
  Proof. inversion WRITE. by eapply lookup_mem_addins_new. Qed.

  Lemma memory_write_msg_wf M1 𝑚 M2
    (WRITE: memory_write M1 𝑚 M2):
    Wf 𝑚.
  Proof. by inversion WRITE. Qed.

  Lemma memory_write_closed_view M1 𝑚 M2 V
    (WRITE: memory_write M1 𝑚 M2)
    (CLOSED: V ∈ M1):
    V ∈ M2.
  Proof.
    inversion WRITE. eapply closed_view_addins_mono; by eauto.
  Qed.

  Lemma memory_write_opt_closed_view M1 𝑚 M2 (oV: option view)
    (WRITE: memory_write M1 𝑚 M2)
    (CLOSED: oV ∈ M1):
    oV ∈ M2.
  Proof. destruct oV; [by eapply memory_write_closed_view|done]. Qed.


  (** Memory list addins ---------------------------------------------------- *)
  Inductive mem_list_addins : list message → relation memory :=
    | MemListAddNone M : mem_list_addins nil M M
    | MemListAddSome 𝑚 𝑚s M1 M2 M3
        (NEXT: mem_list_addins 𝑚s M1 M2)
        (ADD: memory_addins 𝑚 M2 M3)
        (WF: Wf 𝑚)
        (CLOSED: 𝑚.(mbase).(mrel) ∈ M3)
        : mem_list_addins (𝑚 :: 𝑚s) M1 M3.

  Lemma wf_mem_list_addins M1 M2 𝑚s (WF: Wf M1):
    mem_list_addins 𝑚s M1 M2 → Wf M2.
  Proof.
    induction 1; first exact WF.
    eapply wf_mem_addins; eauto.
  Qed.

  Lemma closed_view_list_addins_mono V M1 M2 𝑚s
    (C1: V ∈ M1) (ADD: mem_list_addins 𝑚s M1 M2):
    V ∈ M2.
  Proof.
    induction ADD; first by auto.
    apply (closed_view_addins_mono _ _ _ _ (IHADD C1) ADD0).
  Qed.

  Lemma opt_closed_view_list_addins_mono (V : option view) M1 M2 𝑚s
    (C1: V ∈ M1) (ADD: mem_list_addins 𝑚s M1 M2) (WF: Wf M1):
    V ∈ M2.
  Proof. destruct V; [by eapply closed_view_list_addins_mono|done]. Qed.

  Lemma mem_list_addins_dom_mono M1 𝑚s M2
    (IN: mem_list_addins 𝑚s M1 M2):
    dom M1 ⊆ dom M2.
  Proof.
    induction IN; first done.
    etrans; first apply IHIN. inversion_clear ADD.
    intros l. rewrite !memory_loc_elem_of_dom=>?.
    destruct (decide (l = mloc 𝑚)) as [->|].
    { rewrite memory_cell_lookup_insert. inversion ADD0. apply insert_non_empty. }
    rewrite memory_cell_lookup_insert_ne //.
  Qed.

  Lemma mem_list_addins_dom M1 𝑚s M2
    (IN: mem_list_addins 𝑚s M1 M2) :
    ∀ 𝑚, 𝑚 ∈ 𝑚s → 𝑚.(mloc) ∈ dom M2.
  Proof.
    setoid_rewrite memory_loc_elem_of_dom. revert M2 IN.
    induction 𝑚s as [|𝑚0 𝑚s IH𝑚s]=> M2 IN 𝑚 ; first by rewrite elem_of_nil.
    inversion IN. subst. move => /elem_of_cons [->|].
    - inversion ADD. rewrite memory_cell_lookup_insert.
      inversion ADD0. apply insert_non_empty.
    - move => In. inversion ADD. destruct (decide (mloc 𝑚0 = mloc 𝑚)) as [->|].
      + rewrite memory_cell_lookup_insert. inversion ADD0; apply insert_non_empty.
      + rewrite memory_cell_lookup_insert_ne //. by apply IH𝑚s.
  Qed.

  Lemma mem_list_addins_sub M1 𝑚s M2
    (IN: mem_list_addins 𝑚s M1 M2) (WF: Wf M1) :
    M1 ⊑ M2.
  Proof.
    revert M2 IN.
    induction 𝑚s => M2 IN; inversion IN; subst; first done.
    etrans; first apply (IH𝑚s _ NEXT).
    move => [l t]. case Eq: (M3 !! (l,t)) => [m|]; last done.
    erewrite (lookup_mem_addins_old _ _ _ M3); eauto.
  Qed.

  Definition mem_list_disj (𝑚s : list message) :=
     ∀ n1 n2 𝑚1 𝑚2,
            𝑚s !! n1 = Some 𝑚1 → 𝑚s !! n2 = Some 𝑚2 → 𝑚1.(mloc) = 𝑚2.(mloc)
           → n1 = n2.

  Lemma mem_list_disj_cons 𝑚 𝑚s :
    mem_list_disj (𝑚 :: 𝑚s) → mem_list_disj 𝑚s.
  Proof.
    move => DISJ n1 n2 𝑚1 𝑚2 HL1 HL2 Eq.
    have Eqm : ∀ n, (n + 1 - length [𝑚])%nat = n by intros; simpl; lia.
    have HL1': (𝑚 :: 𝑚s) !! (n1 + 1)%nat = Some 𝑚1.
    { rewrite -HL1 -{2}(Eqm n1)-lookup_app_r; [auto|simpl; lia]. }
    have HL2': (𝑚 :: 𝑚s) !! (n2 + 1)%nat = Some 𝑚2.
    { rewrite -HL2 -{2}(Eqm n2)-lookup_app_r; [auto|simpl; lia]. }
    assert (EQ := DISJ _ _ _ _ HL1' HL2' Eq). by lia.
  Qed.

  Lemma mem_list_disj_cons_rest 𝑚 𝑚s :
    mem_list_disj (𝑚 :: 𝑚s) → ∀ 𝑚', 𝑚' ∈ 𝑚s → 𝑚.(mloc) ≠ 𝑚'.(mloc).
  Proof.
    move => DISJ 𝑚' /elem_of_list_lookup [i HL2] Eq.
    have HL1: (𝑚 :: 𝑚s) !! 0%nat = Some 𝑚 by auto.
    have HL2': (𝑚 :: 𝑚s) !! (i + 1)%nat = Some 𝑚'.
    { rewrite (lookup_app_r [𝑚]); simpl; last by lia.
      rewrite (_: (i + 1 - 1)%nat = i); by [auto|lia]. }
    have Eq' :=DISJ _ _ _ _ HL1 HL2' Eq. clear -Eq'. by lia.
  Qed.

  Lemma mem_list_addins_old 𝑚s M1 M2 l
    (ADD: mem_list_addins 𝑚s M1 M2) (NONE: ∀ 𝑚, 𝑚 ∈ 𝑚s → l ≠ 𝑚.(mloc)):
    M1 !!c l = M2 !!c l.
  Proof.
    induction ADD; first done.
    rewrite IHADD.
    - eapply lookup_mem_addins_old_first_eq; eauto. apply NONE. by left.
    - move => 𝑚' ?. apply NONE. by right.
  Qed.

  Lemma mem_list_addins_old_2 𝑚s M1 M2 l t
    (ADD: mem_list_addins 𝑚s M1 M2) (NONE: ∀ 𝑚, 𝑚 ∈ 𝑚s → l ≠ 𝑚.(mloc)):
    M1 !! (l, t) = M2 !! (l, t).
  Proof. rewrite !memory_lookup_cell. f_equal. by eapply mem_list_addins_old. Qed.

  Lemma mem_list_addins_disjoint 𝑚s M1 M2
    (ADD: mem_list_addins 𝑚s M1 M2)
    (DISJ: mem_list_disj 𝑚s) :
    ∀ 𝑚, 𝑚 ∈ 𝑚s →
      M2 !!c 𝑚.(mloc) = <[𝑚.(mto) := 𝑚.(mbase)]> (M1 !!c 𝑚.(mloc)).
  Proof.
    revert M2 ADD.
    induction 𝑚s as [|𝑚 𝑚s IH] => M2 ADD 𝑚' In𝑚';
      first by apply elem_of_nil in In𝑚'.
    inversion_clear ADD.
    have DISJ' := mem_list_disj_cons _ _ DISJ.
    move : In𝑚'=> /elem_of_cons [?|In].
    - subst 𝑚'.
      rewrite (mem_list_addins_old _ _ _ _ NEXT);
        last by apply mem_list_disj_cons_rest.
      eapply memory_addins_update; eauto.
    - have NEq := mem_list_disj_cons_rest _ _ DISJ _ In.
      specialize (IH DISJ' _ NEXT).
      rewrite -(lookup_mem_addins_old_first_eq _ _ _ _ ADD0);
        [by apply IH|done].
  Qed.

  Lemma mem_list_addins_fresh_alloc M1 𝑚s M2
    (IN: mem_list_addins 𝑚s M1 M2)
    (DISJ : mem_list_disj 𝑚s)
    (FRESH: ∀ 𝑚, 𝑚 ∈ 𝑚s → 𝑚.(mloc) ∉ dom M1 ∧ 𝑚.(mbase).(mval) = AVal)
    (AINV: alloc_inv M1) :
    alloc_inv M2.
  Proof.
    revert M2 IN.
    induction 𝑚s as [|𝑚 𝑚s IH] => M2 IN ; inversion IN; subst; first done.
    destruct (FRESH 𝑚) as [NIn EqV]; first by left.
    apply (memory_addins_AVal_alloc_inv _ _ _ ADD EqV).
    { rewrite -(mem_list_addins_old _ _ _ _ NEXT);
        [by eapply memory_loc_not_elem_of_dom |by apply mem_list_disj_cons_rest]. }
    apply IH; [by eapply mem_list_disj_cons| |done].
    move => ??. apply FRESH. by right.
  Qed.

  Lemma mem_list_addins_dealloc_alloc M1 𝑚s M2
    (IN: mem_list_addins 𝑚s M1 M2)
    (DISJ : mem_list_disj 𝑚s)
    (DEALLOC: ∀ 𝑚, 𝑚 ∈ 𝑚s
              → 𝑚.(mbase).(mval) = DVal
              ∧ (∀ (t': time) m', M1 !! (𝑚.(mloc), t') = Some m'
                        → mval m' ≠ DVal ∧ (t' < 𝑚.(mto))%positive)
              ∧ ∃ t', is_Some (M1 !! (𝑚.(mloc),t')))
    (AINV: alloc_inv M1) :
    alloc_inv M2.
  Proof using All.
    revert M2 IN.
    induction 𝑚s as [|𝑚 𝑚s IH] => M2 IN ; inversion IN; subst; first done.
    destruct (DEALLOC 𝑚) as [EqV [MAX SOME]]; first by left.
    apply (memory_addins_nAVal_alloc _ _ _ ADD);
      [by rewrite EqV|..].
    - move => t' m' Eq'. apply MAX.
      rewrite (mem_list_addins_old_2 _ _ _ _ _ NEXT); first done.
      by apply mem_list_disj_cons_rest.
    - destruct SOME as [t' [m' Eq']].
      eexists t', m'.
      rewrite -(mem_list_addins_old_2 _ _ _ _ _ NEXT); first done.
      by apply mem_list_disj_cons_rest.
    - apply IH; [by eapply mem_list_disj_cons| |done].
      move => ??. apply DEALLOC. by right.
  Qed.

  Definition alloc_new_mem M 𝑚s : memory :=
    foldr (λ 𝑚 M, <[𝑚.(mloc) := {[𝑚.(mto) := 𝑚.(mbase)]}]> M) M 𝑚s.

  Definition dealloc_new_mem (M: memory) (𝑚s: list message) : memory :=
    foldr (λ 𝑚 M,
           <[𝑚.(mloc) := <[𝑚.(mto) := 𝑚.(mbase)]> (M !!c 𝑚.(mloc))]> M) M 𝑚s.

  Definition alloc_new_na (𝓝: view) (𝑚s: list message) : view :=
    foldr (λ 𝑚 𝓝, <[𝑚.(mloc) := [{ 𝑚.(mto), ∅, ∅, ∅ }] ]> 𝓝) 𝓝 𝑚s.

  Lemma alloc_new_mem_lookup_old M (𝑚s: list message) l
    (NONE: ∀ 𝑚, 𝑚 ∈ 𝑚s → l ≠ 𝑚.(mloc)):
    (alloc_new_mem M 𝑚s) !!c l = M !!c l.
  Proof.
    induction 𝑚s as [|𝑚 𝑚s IH] ; first done.
    rewrite /= memory_cell_lookup_insert_ne.
    - apply IH => ??. apply NONE. by right.
    - move => ?. apply (NONE 𝑚); [by left|done].
  Qed.

  Lemma alloc_new_mem_lookup_new M (𝑚s: list message) 𝑚
    (DISJ: mem_list_disj 𝑚s)
    (IN: 𝑚 ∈ 𝑚s):
    (alloc_new_mem M 𝑚s) !!c 𝑚.(mloc) = {[mto 𝑚 := mbase 𝑚]}.
  Proof.
    induction 𝑚s as [|𝑚' 𝑚s' IH];
      first by apply not_elem_of_nil in IN.
    apply elem_of_cons in IN as [?|IN].
    - subst. rewrite memory_cell_lookup_insert //.
    - rewrite /= memory_cell_lookup_insert_ne;
        last by apply (mem_list_disj_cons_rest _ _ DISJ).
      apply IH; last done. by eapply mem_list_disj_cons.
  Qed.

  Lemma alloc_new_na_lookup_old (𝑚s: list message) 𝓝 l
     (NONE: ∀ 𝑚, 𝑚 ∈ 𝑚s → l ≠ 𝑚.(mloc)):
    alloc_new_na 𝓝 𝑚s !! l = 𝓝 !! l.
  Proof.
    induction 𝑚s as [|𝑚 𝑚s IH]; first done.
    simpl. rewrite lookup_insert_ne.
    - apply IH. move => ??. apply NONE. by right.
    - move => ?. apply (NONE 𝑚); [by left|done].
  Qed.

  Lemma closed_na_view_list_addins (𝓝: view) M1 M2 𝑚s
    (C1: 𝓝 ∈ M1) (ADD: mem_list_addins 𝑚s M1 M2):
    alloc_new_na 𝓝 𝑚s ∈ M2.
  Proof.
    revert M2 ADD.
    induction 𝑚s as [|𝑚 𝑚s]
      => M2 ADD /=; inversion ADD; subst; first done.
    move => l t.
    case (decide (l = 𝑚.(mloc))) => [->|NEq].
    - move/(view_lookup_of_wp _ _) => [[t' ws rsa rsn] /= [-> {t'} ]].
      rewrite lookup_insert => [[<-] ? ?].
      do 2 eexists. split; last by eapply lookup_mem_addins_new. done.
    - move/(view_lookup_of_wp _ _) => [[t' ? ? ?] /= [-> {t'} ]].
      rewrite lookup_insert_ne; last by auto.
      move/(view_lookup_w _ _).
      move => /(IH𝑚s _ NEXT) [m [to' H']].
      exists m, to'.
      rewrite -(lookup_mem_addins_old_eq _ _ _ _ _ ADD0); first done.
      by move => [? ?].
  Qed.

  Section Allocation.
    Context `{!Shift loc} `{!Allocator loc memory}.
    (** Allocation *)
    Inductive memory_alloc
      (n : nat) l 𝑚s M1 M2 : Prop :=
      | MemAlloc
          (LEN: length 𝑚s = n)
          (AMES: ∀ (n' : nat) 𝑚, 𝑚s !! n' = Some 𝑚
                    → 𝑚.(mloc) = l >> n'
                    ∧ 𝑚.(mbase).(mval) = AVal
                    ∧ 𝑚.(mbase).(mrel) = None)
          (ADD: mem_list_addins 𝑚s M1 M2)
          (ALLOC: alloc M1 n l).

    Lemma memory_alloc_disjoint n l 𝑚s M1 M2
      (ALLOC: memory_alloc n l 𝑚s M1 M2) :
        mem_list_disj 𝑚s.
    Proof.
      inversion ALLOC.
      move => n1 n2 𝑚1 𝑚2 /AMES [Hn1 _] /AMES [Hn2 _] Eql.
      rewrite Eql Hn2 in Hn1. by eapply shift_nat_inj.
    Qed.

    Lemma memory_alloc_loc_eq n l 𝑚s M1 M2
      (ALLOC: memory_alloc n l 𝑚s M1 M2):
      ∀ (n': nat) 𝑚, 𝑚s !! n' = Some 𝑚 → 𝑚.(mloc) = l >> n'.
    Proof. apply ALLOC. Qed.

    Lemma memory_alloc_AVal n l 𝑚s M1 M2
      (ALLOC: memory_alloc n l 𝑚s M1 M2):
      ∀ (n': nat) 𝑚, 𝑚s !! n' = Some 𝑚 → 𝑚.(mbase).(mval) = AVal.
    Proof. apply ALLOC. Qed.

    Lemma memory_alloc_view_None n l 𝑚s M1 M2
      (ALLOC: memory_alloc n l 𝑚s M1 M2):
      ∀ (n': nat) 𝑚, 𝑚s !! n' = Some 𝑚 → 𝑚.(mbase).(mrel) = None.
    Proof. apply ALLOC. Qed.

    Lemma memory_alloc_length n l 𝑚s M1 M2
      (ALLOC: memory_alloc n l 𝑚s M1 M2):
      length 𝑚s = n.
    Proof. apply ALLOC. Qed.

    Lemma memory_alloc_fresh n l 𝑚s M1 M2
      (ALLOC: memory_alloc n l 𝑚s M1 M2):
      ∀ (n' : nat), (n' < n)%nat → l >> n' ∈ dom M2 ∖ dom M1.
    Proof.
      inversion ALLOC.
      move => n' Lt. rewrite elem_of_difference. split.
      - assert (is_Some (𝑚s !! n')) as [𝑚 HL].
        { apply lookup_lt_is_Some_2. by rewrite LEN. }
        destruct (AMES _ _ HL) as [Eq _].
        rewrite -Eq. eapply mem_list_addins_dom; eauto.
        by eapply elem_of_list_lookup_2.
      - by apply (alloc_add_fresh _ _ _ ALLOC0).
    Qed.

    Lemma memory_alloc_fresh_2 n l 𝑚s M1 M2
      (ALLOC: memory_alloc n l 𝑚s M1 M2):
      ∀ 𝑚, 𝑚 ∈ 𝑚s → 𝑚.(mloc) ∉ dom M1.
    Proof.
      move => 𝑚 /elem_of_list_lookup [n' Eqn'].
      rewrite (memory_alloc_loc_eq _ _ _ _ _ ALLOC _ _ Eqn').
      apply lookup_lt_Some in Eqn'.
      rewrite (memory_alloc_length _ _ _ _ _ ALLOC) in Eqn'.
      move : (memory_alloc_fresh _ _ _ _ _ ALLOC _ Eqn')
        => /elem_of_difference [//].
    Qed.

    Lemma memory_alloc_fresh_3 n l 𝑚s (M1 M2 : memory)
      (ALLOC: memory_alloc n l 𝑚s M1 M2):
      ∀ 𝑚, 𝑚 ∈ 𝑚s → M1 !!c 𝑚.(mloc) = ∅.
    Proof.
      move => 𝑚 In. apply memory_loc_not_elem_of_dom. by eapply memory_alloc_fresh_2.
    Qed.

    Lemma memory_alloc_alloc_inv n l 𝑚s M1 M2
      (ALLOC: memory_alloc n l 𝑚s M1 M2)
      (AINV: alloc_inv M1) :
      alloc_inv M2.
    Proof.
      eapply mem_list_addins_fresh_alloc;
        [apply ALLOC|by eapply memory_alloc_disjoint| |done].
      move => 𝑚 In. split.
      - apply (memory_alloc_fresh_2 _ _ _ _ _ ALLOC _ In).
      - apply elem_of_list_lookup in In as  [n' Eqn'].
        apply (memory_alloc_AVal _ _ _ _ _ ALLOC _ _ Eqn').
    Qed.

    Lemma memory_alloc_lookup n l 𝑚s M1 M2
      (ALLOC: memory_alloc n l 𝑚s M1 M2):
      ∀ 𝑚, 𝑚 ∈ 𝑚s
        → M2 !!c 𝑚.(mloc) = {[𝑚.(mto) := 𝑚.(mbase)]}.
    Proof.
      move => ? In. inversion ALLOC.
      by rewrite (mem_list_addins_disjoint _ _ _
                    ADD (memory_alloc_disjoint _ _ _ _ _ ALLOC) _ In)
                  (memory_alloc_fresh_3 _ _ _ _ _ ALLOC _ In).
    Qed.

    Lemma memory_alloc_insert n l 𝑚s M1 M2
      (ALLOC: memory_alloc n l 𝑚s M1 M2):
      M2 = alloc_new_mem M1 𝑚s.
    Proof.
      have FRESH := memory_alloc_fresh_3 _ _ _ _ _ ALLOC.
      have DISJ := memory_alloc_disjoint _ _ _ _ _ ALLOC.
      inversion_clear ALLOC. clear LEN AMES ALLOC0 n l.
      revert M2 ADD FRESH.
      induction 𝑚s as [|𝑚 𝑚s IH] => M2 ADD FRESH;
        inversion_clear ADD; first done.
      simpl. subst.
      rewrite -(IH (mem_list_disj_cons _ _ DISJ) _ NEXT).
      - rewrite (memory_addins_eq _ _ _ ADD0). f_equal.
        rewrite -(mem_list_addins_old _ _ _ _ NEXT);
          last by apply mem_list_disj_cons_rest.
        rewrite FRESH; [done|by left].
      - move => ??. apply FRESH. by right.
    Qed.

    (** DeAllocation *)
    Inductive memory_dealloc
      (n : nat) l 𝑚s M1 M2 :Prop :=
      | MemDealloc
          (LEN: length 𝑚s = n)
          (DMES: ∀ (n' : nat) 𝑚, 𝑚s !! n' = Some 𝑚
                    → 𝑚.(mloc) = l >> n'
                    ∧ 𝑚.(mbase).(mval) = DVal
                    ∧ 𝑚.(mbase).(mrel) = None
                    ∧ (∀ (t': time) m', M1 !! (𝑚.(mloc), t') = Some m'
                            → mval m' ≠ DVal ∧ (t' < 𝑚.(mto))%positive)
                    ∧ ∃ t', is_Some (M1 !! (𝑚.(mloc), t')))
          (ADD: mem_list_addins 𝑚s M1 M2)
          (DEALLOC: dealloc M1 n l).

    Lemma memory_dealloc_disjoint n l 𝑚s M1 M2
      (DEALLOC: memory_dealloc n l 𝑚s M1 M2) :
        mem_list_disj 𝑚s.
    Proof.
      inversion DEALLOC.
      move => n1 n2 𝑚1 𝑚2 /DMES [Hn1 _] /DMES [Hn2 _] Eql.
      rewrite Eql Hn2 in Hn1. by eapply shift_nat_inj.
    Qed.

    Lemma memory_dealloc_loc_eq n l 𝑚s M1 M2
      (DEALLOC: memory_dealloc n l 𝑚s M1 M2):
      ∀ (n': nat) 𝑚, 𝑚s !! n' = Some 𝑚 → 𝑚.(mloc) = l >> n'.
    Proof. apply DEALLOC. Qed.

    Lemma memory_dealloc_DVal n l 𝑚s M1 M2
      (DEALLOC: memory_dealloc n l 𝑚s M1 M2):
      ∀ (n': nat) 𝑚, 𝑚s !! n' = Some 𝑚 → 𝑚.(mbase).(mval) = DVal.
    Proof. apply DEALLOC. Qed.

    Lemma memory_dealloc_length n l 𝑚s M1 M2
      (DEALLOC: memory_dealloc n l 𝑚s M1 M2):
      length 𝑚s = n.
    Proof. apply DEALLOC. Qed.

    Lemma memory_dealloc_max n l 𝑚s M1 M2
      (DEALLOC: memory_dealloc n l 𝑚s M1 M2) :
      ∀ 𝑚, 𝑚 ∈ 𝑚s
          → ∀ 𝑚', 𝑚' ∈ M1 → 𝑚'.(mloc) = 𝑚.(mloc) → (𝑚'.(mto) < 𝑚.(mto))%positive.
    Proof.
      inversion DEALLOC.
      move => ? /elem_of_list_lookup [n' /DMES [_[_[_ [MAX _]]]]] 𝑚' IN EQL.
      rewrite -EQL in MAX. by apply (MAX _ _ IN).
    Qed.

    Lemma memory_dealloc_remove n l 𝑚s M1 M2
      (DEALLOC: memory_dealloc n l 𝑚s M1 M2) :
      ∀ (n' : nat), (n' < n)%nat
      → l >> n' ∈ (dom M1 ∖ mem_deallocated M1) ∩ mem_deallocated M2.
    Proof.
      inversion DEALLOC.
      move => n' Lt. rewrite elem_of_intersection. split.
      - by apply (dealloc_remove _ _ _ DEALLOC0).
      - apply mem_deallocated_correct2.
        assert (is_Some (𝑚s !! n')) as [𝑚  Eq𝑚].
        { apply lookup_lt_is_Some_2. by rewrite LEN. }
        destruct (DMES _ _ Eq𝑚) as [Eq1 [Eq2 [Eq3 [MAX _]]]].
        have DISJ:= memory_dealloc_disjoint _ _ _ _ _ DEALLOC.
        move : (dealloc_remove _ _ _ DEALLOC0 _ Lt)
          => /elem_of_difference [/memory_loc_elem_of_dom FRESH NIn].
        have IN𝑚: 𝑚 ∈ 𝑚s by apply elem_of_list_lookup; eexists.
        have EqM2: M2 !!c mloc 𝑚 = <[mto 𝑚:=mbase 𝑚]> (M1 !!c (l >> n'))
          by rewrite (mem_list_addins_disjoint _ _ _ ADD) // Eq1.
        rewrite -Eq1 EqM2. apply cell_deallocated_correct2.
        exists 𝑚.(mto), 𝑚.(mbase).
        repeat split; [by rewrite lookup_insert|by auto|].
        move => t' /elem_of_dom Eq.
        case (decide (t' = mto 𝑚)) => [->|NEQ]; first done.
        move : Eq. rewrite lookup_insert_ne; last by auto.
        move => [m' Eqm'].
        apply Pos.lt_le_incl, (MAX _ m'). rewrite Eq1.
        by rewrite memory_lookup_cell.
    Qed.

    Lemma memory_dealloc_dom_old n l 𝑚s M1 M2
      (DEALLOC: memory_dealloc n l 𝑚s M1 M2) :
      ∀ (n' : nat), (n' < n)%nat → l >> n' ∈ dom M1.
    Proof.
      inversion DEALLOC.
      by move => ? /(dealloc_remove _ _ _ DEALLOC0) /elem_of_difference [? _].
    Qed.

    Lemma memory_dealloc_alloc_inv n l 𝑚s M1 M2
      (DEALLOC: memory_dealloc n l 𝑚s M1 M2)
      (AINV: alloc_inv M1) :
      alloc_inv M2.
    Proof.
      inversion DEALLOC.
      apply (mem_list_addins_dealloc_alloc _ _ _ ADD);
        [by eapply memory_dealloc_disjoint| |done].
      move => 𝑚 /elem_of_list_lookup [n' Eqn'].
      by destruct (DMES _ _ Eqn') as (? & ? & _ & ? & ?).
    Qed.

  End Allocation.

  (** Cell lists ------------------------------------------------------------ *)
  Section cell_lists.
    Context `{!Shift loc}.
    Definition cell_cons l (n: nat) (M : memory) (Cl : list cell) : list cell :=
      M !!c (l >> n) :: Cl.

    Fixpoint cell_list' l (n : nat) (M : memory) (Cl: list cell): list cell :=
      match n with
      | O => Cl
      | S n' => cell_list' l n' M (cell_cons l n' M Cl)
      end.

    Definition cell_list l n M := cell_list' l n M [].

    Lemma cell_list'_length l n M Cl:
      (length (cell_list' l n M Cl) ≤ (n + length Cl)%nat)%nat.
    Proof.
      move : Cl. induction n as [|n Hn] => Cl /=; first done.
      rewrite /cell_cons. etrans; first apply Hn. simpl. lia.
    Qed.

    Lemma cell_list'_tail l n M Cl :
      ∃ Cl', cell_list' l n M Cl = Cl' ++ Cl.
    Proof.
      move : Cl. induction n as [|n IH] => Cl; first by exists [].
      simpl. rewrite /cell_cons.
      destruct (IH ((M !!c (l >> n)) :: Cl)) as [Cl' Eq'].
      exists (Cl'++[M !!c (l >> n)]). by rewrite Eq' -app_assoc.
    Qed.

    Lemma cell_list'_length_exact l n M Cl:
      (length (cell_list' l n M Cl) = (n + length Cl)%nat)%nat.
    Proof.
      move : Cl. induction n as [|n Hn] => Cl /=; first done.
      rewrite /cell_cons (_: S (n + length Cl) = (n + length (M !!c (l >> n) :: Cl))%nat);
        last by (simpl;lia).
      apply Hn.
    Qed.

    Lemma cell_list'_app l (n: nat) M Cl:
      cell_list' l n M Cl = cell_list' l n M [] ++ Cl.
    Proof.
      revert Cl. induction n as [|n Hn] => Cl /=; first done.
      rewrite /cell_cons Hn (Hn [_]) app_assoc_reverse //.
    Qed.

    Lemma cell_list'_cons l (n: nat) M Cl C:
      cell_list' l (S n) M Cl = cell_list' l n M (M !!c (l >> n)::Cl).
    Proof. done. Qed.

    Lemma cell_list_app l (n: nat) M C:
      cell_list l (S n) M = cell_list l n M ++ [M !!c (l >> n)].
    Proof.
      rewrite /cell_list (cell_list'_cons _ _ _ []); last done.
      apply cell_list'_app.
    Qed.

    Lemma cell_list'_lookup l n n' M Cl
      (Le: (n ≤ n')%nat) :
      (cell_list' l n M Cl) !! n' = Cl !! (n' - n)%nat.
    Proof.
      destruct (cell_list'_tail l n M Cl) as [Cl' Eq'].
      rewrite Eq'.
      assert (HL:= cell_list'_length_exact l n M Cl).
      rewrite Eq' app_length in HL.
      assert (HL': length Cl' = n) by lia.
      rewrite -HL'. apply lookup_app_r. by rewrite HL'.
    Qed.

    Lemma cell_list'_Some l n M :
      ∀ (n': nat) C Cl,
        (∀ (n0: nat) C0, Cl !! n0 = Some C0 → M !!c (l >> (n + n0)%nat) = C0)
        → (n' < n)%nat
        → (cell_list' l n M Cl) !! n' = Some C ↔ M !!c (l >> n') = C.
    Proof.
      induction n as [|n IH] => n' C Cl HCl Lt; first by lia.
      simpl. rewrite Nat.lt_succ_r in Lt. apply Nat.lt_eq_cases in Lt as [Lt|Eq].
      - apply IH; [|done] => n0 C0.
        rewrite /cell_cons. destruct n0 as [|n0].
        + move => /= [<-]. by rewrite -plus_n_O.
        + rewrite (lookup_app_r [_] Cl); last by (simpl; lia).
          move => /= /HCl. rewrite Nat.sub_0_r.
          rewrite (_: (S n + n0)%nat = (n + S n0)%nat); [done|lia].
       - rewrite Eq cell_list'_lookup; last done.
         rewrite Nat.sub_diag /cell_cons /=. split; congruence.
    Qed.

    Lemma cell_list_Some l n M :
      ∀ (n': nat) C,
        (n' < n)%nat
        → (cell_list l n M) !! n' = Some C ↔ M !!c (l >> n') = C.
    Proof.
      move => n' C Lt. apply cell_list'_Some; auto. by move => ?? /=.
    Qed.

    Lemma cell_list_Some_2 l n M :
      ∀ (n': nat) C,
        (cell_list l n M) !! n' = Some C → M !!c (l >> n') = C.
    Proof.
      move => n' C In. apply (cell_list_Some _ n); last done.
      apply lookup_lt_Some in In.
      rewrite cell_list'_length_exact /= in In. by lia.
    Qed.

    Lemma cell_list_fmap (l : loc) (n: nat) (M: memory) :
      (cell_list l n M) = fmap (λ i : nat, M !!c (l >> i)) (seq 0%nat n).
    Proof.
      apply list_eq=> n'.
      have LEN: length (cell_list l n M) = n.
      { by rewrite cell_list'_length_exact /= -plus_n_O. }
      rewrite list_lookup_fmap.
      case (decide (n' < n)%nat) => [Lt|Ge].
      - assert (is_Some(cell_list l n M !! n')) as [C EqC].
        { apply lookup_lt_is_Some. by rewrite LEN. }
        rewrite EqC. apply cell_list_Some_2 in EqC.
        by rewrite (lookup_seq_lt _ _ _ Lt) /= EqC.
      - apply Nat.nlt_ge in Ge.
        rewrite lookup_ge_None_2; last by rewrite LEN.
        by rewrite (lookup_seq_ge _ _ _ Ge) /=.
    Qed.

    Lemma memory_alloc_cell_list `{!Allocator loc memory} n l 𝑚s M1 M2
      (ALLOC: memory_alloc n l 𝑚s M1 M2):
      ∀ (n': nat) C,
        (cell_list l n M2) !! n' = Some C
        ↔ ∃ 𝑚, 𝑚s !! n' = Some 𝑚 ∧ C = {[𝑚.(mto) := 𝑚.(mbase)]}.
    Proof.
      move => n' C.
      split.
      - move => In.
        assert (Lt: (n' < n)%nat).
        { have HL := cell_list'_length_exact l n M2 [].
          rewrite /= -(plus_n_O n) in HL. rewrite -HL. by eapply lookup_lt_Some. }
        assert (is_Some (𝑚s !! n')) as [𝑚 Eq𝑚].
        { by rewrite lookup_lt_is_Some (memory_alloc_length _ _ _ _ _ ALLOC). }
        exists 𝑚. split; first done.
        move : (cell_list_Some_2 _ _ _ _ _ In).
        rewrite -(memory_alloc_loc_eq _ _ _ _ _ ALLOC _ _ Eq𝑚)
                 (memory_alloc_lookup _ _ _ _ _ ALLOC); [done|].
        apply elem_of_list_lookup. by eexists.
      - move => [𝑚 [Eq𝑚 ->]]. apply cell_list_Some; auto.
        + rewrite -(memory_alloc_length _ _ _ _ _ ALLOC).
          apply lookup_lt_is_Some. by eexists.
        + rewrite -(memory_alloc_loc_eq _ _ _ _ _ ALLOC _ _ Eq𝑚).
          apply (memory_alloc_lookup _ _ _ _ _ ALLOC), elem_of_list_lookup.
          by eexists.
    Qed.

    Lemma memory_alloc_cell_list_map `{!Allocator loc memory} n l 𝑚s M1 M2
      (ALLOC: memory_alloc n l 𝑚s M1 M2):
        (cell_list l n M2) = fmap (λ 𝑚, {[𝑚.(mto) := 𝑚.(mbase)]}) 𝑚s.
    Proof.
      apply list_eq => n'. rewrite list_lookup_fmap.
      destruct (cell_list l n M2 !! n') as [C|] eqn:HC.
      - apply (memory_alloc_cell_list _ _ _ _ _ ALLOC) in HC as [𝑚 [HC1 HC2]].
        by rewrite HC1 HC2.
      - apply lookup_ge_None in HC. move : HC.
        rewrite cell_list'_length_exact /=.
        by rewrite -(plus_n_O n) -(memory_alloc_length _ _ _ _ _ ALLOC)
                     -lookup_ge_None => [->].
    Qed.

  End cell_lists.

  (** Cell cut -------------------------------------------------------------- *)
  Definition cell_cut t: cell → cell := filter (λ t', (t ≤ t')%positive).

  Lemma cell_cut_insert C t t' m :
    (t ≤ t')%positive →
    cell_cut t (<[t' := m]> C) = <[t' := m]> (cell_cut t C).
  Proof. move=>?. by rewrite /cell_cut -map_filter_insert_True. Qed.

  Lemma cell_cut_empty C t
    (MAX: ∀ t', is_Some (C !! t') → (t' < t)%positive) :
    cell_cut t C = ∅.
  Proof.
    apply map_eq => to. rewrite lookup_empty map_filter_lookup_None.
    right => ? Eq. apply Pos.lt_nle, MAX. by eexists.
  Qed.

  Lemma cell_cut_empty_2 t :
    cell_cut t ∅ = ∅.
  Proof. apply map_filter_empty. Qed.

  Lemma cell_cut_addins_atomic (to t: time) m C1 C2
    (Le: (to ≤ t)%positive) (ADD: cell_addins t m C1 C2) :
    cell_cut to C2 = <[t := m]> (cell_cut to C1).
  Proof. inversion ADD. by apply cell_cut_insert. Qed.

  Lemma cell_cut_addins_na (t : time) m C1 C2
    (ADD: cell_addins t m C1 C2) (MAX: ∀ t', is_Some (C1 !! t') → (t' < t)%positive) :
    cell_cut t C2 = {[t := m]}.
  Proof.
    inversion ADD. rewrite cell_cut_insert; last done.
    by rewrite (cell_cut_empty _ _ MAX).
  Qed.

  Lemma cell_cut_lookup_Some C t t' m :
    cell_cut t C !! t' = Some m ↔ C !! t' = Some m ∧ (t ≤ t')%positive.
  Proof. apply map_filter_lookup_Some. Qed.

  Lemma cell_cut_lookup_None C t t':
    cell_cut t C !! t' = None ↔ C !! t' = None ∨ ¬ (t ≤ t')%positive.
  Proof.
    rewrite map_filter_lookup_None.
    split; move => [|]; [naive_solver| |naive_solver|naive_solver].
    destruct (C !! t'); naive_solver.
  Qed.

  Lemma cell_cut_singleton C t t' m':
    cell_cut t C = {[t' := m']} → ∀ t0, is_Some (C !! t0) → (t0 ≤ t')%positive.
  Proof.
    move => HC t0 [m0 Eq0].
    destruct (cell_cut t C !! t0) as [m1|] eqn:Eq1.
    - move : Eq1. by rewrite HC lookup_singleton_Some => [[-> _]].
    - apply cell_cut_lookup_None in Eq1 as [Eq1|Eq1];
        first by rewrite Eq1 in Eq0.
      apply Pos.lt_nle in Eq1.
      have Eq2: cell_cut t C !! t' = Some m' by rewrite HC lookup_insert.
      apply cell_cut_lookup_Some in Eq2 as [_ Le2].
      etrans; last exact Le2. by apply Pos.lt_le_incl.
  Qed.

  Lemma cell_cut_dom t (C: cell) :
    dom (cell_cut t C) ⊆ dom C.
  Proof.
    move => t'. rewrite 2!elem_of_dom.
    move => [m' /cell_cut_lookup_Some [Eq' ?]]. by eexists.
  Qed.

  Lemma cell_cut_cell_alloc_inv t0 C (AINV: cell_alloc_inv C) :
    ∀ t m, cell_cut t0 C !! t = Some m ∧ mval m = AVal
         → cell_min (cell_cut t0 C) = Some (t, m).
  Proof.
    move => t m [Eqt Eqv].
    apply gmap_top_inv; eauto with typeclass_instances.
    apply cell_cut_lookup_Some in Eqt as [Eqt Le].
    have MIN : cell_min C = Some (t, m) by apply AINV.
    move => k' IN. apply (gmap_top_top _ _ _ _ MIN).
    move : IN. apply dom_filter_subseteq.
  Qed.

  Lemma cell_cut_cell_dealloc_inv t0 C (DINV: cell_dealloc_inv C) :
    ∀ t m, cell_cut t0 C !! t = Some m ∧ mval m = DVal
         → cell_max (cell_cut t0 C) = Some (t, m).
  Proof.
    move => t m [Eqt Eqv].
    apply gmap_top_inv; eauto with typeclass_instances.
    apply cell_cut_lookup_Some in Eqt as [Eqt Le].
    have MIN : cell_max C = Some (t, m) by apply DINV.
    move => k' IN. apply (gmap_top_top _ _ _ _ MIN).
    move : IN. apply dom_filter_subseteq.
  Qed.

  (* Cell le *)
  Lemma cell_cut_cell_le (C1 C2: cell) t (LE: cell_le C1 C2) :
    cell_le (cell_cut t C1) (cell_cut t C2).
  Proof.
    move => t'. specialize (LE t').
    destruct (cell_cut t C1 !! t') as [m1|] eqn:Eq1.
    - apply cell_cut_lookup_Some in Eq1 as [Eq1 Let].
      rewrite Eq1 in LE. inversion LE as [? m2 LE' Eq Eq2|].
      rewrite (_ : cell_cut t C2 !! t' = Some m2); first by constructor.
      by apply cell_cut_lookup_Some.
    - rewrite (_ : cell_cut t C2 !! t' = None); first by constructor.
      apply cell_cut_lookup_None in Eq1 as [Eq1|NLe];
        [rewrite Eq1 in LE; inversion LE|];
        apply cell_cut_lookup_None; [by left|by right].
  Qed.

  Lemma cell_addins_cell_cut_le t m t0
    (Ce C: cell) (LE: cell_le Ce (cell_cut t0 C))
    (ADD: cell_addins t m C (<[t:= m]> C)) :
    cell_addins t m Ce (<[t:= m]> Ce).
  Proof.
    constructor.
    inversion ADD; subst; simpl in *.
    specialize (LE t).
    inversion LE as [? m1 LE1 Eq1 Eq2|]; last done. subst.
    symmetry in Eq2. apply cell_cut_lookup_Some in Eq2 as [Eq2 Le'].
    by rewrite Eq2 in DISJ.
  Qed.

  Lemma cell_addins_cell_cut t m t0 C
    (ADD: cell_addins t m C (<[t:= m]> C)) :
    cell_addins t m (cell_cut t0 C) (<[t:= m]> (cell_cut t0 C)).
  Proof.
    constructor. inversion ADD; subst; simpl in *.
    apply cell_cut_lookup_None. by left.
  Qed.

  (** Mem cut -------------------------------------------------------------- *)
  Definition mem_cut_filter V (lt : loc * time) : Prop :=
    from_option (λ t', (t' ≤ lt.2)%positive) False (V !!w lt.1).
  Instance mem_cut_filter_dec V lt : Decision (mem_cut_filter V lt).
  Proof. unfold mem_cut_filter. destruct view_lookup_write; simpl; apply _. Qed.
  Definition mem_cut (M : memory) (V : view) :=
    filter (mem_cut_filter V) M.

  Lemma mem_cut_lookup M V l :
    mem_cut M V !!c l = from_option (λ t, cell_cut t (M !!c l)) ∅ (V !!w l).
  Proof.
    apply map_eq=>t. rewrite -memory_lookup_cell /mem_cut /mem_cut_filter.
    symmetry. case EQ : (filter _ _ !! _).
    - move:EQ=>/map_filter_lookup_Some /=. destruct (V!!wl)=>[/=|[_ []]].
      by rewrite cell_cut_lookup_Some -memory_lookup_cell.
    - move:EQ=>/map_filter_lookup_None /=. destruct (V!!wl)=>//=.
      rewrite cell_cut_lookup_None -memory_lookup_cell=>-[|]; [auto|].
      case: (M !! (l, t)); eauto.
  Qed.

  (* Lemma mem_cut_insert M V l C t: *)
  (*   <[l:=cell_cut t C]> (mem_cut M V) *)
  (*   = mem_cut (<[l:=C]> M) (partial_alter (λ o, Some (t, default ∅ (snd <$> o))) l V). *)
  (* Proof. *)
  (*   apply map_eq=>-[l' t']. rewrite !memory_lookup_cell mem_cut_lookup. *)
  (*   destruct (decide (l = l')) as [->|?]. *)
  (*   - rewrite !memory_cell_lookup_insert /timeNap_lookup_write lookup_partial_alter //. *)
  (*   - rewrite !memory_cell_lookup_insert_ne // /timeNap_lookup_write /= lookup_partial_alter_ne // mem_cut_lookup //. *)
  (* Qed. *)

  Lemma mem_cut_insert M V l C t ws rsa rsn:
    <[l:=cell_cut t C]> (mem_cut M V) =
      mem_cut (<[l:=C]> M) (<[l:= [{ t, ws, rsa, rsn }] ]> V).
  Proof.
    apply map_eq=>-[l' t']. rewrite !memory_lookup_cell mem_cut_lookup.
    destruct (decide (l = l')) as [->|?].
    - rewrite !memory_cell_lookup_insert /view_lookup_write lookup_insert //.
    - rewrite !memory_cell_lookup_insert_ne //
              /view_lookup_write lookup_insert_ne // mem_cut_lookup //.
  Qed.

  Lemma mem_cut_addins_na 𝑚 M1 M2 ws rsa rsn 𝓝
    (ADD: memory_addins 𝑚 M1 M2) :
    mem_cut M2 (<[𝑚.(mloc) := [{ 𝑚.(mto), ws, rsa, rsn }] ]> 𝓝) =
      <[𝑚.(mloc) := (<[𝑚.(mto) := 𝑚.(mbase)]> (cell_cut 𝑚.(mto) (M1 !!c 𝑚.(mloc))))]>
      (mem_cut M1 𝓝).
  Proof.
    apply map_eq => l. inversion ADD. rewrite -mem_cut_insert.
    inversion_clear ADD0. subst. by rewrite cell_cut_insert.
  Qed.

  Lemma mem_cut_list_addins_na M1 M2 𝑚s 𝓝
    (IN: mem_list_addins 𝑚s M1 M2)
    (DISJ : mem_list_disj 𝑚s)
    (MAX: ∀ 𝑚, 𝑚 ∈ 𝑚s
          → ∀ 𝑚', 𝑚' ∈ M1 → 𝑚'.(mloc) = 𝑚.(mloc) → (𝑚'.(mto) < 𝑚.(mto))%positive) :
    mem_cut M2 (alloc_new_na 𝓝 𝑚s) = alloc_new_mem (mem_cut M1 𝓝) 𝑚s.
  Proof.
    revert M2 IN.
    induction 𝑚s as [|𝑚 𝑚s IH] => M2; inversion 1; subst; first done. simpl.
    rewrite (mem_cut_addins_na _ _ _ _ _ _ _ ADD)
            -(mem_list_addins_old _ _ _ _ NEXT);
      last by apply mem_list_disj_cons_rest.
    rewrite IH;
      [|by eapply mem_list_disj_cons|by move => ??; apply MAX; right| done].
    f_equal.
    rewrite /= cell_cut_empty; first done.
    move => t' [m' Eqm'].
    have IN2: 𝑚 ∈ 𝑚 :: 𝑚s by left.
    apply (MAX _ IN2 (mkMsg 𝑚.(mloc) t' m')); last done.
    rewrite /elem_of /message_ElemOf memory_lookup_cell //.
  Qed.

  Lemma mem_cut_list_addins_fresh_na M1 M2 𝑚s 𝓝
    (ADD: mem_list_addins 𝑚s M1 M2)
    (DISJ : mem_list_disj 𝑚s)
    (FRESH: ∀ 𝑚, 𝑚 ∈ 𝑚s → 𝑚.(mloc) ∉ dom M1) :
    mem_cut M2 (alloc_new_na 𝓝 𝑚s) = alloc_new_mem (mem_cut M1 𝓝) 𝑚s.
  Proof.
    apply mem_cut_list_addins_na; [assumption|assumption|].
    move => 𝑚 /FRESH /memory_loc_not_elem_of_dom EMP 𝑚' IN EQL.
    rewrite /elem_of /message_ElemOf memory_lookup_cell EQL EMP
            lookup_empty // in IN.
  Qed.

  Lemma mem_cut_memory_alloc `{!Shift loc} `{!Allocator loc memory} l n M1 M2 𝑚s 𝓝
    (ALLOC: memory_alloc n l 𝑚s M1 M2) :
    mem_cut M2 (alloc_new_na 𝓝 𝑚s) = alloc_new_mem (mem_cut M1 𝓝) 𝑚s.
  Proof.
    apply mem_cut_list_addins_fresh_na; [apply ALLOC|..].
    - by eapply memory_alloc_disjoint.
    - by eapply memory_alloc_fresh_2.
  Qed.

  Lemma mem_cut_memory_dealloc `{!Shift loc} `{!Allocator loc memory} l n M1 M2 𝑚s 𝓝
    (DEALLOC: memory_dealloc n l 𝑚s M1 M2) :
    mem_cut M2 (alloc_new_na 𝓝 𝑚s) = alloc_new_mem (mem_cut M1 𝓝) 𝑚s.
  Proof.
    apply mem_cut_list_addins_na; [apply DEALLOC|..].
    - by eapply memory_dealloc_disjoint.
    - by eapply memory_dealloc_max.
  Qed.

End Memory.

Arguments memory loc {_} VAL.
Arguments message loc {_} VAL.

Notation cell := (gmap time baseMessage) (only parsing).
Notation "M !!c l" := (memory_cell_lookup l M) (at level 20) : stdpp_scope.
