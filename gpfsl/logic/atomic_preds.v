From iris.bi.lib Require Import fractional.
From iris.proofmode Require Import proofmode.

From gpfsl.base_logic Require Import vprop history local_preds.
From gpfsl.base_logic Require Import na.
From gpfsl.base_logic Require Import frame_instances.
From gpfsl.logic Require Import atomic_cmra atomic_ghost.
From gpfsl.lang Require Import notation.

Require Import iris.prelude.options.

Implicit Types (ζ : absHist) (l : loc) (t : time) (v : val) (V : view) (q : frac).

Local Existing Instances atomic_inG.

Definition no_dealloc (C : cell) : Prop :=
  ∀ t m, C !! t = Some m → m.(mval) ≠ DVal.

(** Turn a raw history ([cell]) into an abstract one
  [map_imap] allows us to use the key, but we don't need that here. What we
  need is the option of the value: the [absHist] doesn't contain the
  deallocation event.
  We also extend the views with [Vinit] which is the view at which the atomic
  location is initialized from the non-atomic one. This allows statements where
  the [absHist] view can support things happen-before initialization. *)
Definition toAbsHist (C : cell) (Vinit : view): absHist :=
  map_imap (λ t m, match m.(mval) with
            | VVal v => Some ((v, default ∅ m.(mrel) ⊔ Vinit))
            | AVal => Some ((#☠, default ∅ m.(mrel) ⊔ Vinit))
            | DVal => None
            end) C.

Definition fresh_max_time ζ t : Prop := ∀ t', is_Some (ζ !! t') → (t' < t)%positive.
Definition no_earlier_time ζ t : Prop := ∀ t', is_Some (ζ !! t') → t' ⊑ t.
Definition max_time t ζ : Prop := is_Some (ζ !! t) ∧ no_earlier_time ζ t.

Definition good_absHist ζ Va : Prop :=
  ζ ≠ ∅ ∧ ∃ C, ζ = toAbsHist C Va ∧ no_dealloc C.

Section preds.
Context `{!noprolG Σ, !atomicG Σ}.
#[local] Notation iProp := (iProp Σ).
#[local] Notation vProp := (vProp Σ).

Definition SeenLocal l ζ : vProp := ∀ t, ⌜is_Some (ζ !! t)⌝ → seen_time l t.
Definition SyncLocal l ζ : vProp :=
  ∀ t V, ⌜snd <$> (ζ !! t) = Some V⌝ → seen_view l t V.

(* TODO: γ uniquely identifies l, so we don't actually need l as an argument to
  following definitions. We only need l in AtomicPtsTo. *)

Variant AtomicMode := SingleWriter | CASOnly | ConcurrentWriter.
#[global] Instance AtomicMode_dec : EqDecision AtomicMode.
Proof. solve_decision. Qed.
#[global] Instance AtomicMod_inhabited : Inhabited AtomicMode
  := populate SingleWriter.

(* Almost the same as own_loc_prim `l p↦ C` *)
Definition AtomicPtsToX_def (l : loc) γ (tx : time) ζ (mode : AtomicMode) : vProp :=
  ∃ C (Va : view) rsa rsn ws,
    ⌜good_hist C ∧ ζ = toAbsHist C Va ∧ is_Some (ζ !! tx) ∧ no_dealloc C⌝ ∗
    (* local assertions *)
    (SyncLocal l ζ ∗ AtRLocal l rsa ∗ AtWLocal l ws ∗ NaLocal l rsn Va) ∗
    (* own the history of l *)
    ⎡ hist l 1 C ⎤ ∗
    (* and related race detector states *)
    ⎡ atread l 1 rsa ∗ atwrite l 1 ws ∗ naread l 1 rsn ⎤ ∗
    (* authoritative ghost state of this construction *)
    ⎡ at_auth γ ζ tx Va ⎤ ∗
    (* controller for location mode *)
    ⎡ match mode with
      | SingleWriter => True (* ⌜ no_earlier_time ζ tx ⌝ *)
      | CASOnly => at_writer γ ζ
      | ConcurrentWriter => at_writer γ ζ ∗ at_exclusive_write γ tx 1
      end ⎤.
Definition AtomicPtsToX_aux : seal (@AtomicPtsToX_def). Proof. by eexists. Qed.
Definition AtomicPtsToX := unseal (@AtomicPtsToX_aux).
Definition AtomicPtsToX_eq : @AtomicPtsToX = _ := seal_eq _.

Definition AtomicPtsTo_def (l : loc) γ ζ (mode : AtomicMode) : vProp :=
  ∃ (tx : time), AtomicPtsToX l γ tx ζ mode.
Definition AtomicPtsTo_aux : seal (@AtomicPtsTo_def). Proof. by eexists. Qed.
Definition AtomicPtsTo := unseal (@AtomicPtsTo_aux).
Definition AtomicPtsTo_eq : @AtomicPtsTo = _ := seal_eq _.

(* Both [AtomicSeen] and [AtomicSync] have observed the last non-atomic event,
  as required by [NaLocal]. *)
(* [AtomicSeen] says that one has observed the writes in ζ, but not necessarily
  synchronized with them. *)
Definition AtomicSeen_def l γ ζ : vProp :=
  SeenLocal l ζ ∗ (* seen the writes, but not sync *) ⎡ at_reader γ ζ ⎤ ∗
  ∃ Va, ⌜good_absHist ζ Va⌝ ∗ ⊒Va ∗ ⎡ at_last_na γ Va ⎤.
Definition AtomicSeen_aux : seal (@AtomicSeen_def). Proof. by eexists. Qed.
Definition AtomicSeen := unseal (@AtomicSeen_aux).
Definition AtomicSeen_eq : @AtomicSeen = _ := seal_eq _.

(* [AtomicSync] additionally says that it is synced. *)
Program Definition AtomicSync_def l γ ζ : vProp :=
  SyncLocal l ζ ∗ (* seen the writes, but sync *) ⎡ at_reader γ ζ ⎤ ∗
    ∃ Va, ⌜good_absHist ζ Va⌝ ∗ ⊒Va ∗ ⎡ at_last_na γ Va ⎤.
Definition AtomicSync_aux : seal (@AtomicSync_def). Proof. by eexists. Qed.
Definition AtomicSync := unseal (@AtomicSync_aux).
Definition AtomicSync_eq : @AtomicSync = _ := seal_eq _.

(* A unique writer is synced, and hold the max exclusive writer *)
(* TODO: compute t from ζ *)
Definition AtomicSWriter_def l γ ζ : vProp :=
  (AtomicSync l γ ζ ∗ ⎡ at_writer γ ζ ⎤) ∗
    ∃ t, ⎡ at_exclusive_write γ t 1%Qp ⎤ ∗ ⌜max_time t ζ⌝.
Definition AtomicSWriter_aux : seal (@AtomicSWriter_def). Proof. by eexists. Qed.
Definition AtomicSWriter := unseal (@AtomicSWriter_aux).
Definition AtomicSWriter_eq : @AtomicSWriter = _ := seal_eq _.

(* A CASer holds a share of the shared writer *)
Definition AtomicCASerX_def l γ tx ζ q : vProp :=
  AtomicSeen l γ ζ ∗ ⎡ at_exclusive_write γ tx q ⎤ ∗ ⌜is_Some (ζ !! tx)⌝.
Definition AtomicCASerX_aux : seal (@AtomicCASerX_def). Proof. by eexists. Qed.
Definition AtomicCASerX := unseal (@AtomicCASerX_aux).
Definition AtomicCASerX_eq : @AtomicCASerX = _ := seal_eq _.


Definition AtomicCASer_def l γ ζ q : vProp :=
  ∃ (tx : time), AtomicCASerX l γ tx ζ q.
Definition AtomicCASer_aux : seal (@AtomicCASer_def). Proof. by eexists. Qed.
Definition AtomicCASer := unseal (@AtomicCASer_aux).
Definition AtomicCASer_eq : @AtomicCASer = _ := seal_eq _.
End preds.

Global Instance: Params (@AtomicPtsToX) 5 := {}.
Global Instance: Params (@AtomicPtsTo) 5 := {}.
Global Instance: Params (@AtomicSeen) 4 := {}.
Global Instance: Params (@AtomicSync) 4 := {}.
Global Instance: Params (@AtomicSWriter) 4 := {}.
Global Instance: Params (@AtomicCASerX) 4 := {}.
Global Instance: Params (@AtomicCASerX) 4 := {}.

Notation "l 'casX↦{' γ , tx '}' ζ" := (AtomicPtsToX l γ tx ζ CASOnly)
  (at level 20, format "l  casX↦{ γ , tx }  ζ")  : bi_scope.
Notation "l 'swX↦{' γ , tx '}' ζ" := (AtomicPtsToX l γ tx ζ SingleWriter)
  (at level 20, format "l  swX↦{ γ , tx }  ζ")  : bi_scope.
Notation "l 'atX↦{' γ , tx '}' ζ" := (AtomicPtsToX l γ tx ζ ConcurrentWriter)
  (at level 20, format "l  atX↦{ γ , tx }  ζ")  : bi_scope.

Notation "l 'cas↦{' γ '}' ζ" := (AtomicPtsTo l γ ζ CASOnly)
  (at level 20, format "l  cas↦{ γ }  ζ")  : bi_scope.
Notation "l 'sw↦{' γ '}' ζ" := (AtomicPtsTo l γ ζ SingleWriter)
  (at level 20, format "l  sw↦{ γ }  ζ")  : bi_scope.
Notation "l 'at↦{' γ '}' ζ" := (AtomicPtsTo l γ ζ ConcurrentWriter)
  (at level 20, format "l  at↦{ γ }  ζ")  : bi_scope.

Notation "l 'sn⊒{' γ '}' ζ" := (AtomicSeen l γ ζ)
  (at level 20, format "l  sn⊒{ γ }  ζ")  : bi_scope.
Notation "l 'sy⊒{' γ '}' ζ" := (AtomicSync l γ ζ)
  (at level 20, format "l  sy⊒{ γ }  ζ")  : bi_scope.
Notation "l 'sw⊒{' γ '}' ζ" := (AtomicSWriter l γ ζ)
  (at level 20, format "l  sw⊒{ γ }  ζ")  : bi_scope.
Notation "l 'cas⊒{' γ ',' q '}' ζ" := (AtomicCASer l γ ζ q)
  (at level 20, format "l  cas⊒{ γ , q }  ζ")  : bi_scope.
Notation "l 'casX⊒{' γ ',' t ',' q '}' ζ" := (AtomicCASerX l γ t ζ q)
  (at level 20, format "l  casX⊒{ γ , t , q }  ζ")  : bi_scope.

(** * Properties of [toAbsHist] *)
Lemma toAbsHist_lookup_message C Va t v V :
  toAbsHist C Va !! t = Some (v,V)
  → ∃ m, C !! t = Some m ∧ memval_val_rel m.(mval) v ∧ V = default ∅ m.(mrel) ⊔ Va.
Proof.
  rewrite map_lookup_imap bind_Some.
  move => [m [? Hv]]. exists m. split; [done|].
  case_match; inversion Hv; subst; clear Hv; simpl; split=>//; constructor.
Qed.

Lemma toAbsHist_lookup_state_inv C Va t m v
  (ISV: memval_val_rel m.(mval) v) (HL: C !! t = Some m) :
  toAbsHist C Va !! t = Some (v, default ∅ m.(mrel) ⊔ Va).
Proof. rewrite map_lookup_imap HL /=. by inversion ISV. Qed.

Lemma toAbsHist_lookup_Some C Va t m :
  C !! t = Some m → no_dealloc C →
  ∃ v, toAbsHist C Va !! t = Some (v, default ∅ m.(mrel) ⊔ Va).
Proof.
  move => EqN => /(_ t m EqN) => VAL.
  destruct (mval m) eqn:EqV; [|done|].
  - exists #☠. apply toAbsHist_lookup_state_inv; [rewrite EqV; constructor | done].
  - exists v. apply toAbsHist_lookup_state_inv; [rewrite EqV; constructor | done].
Qed.

Lemma toAbsHist_lookup_None C Va t :
  C !! t = None → toAbsHist C Va !! t = None.
Proof. intros EqN. by rewrite /toAbsHist map_lookup_imap EqN. Qed.

Lemma toAbsHist_singleton Va t m v (ISV: memval_val_rel m.(mval) v) :
  toAbsHist {[t := m]} Va = {[t := (v, default ∅ m.(mrel) ⊔ Va)]}.
Proof.
  apply map_eq. intros t'.
  rewrite /toAbsHist map_lookup_imap.
  case (decide (t' = t)) => [->|?]; last by rewrite !lookup_insert_ne.
  rewrite !lookup_insert.
  destruct m.(mval) eqn:Eq; rewrite /= Eq; by inversion ISV.
Qed.

Global Instance no_dealloc_mono : Proper (flip (⊆) ==> impl) no_dealloc.
Proof.
  rewrite /flip /no_dealloc. move => C1 C2 INCL ND1 t m IS.
  eapply ND1. by eapply lookup_weaken.
Qed.

Lemma no_dealloc_union C1 C2 :
  no_dealloc C1 → no_dealloc C2 → no_dealloc (C1 ∪ C2).
Proof.
  intros ND1 ND2 t m [Eq1|[Eq1 Eq2]]%lookup_union_Some_raw.
  - revert Eq1. apply ND1.
  - revert Eq2. apply ND2.
Qed.

Lemma toAbsHist_union Va C1 C2 (ND1 : no_dealloc C1) (ND2 : no_dealloc C2) :
  toAbsHist (C1 ∪ C2) Va = toAbsHist C1 Va ∪ toAbsHist C2 Va.
Proof.
  apply map_eq. intros t'. rewrite /toAbsHist map_lookup_imap.
  symmetry.
  destruct ((C1 ∪ C2) !! t') as [m|] eqn: Eqt'; simpl.
  - destruct (m.(mval)) as [| |v] eqn:Eqv; simpl.
    + apply lookup_union_Some_raw. rewrite !map_lookup_imap.
      apply lookup_union_Some_raw in Eqt' as [->|[-> ->]]; [left|right];
        by rewrite /= Eqv.
    + exfalso. revert Eqt' Eqv. by apply no_dealloc_union.
    + apply lookup_union_Some_raw. rewrite !map_lookup_imap.
      apply lookup_union_Some_raw in Eqt' as [->|[-> ->]]; [left|right];
        by rewrite /= Eqv.
  - apply lookup_union_None. rewrite !map_lookup_imap.
    by apply lookup_union_None in Eqt' as [-> ->].
Qed.

Lemma toAbsHist_insert C Va t m v
  (ISV: memval_val_rel m.(mval) v) :
  toAbsHist (<[t:=m]> C) Va = <[t:= (v,default ∅ m.(mrel) ⊔ Va)]> (toAbsHist C Va).
Proof.
  apply map_eq => t'. rewrite /toAbsHist map_lookup_imap.
  case (decide (t' = t)) => [->|?].
  - rewrite 2!lookup_insert /=. by inversion ISV.
  - rewrite !lookup_insert_ne // map_lookup_imap. by destruct (C !! t').
Qed.

(** * Properties of [good_hist] *)
Lemma good_hist_mono C1 C2 (NE: C2 ≠ ∅) (SUB: C2 ⊆ C1) :
  good_hist C1 → good_hist C2.
Proof.
  intros [HC1 HC2 HC3 HC4]. constructor; [|done|..].
  - intros DE. apply HC1.
    move : DE. rewrite /cell_deallocated.
    destruct (cell_max C2) as [[t m]|] eqn:Eqm; [|done].
    intros Eq. rewrite (HC4 t m) //. split; [|done].
    by eapply gmap_top_lookup, lookup_weaken in Eqm.
  - intros t m [Eqm Eqv]. apply gmap_top_equiv; try apply _.
    split; [done|].
    have HC3' : cell_min C1 = Some (t, m).
    { apply HC3. split; [|done]. by eapply lookup_weaken. }
    apply gmap_top_equiv in HC3' as [HC3' MIN]; try apply _.
    intros t' IN'. apply MIN. move : IN'. by apply subseteq_dom.
  - intros t m [Eqm Eqv]. apply gmap_top_equiv; try apply _.
    split; [done|].
    have HC4' : cell_max C1 = Some (t, m).
    { apply HC4. split; [|done]. by eapply lookup_weaken. }
    apply gmap_top_equiv in HC4' as [HC4' MAX]; try apply _.
    intros t' IN'. apply MAX. move : IN'. by apply subseteq_dom.
Qed.

Lemma absHist_alloc_local_mono l V C1 C2 ζ1 ζ2 Va
  (EQ1 : ζ1 = toAbsHist C1 Va) (EQ2 : ζ2 = toAbsHist C2 Va)
  (ND1 : no_dealloc C1) (INCL : ζ1 ⊆ ζ2) :
  alloc_local l C1 V → alloc_local l C2 V.
Proof.
  intros ALL.
  set C1' := filter (λ kv, kv.1 ∈ dom ζ1) C2.
  have ALL' : alloc_local l C1' V.
  { destruct ALL as (t & [v OV] & (IS & VAL & SL)). simpl in VAL.
    destruct (toAbsHist_lookup_Some C1 Va t (mkBMes v OV) IS ND1) as (v' & IS').
    have IS2: (toAbsHist C2 Va) !! t = Some (v', default ∅ OV ⊔ Va).
    { eapply lookup_weaken; [done|by rewrite -EQ1 -EQ2]. }
    specialize (toAbsHist_lookup_message _ _ _ _ _ IS2) as (m & ? & MV & ?).
    exists t, m. split; [|split]; last done; last by inversion MV.
    apply map_filter_lookup_Some. split; [done|].
    simpl. eapply elem_of_dom_2. rewrite EQ1. eassumption. }
  eapply alloc_local_mono; [|done..].
  apply map_filter_subseteq.
Qed.

Lemma good_absHist_mono Va ζ1 ζ2 (NE: ζ2 ≠ ∅) (SUB: ζ2 ⊆ ζ1) :
  good_absHist ζ1 Va → good_absHist ζ2 Va.
Proof.
  move => [NE1 [C1 [Eq1 ND1]]]. split; [done|].
  set C2 : cell := (filter (λ kv, kv.1 ∈ dom ζ2) C1).
  exists C2. split; last first.
  { intros t m Eq. apply map_filter_lookup_Some in Eq as [].
    by eapply ND1. }
  apply map_eq. intros t.
  destruct (ζ2 !! t) as [[v V]|] eqn: EqvV; rewrite EqvV.
  - symmetry.
    have Eq' := (lookup_weaken _ _ _ _ EqvV SUB).
    rewrite Eq1 in Eq'.
    apply toAbsHist_lookup_message in Eq' as (m & Eq' & VAL & EqV).
    rewrite EqV.
    apply toAbsHist_lookup_state_inv; [done|].
    apply map_filter_lookup_Some_2; [done|]. simpl. by eapply elem_of_dom_2.
  - symmetry. apply toAbsHist_lookup_None, map_filter_lookup_None_2.
    right. simpl. intros _ _. by apply not_elem_of_dom.
Qed.

Lemma good_absHist_join Va ζ1 ζ2 :
  good_absHist ζ1 Va → good_absHist ζ2 Va → good_absHist (ζ1 ∪ ζ2) Va.
Proof.
  move => [NE1 [C1 [Eq1 ND1]]] [NE2 [C2 [Eq2 ND2]]]. split.
  { by apply map_positive_l_alt. }
  exists (C1 ∪ C2). split.
  - symmetry. rewrite Eq1 Eq2. by apply toAbsHist_union.
  - by apply no_dealloc_union.
Qed.

Lemma good_hist_good_absHist C ζ Va (EQ : ζ = toAbsHist C Va) :
  good_hist C → good_absHist ζ Va.
Proof.
  destruct 1. rewrite /good_absHist.
  have ND : no_dealloc C.
  { rewrite /no_dealloc. intros t m IS VAL.
    apply good_alloc. rewrite /cell_deallocated.
    by rewrite (good_dealloc_max t m). }
  split; [|by exists C].
  apply (gmap_top_nonempty (flip (⊑))) in good_nempty as (t & m & MSG).
  apply gmap_top_lookup in MSG.
  destruct (toAbsHist_lookup_Some _ Va _ _ MSG ND) as [v MSG'].
  intros ->. rewrite -EQ in MSG'.
  destruct (lookup_empty_Some _ _ MSG').
Qed.


Section props.
Context `{!noprolG Σ, !atomicG Σ}.
#[local] Notation iProp := (iProp Σ).
#[local] Notation vProp := (vProp Σ).

#[global] Instance SeenLocal_persistent l ζ :
  Persistent (SeenLocal l ζ : vProp) := _.
#[global] Instance SeenLocal_timeless l ζ :
  Timeless (SeenLocal l ζ : vProp) := _.
#[global] Instance SyncLocal_persistent l ζ :
  Persistent (SyncLocal l ζ : vProp) := _.
#[global] Instance SyncLocal_timeless l ζ :
  Timeless (SyncLocal l ζ : vProp) := _.

#[global] Instance SeenLocal_mono l :
  Proper (flip (⊆) ==> (⊢)) (SeenLocal l : _ → vProp).
Proof.
  iIntros (ζ1 ζ2 SUB) "SL". iIntros (t IS). iApply "SL". iPureIntro.
  eapply lookup_weaken_is_Some; eauto.
Qed.

#[global] Instance SyncLocal_mono l :
  Proper (flip (⊆) ==> (⊢)) (SyncLocal l : _ → vProp).
Proof.
  iIntros (ζ1 ζ2 SUB) "SL". iIntros (t V IS). iApply "SL". iPureIntro.
  destruct (ζ2 !! t) as [vV|] eqn:Eq; [|done].
  by rewrite (lookup_weaken _ _ _ _ Eq SUB).
Qed.

(** AtomicPtsTo *)
Lemma AtomicPtsToX_own_loc_prim l γ tx ζ md :
  AtomicPtsToX l γ tx ζ md ⊢ ∃ C : cell, l p↦{1} C.
Proof.
  rewrite AtomicPtsToX_eq.
  iDestruct 1 as (C Va rsa rns ws (GH & Eq & IS & ND))
                  "((SL & ARL & AWL & #NAL)&H&(AR & AW & NA) & _)".
  iExists C, rsa, rns, ws. iFrame (GH) "∗". iSplitL; last by eauto.
  destruct IS as [[v Vv] Eqv].
  iSpecialize ("SL" $! tx Vv with "[%]"). { by rewrite Eqv. }
  iStopProof. constructor => V /=.
  rewrite monPred_at_sep monPred_at_intuitionistically/=. iPureIntro.
  intros ([NAL LeV] & SL & LeVv). rewrite ->LeV in NAL.
  subst ζ. apply toAbsHist_lookup_message in Eqv as (m & Eqm & Eqv & EqvV).
  exists tx, m. split; [done|]. split; [|done]. by inversion Eqv.
Qed.

Lemma AtomicPtsTo_own_loc_prim l γ ζ md :
  AtomicPtsTo l γ ζ md ⊢ ∃ C : cell, l p↦{1} C.
Proof.
  rewrite AtomicPtsTo_eq. apply bi.exist_elim => ?.
  apply AtomicPtsToX_own_loc_prim.
Qed.

Lemma AtomicPtsToX_exclusive_obj l γ1 t1 ζ1 md1 γ2 t2 ζ2 md2 V1 V2 :
  @{V1} AtomicPtsToX l γ1 t1 ζ1 md1 -∗ @{V2} AtomicPtsToX l γ2 t2 ζ2 md2 -∗ False.
Proof.
  rewrite 2!AtomicPtsToX_own_loc_prim.
  iDestruct 1 as (C1) "A1". iDestruct 1 as (C2) "A2".
  iAssert (@{join V1 V2} l p↦{_ + _} C1)%I with "[A1 A2]" as "A".
  { rewrite own_loc_prim_combine (view_at_mono_2 V1 (V1 ⊔ V2)); [|solve_lat].
    by iApply ("A1" with "[$A2]"). }
  rewrite own_loc_prim_frac_1. by iDestruct "A" as %?.
Qed.

Lemma AtomicPtsTo_exclusive_obj l γ1 ζ1 md1 γ2 ζ2 md2 V1 V2 :
  @{V1} AtomicPtsTo l γ1 ζ1 md1 -∗ @{V2} AtomicPtsTo l γ2 ζ2 md2 -∗ False.
Proof.
  rewrite AtomicPtsTo_eq.
  iIntros "[% H1] [% H2]". iApply (AtomicPtsToX_exclusive_obj with "H1 H2").
Qed.

Lemma AtomicPtsTo_exclusive l γ1 ζ1 md1 γ2 ζ2 md2:
  AtomicPtsTo l γ1 ζ1 md1 -∗ AtomicPtsTo l γ2 ζ2 md2 -∗ False.
Proof. apply view_at_wand_lr, AtomicPtsTo_exclusive_obj. Qed.

(** SeenLocal and SyncLocal *)
Lemma SeenLocal_unfold l ζ V :
  (SeenLocal l ζ : vProp) V ⊢ ⌜∀ t, is_Some (ζ !! t) → seen_local l t V⌝.
Proof. iIntros "S" (t IS). by iApply ("S" $! t IS). Qed.
Lemma SyncLocal_unfold l ζ V :
  (SyncLocal l ζ : vProp) V ⊢
    ⌜∀ t V0 , snd <$> ζ !! t = Some V0 → seen_local l t V ∧ V0 ⊑ V⌝.
Proof.
  iIntros "S" (t V0 IS). iSpecialize ("S" $! t V0 IS).
  rewrite seen_view_seen_time. by iDestruct "S" as "[% %]".
Qed.

Lemma SeenLocal_unfold_singleton l t v V V' :
  let ζ := {[t := (v, V)]} in
  (SeenLocal l ζ : vProp) V' ⊣⊢ ⌜seen_local l t V'⌝.
Proof.
  intros ζ. iSplit.
  - iIntros "S". iApply ("S" $! t with "[%]"). rewrite lookup_insert.
    by eexists.
  - by iIntros "S" (t' V1 -> [vV [<- <-]%lookup_singleton_Some]).
Qed.
Lemma SyncLocal_unfold_singleton l t v V V' :
  let ζ := {[t := (v, V)]} in
  (SyncLocal l ζ : vProp) V' ⊣⊢ ⌜seen_local l t V' ∧ V ⊑ V'⌝.
Proof.
  intros ζ. iSplit.
  - iIntros "S". iApply ("S" $! t with "[%]"). rewrite lookup_insert.
    by eexists.
  - iIntros "[% %]" (t' V1). rewrite /SyncLocal -lookup_fmap lookup_fmap_Some.
    iIntros (V2 ? ([] & ? & []%lookup_singleton_Some)) "!%". simplify_eq.
    simpl. split; [|solve_lat]. eapply seen_local_mono; [|eauto]; done.
Qed.

Lemma SeenLocal_insert l ζ t vV :
  (seen_time l t : vProp) -∗ SeenLocal l ζ -∗ SeenLocal l (<[t := vV]>ζ).
Proof.
  iIntros "st SL". iIntros (t0).
  case (decide (t0 = t)) => [->|?].
  - by iFrame "st".
  - by rewrite lookup_insert_ne.
Qed.

Lemma SyncLocal_insert l ζ t v V :
  (seen_view l t V : vProp) -∗ SyncLocal l ζ -∗ SyncLocal l (<[t := (v,V)]>ζ).
Proof.
  iIntros "st SL". iIntros (t0 V0).
  case (decide (t0 = t)) => [->|?].
  - rewrite lookup_insert /=. iIntros (IS). by simplify_eq.
  - by rewrite lookup_insert_ne.
Qed.

Lemma SyncLocal_SeenLocal l ζ : SyncLocal l ζ ⊢ SeenLocal l ζ : vProp.
Proof.
  iIntros "Sy" (t [[v V] Eq]).
  iDestruct ("Sy" $! t V with "[%]") as "SV". { by rewrite Eq. }
  iDestruct (seen_view_seen_time with "SV") as "[$ _]".
Qed.

Lemma SeenLocal_SyncLocal_singleton l t v V :
  let ζ := {[t := (v, V)]} in
  ⊒V -∗ SeenLocal l ζ -∗ SyncLocal l ζ : vProp.
Proof.
  iIntros (ζ) "SV SL". rewrite /SeenLocal /SyncLocal.
  iIntros (t0 V0 Eq0). rewrite seen_view_seen_time.
  destruct (ζ !! t0) as [[v' V']|] eqn:Eq; [|done].
  simpl in Eq0. simplify_eq.
  apply lookup_singleton_Some in Eq as []. simplify_eq.
  iFrame "SV". iApply "SL". iPureIntro. rewrite lookup_insert. by eexists.
Qed.

Lemma SeenLocal_alloc_local l C t V Va (IS : is_Some (toAbsHist C Va !! t)) :
  SeenLocal l (toAbsHist C Va) V ⊢ ⌜alloc_local l C V⌝ : iProp.
Proof.
  iIntros "SL". iDestruct ("SL" $! t with "[%//]") as %SL.
  destruct IS as [[v V'] IS].
  iPureIntro. apply toAbsHist_lookup_message in IS as (m & Eqm & VAL & EqV).
  exists t, m. repeat split; auto. by inversion VAL.
Qed.

Lemma SeenLocal_join l ζ ζ' :
  (SeenLocal l ζ ∗ SeenLocal l ζ') ⊣⊢ (SeenLocal l (ζ ∪ ζ') : vProp).
Proof.
  iSplit.
  - iIntros "[S1 S2]" (t [vV IS]).
    apply lookup_union_Some_raw in IS as [IS|[IN IS]].
    + iApply "S1". iPureIntro. by eexists.
    + iApply "S2". iPureIntro. by eexists.
  - iIntros "#S". iSplit; iIntros (t [vV IS]).
    + iApply "S". iPureIntro. exists vV. by apply lookup_union_Some_l.
    + destruct (ζ !! t) eqn:Eq.
      * iApply "S". iPureIntro. eexists. by apply lookup_union_Some_l.
      * iApply "S". iPureIntro. eexists. apply lookup_union_Some_raw. by right.
Qed.

(* NOTE for map union : ζ ∪ ζ' ≠ ζ' ∪ ζ. So we cannot prove the reverse of the
  following lemma. *)
Lemma SyncLocal_join l ζ ζ' :
  SyncLocal l ζ -∗ SyncLocal l ζ' -∗ SyncLocal l (ζ ∪ ζ') : vProp.
Proof.
  iIntros "S1 S2" (t V IS).
  destruct ((ζ ∪ ζ') !! t) as [[v' V']|] eqn:Eq; [|done].
  simpl in IS. simplify_eq.
  apply lookup_union_Some_raw in Eq as [IS|[IN IS]].
  + iApply "S1". iPureIntro. by rewrite IS.
  + iApply "S2". iPureIntro. by rewrite IS.
Qed.

(** * Atomic predicates *)
(* Instances *)
#[global] Instance AtomicPtsToX_timeless l γ t ζ b :
  Timeless (AtomicPtsToX l γ t ζ b).
Proof. rewrite AtomicPtsToX_eq /AtomicPtsToX_def. by destruct b; apply _. Qed.

#[global] Instance AtomicPtsTo_timeless l γ ζ b :
  Timeless (AtomicPtsTo l γ ζ b).
Proof. rewrite AtomicPtsTo_eq. apply _. Qed.

#[global] Instance AtomicSeen_persistent l γ ζ : Persistent (AtomicSeen l γ ζ).
Proof. rewrite AtomicSeen_eq. by apply _. Qed.
#[global] Instance AtomicSeen_timeless l γ ζ : Timeless (AtomicSeen l γ ζ).
Proof. rewrite AtomicSeen_eq. by apply _. Qed.

#[global] Instance AtomicSync_persistent l γ ζ : Persistent (AtomicSync l γ ζ).
Proof. rewrite AtomicSync_eq. by apply _. Qed.
#[global] Instance AtomicSync_timeless l γ ζ : Timeless (AtomicSync l γ ζ).
Proof. rewrite AtomicSync_eq. by apply _. Qed.

#[global] Instance AtomicSWriter_timeless l γ ζ : Timeless (l sw⊒{γ} ζ).
Proof. rewrite AtomicSWriter_eq. apply _. Qed.

#[global] Instance AtomicCASerX_timeless l γ t ζ q : Timeless (l casX⊒{γ,t,q} ζ).
Proof. rewrite AtomicCASerX_eq. apply _. Qed.
#[global] Instance AtomicCASerX_fractional l γ t ζ :
  Fractional (AtomicCASerX l γ t ζ).
Proof.
  rewrite /Fractional =>p q. rewrite AtomicCASerX_eq /AtomicCASerX_def.
  setoid_rewrite fractional. iSplit.
  - iIntros "[#$ ([Hp Hq] & #Le)]". iSplitL "Hp"; by iFrame "#∗".
  - iIntros "[[$ [Hp ?]] [_ [Hq ?]]]". by iFrame.
Qed.
#[global] Instance AtomicCASerX_asfractional l γ t ζ q :
  AsFractional (l casX⊒{γ,t,q} ζ) (λ q, l casX⊒{γ,t,q} ζ)%I q.
Proof. split; [done|]. intros ??. by rewrite -fractional. Qed.

Lemma AtomicCASerX_agree_time l γ t1 t2 ζ1 ζ2 q1 q2 :
  l casX⊒{γ,t1,q1} ζ1 -∗ l casX⊒{γ,t2,q2} ζ2 -∗ ⌜ t1 = t2 ⌝.
Proof.
  rewrite AtomicCASerX_eq. iIntros "(_ & H1 & _) (_ & H2 & _)".
  by iDestruct (at_exclusive_write_agree with "H1 H2") as %[_ <-].
Qed.

#[global] Instance AtomicCASer_timeless l γ ζ q : Timeless (l cas⊒{γ,q} ζ).
Proof. rewrite AtomicCASer_eq. apply _. Qed.
#[global] Instance AtomicCASer_fractional l γ ζ :
  Fractional (AtomicCASer l γ ζ).
Proof.
  rewrite /Fractional =>p q. rewrite AtomicCASer_eq /AtomicCASer_def.
  setoid_rewrite fractional. iSplit.
  - iDestruct 1 as (tx) "[Hp Hq]". iSplitL "Hp"; iExists tx; by iFrame.
  - iIntros "[Hp Hq]". iDestruct "Hp" as (tx) "Hp". iDestruct "Hq" as (tx') "Hq".
    iExists tx. iDestruct (AtomicCASerX_agree_time with "Hp Hq") as %->. by iFrame.
Qed.
#[global] Instance AtomicCASer_asfractional l γ ζ q :
  AsFractional (l cas⊒{γ,q} ζ) (λ q, l cas⊒{γ,q} ζ)%I q.
Proof. split; [done|]. intros ??. by rewrite -fractional. Qed.

(* AtomicSeen *)
Lemma AtomicSeen_non_empty l γ ζ : l sn⊒{γ} ζ ⊢ ⌜ ζ ≠ ∅ ⌝.
Proof.
  rewrite AtomicSeen_eq. iIntros "(_ & _ & E)". by iDestruct "E" as (? []) "_".
Qed.

Lemma AtomicSeen_mono l γ ζ1 ζ2 (NE: ζ2 ≠ ∅) (SUB: ζ2 ⊆ ζ1) :
  l sn⊒{γ} ζ1 -∗ l sn⊒{γ} ζ2.
Proof.
  rewrite AtomicSeen_eq. iIntros "(SL & SR & Va)". iDestruct "Va" as (Va ?) "NA".
  iSplit; last iSplit.
  - by iApply (SeenLocal_mono with "SL").
  - by iApply (at_reader_extract with "SR").
  - iExists Va. iFrame "NA". iPureIntro. by eapply good_absHist_mono; eauto.
Qed.

Lemma AtomicSeen_mono_lookup_singleton l γ ζ t v V :
  ζ !! t = Some (v, V) → l sn⊒{γ} ζ ⊢ l sn⊒{γ} {[t := (v, V)]}.
Proof.
  intros. apply AtomicSeen_mono.
  - apply map_non_empty_singleton.
  - by apply map_singleton_subseteq_l.
Qed.

Lemma AtomicSeen_SeenLocal l γ ζ : l sn⊒{γ} ζ ⊢ SeenLocal l ζ.
Proof. rewrite AtomicSeen_eq. by iIntros "[$ _]". Qed.

Lemma AtomicSeen_NaLocal l γ ζ' ζ tx Va :
  l sn⊒{γ} ζ' -∗ ⎡ at_auth γ ζ tx Va ⎤ -∗ ⊒Va.
Proof.
  rewrite AtomicSeen_eq. iIntros "(_ & _ & NA)".
  iDestruct "NA" as (Va' ) "(_ & NL & SN)". iIntros "SA".
  iDestruct (at_auth_at_last_na_agree with "SA SN") as %<-. iFrame "NL".
Qed.

Lemma AtomicSeen_join l γ ζ ζ' :
  l sn⊒{γ} ζ -∗ l sn⊒{γ} ζ' -∗ l sn⊒{γ} (ζ ∪ ζ').
Proof.
  rewrite AtomicSeen_eq. iIntros "(SL1 & SR1 & Va1) (SL2 & SR2 & Va2)".
  iDestruct "Va1" as (Va) "(% & NL & Va1)".
  iDestruct "Va2" as (?) "(% & _ & Va2)".
  iDestruct (at_last_na_agree with "Va1 Va2") as %<-.
  iSplit; last iSplit.
  - rewrite -SeenLocal_join. iFrame.
  - by iApply (at_reader_join with "SR1 SR2").
  - iExists Va. iFrame "NL Va1". iPureIntro. by apply good_absHist_join.
Qed.

Lemma AtomicSeen_join' l γ ζ ζ' :
  l sn⊒{γ} ζ ∗ l sn⊒{γ} ζ' ⊢ l sn⊒{γ} (ζ ∪ ζ').
Proof. apply bi.wand_elim_l', AtomicSeen_join. Qed.

Lemma AtomicPtsToX_AtomicSeen_latest l γ t ζ ζ' m V V' :
  @{V} AtomicPtsToX l γ t ζ m -∗ @{V'} l sn⊒{γ} ζ' -∗ ⌜ζ' ⊆ ζ⌝.
Proof.
  rewrite AtomicPtsToX_eq AtomicSeen_eq.
  iDestruct 1 as (?????) "(_&_&_&_&SA&_)". iIntros "(_ & R & _)".
  by iDestruct (at_auth_reader_latest with "[$SA] [$R]") as %?.
Qed.
Lemma AtomicPtsToX_AtomicSeen_latest_1 l γ t ζ ζ' m V :
  @{V} AtomicPtsToX l γ t ζ m -∗ l sn⊒{γ} ζ' -∗ ⌜ζ' ⊆ ζ⌝.
Proof. apply view_at_wand_r, AtomicPtsToX_AtomicSeen_latest. Qed.
Lemma AtomicPtsToX_AtomicSeen_latest_2 l γ t ζ ζ' m :
  AtomicPtsToX l γ t ζ m -∗ l sn⊒{γ} ζ' -∗ ⌜ζ' ⊆ ζ⌝.
Proof. apply view_at_wand_lr, AtomicPtsToX_AtomicSeen_latest. Qed.

Lemma AtomicPtsTo_AtomicSeen_latest l γ ζ ζ' m V V' :
  @{V} AtomicPtsTo l γ ζ m -∗ @{V'} l sn⊒{γ} ζ' -∗ ⌜ζ' ⊆ ζ⌝.
Proof.
  rewrite AtomicPtsTo_eq view_at_exist. apply bi.exist_elim => ?.
  by apply AtomicPtsToX_AtomicSeen_latest.
Qed.
Lemma AtomicPtsTo_AtomicSeen_latest_1 l γ ζ ζ' m V :
  @{V} AtomicPtsTo l γ ζ m -∗ l sn⊒{γ} ζ' -∗ ⌜ζ' ⊆ ζ⌝.
Proof. apply view_at_wand_r, AtomicPtsTo_AtomicSeen_latest. Qed.
Lemma AtomicPtsTo_AtomicSeen_latest_2 l γ ζ ζ' m :
  AtomicPtsTo l γ ζ m -∗ l sn⊒{γ} ζ' -∗ ⌜ζ' ⊆ ζ⌝.
Proof. apply view_at_wand_lr, AtomicPtsTo_AtomicSeen_latest. Qed.

Lemma AtomicSeen_union_equiv l γ ζ1 ζ2 V1 V2 :
  @{V1} l sn⊒{γ} ζ1 -∗ @{V2} l sn⊒{γ} ζ2 -∗ ⌜ ζ1 ∪ ζ2 = ζ2 ∪ ζ1 ⌝.
Proof.
  rewrite AtomicSeen_eq.
  iDestruct 1 as "(_ & AT1 & _)". iDestruct 1 as "(_ & AT2 & _)".
  rewrite !view_at_objective_iff.
  by iDestruct (at_reader_union_eq with "AT1 AT2") as %?.
Qed.
Lemma AtomicSeen_union_equiv_1 l γ ζ1 ζ2 :
  l sn⊒{γ} ζ1 -∗ l sn⊒{γ} ζ2 -∗ ⌜ ζ1 ∪ ζ2 = ζ2 ∪ ζ1 ⌝.
Proof.
  iIntros "H1 H2".
  iApply (view_at_wand_lr with "H1 H2"). iIntros (V1 V2) "H1 H2".
  iApply (AtomicSeen_union_equiv with "H1 H2").
Qed.

(* AtomicSync *)
Lemma AtomicSync_mono l γ ζ1 ζ2 (NE: ζ2 ≠ ∅) (SUB: ζ2 ⊆ ζ1) :
  l sy⊒{γ} ζ1 ⊢ l sy⊒{γ} ζ2.
Proof.
  rewrite AtomicSync_eq. iIntros "(SL & SR & Va)".
  iDestruct "Va" as (Va GH) "Na".
  iSplit; last iSplit.
  - by iApply (SyncLocal_mono with "SL").
  - by iApply (at_reader_extract with "SR").
  - iExists Va. iFrame. iPureIntro. eapply good_absHist_mono; eauto.
Qed.

Lemma AtomicSync_AtomicSeen l γ ζ : l sy⊒{γ} ζ ⊢ l sn⊒{γ} ζ.
Proof.
  by rewrite AtomicSync_eq AtomicSeen_eq
            /AtomicSync_def /AtomicSeen_def SyncLocal_SeenLocal.
Qed.

Lemma AtomicSync_mono_lookup_singleton l γ ζ t v V :
  ζ !! t = Some (v, V) → l sy⊒{γ} ζ ⊢ l sy⊒{γ} {[t := (v, V)]}.
Proof.
  intros. apply AtomicSync_mono.
  - apply map_non_empty_singleton.
  - by apply map_singleton_subseteq_l.
Qed.

Lemma AtomicSync_SyncLocal l γ ζ : l sy⊒{γ} ζ ⊢ SyncLocal l ζ.
Proof. rewrite AtomicSync_eq. by iIntros "[$ _]". Qed.

Lemma AtomicSync_lookup l γ ζ t v V :
  ζ !! t = Some (v, V) → l sy⊒{γ} ζ ⊢ ⊒V.
Proof.
  intros. rewrite AtomicSync_mono_lookup_singleton; [|eauto].
  rewrite AtomicSync_SyncLocal.
  constructor => ?. rewrite SyncLocal_unfold_singleton. iPureIntro. by intros [].
Qed.

Lemma AtomicSeen_AtomicSync_singleton l γ t v V :
  let ζ := {[t := (v, V)]} in
  ⊒V -∗ l sn⊒{γ} ζ -∗ l sy⊒{γ} ζ.
Proof.
  rewrite AtomicSync_eq AtomicSeen_eq /AtomicSync_def /AtomicSeen_def.
  iIntros "SV [SL $]".
  by iApply (SeenLocal_SyncLocal_singleton with "SV SL").
Qed.

Lemma AtomicPtsToX_AtomicSync l γ t ζ m :
  AtomicPtsToX l γ t ζ m -∗ l sy⊒{γ} ζ.
Proof.
  rewrite AtomicPtsToX_eq AtomicSync_eq.
  iDestruct 1 as (?????) "(F & ($ & ? & ? & NL) & ? & ? & (W & SW & NA) & _)".
  iDestruct "F" as %(GH & EQ & IS & ND). iSplitL "W".
  - by iApply (at_auth_writer_fork_at_reader with "W").
  - iExists Va. iFrame. iDestruct (NaLocal_seen with "NL") as "$".
    iPureIntro. split; last by exists C.
    move => EqE. move : IS. by rewrite EqE => [[?]].
Qed.
Lemma AtomicPtsToX_AtomicSeen l γ t ζ m :
  AtomicPtsToX l γ t ζ m -∗ l sn⊒{γ} ζ.
Proof. rewrite AtomicPtsToX_AtomicSync. by apply AtomicSync_AtomicSeen. Qed.

Lemma AtomicPtsTo_AtomicSync l γ ζ m :
  AtomicPtsTo l γ ζ m -∗ l sy⊒{γ} ζ.
Proof.
  rewrite AtomicPtsTo_eq. apply bi.exist_elim => ?.
  by apply AtomicPtsToX_AtomicSync.
Qed.
Lemma AtomicPtsTo_AtomicSeen l γ ζ m :
  AtomicPtsTo l γ ζ m -∗ l sn⊒{γ} ζ.
Proof. rewrite AtomicPtsTo_AtomicSync. by apply AtomicSync_AtomicSeen. Qed.

Lemma AtomicSync_join l γ ζ ζ' :
  l sy⊒{γ} ζ -∗ l sy⊒{γ} ζ' -∗ l sy⊒{γ} (ζ ∪ ζ').
Proof.
  rewrite AtomicSync_eq.
  iIntros "(SL1 & SR1 & Va1) (SL2 & SR2 & Va2)".
  iDestruct "Va1" as (Va ?) "[NL Va1]". iDestruct "Va2" as (??) "[_ Va2]".
  iDestruct (at_last_na_agree with "Va1 Va2") as %<-.
  iSplit; last iSplit.
  - by iApply (SyncLocal_join with "SL1 SL2").
  - by iApply (at_reader_join with "SR1 SR2").
  - iExists Va. iFrame. iPureIntro. by apply good_absHist_join.
Qed.

Lemma AtomicPtsTo_AtomicSync_latest l γ ζ ζ' m V V' :
  @{V} AtomicPtsTo l γ ζ m -∗ @{V'} l sy⊒{γ} ζ' -∗ ⌜ζ' ⊆ ζ⌝.
Proof.
  iIntros "P C". iApply (AtomicPtsTo_AtomicSeen_latest with "P").
  by rewrite AtomicSync_AtomicSeen.
Qed.
Lemma AtomicPtsTo_AtomicSync_latest_1 l γ ζ ζ' m V :
  @{V} AtomicPtsTo l γ ζ m -∗ l sy⊒{γ} ζ' -∗ ⌜ζ' ⊆ ζ⌝.
Proof. apply view_at_wand_r, AtomicPtsTo_AtomicSync_latest. Qed.
Lemma AtomicPtsTo_AtomicSync_latest_2 l γ ζ ζ' m :
  AtomicPtsTo l γ ζ m -∗ l sy⊒{γ} ζ' -∗ ⌜ζ' ⊆ ζ⌝.
Proof. apply view_at_wand_lr, AtomicPtsTo_AtomicSync_latest. Qed.

(* AtomicSWriter *)
Lemma AtomicSWriter_AtomicSync l γ ζ : l sw⊒{γ} ζ -∗ l sy⊒{γ} ζ.
Proof. rewrite AtomicSWriter_eq. iDestruct 1 as "([$ _] & _)". Qed.

Lemma AtomicSWriter_AtomicSeen l γ ζ : l sw⊒{γ} ζ -∗ l sn⊒{γ} ζ.
Proof. rewrite -AtomicSync_AtomicSeen. by apply AtomicSWriter_AtomicSync. Qed.

Lemma AtomicSWriter_exclusive_obj l γ ζ1 ζ2 V1 V2:
  @{V1} l sw⊒{γ} ζ1 -∗ @{V2} l sw⊒{γ} ζ2 -∗ False.
Proof.
  rewrite AtomicSWriter_eq. iIntros "[[_ W1] _] [[_ W2] _]".
  by iDestruct (at_writer_exclusive with "[$W1] [$W2]") as %?.
Qed.
Lemma AtomicSWriter_exclusive l γ ζ1 ζ2 :
  l sw⊒{γ} ζ1 -∗ l sw⊒{γ} ζ2 -∗ False.
Proof. apply view_at_wand_lr, AtomicSWriter_exclusive_obj. Qed.

Lemma at_writer_AtomicSeen_latest l γ ζ1 ζ2 V2 :
  ⎡ at_writer γ ζ2 ⎤ -∗ @{V2} l sn⊒{γ} ζ1 -∗ ⌜ζ1 ⊆ ζ2⌝.
Proof.
  rewrite AtomicSeen_eq. iIntros "W (_ & R & _)".
  by iDestruct (at_writer_latest with "W [$R]") as %?.
Qed.
Lemma at_writer_AtomicSeen_latest_1 l γ ζ1 ζ2 :
  ⎡ at_writer γ ζ2 ⎤ -∗ l sn⊒{γ} ζ1 -∗ ⌜ζ1 ⊆ ζ2⌝.
Proof.
  apply view_at_wand_lr. intros. rewrite view_at_objective_iff.
  by apply at_writer_AtomicSeen_latest.
Qed.

Lemma AtomicSWriter_latest_obj l γ ζ1 ζ2 V1 V2 :
  @{V1} l sw⊒{γ} ζ2 -∗ @{V2} l sn⊒{γ} ζ1 -∗ ⌜ζ1 ⊆ ζ2⌝.
Proof.
  rewrite AtomicSWriter_eq. iIntros "[[_ W] _]".
  iApply (at_writer_AtomicSeen_latest with "[$W]").
Qed.
Lemma AtomicSWriter_latest l γ ζ1 ζ2 :
  l sw⊒{γ} ζ2 -∗ l sn⊒{γ} ζ1 -∗ ⌜ζ1 ⊆ ζ2⌝.
Proof. apply view_at_wand_lr, AtomicSWriter_latest_obj. Qed.

Lemma AtomicSWriter_AtomicPtsToX_NonSW_excluded_obj
  l γ ζ1 t2 ζ2 mode (NSW: mode ≠ SingleWriter) V1 V2 :
  @{V1} l sw⊒{γ} ζ1 -∗ @{V2} AtomicPtsToX l γ t2 ζ2 mode -∗ False.
Proof.
  rewrite AtomicSWriter_eq AtomicPtsToX_eq.
  iIntros "[[_ W1] _]". iDestruct 1 as (?????) "(_&_&_&_&_&W2)".
  destruct mode; [done|..|iDestruct "W2" as "[W2 _]"];
    by iDestruct (at_writer_exclusive with "[$W1] [$W2]") as %?.
Qed.

Lemma AtomicSWriter_AtomicPtsToX_is_SW
  l γ ζ1 t2 ζ2 mode V1 V2 :
  @{V1} l sw⊒{γ} ζ1 -∗ @{V2} AtomicPtsToX l γ t2 ζ2 mode -∗ ⌜ mode = SingleWriter ⌝.
Proof.
  iIntros "W P". destruct mode; [done|..];
    by iDestruct (AtomicSWriter_AtomicPtsToX_NonSW_excluded_obj with "W P") as %?.
Qed.
Lemma AtomicSWriter_AtomicPtsToX_is_SW_1
  l γ ζ1 t2 ζ2 mode V2 :
  l sw⊒{γ} ζ1 -∗ @{V2} AtomicPtsToX l γ t2 ζ2 mode -∗ ⌜ mode = SingleWriter ⌝.
Proof. by apply view_at_wand_l, AtomicSWriter_AtomicPtsToX_is_SW. Qed.
Lemma AtomicSWriter_AtomicPtsToX_is_SW_2
  l γ ζ1 t2 ζ2 mode :
  l sw⊒{γ} ζ1 -∗ AtomicPtsToX l γ t2 ζ2 mode -∗ ⌜ mode = SingleWriter ⌝.
Proof. by apply view_at_wand_lr, AtomicSWriter_AtomicPtsToX_is_SW. Qed.


Lemma AtomicSWriter_AtomicPtsTo_NonSW_excluded_obj
  l γ ζ1 ζ2 mode (NSW: mode ≠ SingleWriter) V1 V2 :
  @{V1} l sw⊒{γ} ζ1 -∗ @{V2} AtomicPtsTo l γ ζ2 mode -∗ False.
Proof.
  rewrite AtomicPtsTo_eq. iIntros "H1 [% H2]".
  by iApply (AtomicSWriter_AtomicPtsToX_NonSW_excluded_obj with "H1 H2").
Qed.
Lemma AtomicSWriter_AtomicPtsTo_NonSW_excluded
  l γ ζ1 ζ2 mode (NSW: mode ≠ SingleWriter) :
  l sw⊒{γ} ζ1 -∗ AtomicPtsTo l γ ζ2 mode -∗ False.
Proof. by apply view_at_wand_lr, AtomicSWriter_AtomicPtsTo_NonSW_excluded_obj. Qed.

Lemma AtomicSWriter_CASerX_excluded l γ ζ1 ζ2 t q2 V1 V2 :
  @{V1} l sw⊒{γ} ζ1 -∗ @{V2} l casX⊒{γ,t,q2} ζ2 -∗ False.
Proof.
  rewrite AtomicSWriter_eq AtomicCASerX_eq.
  iIntros "[_ [% [E1 _]]] [_ [E2 _]]".
  by iDestruct (at_exclusive_write_agree with "[$E1] [$E2]")
    as %[?%Qp.not_add_le_l _].
Qed.
Lemma AtomicSWriter_CASerX_excluded_1 l γ ζ1 ζ2 t q2 V2 :
  l sw⊒{γ} ζ1 -∗ @{V2} l casX⊒{γ,t,q2} ζ2 -∗ False.
Proof. apply view_at_wand_l, AtomicSWriter_CASerX_excluded. Qed.
Lemma AtomicSWriter_CASerX_excluded_2 l γ ζ1 ζ2 t q2 :
  l sw⊒{γ} ζ1 -∗ l casX⊒{γ,t,q2} ζ2 -∗ False.
Proof. apply view_at_wand_lr, AtomicSWriter_CASerX_excluded. Qed.

Lemma AtomicPtsToX_at_writer_agree l γ t1 ζ1 ζ2 mode V1 :
  @{V1}(AtomicPtsToX l γ t1 ζ1 mode) -∗ ⎡ at_writer γ ζ2 ⎤ -∗ ⌜ζ1 = ζ2⌝.
Proof.
  rewrite AtomicPtsToX_eq. iDestruct 1 as (?????) "(_&_&_&_&SA&_)". iIntros "W".
  by iDestruct (at_auth_all_writer_exact with "[$SA] [$W]") as %?.
Qed.

Lemma AtomicPtsToX_SWriter_agree l γ t1 ζ1 ζ2 mode V1 V2 :
  @{V1}(AtomicPtsToX l γ t1 ζ1 mode) -∗ @{V2} l sw⊒{γ} ζ2 -∗ ⌜ζ1 = ζ2⌝.
Proof.
  rewrite AtomicSWriter_eq. iIntros "P [[_ W] _]".
  iApply (AtomicPtsToX_at_writer_agree with "P [$W]").
Qed.
Lemma AtomicPtsToX_AtomicSWriter_agree_1 l γ t1 ζ1 ζ2 mode V1 :
  @{V1}(AtomicPtsToX l γ t1 ζ1 mode) -∗ l sw⊒{γ} ζ2 -∗ ⌜ζ1 = ζ2⌝.
Proof. apply view_at_wand_r, AtomicPtsToX_SWriter_agree. Qed.
Lemma AtomicPtsToX_AtomicSWriter_agree_2 l γ t1 ζ1 ζ2 mode :
  AtomicPtsToX l γ t1 ζ1 mode -∗ l sw⊒{γ} ζ2 -∗ ⌜ζ1 = ζ2⌝.
Proof. apply view_at_wand_lr, AtomicPtsToX_SWriter_agree. Qed.

Lemma AtomicPtsTo_SWriter_agree l γ ζ1 ζ2 mode V1 V2 :
  @{V1}(AtomicPtsTo l γ ζ1 mode) -∗ @{V2} l sw⊒{γ} ζ2 -∗ ⌜ζ1 = ζ2⌝.
Proof.
  rewrite AtomicPtsTo_eq view_at_exist. apply bi.exist_elim => ?.
  by apply AtomicPtsToX_SWriter_agree.
Qed.
Lemma AtomicPtsTo_AtomicSWriter_agree_1 l γ ζ1 ζ2 mode V1 :
  @{V1}(AtomicPtsTo l γ ζ1 mode) -∗ l sw⊒{γ} ζ2 -∗ ⌜ζ1 = ζ2⌝.
Proof. apply view_at_wand_r, AtomicPtsTo_SWriter_agree. Qed.
Lemma AtomicPtsTo_AtomicSWriter_agree_2 l γ ζ1 ζ2 mode :
  AtomicPtsTo l γ ζ1 mode -∗ l sw⊒{γ} ζ2 -∗ ⌜ζ1 = ζ2⌝.
Proof. apply view_at_wand_lr, AtomicPtsTo_SWriter_agree. Qed.

(* AtomicCASer *)
Lemma AtomicCASerX_AtomicSeen l γ t ζ q : l casX⊒{γ,t,q} ζ -∗ l sn⊒{γ} ζ.
Proof. rewrite AtomicCASerX_eq. by iIntros "[$ _]". Qed.
Lemma AtomicCASer_AtomicSeen l γ ζ q : l cas⊒{γ,q} ζ -∗ l sn⊒{γ} ζ.
Proof.
  rewrite AtomicCASer_eq. apply bi.exist_elim => ?.
  apply : AtomicCASerX_AtomicSeen.
Qed.

Lemma AtomicPtsToX_AtomicCASerX_latest l γ t ζ t' ζ' m q V V' :
  @{V} AtomicPtsToX l γ t ζ m -∗ @{V'} l casX⊒{γ,t',q} ζ' -∗ ⌜ t' = t ∧ ζ' ⊆ ζ ⌝.
Proof.
  rewrite AtomicCASerX_eq. iIntros "P [S [SW _]]".
  iDestruct (AtomicPtsToX_AtomicSeen_latest with  "P S") as %?.
  rewrite AtomicPtsToX_eq.
  iDestruct "P" as (C Va rsa rns ws) "(_ & _ & _ & _ & SA & _)".
  by iDestruct (at_full_auth_exclusive_write_agree with "[$SA] [$SW]") as %<-.
Qed.
Lemma AtomicPtsToX_AtomicCASerX_latest_1 l γ t ζ t' ζ' m q V :
  @{V} AtomicPtsToX l γ t ζ m -∗ l casX⊒{γ,t',q} ζ' -∗ ⌜ t' = t ∧ ζ' ⊆ ζ ⌝.
Proof. apply view_at_wand_r, AtomicPtsToX_AtomicCASerX_latest. Qed.
Lemma AtomicPtsToX_AtomicCASerX_latest_2 l γ t ζ t' ζ' m q :
  AtomicPtsToX l γ t ζ m -∗ l casX⊒{γ,t', q} ζ' -∗ ⌜ t' = t ∧ ζ' ⊆ ζ ⌝.
Proof. apply view_at_wand_lr, AtomicPtsToX_AtomicCASerX_latest. Qed.

Lemma AtomicPtsTo_AtomicCASer_latest l γ ζ ζ' m q V V' :
  @{V} AtomicPtsTo l γ ζ m -∗ @{V'} l cas⊒{γ,q} ζ' -∗ ⌜ζ' ⊆ ζ⌝.
Proof.
  iIntros "P C". iApply (AtomicPtsTo_AtomicSeen_latest with "P").
  by rewrite AtomicCASer_AtomicSeen.
Qed.
Lemma AtomicPtsTo_AtomicCASer_latest_1 l γ ζ ζ' m q V :
  @{V} AtomicPtsTo l γ ζ m -∗ l cas⊒{γ,q} ζ' -∗ ⌜ζ' ⊆ ζ⌝.
Proof. apply view_at_wand_r, AtomicPtsTo_AtomicCASer_latest. Qed.
Lemma AtomicPtsTo_AtomicCASer_latest_2 l γ ζ ζ' m q :
  AtomicPtsTo l γ ζ m -∗ l cas⊒{γ,q} ζ' -∗ ⌜ζ' ⊆ ζ⌝.
Proof. apply view_at_wand_lr, AtomicPtsTo_AtomicCASer_latest. Qed.

Lemma AtomicCASerX_AtomicPtsToX_is_not_concurrent
  l γ t1 q ζ1 t2 ζ2 mode V1 V2 :
  @{V1} l casX⊒{γ,t1,q} ζ1 -∗ @{V2} AtomicPtsToX l γ t2 ζ2 mode -∗
  ⌜ mode ≠ ConcurrentWriter  ⌝.
Proof.
  rewrite AtomicCASerX_eq AtomicPtsToX_eq.
  iIntros "(_ & W1 & _)". iDestruct 1 as (?????) "(_&_&_&_&_&W2)".
  destruct mode; [done..|]. iDestruct "W2" as "[_ W2]".
  by iDestruct (at_exclusive_write_agree with "[$W1] [$W2]")
    as %[?%Qp.not_add_le_r _] .
Qed.

Lemma AtomicPtsToX_exclusive_write_agree l γ tx ζ m tx' q :
  AtomicPtsToX l γ tx ζ m -∗ ⎡ at_exclusive_write γ tx' q ⎤ -∗
  ⌜ tx' = tx ⌝.
Proof.
  iIntros "P Ex". rewrite AtomicPtsToX_eq.
  iDestruct "P" as (C Va rsa rns ws) "(F & SLs & HI & ATs & SA & W)".
  by iDestruct (at_full_auth_exclusive_write_agree with "SA Ex") as %<-.
Qed.

Lemma AtomicCASerX_AtomicSeen_join_l_obj l γ t ζ q V :
  @{V} l casX⊒{γ,t,q} ζ -∗ l sn⊒{γ} ζ -∗ l casX⊒{γ,t,q} ζ.
Proof. rewrite AtomicCASerX_eq. iIntros "[_ [$ %]] $". by iPureIntro. Qed.
Lemma AtomicCASer_AtomicSeen_join_l_obj l γ ζ q V :
  @{V} l cas⊒{γ,q} ζ -∗ l sn⊒{γ} ζ -∗ l cas⊒{γ,q} ζ.
Proof.
  rewrite AtomicCASer_eq. iIntros "[% C] S". iExists _.
  iApply (AtomicCASerX_AtomicSeen_join_l_obj with "C S").
Qed.

Lemma AtomicCASerXs_join l γ t1 t2 ζ1 ζ2 q1 q2 :
  l casX⊒{γ,t1,q1} ζ1 -∗ l casX⊒{γ,t2,q2} ζ2 -∗ l casX⊒{γ,t1,q1 + q2} (ζ1 ∪ ζ2).
Proof.
  rewrite AtomicCASerX_eq.
  iIntros "[S1 [SW [%vV %IS]]] [S2 [SW' %]]".
  iSplitL "S1 S2"; first by iApply (AtomicSeen_join with "S1 S2"). iSplit.
  - by iApply (at_exclusive_write_join with "SW SW'").
  - iPureIntro. eexists. by apply lookup_union_Some_l.
Qed.

Lemma AtomicCASers_join l γ ζ1 ζ2 q1 q2 :
  l cas⊒{γ,q1} ζ1 -∗ l cas⊒{γ,q2} ζ2 -∗ l cas⊒{γ,q1 + q2} (ζ1 ∪ ζ2).
Proof.
  rewrite AtomicCASer_eq.
  iDestruct 1 as (t1) "C1". iDestruct 1 as (t2) "C2".
  iExists t1. iApply (AtomicCASerXs_join with "C1 C2").
Qed.

Lemma AtomicCASerX_AtomicSeen_update_join l γ t ζ q ζ' :
  l casX⊒{γ,t,q} ζ -∗ l sn⊒{γ} ζ' -∗ l casX⊒{γ,t,q} (ζ ∪ ζ').
Proof.
  iIntros " C S". rewrite AtomicCASerX_eq.
  iDestruct "C" as "[S1 [SW [% %IS]]]".
  iDestruct (AtomicSeen_join' with "[$S1 $S]") as "$". iFrame "SW".
  iPureIntro. eexists. by apply lookup_union_Some_l.
Qed.

Lemma AtomicCASer_AtomicSeen_update_join l γ ζ q ζ' :
  l cas⊒{γ,q} ζ -∗ l sn⊒{γ} ζ' -∗ l cas⊒{γ,q} (ζ ∪ ζ').
Proof.
  rewrite AtomicCASer_eq. iIntros "[%tx C] S". iExists tx.
  by iApply (AtomicCASerX_AtomicSeen_update_join with "C S").
Qed.

Lemma AtomicPtsTo_AtomicCASer_update l γ ζ ζ' m q :
  AtomicPtsTo l γ ζ m -∗ l cas⊒{γ,q} ζ' -∗ AtomicPtsTo l γ ζ m ∗ l cas⊒{γ,q} ζ.
Proof.
  iIntros "P C". iDestruct (AtomicPtsTo_AtomicCASer_latest_2 with "P C") as %SUB.
  iDestruct (AtomicPtsTo_AtomicSeen with "P") as "#S".
  iDestruct (AtomicCASer_AtomicSeen_update_join with "C S") as "C".
  rewrite map_subseteq_union; [|done]. iFrame.
Qed.

(* CAS and CON *)
Lemma AtomicPtsToX_SW_max_time l γ tx ζ m V1 V2 :
  @{V1} AtomicPtsToX l γ tx ζ m -∗ @{V2} l sw⊒{γ} ζ -∗ ⌜ max_time tx ζ ⌝.
Proof.
  rewrite AtomicPtsToX_eq /AtomicPtsToX_def AtomicSWriter_eq /AtomicSWriter_def.
  iDestruct 1 as (C Va rsa rns ws) "(_ & _ & _ & _ & A & _)".
  iDestruct 1 as "(_ & %tx' & Ex & %)".
  by iDestruct (at_full_auth_exclusive_write_agree with "[$A] [$Ex]") as %<-.
Qed.
Lemma AtomicPtsToX_SW_max_time_1 l γ tx ζ m V1 :
  @{V1} AtomicPtsToX l γ tx ζ m -∗ l sw⊒{γ} ζ -∗ ⌜ max_time tx ζ ⌝.
Proof. by apply view_at_wand_r, AtomicPtsToX_SW_max_time. Qed.

Lemma AtomicPtsToX_is_SomeX l γ tx ζ m :
  AtomicPtsToX l γ tx ζ m ⊢ ⌜ is_Some (ζ !! tx) ⌝.
Proof.
  rewrite AtomicPtsToX_eq /AtomicPtsToX_def.
  iDestruct 1 as (C Va rsa rns ws) "(F & _)".
  by iDestruct "F" as %(?&?&?&?).
Qed.

Lemma AtomicPtsToX_CON_CAS l γ tx ζ :
  l atX↦{γ,tx} ζ ⊣⊢
  l casX↦{γ,tx} ζ ∗ ⎡ at_exclusive_write γ tx 1 ⎤.
Proof.
  rewrite AtomicPtsToX_eq /AtomicPtsToX_def. iSplit.
  - iDestruct 1 as (C Va rsa rns ws) "(F & SLs & HI & ATs & SA & W & $)".
    iExists C, Va, rsa, rns, ws. by iFrame.
  - iIntros "[C $]". by iFrame.
Qed.

Lemma AtomicPtsTo_CON_CAS l γ ζ :
  l at↦{γ} ζ ⊣⊢
  l cas↦{γ} ζ ∗ (∃ tx, ⎡ at_exclusive_write γ tx 1 ⎤).
Proof.
  rewrite AtomicPtsTo_eq /AtomicPtsTo_def.
  setoid_rewrite AtomicPtsToX_CON_CAS. iSplit.
  - iIntros "[%tx [H1 H2]]". iSplitL "H1"; by iExists _.
  - iIntros "[[%tx1 H1] [%tx2 H2]]".
    iDestruct (AtomicPtsToX_exclusive_write_agree with "H1 H2") as %->.
    iExists _. by iFrame.
Qed.

Lemma AtomicPtsTo_CON_CAS' l γ ζ :
  l at↦{γ} ζ ⊣⊢
  l cas↦{γ} ζ ∗ (∃ tx, ⎡ at_exclusive_write γ tx 1 ⎤ ∗ ⌜is_Some (ζ !! tx)⌝).
Proof.
  rewrite AtomicPtsTo_eq /AtomicPtsTo_def.
  setoid_rewrite AtomicPtsToX_CON_CAS. iSplit.
  - iIntros "[%tx [H1 H2]]". iDestruct (AtomicPtsToX_is_SomeX with "H1") as %?.
    iSplitL "H1"; iExists _; by iFrame.
  - iIntros "[[%tx1 H1] [%tx2 [H2 ?]]]".
    iDestruct (AtomicPtsToX_exclusive_write_agree with "H1 H2") as %->.
    iExists _. by iFrame.
Qed.

(** * Conversion between concurrent and cas-only modes for AtomicPtsTo *)
Lemma AtomicPtsToX_CON_CAS_1 l γ t ζ :
  l atX↦{γ,t} ζ ⊣⊢ l casX↦{γ,t} ζ ∗ l casX⊒{γ,t,1} ζ.
Proof.
  rewrite AtomicCASerX_eq AtomicPtsToX_CON_CAS. iSplit.
  - iIntros "[C Ex]". iDestruct (AtomicPtsToX_AtomicSeen with "C") as "#$".
    iDestruct (AtomicPtsToX_is_SomeX with "C") as %?.
    by iFrame.
  - iIntros "(C & sn & Ex & ?)". by iFrame.
Qed.

Lemma AtomicPtsTo_CON_CAS_1 l γ ζ :
  l at↦{γ} ζ ⊣⊢ l cas↦{γ} ζ ∗ l cas⊒{γ,1} ζ.
Proof.
  rewrite AtomicPtsTo_eq /AtomicPtsTo_def AtomicCASer_eq.
  setoid_rewrite AtomicPtsToX_CON_CAS_1.
  iSplit.
  - iDestruct 1 as (tx) "[P C]". iSplitL "P"; by iExists _.
  - iIntros "[[%t1 P] [%t2 C]]".
    iDestruct (AtomicPtsToX_AtomicCASerX_latest_2 with "P C") as %[-> _].
    iExists _; iFrame.
Qed.

Lemma AtomicPtsTo_CON_CAS_2 l γ ζ V1 V2 :
  @{V1} l cas⊒{γ,1} ζ ∗ @{V2} l cas↦{γ} ζ ⊢ @{V2} l at↦{γ} ζ.
Proof.
  rewrite AtomicPtsTo_CON_CAS' AtomicCASer_eq /AtomicCASer_def AtomicCASerX_eq.
  iIntros "[(% & ? & ?) $]". iExists _. by rewrite !view_at_objective_iff.
Qed.

(** * Conversion from single-writer mode to cas-only mode for AtomicPtsTo *)
Lemma AtomicPtsToX_SW_to_CAS l γ t ζ ζ' V0 :
  @{V0} l swX↦{γ,t} ζ -∗ l sw⊒{γ} ζ' -∗ @{V0} l casX↦{γ,t} ζ ∗ l casX⊒{γ,t,1} ζ.
Proof.
  rewrite AtomicSWriter_eq AtomicCASerX_eq AtomicPtsToX_eq.
  iDestruct 1 as (C Va rsa rns ws) "(F & (SL & ATLs) & HI & ATs & SA & %)".
  iDestruct "F" as %(?&?&?&?).
  iDestruct 1 as "[[SY SE] SW]".
  iDestruct "SW" as (t') "[SW MAX]".
  iDestruct (at_auth_all_writer_exact with "[$SA] SE") as %<-.
  iDestruct (at_full_auth_exclusive_write_agree with "[$SA] SW") as %<-.
  iSplitR "SY SW"; last iSplit.
  - iExists _,_,_,_,_. by iFrame.
  - by iApply AtomicSync_AtomicSeen.
  - by iFrame.
Qed.
Lemma AtomicPtsToX_SW_to_CAS_1 l γ t ζ ζ' :
  l swX↦{γ,t} ζ -∗ l sw⊒{γ} ζ' -∗ l casX↦{γ,t} ζ ∗ l casX⊒{γ,t,1} ζ.
Proof.
  iIntros "P W".
  iDestruct (view_at_intro with "P") as (V) "[sV P]".
  iDestruct (AtomicPtsToX_SW_to_CAS with "P W") as "[P $]".
  iApply (view_at_elim with "sV P").
Qed.

Lemma AtomicPtsTo_SW_to_CAS l γ ζ ζ' V0 :
  @{V0} l sw↦{γ} ζ -∗ l sw⊒{γ} ζ' -∗ @{V0} l cas↦{γ} ζ ∗ l cas⊒{γ,1} ζ.
Proof.
  rewrite AtomicPtsTo_eq AtomicCASer_eq.
  iDestruct 1 as (tx) "P". iIntros "W".
  iDestruct (AtomicPtsToX_SW_to_CAS with "P W") as "[P C]".
  iSplitL "P"; by iExists _.
Qed.

Lemma AtomicSWriter_AtomicCASerX l γ ζ :
  l sw⊒{γ} ζ ⊢
  l sy⊒{γ} ζ ∗ ∃ tx, l casX⊒{γ,tx,1} ζ ∗ ⎡ at_writer γ ζ ⎤ ∗ ⌜ max_time tx ζ ⌝.
Proof.
  rewrite AtomicSWriter_eq AtomicCASerX_eq.
  iIntros "([SY W] & %tx & EW & %IS)".
  iDestruct (AtomicSync_AtomicSeen with "SY") as "#SS". iFrame "SY".
  iExists tx. iFrame (IS) "W". iFrame "SS EW". iPureIntro. apply IS.
Qed.

(** * Conversion from cas-only mode back to single-writer mode for AtomicPtsTo *)
(* A bupd is needed to update the exclusive timestamp. *)

Lemma AtomicCASerX_AtomicWriter l γ tx ζ ζ' V :
  max_time tx ζ →
  l sy⊒{γ} ζ -∗ @{V} l casX⊒{γ,tx,1} ζ' -∗ ⎡ at_writer γ ζ ⎤ -∗ l sw⊒{γ} ζ.
Proof.
  rewrite AtomicSWriter_eq AtomicCASerX_eq.
  iIntros (MAX) "$ (_ & EW & _) $". iExists tx. by iFrame "EW".
Qed.

Lemma AtomicPtsToX_CAS_update l γ t1 ζ1 t2 ζ2 V1 V2 m:
  @{V1} AtomicPtsToX l γ t1 ζ1 m -∗ @{V2} l casX⊒{γ,t2,1} ζ2 ==∗
  ∃ t, ⌜ max_time t ζ1 ⌝ ∗ @{V1} AtomicPtsToX l γ t ζ1 m ∗ @{V1} l casX⊒{γ,t,1} ζ1.
Proof.
  iIntros "P C".
  iDestruct (AtomicCASerX_AtomicPtsToX_is_not_concurrent with "C P") as %NC.
  iDestruct (AtomicPtsToX_AtomicCASerX_latest with "P C") as %[-> ?].
  iAssert (@{V1} l sn⊒{γ} ζ1)%I with "[P]" as "#SS".
  { rewrite AtomicPtsToX_AtomicSeen. iFrame. }
  rewrite AtomicCASerX_eq AtomicPtsToX_eq.
  iDestruct "C" as "(_ & SW & _)".
  iDestruct "P" as (C Va rsa rns ws) "(F & (SL & ATLs) & HI & ATs & SA & AW)".
  iDestruct "F" as %(?&?&IS&?).
  destruct (gmap_top_nonempty (flip (⊑)) ζ1) as (t & vV' & Eq').
  { move => EqE. move : IS => [?]. rewrite EqE. by apply lookup_empty_Some. }
  apply gmap_top_equiv in Eq' as [Eq' MAX]; [|apply _..].
  iMod (at_auth_exclusive_write_update _ _ _ _ t with "[$SA] [$SW]")
    as "[SA SW]".
  iIntros "!>". iExists t. iSplit.
  { iPureIntro. split; [by eexists|]. intros t' IS'. by apply MAX, elem_of_dom. }
  iSplitR "SW".
  - iExists _,_,_,_,_. iFrame. iSplit; [by iPureIntro|by destruct m].
  - by iFrame "SS SW".
Qed.

Lemma AtomicPtsToX_CAS_to_SW l γ t ζ t' ζ' V0:
  @{V0} l casX↦{γ,t} ζ -∗ l casX⊒{γ,t',1} ζ' -∗ l sy⊒{γ} ζ
  ==∗ ∃ t', ⌜ max_time t' ζ ⌝ ∗ @{V0} l swX↦{γ,t'} ζ ∗ l sw⊒{γ} ζ.
Proof.
  iIntros "P C SY".
  iDestruct (AtomicPtsToX_AtomicCASerX_latest_1 with "P C") as %[-> ?].
  rewrite AtomicSWriter_eq AtomicCASerX_eq AtomicPtsToX_eq.
  iDestruct "P" as (C Va rsa rns ws) "(F & (SL & ATLs) & HI & ATs & SA & AW)".
  iDestruct "F" as %(?&?&IS&?). iDestruct "C" as "(SN & SW & _)".
  destruct (gmap_top_nonempty (flip (⊑)) ζ) as (tx' & vV' & Eq').
  { move => EqE. move : IS => [?]. rewrite EqE. by apply lookup_empty_Some. }
  apply gmap_top_equiv in Eq' as [Eq' MAX]; [|apply _..].
  iMod (at_auth_exclusive_write_update _ _ _ _ tx' with "[$SA] SW")
    as "[SA SW]".
  iIntros "!>". iExists tx'.
  have MAX' : max_time tx' ζ.
  { split. + by eexists. + intros t' IS'. by apply MAX, elem_of_dom. }
  iSplit; [done|]. iSplitR "SY SW AW".
  - iExists _,_,_,_,_. iFrame. by iPureIntro.
  - iFrame "SY AW". iExists tx'. by iFrame "SW".
Qed.

Lemma AtomicPtsTo_CAS_to_SW l γ ζ ζ' V0:
  @{V0} l cas↦{γ} ζ -∗ l cas⊒{γ,1} ζ' -∗ l sy⊒{γ} ζ
  ==∗ @{V0} l sw↦{γ} ζ ∗ l sw⊒{γ} ζ.
Proof.
  rewrite AtomicPtsTo_eq AtomicCASer_eq.
  iIntros "[%t P] [%t2 C] SY".
  iMod (AtomicPtsToX_CAS_to_SW with "P C SY") as (t' MAX) "[P $]".
  by iExists _.
Qed.

Lemma AtomicPtsTo_CAS_to_SW_1 l γ ζ ζ':
  l cas↦{γ} ζ -∗ l cas⊒{γ,1} ζ' ==∗ l sw↦{γ} ζ ∗ l sw⊒{γ} ζ.
Proof.
  iIntros "P C".
  iDestruct (AtomicPtsTo_AtomicSync with "P") as "#SY".
  iDestruct (view_at_intro with "P") as (V0) "[In0 P]".
  iMod (AtomicPtsTo_CAS_to_SW with "P C SY") as "[P $]".
  by iDestruct (view_at_elim with "In0 P") as "$".
Qed.

(** * Conversion from single-writer mode to concurrent mode *)
Lemma AtomicPtsToX_SW_to_CON l γ t ζ ζ' V0 V1 :
  @{V0} l swX↦{γ,t} ζ -∗ @{V1} l sw⊒{γ} ζ' -∗ @{V0} l atX↦{γ,t} ζ ∗ @{V1} l sy⊒{γ} ζ.
Proof.
  iIntros "P W".
  rewrite AtomicSWriter_eq AtomicPtsToX_eq.
  iDestruct "P" as (C Va rsa rns ws) "(F & SL & HI & ATs & SA & _)".
  iDestruct "W" as "[[W' W] W2]". iDestruct "W2" as (tx') "[W2 _]".
  iDestruct (at_auth_all_writer_exact with "[$SA] [$W]") as %<-.
  iDestruct (at_full_auth_exclusive_write_agree with "[$SA] [$W2]") as %<-.
  iFrame "W'". iExists C, Va, rsa, rns, ws. iFrame.
  rewrite !view_at_objective_iff. by iFrame.
Qed.
Lemma AtomicPtsToX_SW_to_CON_1 l γ t ζ ζ' V0 :
  @{V0} l swX↦{γ,t} ζ -∗ l sw⊒{γ} ζ' -∗ @{V0} l atX↦{γ,t} ζ ∗ l sy⊒{γ} ζ.
Proof.
  iIntros "P W".
  iDestruct (view_at_intro with "W") as (V1) "[sV1 W]".
  iDestruct (AtomicPtsToX_SW_to_CON with "P W") as "[$ W]".
  iApply (view_at_elim with "sV1 W").
Qed.
Lemma AtomicPtsToX_SW_to_CON_2 l γ t ζ ζ' :
  l swX↦{γ,t} ζ -∗ l sw⊒{γ} ζ' -∗ l atX↦{γ,t} ζ ∗ l sy⊒{γ} ζ.
Proof.
  iIntros "P W".
  iDestruct (view_at_intro with "P") as (V0) "[sV P]".
  iDestruct (AtomicPtsToX_SW_to_CON_1 with "P W") as "[P $]".
  iApply (view_at_elim with "sV P").
Qed.

Lemma AtomicPtsTo_SW_to_CON l γ ζ ζ' V0 V1 :
  @{V0} l sw↦{γ} ζ -∗ @{V1} l sw⊒{γ} ζ' -∗ @{V0} l at↦{γ} ζ ∗ @{V1} l sy⊒{γ} ζ.
Proof.
  rewrite AtomicPtsTo_eq.
  iIntros "[%t P] W". iDestruct (AtomicPtsToX_SW_to_CON with "P W") as "[P $]".
  by iExists _.
Qed.

Lemma AtomicPtsTo_SW_to_CON_1 l γ ζ ζ' :
  l sw↦{γ} ζ -∗ l sw⊒{γ} ζ' -∗ l at↦{γ} ζ ∗ l sy⊒{γ} ζ.
Proof.
  iIntros "P W". iDestruct (view_at_intro with "P") as (V0) "[sV P]".
  iDestruct (view_at_intro with "W") as (V1) "[sV1 W]".
  iDestruct (AtomicPtsTo_SW_to_CON with "P W") as "[P W]".
  iDestruct (view_at_elim with "sV1 W") as "$".
  iApply (view_at_elim with "sV P").
Qed.

Lemma AtomicPtsTo_CON_to_SW l γ ζ :
  l at↦{γ} ζ ==∗ l sw↦{γ} ζ ∗ l sw⊒{γ} ζ.
Proof.
  rewrite AtomicPtsTo_CON_CAS_1. apply bi.wand_elim_l', AtomicPtsTo_CAS_to_SW_1.
Qed.

(* From and to non-atomic pointsto *)
Lemma into_own_loc_na l q rsa ws rsn Va t m v :
  let C := {[t := m]} in
  good_hist C → memval_val_rel m.(mval) v →
  seen_time l t ∗
  ⊒(default ∅ m.(mrel)) ∗ AtRLocal l rsa ∗ AtWLocal l ws ∗ NaLocal l rsn Va ∗
  ⎡ hist l q C ∗ atread l q rsa ∗ atwrite l q ws ∗ naread l q rsn ⎤ -∗
  l ↦{q} v.
Proof.
  intros C GH VAL.
  iIntros "(? & sVm & ? & ? & NAL & HC & AR & AW & NA)".
  iExists t, m. iFrame (VAL) "sVm".
  iExists rsa, rsn, ws. iFrame (GH) "∗". iSplitR "NAL"; last by eauto.
  iStopProof. constructor => V. iPureIntro. intros ?.
  exists t, m. split; last split; [by rewrite lookup_singleton|by inversion VAL|done].
Qed.

Lemma from_own_loc_na l q v Vinit :
  ⊒Vinit -∗ l ↦{q} v -∗
  ∃ t m rsa ws rsn Va,
  let C := {[t := m]} in
  ⌜good_hist C ∧ memval_val_rel m.(mval) v ∧ Vinit ⊑ Va⌝ ∗
  SyncLocal l (toAbsHist C Va) ∗ AtRLocal l rsa ∗ AtWLocal l ws ∗ NaLocal l rsn Va ∗
  ⎡ hist l q C ∗ atread l q rsa ∗ atwrite l q ws ∗ naread l q rsn ⎤.
Proof.
  iIntros "#sVin". iDestruct 1 as (t m) "(Own & %VAL & #sVm)".
  iDestruct "Own" as (rsa rsn ws GH) "(AL & ARL & AWL & [%Va NAL] & HC & AR & AW & NA)".
  iExists t, m, rsa, ws, rsn, (Vinit ⊔ Va). iFrame.
  iSplit. { iPureIntro. do 2 (split; [done|]). solve_lat. }
  iDestruct (NaLocal_seen with "NAL") as "#sVna". iSplit.
  - rewrite (toAbsHist_singleton _ _ _ _ VAL).
    iApply SeenLocal_SyncLocal_singleton.
    { rewrite -!monPred_in_view_op. iFrame "#". }
    (* TODO lemma *)
    iClear "# NAL". iStopProof. constructor => V. rewrite SeenLocal_unfold_singleton.
    iPureIntro. by intros (t1 & m1 & [<- ?]%lookup_singleton_Some & ? & SL).
  - (* TODO lemma *)
    iClear "sVm sVna AL". iStopProof. constructor => V.
    rewrite monPred_at_sep monPred_at_intuitionistically. iPureIntro.
    intros (? & NA & ?). split; [|solve_lat]. move : NA. clear.
    rewrite /na_local view_lookup_nr_join. solve_lat.
Qed.

Lemma SyncLocal_lookup l ζ t v V :
  ζ !! t = Some (v, V) →
  (SyncLocal l ζ : vProp) ⊢ seen_time l t ∗ ⊒V.
Proof.
  iIntros (Eq) "SL".
  iDestruct ("SL" $! t V with "[%]") as "SV". { by rewrite Eq. }
  by iApply seen_view_seen_time.
Qed.

(** * Conversion from AtomicPtsTo to non-atomic points-to *)
Lemma AtomicPtsToX_to_na l γ t0 ζ md E :
  ↑histN ⊆ E →
  ⎡ hist_inv ⎤ -∗ AtomicPtsToX l γ t0 ζ md ={E}=∗
  ∃ t v V, l ↦ v ∗ ⊒V ∗
      ⌜ ζ !! t = Some (v,V) ∧ (t0 ≤ t)%positive ∧ no_earlier_time ζ t ⌝.
Proof.
  iIntros (SUB) "#Inv P". rewrite AtomicPtsToX_eq.
  iDestruct "P" as (C Va rsa rns ws)
                    "(F & (SL & ARL & AWL & NAL) & HC & (AR & AW & NA) & SA)".
  iDestruct "F" as %(GH & EQ & IS & ND).
  destruct (gmap_top_nonempty (flip (⊑)) ζ) as [t [[v V] Eqt]].
  { move => Eq. rewrite Eq in IS. by destruct IS. }
  have EQm: toAbsHist C Va !! t = Some (v, V).
  { rewrite -EQ. by apply (gmap_top_lookup _ _ _ _ Eqt). }
  have TOP: ∀ k', k' ∈ dom (toAbsHist C Va) → k' ⊑ t
        by rewrite -EQ; apply (gmap_top_top _ _ _ _ Eqt).
  destruct (toAbsHist_lookup_message _ _ _ _ _ EQm) as [m [EqCm [Eqvm EqVm]]].
  rewrite -{1}(insert_id _ _ _ EqCm).

  iInv histN as (σ) ">[Hσ ctx]" "HClose".
  iMod (hist_ctx_hist_drop_singleton with "ctx HC") as "[ctx HC]";
    [|by inversion Eqvm|].
  { move => t' [m' Eqt']. apply TOP, elem_of_dom.
    specialize (ND _ _ Eqt').
    destruct m'.(mval) eqn:Eqv'; [|done|]; eexists;
      (apply toAbsHist_lookup_state_inv; [|done]); rewrite Eqv'; by constructor. }
  iDestruct (hist_ctx_hist_good with "ctx HC") as %GH'.
  iMod ("HClose" with "[ctx Hσ]") as "_". { iExists _. by iFrame. }
  iModIntro. iExists t, v, V. iSplit; last iSplit; last first.
  { iIntros "!%". rewrite EQ EQm. split; [done|].
    split. { apply TOP. rewrite -EQ. by apply elem_of_dom. }
    intros t' IS'. apply TOP. by apply elem_of_dom. }
  { rewrite -EQ in EQm.
    iDestruct (SyncLocal_lookup _ _ _ _ _ EQm with "SL") as "[?$]". }
  iApply into_own_loc_na; eauto. iFrame.
  iClear "SA #".
  rewrite EQ. iDestruct (SyncLocal_lookup with "SL") as "[$ sV]"; first done.
  rewrite EqVm. iApply (monPred_in_mono with "sV"). simpl; solve_lat.
Qed.

Lemma AtomicPtsTo_to_na l γ ζ md E :
  ↑histN ⊆ E →
  ⎡ hist_inv ⎤ -∗ AtomicPtsTo l γ ζ md ={E}=∗
  ∃ t v, l ↦ v ∧ ⌜ fst <$> ζ !! t = Some v ∧ no_earlier_time ζ t ⌝.
Proof.
  rewrite AtomicPtsTo_eq. iIntros (SUB) "Inv [%t P]".
  iMod (AtomicPtsToX_to_na with "Inv P") as (t' v V) "(P & sV & (% &%&%))"; [done|].
  iIntros "!>". iExists _, _. iFrame. iPureIntro.
  split; [|done]. rewrite -lookup_fmap. apply lookup_fmap_Some. by exists (v,V).
Qed.

Lemma AtomicPtsToX_from_na_cofinite_view l v (G : gset gname) Vinit :
  ⊒Vinit -∗ l ↦ v ==∗
  ∃ γ t V, ⌜γ ∉ G ∧ Vinit ⊑ V⌝ ∗ ⊒V ∗
           let ζ := {[t := (v,V)]} in @{V} l sw⊒{γ} ζ ∗ @{V} l swX↦{γ,t} ζ.
Proof.
  iIntros "P NA". iCombine "P NA" as "PP".
  iDestruct (view_at_intro with "PP") as (V') "[InV' [%LeV' NA]]".
  iAssert (@{V'} (⊒V' ∗ l ↦ v))%I with "[NA]" as "NA".
  { iSplit; [by iPureIntro|by iFrame]. }
  rewrite (bi.wand_elim_l' _ _ _ (from_own_loc_na l 1 v V')).
  iDestruct "NA" as (t m rsa ws rsn Va)
                "(F & #SL & ARL & AWL & #NAL & HC & AR & AW & NA)".
  iDestruct "F" as %(GH & VAL & LeVa).
  set V := default ∅ m.(mrel).
  set ζ := toAbsHist {[t := m]} Va.
  have Eqζ: ζ = {[t := (v, V ⊔ Va)]} by apply toAbsHist_singleton.
  have ?: ζ !! t = Some (v, V ⊔ Va).
  { by rewrite Eqζ lookup_insert. }
  iMod (at_full_auth_alloc_cofinite ζ t Va G) as (γ) "(% & SA & SW & SE & #SN)".
  iDestruct (at_writer_fork_at_reader with "SW") as "#SR".
  iIntros "!>".
  iExists γ, t, (V ⊔ Va). iSplitR. { iPureIntro. split; [done|solve_lat]. }
  rewrite -Eqζ.
  iAssert (@{V'} ⊒(V ⊔ Va))%I with "[]" as "#sV'".
  { rewrite (SyncLocal_lookup l ζ t v); [|done]. by iDestruct "SL" as "[? $]". }
  iDestruct (view_at_elim with "InV' sV'") as "$".
  rewrite AtomicSWriter_eq AtomicPtsToX_eq. iSplitL "SW SE".
  - iFrame. iSplitR.
    + rewrite AtomicSync_eq. iFrame "SL SR". iExists Va. iFrame "#".
      iSplit; last first. { iPureIntro. solve_lat. }
      iPureIntro. rewrite Eqζ. split.
      * apply map_non_empty_singleton.
      * exists {[t := m]}. split; [done|].
        move => ?? /lookup_singleton_Some [? <-]. by inversion VAL.
    + iExists t. iFrame. iPureIntro. rewrite Eqζ. split.
      * rewrite lookup_insert. by eexists.
      * move => t1 [VV1 /lookup_singleton_Some [<-//]].
  - iExists {[t := m]}, Va, rsa, rsn, ws. iFrame "SA". iFrame "#∗".
    iPureIntro. split; [|done]. do 2 (split; [done|]). rewrite Eqζ. split.
    + rewrite lookup_insert. by eexists.
    + move => ?? /lookup_singleton_Some [? <-]. by inversion VAL.
Qed.

Lemma AtomicPtsToX_from_na_cofinite_rel_view l v (G : gset gname) P :
  P -∗ l ↦ v ==∗
  ∃ γ t V, ⌜γ ∉ G⌝ ∗ ⊒V ∗ @{V} P ∗
           let ζ := {[t := (v,V)]} in @{V} l sw⊒{γ} ζ ∗ @{V} l swX↦{γ,t} ζ.
Proof.
  iIntros "P NA".
  iDestruct (view_at_intro with "P") as (Vinit) "[sVi P]".
  iMod (AtomicPtsToX_from_na_cofinite_view with "sVi NA")
    as (γ t V [FR LeV]) "(sV & Pts)".
  iIntros "!>". iExists γ, t, V. by iFrame (FR) "sV P Pts".
Qed.
Lemma AtomicPtsToX_from_na_cofinite_rel l v (G : gset gname) P :
  P -∗ l ↦ v ==∗ ∃ γ t V, ⌜γ ∉ G⌝ ∗ ⊒V ∗ @{V} P ∗
                  let ζ := {[t := (v,V)]} in l sw⊒{γ} ζ ∗ l swX↦{γ,t} ζ.
Proof.
  iIntros "P NA".
  iMod (AtomicPtsToX_from_na_cofinite_rel_view with "P NA")
    as (γ t V FR) "(#sV & P & W & Pts)".
  iIntros "!>". iExists γ, t, V. iFrame (FR) "sV P".
  iDestruct (view_at_elim with "sV W") as "$".
  by iDestruct (view_at_elim with "sV Pts") as "$".
Qed.
Lemma AtomicPtsToX_from_na_cofinite l v (G : gset gname) :
  l ↦ v ==∗ ∃ γ t V, ⌜γ ∉ G⌝ ∗ ⊒V ∗
            let ζ := {[t := (v,V)]} in l sw⊒{γ} ζ ∗ l swX↦{γ,t} ζ.
Proof.
  iIntros "NA".
  iMod (AtomicPtsToX_from_na_cofinite_rel _ _ _ True%I with "[//] NA")
    as (γ t V) "(? & ? & _ & ?)".
  iIntros "!>". iExists γ, t, V. by iFrame.
Qed.
Lemma AtomicPtsToX_from_na_rel_view l v P :
  P -∗ l ↦ v ==∗ ∃ γ t V, ⊒V ∗ @{V} P ∗
            let ζ := {[t := (v,V)]} in @{V} l sw⊒{γ} ζ ∗ @{V} l swX↦{γ,t} ζ.
Proof.
  iIntros "P N".
  iMod (AtomicPtsToX_from_na_cofinite_rel_view l v ∅ with "P N")
    as (γ t V) "(_ & ? & ? & ?)".
  iIntros "!>". iExists γ, t, V. by iFrame.
Qed.
Lemma AtomicPtsToX_from_na_rel l v P :
  P -∗ l ↦ v ==∗ ∃ γ t V, ⊒V ∗ @{V} P ∗
            let ζ := {[t := (v,V)]} in l sw⊒{γ} ζ ∗ l swX↦{γ,t} ζ.
Proof.
  iIntros "P N".
  iMod (AtomicPtsToX_from_na_cofinite_rel l v ∅ with "P N")
    as (γ t V) "(_ & ? & ? & ?)".
  iIntros "!>". iExists γ, t, V. by iFrame.
Qed.
Lemma AtomicPtsToX_from_na l v :
  l ↦ v ==∗ ∃ γ t V, ⊒V ∗
            let ζ := {[t := (v,V)]} in l sw⊒{γ} ζ ∗ l swX↦{γ,t} ζ.
Proof.
  rewrite (AtomicPtsToX_from_na_cofinite l v ∅). apply bupd_mono.
  iDestruct 1 as (γ t V) "[_ E]". eauto.
Qed.

Lemma AtomicPtsTo_from_na_cofinite_rel l v (G : gset gname) P :
  P -∗ l ↦ v ==∗ ∃ γ t V, ⌜γ ∉ G⌝ ∗ ⊒V ∗ @{V} P ∗
                  let ζ := {[t := (v,V)]} in l sw⊒{γ} ζ ∗ l sw↦{γ} ζ.
Proof.
  iIntros "P NA". rewrite AtomicPtsTo_eq.
  iMod (AtomicPtsToX_from_na_cofinite_rel with "P NA")
    as (γ t V FR) "(sV & P & W & Pt)".
  iIntros "!>". iExists γ, t, V. iFrame (FR) "∗". by iExists _.
Qed.
Lemma AtomicPtsTo_from_na_cofinite l v (G : gset gname) :
  l ↦ v ==∗ ∃ γ t V, ⌜γ ∉ G⌝ ∗ ⊒V ∗
            let ζ := {[t := (v,V)]} in l sw⊒{γ} ζ ∗ l sw↦{γ} ζ.
Proof.
  iIntros "NA".
  iMod (AtomicPtsTo_from_na_cofinite_rel _ _ _ True%I with "[//] NA")
    as (γ t V) "(? & ? & _ & ?)".
  iIntros "!>". iExists γ, t, V. by iFrame.
Qed.
Lemma AtomicPtsTo_from_na_rel l v P :
  P -∗ l ↦ v ==∗ ∃ γ t V, ⊒V ∗ @{V} P ∗
            let ζ := {[t := (v,V)]} in l sw⊒{γ} ζ ∗ l sw↦{γ} ζ.
Proof.
  iIntros "P N".
  iMod (AtomicPtsTo_from_na_cofinite_rel l v ∅ with "P N")
    as (γ t V) "(_ & ? & ? & ?)".
  iIntros "!>". iExists γ, t, V. by iFrame.
Qed.
Lemma AtomicPtsTo_from_na l v :
  l ↦ v ==∗ ∃ γ t V, ⊒V ∗
            let ζ := {[t := (v,V)]} in l sw⊒{γ} ζ ∗ l sw↦{γ} ζ.
Proof.
  rewrite (AtomicPtsTo_from_na_cofinite l v ∅). apply bupd_mono.
  iDestruct 1 as (γ t V) "[_ E]". eauto.
Qed.

Lemma AtomicPtsTo_CON_from_na_cofinite_rel l v (G : gset gname) P :
  P -∗ l ↦ v ==∗ ∃ γ t V, ⌜γ ∉ G⌝ ∗ ⊒V ∗ @{V} P ∗
                          let ζ := {[t := (v,V)]} in l sn⊒{γ} ζ ∗ l at↦{γ} ζ.
Proof.
  iIntros "P NA".
  iMod (AtomicPtsTo_from_na_cofinite_rel _ _ G with "P NA")
    as (γ t V NIn) "(sV & P & SWS & SW)".
  iExists γ, t, V.
  iDestruct (AtomicPtsTo_SW_to_CON_1 with "SW SWS") as "[SY ?]".
  rewrite AtomicSync_AtomicSeen. by iFrame.
Qed.

Lemma AtomicPtsTo_CON_from_na_cofinite l v (G : gset gname) :
  l ↦ v ==∗ ∃ γ t V, ⌜γ ∉ G⌝ ∗ ⊒V ∗
            let ζ := {[t := (v,V)]} in l sn⊒{γ} ζ ∗ l at↦{γ} ζ.
Proof.
  iIntros "NA".
  iMod (AtomicPtsTo_CON_from_na_cofinite_rel _ _ G True%I with "[//] NA")
    as (γ t V NIn) "(sV & _ & SW)".
  iExists γ, t, V. by iFrame.
Qed.

Lemma AtomicPtsTo_CON_from_na_rel l v P :
  P -∗ l ↦ v ==∗ ∃ γ t V, ⊒V ∗ @{V} P ∗
  let ζ := {[t := (v,V)]} in l sn⊒{γ} ζ ∗ l at↦{γ} ζ.
Proof.
  iIntros "P NA".
  iMod (AtomicPtsTo_CON_from_na_cofinite_rel _ _ ∅ with "P NA")
    as (γ t V NIn) "(sV & P & SWS & SW)".
  iExists γ, t, V. by iFrame.
Qed.

Lemma AtomicPtsTo_CON_from_na l v :
  l ↦ v ==∗ ∃ γ t V, ⊒V ∗
  let ζ := {[t := (v,V)]} in l sn⊒{γ} ζ ∗ l at↦{γ} ζ.
Proof.
  rewrite (AtomicPtsTo_CON_from_na_cofinite l v ∅). apply bupd_mono.
  iDestruct 1 as (γ t V) "[_ E]". eauto.
Qed.
End props.

#[global] Typeclasses Opaque SeenLocal SyncLocal.
