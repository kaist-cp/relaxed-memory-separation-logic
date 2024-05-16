From stdpp Require Export gmap tactics.
From orc11 Require Export view memory mem_order.

Require Import stdpp.options.

Section ThreadView.
  Context `{!LocFacts loc} `{CVAL: Countable VAL}.
  Notation view := (@view loc _).
  Implicit Types (V: view).

  (* TODO: clean up these instances *)
  Global Instance all_gmap_sqsubseteq_decision (M: gmap loc view) (V: option view) :
    Decision (∀ l, M !! l ⊑ V).
  Proof.
    assert (IFF : (∀ l, M !! l ⊑ V) ↔ (Forall (λ lV', Some lV'.2 ⊑ V) (map_to_list M))).
    { rewrite list.Forall_forall. split.
      - intros ? [l V'] Eq%elem_of_map_to_list. by rewrite /= -Eq.
      - intros HM l. destruct (M!!l) eqn:Eq; [|done].
        apply elem_of_map_to_list in Eq. eapply (HM (_,_)). eauto. }
    destruct (decide (Forall (λ lV', Some lV'.2 ⊑ V) (map_to_list M)));
      [left|right]; by rewrite IFF.
   Qed.

  Global Instance all_gmap_sqsubseteq_decision' (M: gmap loc view) V :
    Decision (∀ l V', M !! l = Some V' → V ⊑ V').
  Proof.
    assert (IFF : (∀ (l : loc) (V' : view), M !! l = Some V' → V ⊑ V') ↔
                  (Forall (λ lV', V ⊑ lV'.2) (map_to_list M))).
    { rewrite list.Forall_forall. split.
      - intros ? [l V'] Eq%elem_of_map_to_list. eauto.
      - intros HM l V' ?. by eapply (HM (_, _)), elem_of_map_to_list. }
    destruct (decide (Forall (λ lV' : loc * view, V ⊑ lV'.2) (map_to_list M)));
      [left|right]; by rewrite IFF.
  Qed.

  Record threadView : Type :=
    mkTView {
        rel : gmap loc view;  (* The latest release write for each location. *)
        frel: view;           (* The latest SC or REL fence. *)
        cur : view;
        acq : view;

        rel_dom_dec :
          bool_decide (dom rel ⊆ dom cur);
        rel_cur_dec : bool_decide (∀ l, rel !! l ⊑ Some cur);
        frel_cur_dec : bool_decide (frel ⊑ cur);
        cur_acq_dec : bool_decide (cur ⊑ acq);
      }.

  Lemma rel_dom 𝓥 : dom 𝓥.(rel) ⊆ dom 𝓥.(cur).
  Proof. eapply bool_decide_unpack, rel_dom_dec. Qed.
  Lemma rel_cur 𝓥 l : (𝓥.(rel) !! l) ⊑ Some 𝓥.(cur).
  Proof. revert l. eapply bool_decide_unpack, rel_cur_dec. Qed.
  Lemma rel_cur' 𝓥 l : default ∅ (𝓥.(rel) !! l) ⊑ 𝓥.(cur).
  Proof. pose proof (rel_cur 𝓥 l). by destruct lookup. Qed.
  Lemma frel_cur 𝓥 : 𝓥.(frel) ⊑ 𝓥.(cur).
  Proof. eapply bool_decide_unpack, frel_cur_dec. Qed.
  Lemma cur_acq 𝓥 : 𝓥.(cur) ⊑ 𝓥.(acq).
  Proof. eapply bool_decide_unpack, cur_acq_dec. Qed.

  Lemma threadView_eq 𝓥1 𝓥2 :
    𝓥1.(rel) = 𝓥2.(rel) → 𝓥1.(frel) = 𝓥2.(frel) → 𝓥1.(cur) = 𝓥2.(cur) → 𝓥1.(acq) = 𝓥2.(acq) →
    𝓥1 = 𝓥2.
  Proof. destruct 𝓥1, 𝓥2=>/= ????. subst. f_equal; apply proof_irrel. Qed.

  Program Definition init_tview := mkTView ∅ ∅ ∅ ∅ _ _ _ _.
  Solve Obligations with eapply bool_decide_pack; set_solver.

  Global Instance threadViewInhabited : Inhabited threadView.
  Proof. constructor. exact init_tview. Qed.

  Implicit Type (𝓥: threadView (* U+1D4E5 *)).

  Record tview_le 𝓥1 𝓥2 :=
    mkTViewSqSubsetEq {
      tview_sqsubseteq_rel  : 𝓥1.(rel)  ⊑ 𝓥2.(rel);
      tview_sqsubseteq_frel : 𝓥1.(frel) ⊑ 𝓥2.(frel);
      tview_sqsubseteq_cur  : 𝓥1.(cur)  ⊑ 𝓥2.(cur);
      tview_sqsubseteq_acq  : 𝓥1.(acq)  ⊑ 𝓥2.(acq);
    }.

  Program Definition tview_join :=
    λ 𝓥1 𝓥2, mkTView ((𝓥1.(rel) : gmap_Lat loc view_Lat) ⊔ 𝓥2.(rel))
                      (𝓥1.(frel) ⊔ 𝓥2.(frel))
                      (𝓥1.(cur) ⊔ 𝓥2.(cur)) (𝓥1.(acq) ⊔ 𝓥2.(acq)) _ _ _ _.
  Next Obligation.
    intros. apply bool_decide_pack. rewrite !gmap_join_dom_union=>l.
    rewrite !elem_of_union=>-[?|?]; [left|right]; by apply rel_dom.
  Qed.
  Next Obligation.
    intros. apply bool_decide_pack=>l. by rewrite lookup_join !rel_cur.
  Qed.
  Next Obligation. intros. apply bool_decide_pack. by rewrite !frel_cur. Qed.
  Next Obligation. intros. apply bool_decide_pack. by rewrite !cur_acq. Qed.

  Program Definition tview_meet :=
    λ 𝓥1 𝓥2, mkTView ((𝓥1.(rel) : gmap_Lat loc view_Lat) ⊓ 𝓥2.(rel))
                      (𝓥1.(frel) ⊓ 𝓥2.(frel))
                      (𝓥1.(cur) ⊓ 𝓥2.(cur)) (𝓥1.(acq) ⊓ 𝓥2.(acq)) _ _ _ _.
  Next Obligation.
    intros. apply bool_decide_pack. rewrite !gmap_meet_dom_intersection=>l.
    rewrite !elem_of_intersection=>-[? ?]; split; by apply rel_dom.
  Qed.
  Next Obligation.
    intros. apply bool_decide_pack=>l. by rewrite lookup_meet !rel_cur.
  Qed.
  Next Obligation. intros. apply bool_decide_pack. by rewrite !frel_cur. Qed.
  Next Obligation. intros. apply bool_decide_pack. by rewrite !cur_acq. Qed.

  Program Canonical Structure tview_Lat :=
    Make_Lat threadView (=) tview_le tview_join tview_meet
             _ _ _ _ _ _ _ _ _ _ _ _ _.
  Next Obligation.
    split; [by split|] => ??? [????] [????]. constructor; by etrans.
  Qed.
  Next Obligation.
    intros [][][][]. apply threadView_eq; by apply: (anti_symm (⊑)).
  Qed.
  Next Obligation.
    move => ??. split; simpl; try solve_lat.
    move => ?. rewrite lookup_join. by apply lat_join_sqsubseteq_l.
  Qed.
  Next Obligation.
    move => ??. split; simpl; try solve_lat.
    move => ?. rewrite lookup_join. by apply lat_join_sqsubseteq_r.
  Qed.
  Next Obligation.
    intros ??? [][]. split; simpl; try solve_lat.
    move => ?. rewrite lookup_join. apply lat_join_lub; auto.
  Qed.
  Next Obligation.
    move => ??. split; simpl; try solve_lat.
    move => ?. rewrite lookup_meet. by apply lat_meet_sqsubseteq_l.
  Qed.
  Next Obligation.
    move => ??. split; simpl; try solve_lat.
    move => ?. rewrite lookup_meet. by apply lat_meet_sqsubseteq_r.
  Qed.
  Next Obligation.
    intros ??? [][]. split; simpl; try solve_lat.
    move => ?. rewrite lookup_meet. apply lat_meet_glb; auto.
  Qed.

  Global Instance rel_mono : Proper ((⊑) ==> (⊑)) rel.
  Proof. solve_proper. Qed.
  Global Instance acq_mono : Proper ((⊑) ==> (⊑)) acq.
  Proof. solve_proper. Qed.
  Global Instance frel_mono : Proper ((⊑) ==> (⊑)) frel.
  Proof. solve_proper. Qed.
  Global Instance cur_mono : Proper ((⊑) ==> (⊑)) cur.
  Proof. solve_proper. Qed.

  Global Instance rel_mono_flip : Proper (flip (⊑) ==> flip (⊑)) rel.
  Proof. solve_proper. Qed.
  Global Instance acq_mono_flip : Proper (flip (⊑) ==> flip (⊑)) acq.
  Proof. solve_proper. Qed.
  Global Instance frel_mono_flip : Proper (flip (⊑) ==> flip (⊑)) frel.
  Proof. solve_proper. Qed.
  Global Instance cur_mono_flip : Proper (flip (⊑) ==> flip (⊑)) cur.
  Proof. solve_proper. Qed.

  Global Instance tview_Lat_bot : LatBottom init_tview.
  Proof. done. Qed.

  Notation memory := (memory loc VAL).
  Notation message := (message loc VAL).
  Implicit Type (M: memory).

  Record closed_tview' 𝓥 M :=
    { closed_tview_rel: ∀ l, (𝓥.(rel) !! l) ∈ M;
      closed_tview_frel: 𝓥.(frel) ∈ M;
      closed_tview_cur: 𝓥.(cur) ∈ M;
      closed_tview_acq: 𝓥.(acq) ∈ M; }.

  Global Instance closed_tview : ElemOf threadView memory := closed_tview'.

  Global Instance closed_tview_downclosed :
    Proper ((@sqsubseteq threadView _) ==> (@eq memory) ==> flip impl) (∈).
  Proof.
    move => [????????] [????????] [/= SE1 SE2 SE3 SE4] ?? -> [/=????].
    constructor => /=.
    - move => l. by rewrite (SE1 l).
    - by rewrite SE2.
    - by rewrite SE3.
    - by rewrite SE4.
  Qed.

  Lemma closed_tview_acq_inv 𝓥 M (HC: 𝓥.(acq) ∈ M):
    𝓥 ∈ M.
  Proof.
    have HCur: 𝓥.(cur) ∈ M by rewrite cur_acq.
    constructor; [|by rewrite frel_cur|done..].
    by move => l; rewrite rel_cur.
  Qed.

  (* <rel,cur,acq> -{o,l,t,R}-> <cur',acq',rel> *)
  Program Definition read_tview 𝓥 o R V
    (cur' := if decide (AcqRel ⊑ o) then 𝓥.(cur) ⊔ V ⊔ R else 𝓥.(cur) ⊔ V)
    (acq' := if decide (Relaxed ⊑ o) then 𝓥.(acq) ⊔ V ⊔ R else 𝓥.(acq) ⊔ V)
    := (mkTView 𝓥.(rel) 𝓥.(frel) cur' acq' _ _ _ _).
  Next Obligation.
    intros. apply bool_decide_pack. etrans; [apply rel_dom|f_equiv; subst cur'].
    case_match; solve_lat.
  Qed.
  Next Obligation.
    intros. apply bool_decide_pack=>l. rewrite rel_cur /cur'. case_match; solve_lat.
  Qed.
  Next Obligation.
    intros. apply bool_decide_pack. rewrite frel_cur /cur'. case_match; solve_lat.
  Qed.
  Next Obligation.
    intros. apply bool_decide_pack. destruct o; rewrite /cur' /acq' /= cur_acq; solve_lat.
  Qed.

  Inductive read_helper 𝓥 (o: memOrder) l t tr (R: view) : threadView → Prop :=
    | ReadHelper
        (PLN: 𝓥.(cur) !!w l ⊑ Some t)
        (PLN2: R !!w l ⊑ Some t)
        (V : view := if decide (Relaxed ⊑ o)
                     then {[l := [{ t, ∅, ∅, {[tr]} }] ]}
                     else {[l :=  [{ t, ∅, {[tr]}, ∅ }] ]})
        (cur' := if decide (AcqRel ⊑ o) then 𝓥.(cur) ⊔ V ⊔ R else 𝓥.(cur) ⊔ V)
        (acq' := if decide (Relaxed ⊑ o) then 𝓥.(acq) ⊔ V ⊔ R else 𝓥.(acq) ⊔ V)
    : read_helper 𝓥 o l t tr R (read_tview 𝓥 o R V).

  (* <rel,cur,acq> -{o,l,t,Rr,Rw}-> <cur',acq',rel'> *)
  Section write.
    Context 𝓥 o l t
            (V : view := if decide (Relaxed ⊑ o)
                         then {[l := [{ t, {[t]}, ∅, ∅ }] ]}
                         else {[l :=  [{ t, ∅, ∅, ∅ }] ]})
            (Vra  := if decide (AcqRel ⊑ o) then 𝓥.(cur) ⊔ V else V)
            (V'   := default ∅ (𝓥.(rel) !! l) ⊔ Vra)
            (rel' := <[l := V']> (𝓥.(rel))).

    Program Definition write_tview :=
      mkTView rel' 𝓥.(frel) (𝓥.(cur) ⊔ V) (𝓥.(acq) ⊔ V) _ _ _ _.
    Next Obligation.
      intros. apply bool_decide_pack. pose proof (rel_dom 𝓥).
      rewrite /rel' dom_insert gmap_join_dom_union /V.
      case decide => ?; rewrite dom_singleton; set_solver.
    Qed.
    Next Obligation.
      intros. apply bool_decide_pack=>l'. destruct (decide (l = l')) as [<-|].
      - rewrite lookup_insert /V' rel_cur' /Vra. case_match; solve_lat.
      - rewrite lookup_insert_ne // rel_cur. solve_lat.
    Qed.
    Next Obligation. intros. apply bool_decide_pack. rewrite frel_cur. solve_lat. Qed.
    Next Obligation. intros. apply bool_decide_pack. by rewrite cur_acq. Qed.

    Definition write_Rw Rr :=
      if decide (Relaxed ⊑ o) then Some (V' ⊔ 𝓥.(frel) ⊔ Rr) else None.
  End write.
  Inductive write_helper 𝓥 o l t Rr : option view → threadView → Prop :=
    | WriteHelper
      (RLX: 𝓥.(cur) !!w l ⊏ Some t)
    : write_helper 𝓥 o l t Rr (write_Rw 𝓥 o l t Rr) (write_tview 𝓥 o l t).

  (* <𝓥,𝓢> -{ F_sc }-> <𝓥',𝓢'> *)
  Program Definition sc_fence_tview 𝓥 𝓢 :=
    let 𝓢' := 𝓥.(acq) ⊔ 𝓢 in
    mkTView 𝓥.(rel) 𝓢' 𝓢' 𝓢' _ _ _ _.
  Next Obligation.
    intros. apply bool_decide_pack. etrans; [apply rel_dom|]. f_equiv.
    rewrite cur_acq. solve_lat.
  Qed.
  Next Obligation.
    intros. apply bool_decide_pack=>l. rewrite rel_cur cur_acq. solve_lat.
  Qed.
  Next Obligation. intros. apply bool_decide_pack=>//. Qed.
  Next Obligation. intros. apply bool_decide_pack=>//. Qed.

  Inductive sc_fence_helper 𝓥 𝓢 : threadView → view → Prop :=
    | SCFenceHelper (𝓢' := 𝓥.(acq) ⊔ 𝓢 )
    : sc_fence_helper 𝓥 𝓢 (sc_fence_tview 𝓥 𝓢) 𝓢'.

  Inductive alloc_helper : list message → relation threadView :=
    | AllocListNone 𝓥: alloc_helper nil 𝓥 𝓥
    | AllocListSome 𝑚 𝑚s 𝓥1 𝓥2 𝓥3
        (NEXT: alloc_helper 𝑚s 𝓥1 𝓥2)
        (WRITE: write_helper 𝓥2 NonAtomic 𝑚.(mloc) 𝑚.(mto) ∅ None 𝓥3)
        : alloc_helper (𝑚 :: 𝑚s) 𝓥1 𝓥3.

  (** Lots of lemmas about thread-views *)
  Lemma read_helper_tview_sqsubseteq 𝓥 𝓥' o l t tr R
    (READ: read_helper 𝓥 o l t tr R 𝓥'):
    𝓥 ⊑ 𝓥'.
  Proof.
    inversion READ. subst V cur' acq'. constructor=>//=; clear; case_match; solve_lat.
  Qed.

  Lemma write_helper_tview_sqsubseteq 𝓥 𝓥' o l t Rr Rw
    (WRITE: write_helper 𝓥 o l t Rr Rw 𝓥'):
    𝓥 ⊑ 𝓥'.
  Proof.
    inversion_clear WRITE.
    constructor; (try solve_lat) => l'.
    case (decide (l' = l)) => [->|?]; [rewrite lookup_insert|by rewrite lookup_insert_ne].
    case: (rel 𝓥 !! l) => [?|]; solve_lat.
  Qed.

  Lemma read_helper_closed_tview 𝓥 𝓥' o l t tr R M
    (READ: read_helper 𝓥 o l t tr R 𝓥')
    (CLOSED: 𝓥 ∈ M) (CR: R ∈ M) (SOME: ∃ m, M !! (l, t) = Some m):
    𝓥' ∈ M.
  Proof.
    inversion READ. subst.
    have ?: {[l := [{ t,∅,∅,{[tr]} }] ]} ∈ M.
    { move => ??.
      rewrite /view_lookup_write fmap_Some.
      move => [[? ? ? ?] []] /lookup_singleton_Some [<- <-] /= ->. naive_solver. }
    have ?: {[l := [{ t,∅,{[tr]},∅ }] ]} ∈ M.
    { move => ??.
      rewrite /view_lookup_write fmap_Some.
      move => [[? ? ? ?] []] /lookup_singleton_Some [<- <-] /= ->. naive_solver. }
    have ?: V ∈ M by subst V; case_match.
    have ?: cur 𝓥 ⊔ V ∈ M by apply join_closed_view; [apply CLOSED|by auto].
    have ?: acq 𝓥 ⊔ V ∈ M by apply join_closed_view; [apply CLOSED|by auto].
    subst cur' acq'. constructor; simpl; [apply CLOSED|apply CLOSED|..].
    - case (decide (AcqRel ⊑ _)) => _ /=; [by apply join_closed_view|by auto].
    - subst V. case_match; [by apply join_closed_view|by auto].
  Qed.

  Lemma read_helper_view_relaxed_1 {l t tr 𝓥 𝓥' V}
    (RH : read_helper 𝓥 Relaxed l t tr V 𝓥'):
    V ⊑ 𝓥'.(acq).
  Proof. inversion RH; simpl in *. solve_lat. Qed.

  Lemma read_helper_view_relaxed {l t tr 𝓥 𝓥' oV1 oV2}
    (RH : read_helper 𝓥 Relaxed l t tr (default ∅ oV2) 𝓥')
    (LE: oV1 ⊑ oV2):
    default ∅ oV1 ⊑ 𝓥'.(acq).
  Proof. etrans; last by eapply read_helper_view_relaxed_1. by rewrite LE. Qed.

  Lemma read_helper_view_acq_1 {l t tr 𝓥 𝓥' V}
    (RH : read_helper 𝓥 AcqRel l t tr V 𝓥'):
    V ⊑ 𝓥'.(cur).
  Proof. inversion RH; simpl in *. by solve_lat. Qed.

  Lemma read_helper_view_acq {l t tr 𝓥 𝓥' oV1 oV2}
    (RH : read_helper 𝓥 AcqRel l t tr (default ∅ oV2) 𝓥')
    (LE: oV1 ⊑ oV2):
    default ∅ oV1 ⊑ 𝓥'.(cur).
  Proof. etrans; last by eapply read_helper_view_acq_1. by rewrite LE. Qed.

  Lemma read_helper_view_sc_1 l t tr 𝓥 𝓥' V
    (RH : read_helper 𝓥 SeqCst l t tr V 𝓥'):
    V ⊑ 𝓥'.(cur).
  Proof. inversion RH; simpl in *. by solve_lat. Qed.

  Lemma read_helper_view_sc l t tr 𝓥 𝓥' oV1 oV2
    (RH : read_helper 𝓥 SeqCst l t tr (default ∅ oV2) 𝓥')
    (LE: oV1 ⊑ oV2):
    default ∅ oV1 ⊑ 𝓥'.(cur).
  Proof. etrans; last by eapply read_helper_view_sc_1. by rewrite LE. Qed.

  Lemma read_helper_view_at l t tr 𝓥 𝓥' oV1 oV2 o
    (RH : read_helper 𝓥 o l t tr (default ∅ oV2) 𝓥')
    (LE: oV1 ⊑ oV2)
    (RLX: Relaxed ⊑ o):
    default ∅ oV1 ⊑ if decide (AcqRel ⊑ o) then 𝓥'.(cur) else 𝓥'.(acq).
  Proof.
    destruct o; [done|..]; simpl.
    - by eapply read_helper_view_relaxed.
    - by eapply read_helper_view_acq.
    - by eapply read_helper_view_sc.
  Qed.

  Lemma read_helper_view_at_acq l t tr 𝓥 𝓥' oV1 oV2 o
    (RH : read_helper 𝓥 o l t tr (default ∅ oV2) 𝓥')
    (LE: oV1 ⊑ oV2)
    (RLX: Relaxed ⊑ o):
    default ∅ oV1 ⊑ 𝓥'.(acq).
  Proof.
    etrans; first by eapply read_helper_view_at.
    case decide => ?; [by apply cur_acq|done].
  Qed.


  Lemma mem_addins_closed_tview 𝓥 𝓥' o Rr M1 𝑚 M2
    (WRITE: write_helper 𝓥 o (mloc 𝑚) (mto 𝑚) Rr 𝑚.(mbase).(mrel) 𝓥')
    (MADD: memory_addins 𝑚 M1 M2)
    (CLOSED: 𝓥 ∈ M1) : 𝓥' ∈ M2.
  Proof.
    inversion WRITE. clear H0.
    have INM2: ∀ ws, {[𝑚.(mloc) := [{ 𝑚.(mto), ws ,∅,∅ }] ]} ∈ M2.
    { move => ???.
      rewrite /view_lookup_write fmap_Some.
      move => [[????] []] /lookup_singleton_Some [<- <-] /= ->. do 2 eexists.
      split; last by eapply lookup_mem_addins_new. done. }
    have ?: (if decide (Relaxed ⊑ o)
            then {[𝑚.(mloc) := [{ 𝑚.(mto),{[𝑚.(mto)]},∅,∅ }]]}
            else {[𝑚.(mloc) := [{ 𝑚.(mto),∅,∅,∅ }]]}) ∈ M2.
    { by case decide => ?; apply INM2. }
    have ?: 𝓥.(frel) ∈ M2.
    { eapply closed_view_addins_mono; eauto. by apply CLOSED. }
    constructor; simpl; [|done|..].
    - move => l. case (decide (l = mloc 𝑚)) => [->|?];
        [rewrite lookup_insert|rewrite lookup_insert_ne; last done].
      + repeat apply join_closed_view=>//.
        * pose proof (closed_tview_rel _ _ CLOSED (mloc 𝑚)).
          destruct (rel 𝓥 !! mloc 𝑚) eqn:?; [|done].
          by eapply closed_view_addins_mono.
        * case (decide (AcqRel ⊑ _)) => _ //.
          apply join_closed_view => //.
          eapply closed_view_addins_mono; eauto. apply CLOSED.
      + eapply opt_closed_view_addins_mono=>//. apply CLOSED.
    - apply join_closed_view => //.
      eapply closed_view_addins_mono; eauto. apply CLOSED.
    - apply join_closed_view; [|by auto].
      eapply closed_view_addins_mono; eauto. apply CLOSED.
  Qed.

  Lemma write_helper_closed_tview 𝓥 𝓥' o Rr M1 𝑚 M2
    (WRITE: write_helper 𝓥 o (mloc 𝑚) (mto 𝑚) Rr 𝑚.(mbase).(mrel) 𝓥')
    (MWRITE: memory_write M1 𝑚 M2)
    (CLOSED: 𝓥 ∈ M1) : 𝓥' ∈ M2.
  Proof.
    inversion WRITE. clear H0.
    have INM2: ∀ ws, {[𝑚.(mloc) := [{ 𝑚.(mto), ws ,∅,∅ }] ]} ∈ M2.
    { move => ???.
      rewrite /view_lookup_write fmap_Some.
      move => [[????] []] /lookup_singleton_Some [<- <-] /= ->. do 2 eexists.
      split; last by eapply memory_write_new. done. }
    have ?: (if decide (Relaxed ⊑ o)
            then {[𝑚.(mloc) := [{ 𝑚.(mto),{[𝑚.(mto)]},∅,∅ }]]}
            else {[𝑚.(mloc) := [{ 𝑚.(mto),∅,∅,∅ }]]}) ∈ M2.
    { by case decide => ?; apply INM2. }
    have ?: 𝓥.(frel) ∈ M2.
    { eapply memory_write_closed_view; eauto. by apply CLOSED. }
    constructor; simpl; [|done|..].
    - move => l.
      case (decide (l = mloc 𝑚)) => [->|?];
        [rewrite lookup_insert|rewrite lookup_insert_ne; last done].
      + repeat apply join_closed_view=>//.
        * pose proof (closed_tview_rel _ _ CLOSED (mloc 𝑚)).
          destruct (rel 𝓥 !! mloc 𝑚)=>//.
          eapply memory_write_closed_view=>//.
        * case (decide (AcqRel ⊑ _)) => _ /=; [|done].
          apply join_closed_view; [|done].
          eapply memory_write_closed_view; eauto. apply CLOSED.
      + eapply memory_write_opt_closed_view; eauto. by apply CLOSED.
    - apply join_closed_view; [|by auto].
      eapply memory_write_closed_view; eauto. apply CLOSED.
    - apply join_closed_view; [|by auto].
      eapply memory_write_closed_view; eauto. apply CLOSED.
  Qed.

  Lemma write_helper_fresh {𝓥 l o t Rr Rw 𝓥'}
    (WH: write_helper 𝓥 o l t Rr Rw 𝓥') :
    𝓥.(cur) !!w l ⊏ Some t.
  Proof. by inversion WH. Qed.

  Lemma write_helper_read_write_relaxed' {𝓥 l o t Rr Rw 𝓥'}
    (WH: write_helper 𝓥 o l t Rr Rw 𝓥') (RLX: Relaxed ⊑ o) :
    Some Rr ⊑ Rw.
  Proof. inversion_clear WH. rewrite /write_Rw /= decide_True //. solve_lat. Qed.
  Lemma write_helper_read_write_relaxed {𝓥 l o t Rr Rw 𝓥'}
    (WH: write_helper 𝓥 o l t Rr Rw 𝓥') (RLX: Relaxed ⊑ o) :
    Rr ⊑ default ∅ Rw.
  Proof. inversion_clear WH. rewrite /write_Rw /= decide_True //. solve_lat. Qed.

  Lemma write_helper_read_write_relaxed_inv 𝓥 l o t Rr Rw 𝓥'
    (WH: write_helper 𝓥 o l t Rr Rw 𝓥') (RLX: Relaxed ⊑ o) :
    default ∅ Rw ⊑ Rr ⊔ 𝓥'.(cur).
  Proof.
    inversion_clear WH.
    rewrite /write_Rw /= !(decide_True (P := Relaxed ⊑ o)) //.
    have LeRel : default ∅ (𝓥.(rel) !! l) ⊑ 𝓥.(cur) by apply rel_cur'.
    have LeFrel : 𝓥.(frel) ⊑ 𝓥.(cur) by apply frel_cur.
    case decide => ? /=; solve_lat.
  Qed.

  Lemma write_helper_relaxed_mrel 𝓥 l t R oV 𝓥'
    (WH: write_helper 𝓥 Relaxed l t R oV 𝓥') :
    Some (𝓥.(frel) ⊔ {[l := [{ t,{[t]},∅,∅ }] ]}) ⊑ oV.
  Proof. inversion_clear WH. rewrite /write_Rw /=. solve_lat. Qed.

  Lemma write_helper_relaxed_mrel_frel 𝓥 l t R oV 𝓥'
    (WH: write_helper 𝓥 Relaxed l t R oV 𝓥') :
    Some 𝓥'.(frel) ⊑ oV.
  Proof. inversion WH. rewrite /write_Rw /=. solve_lat. Qed.

  Lemma write_helper_release_seqcst_mrel 𝓥 o l t R oV 𝓥'
    (REL: AcqRel ⊑ o)
    (WH: write_helper 𝓥 o l t R oV 𝓥'):
    Some (𝓥.(cur) ⊔ {[l := [{ t,{[t]},∅,∅ }] ]}) ⊑ oV.
  Proof. inversion_clear WH. destruct o; [done|done|simpl..]; solve_lat. Qed.

  Lemma write_helper_release_seqcst_mrel_cur' 𝓥 o l t R oV 𝓥'
    (REL: AcqRel ⊑ o)
    (WH: write_helper 𝓥 o l t R oV 𝓥'):
    𝓥.(cur) ⊑ default ∅ oV.
  Proof.
    eapply write_helper_release_seqcst_mrel in WH; [|done].
    change (Some 𝓥.(cur) ⊑ Some (default ∅ oV)). destruct oV as [V|]; [|done].
    simpl; etrans; [|apply WH]. solve_lat.
  Qed.

  Lemma write_helper_release_seqcst_mrel_cur 𝓥 o l t R oV 𝓥'
    (REL: AcqRel ⊑ o)
    (WH: write_helper 𝓥 o l t R oV 𝓥'):
    Some 𝓥'.(cur) ⊑ oV.
  Proof.
    etrans; last by eapply write_helper_release_seqcst_mrel.
    destruct o; [done|done|..]; by inversion WH.
  Qed.

  Lemma write_helper_release_mrel 𝓥 l t R oV 𝓥'
    (WH: write_helper 𝓥 AcqRel l t R oV 𝓥'):
    Some (𝓥.(cur) ⊔ {[l := [{ t,{[t]},∅,∅ }] ]}) ⊑ oV.
  Proof. by eapply write_helper_release_seqcst_mrel. Qed.

  Lemma write_helper_release_mrel_cur 𝓥 l t R oV 𝓥'
    (WH: write_helper 𝓥 AcqRel l t R oV 𝓥'):
    Some 𝓥'.(cur) ⊑ oV.
  Proof. by eapply write_helper_release_seqcst_mrel_cur. Qed.

  Lemma write_helper_acq_tview_include {𝓥 l t o R oV 𝓥'}
    (WH: write_helper 𝓥 o l t R oV 𝓥') (HACQ: R ⊑ 𝓥.(acq)) :
    oV ⊑ Some 𝓥'.(acq).
  Proof.
    inversion_clear WH. rewrite /write_tview /write_Rw /=.
    case_match=>//. case_match; rewrite rel_cur' frel_cur HACQ cur_acq; solve_lat.
  Qed.

  Lemma write_helper_cur_tview_include {𝓥 l t o R oV 𝓥'}
    (WH: write_helper 𝓥 o l t R oV 𝓥') (CUR: R ⊑ 𝓥.(cur)) :
    oV ⊑ Some 𝓥'.(cur).
  Proof.
    inversion_clear WH. rewrite /write_tview /write_Rw /=.
    case_match=>//. case_match; rewrite rel_cur' frel_cur CUR; solve_lat.
  Qed.

  Lemma writeRw_included 𝓥 o l t R:
    write_Rw 𝓥 o l t R ⊑ Some (R ⊔ 𝓥.(cur) ⊔ {[l := [{ t,{[t]},∅,∅ }] ]}).
  Proof.
    rewrite /write_Rw. case (decide _) => ?; [|done].
    destruct (𝓥.(rel) !! l) as [V|] eqn:EqV; simpl.
    - have LeV: V ⊑ 𝓥.(cur).
      { change (Some V ⊑ Some 𝓥.(cur)). rewrite -EqV. apply rel_cur. }
      rewrite LeV frel_cur. case (decide _) => ?; solve_lat.
    - rewrite frel_cur left_id_L. case (decide _) => ?; solve_lat.
  Qed.


  Lemma sc_fence_helper_closed_sc 𝓥 𝓥' 𝓢 𝓢' M
    (SC: sc_fence_helper 𝓥 𝓢 𝓥' 𝓢')
    (CLOSED: 𝓥 ∈ M) (CS: 𝓢 ∈ M):
    𝓢' ∈ M.
  Proof. inversion SC. apply join_closed_view; [by apply CLOSED|by auto]. Qed.

  Lemma sc_fence_helper_tview_sqsubseteq 𝓥 𝓥' 𝓢 𝓢'
    (SC: sc_fence_helper 𝓥 𝓢 𝓥' 𝓢') :
    𝓥 ⊑ 𝓥'.
  Proof.
    inversion SC.
    have ? : 𝓥.(acq) ⊑ (𝓥.(acq) ⊔ 𝓢) by solve_lat.
    constructor; rewrite /sc_fence_tview //= ?frel_cur cur_acq //.
  Qed.

  Lemma sc_fence_helper_sc_sqsubseteq 𝓥 𝓥' 𝓢 𝓢'
    (SC: sc_fence_helper 𝓥 𝓢 𝓥' 𝓢') :
    𝓢 ⊑ 𝓢'.
  Proof. inversion SC. solve_lat. Qed.

  Lemma sc_fence_helper_closed_tview 𝓥 𝓥' 𝓢 𝓢' M
    (SC: sc_fence_helper 𝓥 𝓢 𝓥' 𝓢')
    (CLOSED: 𝓥 ∈ M) (CS: 𝓢 ∈ M):
    𝓥' ∈ M.
  Proof.
    inversion SC.
    have ?: 𝓢' ∈ M by eapply sc_fence_helper_closed_sc.
    subst. constructor; simpl; [|done..]. apply CLOSED.
  Qed.

  Lemma alloc_helper_mem_closed_tview
        𝓥1 𝓥2 (𝑚s: list message) M1 M2
    (NONE: ∀ (n' : nat) 𝑚, 𝑚s !! n' = Some 𝑚 → 𝑚.(mbase).(mrel) = None)
    (MALL: mem_list_addins 𝑚s M1 M2)
    (VALL: alloc_helper 𝑚s 𝓥1 𝓥2)
    (CLOSED: 𝓥1 ∈ M1) : 𝓥2 ∈ M2.
  Proof.
    revert 𝓥1 𝓥2 M1 M2 CLOSED MALL VALL.
    induction 𝑚s; move => 𝓥1 𝓥2 M1 M2 CLOSED MALL VALL.
    - inversion VALL. inversion MALL. by subst.
    - inversion VALL. inversion MALL. subst.
      assert (NONE': ∀ (n' : nat) 𝑚, 𝑚s !! n' = Some 𝑚 → mrel (mbase 𝑚) = None).
      { move => n' 𝑚 In. eapply (NONE (n' + 1)).
        rewrite (lookup_app_r (a :: nil)); simpl; last by lia.
        rewrite (_: n' + 1 - 1 = n'); [done|by lia]. }
      eapply mem_addins_closed_tview; eauto.
      by rewrite (NONE 0 a).
  Qed.

  Lemma alloc_helper_tview_sqsubseteq 𝑚s 𝓥 𝓥'
    (ALLOC: alloc_helper 𝑚s 𝓥 𝓥') :
    𝓥 ⊑ 𝓥'.
  Proof.
    induction ALLOC; first by auto.
    apply write_helper_tview_sqsubseteq in WRITE. etrans; eauto.
  Qed.

  Lemma alloc_helper_cur_sqsubseteq 𝑚s 𝓥1 𝓥2
    (ALLOC: alloc_helper 𝑚s 𝓥1 𝓥2) :
    ∀ 𝑚, 𝑚 ∈ 𝑚s → Some 𝑚.(mto) ⊑ 𝓥2.(cur) !!w 𝑚.(mloc).
  Proof.
    move : 𝓥2 ALLOC.
    induction 𝑚s as [|𝑚 𝑚s IH] => 𝓥3 ALLOC 𝑚'; first by inversion 1.
    inversion_clear ALLOC.
    move => /elem_of_cons [->|In].
    - inversion WRITE. rewrite view_lookup_w_join view_lookup_w_insert.
      solve_lat.
    - etrans; first apply (IH _ NEXT _ In).
      rewrite /view_lookup_write. apply fmap_sqsubseteq; [apply _|].
      eapply write_helper_tview_sqsubseteq, WRITE.
  Qed.

  Lemma alloc_helper_awrite_ids  𝑚s 𝓥1 𝓥2
    (ALLOC: alloc_helper 𝑚s 𝓥1 𝓥2) :
    ∀ 𝑚, 𝑚 ∈ 𝑚s → Some ∅ ⊑ 𝓥2.(cur) !!aw 𝑚.(mloc).
  Proof.
    move : 𝓥2 ALLOC.
    induction 𝑚s as [|𝑚 𝑚s IH] => 𝓥3 ALLOC 𝑚'; first by inversion 1.
    inversion_clear ALLOC.
    move => /elem_of_cons [->|In].
    - inversion WRITE. rewrite view_lookup_aw_join view_lookup_aw_insert.
      solve_lat.
    - etrans; first apply (IH _ NEXT _ In).
      apply fmap_sqsubseteq; [apply _|].
      eapply write_helper_tview_sqsubseteq, WRITE.
  Qed.

  Lemma alloc_helper_nread_ids  𝑚s 𝓥1 𝓥2
    (ALLOC: alloc_helper 𝑚s 𝓥1 𝓥2) :
    ∀ 𝑚, 𝑚 ∈ 𝑚s → Some ∅ ⊑ 𝓥2.(cur) !!nr 𝑚.(mloc).
  Proof.
    move : 𝓥2 ALLOC.
    induction 𝑚s as [|𝑚 𝑚s IH] => 𝓥3 ALLOC 𝑚'; first by inversion 1.
    inversion_clear ALLOC.
    move => /elem_of_cons [->|In].
    - inversion WRITE. rewrite view_lookup_nr_join view_lookup_nr_insert.
      solve_lat.
    - etrans; first apply (IH _ NEXT _ In).
      apply fmap_sqsubseteq; [apply _|].
      eapply write_helper_tview_sqsubseteq, WRITE.
  Qed.

  Lemma alloc_helper_aread_ids  𝑚s 𝓥1 𝓥2
    (ALLOC: alloc_helper 𝑚s 𝓥1 𝓥2) :
    ∀ 𝑚, 𝑚 ∈ 𝑚s → Some ∅ ⊑ 𝓥2.(cur) !!ar 𝑚.(mloc).
  Proof.
    move : 𝓥2 ALLOC.
    induction 𝑚s as [|𝑚 𝑚s IH] => 𝓥3 ALLOC 𝑚'; first by inversion 1.
    inversion_clear ALLOC.
    move => /elem_of_cons [->|In].
    - inversion WRITE. rewrite view_lookup_ar_join view_lookup_ar_insert.
      solve_lat.
    - etrans; first apply (IH _ NEXT _ In).
      apply fmap_sqsubseteq; [apply _|].
      eapply write_helper_tview_sqsubseteq, WRITE.
  Qed.

  Lemma alloc_helper_cur_old 𝑚s 𝓥1 𝓥2 l
    (UPDATE : alloc_helper 𝑚s 𝓥1 𝓥2) (NONE: ∀ 𝑚, 𝑚 ∈ 𝑚s → l ≠ 𝑚.(mloc)):
    𝓥1.(cur) !! l = 𝓥2.(cur) !! l.
  Proof.
    induction UPDATE; first done.
    rewrite IHUPDATE.
    - inversion WRITE. rewrite lookup_join lookup_insert_ne; last first.
      { move => ?. eapply NONE; [by left|done]. }
      by rewrite lookup_empty right_id_L.
    - move => 𝑚' ?. apply NONE. by right.
  Qed.

  Lemma alloc_helper_rel_old 𝑚s 𝓥1 𝓥2 l
    (UPDATE : alloc_helper 𝑚s 𝓥1 𝓥2) (NONE: ∀ 𝑚, 𝑚 ∈ 𝑚s → l ≠ 𝑚.(mloc)):
    𝓥1.(rel) !! l = 𝓥2.(rel) !! l.
  Proof.
    induction UPDATE; first done.
    rewrite IHUPDATE.
    - inversion WRITE. rewrite /= lookup_insert_ne //.
      move => ?. eapply NONE; [by left|done].
    - move => 𝑚' ?. apply NONE. by right.
  Qed.

End ThreadView.
