From stdpp Require Import numbers.
From orc11 Require Export tview event.

Require Import stdpp.options.

Section Thread.

  Context `{!LocFacts loc} `{CVAL: Countable VAL} `{!Shift loc} `{!Allocator loc (memory loc VAL)}.

  Notation memory := (memory loc VAL).
  Notation message := (message loc VAL).
  Notation event := (event loc VAL).
  Notation view := (@view loc _).
  Notation threadView := (@threadView loc).

  Record global := mkGB {
    sc: view;
    na : view;
    mem: memory
  }.
  Record config := mkCFG { lc: threadView; gb : global; }.

  Implicit Type (𝑚: message) (M: memory) (𝓝: view) (G: global)
                (c: config) (𝓥: threadView).

  Definition dealloc_na_agree M 𝓝 :=
    ∀ l t m, M !! (l, t) = Some m → m.(mval) = DVal → Some t ⊑ 𝓝 !!w l.

  Record global_wf' G := {
    global_wf_mem : Wf G.(mem);
    global_wf_alloc : alloc_inv G.(mem);
    global_wf_dealloc_na : dealloc_na_agree G.(mem) G.(na);
    global_wf_sc : G.(sc) ∈ G.(mem);
    global_wf_na : G.(na) ∈ G.(mem);
  }.
  Global Instance global_wf : Wellformed global := global_wf'.

  Record global_le g1 g2 :=
    mkGlobalSqSubsetEq {
      global_sqsubseteq_sc  : g1.(sc)  ⊑ g2.(sc) ;
      global_sqsubseteq_na  : g1.(na)  = g2.(na) ; (* YES WE CAN *)
      global_sqsubseteq_mem : memory_le g1.(mem) g2.(mem)
    }.
  Global Instance global_sqsubseteq : SqSubsetEq global := global_le.

  Global Instance global_sqsubseteq_po :
    PartialOrder ((⊑) : SqSubsetEq global).
  Proof.
    constructor; [constructor|]; [done|..].
    - intros [][][] [][]. constructor; intros; by etrans.
    - intros [][] [][]. simpl in *. f_equal; [|done|].
      + by apply : (anti_symm (⊑)).
      + by apply : (anti_symm memory_le).
  Qed.

  Record config_wf' c := {
    config_wf_global: Wf c.(gb);
    config_wf_closed_tview : c.(lc) ∈ c.(gb).(mem);
  }.
  Global Instance config_wf : Wellformed config := config_wf'.

  Record config_le c1 c2 :=
    mkCFGSqSubsetEq {
      config_sqsubseteq_local  : c1.(lc)  ⊑ c2.(lc)  ;
      config_sqsubseteq_global : c1.(gb)  ⊑ c2.(gb) ;
    }.
  Global Instance config_sqsubseteq : SqSubsetEq config := config_le.

  Global Instance config_sqsubseteq_po :
    PartialOrder ((⊑) : SqSubsetEq config).
  Proof.
    split; [split|]; [done|..].
    - intros [][][] [][]. split; by etrans.
    - intros [][] [][]. simpl in *. f_equal; by apply : (anti_symm (⊑)).
  Qed.

  (** Thread-local non-promising steps *)

  (* <𝓥 ,M> -{ R(l,v,o) }-> <𝓥 ',M> *)
  Inductive read_step 𝓥1 M1 tr 𝑚 o 𝓥2: Prop :=
    | ReadStep
        (READ: read_helper 𝓥1 o 𝑚.(mloc) 𝑚.(mto) tr (default ∅ 𝑚.(mbase).(mrel)) 𝓥2)
        (IN: 𝑚 ∈ M1)
        (ALLOC: allocated 𝑚.(mloc) M1).

  (* <𝓥,M> -{ W(l,v,o) }-> <𝓥',M'> *)
  Inductive write_step 𝓥1 M1 𝑚 o V 𝓥2 M2: Prop :=
    | WriteStep
        (WRITE: memory_write M1 𝑚 M2)
        (WVIEW : write_helper 𝓥1 o 𝑚.(mloc) 𝑚.(mto) V 𝑚.(mbase).(mrel) 𝓥2).

  (* <𝓥,M> -{ U(l,vr,vw,or,ow) }-> <𝓥',M'> *)
  (* Inductive update_step L1 M1 𝑚1 𝑚2 or ow: bool → local → memory → Prop :=
    | UpdateStep 𝓥2 𝓥3 M3 b
        (READ: read_step L1 M1 𝑚1 or 𝓥2)
        (WRITE: write_step 𝓥2 M1 𝑚2 ow b (default ∅ 𝑚1.(mbase).(mrel)) 𝓥3 M3)
        (ADJ: 𝑚1.(mto) = 𝑚2.(mbase).(mfrom))
        (SAME: 𝑚1.(mloc) = 𝑚2.(mloc))
    : update_step L1 M1 𝑚1 𝑚2 or ow b 𝓥3 M3. *)

  (* 𝓥> -{ F_acq }-> 𝓥 ' *)
  Program Definition acq_fence_tview 𝓥 :=
    mkTView 𝓥.(rel) 𝓥.(frel) 𝓥.(acq) 𝓥.(acq) _ _ _ _.
  Next Obligation.
    intros. apply bool_decide_pack. etrans; [apply rel_dom|]. by rewrite cur_acq.
  Qed.
  Next Obligation. intros. apply bool_decide_pack=>l. by rewrite rel_cur cur_acq. Qed.
  Next Obligation. intros. apply bool_decide_pack. by rewrite frel_cur cur_acq. Qed.
  Next Obligation. intros. by apply bool_decide_pack. Qed.

  Inductive acq_fence_step 𝓥 : threadView → Prop :=
    | AcqFenceStep : acq_fence_step 𝓥 (acq_fence_tview 𝓥).

  (* 𝓥 -{ F_rel }-> <𝓥 ',P> *)
  Program Definition rel_fence_tview 𝓥 :=
    mkTView 𝓥.(rel) 𝓥.(cur) 𝓥.(cur) 𝓥.(acq) _ _ _ _.
  Next Obligation. intros. apply bool_decide_pack, rel_dom. Qed.
  Next Obligation. intros. apply bool_decide_pack, rel_cur. Qed.
  Next Obligation. intros. by apply bool_decide_pack. Qed.
  Next Obligation. intros. apply bool_decide_pack, cur_acq. Qed.
  Inductive rel_fence_step 𝓥: threadView → Prop :=
    | RelFenceStep
    : rel_fence_step 𝓥 (rel_fence_tview 𝓥).

  (* <𝓥,𝓢> -{ F_sc }-> <<𝓥 ',P>,𝓢'> *)
  Inductive sc_fence_step 𝓥 𝓢: view → threadView → Prop :=
    | SCFenceStep 𝓢' 𝓥'
        (SC: sc_fence_helper 𝓥 𝓢 𝓥' 𝓢')
    : sc_fence_step 𝓥 𝓢 𝓢' 𝓥'.

  (* <𝓥 ,M> -{ Alloc(l,n) }-> <𝓥 ',M'> *)
  Inductive alloc_step 𝓥1 M1 l n 𝑚s: threadView → memory → Prop :=
    | AllocStep M2 𝓥2
        (MEMALL: memory_alloc n l 𝑚s M1 M2)
        (VALL: alloc_helper 𝑚s 𝓥1 𝓥2)
    : alloc_step 𝓥1 M1 l n 𝑚s 𝓥2 M2.

  (* <𝓥 ,M> -{ Dealloc(l,n) }-> <𝓥 ',M'> *)
  Inductive dealloc_step 𝓥1 M1 l n: list message → threadView → memory → Prop :=
    | DeallocStep 𝑚s M2 𝓥2
        (MEMALL: memory_dealloc n l 𝑚s M1 M2)
        (VALL: alloc_helper 𝑚s 𝓥1 𝓥2)
    : dealloc_step 𝓥1 M1 l n 𝑚s 𝓥2 M2.

  (* DRF steps *)
  Definition fresh_aread_id (𝓝 : view) l :=
    fresh (default ∅ (𝓝 !!ar l)).
  Definition fresh_nread_id (𝓝 : view) l :=
    fresh (default ∅ (𝓝 !!nr l)).

  Definition add_aread_id (V : view) l r :=
    partial_alter
      (λ o, (λ p, [{ p.(twrite), p.(tawrite), p.(tnread), {[r]} ∪ p.(taread) }]) <$> o)
      l V.
  Definition add_nread_id (V : view) l r :=
    partial_alter
      (λ o, (λ p, [{ p.(twrite), p.(tawrite), {[r]} ∪ p.(tnread), p.(taread) }]) <$> o)
      l V.
  Definition add_awrite_id (V : view) l w :=
    partial_alter
      (λ o, (λ p, [{ p.(twrite), {[w]} ∪ p.(tawrite), p.(tnread), p.(taread) }]) <$> o)
      l V.
  Definition set_write_time (V : view) l t :=
    partial_alter (λ o, (λ p, [{ t, p.(tawrite), p.(tnread), p.(taread) }]) <$> o) l V.

  Lemma add_aread_id_sqsubseteq V l r :
    V ⊑ add_aread_id V l r.
  Proof.
    intros l'. rewrite /add_aread_id.
    case: (decide (l' = l)).
    - move => -> {l'}. rewrite lookup_partial_alter.
      move: (V !! l) => [/=[????]|//].
      repeat split; simpl; [done..|]. set_solver.
    - move => ?. rewrite lookup_partial_alter_ne //.
  Qed.

  Lemma add_nread_id_sqsubseteq V l r :
    V ⊑ add_nread_id V l r.
  Proof.
    intros l'. rewrite /add_aread_id.
    case: (decide (l' = l)).
    - move => -> {l'}. rewrite lookup_partial_alter.
      move: (V !! l) => [/=[????]|//].
      repeat split; simpl; [done..|set_solver|done].
    - move => ?. rewrite lookup_partial_alter_ne //.
  Qed.

  Section InsertAReadID.
    Context (𝓥 : threadView) (l : loc) (r : time_id).

    Program Definition tview_insert_aread_id :=
      let cur' := add_aread_id 𝓥.(cur) l r in
      let acq' := 𝓥.(acq) ⊔ cur' in
      mkTView 𝓥.(rel) 𝓥.(frel) cur' acq' _ _ _ _.
    Next Obligation.
      intros. apply bool_decide_pack. pose proof (rel_dom 𝓥).
      rewrite /cur' /add_aread_id. etrans; [done|].
      move => l' /elem_of_dom [[????] ?]. apply/elem_of_dom.
      case: (decide (l' = l)) => ?.
      - simplify_eq. rewrite lookup_partial_alter.
        eexists. rewrite fmap_Some. eexists; split; [eassumption|reflexivity].
      - rewrite lookup_partial_alter_ne //.
    Qed.
    Next Obligation.
      intros. apply bool_decide_pack=>l'.
      transitivity (Some 𝓥.(cur)).
      { generalize l'. eapply bool_decide_unpack, rel_cur_dec. }
      apply add_aread_id_sqsubseteq.
    Qed.
    Next Obligation.
      intros. apply bool_decide_pack.
      transitivity (𝓥.(cur)).
      { eapply bool_decide_unpack, frel_cur_dec. }
      apply add_aread_id_sqsubseteq.
    Qed.
    Next Obligation. intros. solve_lat. Qed.
  End InsertAReadID.

  Section InsertNReadID.
    Context (𝓥 : threadView) (l : loc) (r: time_id).

    Program Definition tview_insert_nread_id :=
      let cur' := add_nread_id 𝓥.(cur) l r in
      let acq' := 𝓥.(acq) ⊔ cur' in
      mkTView 𝓥.(rel) 𝓥.(frel) cur' acq' _ _ _ _.
    Next Obligation.
      intros. apply bool_decide_pack. pose proof (rel_dom 𝓥).
      rewrite /cur' /add_aread_id. etrans; [done|].
      move => l' /elem_of_dom [[????] ?]. apply/elem_of_dom.
      case: (decide (l' = l)) => ?.
      - simplify_eq. rewrite lookup_partial_alter.
        eexists. rewrite fmap_Some. eexists; split; [eassumption|reflexivity].
      - rewrite lookup_partial_alter_ne //.
    Qed.
    Next Obligation.
      intros. apply bool_decide_pack=>l'.
      transitivity (Some 𝓥.(cur)).
      { generalize l'. eapply bool_decide_unpack, rel_cur_dec. }
      apply add_nread_id_sqsubseteq.
    Qed.
    Next Obligation.
      intros. apply bool_decide_pack.
      transitivity (𝓥.(cur)).
      { eapply bool_decide_unpack, frel_cur_dec. }
      apply add_nread_id_sqsubseteq.
    Qed.
    Next Obligation. intros. solve_lat. Qed.
  End InsertNReadID.

  Inductive drf_pre_write l (𝓝 : view) 𝓥 M o : Prop :=
  | WriteDRF
      (* All writes must have seen all NA reads *)
      (ReadNA : 𝓝 !!nr l ⊑ 𝓥.(cur) !!nr l)
      (* All writes must have seen all NA writes *)
      (AllW   : 𝓝 !!w l ⊑ 𝓥.(cur) !!w l)
      (* NA writes must have seen the mo-latest write, all atomics reads and writes *)
      (WriteNA: if decide (Relaxed ⊑ o) then True
                else (∀ 𝑚', 𝑚' ∈ M → 𝑚'.(mloc) = l → Some (𝑚'.(mto)) ⊑ 𝓥.(cur) !!w l)
                    ∧ 𝓝 !!aw l ⊑ 𝓥.(cur) !!aw l ∧ 𝓝 !!ar l ⊑ 𝓥.(cur) !!ar l).

  Inductive drf_pre_read l (𝓝 : view) 𝓥 M o : Prop :=
  | ReadDRF
      (* All reads must have seen all NA writes *)
      (WriteNA: 𝓝 !!w l ⊑ 𝓥.(cur) !!w l)
      (* NA reads must have seen the mo-latest write *)
      (AllW   : if decide (Relaxed ⊑ o) then True
                else (∀ 𝑚', 𝑚' ∈ M → 𝑚'.(mloc) = l → Some (𝑚'.(mto)) ⊑ 𝓥.(cur) !!w l)
                ∧ 𝓝 !!aw l ⊑ 𝓥.(cur) !!aw l).

  Inductive drf_pre_dealloc l (n: positive) 𝓥 M 𝓝 : Prop :=
  | DeallocDRF
      (WNA: ∀ n', (n' < Pos.to_nat n)%nat →
            (∀ 𝑚', 𝑚' ∈ M → 𝑚'.(mloc) = l >> n' → Some (𝑚'.(mto)) ⊑ 𝓥.(cur) !!w (l >> n')))
      (ALL: ∀ n', (n' < Pos.to_nat n)%nat → 𝓝 !! (l >> n') ⊑ 𝓥.(cur) !! (l >> n'))
  : drf_pre_dealloc l n 𝓥 M 𝓝.

  Inductive drf_pre (𝓝 : view) 𝓥 M : event → Prop :=
  (* write *)
  | DRFPreW l o v (DRF: drf_pre_write l 𝓝 𝓥 M o)
    : drf_pre 𝓝 𝓥 M (Write l v o)
  (* read *)
  | DRFPreR l o v (DRF: drf_pre_read l 𝓝 𝓥 M o)
    : drf_pre 𝓝 𝓥 M (Read l v o)
  (* update *)
  | DRFPreU l or ow vr vw
      (DRFR: drf_pre_read l 𝓝 𝓥 M or) (DRFW: drf_pre_write l 𝓝 𝓥 M ow)
    : drf_pre 𝓝 𝓥 M (Update l vr vw or ow)
  (* dealloc *)
  | DRFPreDA l n (DRF: drf_pre_dealloc l n 𝓥 M 𝓝)
    : drf_pre 𝓝 𝓥 M (Dealloc l n)
  (* alloc *)
  | DRFPreAL l n
    : drf_pre 𝓝 𝓥 M (Alloc l n)
  (* fences *)
  | DRFPreF o1 o2
    : drf_pre 𝓝 𝓥 M (Fence o1 o2)
  .

  Inductive drf_post_read l o tr 𝓝 : view → Prop :=
  | DRFPstR 𝓝'
      (POST:  if decide (Relaxed ⊑ o)
              then (𝓝' = add_aread_id 𝓝 l tr ∧ tr = fresh_aread_id 𝓝 l)
              else (𝓝' = add_nread_id 𝓝 l tr) ∧ tr = fresh_nread_id 𝓝 l)
  : drf_post_read l o tr 𝓝 𝓝'.

  Inductive drf_post_write l t o 𝓝 : view → Prop :=
  | DRFPstW 𝓝'
      (POST:  if decide (Relaxed ⊑ o)
              then 𝓝' = add_awrite_id 𝓝 l t
              else 𝓝' = set_write_time 𝓝 l t)
  : drf_post_write l t o 𝓝 𝓝'.

  Inductive drf_post_update l tr tw 𝓝 : view → Prop :=
  | DRFPstU 𝓝'
      (POST: 𝓝' = add_awrite_id (add_aread_id 𝓝 l tr) l tw ∧ tr = fresh_aread_id 𝓝 l)
  : drf_post_update l tr tw 𝓝 𝓝'.

  Inductive drf_post (𝓝 : view) : event → option time → list message → view → Prop :=
  (* write *)
  | DRFPostW 𝑚 v o 𝓝'
      (DRF: drf_post_write 𝑚.(mloc) 𝑚.(mto) o 𝓝 𝓝')
    : drf_post 𝓝  (Write 𝑚.(mloc) v o) None [𝑚] 𝓝'
  (* read *)
  | DRFPostR l tr o v 𝓝' (DRF: drf_post_read l o tr 𝓝 𝓝')
    : drf_post 𝓝 (Read l v o) (Some tr) [] 𝓝'
  (* update *)
  | DRFPostU 𝑚 or ow tr vr vw 𝓝'
      (DRF: drf_post_update 𝑚.(mloc) tr 𝑚.(mto) 𝓝 𝓝')
    : drf_post 𝓝 (Update 𝑚.(mloc) vr vw or ow) (Some tr) [𝑚] 𝓝'
  (* dealloc *)
  | DRFPostDA l n 𝑚s
    : drf_post 𝓝 (Dealloc l n) None 𝑚s (alloc_new_na 𝓝 𝑚s)
  (* alloc *)
  | DRFPostAL l n 𝑚s
    : drf_post 𝓝 (Alloc l n) None 𝑚s (alloc_new_na 𝓝 𝑚s)
  (* fences *)
  | DRFPostF o1 o2
    : drf_post 𝓝 (Fence o1 o2) None [] 𝓝
  .


  Inductive machine_step 𝓥1 M1 𝓢1 :
    event → option time → list message → threadView → memory → view → Prop :=
  (* ALLOC *)
  (* (alloc_new_na c1.(gb).(na) 𝑚s) *)
  | PStepA l n 𝓥2 M2 𝑚s
        (ALLOC: alloc_step 𝓥1 M1 l (Pos.to_nat n) 𝑚s 𝓥2 M2)
  : machine_step 𝓥1 M1 𝓢1 (Alloc l n) None 𝑚s 𝓥2 M2 𝓢1
  (* DEALLOC *)
  (* (alloc_new_na c1.(gb).(na) 𝑚s) *)
  | PStepD l n 𝑚s 𝓥2 M2
        (DEALLOC: dealloc_step 𝓥1 M1 l (Pos.to_nat n) 𝑚s 𝓥2 M2)
  : machine_step 𝓥1 M1 𝓢1
        (Dealloc l n) None 𝑚s 𝓥2 M2 𝓢1
  (* READ *)
  | PStepR 𝑚 o 𝓥2 𝓝2 tr
        (READ: read_step 𝓥1 M1 tr 𝑚 o 𝓥2)
  : machine_step 𝓥1 M1 𝓢1
        (Read 𝑚.(mloc) 𝑚.(mbase).(mval) o) (Some tr) [] 𝓥2 M1 𝓢1
  (* WRITE *)
  | PStepW 𝑚 o 𝓥2 M2 v
        (ISVAL: 𝑚.(mbase).(mval) = VVal v)
        (WRITE: write_step 𝓥1 M1 𝑚 o ∅ 𝓥2 M2)
  : machine_step 𝓥1 M1 𝓢1
        (Write 𝑚.(mloc) v o) None [𝑚] 𝓥2 M2 𝓢1
  (* UPDATE *)
  | PStepU 𝑚1 𝑚2 or ow 𝓥2 𝓥3 M3 tr v1 v2
        (ISV1 : 𝑚1.(mbase).(mval) = VVal v1)
        (ISV2 : 𝑚2.(mbase).(mval) = VVal v2)
        (ADJ: 𝑚2.(mto) = (𝑚1.(mto) + 1)%positive)
        (SAME: 𝑚1.(mloc) = 𝑚2.(mloc))
        (READ: read_step 𝓥1 M1 tr 𝑚1 or 𝓥2)
        (WRITE: write_step 𝓥2 M1 𝑚2 ow (default ∅ 𝑚1.(mbase).(mrel)) 𝓥3 M3)
  :  machine_step 𝓥1 M1 𝓢1
        (Update 𝑚1.(mloc) v1 v2 or ow) (Some tr) [𝑚2] 𝓥3 M3 𝓢1
  (* ACQ-FENCE *)
  | PStepFAcq 𝓥2
        (FACQ: acq_fence_step 𝓥1 𝓥2)
  : machine_step 𝓥1 M1 𝓢1
        (Fence AcqRel Relaxed) None [] 𝓥2 M1 𝓢1
  (* REL-FENCE *)
  | PStepFRel 𝓥2
        (FREL: rel_fence_step 𝓥1 𝓥2)
  : machine_step 𝓥1 M1 𝓢1
        (Fence Relaxed AcqRel) None [] 𝓥2 M1 𝓢1
  (* SC-FENCE *)
  | PStepFSC 𝓥2 𝓢2
        (FSC: sc_fence_step 𝓥1 𝓢1 𝓢2 𝓥2)
  : machine_step 𝓥1 M1 𝓢1
        (Fence SeqCst SeqCst) None [] 𝓥2 M1 𝓢2.

End Thread.

Section Machine.
  (** Machine instantiations *)
  Context `{Countable VAL}.

  (** Thread steps for machine whose locations are positives *)
  Definition pos_machine_step := machine_step (loc:= positive) (VAL:=VAL).

  (** Thread steps for machine whose locations are block+offset's *)
  Definition lbl_machine_step := machine_step (loc:= lblock) (VAL:=VAL).

End Machine.


Section props.

  Context `{!LocFacts loc} `{CVAL: Countable VAL} `{!Shift loc} `{!Allocator loc (memory loc VAL)}.

  Notation memory := (memory loc VAL).
  Notation message := (message loc VAL).
  Notation baseMessage := (@baseMessage loc _ VAL).
  Notation event := (event loc VAL).
  Notation view := (@view loc _).
  Notation threadView := (@threadView loc).
  Notation global := (@global loc _ VAL).
  Notation config := (@config loc _ VAL).

  Implicit Type (𝑚: message) (M: memory) (𝓝: view) (G: global)
                (c: config) (𝓥: threadView).

  Lemma add_nread_id_eq V l r l' :
   add_nread_id V l r !!w l' = V !!w l' ∧
   add_nread_id V l r !!aw l' = V !!aw l' ∧
   add_nread_id V l r !!ar l' = V !!ar l'.
  Proof.
    rewrite /view_lookup_write /view_lookup_awrite /view_lookup_aread /add_nread_id.
    case: (decide (l' = l)) => [->|?].
    - rewrite lookup_partial_alter.
      by case: (_ !! _) => //.
    - rewrite lookup_partial_alter_ne //.
  Qed.
  Lemma add_nread_id_eqw V l r l' :
   add_nread_id V l r !!w l' = V !!w l'.
  Proof. by apply add_nread_id_eq. Qed.
  Lemma add_nread_id_eqaw V l r l' :
   add_nread_id V l r !!aw l' = V !!aw l'.
  Proof. by apply add_nread_id_eq. Qed.
  Lemma add_nread_id_eqar V l r l' :
   add_nread_id V l r !!ar l' = V !!ar l'.
  Proof. by apply add_nread_id_eq. Qed.

  Lemma add_aread_id_eq V l r l' :
    add_aread_id V l r !!w l' = V !!w l' ∧
    add_aread_id V l r !!aw l' = V !!aw l' ∧
    add_aread_id V l r !!nr l' = V !!nr l'.
  Proof.
    rewrite /view_lookup_write /view_lookup_awrite /view_lookup_nread /add_aread_id.
    case: (decide (l' = l)) => [->|?].
    - rewrite lookup_partial_alter.
      by case: (_ !! _) => //.
    - rewrite lookup_partial_alter_ne //.
  Qed.
  Lemma add_aread_id_eqw V l r l' :
   add_aread_id V l r !!w l' = V !!w l'.
  Proof. by apply add_aread_id_eq. Qed.
  Lemma add_aread_id_eqaw V l r l' :
   add_aread_id V l r !!aw l' = V !!aw l'.
  Proof. by apply add_aread_id_eq. Qed.
  Lemma add_aread_id_eqnr V l r l' :
   add_aread_id V l r !!nr l' = V !!nr l'.
  Proof. by apply add_aread_id_eq. Qed.

  Lemma add_awrite_id_eq V l r l' :
   add_awrite_id V l r !!w l' = V !!w l' ∧
   add_awrite_id V l r !!nr l' = V !!nr l' ∧
   add_awrite_id V l r !!ar l' = V !!ar l'.
  Proof.
    rewrite /view_lookup_write /view_lookup_nread /view_lookup_aread /add_awrite_id.
    case: (decide (l' = l)) => [->|?].
    - rewrite lookup_partial_alter.
      by case: (_ !! _) => //.
    - rewrite lookup_partial_alter_ne //.
  Qed.
  Lemma add_awrite_id_eqw V l r l' :
   add_awrite_id V l r !!w l' = V !!w l'.
  Proof. by apply add_awrite_id_eq. Qed.
  Lemma add_awrite_id_eqnr V l r l' :
   add_awrite_id V l r !!nr l' = V !!nr l'.
  Proof. by apply add_awrite_id_eq. Qed.
  Lemma add_awrite_id_eqar V l r l' :
   add_awrite_id V l r !!ar l' = V !!ar l'.
  Proof. by apply add_awrite_id_eq. Qed.

  Lemma add_aread_id_memory V l r M :
    V ∈ M → add_aread_id V l r ∈ M.
  Proof. move => IN ??. rewrite add_aread_id_eqw. by apply IN. Qed.

  Lemma add_nread_id_memory V l r M :
    V ∈ M → add_nread_id V l r ∈ M.
  Proof. move => IN ??. rewrite add_nread_id_eqw. by apply IN. Qed.

  Lemma add_awrite_id_memory V l r M :
    V ∈ M → add_awrite_id V l r ∈ M.
  Proof. move => IN ??. rewrite add_awrite_id_eqw. by apply IN. Qed.

  Lemma add_awrite_id_sqsubseteq V l r :
    V ⊑ add_awrite_id V l r.
  Proof.
    intros l'. rewrite /add_awrite_id.
    case: (decide (l' = l)).
    - move => -> {l'}. rewrite lookup_partial_alter.
      move: (V !! l) => [/=[????]|//].
      repeat split; simpl; [done| |done..]. set_solver.
    - move => ?. rewrite lookup_partial_alter_ne //.
  Qed.

  Lemma add_awrite_id_mono V1 V2 l r:
    V1 ⊑ V2 → add_awrite_id V1 l r ⊑ add_awrite_id V2 l r.
  Proof.
    move => LE l'. apply view_sqsubseteq. repeat split.
    - rewrite 2!add_awrite_id_eqw. by apply view_sqsubseteq.
    - rewrite /add_awrite_id /= /view_lookup_awrite /=.
      case (decide (l' = l)) => [->|?].
      + rewrite !lookup_partial_alter. apply fmap_sqsubseteq; [apply _|].
        apply fmap_sqsubseteq; [|apply LE].
        intros [][] [?[?[??]]]; simpl. repeat split => //. solve_proper.
      + do 2 (rewrite lookup_partial_alter_ne; [|done]).
        apply fmap_sqsubseteq; [apply _|apply LE].
    - rewrite 2!add_awrite_id_eqnr. by apply view_sqsubseteq.
    - rewrite 2!add_awrite_id_eqar. by apply view_sqsubseteq.
  Qed.

  Lemma add_aread_id_mono V1 V2 l r:
    V1 ⊑ V2 → add_aread_id V1 l r ⊑ add_aread_id V2 l r.
  Proof.
    move => LE l'. apply view_sqsubseteq. repeat split.
    - rewrite 2!add_aread_id_eqw. by apply view_sqsubseteq.
    - rewrite 2!add_aread_id_eqaw. by apply view_sqsubseteq.
    - rewrite 2!add_aread_id_eqnr. by apply view_sqsubseteq.
    - rewrite /add_aread_id /= /view_lookup_aread /=.
      case (decide (l' = l)) => [->|?].
      + rewrite !lookup_partial_alter. apply fmap_sqsubseteq; [apply _|].
        apply fmap_sqsubseteq; [|apply LE].
        intros [][] [?[?[??]]]; simpl. repeat split => //. solve_proper.
      + do 2 (rewrite lookup_partial_alter_ne; [|done]).
        apply fmap_sqsubseteq; [apply _|apply LE].
  Qed.

  Lemma add_nread_id_mono V1 V2 l r:
    V1 ⊑ V2 → add_nread_id V1 l r ⊑ add_nread_id V2 l r.
  Proof.
    move => LE l'. apply view_sqsubseteq. repeat split.
    - rewrite 2!add_nread_id_eqw. by apply view_sqsubseteq.
    - rewrite 2!add_nread_id_eqaw. by apply view_sqsubseteq.
    - rewrite /add_nread_id /= /view_lookup_nread /=.
      case (decide (l' = l)) => [->|?].
      + rewrite !lookup_partial_alter. apply fmap_sqsubseteq; [apply _|].
        apply fmap_sqsubseteq; [|apply LE].
        intros [][] [?[?[??]]]; simpl. repeat split => //. solve_proper.
      + do 2 (rewrite lookup_partial_alter_ne; [|done]).
        apply fmap_sqsubseteq; [apply _|apply LE].
    - rewrite 2!add_nread_id_eqar. by apply view_sqsubseteq.
  Qed.

  Lemma add_nread_id_dealloc_agree M V l t:
    dealloc_na_agree M V → dealloc_na_agree M (add_nread_id V l t).
  Proof. move => DA ???. rewrite add_nread_id_eqw. by apply DA. Qed.

  Lemma add_aread_id_dealloc_agree M V l t:
    dealloc_na_agree M V → dealloc_na_agree M (add_aread_id V l t).
  Proof. move => DA ???. rewrite add_aread_id_eqw. by apply DA. Qed.

  Lemma add_awrite_id_dealloc_agree M V l t:
    dealloc_na_agree M V → dealloc_na_agree M (add_awrite_id V l t).
  Proof. move => DA ???. rewrite add_awrite_id_eqw. by apply DA. Qed.

  Lemma set_write_time_id V l t (HL: V !!w l = Some t):
    set_write_time V l t = V.
  Proof.
    apply (map_eq _ V) => l'. rewrite /set_write_time.
    case: (decide (l' = l)).
    - move => -> {l'}. rewrite lookup_partial_alter.
      destruct (V !! l) as [[]|] eqn:EqV; rewrite EqV; [|done]. simpl.
      f_equal. f_equal. rewrite (view_lookup_w _ _ _ _ _ _ EqV) in HL.
      by inversion HL.
    - move => ?. rewrite lookup_partial_alter_ne //.
  Qed.

  Lemma set_write_time_mono V1 V2 l t:
  V1 ⊑ V2 → set_write_time V1 l t ⊑ set_write_time V2 l t.
  Proof.
    move => LE l'. rewrite /set_write_time.
    case (decide (l' = l)) => [->|?].
    - rewrite 2!lookup_partial_alter /=. apply fmap_sqsubseteq.
      + by intros [] [] [? [? []]].
      + by apply LE.
    - do 2 (rewrite lookup_partial_alter_ne; [|done]). by apply LE.
  Qed.

  Lemma mem_cut_insert_set_write M V l C t (IS: is_Some (V !! l)):
    <[l:=cell_cut t C]> (mem_cut M V) = mem_cut (<[l:=C]> M) (set_write_time V l t).
  Proof.
    rewrite /set_write_time
      (mem_cut_insert _ _ _ _ _ (default ∅ (V !!aw l))
          (default ∅ (V !!nr l)) (default ∅ (V !!ar l))).
    f_equal. apply (map_eq (<[_ := _]> V)) => l'.
    case (decide (l' = l)) => ?; [subst l'|].
    - rewrite lookup_insert lookup_partial_alter /=.
      destruct (V !! l) as [[]|] eqn:Eql; rewrite Eql; simpl.
      + by rewrite (view_lookup_aw _ _ _ _ _ _ Eql)
          (view_lookup_ar _ _ _ _ _ _ Eql) (view_lookup_nr _ _ _ _ _ _ Eql) /=.
      + by destruct IS.
    - rewrite lookup_insert_ne; [|done].
      by rewrite lookup_partial_alter_ne; [|done].
  Qed.

  Lemma mem_cut_write l 𝑚 o M1 M2 𝓝1 𝓝2 Vc 𝓥 t1 Cf1
    (WRITE : memory_addins 𝑚 M1 M2)
    (DRFR : drf_pre_write 𝑚.(mloc) 𝓝1 𝓥 M1 o)
    (DRFP : drf_post_write 𝑚.(mloc) 𝑚.(mto) o 𝓝1 𝓝2)
    (LE: 𝓝1 ⊑ Vc)
    (HL: M1 !!c l = Cf1 ∧ Vc !!w l = Some t1)
    (NEWT: t1 ⊏ 𝑚.(mto)) (EQLOC: l = 𝑚.(mloc))
    (NEW: 𝓥.(cur) !!w l ⊏ Some 𝑚.(mto)) :
    let C2 : cell :=  <[𝑚.(mto) := 𝑚.(mbase)]> (if (decide (Relaxed ⊑ o))
                                                then (cell_cut t1 Cf1) else ∅) in
    let Vc' : view := (if decide (Relaxed ⊑ o) then add_awrite_id Vc l 𝑚.(mto)
                      else set_write_time Vc l 𝑚.(mto)) in
    let t2 : time := (if (decide (Relaxed ⊑ o)) then t1 else 𝑚.(mto)) in
    ∃ Cf2, M2 = <[l:=Cf2]> M1 ∧ 𝓝2 ⊑ Vc' ∧ C2 = cell_cut t2 Cf2.
  Proof.
    have EqCf2 := memory_addins_eq _ _ _ WRITE.
    destruct HL as [EqCf1 HL]. rewrite -EQLOC EqCf1 /= in EqCf2.
    exists (<[mto 𝑚:=mbase 𝑚]> Cf1).
    split; [done|]. inversion DRFR. inversion DRFP; subst.
    case_decide; subst; split.
    - by apply add_awrite_id_mono.
    - rewrite cell_cut_insert; [done|]. by apply strict_include in NEWT.
    - by apply set_write_time_mono.
    - rewrite cell_cut_insert; [|done].
      f_equal. symmetry. apply cell_cut_empty => t' [m' Eqt'].
      have LT: t' ⊏ 𝑚.(mto).
      { change (Some t' ⊏ Some 𝑚.(mto)). destruct WriteNA as [LAST ?].
        eapply strict_transitive_r;
          [apply (LAST (mkMsg 𝑚.(mloc) t' m')); [|done]|done].
        by rewrite -memory_lookup_cell in Eqt'. }
      by apply Pos.lt_nle, LT.
  Qed.

  Lemma mem_cut_add_aread_id M V l t:
    mem_cut M (add_aread_id V l t) = mem_cut M V.
  Proof.
    rewrite /mem_cut /mem_cut_filter.
    apply (map_filter_ext (M:= gmap (loc * time))).
    move => [l' t'] m' ? /=. by rewrite add_aread_id_eqw.
  Qed.

  Lemma mem_cut_add_nread_id M V l t:
    mem_cut M (add_nread_id V l t) = mem_cut M V.
  Proof.
    rewrite /mem_cut /mem_cut_filter.
    apply (map_filter_ext (M:= gmap (loc * time))).
    move => [l' t'] m' ? /=. by rewrite add_nread_id_eqw.
  Qed.

  Lemma mem_cut_add_awrite_id M V l t:
    mem_cut M (add_awrite_id V l t) = mem_cut M V.
  Proof.
    rewrite /mem_cut /mem_cut_filter.
    apply (map_filter_ext (M:= gmap (loc * time))).
    move => [l' t'] m' ? /=. by rewrite add_awrite_id_eqw.
  Qed.

  Lemma memory_cell_insert_id l M:
    <[l := M !!c l]> M = M.
  Proof.
    apply (map_eq (M:= gmap _)) => [[l' t]]. rewrite !memory_lookup_cell.
    destruct (decide (l = l')) as [->|?].
    - by rewrite memory_cell_lookup_insert.
    - by rewrite memory_cell_lookup_insert_ne.
  Qed.

  Lemma cell_cut_singleton_eq C (t: time) (m: baseMessage)
    (MAX: ∀ (t0: time), is_Some (C !! t0) → (t0 ≤ t)%positive)
    (Eqt': C !! t = Some m):
    cell_cut t C = {[t := m]}.
  Proof.
    apply map_eq => t0.
    case (decide (t0 = t)) => [->|NE];
      [rewrite lookup_insert|rewrite lookup_insert_ne; last done].
    - by apply cell_cut_lookup_Some.
    - apply cell_cut_lookup_None.
      destruct (C !! t0) as [m0|] eqn:Eqt0; [right|by left].
      move => Le. apply NE. apply : anti_symm; [apply MAX; by eexists|done].
  Qed.

  Lemma mem_cut_max_time l (t: time) m M C Vc tc
    (CUT: C = cell_cut tc (M !!c l))
    (MAX: ∀ (t0 : time), is_Some (C !! t0) → (t0 ≤ t)%positive)
    (Eqt: C !! t = Some m)
    (IS: is_Some (Vc !! l)) :
    mem_cut M (set_write_time Vc l t) = (<[l:={[t := m]}]> (mem_cut M Vc)).
  Proof.
    rewrite -{1}(memory_cell_insert_id l M) -mem_cut_insert_set_write; [|done].
    f_equal. apply cell_cut_singleton_eq.
    - move => t0 [m0 Eqt0].
      case (decide (t0 ≤ tc)%positive) => Le.
      + etrans; [apply Le|].
        apply (cell_cut_lookup_Some (M !!c l) _ _ m). by rewrite -CUT.
      + apply MAX. exists m0. rewrite CUT.
        apply cell_cut_lookup_Some. split; [done|].
        apply Pos.lt_le_incl. by apply Pos.lt_nle in Le.
    - move : Eqt. rewrite CUT. by move => /cell_cut_lookup_Some [?].
  Qed.
End props.

Section memory_lblock.
  Context `{CVAL: Countable VAL}.
  Notation memory := (@memory _ lblock_loc VAL).
  (** Some properties of memory specific to lblock *)
  Lemma memory_alloc_old n l 𝑚s (M1 M2 : memory)
    (ALLOC: memory_alloc n l 𝑚s M1 M2):
    ∀ i : Z, (¬ l.2 ≤ i < l.2 + Z.of_nat n)%Z → M2 !!c (l.1, i) = M1 !!c (l.1, i).
  Proof.
    move => n' NIn.
    inversion ALLOC. symmetry.
    eapply mem_list_addins_old; first exact ADD.
    move => 𝑚 /elem_of_list_lookup [n1 Eq1].
    have Lt := lookup_lt_Some _ _ _ Eq1. rewrite LEN in Lt.
    apply AMES in Eq1 as [Eq1 _]. rewrite Eq1.
    rewrite /location.shift /=. inversion 1; subst n'. lia.
  Qed.

  Lemma alloc_step_mem_old 𝓥1 (M1: memory) l n 𝑚s 𝓥2 M2
    (ALLOC: alloc_step 𝓥1 M1 l n 𝑚s 𝓥2 M2) :
    ∀ i : Z, (¬ l.2 ≤ i < l.2 + Z.of_nat n)%Z → M2 !!c (l.1, i) = M1 !!c (l.1, i).
  Proof. inversion ALLOC. by eapply memory_alloc_old. Qed.

  Lemma memory_alloc_old_2 n l 𝑚s (M1 M2 : memory)
    (ALLOC: memory_alloc n l 𝑚s M1 M2) :
    ∀ l', l'.1 ≠ l.1 → M2 !!c l' = M1 !!c l'.
  Proof.
    move => l' NEq. inversion ALLOC. symmetry.
    eapply mem_list_addins_old; first exact ADD.
    move => 𝑚 /elem_of_list_lookup [n1 Eq1].
    have Lt := lookup_lt_Some _ _ _ Eq1. rewrite LEN in Lt.
    apply AMES in Eq1 as [Eq1 _]. rewrite Eq1. rewrite /shift /=.
    destruct l'. by inversion 1.
  Qed.

  Lemma alloc_step_mem_old_2 𝓥1 (M1: memory) l n 𝑚s 𝓥2 M2
    (ALLOC: alloc_step 𝓥1 M1 l n 𝑚s 𝓥2 M2) :
    ∀ l', l'.1 ≠ l.1 → M2 !!c l' = M1 !!c l'.
  Proof. inversion ALLOC. by eapply memory_alloc_old_2. Qed.
End memory_lblock.
