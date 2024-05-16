From gpfsl.examples Require Import sflib.

From stdpp Require Import namespaces.

From gpfsl.logic Require Import logatom.

From gpfsl.examples.history Require Export spec.
From gpfsl.examples.stack Require Export event.

Require Import iris.prelude.options.

Local Open Scope Z_scope.

Definition stack_state := list (event_id * Z * view * logView).

Local Notation history := (history sevent).
Implicit Types (E : history) (stk : stack_state).

(* Build stack state with the events in the given order *)
Inductive stack_run : ∀ (e : event_id) (eV : graph_event sevent) stk stk', Prop :=
  | stack_run_Push u uV v stk
      (PUSH : uV.(ge_event) = Push v)
      (NZ : 0 < v)
      : stack_run u uV
          stk
          ((u, v, uV.(ge_view).(dv_comm), uV.(ge_lview)) :: stk)
  | stack_run_Pop u o oV v V lV stk
      (POP : oV.(ge_event) = Pop v)
      (NZ : 0 < v)
      (SYNC : V ⊑ oV.(ge_view).(dv_comm))
      (LVIEW : u ∈ oV.(ge_lview))
      : stack_run o oV
          ((u, v, V, lV) :: stk)
          stk
  | stack_run_EmpPop o oV stk
      (EMPPOP : oV.(ge_event) = EmpPop)
      : stack_run o oV [] []
  .

Inductive stack_interp E : ∀ (ord : list event_id) stk1 stk2, Prop :=
  | stack_interp_nil stk : stack_interp E [] stk stk
  | stack_interp_snoc e eV ord ord' stk1 stk2 stk3
      (INTERP' : stack_interp E ord' stk1 stk2)
      (ORD : ord = ord' ++ [e])
      (EVENT : E !! e = Some eV)
      (RUN : stack_run e eV stk2 stk3)
      : stack_interp E ord stk1 stk3.

Definition not_empty_pop E (e : event_id) :=
  ∀ eV (EV : E !! e = Some eV), eV.(ge_event) ≠ EmpPop.

Global Instance not_empty_pop_dec E e : Decision (not_empty_pop E e).
Proof.
  unfold not_empty_pop. case (E !! e) as [[s V]|].
  - destruct s; [left|left|right]; eauto; by intros ? [= <-].
  - by left.
Qed.

(** Write event ids orderd by [xo] *)
Definition write_xo E : list event_id :=
  filter (not_empty_pop E) (seq 0 (length E)).

Local Notation EMPTY := 0 (only parsing).
Local Notation FAIL_RACE := (-1) (only parsing).

Definition StackLocalT Σ : Type :=
  ∀ (γg : gname) (s : loc) (E : history) (M : logView), vProp Σ.
Definition StackLocalNT Σ : Type :=
  ∀ (N : namespace), StackLocalT Σ.
Definition StackInvT Σ : Type :=
  ∀ (γg : gname) (s : loc) (E : history), vProp Σ.

Definition new_stack_spec' {Σ} `{!noprolG Σ, !inG Σ (historyR sevent)}
  (new_stack : val) (StackLocal : StackLocalNT Σ) (StackInv : StackInvT Σ) : Prop :=
  ∀ N tid,
  {{{ True }}}
    new_stack [] @ tid; ⊤
  {{{ γg (s: loc), RET #s; StackLocal N γg s [] ∅ ∗ StackInv γg s [] }}}.

Definition try_push_spec' {Σ} `{!noprolG Σ, !inG Σ (historyR sevent)}
  (try_push : val) (StackLocal : StackLocalNT Σ) (StackInv : StackInvT Σ) : Prop :=
  ∀ N (DISJ: N ## histN) (s: loc) tid γg E1 M (V : view) (v : Z) (Posx: 0 < v),
  (* PRIVATE PRE *)
  (* E1 is a snapshot of the history, locally observed by M *)
  ⊒V -∗ StackLocal N γg s E1 M -∗
  (* PUBLIC PRE *)
  <<< ∀ E, ▷ StackInv γg s E >>>
    try_push [ #s ; #v] @ tid; ↑N
  <<< ∃ (b: bool) V' E' (psId : event_id) ps Vpush M',
      (* PUBLIC POST *)
      ▷ StackInv γg s E' ∗
      ⊒V' ∗ @{V'} StackLocal N γg s E' M' ∗
      ⌜ (* FAIL_RACE case *)
        (b = false ∧ E' = E ∧ M' = M)
      ∨ (* successful case *)
        ( b = true ∧
          Vpush.(dv_in) = V ∧ Vpush.(dv_comm) = V' ∧
          is_push ps v ∧
          psId = length E ∧
          E' = E ++ [mkGraphEvent ps Vpush M'] ∧
          M' = {[psId]} ∪ M ) ⌝,
      RET #b, emp >>>
  .

Definition push_spec' {Σ} `{!noprolG Σ, !inG Σ (historyR sevent)}
  (push : val) (StackLocal : StackLocalNT Σ) (StackInv : StackInvT Σ) : Prop :=
  ∀ N (DISJ: N ## histN) (s: loc) tid γg E1 M (V : view) (v : Z) (Posx: 0 < v),
  (* PRIVATE PRE *)
  (* E1 is a snapshot of the history, locally observed by M *)
  ⊒V -∗ StackLocal N γg s E1 M -∗
  (* PUBLIC PRE *)
  <<< ∀ E, ▷ StackInv γg s E >>>
    push [ #s ; #v] @ tid; ↑N
  <<< ∃ V' E' (psId : event_id) ps Vpush M',
      (* PUBLIC POST *)
      ▷ StackInv γg s E' ∗
      ⊒V' ∗ @{V'} StackLocal N γg s E' M' ∗
      ⌜ Vpush.(dv_in) = V ∧ Vpush.(dv_comm) = V' ∧
        is_push ps v ∧
        psId = length E ∧
        E' = E ++ [mkGraphEvent ps Vpush M'] ∧
        M' = {[psId]} ∪ M ⌝,
      RET #☠, emp >>>
  .

Definition try_pop_spec' {Σ} `{!noprolG Σ, !inG Σ (historyR sevent)}
  (try_pop : val) (StackLocal : StackLocalNT Σ) (StackInv : StackInvT Σ) : Prop :=
  ∀ N (DISJ: N ## histN) (s: loc) tid γg E1 M V,
  (* PRIVATE PRE *)
  ⊒V -∗ StackLocal N γg s E1 M -∗
  (* PUBLIC PRE *)
  <<< ∀ E, ▷ StackInv γg s E >>>
    try_pop [ #s] @ tid; ↑N
  <<< ∃ (v: Z) V' E' (psId ppId : event_id) ps pp Vpp M',
      (* PUBLIC POST *)
      ▷ StackInv γg s E' ∗
      ⊒V' ∗ @{V'} StackLocal N γg s E' M' ∗
      ⌜ Vpp.(dv_in) = V ∧ Vpp.(dv_comm) = V' ⌝ ∗
      ⌜ (* FAIL_RACE case *)
        (v = FAIL_RACE ∧ E' = E ∧ M' = M)
      ∨ (* EMPTY case *)
        ( v = EMPTY ∧ pp = EmpPop ∧
          ppId = length E ∧
          E' = E ++ [mkGraphEvent pp Vpp M'] ∧
          M' = {[ppId]} ∪ M )
      ∨ (* successful case *)
        ( 0 < v ∧ is_push ps v ∧ is_pop pp v ∧ (psId < length E)%nat ∧
          ppId = length E ∧
          E' = E ++ [mkGraphEvent pp Vpp M'] ∧
          ∃ eV, E !! psId = Some eV ∧ eV.(ge_event) = ps ∧
            M' = {[ppId]} ∪ eV.(ge_lview) ∪ M ) ⌝ ,
      RET #v , emp >>>
  .

Definition pop_spec' {Σ} `{!noprolG Σ, !inG Σ (historyR sevent)}
  (pop : val) (StackLocal : StackLocalNT Σ) (StackInv : StackInvT Σ) : Prop :=
  ∀ N (DISJ: N ## histN) (s: loc) tid γg E1 M V,
  (* PRIVATE PRE *)
  ⊒V -∗ StackLocal N γg s E1 M -∗
  (* PUBLIC PRE *)
  <<< ∀ E, ▷ StackInv γg s E >>>
    pop [ #s] @ tid; ↑N
  <<< ∃ (v: Z) V' E' (psId ppId : event_id) ps pp Vpp M',
      (* PUBLIC POST *)
      ▷ StackInv γg s E' ∗
      ⊒V' ∗ @{V'} StackLocal N γg s E' M' ∗
      ⌜ Vpp.(dv_in) = V ∧ Vpp.(dv_comm) = V' ⌝ ∗
      ⌜ (* EMPTY case *)
        ( v = 0 ∧ pp = EmpPop ∧
          ppId = length E ∧
          E' = E ++ [mkGraphEvent pp Vpp M'] ∧
          M' = {[ppId]} ∪ M )
      ∨ (* successful case *)
        ( 0 < v ∧ is_push ps v ∧ is_pop pp v ∧ (psId < length E)%nat ∧
          ppId = length E ∧
          E' = E ++ [mkGraphEvent pp Vpp M'] ∧
          ∃ eV, E !! psId = Some eV ∧ eV.(ge_event) = ps ∧
            M' = {[ppId]} ∪ eV.(ge_lview) ∪ M ) ⌝ ,
      RET #v, emp >>>
  .

Inductive StackLinearizability E : Prop :=
  | StackLinearizability_intro xo lin stk
      (XO : xo = seq 0 (length E))
      (LIN_PERM : lin ≡ₚ xo)
      (XO_LIN_AGREE : filter (not_empty_pop E) lin = filter (not_empty_pop E) xo) (* or Sorted Nat.lt (filter (not_empty_pop E) lin)  *)
      (HB_XO : hb_ord E xo)
      (HB_LIN : hb_ord E lin)
      (INTERP_XO : stack_interp E (filter (not_empty_pop E) xo) [] stk)
      (INTERP_LIN : stack_interp E lin [] stk)
  .

Record stack_spec {Σ} `{!noprolG Σ, !inG Σ (historyR sevent)} := StackSpec {
  (** operations *)
  new_stack : val;
  try_push : val;
  push : val;
  try_pop : val;
  pop : val;

  (** predicates *)
  StackLocal : StackLocalNT Σ;
  StackInv : StackInvT Σ;

  (** predicates properties *)
  StackInv_Objective : ∀ γg s E, Objective (StackInv γg s E);
  StackInv_Timeless : ∀ γg s E, Timeless (StackInv γg s E);
  StackInv_StackLinearizability : ∀ γg s E, StackInv γg s E ⊢ ⌜ StackLinearizability E ⌝;
  StackInv_history_master_acc :
    ∀ γg s E, StackInv γg s E ⊢ history_master γg 1 E ∗
                                      (history_master γg 1 E -∗ StackInv γg s E);
  StackInv_history_snap :
    ∀ γg s E E' M',
      StackInv γg s E -∗ history_snap γg E' M' -∗ ⌜ E' ⊑ E ⌝;

  StackLocal_Persistent :
    ∀ N γg s E M, Persistent (StackLocal N γg s E M);
  StackLocal_history_snap :
    ∀ N γg s E M, StackLocal N γg s E M ⊢ history_snap γg E M;

  (* operations specs *)
  new_stack_spec : new_stack_spec' new_stack StackLocal StackInv;
  try_push_spec : try_push_spec' try_push StackLocal StackInv;
  push_spec : push_spec' push StackLocal StackInv;
  try_pop_spec : try_pop_spec' try_pop StackLocal StackInv;
  pop_spec : pop_spec' pop StackLocal StackInv;
}.

Arguments stack_spec _ {_ _}.
Global Existing Instances StackInv_Objective StackInv_Timeless StackLocal_Persistent.


(** Properties of stack spec *)

Lemma write_xo_stable E1 E2 e (LEN : (e ≤ length E1)%nat) (SubE : E1 ⊑ E2) :
  filter (not_empty_pop E1) (seq 0 e)
  = filter (not_empty_pop E2) (seq 0 e).
Proof.
  destruct SubE as [E ->]. apply list_filter_iff'.
  rewrite Forall_lookup => i e' H.
  apply lookup_lt_Some in H as LT. rewrite seq_length in LT.
  rewrite lookup_xo in H; [|done]. injection H as ->.
  unfold not_empty_pop. split; intros NE eV' EV'.
  - rewrite lookup_app_l in EV'; [|lia]. apply (NE _ EV').
  - have {}EV' : (E1 ++ E) !! e' = Some eV' by eapply prefix_lookup_Some; [done|by exists E].
    apply (NE _ EV').
Qed.

(* TODO: upstream. Also, make [simplify_eq] prefer the "old name" without suffix? *)
Ltac simplify_list_eq2 :=
  repeat match goal with
  | _ => done
  | _ => progress simplify_list_eq
  | H : [] = _ ++ _ :: _ |- _ => apply app_cons_not_nil in H
  | H : [] = _ ++ [_] |- _ => apply nil_snoc in H
  end.

Lemma stack_run_functional e eV stk1 stk21 stk22
    (RUN1 : stack_run e eV stk1 stk21)
    (RUN2 : stack_run e eV stk1 stk22) :
  stk21 = stk22.
Proof.
  inv RUN1; inv RUN2;
    match goal with
    | H1 : eV.(ge_event) = _, H2 : eV.(ge_event) = _ |- _ => rewrite H2 in H1
    end; simplify_eq; done.
Qed.

Lemma stack_interp_functional E ord stk1 stk21 stk22
    (INTERP1 : stack_interp E ord stk1 stk21)
    (INTERP2 : stack_interp E ord stk1 stk22) :
  stk21 = stk22.
Proof.
  move: stk21 stk22 INTERP1 INTERP2. induction ord using rev_ind; intros.
  - inv INTERP1; inv INTERP2; [done|simplify_list_eq2..].
  - inv INTERP1; inv INTERP2; [done|simplify_list_eq2..].
    specialize (IHord _ _ INTERP' INTERP'0) as ->.
    by eapply stack_run_functional.
Qed.

Lemma stack_interp_mono E1 E2 ord stk1 stk2
    (IN : Forall (λ e, ∀ eV, E1 !! e = Some eV → E2 !! e = Some eV) ord)
    (INTERP : stack_interp E1 ord stk1 stk2) :
  stack_interp E2 ord stk1 stk2.
Proof.
  rewrite ->Forall_lookup in IN.
  induction INTERP; [constructor|].
  subst. econstructor; [|done| |done].
  - apply IHINTERP. intros ???.
    eapply IN. eapply prefix_lookup_Some; [done|by eexists].
  - eapply (IN (length ord')); [|done]. apply lookup_app_1_eq.
Qed.

Lemma stack_interp_mono_prefix E1 E2 ord stk1 stk2
    (SubE : E1 ⊑ E2)
    (INTERP : stack_interp E1 ord stk1 stk2) :
  stack_interp E2 ord stk1 stk2.
Proof.
  move: INTERP. apply stack_interp_mono.
  rewrite Forall_lookup. intros. by eapply prefix_lookup_Some.
Qed.

(* todo this is weaker than stack_interp_app *)
Lemma stack_interp_app_inv E ord1 ord2 stk1 stk2
    (INTERP : stack_interp E (ord1 ++ ord2) stk1 stk2) :
  ∃ stk, stack_interp E ord1 stk1 stk ∧ stack_interp E ord2 stk stk2.
Proof.
  generalize dependent stk2.
  induction ord2 using rev_ind; intros.
  { rewrite app_nil_r in INTERP. exists stk2. split; [done|constructor]. }
  inv INTERP. { rewrite app_assoc in H0. apply nil_snoc in H0. done. }
  simplify_list_eq.
  specialize (IHord2 _ INTERP') as [stk [? ?]].
  exists stk. split; [done|by econstructor].
Qed.

Lemma stack_node_ids E ord stk
    (INTERP : stack_interp E ord [] stk)
    (ORD_NODUP : NoDup ord) :
  « NODE_NODUP : NoDup stk.*1.*1.*1 » ∧
  « NODE_INCL : stk.*1.*1.*1 ⊆ ord » .
Proof.
  remember [] as stk' in INTERP.
  induction INTERP. { subst. by unnw. }
  subst. apply NoDup_app in ORD_NODUP as (ORD_NODUP & NE & _).
  specialize (IHINTERP eq_refl ORD_NODUP). des.
  inv RUN.
  - rewrite !fmap_cons /=. split; red.
    + constructor; [set_solver|done].
    + set_solver.
  - split; red.
    + rewrite !fmap_cons /= in NODE_NODUP. by inv NODE_NODUP.
    + set_solver.
  - simpl. split; red; [done|set_solver].
Qed.

Lemma stack_node_pushed_inv E node ord stk1 stk2
    (INTERP : stack_interp E ord [] (stk1 ++ node :: stk2))
    (ORD_NODUP : NoDup ord) :
  ∃ uV,
    « ID : node.1.1.1 ∈ ord » ∧
    « EV : E !! node.1.1.1 = Some uV » ∧
    « PUSH_VAL : uV.(ge_event) = Push node.1.1.2 » ∧
    « PUSH_VAL_NZ : 0 < node.1.1.2 » ∧
    « PUSH_LVIEW : uV.(ge_lview) = node.2 » ∧
    « PUSH_VIEW : uV.(ge_view).(dv_comm) = node.1.2 ».
Proof.
  elim/rev_ind: ord stk1 stk2 INTERP ORD_NODUP.
  { intros. inv INTERP; simplify_list_eq2. }
  intros e ord IH ????. set (u := node.1.1.1) in *.
  inv INTERP; simplify_list_eq2. rename e0 into e.
  apply NoDup_app in ORD_NODUP as (ORD_NODUP' & NOT_IN & _).
  case (decide (u = e)) as [<-|NE].
  - (* the last event pushed [node] *) inv RUN; simplify_list_eq2.
    + (* push *) destruct stk1; last first.
      { (* no duplicate push id *) exfalso. simplify_list_eq.
        exploit stack_node_ids; [done..|].
        rewrite !fmap_app !fmap_cons /=. i. des. set_solver. }
      apply eq_sym in H3 as Hnode; clear H3. simplify_list_eq.
      rewrite H /=. exists eV.
      split_and!; red; [set_solver|done..].
    + (* pop *) specialize (IH (_ :: stk1) _ INTERP' ORD_NODUP'). des.
      exists uV. split_and!; red; set_solver.
  - inv RUN; simpl in *; simplify_list_eq2.
    + case Estk1: stk1 => [|? stk1']; simplify_list_eq.
      specialize (IH _ _ INTERP' ORD_NODUP'). des.
      exists uV. split_and!; red; [set_solver|done..].
    + specialize (IH (_ :: stk1) _ INTERP' ORD_NODUP'). des.
      exists uV. split_and!; red; [set_solver|done..].
Qed.

Lemma stack_interp_nil_inv E stk stk'
    (INTERP: stack_interp E [] stk stk'):
  stk' = stk.
Proof.
  inversion INTERP; auto; subst.
  destruct ord'; simpl in ORD; inversion ORD.
Qed.

Lemma stack_interp_snoc_inv E ord e stk stk'
    (INTERP: stack_interp E (ord ++ [e]) stk stk'):
  ∃ eV midstk,
    stack_interp E ord stk midstk ∧
    E !! e = Some eV ∧
    stack_run e eV midstk stk'.
Proof.
  inversion INTERP; subst.
  { destruct ord; simpl in H0; inversion H0. }
  apply app_inj_tail in ORD as [O1 O2]; subst.
  by exists eV, stk2.
Qed.

Lemma stack_interp_app E ord1 ord2 stk stk':
  stack_interp E (ord1 ++ ord2) stk stk' ↔
  ∃ midstk,
    stack_interp E ord1 stk midstk ∧
    stack_interp E ord2 midstk stk'.
Proof.
  split; intros.
  - revert stk' H.
    induction ord2 using rev_ind; intros.
    + rewrite app_nil_r in H.
      exists stk'; split; auto. constructor.
    + rewrite app_assoc in H.
      apply stack_interp_snoc_inv in H; des.
      apply IHord2 in H; des.
      exists midstk0; split; auto.
      by apply (stack_interp_snoc _ x eV _ ord2 _ midstk _).
  - des. revert stk' H H0.
    induction ord2 using rev_ind; intros.
    + rewrite app_nil_r.
      apply stack_interp_nil_inv in H0; by subst.
    + apply stack_interp_snoc_inv in H0; des.
      apply (IHord2 midstk0) in H; auto.
      rewrite app_assoc.
      by apply (stack_interp_snoc _ x eV _ (ord1 ++ ord2) _ midstk0 _).
Qed.

Lemma stack_interp_prefix_rev E E' ord stk stk'
    (INTERP: stack_interp E' ord stk stk')
    (PREFIX: E ⊑ E')
    (ORD: Forall (λ e, e < (length E))%nat ord) :
  stack_interp E ord stk stk'.
Proof.
  eapply (stack_interp_mono E'); auto.
  apply Forall_forall; intros.
  apply (prefix_lookup_inv _ E'); auto.
  rewrite -> Forall_forall in ORD; apply ORD in H.
  by apply lookup_lt_is_Some.
Qed.

(** Properties of write_xo *)

Lemma write_xo_nil : write_xo [] = [].
Proof.
  unfold write_xo; simpl. apply filter_nil.
Qed.

Lemma write_xo_snoc_e E eV
    (HE: eV.(ge_event) = EmpPop) :
  write_xo (E ++ [eV]) = write_xo E.
Proof.
  unfold write_xo. rewrite app_length seq_app filter_app.
  rewrite filter_cons_False; last first. {
    unfold not, not_empty_pop; intros.
    specialize (H eV). rewrite lookup_app_1_eq in H.
    by apply H.
  }
  rewrite filter_nil app_nil_r.
  rewrite (write_xo_stable E (E ++ [eV])); auto.
  by apply prefix_app_r.
Qed.

Lemma write_xo_snoc_ne E eV
    (HNE: eV.(ge_event) ≠ EmpPop) :
  write_xo (E ++ [eV]) = write_xo E ++ [length E].
Proof.
  unfold write_xo. rewrite app_length seq_app filter_app.
  rewrite filter_cons_True; last first. {
    unfold not_empty_pop; intros.
    rewrite lookup_app_1_eq in EV. by inv EV.
  }
  rewrite filter_nil.
  rewrite (write_xo_stable E (E ++ [eV])); auto.
  by apply prefix_app_r.
Qed.

Lemma stack_interp_write_xo E1 E2 stk
    (XO_INTERP : stack_interp E2 (write_xo E1) [] stk)
    (PREFIX : E1 ⊑ E2):
  stack_interp E1 (write_xo E1) [] stk.
Proof.
  apply (stack_interp_prefix_rev _ E2); auto.
  apply Forall_filter. apply Forall_seq; lia.
Qed.
