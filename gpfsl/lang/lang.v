From stdpp Require Export binders strings.
From iris.program_logic Require Export language ectx_language ectxi_language.
From iris.algebra Require Import ofe.

From orc11 Require Export progress.

Require Import iris.prelude.options.

(* Note: We consider that reading uninitialized memory can return poison.
   This is not what Rust does, but LLVM considers that reading
   from undefined memory returns the undef value.

   https://doc.rust-lang.org/std/mem/fn.uninitialized.html#undefined-behavior
*)

(** Locations **)
Notation loc := lblock.

Declare Scope loc_scope.
Bind Scope loc_scope with loc.
Delimit Scope loc_scope with L.
Open Scope loc_scope.

Open Scope Z_scope.

(** Literals **)
Inductive lit := | LitPoison | LitLoc (l : loc) | LitInt (n : Z).

Global Instance lit_inhabited : Inhabited lit := populate LitPoison.

(** Expressions and values. *)

Inductive un_op := | NegOp | MinusUnOp.

Inductive bin_op := | PlusOp | MinusOp | MultOp | QuotOp | DivOp | RemOp | ModOp | LeOp | LtOp | EqOp | OffsetOp.

Module base.
  (** Base expression language without views *)
  Inductive expr :=
  (* Basic lambda calculus *)
  | Var (x : string)
  | Rec (f : binder) (xl : list binder) (e : expr)
  | App (e : expr) (el : list expr)
  (* Basic operations *)
  | Lit (l : lit)
  | UnOp (op : un_op) (e: expr)
  | BinOp (op : bin_op) (e1 e2 : expr)
  | Case (e : expr) (el : list expr)
  (* Concurrency *)
  | Fork (e : expr)
  (* Memory *)
  | Read (o : memOrder) (e : expr)
  | Write (o : memOrder) (e1 e2: expr)
  | CAS (e0 e1 e2 : expr) (orf or ow: memOrder)
  | FenceAcq
  | FenceRel
  | FenceSC
  | Alloc (e : expr)
  | Free (e1 e2 : expr).

  Bind Scope expr_scope with expr.
  Delimit Scope expr_scope with E.

  Arguments Rec _ _ _%E.
  Arguments App _%E _%E.
  Arguments UnOp _ _%E.
  Arguments BinOp _ _%E _%E.
  Arguments Case _%E _%E.
  Arguments Fork _%E.
  Arguments Read _ _%E.
  Arguments Write _ _%E _%E.
  Arguments CAS _%E _%E _%E _ _.
  Arguments Alloc _%E.
  Arguments Free _%E _%E.

  Fixpoint is_closed (X : list string) (e : expr) : bool :=
    match e with
    | Var x => bool_decide (x ∈ X)
    | Lit _ | FenceAcq | FenceRel | FenceSC => true
    | Rec f xl e => is_closed (f :b: xl +b+ X) e
    | BinOp _ e1 e2 | Write _ e1 e2 | Free e1 e2 => is_closed X e1 && is_closed X e2
    | App e el | Case e el => is_closed X e && forallb (is_closed X) el
    | UnOp _ e | Read _ e | Fork e | Alloc e => is_closed X e
    | CAS e0 e1 e2 _ _ _ => is_closed X e0 && is_closed X e1 && is_closed X e2
    end.

  Class Closed (X : list string) (e : expr) := closed : is_closed X e.
  Global Instance closed_proof_irrel env e : ProofIrrel (Closed env e).
  Proof. rewrite /Closed. apply _. Qed.
  Global Instance closed_decision env e : Decision (Closed env e).
  Proof. rewrite /Closed. apply _. Qed.

  Inductive val :=
  | LitV (l : lit)
  | RecV (f : binder) (xl : list binder) (e : expr) `{Closed (f :b: xl +b+ []) e}.

  Bind Scope val_scope with val.
  Delimit Scope val_scope with V.

  Definition of_val (v : val) : expr :=
    match v with
    | RecV f x e => Rec f x e
    | LitV l => Lit l
    end.

  Definition to_val (e : expr) : option val :=
    match e with
    | Rec f xl e =>
      if decide (Closed (f :b: xl +b+ []) e) then Some (RecV f xl e) else None
    | Lit l => Some (LitV l)
    | _ => None
    end.

  (** Evaluation contexts *)
  Inductive ectx_item :=
  | UnOpCtx (op : un_op)
  | BinOpLCtx (op : bin_op) (e2 : expr)
  | BinOpRCtx (op : bin_op) (v1 : val)
  | AppLCtx (e2 : list expr)
  | AppRCtx (v : val) (vl : list val) (el : list expr)
  | ReadCtx (o : memOrder)
  | WriteLCtx (o : memOrder) (e2 : expr)
  | WriteRCtx (o : memOrder) (v1 : val)
  | CasLCtx (orf or ow : memOrder) (e1 e2: expr)
  | CasMCtx (orf or ow : memOrder) (v0 : val) (e2 : expr)
  | CasRCtx (orf or ow : memOrder) (v0 : val) (v1 : val)
  | AllocCtx
  | FreeLCtx (e2 : expr)
  | FreeRCtx (v1 : val)
  | CaseCtx (el : list expr).

  Definition fill_item (Ki : ectx_item) (e : expr) : expr :=
    match Ki with
    | UnOpCtx op => UnOp op e
    | BinOpLCtx op e2 => BinOp op e e2
    | BinOpRCtx op v1 => BinOp op (of_val v1) e
    | AppLCtx e2 => App e e2
    | AppRCtx v vl el => App (of_val v) ((of_val <$> vl) ++ e :: el)
    | ReadCtx o => Read o e
    | WriteLCtx o e2 => Write o e e2
    | WriteRCtx o v1 => Write o (of_val v1) e
    | CasLCtx orf or ow e1 e2 => CAS e e1 e2 orf or ow
    | CasMCtx orf or ow v0 e2 => CAS (of_val v0) e e2 orf or ow
    | CasRCtx orf or ow v0 v1 => CAS (of_val v0) (of_val v1) e orf or ow
    | AllocCtx => Alloc e
    | FreeLCtx e2 => Free e e2
    | FreeRCtx v1 => Free (of_val v1) e
    | CaseCtx el => Case e el
    end.

  Definition fill (K : list ectx_item) (e : expr) : expr := foldl (flip fill_item) e K.

  (** Substitution *)
  Fixpoint subst (x : string) (es : expr) (e : expr) : expr :=
    match e with
    | Var y => if bool_decide (y = x) then es else Var y
    | Lit l => Lit l
    | Rec f xl e =>
      Rec f xl $ if bool_decide (BNamed x ≠ f ∧ BNamed x ∉ xl) then subst x es e else e
    | UnOp op e => UnOp op (subst x es e)
    | BinOp op e1 e2 => BinOp op (subst x es e1) (subst x es e2)
    | App e el => App (subst x es e) (map (subst x es) el)
    | Read o e => Read o (subst x es e)
    | Write o e1 e2 => Write o (subst x es e1) (subst x es e2)
    | CAS e0 e1 e2 orf or ow => CAS (subst x es e0) (subst x es e1) (subst x es e2) orf or ow
    | Case e el => Case (subst x es e) (map (subst x es) el)
    | Fork e => Fork (subst x es e)
    | Alloc e => Alloc (subst x es e)
    | Free e1 e2 => Free (subst x es e1) (subst x es e2)
    | FenceAcq => FenceAcq
    | FenceRel => FenceRel
    | FenceSC => FenceSC
    end.

  Definition subst' (mx : binder) (es : expr) : expr → expr :=
    match mx with BNamed x => subst x es | BAnon => id end.

  Fixpoint subst_l (xl : list binder) (esl : list expr) (e : expr) : option expr :=
    match xl, esl with
    | [], [] => Some e
    | x::xl, es::esl => subst' x es <$> subst_l xl esl e
    | _, _ => None
    end.

  Arguments subst_l _%binder _ _%E.

  Definition subst_v (xl : list binder) (vsl : vec val (length xl))
                     (e : expr) : expr :=
    Vector.fold_right2 (λ b, subst' b ∘ of_val) e _ (list_to_vec xl) vsl.
  Arguments subst_v _%binder _ _%E.

  Lemma subst_v_eq (xl : list binder) (vsl : vec val (length xl)) e :
    Some $ subst_v xl vsl e = subst_l xl (of_val <$> vec_to_list vsl) e.
  Proof.
    revert vsl. induction xl=>/= vsl; inv_vec vsl=>//=v vsl. by rewrite -IHxl.
  Qed.

  (** The stepping relation *)
  (* Be careful to make sure that poison is always stuck when used for anything
     except for reading from or writing to memory! *)

  Definition Z_of_bool (b : bool) : Z :=
    if b then 1 else 0.

  Definition lit_of_bool (b : bool) : lit :=
    LitInt $ Z_of_bool b.

  Inductive un_op_eval : un_op → lit → lit → Prop :=
  | UnOpNeg z :
      un_op_eval NegOp (LitInt z) (lit_of_bool $ bool_decide (z = 0))
  | UnOpMinus z :
      un_op_eval MinusUnOp (LitInt z) (LitInt (-z)).

  Notation memory := (@memory loc lblock_loc val).
  Notation event := (@event loc val).

  Implicit Type (M: memory).

  Inductive lit_eq M : lit → lit → Prop :=
  (* No refl case for poison *)
  | IntRefl z : lit_eq M (LitInt z) (LitInt z)
  | LocRefl l : lit_eq M (LitLoc l) (LitLoc l).

  Inductive lit_neq : lit → lit → Prop :=
  | IntNeq z1 z2 :
      z1 ≠ z2 → lit_neq (LitInt z1) (LitInt z2)
  | LocNeq l1 l2 :
      l1 ≠ l2 → lit_neq (LitLoc l1) (LitLoc l2)
  | LocNeqNullR z l :
      lit_neq (LitLoc l) (LitInt z)
  | LocNeqNullL z l :
      lit_neq (LitInt z) (LitLoc l).

  (* Condition for non-UB comparison *)
  Inductive lit_comparable : lit → lit → Prop :=
  | IntComp z1 z2 : lit_comparable (LitInt z1) (LitInt z2)
  | LocComp l1 l2 : lit_comparable (LitLoc l1) (LitLoc l2)
  | LocIntComp z l  : lit_comparable (LitLoc l) (LitInt z)
  | IntLocComp z l  : lit_comparable (LitInt z) (LitLoc l).

  Lemma lit_comparable_spec M l1 l2 :
    lit_comparable l1 l2 ↔ lit_eq M l1 l2 ∨ lit_neq l1 l2.
  Proof.
    intros. split=>[|[]]; inversion 1; subst; try by constructor.
    - destruct (decide (z1 = z2)) as [->|]; [left|right]; by constructor.
    - destruct (decide (l0 = l3)) as [->|]; [left|right]; by constructor.
    - right. constructor.
    - right. constructor.
  Qed.

  (* No reduction for poison *)
  Inductive bin_op_eval M : bin_op → lit → lit → lit → Prop :=
  | BinOpPlus z1 z2 :
      bin_op_eval M PlusOp (LitInt z1) (LitInt z2) (LitInt (z1 + z2))
  | BinOpMinus z1 z2 :
      bin_op_eval M MinusOp (LitInt z1) (LitInt z2) (LitInt (z1 - z2))
  | BinOpMult z1 z2 :
      bin_op_eval M MultOp (LitInt z1) (LitInt z2) (LitInt (z1 * z2))
  | BinOpQuot z1 z2 :
      bin_op_eval M QuotOp (LitInt z1) (LitInt z2) (LitInt (z1 `quot` z2))
  | BinOpDiv z1 z2 :
      bin_op_eval M DivOp (LitInt z1) (LitInt z2) (LitInt (z1 `div` z2))
  | BinOpRem z1 z2 :
      bin_op_eval M RemOp (LitInt z1) (LitInt z2) (LitInt (z1 `rem` z2))
  | BinOpMod z1 z2 :
      bin_op_eval M ModOp (LitInt z1) (LitInt z2) (LitInt (z1 `mod` z2))
  | BinOpLe z1 z2 :
      bin_op_eval M LeOp (LitInt z1) (LitInt z2) (lit_of_bool $ bool_decide (z1 ≤ z2))
  | BinOpLt z1 z2 :
      bin_op_eval M LtOp (LitInt z1) (LitInt z2) (lit_of_bool $ bool_decide (z1 < z2))
  | BinOpEqTrue l1 l2 :
      lit_eq M l1 l2 → bin_op_eval M EqOp l1 l2 (lit_of_bool true)
  | BinOpEqFalse l1 l2 :
      lit_neq l1 l2 → bin_op_eval M EqOp l1 l2 (lit_of_bool false)
  | BinOpOffset l z :
      bin_op_eval M OffsetOp (LitLoc l) (LitInt z) (LitLoc $ l >> Z.to_nat z).

  (* turn AVal to poison *)
  Inductive memval_val_rel : value.val → val → Prop :=
  | memval_val_VVal v : memval_val_rel (VVal v) v
  | memval_val_AVal : memval_val_rel AVal (LitV LitPoison).

  Inductive head_step M 𝓥 : expr → option event → expr → list expr → Prop :=
  | BetaS f xl e e' el:
      Forall (λ ei, is_Some (to_val ei)) el →
      Closed (f :b: xl +b+ []) e →
      subst_l (f::xl) (Rec f xl e :: el) e = Some e' →
      head_step M 𝓥 (App (Rec f xl e) el)
                  None
                  e'
                  []
  | UnOpS op l l' :
      un_op_eval op l l' →
      head_step M 𝓥 (UnOp op (Lit l))
                  None
                  (Lit l')
                  []
  | BinOpS op l1 l2 l' :
      bin_op_eval M op l1 l2 l' →
      head_step M 𝓥 (BinOp op (Lit l1) (Lit l2))
                  None
                  (Lit l')
                  []
  | CaseS i el e :
      0 ≤ i →
      el !! (Z.to_nat i) = Some e →
      head_step M 𝓥 (Case (Lit $ LitInt i) el)
                  None
                  e
                  []
  | ForkS e :
      head_step M 𝓥 (Fork e)
                  None
                  (Lit LitPoison)
                  [e]
  | AllocS n l:
      0 < n →
      head_step M 𝓥 (Alloc $ Lit $ LitInt n)
                  (Some $ event.Alloc l (Z.to_pos n))
                  (Lit $ LitLoc l)
                  []
  | FreeS n (l : loc) :
      0 < n →
      head_step M 𝓥 (Free (Lit $ LitInt n) (Lit $ LitLoc l))
                  (Some $ Dealloc l (Z.to_pos n))
                  (Lit LitPoison)
                  []
  | ReadS (l : loc) (v: value.val) vr o :
      memval_val_rel v vr →
      head_step M 𝓥 (Read o (Lit $ LitLoc l))
                  (Some $ event.Read l v o)
                  (of_val vr)
                  []
  | WriteS (l : loc) e v o :
      to_val e = Some v →
      head_step M 𝓥 (Write o (Lit $ LitLoc l) e)
                  (Some $ event.Write l v o)
                  (Lit LitPoison)
                  []
  | CasFailS (l : loc) e1 lit1 e2 v2 lito orf or ow:
      (* no plain CASes allowed *)
      (* C/Rust CAS takes a pair of success/failure modes, which effectively
        mean 3 access modes:
         - orf for reading in the failure case
         - or and ow for reading and writing, respectively, in the success case
         C11 maintains that orf ⊑ or, but this is dropped in C17. *)
      (* FIXME: C's CAS returns boolean, but Rust's CAS also returns the read value
         in addition to the boolean *)
      Relaxed ⊑ orf → Relaxed ⊑ or → Relaxed ⊑ ow →
      to_val e1 = Some $ LitV lit1 → to_val e2 = Some $ v2 →
      lit_neq lit1 lito →
      (* all readable values must be comparable *)
      (∀ t m, M !! (l,t) = Some m → 𝓥.(cur) !!w l ⊑ Some t
          → ∃ v, memval_val_rel m.(mval) (LitV v) ∧ lit_comparable lit1 v) →
      head_step M 𝓥 (CAS (Lit $ LitLoc l) e1 e2 orf or ow)
                  (Some $ event.Read l (VVal $ LitV lito) orf)
                  (Lit $ lit_of_bool false)
                  []
  | CasSucS (l : loc) e1 lit1 e2 v2 lito orf or ow:
      Relaxed ⊑ orf → Relaxed ⊑ or → Relaxed ⊑ ow →
      to_val e1 = Some $ LitV lit1 → to_val e2 = Some v2 →
      lit_eq M lit1 lito →
      (* all readable values must be comparable *)
      (∀ t m, M !! (l,t) = Some m → 𝓥.(cur) !!w l ⊑ Some t
          → ∃ v, memval_val_rel m.(mval) (LitV v) ∧ lit_comparable lit1 v) →
      head_step M 𝓥 (CAS (Lit $ LitLoc l) e1 e2 orf or ow)
                  (Some $ event.Update l (LitV lito) v2 or ow)
                  (Lit $ lit_of_bool true)
                  []
  | FAcqS :
      head_step M 𝓥 (FenceAcq)
                  (Some $ Fence AcqRel Relaxed)
                  (Lit LitPoison)
                  []
  | FRelS :
      head_step M 𝓥 (FenceRel)
                  (Some $ Fence Relaxed AcqRel)
                  (Lit LitPoison)
                  []
  | FSCS :
      head_step M 𝓥 (FenceSC)
                  (Some $ Fence SeqCst SeqCst)
                  (Lit LitPoison)
                  []
  .

  (** Basic properties about the language *)

  Lemma to_of_val v : to_val (of_val v) = Some v.
  Proof.
    by induction v; simplify_option_eq; repeat f_equal; try apply (proof_irrel _).
  Qed.

  Lemma of_to_val e v : to_val e = Some v → of_val v = e.
  Proof.
    revert v; induction e; intros v ?; simplify_option_eq; auto with f_equal.
  Qed.

  Global Instance of_val_inj : Inj (=) (=) of_val.
  Proof. by intros ?? Hv; apply (inj Some); rewrite -!to_of_val Hv. Qed.

  Global Instance fill_item_inj Ki : Inj (=) (=) (fill_item Ki).
  Proof. destruct Ki; intros ???; simplify_eq/=; auto with f_equal. Qed.

  Lemma fill_item_val Ki e :
    is_Some (to_val (fill_item Ki e)) → is_Some (to_val e).
  Proof. intros [v ?]. destruct Ki; simplify_option_eq; eauto. Qed.

  Lemma val_stuck M 𝓥 e1 evt e2 efs :
    head_step M 𝓥 e1 evt e2 efs → to_val e1 = None.
  Proof. destruct 1; naive_solver. Qed.

  Lemma head_ctx_step_val M 𝓥 Ki e evt e2 efs :
    head_step M 𝓥 (fill_item Ki e) evt e2 efs → is_Some (to_val e).
  Proof.
    destruct Ki; inversion_clear 1; decompose_Forall_hyps;
    simplify_option_eq; by eauto.
  Qed.

  Lemma list_expr_val_eq_inv vl1 vl2 e1 e2 el1 el2 :
    to_val e1 = None → to_val e2 = None →
    map of_val vl1 ++ e1 :: el1 = map of_val vl2 ++ e2 :: el2 →
    vl1 = vl2 ∧ el1 = el2.
  Proof.
    revert vl2; induction vl1; destruct vl2; intros H1 H2; inversion 1.
    - done.
    - subst. by rewrite to_of_val in H1.
    - subst. by rewrite to_of_val in H2.
    - destruct (IHvl1 vl2); auto. split; f_equal; auto. by apply (inj of_val).
  Qed.

  Lemma fill_item_no_val_inj Ki1 Ki2 e1 e2 :
    to_val e1 = None → to_val e2 = None →
    fill_item Ki1 e1 = fill_item Ki2 e2 → Ki1 = Ki2.
  Proof.
    destruct Ki1 as [| | | |v1 vl1 el1| | | | | | | | | |],
             Ki2 as [| | | |v2 vl2 el2| | | | | | | | | |];
    intros He1 He2 EQ; try discriminate; simplify_eq/=;
      repeat match goal with
      | H : to_val (of_val _) = None |- _ => by rewrite to_of_val in H
      end; auto.
    destruct (list_expr_val_eq_inv vl1 vl2 e1 e2 el1 el2); auto. congruence.
  Qed.

  (* Lemmas we don't get for free because we are not an Iris language. *)
  Lemma as_val_is_Some e :
    (∃ v : base.val, base.of_val v = e) → is_Some (base.to_val e).
  Proof. intros [v <-]. rewrite base.to_of_val. eauto. Qed.

  (** Closed expressions *)
  Lemma is_closed_weaken X Y e : is_closed X e → X ⊆ Y → is_closed Y e.
  Proof.
    revert e X Y. fix FIX 1; destruct e=>X Y/=; try naive_solver.
    - naive_solver set_solver.
    - rewrite !andb_True. intros [He Hel] HXY. split; first by eauto.
      induction el=>/=; naive_solver.
    - rewrite !andb_True. intros [He Hel] HXY. split; first by eauto.
      induction el=>/=; naive_solver.
  Qed.

  Lemma is_closed_weaken_nil X e : is_closed [] e → is_closed X e.
  Proof. intros. by apply is_closed_weaken with [], list_subseteq_nil. Qed.

  Lemma is_closed_subst X e x es : is_closed X e → x ∉ X → subst x es e = e.
  Proof.
    revert e X. fix FIX 1; destruct e=> X /=; rewrite ?bool_decide_spec ?andb_True=> He ?;
      repeat case_bool_decide; simplify_eq/=; f_equal;
      try by intuition eauto with set_solver.
    - case He=> _. clear He. induction el=>//=. rewrite andb_True=>?.
      f_equal; intuition eauto with set_solver.
    - case He=> _. clear He. induction el=>//=. rewrite andb_True=>?.
      f_equal; intuition eauto with set_solver.
  Qed.

  Lemma is_closed_nil_subst e x es : is_closed [] e → subst x es e = e.
  Proof. intros. apply is_closed_subst with []; set_solver. Qed.

  Lemma is_closed_of_val X v : is_closed X (of_val v).
  Proof. apply is_closed_weaken_nil. induction v; simpl; auto. Qed.

  Lemma subst_is_closed X x es e :
    is_closed X es → is_closed (x::X) e → is_closed X (subst x es e).
  Proof.
    revert e X. fix FIX 1; destruct e=>X //=; repeat (case_bool_decide=>//=);
      try naive_solver; rewrite ?andb_True; intros.
    - set_solver.
    - eauto using is_closed_weaken with set_solver.
    - eapply is_closed_weaken; first done.
      destruct (decide (BNamed x = f)), (decide (BNamed x ∈ xl)); set_solver.
    - split; first naive_solver. induction el; naive_solver.
    - split; first naive_solver. induction el; naive_solver.
  Qed.

  Lemma subst'_is_closed X b es e :
    is_closed X es → is_closed (b:b:X) e → is_closed X (subst' b es e).
  Proof. destruct b; first done. apply subst_is_closed. Qed.

  (** Equality and other typeclass stuff *)
  Global Instance bin_op_dec_eq : EqDecision bin_op.
  Proof. solve_decision. Defined.
  Global Instance bin_op_countable : Countable bin_op.
  Proof.
    refine (inj_countable'
      (λ o, match o with PlusOp => 0 | MinusOp => 1 | LeOp => 2 |
                    LtOp => 3 | EqOp => 4 | OffsetOp => 5 | ModOp => 6 | DivOp => 7 | MultOp => 8 | QuotOp => 9 | RemOp => 10 end)
      (λ x, match x with 0 => PlusOp | 1 => MinusOp | 2 => LeOp |
                    3 => LtOp | 4 => EqOp | 5 => OffsetOp | 6 => ModOp | 7 => DivOp | 8 => MultOp | 9 => QuotOp | _ => RemOp end) _);
    by intros [].
  Qed.
  Global Instance un_op_dec_eq : EqDecision un_op.
  Proof. solve_decision. Defined.
  Global Instance un_op_countable : Countable un_op.
  Proof.
    refine (inj_countable'
      (λ o, match o with NegOp => true | MinusUnOp => false end)
      (λ x, match x with true => NegOp | false => MinusUnOp end) _); by intros [].
  Qed.

  Global Instance lit_dec_eq : EqDecision lit.
  Proof. solve_decision. Defined.
  Global Instance lit_countable : Countable lit.
  Proof.
    refine (inj_countable
      (λ v, match v with
          | LitPoison => inl ()
          | LitLoc l => inr (inl l)
          | LitInt n => inr (inr n)
          end)
      (λ s, match s with
          | inl () => Some LitPoison
          | inr (inl l) => Some $ LitLoc l
          | inr (inr n) => Some $ LitInt n
          end) _); by intros [].
  Qed.

  Fixpoint expr_beq (e : expr) (e' : expr) : bool :=
    let fix expr_list_beq el el' :=
      match el, el' with
      | [], [] => true
      | eh::eq, eh'::eq' => expr_beq eh eh' && expr_list_beq eq eq'
      | _, _ => false
      end
    in
    match e, e' with
    | Var x, Var x' => bool_decide (x = x')
    | Lit l, Lit l' => bool_decide (l = l')
    | Rec f xl e, Rec f' xl' e' =>
      bool_decide (f = f') && bool_decide (xl = xl') && expr_beq e e'
    | UnOp op e, UnOp op' e' =>
      bool_decide (op = op') && expr_beq e e'
    | BinOp op e1 e2, BinOp op' e1' e2' =>
      bool_decide (op = op') && expr_beq e1 e1' && expr_beq e2 e2'
    | App e el, App e' el' | Case e el, Case e' el' =>
      expr_beq e e' && expr_list_beq el el'
    | Read o e, Read o' e' => bool_decide (o = o') && expr_beq e e'
    | Write o e1 e2, Write o' e1' e2' =>
      bool_decide (o = o') && expr_beq e1 e1' && expr_beq e2 e2'
    | CAS e0 e1 e2 orf or ow, CAS e0' e1' e2' orf' or' ow' =>
      bool_decide (orf = orf') && bool_decide (or = or') && bool_decide (ow = ow') &&
      expr_beq e0 e0' && expr_beq e1 e1' && expr_beq e2 e2'
    | Fork e, Fork e' | Alloc e, Alloc e' => expr_beq e e'
    | Free e1 e2, Free e1' e2' => expr_beq e1 e1' && expr_beq e2 e2'
    | FenceAcq, FenceAcq | FenceRel, FenceRel | FenceSC, FenceSC => true
    | _, _ => false
    end.

  Lemma expr_beq_correct (e1 e2 : expr) : expr_beq e1 e2 ↔ e1 = e2.
  Proof.
    revert e1 e2; fix FIX 1;
      destruct e1 as [| |? el1| | | |? el1| | | | | | | | |],
               e2 as [| |? el2| | | |? el2| | | | | | | | |]; simpl; try done;
    rewrite ?andb_True ?bool_decide_spec ?FIX;
    try (split; intro; [destruct_and?|split_and?]; congruence).
    - match goal with |- context [?F el1 el2] => assert (F el1 el2 ↔ el1 = el2) end.
      { revert el2. induction el1 as [|el1h el1q]; destruct el2; try done.
        specialize (FIX el1h). naive_solver. }
      clear FIX. naive_solver.
    - match goal with |- context [?F el1 el2] => assert (F el1 el2 ↔ el1 = el2) end.
      { revert el2. induction el1 as [|el1h el1q]; destruct el2; try done.
        specialize (FIX el1h). naive_solver. }
      clear FIX. naive_solver.
  Qed.

  Global Instance expr_inhabited : Inhabited expr := populate (Lit LitPoison).
  Global Instance expr_dec_eq : EqDecision expr.
  Proof.
    refine (λ e1 e2, cast_if (decide (expr_beq e1 e2))); by rewrite -expr_beq_correct.
  Defined.

  Global Instance expr_countable : Countable expr.
  Proof.
    refine (inj_countable'
      (fix go e := match e with
       | Var x => GenNode 0 [GenLeaf $ inl $ inl $ inl x]
       | Rec f xl e => GenNode 1 [GenLeaf $ inl $ inl $ inr f;
                                  GenLeaf $ inl $ inr $ inl xl; go e]
       | App e el => GenNode 2 (go e :: (go <$> el))
       | Lit l => GenNode 3 [GenLeaf $ inl $ inr $ inr l]
       | UnOp op e => GenNode 4 [GenLeaf $ inr $ inl $ inl op; go e]
       | BinOp op e1 e2 => GenNode 5 [GenLeaf $ inr $ inl $ inr op; go e1; go e2]
       | Case e el => GenNode 6 (go e :: (go <$> el))
       | Fork e => GenNode 7 [go e]
       | Read o e => GenNode 8 [GenLeaf $ inr $ inr o; go e]
       | Write o e1 e2 => GenNode 9 [GenLeaf $ inr $ inr o; go e1; go e2]
       | CAS e0 e1 e2 orf or ow =>
         GenNode 10 [go e0; go e1; go e2; GenLeaf $ inr $ inr orf;
                                          GenLeaf $ inr $ inr or;
                                          GenLeaf $ inr $ inr ow]
       | FenceAcq => GenNode 11 []
       | FenceRel => GenNode 12 []
       | FenceSC => GenNode 13 []
       | Alloc e => GenNode 14 [go e]
       | Free e1 e2 => GenNode 15 [go e1; go e2]
       end)
      (fix go t := match t with
       | GenNode 0 [GenLeaf (inl (inl (inl x)))] => Var x
       | GenNode 1 [GenLeaf (inl (inl (inr f)));
                    GenLeaf (inl (inr (inl xl))); e] => Rec f xl (go e)
       | GenNode 2 (e :: el) => App (go e) (go <$> el)
       | GenNode 3 [GenLeaf (inl (inr (inr l)))] => Lit l
       | GenNode 4 [GenLeaf (inr (inl (inl op))); e] => UnOp op (go e)
       | GenNode 5 [GenLeaf (inr (inl (inr op))); e1; e2] => BinOp op (go e1) (go e2)
       | GenNode 6 (e :: el) => Case (go e) (go <$> el)
       | GenNode 7 [e] => Fork (go e)
       | GenNode 8 [GenLeaf (inr (inr o)); e] => Read o (go e)
       | GenNode 9 [GenLeaf (inr (inr o)); e1; e2] => Write o (go e1) (go e2)
       | GenNode 10 [e0; e1; e2; GenLeaf (inr (inr orf));
                     GenLeaf (inr (inr or)); GenLeaf (inr (inr ow))] =>
         CAS (go e0) (go e1) (go e2) orf or ow
       | GenNode 11 [] => FenceAcq
       | GenNode 12 [] => FenceRel
       | GenNode 13 [] => FenceSC
       | GenNode 14 [e] => Alloc (go e)
       | GenNode 15 [e1; e2] => Free (go e1) (go e2)
       | _ => Lit LitPoison
       end) _).
    fix FIX 1. intros []; f_equal=>//; revert el; clear -FIX.
    - fix FIX_INNER 1. intros []; [done|]. by simpl; f_equal.
    - fix FIX_INNER 1. intros []; [done|]. by simpl; f_equal.
  Qed.

  Global Instance val_inhabited : Inhabited val := populate (LitV LitPoison).
  Global Instance val_dec_eq : EqDecision val.
  Proof.
    refine (λ v1 v2, cast_if (decide (of_val v1 = of_val v2))); abstract naive_solver.
  Defined.
  Global Instance val_countable : Countable val.
  Proof.
    refine (inj_countable
      (λ v, match v with LitV l => inl l | RecV f xl e => inr (f, xl, e) end)
      (λ x, match x with inl l => Some $ LitV l | inr (f, xl, e) =>
            match decide _ with left C => Some $ @RecV f xl e C | _ => None end end) _).
    intros [] =>//. by rewrite decide_True_pi.
  Qed.

  Canonical Structure valO := leibnizO val.
  Canonical Structure exprO := leibnizO expr.

  Class IntoVal (e : expr) (v : val) :=
    into_val : of_val v = e.
  Class AsVal (e : expr) := as_val : ∃ v, of_val v = e.
  Global Instance as_vals_of_val vs : TCForall AsVal (of_val <$> vs).
  Proof.
    apply TCForall_Forall, Forall_fmap, Forall_true=> v.
    rewrite /AsVal /=; eauto.
  Qed.

  Class Atomic (e : expr) := atomic :
    match e with
    | Read _ e | Alloc e => is_Some (to_val e)
    | Write _ e1 e2 | Free e1 e2 => is_Some (to_val e1) ∧ is_Some (to_val e2)
    | CAS e0 e1 e2 _ _ _ =>
      is_Some (to_val e0) ∧ is_Some (to_val e1) ∧ is_Some (to_val e2)
    | Fork _ | FenceRel | FenceAcq | FenceSC => True
    | _ => False
    end.
End base.

Export base.

(* Some coercions for expresions *)
Coercion lit_of_bool : bool >-> lit.
Coercion LitInt : Z >-> lit.
Coercion LitLoc : loc >-> lit.

(** The state *)
Notation baseMessage := (@baseMessage loc lblock_loc val).
Notation cell := (gmap time baseMessage).
Notation message := (@message loc lblock_loc val).
Notation view := (@view loc lblock_loc).
Notation threadView := (@threadView loc lblock_loc).
Notation view_Lat := (@view_Lat loc lblock_loc).
Notation tview_Lat := (@tview_Lat loc lblock_loc).

Definition state := @global loc lblock_loc val.

Implicit Type (σ : state) (M: memory) (C: cell).

Global Instance state_Inhabited : Inhabited state.
Proof. do 2!econstructor; exact: inhabitant. Qed.

Canonical Structure stateO := leibnizO state.

Module nopro_lang.
    (** The actual language has views *)
  Record expr : Type :=
    mkExpr { expr_expr :> base.expr; expr_view : threadView }.
  Record val : Type :=
    mkVal { val_val :> base.val; val_view : threadView }.
  Definition ectx_item := ectx_item.
  Definition fill_item (Ki : ectx_item) (e : expr) : expr :=
    mkExpr (fill_item Ki e) e.(expr_view).
  Definition of_val (v : val) : expr :=
    mkExpr (of_val v) v.(val_view).
  Definition to_val (e : expr) : option val :=
    (λ v, mkVal v e.(expr_view)) <$> to_val e.

  Definition subst x es (e : expr) : expr :=
    mkExpr (subst x es e) (expr_view e).


  Program Definition forkView (𝓥 : threadView) : threadView
    := mkTView ∅ ∅ 𝓥.(cur) 𝓥.(cur) _ _ _ _.
  Solve Obligations with (intros; by eapply bool_decide_pack).

  Lemma forkView_subseteq 𝓥: forkView 𝓥 ⊑ 𝓥.
  Proof. rewrite /forkView; split; simpl; [done..|apply cur_acq]. Qed.

  Inductive head_step :
    expr → state → list Empty_set → expr → state → list expr → Prop :=
  | pure_step σ 𝓥 e e' efs
      (BaseStep : base.head_step σ.(mem) 𝓥 e None e' (expr_expr <$> efs))
      (ForkViews : Forall (eq (forkView 𝓥)) (expr_view <$> efs))
    : head_step (mkExpr e 𝓥) σ [] (mkExpr e' 𝓥) σ efs
  | impure_step σ 𝓥  𝓝' 𝓥' M' 𝓢' ot 𝑚s e evt e' efs
      (NoFork : efs = [])
      (ExprStep : base.head_step σ.(mem) 𝓥 e (Some evt) e' (expr_expr <$> efs))
      (PStep : lbl_machine_step 𝓥 σ.(mem) σ.(sc) evt ot 𝑚s 𝓥' M' 𝓢')
      (DRFPost: drf_post σ.(na) evt ot 𝑚s 𝓝')
      (DRFPre: ∀ evt2 e2 efs2 ot2 𝑚s2 𝓥2 M2 𝓢2,
          base.head_step σ.(mem) 𝓥 e (Some evt2) e2 (expr_expr <$> efs2) →
          lbl_machine_step 𝓥 σ.(mem) σ.(sc) evt2 ot2 𝑚s2 𝓥2 M2 𝓢2 →
          drf_pre σ.(na) 𝓥 σ.(mem) evt2)
    : head_step (mkExpr e 𝓥) σ [] (mkExpr e' 𝓥') (mkGB 𝓢' 𝓝' M') efs.
  Arguments head_step _%E _ _ _%E _ _%E.

  Lemma head_step_tview_sqsubseteq e 𝓥 σ κs e' 𝓥' σ' ef
    (STEP: head_step (mkExpr e 𝓥) σ κs (mkExpr e' 𝓥') σ' ef) :
    𝓥 ⊑ 𝓥'.
  Proof.
    inversion STEP; first done. subst.
    by eapply (machine_step_tview_sqsubseteq _ _ _ _ _ _ _ _ _ PStep).
  Qed.

  (* Some properties of the language *)
  Lemma to_of_val v : to_val (of_val v) = Some v.
  Proof. destruct v. cbv -[base.to_val base.of_val]. by rewrite base.to_of_val. Qed.

  Lemma of_to_val e v : to_val e = Some v → of_val v = e.
  Proof.
    destruct e as [e ?], v. cbv -[base.to_val base.of_val].
    case C : (base.to_val e) => //. move => [<- <-]. f_equal. exact: of_to_val.
  Qed.

  Lemma to_base_val e v:
    to_val e = Some v → base.to_val e = Some v.(val_val).
  Proof. destruct e, v. cbv -[base.to_val]. case_match; naive_solver. Qed.

  Lemma to_base_val_inv e v π:
    base.to_val e = Some v → to_val (mkExpr e π) = Some (mkVal v π).
  Proof. cbv -[base.to_val]. by move => ->. Qed.

  Lemma of_base_val e v:
    of_val v = e → base.of_val v = e.
  Proof. destruct e,v. by inversion 1. Qed.

  Global Instance of_val_inj : Inj (=) (=) of_val.
  Proof.
    intros [][]. cbv -[of_val]. move => [? <-]. f_equal. by eapply of_val_inj.
  Qed.

  Global Instance fill_item_inj Ki : Inj (=) (=) (fill_item Ki).
  Proof.
    intros [][]. cbv -[fill_item]. move => [? <-]. f_equal.
    by eapply fill_item_inj.
  Qed.

  Lemma fill_item_val Ki e :
    is_Some (to_val (fill_item Ki e)) → is_Some (to_val e).
  Proof. move/fmap_is_Some/fill_item_val => H. exact/fmap_is_Some. Qed.

  Lemma val_stuck σ1 e1 κs σ2 e2 ef :
    head_step e1 σ1 κs e2 σ2 ef → to_val e1 = None.
  Proof.
    inversion 1; subst; last inversion ExprStep;
      first (cbv -[base.to_val]; by erewrite val_stuck; last eassumption);
      reflexivity.
  Qed.

  Lemma head_ctx_step_val Ki e σ κs e2 σ2 ef :
    head_step (fill_item Ki e) σ κs e2 σ2 ef → is_Some (to_val e).
  Proof.
    inversion 1; subst; apply fmap_is_Some; exact: head_ctx_step_val.
  Qed.

  Lemma fill_item_no_val_inj Ki1 Ki2 e1 e2 :
    to_val e1 = None → to_val e2 = None → fill_item Ki1 e1 = fill_item Ki2 e2
    → Ki1 = Ki2.
  Proof.
    move => /fmap_None H1 /fmap_None H2 [] H3 ?.
    exact: fill_item_no_val_inj H1 H2 H3.
  Qed.

  (** Closed expressions *)

  Lemma nopro_ectxi_lang_mixin :
    EctxiLanguageMixin of_val to_val fill_item head_step.
  Proof.
    split; eauto using to_of_val, of_to_val, val_stuck, fill_item_val,
      fill_item_no_val_inj, head_ctx_step_val with typeclass_instances.
  Qed.
End nopro_lang.

Notation mkExpr := nopro_lang.mkExpr.
Notation mkVal := nopro_lang.mkVal.
Coercion nopro_lang.expr_expr : nopro_lang.expr >-> expr.
Coercion nopro_lang.val_val : nopro_lang.val >-> val.

Canonical Structure nopro_ectxi_lang := EctxiLanguage nopro_lang.nopro_ectxi_lang_mixin.
Canonical Structure nopro_ectx_lang := EctxLanguageOfEctxi nopro_ectxi_lang.
Canonical Structure nopro_lang := LanguageOfEctx nopro_ectx_lang.

(* Lemmas about the language. *)
Global Instance base_atomic_atomic e 𝓥 :
  Atomic e → language.Atomic WeaklyAtomic (nopro_lang.mkExpr e 𝓥).
Proof.
  intros He. apply strongly_atomic_atomic, ectx_language_atomic.
  - intros σ κs [e' 𝓥'] σ' ef. cbn. move => STEP. apply/fmap_is_Some.
    destruct e=>//=; repeat (case_match; try done);
    inversion STEP; (inversion BaseStep || inversion ExprStep);
    rewrite ?to_of_val; eauto.
  - apply ectxi_language_sub_redexes_are_values=> /= Ki [e' ?] Hfill.
    apply/fmap_is_Some. revert He. inversion Hfill as [Hfill']; subst; clear Hfill.
    destruct Ki, e'=>//=; naive_solver.
Qed.

Lemma fill_base_nopro (K : list nopro_lang.ectx_item) e 𝓥 :
  mkExpr (fill K e) 𝓥 = ectxi_language.fill K (mkExpr e 𝓥).
Proof.
  revert e. induction K; intros ?; [done|apply IHK].
Qed.

Section Progress.
  (** Lemmas for progress *)
  Lemma alloc_fresh_head_step n σ 𝓥
    (CLOSED: 𝓥 ∈ σ.(mem)):
    let l := (fresh_block σ.(mem), 0) in
    0 < n →
    ∃ σ' 𝓥', nopro_lang.head_step (mkExpr (Alloc $ Lit n) 𝓥) σ []
                                  (mkExpr (Lit $ LitLoc l) 𝓥') σ' [].
  Proof.
    intros l Hn.
    have ALLOC : alloc σ.(mem) (Pos.to_nat $ Z.to_pos n) l.
    { apply lblock_alloc_fresh. lia. }
    have STEP := (alloc_progress 𝓥 σ.(mem) σ.(sc) l (Z.to_pos n) CLOSED ALLOC).
    eexists _, _. econstructor 2; [by econstructor..|done|constructor|].
    move => evt2 e2 efs2 ots 𝑚s2 𝓥2 M2 𝓢2 STEP' MSTEP'.
    inversion STEP'. constructor.
  Qed.

  Lemma dealloc_head_step (n: nat) (l: loc) σ 𝓥
    (NEMP: ∀ n', (n' < n)%nat → σ.(mem) !!c (l >> n') ≠ ∅)
    (NAR: ∀ n', (n' < n)%nat
            → σ.(na) !! (l >> n') ⊑ 𝓥.(cur) !! (l >> n'))
    (NAW: ∀ n', (n' < n)%nat →
            ∀ 𝑚', 𝑚' ∈ σ.(mem) → mloc 𝑚' = l >> n' →
              Some (mto 𝑚') ⊑ 𝓥.(cur) !!w (l >> n'))
    (BLK: ∀ n' : nat, l >> n' ∈ dom σ.(mem) ↔ (n' < n)%nat)
    (ALLOC: ∀ n', (n' < n)%nat → ¬ cell_deallocated (σ.(mem) !!c (l >> n')))
    (AINV: alloc_inv σ.(mem)) (CLOSED: 𝓥 ∈ σ.(mem)) :
    (0 < n)%nat →
    ∃ σ' 𝓥',
    nopro_lang.head_step (mkExpr (Free (Lit n) (Lit l)) 𝓥) σ []
                         (mkExpr (Lit LitPoison) 𝓥') σ' [].
  Proof.
    move => /Nat.neq_0_lt_0 /Nat.neq_sym LT0.
    have DEALLOC : dealloc σ.(mem) n l.
    { constructor; [lia|..|done]=> ? Lt. specialize (ALLOC _ Lt). apply BLK in Lt.
      apply elem_of_difference. split; first done.
      move => ?. by apply ALLOC, mem_deallocated_correct1. }
    destruct (dealloc_progress 𝓥 σ.(mem) σ.(sc) σ.(na) l (Pos.of_nat n))
      as [PRE STEP]; rewrite ?Nat2Pos.id //; [].
    have Eqn: Z.to_pos n = Pos.of_nat n.
    { destruct n=>//=. by rewrite Pos.of_nat_succ. }
    eexists _, _. econstructor 2;
        [econstructor; lia|econstructor; lia|by rewrite Eqn|constructor|].
    move => evt2 e2 efs2 ots 𝑚s2 𝓥2 M2 𝓢2 STEP' MSTEP'.
    inversion STEP'. subst. rewrite Eqn. by constructor.
  Qed.

  (* Reading doesn't need initialization, thus can return poison *)
  Lemma read_head_step l o σ 𝓥
    (CLOSED: 𝓥 ∈ σ.(mem)) (WFM: Wf σ.(mem))
    (AINV: alloc_inv σ.(mem)) (ALLOC: allocated l σ.(mem))
    (NE: σ.(mem) !!c l ≠ ∅) :
    let ot :=  𝓥.(cur) in
    (* basic na safe *)
    (σ.(na) !!w l ⊑ ot !!w l) →
    (o = NonAtomic →
      (∀ 𝑚', 𝑚' ∈ σ.(mem) → mloc 𝑚' = l → Some (mto 𝑚') ⊑ ot !!w l) ∧
      σ.(na) !!aw l ⊑ 𝓥.(cur) !!aw l) →
    ∃ σ' 𝓥' v,
      nopro_lang.head_step (mkExpr (Read o (Lit $ LitLoc l)) 𝓥) σ []
                           (nopro_lang.of_val (mkVal v 𝓥')) σ' [].
  Proof.
    move => otl NA RNA.
    destruct (read_progress _ _ σ.(sc) _ _ _ CLOSED WFM AINV ALLOC NE NA RNA)
      as [? [𝓥' [𝓝' [tr [v [RS [DRF ISVAL]]]]]]].
    exists (mkGB σ.(sc) 𝓝' σ.(mem)), 𝓥'.
    exists (match v with | VVal v' => v' | _ => LitV LitPoison end).
    econstructor 2; [by econstructor| | |by constructor|..].
    - constructor.
      destruct v eqn:Eqv; [apply memval_val_AVal| |apply memval_val_VVal].
      inversion RS. subst. inversion READ. simpl in *.
      by specialize (ALLOC _ _ IN).
    - done.
    - clear DRF RS ISVAL. move => evt2 e2 efs2 ots 𝑚s2 𝓥2 M2 𝓢2 STEP' MSTEP'.
      inversion STEP'. by constructor.
  Qed.

  Lemma write_head_step l e v o σ 𝓥
    (CLOSED: 𝓥 ∈ σ.(mem))
    (AINV: alloc_inv σ.(mem))
    (ALLOC: allocated l σ.(mem))
    (NEMP: ∃ t, is_Some (σ.(mem) !! (l,t)))
    (TOVAL: to_val e = Some v) :
    let ot :=  𝓥.(cur) in
    σ.(na) !!nr l ⊑ ot !!nr l →
    (* basic na safe *)
    (σ.(na) !!w l ⊑ ot !!w l) →
    (o = NonAtomic →
      (∀ 𝑚', 𝑚' ∈ σ.(mem) → mloc 𝑚' = l → Some (mto 𝑚') ⊑ ot !!w l) ∧
       σ.(na) !!aw l ⊑ ot !!aw l ∧
       σ.(na) !!ar l ⊑ ot !!ar l) →
    ∃ σ' 𝓥',
      nopro_lang.head_step (mkExpr (Write o (base .Lit $ LitLoc l) e) 𝓥) σ []
                           (mkExpr (Lit LitPoison) 𝓥') σ' [].
  Proof.
    move => otl NAR NA NAW.
    destruct (write_addins_progress 𝓥 σ.(mem) σ.(sc) σ.(na) l o v
                CLOSED AINV ALLOC NEMP NAR NA NAW)
      as [DRFR [𝑚 [𝓥' [M' [STEP [EQL DRF]]]]]]. subst l.
    eexists _, _.
    econstructor 2; [by econstructor|by constructor|done|by constructor|..].
    clear DRF STEP. move => evt2 e2 efs2 ots 𝑚s2 𝓥2 M2 𝓢2 STEP' MSTEP'.
    inversion STEP'. by constructor.
  Qed.

  (* Update requires allocated and non-UB for all possible comparisons *)
  Lemma update_head_step l er ew vr (vw: val) orf or ow σ 𝓥
    (WFM: Wf σ.(mem)) (CLOSED: 𝓥 ∈ σ.(mem))
    (AINV: alloc_inv σ.(mem))
    (ALLOC: allocated l σ.(mem)) (NE: σ.(mem) !!c l ≠ ∅)
    (TVR: to_val er = Some $ LitV vr)
    (TVW: to_val ew = Some $ vw)
    (RLXR: Relaxed ⊑ orf) (RLXR2: Relaxed ⊑ or)
    (RLXW: Relaxed ⊑ ow) :
    (* basic na safe *)
    σ.(na) !!nr l ⊑ 𝓥.(cur) !!nr l →
    let ot :=  𝓥.(cur) in
    (σ.(na) !!w l ⊑ ot !!w l) →
    (* allocated *)
    (∃ t m, σ.(mem) !! (l,t) = Some m) →
    (* non-UB for all possible comparisons, i.e. all readable values *)
    (∀ (t: time) (m: baseMessage), σ.(mem) !! (l,t) = Some m → ot !!w l ⊑ Some t
      → ∃ v, memval_val_rel m.(mval) (LitV v) ∧ lit_comparable vr v) →
    ∃ σ' 𝓥' b,
      nopro_lang.head_step (mkExpr (CAS (Lit $ LitLoc l) er ew orf or ow) 𝓥) σ []
                           (mkExpr (Lit b) 𝓥') σ' [].
  Proof.
    move => NAR ot NA INIT NUB.
    destruct (update_read_write_addins_progress 𝓥 σ.(mem) σ.(sc) σ.(na) l
                                                (LitV vr) vw orf or ow CLOSED)
      as [DRFR [[𝓥' [M' [𝓝' [v [tr [NEQ [READ DRFP]]]]]]]|
                [𝓥' [M' [𝓝' [tr [𝑚 [UPDATE [EQL DRFP]]]]]]]]];
      [done.. | | |].
    - destruct INIT as (t & m & Htm). exists t, m. split=>//=.
      case (decide (ot !!w l ⊑ Some t)) as [Ht|?%total_not_strict]; [|done].
      destruct (NUB _ _ Htm Ht) as (?&REL&COMP)=>EQ. rewrite EQ in REL.
      inversion REL. subst. inversion COMP.
    - exists (mkGB σ.(sc) 𝓝' M'), 𝓥', false.
      econstructor 2;  [done| |done|by constructor|..].
      + inversion READ. inversion READ0. inversion READ1. simpl in *. subst.
        destruct (NUB _ _ IN PLN) as [v0 [REL Comp0]].
        inversion REL; subst; [|by inversion Comp0].
        eapply CasFailS; [eauto..| |done]. rewrite H1 in H0. inversion H0. subst.
        inversion Comp0; subst; constructor; clear -NEQ; naive_solver.
      + clear READ DRFP NEQ NUB.
        move => evt2 e2 efs2 ots 𝑚s2 𝓥2 M2 𝓢2 STEP' MSTEP'. inversion STEP'.
        * subst. simplify_eq. constructor. clear - DRFR RLXR.
          inversion DRFR; subst. inversion DRFR0.
          constructor; [done|]. by rewrite (decide_True _ _ RLXR).
        * subst. simplify_eq. clear -DRFR. inversion DRFR; subst.
          by constructor.
    - exists (mkGB σ.(sc) 𝓝' M'), 𝓥', true. subst l.
      econstructor 2; [done| |done|by constructor|..].
      + inversion UPDATE. inversion READ. inversion READ0.
        simpl in *. subst. rewrite -SAME in NUB.
        destruct (NUB _ _ IN PLN) as [v0 [Eq0 Comp0]].
        rewrite ISV1 in Eq0. inversion Eq0. subst v0.
        eapply CasSucS; [eauto..|inversion Comp0; constructor|done].
      + clear UPDATE DRFP.
        move => evt2 e2 efs2 ots 𝑚s2 𝓥2 M2 𝓢2 STEP' MSTEP'. inversion STEP'.
        * subst. simplify_eq. constructor. clear - DRFR RLXR.
          inversion DRFR; subst. inversion DRFR0.
          constructor; [done|]. by rewrite (decide_True _ _ RLXR).
        * subst. simplify_eq. clear -DRFR. inversion DRFR; subst.
          by constructor.
  Qed.

  Lemma acq_fence_head_step σ 𝓥 :
    ∃ σ' 𝓥', nopro_lang.head_step (mkExpr FenceAcq 𝓥) σ []
                                  (mkExpr (Lit LitPoison) 𝓥') σ' [].
  Proof.
    do 2 eexists. econstructor 2;
      [econstructor|econstructor|by repeat econstructor|econstructor|..].
    move => ???????? STEP _. inversion STEP. constructor.
  Qed.

  Lemma rel_fence_head_step σ 𝓥 :
    ∃ σ' 𝓥', nopro_lang.head_step (mkExpr FenceRel 𝓥) σ []
                                  (mkExpr (Lit LitPoison) 𝓥') σ' [].
  Proof.
    do 2 eexists. econstructor 2;
      [econstructor|econstructor|by repeat econstructor|econstructor|..].
    move => ???????? STEP _. inversion STEP. constructor.
  Qed.

  Lemma sc_fence_head_step σ 𝓥 :
    ∃ σ' 𝓥', nopro_lang.head_step (mkExpr FenceSC 𝓥) σ []
                                  (mkExpr (Lit LitPoison) 𝓥') σ' [].
  Proof.
    do 2 eexists. econstructor 2;
      [econstructor|econstructor|by repeat econstructor|econstructor|..].
    move => ???????? STEP _. inversion STEP. constructor.
  Qed.

  Lemma fork_head_step e σ 𝓥:
    ∃ σ' 𝓥', nopro_lang.head_step (mkExpr (Fork e) 𝓥) σ []
                                  (mkExpr (Lit LitPoison) 𝓥) σ' [mkExpr e 𝓥'].
  Proof. by repeat econstructor. Qed.
End Progress.
