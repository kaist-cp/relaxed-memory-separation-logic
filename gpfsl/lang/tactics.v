From stdpp Require Import fin_maps.
From gpfsl Require Export lang.

(** We define an alternative representation of expressions in which the
embedding of values and closed expressions is explicit. By reification of
expressions into this type we can implement substitution, closedness
checking, atomic checking, and conversion into values, by computation. *)
Module W.
Inductive expr :=
| Val (v : val)
| ClosedExpr (e : base.expr) `{!Closed [] e}
(* Base lambda calculus *)
| Var (x : string)
| Rec (f : binder) (xl : list binder) (e : expr)
| App (e : expr) (el : list expr)
(* Base types and their operations *)
| Lit (l : lit)
| UnOp (op : un_op) (e : expr)
| BinOp (op : bin_op) (e1 e2 : expr)
| Case (e : expr) (el : list expr)
(* Concurrency *)
| Fork (e : expr)
(* Memory *)
| Read (o : memOrder) (e : expr)
| Write (o : memOrder) (e1 e2: expr)
| CAS (e0 e1 e2 : expr) (orf or or: memOrder)
| Alloc (e : expr)
| Free (e1 e2 : expr)
| FenceAcq
| FenceRel
| FenceSC
.

Fixpoint to_expr (e : expr) : base.expr :=
  match e return base.expr with
  | Val v => base.of_val v
  | ClosedExpr e => e
  | Var x => base.Var x
  | Rec f xl e => base.Rec f xl (to_expr e)
  | App e el => base.App (to_expr e) (map to_expr el)
  | Lit l => base.Lit l
  | UnOp op e => base.UnOp op (to_expr e)
  | BinOp op e1 e2 => base.BinOp op (to_expr e1) (to_expr e2)
  | Case e el => base.Case (to_expr e) (map to_expr el)
  | Fork e => base.Fork (to_expr e)
  | Read o e => base.Read o (to_expr e)
  | Write o e1 e2 => base.Write o (to_expr e1) (to_expr e2)
  | CAS e0 e1 e2 orf or ow => base.CAS (to_expr e0) (to_expr e1) (to_expr e2) orf or ow
  | Alloc e => base.Alloc (to_expr e)
  | Free e1 e2 => base.Free (to_expr e1) (to_expr e2)
  | FenceAcq => base.FenceAcq
  | FenceRel => base.FenceRel
  | FenceSC => base.FenceSC
  end.

Ltac of_expr e :=
  lazymatch e with
  | base.Var ?x => constr:(Var x)
  | base.Rec ?f ?xl ?e => let e := of_expr e in constr:(Rec f xl e)
  | base.App ?e ?el =>
     let e := of_expr e in let el := of_expr el in constr:(App e el)
  | base.Lit ?l => constr:(Lit l)
  | base.UnOp ?op ?e => let e := of_expr e in constr:(UnOp op e)
  | base.BinOp ?op ?e1 ?e2 =>
     let e1 := of_expr e1 in let e2 := of_expr e2 in constr:(BinOp op e1 e2)
  | base.Case ?e ?el =>
     let e := of_expr e in let el := of_expr el in constr:(Case e el)
  | base.Fork ?e => let e := of_expr e in constr:(Fork e)
  | base.Read ?o ?e => let e := of_expr e in constr:(Read o e)
  | base.Write ?o ?e1 ?e2 =>
     let e1 := of_expr e1 in let e2 := of_expr e2 in constr:(Write o e1 e2)
  | base.CAS ?e0 ?e1 ?e2 ?orf ?or ?ow =>
     let e0 := of_expr e0 in let e1 := of_expr e1 in let e2 := of_expr e2 in
     constr:(CAS e0 e1 e2 orf or ow)
  | base.Alloc ?e => let e := of_expr e in constr:(Alloc e)
  | base.Free ?e1 ?e2 =>
     let e1 := of_expr e1 in let e2 := of_expr e2 in constr:(Free e1 e2)
  | base.FenceAcq => constr:(FenceAcq)
  | base.FenceRel => constr:(FenceRel)
  | base.FenceSC => constr:(FenceSC)
  | @nil base.expr => constr:(@nil expr)
  | @cons base.expr ?e ?el =>
    let e := of_expr e in let el := of_expr el in constr:(e::el)
  | to_expr ?e => e
  | base.of_val ?v => constr:(Val v)
  | _ => match goal with H : Closed [] e |- _ => constr:(@ClosedExpr e H) end
  end.

Fixpoint is_closed (X : list string) (e : expr) : bool :=
  match e with
  | Val _ | ClosedExpr _ | Lit _ | FenceAcq | FenceRel | FenceSC => true
  | Var x => bool_decide (x ∈ X)
  | Rec f xl e => is_closed (f :b: xl +b+ X) e
  | UnOp _ e | Fork e | Read _ e | Alloc e => is_closed X e
  | BinOp _ e1 e2 | Write _ e1 e2 | Free e1 e2 =>
     is_closed X e1 && is_closed X e2
  | App e el | Case e el => is_closed X e && forallb (is_closed X) el
  | CAS e0 e1 e2 _ _ _ =>
     is_closed X e0 && is_closed X e1 && is_closed X e2
  end.

Lemma is_closed_correct X e : is_closed X e → base.is_closed X (to_expr e).
Proof.
  revert e X. fix FIX 1; destruct e =>/=;
  try naive_solver eauto using is_closed_of_val, is_closed_weaken_nil.
  - induction el=>/=; naive_solver.
  - induction el=>/=; naive_solver.
Qed.

(* We define [to_val (ClosedExpr _)] to be [None] since [ClosedExpr]
constructors are only generated for closed expressions of which we know nothing
about apart from being closed. Notice that the reverse implication of
[to_val_Some] thus does not hold. *)
Definition to_val (e : expr) : option val :=
  match e with
  | Val v => Some v
  | Rec f xl e =>
     if decide (is_closed (f :b: xl +b+ []) e) is left H
     then Some (@RecV f xl (to_expr e) (is_closed_correct _ _ H)) else None
  | Lit l => Some (LitV l)
  | _ => None
  end.
Lemma to_val_Some e v :
  to_val e = Some v → base.of_val v = W.to_expr e.
Proof.
  revert v. induction e; intros; simplify_option_eq; try f_equal; auto using of_to_val.
Qed.
Lemma to_val_is_Some e :
  is_Some (to_val e) → ∃ v, base.of_val v = to_expr e.
Proof. intros [v ?]; exists v; eauto using to_val_Some. Qed.

Fixpoint subst (x : string) (es : expr) (e : expr)  : expr :=
  match e with
  | Val v => Val v
  | @ClosedExpr e H => @ClosedExpr e H
  | Var y => if bool_decide (y = x) then es else Var y
  | Rec f xl e =>
     Rec f xl $ if bool_decide (BNamed x ≠ f ∧ BNamed x ∉ xl) then subst x es e else e
  | App e el => App (subst x es e) (map (subst x es) el)
  | Lit l => Lit l
  | UnOp op e => UnOp op (subst x es e)
  | BinOp op e1 e2 => BinOp op (subst x es e1) (subst x es e2)
  | Case e el => Case (subst x es e) (map (subst x es) el)
  | Fork e => Fork (subst x es e)
  | Read o e => Read o (subst x es e)
  | Write o e1 e2 => Write o (subst x es e1) (subst x es e2)
  | CAS e0 e1 e2 orf or ow =>
      CAS (subst x es e0) (subst x es e1) (subst x es e2) orf or ow
  | Alloc e => Alloc (subst x es e)
  | Free e1 e2 => Free (subst x es e1) (subst x es e2)
  | FenceAcq => FenceAcq
  | FenceRel => FenceRel
  | FenceSC => FenceSC
  end.

Lemma to_expr_subst x er e :
  to_expr (subst x er e) = base.subst x (to_expr er) (to_expr e).
Proof.
  revert e x er. fix FIX 1; destruct e=> /= ? er; repeat case_bool_decide;
    f_equal; auto using is_closed_nil_subst, is_closed_of_val, eq_sym.
  - induction el=>//=. f_equal; auto.
  - induction el=>//=. f_equal; auto.
Qed.

Definition is_atomic (e : expr) :=
  match e with
  | Read _ e | Alloc e => bool_decide (is_Some (to_val e))
  | Write _ e1 e2 | Free e1 e2 => bool_decide (is_Some (to_val e1) ∧ is_Some (to_val e2))
  | CAS e0 e1 e2 _ _ _ =>
     bool_decide (is_Some (to_val e0) ∧ is_Some (to_val e1) ∧ is_Some (to_val e2))
  | Fork _ | FenceRel | FenceAcq | FenceSC => true
  | _ => false
  end.

Lemma is_atomic_correct e :
  is_atomic e  → Atomic (to_expr e).
Proof.
  destruct e=>//=; naive_solver eauto using base.as_val_is_Some, to_val_is_Some, bool_decide_spec.
Qed.
End W.

Ltac solve_closed :=
  match goal with
  | |- Closed ?X ?e =>
     let e' := W.of_expr e in change (Closed X (W.to_expr e'));
     apply W.is_closed_correct;
      (vm_compute; exact I) || (rewrite /= bool_decide_true; set_solver)
  end.
Global Hint Extern 0 (Closed _ _) => solve_closed : typeclass_instances.

Ltac solve_base_to_val :=
  rewrite /AsVal /IntoVal;
  try match goal with
  | |- context E [language.to_val ?e] =>
        let X := context E [to_val e] in change X
  end;
  match goal with
  | |- of_val ?v = ?e =>
    let e' := W.of_expr e in
    change (of_val v = W.to_expr e');
    apply W.to_val_Some; simpl; unfold W.to_expr; reflexivity
  | |- ∃ v, of_val v = ?e =>
    let e' := W.of_expr e in
    change (∃ v, of_val v = W.to_expr e');
    apply W.to_val_is_Some, (bool_decide_unpack _); vm_compute; exact I
  end.
Global Hint Extern 10 (IntoVal _ _) => solve_base_to_val : typeclass_instances.
Global Hint Extern 10 (AsVal _) => solve_base_to_val : typeclass_instances.

Global Instance noprol_lang_intoval e v π :
  IntoVal e v → language.IntoVal (mkExpr e π) (mkVal v π).
Proof. intros <-. done. Qed.
Global Instance noprol_lang_asval e π :
  AsVal e → language.AsVal (mkExpr e π).
Proof. intros [? <-]. eexists (mkVal _ _). done. Qed.

Ltac solve_atomic :=
  match goal with
  | |- Atomic ?e => let e' := W.of_expr e in change (Atomic (W.to_expr e'));
     apply W.is_atomic_correct; vm_compute; exact I
  end.
Global Hint Extern 10 (Atomic _) => solve_atomic : typeclass_instances.

(** Substitution *)
Ltac simpl_subst :=
  unfold subst_v; simpl;
  repeat match goal with
  | |- context [subst ?x ?er ?e] =>
    let er' := W.of_expr er in let e' := W.of_expr e in
    change (subst x er e) with (subst x (W.to_expr er') (W.to_expr e'));
    rewrite <-(W.to_expr_subst x); simpl
  end;
  unfold W.to_expr; simpl.
Arguments W.to_expr : simpl never.
Arguments subst : simpl never.
Arguments nopro_lang.subst : simpl never.

(** The tactic [reshape_expr e tac] decomposes the expression [e] into an
evaluation context [K] and a subexpression [e']. It calls the tactic [tac K e']
for each possible decomposition until [tac] succeeds. *)
Ltac reshape_val e tac :=
  let rec go e :=
  lazymatch e with
  | of_val ?v => v
  | Lit ?l => constr:(LitV l)
  | Rec ?f ?xl ?e => constr:(RecV f xl e)
  end in let v := go e in tac v.

Ltac reshape_expr e tac :=
  let rec go_fun K f vs es :=
    match es with
    | ?e :: ?es => reshape_val e ltac:(fun v => go_fun K f (v :: vs) es)
    | ?e :: ?es => go (AppRCtx f (reverse vs) es :: K) e
    end
  with go K e :=
  match e with
  | _ => tac K e
  | UnOp ?op ?e => go (UnOpCtx op :: K) e
  | BinOp ?op ?e1 ?e2 =>
     reshape_val e1 ltac:(fun v1 => go (BinOpRCtx op v1 :: K) e2)
  | BinOp ?op ?e1 ?e2 => go (BinOpLCtx op e2 :: K) e1
  | App ?e ?el => reshape_val e ltac:(fun f => go_fun K f (@nil val) el)
  | App ?e ?el => go (AppLCtx el :: K) e
  | Read ?o ?e => go (ReadCtx o :: K) e
  | Write ?o ?e1 ?e2 =>
    reshape_val e1 ltac:(fun v1 => go (WriteRCtx o v1 :: K) e2)
  | Write ?o ?e1 ?e2 => go (WriteLCtx o e2 :: K) e1
  | CAS ?e0 ?e1 ?e2 ?orf ?or ?ow => reshape_val e0 ltac:(fun v0 => first
     [ reshape_val e1 ltac:(fun v1 => go (CasRCtx orf or ow v0 v1 :: K) e2)
     | go (CasMCtx orf or ow v0 e2 :: K) e1 ])
  | CAS ?e0 ?e1 ?e2 ?orf ?or ?ow => go (CasLCtx orf or ow e1 e2 :: K) e0
  | Alloc ?e => go (AllocCtx :: K) e
  | Free ?e1 ?e2 => reshape_val e1 ltac:(fun v1 => go (FreeRCtx v1 :: K) e2)
  | Free ?e1 ?e2 => go (FreeLCtx e2 :: K) e1
  | Case ?e ?el => go (CaseCtx el :: K) e
  end
  in go (@nil ectx_item) e.

Ltac inv_head_step :=
  repeat match goal with
  | _ => progress simplify_map_eq/= (* simplify memory stuff *)
  | H : to_val _ = Some _ |- _ => apply of_to_val in H
  | H : _ = of_val ?v |- _ =>
     is_var v; destruct v; first[discriminate H|injection H as H]
  | H : head_step _ _ ?e _ _ _ |- _ =>
     try (is_var e; fail 1); (* inversion yields many goals if [e] is a variable
     and can thus better be avoided. *)
     inversion H ; subst; clear H
  | H : nopro_lang.head_step ?e _ _ _ _ _ |- _ =>
     try (is_var e; fail 1);
     inversion H ; subst; clear H
  | H : _ <$> _ = [] |- _ => apply fmap_nil_inv in H; subst
  | H : _ <$> _ = ?e :: _ |- _ =>
    apply fmap_cons_inv in H; destruct H as ([]&?&?&?&?); subst
  | H : _::_ = _ <$> _ |- _ => apply eq_sym in H
  | H : [] = _ <$> _ |- _ => apply eq_sym in H
  | H : Forall _ [] |- _ => clear H
  | H : Forall _ (_ :: _) |- _ => inversion H; clear H; subst
  end.

Ltac inv_bin_op_eval :=
  repeat match goal with
  | H : bin_op_eval _ ?c _ _ _ |- _ => is_constructor c; inversion H; clear H; simplify_eq/=
  end.

Ltac inv_un_op_eval :=
  repeat match goal with
  | H : un_op_eval ?c _ _ |- _ => is_constructor c; inversion H; clear H; simplify_eq/=
  end.

Ltac inv_lit :=
  repeat match goal with
  | H : lit_eq _ ?x ?y |- _ => inversion H; clear H; simplify_map_eq/=
  | H : lit_neq ?x ?y |- _ => inversion H; clear H; simplify_map_eq/=
  end.
