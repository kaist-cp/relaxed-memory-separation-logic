From iris.program_logic Require Import language.

From gpfsl Require Export lang.

From iris.prelude Require Import options.

Coercion App : expr >-> Funclass.

Coercion nopro_lang.of_val : nopro_lang.val >-> nopro_lang.expr.
Coercion of_val : val >-> expr.

Coercion Var : string >-> expr.

Notation "[ ]" := (@nil binder) : binder_scope.
Notation "a :: b" := (@cons binder a%binder b%binder)
  (at level 60, right associativity) : binder_scope.
Notation "[ x1 ; x2 ; .. ; xn ]" :=
  (@cons binder x1%binder (@cons binder x2%binder
        (..(@cons binder xn%binder (@nil binder))..))) : binder_scope.
Notation "[ x ]" := (@cons binder x%binder (@nil binder)) : binder_scope.

Notation "[ ]" := (@nil expr) : expr_scope.
Notation "[ x ]" := (@cons expr x%E (@nil expr)) : expr_scope.
Notation "[ x1 ; x2 ; .. ; xn ]" :=
  (@cons expr x1%E (@cons expr x2%E
        (..(@cons expr xn%E (@nil expr))..))) : expr_scope.

(* Some derived forms *)
Notation Lam xl e := (Rec BAnon xl e) (only parsing).
Notation Let x e1 e2 := (App (Lam [x] e2) [e1]) (only parsing).
Notation Seq e1 e2 := (Let BAnon e1 e2) (only parsing).
Notation LamV xl e := (RecV BAnon xl e) (only parsing).
Notation LetCtx x e2 := (AppRCtx (LamV [x] e2) [] []) (only parsing).
Notation SeqCtx e2 := (LetCtx BAnon e2) (only parsing).
Notation Skip := (Seq (Lit LitPoison) (Lit LitPoison)).
Notation If e0 e1 e2 := (Case e0 [e2;e1]).

(* No scope for the values, does not conflict and scope is often not inferred
properly. *)
Notation "# l" := (LitV l%Z%V%L) (at level 8, format "# l").
Notation "# l" := (Lit l%Z%V%L) (at level 8, format "# l") : expr_scope.

(** Syntax inspired by Coq/Ocaml. Constructions with higher precedence come
    first. *)
Notation "'case:' e0 'of' el" := (Case e0%E el%E)
  (at level 102, e0, el at level 150) : expr_scope.
Notation "'if:' e1 'then' e2 'else' e3" := (If e1%E e2%E e3%E)
  (only parsing, at level 102, e1, e2, e3 at level 150) : expr_scope.
Notation "☠" := LitPoison : val_scope.

Notation "! e" := (Read NonAtomic e%E) (at level 9, format "! e") : expr_scope.
Notation "!ʳˡˣ e" := (Read Relaxed e%E) (at level 9, format "!ʳˡˣ e") : expr_scope.
Notation "!ᵃᶜ e" := (Read AcqRel e%E) (at level 9, format "!ᵃᶜ e") : expr_scope.

(* The unicode ← is already part of the notation "_ ← _; _" for bind. *)
Notation "e1 <- e2" := (Write NonAtomic e1%E e2%E)
  (at level 80) : expr_scope.
Notation "e1 <-ʳˡˣ e2" := (Write Relaxed e1%E e2%E)
  (at level 80) : expr_scope.
Notation "e1 <-ʳᵉˡ e2" := (Write AcqRel e1%E e2%E)
  (at level 80) : expr_scope.

(* A fully relaxed CAS *)
Notation "'casʳˡˣ(' l , e1 , e2 )" := (CAS l%E e1%E e2%E Relaxed Relaxed Relaxed)
  (at level 80, format "casʳˡˣ( l ,  e1 ,  e2 )") : expr_scope.
(* A release CAS, only the successful case makes a release write *)
Notation "'casʳᵉˡ(' l , e1 , e2 )" := (CAS l%E e1%E e2%E Relaxed Relaxed AcqRel)
  (at level 80, format "casʳᵉˡ( l ,  e1 ,  e2 )") : expr_scope.
(* An acquire CAS, only the successful case makes an acquire read *)
Notation "'casᵃᶜ(' l , e1 , e2 )" := (CAS l%E e1%E e2%E Relaxed AcqRel Relaxed)
  (at level 80, format "casᵃᶜ( l ,  e1 ,  e2 )") : expr_scope.
(* A release-acquire CAS, only the successful case makes an acquire read AND
  a release write *)
Notation "'casʳᵃ(' l , e1 , e2 )" := (CAS l%E e1%E e2%E Relaxed AcqRel AcqRel)
  (at level 80, format "casʳᵃ( l ,  e1 ,  e2 )") : expr_scope.

Notation "e1 + e2" := (BinOp PlusOp e1%E e2%E)
  (at level 50, left associativity) : expr_scope.
Notation "e1 - e2" := (BinOp MinusOp e1%E e2%E)
  (at level 50, left associativity) : expr_scope.
Notation "e1 * e2" := (BinOp MultOp e1%E e2%E)
  (at level 40, left associativity) : expr_scope.
Notation "e1 `quot` e2" := (BinOp QuotOp e1%E e2%E)
  (at level 35) : expr_scope.
Notation "e1 `div` e2" := (BinOp DivOp e1%E e2%E)
  (at level 35) : expr_scope.
Notation "e1 `rem` e2" := (BinOp RemOp e1%E e2%E)
  (at level 35) : expr_scope.
Notation "e1 '`mod`' e2" := (BinOp ModOp e1%E e2%E)
  (at level 35) : expr_scope.
Notation "e1 ≤ e2" := (BinOp LeOp e1%E e2%E)
  (at level 70) : expr_scope.
Notation "e1 < e2" := (BinOp LtOp e1%E e2%E)
  (at level 70) : expr_scope.
Notation "e1 = e2" := (BinOp EqOp e1%E e2%E)
  (at level 70) : expr_scope.
Notation "e1 +ₗ e2" := (BinOp OffsetOp e1%E e2%E)
  (at level 50, left associativity) : expr_scope.

Notation "'rec:' f xl := e" := (Rec f%binder xl%binder e%E)
  (at level 102, f, xl at level 1, e at level 200) : expr_scope.
Notation "'rec:' f xl := e" := (locked (RecV f%binder xl%binder e%E))
  (at level 102, f, xl at level 1, e at level 200) : val_scope.

Notation "λ: xl , e" := (Lam xl%binder e%E)
  (at level 102, xl at level 1, e at level 200) : expr_scope.
Notation "λ: xl , e" := (locked (LamV xl%binder e%E))
  (at level 102, xl at level 1, e at level 200) : val_scope.

Notation "e 'at' 𝓥" := (mkExpr e 𝓥) (at level 180) : expr_scope.
Notation "v 'at' 𝓥" := (mkVal v 𝓥) (at level 180) : val_scope.

Notation "'let:' x := e1 'in' e2" :=
  ((Lam (@cons binder x%binder nil) e2%E) (@cons expr e1%E nil))
  (at level 102, x at level 1, e1, e2 at level 150) : expr_scope.
Notation "e1 ;; e2" := (let: <> := e1 in e2)%E
  (at level 100, e2 at level 200, format "e1  ;;  e2") : expr_scope.
(* These are not actually values, but we want them to be pretty-printed. *)
Notation "'let:' x := e1 'in' e2" :=
  (LamV (@cons binder x%binder nil) e2%E (@cons expr e1%E nil))
  (at level 102, x at level 1, e1, e2 at level 150) : val_scope.
Notation "e1 ;; e2" := (let: <> := e1 in e2)%V
  (at level 100, e2 at level 200, format "e1  ;;  e2") : val_scope.
