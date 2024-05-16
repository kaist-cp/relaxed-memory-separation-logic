From stdpp Require Import namespaces.

From gpfsl.logic Require Import logatom.

Require Import iris.prelude.options.

Local Open Scope Z_scope.

(** * Abstract State Specs, similar to Cosmo style. *)
(** abstract state of stack *)
Definition stack := list (Z * view).

Implicit Type (S : stack) (N : namespace).

(** Stack predicates *)
Definition isStackT Σ : Type := namespace → gname → loc → vProp Σ.
Definition StackT Σ : Type := gname → loc → stack → vProp Σ.

(** Operation specs *)
Definition new_stack_spec' {Σ} `{!noprolG Σ}
  (new_stack : val) (isStack : isStackT Σ) (Stack : StackT Σ) : Prop :=
  ∀ N tid,
  {{{ True }}}
    new_stack [] @ tid; ⊤
  {{{ γs (s: loc), RET #s; isStack N γs s ∗ Stack γs s [] }}}.

Definition push_spec' {Σ} `{!noprolG Σ}
  (push : val) (isStack : isStackT Σ) (Stack : StackT Σ) : Prop :=
  ∀ N (DISJ: N ## histN) (s : loc) tid γs (V : view) (v : Z) (Posx: 0 < v),
  (* PRIVATE PRE *)
  ⊒V -∗ isStack N γs s -∗
  (* PUBLIC PRE *)
  <<< ∀ S, ▷ Stack γs s S >>>
    push [ #s ; #v] @ tid; ↑N
  <<< ∃ V' S',
      (* PUBLIC POST *)
      ▷ Stack γs s S' ∗
      ⊒V' ∗
      ⌜ V ⊑ V' ∧ S' = (v, V') :: S ⌝,
      (* RETURN VALUE AT COMMITTING POINT *)
      RET #☠, emp >>>
  .

Definition pop_spec' {Σ} `{!noprolG Σ}
  (pop : val) (isStack : isStackT Σ) (Stack : StackT Σ) : Prop :=
  ∀ N (DISJ: N ## histN) (s : loc) tid γs V,
  (* PRIVATE PRE *)
  ⊒V -∗ isStack N γs s -∗
  (* PUBLIC PRE *)
  <<< ∀ S, ▷ Stack γs s S >>>
    pop [ #s] @ tid; ↑N
  <<< ∃ (v: Z) V' S',
      (* PUBLIC POST *)
      ▷ Stack γs s S' ∗
      ⊒V' ∗
      ⌜ ( (* EMPTY case *)
          ( S' = S ∧ v = 0 )
        ∨ (* successful case *)
          ( S = (v, V') :: S' ∧ 0 < v ) ) ⌝,
      (* RETURN VALUE AT COMMITTING POINT *)
      RET #v, emp >>>
  .


Definition try_push_spec' {Σ} `{!noprolG Σ}
  (try_push : val) (isStack : isStackT Σ) (Stack : StackT Σ) : Prop :=
  ∀ N (DISJ: N ## histN) (s : loc) tid γs (V : view) (v : Z) (Posx: 0 < v),
  (* PRIVATE PRE *)
  ⊒V -∗ isStack N γs s -∗
  (* PUBLIC PRE *)
  <<< ∀ S, ▷ Stack γs s S >>>
    try_push [ #s ; #v] @ tid; ↑N
  <<< ∃ (b: bool) V' S',
      (* PUBLIC POST *)
      ▷ (Stack γs s S') ∗
      ⊒V' ∗
      ⌜ V ⊑ V' ∧
          if b is false then
            S' = S
          else
            S' = (v, V') :: S ⌝,
      (* RETURN VALUE AT COMMITTING POINT *)
      RET #b, emp >>>
  .

Definition try_pop_spec' {Σ} `{!noprolG Σ}
  (try_pop : val) (isStack : isStackT Σ) (Stack : StackT Σ) : Prop :=
  ∀ N (DISJ: N ## histN) (s : loc) tid γs V,
  (* PRIVATE PRE *)
  ⊒V -∗ isStack N γs s -∗
  <<< (* PUBLIC PRE *)
      ∀ S, ▷ (Stack γs s S) >>>
    try_pop [ #s] @ tid; ↑N
  <<< ∃ (v: Z) V' S',
      (* PUBLIC POST *)
      ▷ (Stack γs s S') ∗
      ⊒V' ∗
      ⌜ (* FAIL case *)
        ( ( S' = S ∧ v < 0 )
        ∨ (* EMPTY case *)
          ( S' = S ∧ v = 0 )
        ∨ (* successful case *)
          ( S = (v, V') :: S' ∧ 0 < v ) ) ⌝,
      (* RETURN VALUE AT COMMITTING POINT *)
      RET #v, emp >>>
  .

Record stack_spec {Σ} `{!noprolG Σ} := StackSpec {
  (* operations *)
  new_stack : val;
  push : val;
  pop : val;
  try_push : val;
  try_pop : val;

  (* predicates *)
  isStack : isStackT Σ;
  Stack : StackT Σ;

  (** predicates properties *)
  Stack_Timeless : ∀ γs s S, Timeless (Stack γs s S);
  Stack_Objective : ∀ γs s S, Objective (Stack γs s S);
  isStack_Persistent :
    ∀ N γs s, Persistent (isStack N γs s);

  (* operations specs *)
  new_stack_spec : new_stack_spec' new_stack isStack Stack;
  push_spec : push_spec' push isStack Stack;
  pop_spec : pop_spec' pop isStack Stack;
  try_push_spec : try_push_spec' try_push isStack Stack;
  try_pop_spec : try_pop_spec' try_pop isStack Stack;
}.

Arguments stack_spec _ {_}.

