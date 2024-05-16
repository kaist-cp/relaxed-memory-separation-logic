From gpfsl.examples Require Import sflib.

From stdpp Require Import namespaces.

From gpfsl.logic Require Import logatom.

From gpfsl.examples.stack Require Export stack_event_omo.
From gpfsl.examples.omo Require Export omo omo_preds append_only_loc.

Require Import iris.prelude.options.

Local Open Scope Z_scope.

Local Notation history := (history sevent_hist).
Implicit Types (E : history) (stk : stack_state).

Local Notation EMPTY := 0 (only parsing).
Local Notation FAIL_RACE := (-1) (only parsing).

Definition StackLocalT Σ : Type :=
  ∀ (γg : gname) (s : loc) (M : eView), vProp Σ.
Definition StackLocalNT Σ : Type :=
  ∀ (N : namespace), StackLocalT Σ.
Definition StackInvT Σ : Type :=
  ∀ (γg γs : gname) (s : loc) (E : history) (omo : omoT) (stlist : list stack_state), vProp Σ.

Definition new_stack_spec' {Σ} `{!noprolG Σ, !omoGeneralG Σ}
  (new_stack : val) (StackLocal : StackLocalNT Σ) (StackInv : StackInvT Σ) : Prop :=
  ∀ N tid V,
  {{{ ⊒V }}}
    new_stack [] @ tid; ⊤
  {{{ γg γs (s: loc) M V', RET #s;
      let eVinit := mkOmoEvent Init V' M in
      let E := [eVinit] in
      let stinit : stack_state := [] in
      ⊒V' ∗ StackInv γg γs s E (omo_append_w [] 0%nat []) [stinit] ∗ @{V'} StackLocal N γg s M ∗
      OmoTokenW γg 0%nat ∗
      ⌜ V ⊑ V' ⌝}}}.

Definition try_push_spec' {Σ} `{!noprolG Σ, !omoGeneralG Σ}
  (try_push : val) (StackLocal : StackLocalNT Σ) (StackInv : StackInvT Σ) : Prop :=
  ∀ N (DISJ: N ## histN) (s: loc) tid γg M (V : view) (v : Z) (Posx: 0 < v),
  (* PRIVATE PRE *)
  ⊒V -∗ StackLocal N γg s M -∗
  (* PUBLIC PRE *)
  <<< ∀ γs E omo stlist, ▷ StackInv γg γs s E omo stlist >>>
    try_push [ #s ; #v] @ tid; ↑N
  <<< ∃ (b: bool) V' γs' E' omo' stlist' M',
      (* PUBLIC POST *)
      ⊒V' ∗ ▷ StackInv γg γs' s E' omo' stlist' ∗ @{V'} StackLocal N γg s M' ∗
      if b then (
        (* successful case *)
        ⌜ E' = E ++ [mkOmoEvent (Push v) V' M']
        ∧ (∃ gen, omo' = omo_insert_w omo gen (length E) [])
        ∧ V ⊑ V' ∧ M ⊆ M' ⌝ ∗
        OmoUB γg M (length E) ∗
        OmoTokenW γg (length E)
      ) else (
        (* FAIL_RACE case *)
        ⌜ γs' = γs ∧ E' = E ∧ omo' = omo ∧ stlist' = stlist ∧ M' = M ⌝
      ),
      RET #b, emp >>>
  .

Definition push_spec' {Σ} `{!noprolG Σ, !omoGeneralG Σ}
  (push : val) (StackLocal : StackLocalNT Σ) (StackInv : StackInvT Σ) : Prop :=
  ∀ N (DISJ: N ## histN) (s: loc) tid γg M (V : view) (v : Z) (Posx: 0 < v),
  (* PRIVATE PRE *)
  ⊒V -∗ StackLocal N γg s M -∗
  (* PUBLIC PRE *)
  <<< ∀ γs E omo stlist, ▷ StackInv γg γs s E omo stlist >>>
    push [ #s ; #v] @ tid; ↑N
  <<< ∃ V' γs' omo' stlist' M',
      (* PUBLIC POST *)
      let eVpush := mkOmoEvent (Push v) V' M' in
      let E' := E ++ [eVpush] in
      ⊒V' ∗ ▷ StackInv γg γs' s E' omo' stlist' ∗ @{V'} StackLocal N γg s M' ∗
      OmoUB γg M (length E) ∗
      OmoTokenW γg (length E) ∗
      ⌜ (∃ gen, omo' = omo_insert_w omo gen (length E) [])
      ∧ V ⊑ V' ∧ M ⊆ M' ⌝,
      RET #☠, emp >>>
  .

Definition try_pop_spec' {Σ} `{!noprolG Σ, !omoGeneralG Σ}
  (try_pop : val) (StackLocal : StackLocalNT Σ) (StackInv : StackInvT Σ) : Prop :=
  ∀ N (DISJ: N ## histN) (s: loc) tid γg M V,
  (* PRIVATE PRE *)
  ⊒V -∗ StackLocal N γg s M -∗
  (* PUBLIC PRE *)
  <<< ∀ γs E omo stlist, ▷ StackInv γg γs s E omo stlist >>>
    try_pop [ #s] @ tid; ↑N
  <<< ∃ (v : Z) V' γs' E' omo' stlist' M',
      (* PUBLIC POST *)
      ⊒V' ∗ ▷ StackInv γg γs' s E' omo' stlist' ∗ @{V'} StackLocal N γg s M' ∗
      if (decide (v = FAIL_RACE)) then (
        (* FAIL_RACE case *)
        ⌜ γs' = γs ∧ E' = E ∧ omo' = omo ∧ stlist' = stlist ∧ M' = M ⌝
      ) else (
        ⌜ V ⊑ V' ∧ M ⊆ M' ⌝ ∗
        OmoUB γg M (length E) ∗
        if (decide (v = EMPTY)) then ( (* EMPTY case *)
          ⌜ E' = E ++ [mkOmoEvent EmpPop V' M'] ∧ stlist' = stlist ∧ γs' = γs
          ∧ (∃ gen, omo' = omo_insert_r omo gen (length E) ∧ (gen < length omo)%nat) ⌝  ∗
          OmoTokenR γg (length E)
        ) else ( (* successful case *)
          ⌜ E' = E ++ [mkOmoEvent (Pop v) V' M'] ∧ (∃ gen, omo' = omo_insert_w omo gen (length E) []) ⌝ ∗
          OmoTokenW γg (length E)
        )
      ),
      RET #v , emp >>>
  .

Definition pop_spec' {Σ} `{!noprolG Σ, !omoGeneralG Σ}
  (pop : val) (StackLocal : StackLocalNT Σ) (StackInv : StackInvT Σ) : Prop :=
  ∀ N (DISJ: N ## histN) (s: loc) tid γg M V,
  (* PRIVATE PRE *)
  ⊒V -∗ StackLocal N γg s M -∗
  (* PUBLIC PRE *)
  <<< ∀ γs E omo stlist, ▷ StackInv γg γs s E omo stlist >>>
    pop [ #s] @ tid; ↑N
  <<< ∃ (v : Z) V' γs' E' omo' stlist' M',
      (* PUBLIC POST *)
      ⊒V' ∗ ▷ StackInv γg γs' s E' omo' stlist' ∗ @{V'} StackLocal N γg s M' ∗
      ⌜ V ⊑ V' ∧ M ⊆ M' ⌝ ∗
      OmoUB γg M (length E) ∗
      if (decide (v = EMPTY)) then ( (* EMPTY case *)
        ⌜ E' = E ++ [mkOmoEvent EmpPop V' M'] ∧ stlist' = stlist ∧ γs' = γs
        ∧ (∃ gen, omo' = omo_insert_r omo gen (length E) ∧ (gen < length omo)%nat) ⌝ ∗
        OmoTokenR γg (length E)
      ) else ( (* successful case *)
        ⌜ E' = E ++ [mkOmoEvent (Pop v) V' M'] ∧ (∃ gen, omo' = omo_insert_w omo gen (length E) []) ⌝ ∗
        OmoTokenW γg (length E)
      ),
      RET #v, emp >>>
  .

Record stack_spec {Σ} `{!noprolG Σ, !omoGeneralG Σ, !omoSpecificG Σ sevent_hist stack_state} := StackSpec {
  (** operations *)
  new_stack : val;
  try_push : val;
  push : val;
  try_pop : val;
  pop : val;

  (** These are common elements in arbitrary composable linearizability spec *)
  (** predicates *)
  StackLocal : StackLocalNT Σ;
  StackInv : StackInvT Σ;

  (** predicates properties *)
  StackInv_Objective : ∀ γg γs s E omo stlist, Objective (StackInv γg γs s E omo stlist);
  StackInv_Timeless : ∀ γg γs s E omo stlist, Timeless (StackInv γg γs s E omo stlist);
  StackInv_Linearizable : ∀ γg γs s E omo stlist, StackInv γg γs s E omo stlist ⊢ ⌜ Linearizability_omo E omo stlist ⌝;
  StackInv_OmoAuth_acc : ∀ γg γs s E omo stlist,
    StackInv γg γs s E omo stlist ⊢ OmoAuth γg γs (1/2)%Qp E omo stlist _ ∗ (OmoAuth γg γs (1/2)%Qp E omo stlist _ -∗ StackInv γg γs s E omo stlist);
  StackLocal_OmoEview : ∀ N γg s M, StackLocal N γg s M ⊢ OmoEview γg M;
  StackLocal_Eview_update : ∀ N γg s M1 M2, StackLocal N γg s M1 -∗ OmoEview γg M2 -∗ StackLocal N γg s (M1 ∪ M2);
  StackLocal_Persistent :
    ∀ N γg s M, Persistent (StackLocal N γg s M);
  (**************************************************************)

  (* operations specs *)
  new_stack_spec : new_stack_spec' new_stack StackLocal StackInv;
  try_push_spec : try_push_spec' try_push StackLocal StackInv;
  push_spec : push_spec' push StackLocal StackInv;
  try_pop_spec : try_pop_spec' try_pop StackLocal StackInv;
  pop_spec : pop_spec' pop StackLocal StackInv;
}.

Arguments stack_spec _ {_ _ _}.
Global Existing Instances StackInv_Objective StackInv_Timeless StackLocal_Persistent.
