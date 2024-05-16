From gpfsl.examples Require Import sflib.

From stdpp Require Import namespaces.

From gpfsl.logic Require Import logatom.

From gpfsl.examples.stack Require Export stack_event_omo.
From gpfsl.examples.omo Require Export omo omo_preds append_only_loc.

From gpfsl.diaframe Require Import spec_notation atom_spec_notation.

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

Class new_stack_dspec' {Σ} `{!noprolG Σ, !omoGeneralG Σ}
  (new_stack : val) (StackLocal : StackLocalNT Σ) (StackInv : StackInvT Σ) : Prop :=
  new_stack_dspec'' :>
    SPEC N V, {{ ⊒V }}
      new_stack []
    {{ (s: loc) , RET #s;
      ∃ γg γs M V',
      let eVinit := mkOmoEvent Init V' M in
      let E := [eVinit] in
      let stinit : stack_state := [] in
      StackInv γg γs s E (omo_append_w [] 0%nat []) [stinit] ∗ ⊒V' ∗ @{V'} StackLocal N γg s M ∗
      OmoTokenW γg 0%nat ∗ ⌜ V ⊑ V' ⌝} }.

Class try_push_dspec' {Σ} `{!noprolG Σ, !omoGeneralG Σ}
  (try_push : val) (StackLocal : StackLocalNT Σ) (StackInv : StackInvT Σ) : Prop :=
  try_push_dspec'' :> ∀ N (s : loc) γg M (V : view) (v : Z),
    SPEC ⟨ ⊤ , ↑N , ↑histN⟩ γs E omo stlist, <<
      (* PRIVATE PRE *)
      ⊒V ∗
      StackLocal N γg s M ∗
      ⌜ 0 < v ∧ N ## histN ⌝
    ¦
      (* PUBLIC PRE *)
      ▷ StackInv γg γs s E omo stlist
    > >
      try_push [ #s ; #v]
    << (b : bool), RET #b;
      emp
    ¦
      ( (* PUBLIC POST *)
      ∃ V', ⊒V' ∗
      if b then (
        (* successful case *)
        ∃ γs' M' omo' stlist' gen,
        let E' := E ++ [mkOmoEvent (Push v) V' M'] in
        ▷ StackInv γg γs' s E' omo' stlist' ∗ @{V'} StackLocal N γg s M' ∗
        ⌜ omo' = omo_insert_w omo gen (length E) [] ⌝ ∗
        OmoTokenW γg (length E) ∗
        OmoUB γg M (length E) ∗
        ⌜ V ⊑ V' ∧ M ⊆ M' ⌝
      ) else (
        (* FAIL_RACE case *)
        ▷ StackInv γg γs s E omo stlist ∗ @{V'} StackLocal N γg s M
      ))
    > >.

Class push_dspec' {Σ} `{!noprolG Σ, !omoGeneralG Σ}
  (push : val) (StackLocal : StackLocalNT Σ) (StackInv : StackInvT Σ) : Prop :=
  push_dspec'' :>
    ∀ N (s: loc) γg M (V : view) (v : Z) ,
    SPEC ⟨ ⊤ , ↑N , ↑histN⟩ γs E omo stlist, <<
      (* PRIVATE PRE *)
      ⊒V ∗
      StackLocal N γg s M ∗
      ⌜ 0 < v ∧ N ## histN ⌝
    ¦
      (* PUBLIC PRE *)
      ▷ StackInv γg γs s E omo stlist
    > >
      push [ #s ; #v]
    << RET #☠;
      emp
    ¦
      ( (* PUBLIC POST *)
      ∃ V' γs' M' omo' stlist' gen,
        ⊒V' ∗
        let E' := E ++ [mkOmoEvent (Push v) V' M'] in
        ▷ StackInv γg γs' s E' omo' stlist' ∗ @{V'} StackLocal N γg s M' ∗
        ⌜ omo' = omo_insert_w omo gen (length E) [] ⌝ ∗
        OmoTokenW γg (length E) ∗
        OmoUB γg M (length E) ∗
        ⌜ V ⊑ V' ∧ M ⊆ M' ⌝
      )
    > >.


Class try_pop_dspec' {Σ} `{!noprolG Σ, !omoGeneralG Σ}
  (try_pop : val) (StackLocal : StackLocalNT Σ) (StackInv : StackInvT Σ) : Prop :=
  try_pop_dspec'' :>
    ∀ N (s: loc) γg M V,
    SPEC ⟨ ⊤ , ↑N , ↑histN⟩ γs E omo stlist, <<
      (* PRIVATE PRE *)
      ⊒V ∗
      StackLocal N γg s M ∗
      ⌜ N ## histN ⌝
    ¦
      (* PUBLIC PRE *)
      ▷ StackInv γg γs s E omo stlist
    > >
      try_pop [ #s ]
    << (v : Z), RET #v;
      emp
    ¦
      ( (* PUBLIC POST *)
      ∃ V', ⊒V' ∗
      if (decide (v = FAIL_RACE)) then (
        (* FAIL_RACE case *)
        ▷ StackInv γg γs s E omo stlist ∗ @{V'} StackLocal N γg s M
      )
      else (
        ∃ γs' M',
        ⌜ V ⊑ V' ⌝ ∗
        (if (decide (v = EMPTY)) then ( (* EMPTY case *)
          ∃ gen omo' stlist',
          let E' := E ++ [mkOmoEvent EmpPop V' M'] in
          ▷ StackInv γg γs' s E' omo' stlist' ∗ @{V'} StackLocal N γg s M' ∗
          ⌜ omo' = omo_insert_r omo gen (length E) ∧ (gen < length omo)%nat ∧ stlist' = stlist ∧ γs' = γs ⌝ ∗
          OmoTokenR γg (length E)
        ) else ( (* successful case *)
          ∃ gen omo' stlist',
          let E' := E ++ [mkOmoEvent (Pop v) V' M'] in
          ▷ StackInv γg γs' s E' omo' stlist' ∗ @{V'} StackLocal N γg s M' ∗
          ⌜ omo' = omo_insert_w omo gen (length E) [] ⌝ ∗
          OmoTokenW γg (length E)
        )) ∗
        OmoUB γg M (length E) ∗ ⌜ M ⊆ M' ⌝
      ))
    > >.

Class pop_dspec' {Σ} `{!noprolG Σ, !omoGeneralG Σ}
  (pop : val) (StackLocal : StackLocalNT Σ) (StackInv : StackInvT Σ) : Prop :=
  pop_dspec'' :>
    ∀ N (s: loc) γg M V,
    SPEC ⟨ ⊤ , ↑N , ↑histN⟩ γs E omo stlist, <<
      (* PRIVATE PRE *)
      ⊒V ∗
      StackLocal N γg s M ∗
      ⌜ N ## histN ⌝
    ¦
      (* PUBLIC PRE *)
      ▷ StackInv γg γs s E omo stlist
    > >
      pop [ #s ]
    << (v : Z), RET #v;
      emp
    ¦
      ( (* PUBLIC POST *)
      ∃ V', ⊒V' ∗
        ∃ γs' M',
        OmoUB γg M (length E) ∗ ⌜ V ⊑ V' ⌝ ∗
        if (decide (v = EMPTY)) then ( (* EMPTY case *)
          ∃ gen omo' stlist',
          let E' := E ++ [mkOmoEvent EmpPop V' M'] in
          ▷ StackInv γg γs' s E' omo' stlist' ∗ @{V'} StackLocal N γg s M' ∗
          ⌜ omo' = omo_insert_r omo gen (length E) ∧ (gen < length omo)%nat ∧ stlist' = stlist ∧ γs' = γs ⌝ ∗
          OmoTokenR γg (length E)
        ) else ( (* successful case *)
          ∃ gen omo' stlist',
          let E' := E ++ [mkOmoEvent (Pop v) V' M'] in
          ▷ StackInv γg γs' s E' omo' stlist' ∗ @{V'} StackLocal N γg s M' ∗
          ⌜ omo' = omo_insert_w omo gen (length E) [] ⌝ ∗
          OmoTokenW γg (length E)
        ) ∗
        ⌜ M ⊆ M' ⌝
      )
    > >.

Record stack_spec {Σ} `{!noprolG Σ, !omoGeneralG Σ, !omoSpecificG Σ sevent_hist stack_state} := StackSpec {
  (** operations *)
  new_stack : val;
  try_push : val;
  push : val;
  try_pop : val;
  pop : val;

  (** These are common elements in arbitrary history-style spec *)
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
  new_stack_dspec : new_stack_dspec' new_stack StackLocal StackInv;
  try_push_dspec : try_push_dspec' try_push StackLocal StackInv;
  push_dspec : push_dspec' push StackLocal StackInv;
  try_pop_dspec : try_pop_dspec' try_pop StackLocal StackInv;
  pop_dspec : pop_dspec' pop StackLocal StackInv;
}.

Arguments stack_spec _ {_ _ _}.
Global Existing Instances StackInv_Objective StackInv_Timeless StackLocal_Persistent
    new_stack_dspec try_push_dspec push_dspec try_pop_dspec pop_dspec.
