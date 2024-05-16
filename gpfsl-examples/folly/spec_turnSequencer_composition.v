From gpfsl.examples Require Import sflib.

From stdpp Require Import namespaces.

From gpfsl.logic Require Import logatom.

From gpfsl.examples.stack Require Export event.
From gpfsl.examples.omo Require Export omo omo_preds append_only_loc.

Require Import iris.prelude.options.

Local Open Scope nat_scope.

Inductive tseq_event := Init | Take (n : nat) | Complete (n : nat).
Definition tseq_state := (event_id * nat * view * eView)%type.
Global Instance tseq_event_inhabited : Inhabited tseq_event := populate Init.

Local Notation history := (history tseq_event).
Implicit Types (E : history) (st : tseq_state).

Inductive tseq_step : ∀ (e : event_id) (eV : omo_event tseq_event) st st', Prop :=
  | tseq_step_Take e eV v e' V' lV'
    (TAKE : eV.(type) = Take v)
    (LEQ : 0 ≤ v)
    (SYNC : V' ⊑ eV.(sync))
    (EVIEW : {[e; e']} ∪ lV' ⊆ eV.(eview))
    : tseq_step e eV (e', v, V', lV') (e', v, V', lV')
  | tseq_step_Complete e eV v e' V' lV'
    (COMPLETE : eV.(type) = Complete v)
    (LEQ : 0 ≤ v)
    (SYNC : V' ⊑ eV.(sync))
    (EVIEW : {[e; e']} ∪ lV' ⊆ eV.(eview))
    : tseq_step e eV (e', v, V', lV') (e, v + 1, eV.(sync), eV.(eview))
  | tseq_step_Init eV
    (INIT : eV.(type) = Init)
    (EVIEW : eV.(eview) = {[0%nat]})
    : tseq_step 0%nat eV (0%nat, 0, ∅, ∅) (0%nat, 0, eV.(sync), eV.(eview))
  .

Global Instance tseq_interpretable : Interpretable tseq_event tseq_state :=
  {
    init := (0%nat, 0, ∅, ∅);
    step := tseq_step
  }.

Definition TSeqLocalT Σ : Type :=
  ∀ (γg : gname) (l : loc) (M : eView), vProp Σ.
Definition TSeqLocalNT Σ : Type :=
  ∀ (N : namespace), TSeqLocalT Σ.
Definition TSeqInvT Σ : Type :=
  ∀ (γg γs : gname) (l : loc) (E : history) (omo : omoT) (stlist : list tseq_state) (R : nat → vProp Σ), vProp Σ.
Definition TSeqPermT Σ : Type :=
  ∀ (γg : gname) (l : loc) (P : nat → bool), vProp Σ.
Definition TSeqCompleteT Σ : Type :=
  ∀ (γg : gname) (l : loc) (n : nat), vProp Σ.

Definition new_tseq_spec' {Σ} `{!noprolG Σ, !omoGeneralG Σ}
  (newTS : val) (TSeqLocal : TSeqLocalNT Σ) (TSeqInv : TSeqInvT Σ) (TSeqPerm : TSeqPermT Σ) : Prop :=
  ∀ N tid V R,
  {{{ ⊒V ∗ ▷ (R 0%nat) }}}
    newTS [] @ tid; ⊤
  {{{ γg γs (l: loc) M V', RET #l;
      let eVinit := mkOmoEvent Init V' M in
      let E := [eVinit] in
      let stinit := (0%nat, 0, eVinit.(sync), eVinit.(eview)) in
      ⊒V' ∗ @{V'} TSeqLocal N γg l M ∗
      TSeqInv γg γs l E (omo_append_w [] 0%nat []) [stinit] R ∗
      OmoTokenW γg 0%nat ∗
      TSeqPerm γg l (λ _, true) ∗
      ⌜ V ⊑ V' ⌝ }}}.

Definition wait_spec' {Σ} `{!noprolG Σ, !omoGeneralG Σ}
  (waitForTurn : val) (TSeqLocal : TSeqLocalNT Σ) (TSeqInv : TSeqInvT Σ) (TSeqPerm : TSeqPermT Σ) (TSeqComplete : TSeqCompleteT Σ) : Prop :=
  ∀ N (DISJ: N ## histN) (l: loc) tid γg γs M (V : view) (n : nat) (R : nat → vProp Σ),
  (* PRIVATE PRE *)
  ⊒V -∗ TSeqLocal N γg l M -∗ TSeqPerm γg l (λ m, m =? n) -∗
  (* PUBLIC PRE *)
  <<< ∀ E omo stlist, ▷ TSeqInv γg γs l E omo stlist R >>>
    waitForTurn [ #l; #n] @ tid; ↑N
  <<< ∃ V' M',
      (* PUBLIC POST *)
      let eVwait := mkOmoEvent (Take n) V' M' in
      let E' := E ++ [eVwait] in
      let waitId := length E in
      let gen := length omo - 1 in
      let omo' := omo_insert_r omo gen waitId in
      ▷ TSeqInv γg γs l E' omo' stlist R ∗ OmoTokenR γg waitId ∗
      ⊒V' ∗ @{V'} TSeqLocal N γg l M' ∗
      ⌜ V ⊑ V' ∧ M ⊆ M' ⌝,
      RET #☠, R n ∗ TSeqComplete γg l n >>>
  .

Definition complete_spec' {Σ} `{!noprolG Σ, !omoGeneralG Σ}
  (completeTurn : val) (TSeqLocal : TSeqLocalNT Σ) (TSeqInv : TSeqInvT Σ) (TSeqComplete : TSeqCompleteT Σ) : Prop :=
  ∀ N (DISJ: N ## histN) (l: loc) tid γg γs M (V : view) (n : nat) (R : nat → vProp Σ),
  (* PRIVATE PRE *)
  ⊒V -∗ TSeqLocal N γg l M -∗ R (n + 1)%nat -∗ TSeqComplete γg l n -∗
  (* PUBLIC PRE *)
  <<< ∀ E omo stlist, ▷ TSeqInv γg γs l E omo stlist R >>>
    completeTurn [ #l; #n] @ tid; ↑N
  <<< ∃ V' M',
      let eVcomp := mkOmoEvent (Complete n) V' M' in
      let E' := E ++ [eVcomp] in
      let compId := length E in
      let omo' := omo_append_w omo compId [] in
      let st := (compId, n + 1, eVcomp.(sync), eVcomp.(eview)) in
      (* PUBLIC POST *)
      ▷ TSeqInv γg γs l E' omo' (stlist ++ [st]) R ∗ OmoTokenW γg compId ∗
      ⊒V' ∗ @{V'} TSeqLocal N γg l M' ∗
      ⌜ V ⊑ V' ∧ M ⊆ M' ⌝,
      RET #☠, emp >>>
  .

Record tseq_composition_spec {Σ} `{!noprolG Σ, !omoGeneralG Σ, !omoSpecificG Σ tseq_event tseq_state} := TSeqCompositionSpec {
  (** operations *)
  newTS : val;
  waitForTurn : val;
  completeTurn : val;

  (** These are common elements in arbitrary composable linearizability spec *)
  (** predicates *)
  TSeqLocal : TSeqLocalNT Σ;
  TSeqInv : TSeqInvT Σ;
  TSeqPerm : TSeqPermT Σ;
  TSeqComplete : TSeqCompleteT Σ;

  (** predicates properties *)
  TSeqInv_Objective : ∀ γg γs l E omo stlist R, Objective (TSeqInv γg γs l E omo stlist R);
  TSeqInv_Linearizable : ∀ γg γs l E omo stlist R, TSeqInv γg γs l E omo stlist R ⊢ ⌜ Linearizability_omo E omo stlist ⌝;
  TSeqInv_OmoAuth_acc : ∀ γg γs l E omo stlist R,
    TSeqInv γg γs l E omo stlist R ⊢ OmoAuth γg γs 1 E omo stlist _ ∗ (OmoAuth γg γs 1 E omo stlist _ -∗ TSeqInv γg γs l E omo stlist R);
  TSeqLocal_OmoEview : ∀ N γg l M, TSeqLocal N γg l M ⊢ OmoEview γg M;
  TSeqLocal_Persistent :
    ∀ N γg l M, Persistent (TSeqLocal N γg l M);

  TSeqPerm_Objective : ∀ γg l P, Objective (TSeqPerm γg l P);
  TSeqPerm_Equiv : ∀ γg l P1 P2, (∀ n, P1 n = P2 n) → TSeqPerm γg l P1 -∗ TSeqPerm γg l P2;
  TSeqPerm_Split : ∀ γg l P1 P2, TSeqPerm γg l P1 -∗ TSeqPerm γg l (λ n, P1 n && P2 n) ∗ TSeqPerm γg l (λ n, P1 n && negb (P2 n));
  TSeqPerm_Combine : ∀ γg l P1 P2, TSeqPerm γg l P1 -∗ TSeqPerm γg l P2 -∗ TSeqPerm γg l (λ n, P1 n || P2 n);
  TSeqPerm_Excl : ∀ γg l P1 P2 n, P1 n = true → P2 n = true → TSeqPerm γg l P1 -∗ TSeqPerm γg l P2 -∗ False;
  (**************************************************************)

  (* operations specs *)
  new_tseq_spec : new_tseq_spec' newTS TSeqLocal TSeqInv TSeqPerm;
  wait_spec : wait_spec' waitForTurn TSeqLocal TSeqInv TSeqPerm TSeqComplete;
  complete_spec : complete_spec' completeTurn TSeqLocal TSeqInv TSeqComplete;
}.

Arguments tseq_composition_spec _ {_ _ _}.
Global Existing Instances TSeqInv_Objective TSeqLocal_Persistent TSeqPerm_Objective.
