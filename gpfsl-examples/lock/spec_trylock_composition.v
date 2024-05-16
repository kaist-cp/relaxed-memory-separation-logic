From gpfsl.logic Require Import proofmode invariants logatom.


From iris.prelude Require Import options.

From gpfsl.examples.omo Require Export omo omo_preds append_only_loc.

Require Import iris.prelude.options.

#[local] Open Scope Z_scope.


Inductive lock_event_type := Init | Lock | Trylock | Unlock.
Global Instance lock_event_type_inhabited : Inhabited lock_event_type := populate Init.

Definition lock_state := (event_id * bool * view * eView)%type. (* true if locked *)

#[local] Notation history := (history lock_event_type).
Implicit Types (E: history) (lock: lock_state).


Inductive lock_step : event_id → (omo_event lock_event_type) → lock_state → lock_state → Prop :=
  | lock_step_Lock e_lock eV_lock e_unlock V lV
      (LOCK: eV_lock.(type) = Lock)
      (SYNC: V ⊑ eV_lock.(sync))
      (EVIEW: ({[e_lock; e_unlock]} ∪ lV) ⊆ eV_lock.(eview))
      : lock_step e_lock eV_lock (e_unlock, false, V, lV) (e_lock, true, eV_lock.(sync), eV_lock.(eview))
  | lock_step_Unlock e_unlock eV_unlock e_lock V lV
      (UNLOCK: eV_unlock.(type) = Unlock)
      (SYNC: V ⊑ eV_unlock.(sync))
      (EVIEW: ({[e_lock; e_unlock]} ∪ lV) ⊆ eV_unlock.(eview))
      : lock_step e_unlock eV_unlock (e_lock, true, V, lV) (e_unlock, false, eV_unlock.(sync), eV_unlock.(eview))
  | lock_step_Trylock e_trylock eV_trylock e_unlock V lV
      (TRYLOCK: eV_trylock.(type) = Trylock)
      (EVIEW: e_trylock ∈ eV_trylock.(eview))
      : lock_step e_trylock eV_trylock (e_unlock, true, V, lV) (e_unlock, true, V, lV)
  | lock_step_Init eV
      (INIT: eV.(type) = Init)
      (EVIEW: eV.(eview) = {[ 0%nat ]})
       : lock_step 0%nat eV (0%nat, false, ∅, ∅) (0%nat, false, eV.(sync), eV.(eview))
  .

#[global] Instance lock_interpretable: Interpretable lock_event_type lock_state :=
  {
    init := (0%nat, false, ∅, ∅);
    step := lock_step
  }.



Definition LockLocalT Σ: Type :=
  ∀ (γg: gname) (l:loc) (M: eView), vProp Σ.
Definition LockLocalNT Σ: Type :=
  ∀ (N: namespace), LockLocalT Σ.
Definition LockInvT Σ : Type :=
  ∀ (γg γs: gname) (l: loc) (E: history) (omo : omoT) (stlist : list lock_state) (P: vProp Σ),  vProp Σ.
Definition LockedT Σ: Type := gname → loc → vProp Σ.

Section spec.

Context `{!noprolG Σ}.

Definition new_lock_spec' {Σ} `{!noprolG Σ, !omoGeneralG Σ}
  (new_lock : val) (LockLocal : LockLocalNT Σ) (LockInv : LockInvT Σ) : Prop :=
  ∀ N tid V P,
  {{{ ⊒V ∗ ▷ P }}}
    new_lock [] @ tid; ⊤
  {{{ γg γs (l: loc) V' M, RET #l;
      let eVinit := mkOmoEvent Init V' M in
      let E := [eVinit] in
      let omo := omo_append_w [] 0%nat [] in
      let st : lock_state := (0%nat, false, V', M) in
      ⊒V' ∗ LockInv γg γs l E omo [st] P ∗ @{V'} LockLocal N γg l M ∗
      OmoTokenW γg 0%nat ∗
      ⌜ V ⊑ V' ⌝}}}.

Definition do_lock_spec' {Σ} `{!noprolG Σ, !omoGeneralG Σ}
  (do_lock : val) (LockLocal : LockLocalNT Σ) (LockInv : LockInvT Σ) (Locked : LockedT Σ) : Prop :=
  ∀ N (DISJ: N ## histN) (l: loc) tid γg M (V : view),
  (* PRIVATE PRE *)
  ⊒V -∗ LockLocal N γg l M -∗
  (* PUBLIC PRE *)
  <<< ∀ γs E omo stlist P, ▷ LockInv γg γs l E omo stlist P >>>
    do_lock [ #l] @ tid; ↑N
  <<< ∃ V' st M',
      let eVop := mkOmoEvent Lock V' M' in
      let E' := E ++ [eVop] in
      let omo' := omo_append_w omo (length E) [] in
      (* PUBLIC POST *)
      ⊒V' ∗ ▷ LockInv γg γs l E' omo' (stlist ++ [st]) P ∗ @{V'} LockLocal N γg l M' ∗
      OmoTokenW γg (length E) ∗ OmoUB γg M (length E) ∗
      ⌜ V ⊑ V' ∧ M ⊑ M' ⌝,
      RET #☠, P ∗ Locked γg l >>>
  .

Definition try_lock_spec' {Σ} `{!noprolG Σ, !omoGeneralG Σ}
  (try_lock : val) (LockLocal : LockLocalNT Σ) (LockInv : LockInvT Σ) (Locked : LockedT Σ) : Prop :=
  ∀ N (DISJ: N ## histN) (l: loc) tid γg M (V : view),
  (* PRIVATE PRE *)
  ⊒V -∗ LockLocal N γg l M -∗
  (* PUBLIC PRE *)
  <<< ∀ γs E omo stlist P, ▷ LockInv γg γs l E omo stlist P >>>
    try_lock [ #l] @ tid; ↑N
  <<< ∃ (b: bool) V' op omo' stlist' M',
      let eVop := mkOmoEvent op V' M' in
      let E' := E ++ [eVop] in
      (* PUBLIC POST *)
      ⊒V' ∗ ▷ LockInv γg γs l E' omo' stlist' P ∗ @{V'} LockLocal N γg l M' ∗
      OmoUB γg M (length E) ∗ ⌜ V ⊑ V' ∧ M ⊆ M' ⌝ ∗
      if b then ( (* try_lock success *)
        ⌜ op = Lock ∧ omo' = omo_append_w omo (length E) [] ∧ (∃ st, stlist' = stlist ++ [st]) ⌝ ∗
        OmoTokenW γg (length E)
      ) else ( (* try_lock fail *)
        ⌜ op = Trylock ∧ (∃ gen, omo' = omo_insert_r omo gen (length E)) ∧ stlist' = stlist ⌝ ∗
        OmoTokenR γg (length E)
      ),
      RET #b, if b then (P ∗ Locked γg l) else emp >>>
  .

Definition unlock_spec' {Σ} `{!noprolG Σ, !omoGeneralG Σ}
  (unlock : val) (LockLocal : LockLocalNT Σ) (LockInv : LockInvT Σ) (Locked : LockedT Σ) : Prop :=
  ∀ N (DISJ: N ## histN) (l: loc) tid γg M (V : view) (P : vProp Σ),
  (* PRIVATE PRE *)
  ⊒V -∗ LockLocal N γg l M -∗ P -∗ Locked γg l -∗
  (* PUBLIC PRE *)
  <<< ∀ γs E omo stlist, ▷ LockInv γg γs l E omo stlist P >>>
    unlock [ #l] @ tid; ↑N
  <<< ∃ V' st M',
      let eVop := mkOmoEvent Unlock V' M' in
      let E' := E ++ [eVop] in
      let omo' := omo_append_w omo (length E) [] in
      (* PUBLIC POST *)
      ⊒V' ∗ ▷ LockInv γg γs l E' omo' (stlist ++ [st]) P ∗ @{V'} LockLocal N γg l M' ∗
      OmoTokenW γg (length E) ∗ OmoUB γg M (length E) ∗
      ⌜ V ⊑ V' ∧ M ⊑ M' ⌝,
      RET #☠, emp >>>
  .

End spec.

Record lock_spec {Σ} `{!noprolG Σ, !omoGeneralG Σ, !omoSpecificG Σ lock_event_type lock_state} : Type := LockSpec {
  new_lock : val;
  do_lock : val;
  try_lock : val;
  unlock : val;

  LockLocal: LockLocalNT Σ;
  LockInv: LockInvT Σ;
  Locked: LockedT Σ;

  LockInv_Objective: ∀ γg γs l E omo stlist P, Objective (LockInv γg γs l E omo stlist P);
  LockInv_Linearizable : ∀ γg γs l E omo stlist P, LockInv γg γs l E omo stlist P ⊢ ⌜ Linearizability_omo E omo stlist ⌝;
  LockInv_OmoAuth_acc : ∀ γg γs l E omo stlist P,
    LockInv γg γs l E omo stlist P ⊢ OmoAuth γg γs 1 E omo stlist _ ∗ (OmoAuth γg γs 1 E omo stlist _ -∗ LockInv γg γs l E omo stlist P);
  LockLocal_OmoEview : ∀ N γg l M, LockLocal N γg l M ⊢ OmoEview γg M;
  LockLocal_Persistent :
    ∀ N γg l M, Persistent (LockLocal N γg l M);

  new_lock_spec: new_lock_spec' new_lock LockLocal LockInv;
  do_lock_spec: do_lock_spec' do_lock LockLocal LockInv Locked;
  try_lock_spec: try_lock_spec' try_lock LockLocal LockInv Locked;
  unlock_spec: unlock_spec' unlock LockLocal LockInv Locked;
}.

#[global] Arguments lock_spec _ {_ _ _} : assert.

#[global] Existing Instances LockInv_Objective LockLocal_Persistent.
