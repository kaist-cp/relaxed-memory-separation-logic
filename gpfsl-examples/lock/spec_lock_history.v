From gpfsl.logic Require Import proofmode invariants logatom.


From iris.prelude Require Import options.

From gpfsl.examples.omo Require Export omo omo_preds append_only_loc.

Require Import iris.prelude.options.

#[local] Open Scope Z_scope.


Inductive lock_event_hist := Init | Lock | Unlock.
Global Instance lock_event_hist_inhabited : Inhabited lock_event_hist := populate Init.

Definition lock_state := (event_id * bool * view * eView)%type. (* true if locked *)

#[local] Notation history := (history lock_event_hist).
Implicit Types (E: history) (lock: lock_state).


Inductive lock_step : event_id → (omo_event lock_event_hist) → lock_state → lock_state → Prop :=
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
  | lock_step_Init eV
      (INIT: eV.(type) = Init)
      (EVIEW: eV.(eview) = {[ 0%nat ]})
       : lock_step 0%nat eV (0%nat, false, ∅, ∅) (0%nat, false, eV.(sync), eV.(eview))
  .

#[global] Instance lock_interpretable: Interpretable lock_event_hist lock_state :=
  {
    init := (0%nat, false, ∅, ∅);
    step := lock_step
  }.



Definition LockLocalT Σ: Type :=
  ∀ (γ: gname) (l:loc) (E: history) (M: eView), vProp Σ.
Definition LockLocalNT Σ: Type :=
  ∀ (N: namespace), LockLocalT Σ.
Definition LockInvT Σ : Type :=
  ∀ (γ: gname) (l: loc) (P: vProp Σ) (E: history),  vProp Σ.
Definition LockedT Σ: Type := gname → loc → vProp Σ.

Section spec.

Context `{!noprolG Σ}.

Local Notation iProp := (iProp Σ).
Local Notation vProp := (vProp Σ).

Variables
  (new_lock : val)
  (do_lock : val)
  (unlock : val).
Variables
  (LockInv: LockInvT Σ)
  (LockLocal: LockLocalNT Σ)
  (Locked: LockedT Σ).


Definition new_lock_spec' : Prop :=
  ∀ N P tid,
  {{{ ▷ P }}}
    new_lock [] @ tid; ⊤
  {{{ (l: loc) (γ: gname) V M E, RET #l;
      ⊒V ∗ @{V} LockLocal N γ l E M ∗ LockInv γ l P E
      ∗ ⌜ E = [mkOmoEvent Init V M] ⌝
  }}}.


Definition do_lock_spec' : Prop :=
  ∀ N (DISJ: N ## histN) γ (l: loc) (P: vProp) tid V M E1,
  ⊒V -∗ LockLocal N γ l E1 M -∗
  <<< ∀ E, ▷ LockInv γ l P E >>>
    do_lock [ #l ] @ tid; ⊤
  <<< ∃ V' E' M',
    ▷ LockInv γ l P E' ∗
    ⊒V' ∗ @{V'} LockLocal N γ l E' M' ∗
    ⌜ V ⊑ V' ∧
      E' = E ++ [mkOmoEvent Lock V' M'] ∧ M ⊆ M' ⌝
    , RET  #☠, P ∗ Locked γ l >>>.


Definition unlock_spec' : Prop :=
  ∀ N (DISJ: N ## histN) γ (l: loc) (P: vProp) tid V M E1,
  ⊒V -∗ LockLocal N γ l E1 M -∗ P -∗ Locked γ l -∗
  <<< ∀ E, ▷ LockInv γ l P E >>>
    unlock [ #l ] @ tid; ⊤
  <<< ∃ V' E' M',
      ▷ LockInv γ l P E' ∗
      ⊒V' ∗ @{V'} LockLocal N γ l E' M' ∗
      ⌜ V ⊑ V' ∧
        E' = E ++ [mkOmoEvent Unlock V' M'] ∧ M ⊆ M' ⌝
      , RET #☠, True >>>.

End spec.

Record lock_spec {Σ} `{!noprolG Σ} : Type := LockSpec {
  new_lock : val;
  do_lock : val;
  unlock : val;

  LockLocal: LockLocalNT Σ;
  LockInv: LockInvT Σ;
  Locked: LockedT Σ;

  LockInv_Objective: ∀ γ l P E, Objective (LockInv γ l P E);
  (* LockInv_Timeless: ∀ γ l P E, Timeless (LockInv γ l P E); *)
  LockInv_Linearizable:
      ∀ γ l P E, LockInv γ l P E ⊢ ⌜ Linearizability E ⌝;
  LockInv_history_wf:
      ∀ γ l P E, LockInv γ l P E ⊢ ⌜ history_wf E ⌝;

  LockInv_LockLocal:
      ∀ N γ l P E E' M',
          LockInv γ l P E -∗ LockLocal N γ l E' M' -∗ ⌜ E' ⊑ E ⌝;
  LockLocal_lookup:
      ∀ N γ l E M e V,
          sync <$> E !! e = Some V → e ∈ M → LockLocal N γ l E M -∗ ⊒V;
  LockLocal_Persistent : ∀ N γ l E M, Persistent (LockLocal N γ l E M);

  new_lock_spec: new_lock_spec' new_lock LockInv LockLocal;
  do_lock_spec: do_lock_spec' do_lock LockInv LockLocal Locked;
  unlock_spec: unlock_spec' unlock LockInv LockLocal Locked;
}.

#[global] Arguments lock_spec : clear implicits.
#[global] Arguments lock_spec _ {_} : assert.

#[global] Existing Instances LockInv_Objective LockLocal_Persistent.

