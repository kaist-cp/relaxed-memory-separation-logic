From gpfsl.logic Require Import proofmode invariants.


From iris.prelude Require Import options.


Definition LockedT Σ: Type := gname → vProp Σ.
Definition IsLockT Σ (N: namespace) : Type := gname → loc → vProp Σ → vProp Σ.


Section spec.

Context `{!noprolG Σ}.
Context (lockN : namespace).

Local Notation iProp := (iProp Σ).
Local Notation vProp := (vProp Σ).


Variables
  (new_lock : val)
  (do_lock : val)
  (unlock : val).
Variables
  (IsLock: IsLockT Σ lockN)
  (Locked: LockedT Σ).


Definition IsLock_persistent : Prop :=
  ∀ γ l P, Persistent (IsLock γ l P).

Definition new_lock_spec': Prop :=
  ∀ P tid,
  {{{ ▷ P }}}
    new_lock [] @ tid; ⊤
  {{{ (l: loc) (γ: gname), RET #l; IsLock γ l P}}}.

Definition do_lock_spec' : Prop :=
  ∀ γ (l: loc) (P: vProp) tid,
  {{{ IsLock γ l P }}}
    do_lock [ #l ] @ tid; ⊤
  {{{ RET  #☠; P ∗ Locked γ }}}.

Definition unlock_spec' : Prop :=
  ∀ γ (l: loc) (P: vProp) tid,
  {{{ IsLock γ l P ∗ P ∗ Locked γ }}}
    unlock [ #l ] @ tid; ⊤
  {{{ RET #☠; True }}}.


End spec.

Record lock_spec {Σ} `{!noprolG Σ} {lockN: namespace} : Type := LockSpec {
  new_lock : val;
  do_lock : val;
  unlock : val;

  IsLock: IsLockT Σ lockN;
  Locked: LockedT Σ;

  IsLock_Persistent : ∀ γ l P, Persistent (IsLock γ l P);

  new_lock_spec: new_lock_spec' lockN new_lock IsLock;
  do_lock_spec: do_lock_spec' lockN do_lock IsLock Locked;
  unlock_spec: unlock_spec' lockN unlock IsLock Locked;
}.

Global Arguments lock_spec : clear implicits.
Global Arguments lock_spec _ {_} _: assert.
Global Existing Instances IsLock_Persistent.

