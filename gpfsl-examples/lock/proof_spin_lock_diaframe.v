From gpfsl.examples.lock Require Import code_spin_lock spec_lock.
From gpfsl.examples Require Import uniq_token.
From gpfsl.logic Require Import proofmode repeat_loop new_delete atomics invariants.

From gpfsl.lang Require Import notation.

From gpfsl.diaframe Require Import vprop_weakestpre spec_notation
 vprop_weakestpre_logatom atom_spec_notation proof_automation.
From diaframe Require Import proofmode_base lib.except_zero own_hints steps.verify_tac util_instances.
From diaframe.symb_exec Require Import weakestpre_logatom.



Require Import iris.prelude.options.

Local Open Scope positive_scope.

Section spinlock.

Context `{!noprolG Σ, !uniqTokG Σ, !atomicG Σ}.
Context (lockN : namespace) (DISJ: lockN ## histN).
Notation iProp := (iProp Σ).
Notation vProp := (vProp Σ).

Definition Locked: LockedT Σ := λ (γ: gname), UTok γ.


Definition can_cas_from (ζ: absHist) t V : Prop :=
  (ζ !! t) = Some (#0, V) ∧ ((ζ !! (t+1)%positive)) = None.

(* Needed to prove that the lock flag value is comparable with #0 *)
Definition is_bool_history (ζ: absHist) : Prop :=
  ∀ t (v : val), fst <$> ζ !! t = Some v → v = #0 ∨ v = #1.


Definition case_unlocked γ P ζ: vProp :=
  ∃ tlast Vlast, Locked γ ∗ ⌜ ∀ t V, can_cas_from ζ t V → V = Vlast ∧ t = tlast ⌝ ∗ @{Vlast} P .

Definition case_locked (ζ: absHist): vProp :=
  ⌜ ∀ t V, ¬ can_cas_from ζ t V ⌝.


Definition LockInv (γ γx: gname) (l: loc) (P: vProp) :=
  (∃ ζ Vx , @{Vx}l at↦{γx} ζ ∗ ( case_unlocked γ P ζ ∨ case_locked ζ ) ∗ ⌜ is_bool_history ζ ⌝ )%I.

#[global] Instance LockInv_objective γ γx l P :
  Objective (LockInv γ γx l P) := _.

Definition IsLock : IsLockT Σ lockN :=
  (λ (γ: gname) (l: loc) (P: vProp), ∃ γx t0 V0, inv lockN (LockInv γ γx l P) ∗ l sn⊒{γx} {[t0 := (#0, V0)]})%I.

#[global] Instance IsLock_Persistent γ l P:
  Persistent (IsLock γ l P) := monPred_persistent _ _.


(* Hints *)

#[global] Instance remove_shift_0_from_context l v:
  MergableConsume ((l >> 0) ↦ v)%I true
  (λ p Pin Pout, TCAnd (TCEq Pin (ε₀)%I) (TCEq Pout (l ↦ v)))%I.
Proof.
  rewrite /MergableConsume => p Pin Pout [-> ->].
  rewrite bi.intuitionistically_if_elim shift_lblock_0.
  iSteps.
Qed.


Definition new_lock_spec :
  new_lock_spec' lockN code_spin_lock.new_lock IsLock.
Proof.
  iMod UTok_alloc as (γ) "Tok".
  iSteps.

  split.
  { (* case_unlocked *) iPureIntro. unfold BehindModal, can_cas_from. intros ??[H_lookup _].
    rewrite lookup_singleton_Some in H_lookup. naive_solver. }
  iSteps.
  (*is_bool_history*) iPureIntro. unfold is_bool_history. intros ?? lu. rewrite fmap_Some in lu.
  destruct lu as (? & lu & ?). rewrite lookup_singleton_Some in lu. naive_solver.
Qed.


Lemma bool_history_preserved ζ t' (v': val) V':
  is_bool_history ζ → (v' = #0 ∨ v' = #1) → is_bool_history (<[t':=(v', V')]> ζ).
Proof.
  unfold is_bool_history. intros ????.
  case (decide (t = t')) as [-> | NE].
  + rewrite lookup_insert. naive_solver.
  + rewrite lookup_insert_ne; eauto.
Qed.

Lemma bool_history_comparable_with_0 ζ t v:
  is_bool_history ζ → fst <$> ζ !! t = Some v → ∃ vl : lit, v = #vl ∧ lit_comparable 0%Z vl.
Proof.
  rewrite /is_bool_history. intros. destruct (H _ _ H0); eexists; (split; [done|constructor]).
Qed.


Definition do_lock_spec :
  do_lock_spec' lockN code_spin_lock.do_lock IsLock Locked.
Proof using All.
  iStep 10. iLöb as "IH". iStepsSafe.
  - (* unlocked*) split. { rewrite /BehindModal. eauto using bool_history_comparable_with_0. }
    iStepsSafe.
    + (* unlocked - fail case *) iLeft. unseal_diaframe. iSteps.
    + (* unlocked - succeed case *)
      iRight.
      assert (can_cas_from x13 x11 x18) as ccf. {
        unfold can_cas_from.
        apply (lookup_weaken _ _ _ _ H6) in H5 as ζ'_t'.
        rewrite lookup_insert_ne in ζ'_t'; last lia.
        naive_solver.
      }
      destruct (H2 _ _ ccf) as [<- <-]. rename x11 into t'.
      iSteps.
      * iPureIntro. intros. unfold can_cas_from in *.
        case (decide (t = t')) as [-> | NE_tt'].
        { rewrite lookup_insert. naive_solver. }
        case (decide (t = t' + 1)) as [-> | NE_].
        { rewrite lookup_insert; naive_solver. }
        { do 2 (rewrite lookup_insert_ne; try lia). naive_solver. }
      * eauto using bool_history_comparable_with_0, bool_history_preserved.
  - (* locked *)split. { rewrite /BehindModal. eauto using bool_history_comparable_with_0. }
    iStep 10.
    + (* locked - fail case *) iSteps.
    + (* locked - success case *) iExFalso. iPureIntro.
      assert (can_cas_from x13 x11 x16) as ccf. {
        unfold can_cas_from.
        apply (lookup_weaken _ _ _ _ H6) in H5 as ζ'_t'.
        rewrite lookup_insert_ne in ζ'_t'; last lia.
        naive_solver.
      }
      naive_solver.
Qed.

Definition unlock_spec :
  unlock_spec' lockN code_spin_lock.unlock IsLock Locked.
Proof using All.
  iStepsSafe.
  - (* lock was unlocked *) iRight. unseal_diaframe. iStep. iExFalso. iApply (UTok_unique with "H5 H6").
  - (* lock was locked *) iLeft. unseal_diaframe. iSteps. split.
    { iPureIntro. rewrite /BehindModal. unfold can_cas_from in *. intros ?? H'.
      case (decide (t = x10)) as [-> | NE].
      - rewrite lookup_insert in H'. naive_solver.
      - exfalso. rewrite lookup_insert_ne in H'; last done.
        rewrite lookup_insert_None in H'. naive_solver.
    }
    iSteps. eauto using bool_history_preserved.
Qed.


End spinlock.

