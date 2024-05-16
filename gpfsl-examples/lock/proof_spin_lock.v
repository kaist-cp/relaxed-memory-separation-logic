From gpfsl.examples.lock Require Import code_spin_lock spec_lock.
From gpfsl.examples Require Import uniq_token.
From gpfsl.logic Require Import proofmode repeat_loop new_delete atomics invariants.

From gpfsl.lang Require Import notation.

Require Import iris.prelude.options.

Local Open Scope positive_scope.

Section spinlock.

Context `{!noprolG Σ, !uniqTokG Σ, !atomicG Σ}.
Context (lockN : namespace) (DISJ: lockN ## histN).
Notation iProp := (iProp Σ).
Notation vProp := (vProp Σ).

Definition Locked: LockedT Σ := λ (γ: gname), UTok γ.


Definition can_cas_from (ζ: absHist) t V : Prop := (ζ !! t) = Some (#0, V) ∧ ((ζ !! (t+1)%positive)) = None.

(* Needed to prove that the lock flag value is comparable with #0 *)
Definition is_bool_history (ζ: absHist) : Prop := ∀ t (v : val), fst <$> ζ !! t = Some v → v = #0 ∨ v = #1.


Definition case_unlocked γ P ζ: vProp :=
   ∃ tlast Vlast, Locked γ ∗ @{Vlast} P ∗ ⌜ ∀ t V, can_cas_from ζ t V → V = Vlast ∧ t = tlast ⌝.

Definition case_locked (ζ: absHist): vProp :=
  ⌜ ∀ t V, ¬ can_cas_from ζ t V ⌝.


Definition LockInv (γ γx: gname) (l: loc) (P: vProp) :=
  (∃ ζ Vx , @{Vx}l at↦{γx} ζ ∗ ⌜ is_bool_history ζ ⌝ ∗
    ( case_unlocked γ P ζ ∨ case_locked ζ ))%I.

#[global] Instance LockInv_objective γ γx l P :
  Objective (LockInv γ γx l P) := _.

Definition IsLock : IsLockT Σ lockN :=
  (λ (γ: gname) (l: loc) (P: vProp), ∃ γx t0 V0, l sn⊒{γx} {[t0 := (#0, V0)]} ∗ inv lockN (LockInv γ γx l P))%I.

#[global] Instance IsLock_Persistent γ l P:
  Persistent (IsLock γ l P) := monPred_persistent _ _.

Definition new_lock_spec :
  new_lock_spec' lockN code_spin_lock.new_lock IsLock.
Proof.
  iIntros (P tid Φ) "P HΦ". rewrite /code_spin_lock.new_lock.
  wp_lam. wp_apply wp_new; [done..|].
  iIntros (l) "([†l|%] & l↦ & _) //". rewrite own_loc_na_vec_singleton.
  wp_pures. wp_bind (_ <- _)%E. wp_write.

  iMod (AtomicPtsTo_from_na_rel with "P l↦") as (γx t V) "(#SeenV & P & SN & l↦)".

  iDestruct (AtomicPtsTo_SW_to_CON_1 with "l↦ SN") as "[l↦ sy⊒]".
  iDestruct (AtomicSync_AtomicSeen with "sy⊒") as "sn⊒".

  iMod UTok_alloc as (γ) "Tok".

  iMod (inv_alloc lockN _ (LockInv γ _ _ _) with "[-HΦ sn⊒]") as "LockInv". {
    iDestruct (view_at_intro with "l↦") as (Vx) "[_ l↦]".
    repeat iExists _. iModIntro. iFrame "l↦". iSplitR.
    - iPureIntro. unfold is_bool_history. intros. rewrite fmap_Some in H. destruct H as (? & ? & ?).
      rewrite lookup_singleton_Some in H. naive_solver.
    - iLeft. unfold case_unlocked. repeat iExists _. iFrame.
      iPureIntro. intros. destruct H  as [H _]. rewrite lookup_singleton_Some in H. naive_solver.
  }

  wp_pures. iApply "HΦ". rewrite /IsLock. repeat iExists _. iFrame.
Qed.

Definition bool_history_preserved ζ t' (v': val) V':
  is_bool_history ζ → (v' = #0 ∨ v' = #1) → is_bool_history (<[t':=(v', V')]> ζ).
Proof.
  unfold is_bool_history. intros ????.
  case (decide (t = t')) as [-> | NE].
  + rewrite lookup_insert. naive_solver.
  + rewrite lookup_insert_ne; eauto.
Qed.


Definition do_lock_spec :
  do_lock_spec' lockN code_spin_lock.do_lock IsLock Locked.
Proof using All.
  iIntros (γ l P tid Φ) "#IsLock HΦ". rewrite /code_spin_lock.do_lock.
  iDestruct "IsLock" as (γx t0 V0) "[Seen0 LockInv]".
  wp_seq.
  iLöb as "IH".

  wp_pures.
  wp_bind (casᵃᶜ(_, _, _))%E.

  iInv "LockInv" as (ζ Vx) "(>l↦ & >%is_bool_hist_ζ & lock_cases)" "Close".

  iDestruct (view_at_intro True with "[//]") as (Vbefore) "[#⊒Vbefore _]".

  iMod (rel_objectively_intro (⊒∅) tid with "[]") as "#rel_empty".
  { iApply objective_objectively. iApply monPred_in_bot. }

  wp_apply (AtomicSeen_CON_CAS_int _ _ _ _ _ _ _ _ #1 with "[$Seen0 $l↦ $⊒Vbefore]");[done..| solve_ndisj | | done |].
  { intros ?? _?. unfold is_bool_history in *. destruct (is_bool_hist_ζ _ _ H) as [-> | ->]; eexists; (split; [done|constructor]). }
  iIntros (??? Vread Vafter ζ'0 ζ'). iIntros "(([_ %ζ'0_incl_ζ'] & %ζ'0_read_v' & _) & #⊒Vafter & _ & l↦ & CASE)".

  iDestruct "CASE" as "[[[-> [_ ->]] _] | [[-> ->] [%Vw [(%t'_next_was_empty & -> & _ & %Vread_Vw & _) [_ %Vw_Vafter]]]]]".
  - (* cas failed *)
    iMod ("Close" with "[l↦ lock_cases]"). {
      rewrite /LockInv. repeat iExists _. iFrame "∗%".
    }
    iModIntro. do 3 wp_pure _. iApply "IH". done.
  - (* cas succeeded *)
    assert (can_cas_from ζ t' Vread) as can_cas_and_get_Vread. {
      unfold can_cas_from.
      apply (lookup_weaken _ _ _ _ ζ'0_read_v') in ζ'0_incl_ζ' as ζ'_t'.
      rewrite lookup_insert_ne in ζ'_t'; last lia.
      naive_solver.
    }

    (* The lock was in unlocked state since otherwise cas would not have been possible. *)
    iAssert (case_unlocked γ P ζ)%I with "[lock_cases]" as "lock_was_unlocked". {
      iDestruct "lock_cases" as "[? | %locked]"; naive_solver.
    }

    unfold case_unlocked. iDestruct "lock_was_unlocked" as (tlast Vlast) "(Locked & P & %cas_reads_last)".

    (* acquire P *)
    assert (Vlast = Vread ∧ tlast = t') as [-> ->]; first naive_solver.

    iDestruct (view_at_elim with "[⊒Vafter] P") as "P".
    { iApply (monPred_in_mono with "⊒Vafter"). simpl. solve_lat. }

    iMod ("Close" with "[l↦]"). {
      unfold LockInv. iModIntro. repeat iExists _. iFrame "l↦".
      iSplitR.
      - iPureIntro. apply bool_history_preserved; auto.
      - iRight. iPureIntro. unfold case_locked, can_cas_from in *.
        intros ??.
        case (decide (t = t')) as [-> | NE_tt'].
        { rewrite lookup_insert. naive_solver. }
        case (decide (t = t' + 1)) as [-> | NE_].
        { rewrite lookup_insert; naive_solver. }
        { repeat rewrite lookup_insert_ne; try lia. naive_solver. }
    }
    iModIntro. wp_pures. iApply "HΦ". iFrame.
Qed.


Definition unlock_spec :
  unlock_spec' lockN code_spin_lock.unlock IsLock Locked.
Proof using All.
  iIntros (?????) "(#IsLock & P & Locked) HΦ". rewrite /code_spin_lock.unlock.
  iDestruct "IsLock" as (γx t0 V0) "[Seen0 LockInv]".
  wp_seq.

  wp_bind (_ <-ʳᵉˡ _)%E.

  iInv "LockInv" as (ζ Vx) "(>l↦ & >%is_bool_hist_ζ & lock_cases)" "Close".

  iDestruct (view_at_intro with "P") as (Vbefore) "[#⊒Vbefore P]".

  wp_apply (AtomicSeen_concurrent_write _ _ _ _ _ _ ∅ _ _ #0 with "[$Seen0 $l↦ $⊒Vbefore]"); [done| solve_ndisj| done| ].

  (* The lock was in locked state since this thread holds the Locked token. *)
  iAssert (case_locked ζ)%I with "[lock_cases Locked]" as "%lock_was_locked {lock_cases}". {
    iDestruct "lock_cases" as "[unlocked | ?]"; last done.
    unfold case_unlocked. iDestruct "unlocked" as (??) "(Locked' & _)". unfold Locked.
    iExFalso. iApply (UTok_unique with "Locked Locked'").
  }

  iIntros (???) "((_ & _ & %Le_Vbefore_V' & _ & _ & ->) & _ & _ & l↦)".

  iMod ("Close" with "[l↦ P Locked]") as "_". {
    unfold LockInv. iModIntro. repeat iExists _. iFrame "l↦".
    iSplitR.
    - iPureIntro. apply bool_history_preserved; auto.
    - iLeft. unfold case_unlocked. iExists t', V'. iFrame. iPureIntro.
      intros. unfold can_cas_from in *.
      case (decide (t = t')) as [-> | NE].
      + rewrite lookup_insert in H. naive_solver.
      + exfalso. rewrite lookup_insert_ne in H ; last done.
        rewrite lookup_insert_None in H. naive_solver.
  }

  iModIntro. wp_pures. iApply "HΦ". done.
Qed.


End spinlock.


