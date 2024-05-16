
From diaframe Require Import proofmode_base.
From gpfsl.logic Require Import proofmode atomics.
From gpfsl.lang Require Import notation.

From gpfsl.diaframe Require Export lattice_hints.


Section hints.

Context `{!noprolG Σ}.

Notation iProp := (iProp Σ).
Notation vProp := (vProp Σ).


#[global] Instance mergable_consume_remove_weaker_view_seen V V' :
  (MergableConsume (PROP := vProp) (⊒V') true
  (λ p Pin Pout,
    TCAnd (TCEq Pin (⊒V)) $
      TCIf (SolveSepSideCondition (V ⊑ V'))
        (TCEq Pout ( ⊒V' ))
        (TCEq Pout ( ⊒(V ⊔ V')))))%I | 100.
Proof.
  intros p Pin Pout [-> [_ ->| ->]]; rewrite bi.intuitionistically_if_elim.
  - iSteps.
  - iIntros "[A B]". iApply monPred_in_view_op. iFrame.
Qed.


#[global] Instance biabd_monPred_in_mono `{BiAffine PROP} p (V1 V2 : view) :
  SolveSepSideCondition (V2 ⊑ V1) →
  HINT □⟨p⟩ @monPred_in _ PROP V1 ✱ [- ; emp ]
   ⊫ [id]
  ; ⊒V2 ✱ [ emp ].
Proof.
  intros ?. iStep as "P1". rewrite bi.intuitionistically_if_elim.
  iSplit; [|done].
  iApply (monPred_in_mono with "P1"). done.
Qed.


(* for abduction hints *)
#[global] Instance view_at_into_wand p (P: vProp) V:
  IntoWand2 p (@{V} P)
  ( ⊒V ) (* -∗ *) (P)%I.
Proof.
  rewrite /IntoWand2 bi.intuitionistically_if_elim. iSteps as "H2 H1".
  iApply (view_at_elim with "H2 H1").
Qed.

(* for bi-abduction hints *)
#[global] Instance view_at_into_connective (P: vProp) V:
  AtomIntoConnective (@{V} P) ( ⊒V -∗ P)%I.
Proof.
  rewrite /AtomIntoConnective. iSteps.
Qed.

#[global] Instance biabd_view_at_to_view_at p (P: vProp) V₁ V₂:
  SolveSepSideCondition (V₁ ⊑ V₂) →
    HINT □⟨p⟩ @{V₁} P ✱ [- ; emp ]
    ⊫ [id]
    ; @{V₂} P ✱ [ True ].
Proof.
  intros LE. iStep as "P". rewrite bi.intuitionistically_if_elim.
  iSplit; [|done]. iApply (view_at_mono with "P"); done.
Qed.


Class DisableViewIntroFor (P : vProp) :=
  disable_view_intro : True.
Global Hint Mode DisableViewIntroFor ! : typeclass_instances.

#[global] Instance disable_view_intro_for_objective P :
  Objective P → DisableViewIntroFor P | 500.
Proof. done. Qed.


#[global] Instance disable_view_intro_for_view_seen V :
  DisableViewIntroFor (⊒V).
Proof. done. Qed.

#[global] Instance disable_view_intro_for_empty_hyp_first :
  DisableViewIntroFor (ε₀).
Proof. done. Qed.

#[global] Instance disable_view_intro_for_empty_hyp_last :
  DisableViewIntroFor (ε₁).
Proof. done. Qed.

#[global] Instance disable_view_intro_for_empty_hyp_last_spatial :
  DisableViewIntroFor (empty_hyp_last_spatial).
Proof. done. Qed.

(* #[global] Instance disable_view_intro_for_pers (P : vProp) :
  DisableViewIntroFor (P) →
  DisableViewIntroFor (□ P).
Proof. done. Qed.

#[global] Instance disable_view_intro_for_later (P : vProp) :
  DisableViewIntroFor (P) →
  DisableViewIntroFor (▷ P).
Proof. done. Qed.

#[global] Instance disable_view_intro_for_atomic_update {BiFUpd0 TA TB} Eo Ei α β Φ:
  DisableViewIntroFor (@atomic.atomic_update vProp BiFUpd0 TA TB Eo Ei α β Φ).
Proof. done. Qed. *)



#[global] Instance mergable_consume_remove_view_at_from_objective V (P : vProp) :
  Objective P →
  MergableConsume (@{V} P)%I true
  (λ p Pin Pout, TCAnd (TCEq Pin (ε₀)%I) (TCEq Pout (P)%I)) | 0.
Proof.
  intros ? p Pin Pout [-> ->].
  rewrite bi.intuitionistically_if_elim view_at_objective_iff. iSteps.
Qed.


Definition do_intro_view_forall_def : vProp := emp%I.
Definition do_intro_view_forall_aux : seal (@do_intro_view_forall_def). Proof. by eexists. Qed.
Definition do_intro_view_forall := do_intro_view_forall_aux.(unseal).
#[global] Opaque do_intro_view_forall.
#[global] Arguments do_intro_view_forall : simpl never.
Lemma do_intro_view_forall_eq : @do_intro_view_forall = @do_intro_view_forall_def.
Proof. rewrite -do_intro_view_forall_aux.(seal_eq) //. Qed.


Definition create_collector_def : vProp := emp%I.
Definition create_collector_aux : seal (@create_collector_def). Proof. by eexists. Qed.
Definition create_collector := create_collector_aux.(unseal).
#[global] Opaque create_collector.
#[global] Arguments create_collector : simpl never.
Lemma create_collector_eq : @create_collector = @create_collector_def.
Proof. rewrite -create_collector_aux.(seal_eq) //. Qed.


Definition collector_def (P : vProp) := P%I.
Definition collector_aux : seal (@collector_def). Proof. by eexists. Qed.
Definition collector := collector_aux.(unseal).
#[global] Opaque collector.
#[global] Arguments collector _ : simpl never.
Lemma collector_eq : @collector = @collector_def.
Proof. rewrite -collector_aux.(seal_eq) //. Qed.


#[global] Instance biabd_create_collector :
HINT ε₀ ✱ [- ; emp ]
⊫ [id]
; create_collector ✱ [ collector emp ].
Proof. rewrite create_collector_eq collector_eq. iSteps. Qed.


#[global] Instance mergable_consume_collect_resources P Q :
  MergableConsume (collector P) true (λ p Pin Pout,
    TCAnd (TCEq Pin ( Q )%I) $
    TCAnd (TCIf (DisableViewIntroFor Q) False TCTrue) $
      TCEq Pout (collector (Q ∗ P))
    )%I | 10.
Proof.
  rewrite collector_eq => p Pin Pout [-> [_ ->]].
  rewrite bi.intuitionistically_if_elim.
  iSteps.
Qed.


#[global] Instance biabd_do_intro_view_forall :
  HINT ε₀ ✱ [V P; ⊒V ∗ create_collector ∗ collector P ]
  ⊫ [id]
  ; do_intro_view_forall ✱ [ ∃ V', ⌜ V ⊑ V' ⌝ ∗ ⊒V' ∗ @{V'} P ].
Proof.
  rewrite do_intro_view_forall_eq collector_eq /collector_def.
  iStep 4 as (V P) "⊒V _ P". iDestruct (view_at_intro_incl with "P ⊒V") as (V') "(? & % & ?)".
  iSteps.
Qed.


#[global] Instance into_sep_careful_view_at V (P Q1 Q2: vProp):
  IntoSepCareful P Q1 Q2 → IntoSepCareful (@{V} P)%I (@{V} Q1)%I (@{V} Q2)%I.
Proof.
  rewrite /IntoSepCareful => H.
  rewrite -view_at_sep. iApply view_at_wand. iApply view_at_at. iApply H.
Qed.

#[global] Instance from_sep_careful_view_at V (P Q1 Q2 : vProp):
  FromSepCareful P Q1 Q2 → (FromSepCareful (@{V} P) (@{V} Q1) (@{V} Q2))%I.
Proof. rewrite /FromSepCareful -view_at_sep => H. iApply view_at_wand. iApply view_at_at. iApply H. Qed.


#[global] Instance from_texist_view_at V (P: vProp) {TT} P' :
  FromTExist P TT P' →
  FromTExist (@{V} P)%I TT (tele_map (view_at V) P') | 5.
Proof.
  rewrite /FromTExist !bi_texist_exist => <-.
  rewrite view_at_exist.
  apply bi.exist_mono => tt.
  by rewrite tele_map_app.
Qed.

#[global] Instance biabd_view_at_objective V (P : vProp) :
  Objective P →
  HINT ε₀ ✱ [- ; P ]
  ⊫ [id]
  ; @{V} P ✱ [ True ].
Proof.
  intros P_obj. iStep as "P". rewrite view_at_objective_iff. auto.
Qed.



#[global] Instance view_at_into_exist_careful {A} P (P' : A → vProp) V :
  IntoExistCareful P P' →
  IntoExistCareful (@{V} P)%I (λ a, @{V} (P' a))%I.
Proof. rewrite /IntoExistCareful => ->. rewrite view_at_exist. done. Qed.

#[global] Instance view_at_into_forall_careful {A} (Q : vProp) (Q' : A -> vProp) V :
  IntoForallCareful Q Q' →
  IntoForallCareful (@{V} Q)%I (λ a, @{V} Q' a)%I.
Proof.
  rewrite /IntoForallCareful => ->. rewrite view_at_forall. done.
Qed.

#[global] Instance mergable_consume_view_at_view_at V1 V2 P :
  MergableConsume (PROP := vProp) ( @{V1} (@{V2} P) ) true (λ p Pin Pout,
  TCAnd (TCEq Pin ( ε₀ )%I) $
    TCEq Pout (@{V2} P)
  )%I | 10.
Proof. intros p Pin Pout [-> ->]. rewrite bi.intuitionistically_if_elim. rewrite view_at_view_at. iSteps. Qed.


#[global] Instance mergable_consume_remove_view_at_emp V :
  MergableConsume (PROP := vProp) ( @{V} (emp) ) true (λ p Pin Pout,
  TCAnd (TCEq Pin ( ε₀ )%I) $
    TCEq Pout (emp)
  )%I.
Proof. intros p Pin Pout [-> ->]. iSteps. Qed.

End hints.

#[global] Opaque view_at.

(* This hint is disabled for performance reasons. Please turn it on manually if you need them. *)
#[global] Remove Hints mergable_consume_remove_view_at_from_objective : typeclass_instances. 
