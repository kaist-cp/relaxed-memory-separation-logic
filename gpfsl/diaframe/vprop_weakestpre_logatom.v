From iris.bi Require Export bi telescopes lib.atomic updates.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre lifting atomic.
From diaframe Require Import proofmode_base.
From diaframe.lib Require Import atomic laterable.
From diaframe.symb_exec Require Import defs weakestpre.
Import bi.

(* This file extends the weakestpre executor with support for logically atomic specifications *)

Section atomic_template.
  Context `{BiFUpd PROP}.

  (* some thoughts on the masks for atomic_update. The lemmas below show that the current requirement is stronger (so the specification weaker)
     than the other option, |={⊤, M}=>. However, one is not necessarily better than the other - it depends on the syntactic order of opening
     the implementation invariant and the supplied atomic update. For the current examples, I think Iris's default approach is fine: usually,
     the implemantation invariant contains the resource that is syntactically required, and sometimes we need to open the atomic update to 
     complete the proof. In this order, |={⊤ ∖ M, ∅}=> does exactly what we want.  *)
  Lemma acc_1 (M : coPset) (P : PROP) : (|={⊤ ∖ M, ∅}=> P) ⊢ |={⊤, M}=> P.
  Proof.
    iIntros "HP".
    iMod (fupd_mask_subseteq_emptyset_difference) as "HM"; last first.
    iMod "HP". 2:{ set_solver. }
    iMod "HM". replace (⊤ ∖ (⊤ ∖ M)) with M. by iFrame "HP".
    apply set_eq => x; split; set_solver.
  Qed.

  Lemma acc_2 (M : coPset) (P Q : PROP) : (|={⊤ ∖ M, ∅}=> P ∗ |={∅, ⊤ ∖ M}=> Q) ⊢ |={⊤, M}=> P ∗ |={M, ⊤}=> Q.
  Proof.
    iIntros "HPQ".
    iPoseProof (fupd_mask_intro_subseteq ⊤ (⊤ ∖ M) bi_emp) as "H"; first set_solver.
    rewrite left_id.
    iMod "H".
    iMod "HPQ" as "[$ HQ]".
    iMod "HQ" as "$".
    iMod "H".
    iApply fupd_mask_intro_subseteq. set_solver. done.
  Qed.

  Definition atomic_templateM (A M M' : coPset) (P1 : PROP) TT1 TT2 (P2 : TT1 -t> PROP) (Q1 Q2 : TT1 -t> TT2 -t> PROP) : (TT1 * TT2 → PROP) → PROP
    := (λ Ψ, |={A}=> P1 ∗ atomic_update (A∖ M) M' (tele_app P2) (tele_app (tele_map tele_app Q2)) (λ a b, tele_app (tele_app Q1 a) b -∗ Ψ (a, b)))%I.

  Global Arguments atomic_templateM A M M' P1 TT1 TT2 P2 Q1 Q2 Ψ /.

  (* atomic specifications will 'just' be instances of AtomicReductionStep' *)
  Class AtomicReductionStep' `(condition : ReductionCondition PROP E W ) (pre : PROP) A M M' TT1 TT2 (P1 : PROP) (P2 : TT1 -t> PROP) (Q1 Q2 : TT1 -t> TT2 -t> PROP) e (e' : TT1 -t> TT2 -t> E) w :=
    atomic_step_as_template_step :> ReductionTemplateStep condition (TT1 * TT2)%type pre w e (λ pr, tele_app (tele_app e' pr.1) pr.2) 
                  (atomic_templateM A M M' P1 TT1 TT2 P2 Q1 Q2).

  Lemma atomic_templateM_is_mono A M M' P1 TT1 TT2 P2 Q1 Q2 :
    template_mono (atomic_templateM A M M' P1 TT1 TT2 P2 Q1 Q2).
  Proof.
    move => S T HST /=.
    apply fupd_mono, bi.sep_mono_r.
    iIntros "H".
    iApply (atomic_update_mono with "H").
    iIntros "!>"; iSplit; first eauto.
    iIntros (a). iExists id.
    iSplit; first eauto.
    iIntros (b) => /=.
    rewrite -fupd_intro. iStopProof.
    apply bi.wand_intro_l.
    rewrite right_id.
    apply bi.wand_mono; first done.
    apply HST.
  Qed.

  Global Arguments difference {_ _} _ _ : simpl never.

  Lemma atomic_templateM_is_absorbing A M M' P1 TT1 TT2 P2 Q1 Q2 :
    Affine (PROP := PROP) True%I →
    template_absorbing (atomic_templateM A M M' P1 TT1 TT2 P2 Q1 Q2). (* this could be used for relocs symbolic execution *)
  Proof.
    move => Htrue P Q /=.
    iIntros "[>[$ H] HQ] !>".
    assert (SimplTeleEq TT2 (tele_eq TT2)).
    { rewrite /SimplTeleEq.
      apply tforall_forall => tt1.
      apply tforall_forall => tt2. done. } (* needed to prove the atomic_acc' which will appear *)
    iStep.
    iStep.
    iStep.
    iMod "H" as (x) "[HP2 Hr]".
    iExists (x). iFrame "HP2".
    iStep.
    - iStep as "HP2". iDestruct "Hr" as "[Hr _]".
      iMod ("Hr" with "HP2") as "$".
      iSteps.
    - iIntros (y). iStep as "H2".
      iDestruct "Hr" as "[_ Hr]".
      iMod ("Hr" with "H2").
      iSteps.
  Qed.
End atomic_template.

Global Arguments AtomicReductionStep' : simpl never. (* unfortunately, Program just ignores this. *)


From gpfsl.base_logic Require Export weakestpre.
From gpfsl.logic Require Import lifting logatom.
From gpfsl.diaframe Require Import vprop_weakestpre.

Section atomic_wp_compat.
  Context `{!noprolG Σ}.

  (* the only thing we need to prove is that atomic_templateM satisfies the template condition of the WP executor *)

  Global Instance atomic_templateM_satisfies_wp_template_condition R A M M' P1 TT1 TT2 P2 Q1 Q2 :
    SolveSepSideCondition (↑histN ⊆ R.t1) →
    SatisfiesTemplateCondition wp_template_condition R (atomic_templateM A M M' P1 TT1 TT2 P2 Q1 Q2) R (atomic_templateM A M M' P1 TT1 TT2 P2 Q1 Q2).
  Proof.
    rewrite /SatisfiesTemplateCondition /=.
    split => //.
    by apply atomic_templateM_is_mono.
  Qed.

  Global Instance atomic_step_emp_valid_value pre e T E E' (A B : tele) P1 P2 e' v' Q1 Q2 :
    (∀.. (a : A), ∀.. (b : B), (IntoVal (tele_app (tele_app e' a) b) (tele_app (tele_app v' a) b))) →
    AsEmpValidWeak (PROP := vPropI Σ)
      (AtomicReductionStep' wp_red_cond pre T E E' A B P1 P2 Q1 Q2 e e' [tele_arg3 T]) 
      (∀ tid Φ, pre ∗ P1 ∗ atomic_update (T ∖ E) E' (tele_app P2) (tele_app (tele_map tele_app Q2))
          (λ.. a b, tele_app (tele_app Q1 a) b -∗ Φ (tele_app (tele_app v' a) b)) -∗ WP e @ tid; T {{ Φ }})%I.
  Proof.
    rewrite /AsEmpValidWeak /AtomicReductionStep' /ReductionTemplateStep => Hv' HPQ. cbn.
    iIntros "Hpre". iExists (λ pr, tele_app (tele_app v' pr.1) pr.2).
    iSplitR; first iPureIntro. { case => /= a b. by revert Hv' => /(dep_eval_tele a) /(dep_eval_tele b) ->. }
    iIntros (Φ tid) ">[HP1 HAU]".
    iCombine "Hpre HP1" as "Hpre".
    revert HPQ.
    rewrite (bi.forall_elim tid) (bi.forall_elim (λ v, |={T}=> Φ v))%I.
    rewrite assoc.
    move => /bi.wand_entails /bi.wand_intro_r ->.
    iApply wp_fupd.
    iApply "Hpre".
    iApply (atomic_update_mono with "HAU").
    iIntros "!>". iSplit; first eauto.
    iIntros (a). iExists id.
    iSplit; first eauto.
    iIntros (b) => /=.
    rewrite !tele_app_bind.
    iIntros "HQΦ !> HQ".
    by iApply "HQΦ".
  Qed.

  (* this instance makes iSteps work on goals built by Program, which for some reason unfolds AtomicReductionStep' goals *)
  Global Instance template_step_emp_valid `{BiFUpd PROP} (pre : PROP) `(red_cond : ReductionCondition PROP E W) e T M M' P1 A B P2 Q1 Q2 f' w G :
    AsEmpValidWeak (PROP := PROP) (AtomicReductionStep' red_cond pre T M M' A B P1 P2 Q1 Q2 e f' w) G →
    AsEmpValidWeak (PROP := PROP) (ReductionTemplateStep red_cond (A * B) pre w e (λ pr: A * B, tele_app (tele_app f' pr.1) pr.2) (atomic_templateM T M M' P1 A B P2 Q1 Q2)) G.
  Proof. done. Qed.

  Lemma atomic_wp_strong_mono e tid E {TA TB TB' : tele} (α α' : TA → vProp Σ) (β Φ : TA → TB → vProp Σ) (f : TA → TB → val) (β' Φ' : TA → TB' → vProp Σ) (f' : TA → TB' → val) :
    atomic_wp e tid E α β Φ f -∗ 
    □ ((∀.. a, (|={↑histN}=> α' a) ∗-∗ |={↑histN}=> α a) ∗ 
       (∀.. a, ∃ (g : TB → TB'), (∀.. b, β a b ={↑histN}=∗ β' a (g b)) ∗ 
                                 (∀.. b, ⌜f a b = f' a (g b)⌝) ∗
                                 (∀.. b, Φ a b -∗ Φ' a (g b)))) -∗ 
    atomic_wp e tid E α' β' Φ' f'.
  Proof.
    iIntros "Hwp (#Hα & #Hf)" (Ψ) "Hau".
    iApply "Hwp".
    iApply (atomic_update_mono with "Hau").
    iIntros "!>"; repeat iSplit; try (iFrame "∗ #").
    iIntros (a).
    iDestruct ("Hf" $! a) as "[%g (#Hβ & #% & HΦΦ')]".
    iExists g; iSplit; try (iFrame "∗ #").
    iIntros (b).
    rewrite !tele_app_bind.
    revert H => /(dep_eval_tele b) -> //.
    iIntros "HΦ' !> HΦ". iApply "HΦ'". by iApply "HΦΦ'".
  Qed.

End atomic_wp_compat.

(* SPEC2 is usually used by Coq for printing atomic specs with two non-trivial telescopes,
   as Coq is not smart enough to see the shared binders in Q2 *)

Global Notation "'SPEC2' ⟨ A , E , E' ⟩ x1 .. xn , << P1 ¦ P2 >> e << 'RET' [ e' ] ; Q1 ¦ Q2 >>" :=
  (AtomicReductionStep'
    wp_red_cond
    empty_hyp_first
    A
    E
    E'
    (TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
    _
    P1%I
    (λ x1, .. (λ xn, P2%I) .. )
    Q1%I
    Q2%I
    e
    e'
    [tele_arg ⊤ ; NotStuck] )
  (at level 20, E at level 9, x1 closed binder, xn closed binder, e, P1, P2, e', Q1, Q2 at level 200, format
  "'[hv' SPEC2  ⟨ A ,  E ,  E' ⟩  x1 .. xn ,  '/ ' <<  P1  ¦  P2  >> '/  '  e  '/ ' <<  'RET'  [ e' ] ; '/  '  Q1  ¦ '/  '  Q2  >> ']'", only printing
).









