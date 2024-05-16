From gpfsl.base_logic Require Export weakestpre.
From gpfsl.logic Require Import lifting.
From diaframe Require Import proofmode_base lib.except_zero tele_utils.
From diaframe.symb_exec Require Import defs.


Set Universe Polymorphism.

Proposition to_tforall {TT : tele} (Ψ : TT → Prop) :
  tforall Ψ → (∀ x, Ψ x).
Proof. apply tforall_forall. Qed.

Unset Universe Polymorphism.

Ltac drop_telescope_tac tele_name intro_pat :=
  revert tele_name; refine (to_tforall _ _); intros intro_pat.

Tactic Notation "drop_telescope" constr(R) "as" simple_intropattern_list(intro_pat) := 
  drop_telescope_tac R intro_pat.


Section vprop_wp_executor.
  Context `{!noprolG Σ}.
  Implicit Type (Φ : val → vProp Σ).

  Instance wp_execute_op : ExecuteOp (vPropI Σ) (expr) [tele_pair coPset; thread_id; val → vProp Σ] :=
    λ e, (λᵗ E t Φ, WP e @ t; E {{ Φ }})%I.

  Global Arguments wp_execute_op e !R /.

  Global Instance as_wp_execution e E s Φ : AsExecutionOf (WP e @ s ; E {{ Φ }})%I wp_execute_op e [tele_arg3 E; s; Φ].
  Proof. done. Qed.

  Instance wp_red_cond : ReductionCondition (vPropI Σ) (expr) [tele_pair coPset] :=
    (λ A, λᵗ E, λ e e' M, 
      (* since wp_bind_inv does not hold, we must reduce to a value!
        this prohibits PureExec usage. Make a separate hint for that *)
      ∃ v', ⌜∀ a, e' a = of_val (v' a)⌝ ∗ (
      ∀ Φ tid, M (λ a, |={E}=> Φ (v' a)) -∗ WP e @ tid ; E {{ Φ }}))%I.

  Global Arguments wp_red_cond A !R e e' M /.

  Global Instance wp_red_cond_well_behaved_equiv A : Proper ((=) ==> (=) ==>
      (pointwise_relation _ (=)) ==>
      ((pointwise_relation _ (⊣⊢)) ==> (⊣⊢)) ==> (⊣⊢)) (wp_red_cond A).
  Proof.
    move => w1 w -> {w1} e1 e -> {e1} e'' e' Hee' M1 M2 HM.
    drop_telescope w as E => /=.
    apply (anti_symm _).
    all: apply bi.exist_mono => a.
    all: apply bi.sep_mono.
    1,3: by setoid_rewrite Hee'.
    all: apply bi.forall_mono => Φ.
    all: apply bi.forall_mono => tid.
    all: rewrite HM // => a.
    all: by rewrite Hee'.
  Qed.

  Global Instance wp_red_cond_well_behaved_ent A : Proper ((=) ==> (=) ==>
      (pointwise_relation _ (=)) ==>
      ((pointwise_relation _ (flip (⊢))) ==> (flip (⊢))) ==> (⊢)) (wp_red_cond A).
  Proof.
    move => w1 w -> {w1} e1 e -> {e1} e'' e' Hee' M1 M2 HM.
    drop_telescope w as E => /=.
    all: apply bi.exist_mono => a.
    apply bi.sep_mono.
    1: by setoid_rewrite Hee'.
    apply bi.forall_mono=> Φ.
    apply bi.forall_mono=> tid.
    apply bi.wand_mono => //.
    apply HM => ? //=.
  Qed.

  Global Instance wp_red_cond_well_behaved_tne A : Proper ((=) ==> (=) ==>
      (pointwise_relation _ (=)) ==>
      ((pointwise_relation _ (⊢)) ==> (⊢)) ==> (flip (⊢))) (wp_red_cond A).
  Proof.
    move => w1 w -> {w1} e1 e -> {e1} e'' e' Hee' M1 M2 HM.
    drop_telescope w as E => /=.
    all: apply bi.exist_mono => a.
    apply bi.sep_mono.
    1: by setoid_rewrite Hee'.
    apply bi.forall_mono=> Φ.
    apply bi.forall_mono=> tid.
    apply bi.wand_mono => //.
    by apply HM => ?.
  Qed.

  Inductive context_as_item : (expr → expr) → Prop :=
    is_item K Kits : (∀ e, fill Kits e = K e) → context_as_item K.

  Instance context_as_item_condition : ContextCondition expr := λ K, context_as_item K.

  Global Arguments context_as_item_condition K /.

  Global Instance items_valid_context K : SatisfiesContextCondition context_as_item_condition (fill K).
  Proof. by econstructor. Qed.

  Instance wp_template_condition : TemplateCondition (vPropI Σ) [tele_pair coPset; thread_id; val → vPropI Σ] 
    := (λ A R M R' M', template_mono M ∧ R = R' ∧ M = M' ∧ ↑histN ⊆ R.t1).

  Global Arguments wp_template_condition _ _ _ /.

  Global Instance templateM_satisfies_wp_template_condition R n M1 M2 TT1 TT2 Ps Qs :
    ModalityMono M1 → 
    ModalityMono M2 → 
    SolveSepSideCondition (↑histN ⊆ R.t1) →
    SatisfiesTemplateCondition wp_template_condition R (template_M n M1 M2 TT1 TT2 Ps Qs) R (template_M n M1 M2 TT1 TT2 Ps Qs).
  Proof.
    rewrite /SatisfiesTemplateCondition /= => HM1 HM2 HE.
    split => //.
    by apply template_M_is_mono.
  Qed.

  Global Instance wp_execute_reduction_compat : 
    ExecuteReductionCompatibility wp_execute_op (λᵗ E _ _, [tele_arg3 E]) wp_red_cond context_as_item_condition wp_template_condition.
  Proof.
    move => K e A e' M /= HK R R' M' [HM [<- [<- HE]]].
    revert HE.
    drop_telescope R as E t Φ => /=. clear R' => HE.
    inversion_clear HK. rewrite -H.
    rewrite -wp_bind //.
    apply bi.wand_elim_l'.
    apply bi.exist_elim => v.
    apply bi.wand_elim_l'. apply bi.pure_elim' => [Hv]. apply bi.wand_intro_r. rewrite left_id.
    do 2 rewrite bi.forall_elim /=.
    apply bi.wand_mono => //.
    apply HM => a /=.
    rewrite Hv. iIntros "HWP". by rewrite H.
  Qed.

  Proposition as_unit_fun_texan P e v Q s E :
    {{{ P }}} e @ s ; E {{{ RET v; Q }}} →
    {{{ P }}} e @ s ; E {{{ (_ : ()), RET v; Q }}}.
  Proof.
    move => HT Φ.
    rewrite HT.
    apply bi.wand_mono => //.
    apply bi.later_mono.
    rewrite (bi.forall_elim tt) //.
  Qed.

  Proposition later_if_laterN_if {PROP : bi} (P : PROP) (p : bool) :
    ▷^ (if p then 1 else 0) P ⊣⊢@{PROP} ▷?p P.
  Proof. done. Qed.

  Proposition later_if_sep {PROP : bi} (P Q : PROP) (p : bool) :
    ▷?p (P ∗ Q) ⊣⊢@{PROP} ▷?p P ∗ ▷?p Q.
  Proof. destruct p => //=. apply bi.later_sep. Qed.

  Proposition if_bool_as_nat (n : nat) (p : bool) :
    TCOr (TCAnd (TCEq n 1) (TCEq p true)) (TCAnd (TCEq n 0) (TCEq p false)) →
    n = if p then 1 else 0.
  Proof. by case => [[-> ->] | [-> ->]]. Qed.

  (* this is basically sym-ex-fupd-exist, but stated in terms of ReductionStep' *)
  Proposition texan_to_red_cond (A B : tele) n p (P : A -t> vProp Σ) e (Q : A -t> B -t> vProp Σ) (f : A -t> B -t> val) f' E1 E2 pre :
    TCOr (TCAnd (TCEq n 1) (TCEq p true)) (TCAnd (TCEq n 0) (TCEq p false)) →
    (∀.. (a : A) (b : B), tele_app (tele_app f' a) b = of_val (tele_app (tele_app f a) b)) →
    TCOr (Atomic e) (TCEq E1 E2) → 
    (* the following rule reduces to texan triple notation when B is a constructor. *)
    (∀.. a : A, ∀ Φ tid, 
      pre ∗ tele_app P a -∗ ▷ (∀.. (b : B), tele_app (tele_app Q a) b -∗ Φ (tele_app (tele_app f a) b)) -∗ WP e @ tid; E2 {{ Φ } }) →
    ReductionStep' wp_red_cond pre n (fupd E1 E2) (fupd E2 E1) A B P Q e f' [tele_arg3 E1].
  Proof.
    rewrite /ReductionStep' => /if_bool_as_nat -> 
      /tforall_forall Hf' HeE /tforall_forall HT.
    rewrite /ReductionTemplateStep /=.
    iIntros "Hpre".
    iExists (λ '(a, b), tele_app (tele_app f a) b) => /=.
    iSplitR.
    { iPureIntro. case => /= a. apply tforall_forall. apply Hf'. } 
    iStopProof.
    apply bi.forall_intro => Φ.
    apply bi.forall_intro => tid.
    apply bi.wand_intro_r.
    rewrite fupd_frame_l.
    match goal with 
    | |- (fupd ?E1 ?E2 ?Hp ⊢ wp ?s E1 ?e ?Φ) => 
      enough (Hp ⊢ wp s E2 e (fupd E2 E1 ∘ Φ))
    end.
    - destruct HeE as [He | <-].
      * rewrite -wp_atomic.
        by apply fupd_mono.
      * rewrite -fupd_wp -wp_fupd.
        by apply fupd_mono.
    - apply bi.wand_elim_r'. apply bi_texist_elim => a.
      rewrite later_if_laterN_if. apply bi.wand_intro_l. rewrite assoc.
      rewrite HT {HT}. (*
      rewrite -(wp_bind [] (fupd E2 E1 ∘ Φ) _). *)
      apply bi.wand_elim_l', bi.wand_mono => //.
      rewrite !bi_tforall_forall.
      wlog:p /(p = true) => [ | -> /=].
      {{ destruct p; [ move => H; by apply H | (move => <-; last done) => /=; apply bi.later_intro ]. } }
      apply bi.later_mono, bi.forall_mono => b.
      iIntros "HΦ HQ". by iMod ("HΦ" with "HQ").
  Qed.

  Global Instance reduction_step_from e E Φ :
    ReductionStep (wp_red_cond, [tele_arg3 E]) e ⊣ ⟨fupd E E⟩ emp; (∀ tid, WP e @ tid; E {{ Φ }}) =[▷^0]=> ∃ v, ⟨fupd E E⟩ of_val v ⊣ Φ v.
  Proof.
    rewrite /ReductionStep' /ReductionTemplateStep /=.
    iIntros "HWP".
    iExists (λ '(_, tv), (λᵗ v, v) tv). iSplitR.
    { iPureIntro. case. refine (to_tforall (TT := TeleO) _ _)=> /=. apply (to_tforall) => //=. }
    iStopProof.
    apply bi.forall_intro => Ψ.
    apply bi.forall_intro => tid.
    apply bi.wand_intro_l.
    etrans; [ | apply bi.wand_elim_l', wp_strong_mono => // ].
    rewrite bi.sep_comm.
    rewrite bi.forall_elim.
    apply bi.sep_mono_r.
    apply bi.forall_intro => v.
    rewrite (bi.forall_elim v) => /=.
    iIntros ">[_ HΦΨ] HΦ".
    by iMod ("HΦΨ" with "HΦ") as "H".
  Qed.

  Global Instance red_cond_emp_valid_atomic_no_Φ (A B : tele) P e Q f' fv w E1 E2 pre :
    TCEq (tele_app (TT := [tele_pair coPset]) (λ E, E) w) E1 →
    Atomic e →
    TCEq (to_val e) None →
    (∀.. (a : A), ∀.. (b : B), (IntoVal (tele_app (tele_app f' a) b) (tele_app (tele_app fv a) b))) →
    (* the following rule reduces to texan triple notation when B is a constructor. *)
    AsEmpValidWeak
      (ReductionStep' wp_red_cond pre 1 (fupd E1 E2) (fupd E2 E1) A B P Q e f' w)
      ((∀ tid, ∀.. a : A, 
      pre ∗ tele_app P a -∗ WP e @ tid; E2 {{ λ v, ∃.. (b : B), ⌜v = tele_app (tele_app fv a) b⌝ ∗ tele_app (tele_app Q a) b } })) | 10.
  Proof. 
    drop_telescope w as E' => /= ->.
    rewrite /AsEmpValidWeak.
    move => He1 He2 Hfv HPQ.
    eapply texan_to_red_cond.
    - left. split => //.
    - apply tforall_forall => a.
      apply tforall_forall => b.
      revert Hfv. move => /(dep_eval_tele a) /(dep_eval_tele b) <- //.
    - by left.
    - apply tforall_forall => a Φ tid /=.
      iIntros "Hpre Hlater".
      iApply (wp_step_fupd with "[Hlater]"); first by rewrite He2. reflexivity.
      { iIntros "!> !>". iApply "Hlater". } iStopProof.
      revert HPQ. rewrite bi.forall_elim.
      rewrite bi_tforall_forall.
      rewrite (bi.forall_elim a) => /bi.wand_entails ->.
      apply wp_mono => v /=.
      iIntros "[%b [-> HQ]] HΦ".
      iSpecialize ("HΦ" $! b).
      by iApply "HΦ".
  Qed.

  Global Instance red_cond_emp_valid_value_no_Φ_not_atomic (A B : tele) P e Q f' fv E1 pre w :
    TCEq (tele_app (TT := [tele_pair coPset]) (λ E, E) w) E1 →
    TCEq (to_val e) None →
    (∀.. (a : A), ∀.. (b : B), (IntoVal (tele_app (tele_app f' a) b) (tele_app (tele_app fv a) b))) →
    (* the following rule reduces to texan triple notation when B is a constructor. *)
    AsEmpValidWeak
      (ReductionStep' wp_red_cond pre 1 (fupd E1 E1) (fupd E1 E1) A B P Q e f' w)
      ((∀ tid, ∀.. a : A, 
      pre ∗ tele_app P a -∗ WP e @ tid; E1 {{ λ v, ∃.. (b : B), ⌜v = tele_app (tele_app fv a) b⌝ ∗ tele_app (tele_app Q a) b }})) | 20.
  Proof. (* so.. the texan version is stronger, since it allows us to eliminate laters? *)
    drop_telescope w as E' => /= ->.
    rewrite /AsEmpValidWeak.
    move => He Hfv HPQ.
    eapply texan_to_red_cond.
    - tc_solve.
    - apply tforall_forall => a.
      apply tforall_forall => b.
      revert Hfv. move => /(dep_eval_tele a) /(dep_eval_tele b) <- //.
    - right. done.
    - apply tforall_forall => a Φ /= tid.
      iIntros "Hpre Hlater".
      iApply (wp_step_fupd with "[Hlater]"); first by rewrite He. reflexivity.
      { iIntros "!> !>". iApply "Hlater". } iStopProof.
      revert HPQ. rewrite bi.forall_elim.
      rewrite bi_tforall_forall.
      rewrite (bi.forall_elim a).
      move => /bi.wand_entails ->.
      iApply wp_mono => v /=.
      iIntros "[%b [-> HQ]] HΦ".
      iSpecialize ("HΦ" $! b).
      by iApply "HΦ".
  Qed.

End vprop_wp_executor.

(* this instance makes iSteps work on goals built by Program, which for some reason unfolds ReductionStep' goals *)
Global Instance template_step_emp_valid {PROP : bi} (pre : PROP) `(red_cond : ReductionCondition PROP E W) e n M1 M2 (A B : tele) P' f'  Q w G :
  AsEmpValidWeak (PROP := PROP) (ReductionStep' red_cond pre n M1 M2 A B P' Q e f' w) G →
  AsEmpValidWeak (PROP := PROP) (ReductionTemplateStep red_cond (A * B) pre w e (λ pr: A * B, tele_app (tele_app f' pr.1) pr.2) (template_M (PROP := PROP) n M1 M2 A B P' Q)) G.
Proof. done. Qed.

Section abducts.
  Context `{!noprolG Σ}.

  Global Instance abduct_from_execution P Q e R K e_in' T e_out' MT MT' R' p E :
    AsExecutionOf P wp_execute_op e R →
    TCEq ((λᵗ E _ _, [tele_arg3 E]) R) E →
    ReshapeExprAnd (expr) e K e_in' (ReductionTemplateStep wp_red_cond T Q%I E e_in' e_out' MT) →
    SatisfiesContextCondition context_as_item_condition K →
    SatisfiesTemplateCondition wp_template_condition R MT R' MT' →
    HINT1 □⟨p⟩ Q ✱ [MT' $ flip wp_execute_op R' ∘ K ∘ e_out'] ⊫ [id]; P.
  Proof. intros. rewrite -H0 in H1. eapply execution_abduct_lem => //. tc_solve. Qed.

  Global Instance collect_modal_wp_value s e v Φ E :
    IntoVal e v →
    HINT1 ε₀ ✱ [fupd E E $ Φ v] ⊫ [id]; WP e @ s ; E {{ Φ }} | 10.
  Proof.
    rewrite /IntoVal /Abduct /= empty_hyp_first_eq left_id => <-.
    erewrite (wp_value_fupd _ _ Φ) => //.
  Qed.

  Global Instance prepend_modal_wp_expr e Φ E s :
    PrependModality (WP e @ s ; E {{ Φ }})%I (fupd E E) (WP e @ s; E {{ Φ }})%I | 20.
  Proof.
    rewrite /PrependModality.
    apply (anti_symm _).
    - by rewrite -{2}fupd_wp.
    - apply fupd_intro.
  Qed.

  Global Instance abduct_pure_exec e tid (Φ : val → vProp Σ) K e_in' e_out' n φ E :
    ReshapeExprAnd expr e K e_in' (∀ 𝓥, PureExec φ n (e_in' at 𝓥) (e_out' at 𝓥)) →
    SatisfiesContextCondition context_as_item_condition K →
                      (* emp -∗ forces later introduction *)
    HINT1 ε₁ ✱ [⌜φ⌝ ∗ ▷^n (emp -∗ WP (K e_out') @ tid ; E {{ Φ }}) ] ⊫ [id]; WP e @ tid ; E {{ Φ }} | 15.
  Proof.
    case => -> Hpure HK. inversion_clear HK.
    iIntros "(_ & % & Hl)" => /=.
    rewrite wp_eq /wp_def. iStopProof. iStartProof (iProp _).
    iIntros "% /= H" (𝓥 ?) "? #?". rewrite -!H.
    iApply (lifting.wp_pure_step_later _ _ (mkExpr (fill Kits e_in') _) (mkExpr (fill Kits e_out') _) φ);
      [|done|]. 
    { rewrite !fill_base_nopro. intros ?.
      by apply (pure_step_nsteps_ctx (@ectxi_language.fill nopro_ectxi_lang Kits)), Hpure. }
    iIntros "!> _". by iApply ("H" with "[//] [//] [$]").
  Qed.
End abducts.


Ltac find_reshape e K e' TC :=
  reshape_expr e ltac:(fun K' e'' => 
    unify K (fill K'); unify e' e''; 
    notypeclasses refine (ConstructReshape e (fill K') e'' _ (eq_refl) _); tc_solve ).

Global Hint Extern 4 (ReshapeExprAnd expr ?e ?K ?e' ?TC) => 
  find_reshape e K e' TC : typeclass_instances.



