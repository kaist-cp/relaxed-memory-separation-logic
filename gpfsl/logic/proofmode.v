From stdpp Require Import namespaces.
From iris.proofmode Require Import coq_tactics reduction.
From iris.proofmode Require Export proofmode.
From iris.algebra Require Import auth.
From iris.program_logic Require Import lifting.
From iris.bi Require Import bi lib.atomic.
Import bi.

From gpfsl.base_logic Require Import weakestpre na meta_data.
From gpfsl.logic Require Export lifting.

Require Import iris.prelude.options.

Lemma tac_wp_pure `{!noprolG Σ} K Δ Δ' tid E e1 e2 φ n Φ :
  (∀ 𝓥, PureExec φ n (e1 at 𝓥) (e2 at 𝓥)) →
  φ →
  MaybeIntoLaterNEnvs n Δ Δ' →
  envs_entails Δ' (WP fill K e2 @ tid; E {{ Φ }}) →
  envs_entails Δ (WP fill K e1 @ tid; E {{ Φ }}).
Proof.
  rewrite envs_entails_unseal=> Hexec ?? HΔ'. rewrite into_laterN_env_sound /=.
  rewrite HΔ' wp_eq /wp_def. iStartProof (iProp _).
  iIntros "% /= H" (𝓥 ?) "? #?".
  iApply (wp_pure_step_later _ _ (mkExpr (fill K e1) _) (mkExpr (fill K e2) _) φ);
    [|done|].
  { rewrite !fill_base_nopro. intros ?.
    by apply (pure_step_nsteps_ctx (@ectxi_language.fill nopro_ectxi_lang K)),
             Hexec. }
  iIntros "!> _". by iApply ("H" with "[//] [$]").
Qed.

Lemma tac_wp_value `{!noprolG Σ} Δ tid E Φ e v :
  IntoVal e v →
  envs_entails Δ (Φ v) → envs_entails Δ (WP e @ tid; E {{ Φ }}).
Proof. rewrite envs_entails_unseal=> ? ->. by apply wp_value. Qed.

Ltac wp_value_head := eapply tac_wp_value; [apply _|lazy beta].

Ltac wp_finish :=
  simpl_subst;        (* simplify occurences of subst/fill *)
  try wp_value_head   (* in case we have reached a value, get rid of the WP *)
  .

Tactic Notation "wp_pure" open_constr(efoc) :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (wp ?tid ?E ?e ?Q) => reshape_expr e ltac:(fun K e' =>
    unify e' efoc;
    eapply (tac_wp_pure K);
    [tc_solve                       (* PureExec *)
    |try done                       (* The pure condition for PureExec *)
    |tc_solve                       (* IntoLaters *)
    |wp_finish                      (* new goal *)])
   || fail "wp_pure: cannot find" efoc "in" e "or" efoc "is not a reduct"
  | _ => fail "wp_pure: not a 'wp'"
  end.

Ltac wp_pures :=
  iStartProof;
  first [ (* The `;[]` makes sure that no side-condition magically spawns. *)
          progress repeat (wp_pure _; [])
        | wp_finish (* In case wp_pure never ran, make sure we do the usual cleanup. *)
        ].

Lemma tac_wp_eq_loc `{!noprolG Σ} K Δ Δ' tid E i1 i2 l1 l2 q1 q2 Φ :
  ↑histN ⊆ E →
  MaybeIntoLaterNEnvs 1 Δ Δ' →
  envs_lookup i1 Δ' = Some (false, l1 ↦{q1} ?)%I →
  envs_lookup i2 Δ' = Some (false, l2 ↦{q2} ?)%I →
  envs_entails Δ' (WP fill K #(bool_decide (l1 = l2)) @ tid; E {{ Φ }}) →
  envs_entails Δ (WP fill K (BinOp EqOp #l1 #l2) @ tid; E {{ Φ }}).
Proof.
  rewrite envs_entails_unseal=> ? ? /envs_lookup_sound /=. rewrite sep_elim_l=> ?.
  move /envs_lookup_sound; rewrite sep_elim_l=> ? HΔ. rewrite -wp_bind; [|done].
  rewrite into_laterN_env_sound /=. eapply wp_eq_loc; eauto using later_mono.
Qed.

Tactic Notation "wp_eq_loc" :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (wp ?tid ?E ?e ?Q) =>
     reshape_expr e ltac:(fun K e' => eapply (tac_wp_eq_loc K));
       [try solve [ fast_done | solve_ndisj ]
       |apply _|iAssumptionCore|iAssumptionCore|simpl; try wp_value_head]
  | _ => fail "wp_pure: not a 'wp'"
  end.

Tactic Notation "wp_rec" := wp_pure (App _ _).
Tactic Notation "wp_lam" := wp_rec.
Tactic Notation "wp_let" := wp_lam.
Tactic Notation "wp_seq" := wp_let.
Tactic Notation "wp_op" := wp_pure (BinOp _ _ _) || wp_eq_loc.
Tactic Notation "wp_if" := wp_pure (If _ _ _).
Tactic Notation "wp_case" := wp_pure (Case _ _); try wp_value_head.

Lemma tac_wp_bind `{!noprolG Σ} K Δ tid E Φ e (SUB: ↑histN ⊆ E):
  envs_entails Δ (WP e @ tid; E {{ v, WP fill K (of_val v) @ tid; E {{ Φ }} }})%I →
  envs_entails Δ (WP fill K e @ tid; E {{ Φ }}).
Proof. rewrite envs_entails_unseal=> ->. by apply: wp_bind. Qed.

Ltac wp_bind_core K :=
  lazymatch eval hnf in K with
  | [] => idtac
  | _ => apply (tac_wp_bind K); [try solve [ fast_done | solve_ndisj ]|simpl]
  end.

Tactic Notation "wp_bind" open_constr(efoc) :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (wp ?tid ?E ?e ?Q) => reshape_expr e ltac:(fun K e' =>
    match e' with
    | efoc => unify e' efoc; wp_bind_core K
    end) || fail "wp_bind: cannot find" efoc "in" e
  | _ => fail "wp_bind: not a 'wp'"
  end.

Section heap.
Context `{!noprolG Σ}.
Implicit Types P Q : vProp Σ.
Implicit Types Φ : val → vProp Σ.
Implicit Types Δ : envs (vPropI Σ).

Lemma tac_wp_alloc K Δ Δ' E j0 j1 j2 (n : Z) Φ tid :
  ↑histN ⊆ E → 0 < n →
  MaybeIntoLaterNEnvs 1 Δ Δ' →
  (∀ l (sz: nat), n = sz → ∃ Δ'',
    envs_app false (Esnoc (Esnoc (Esnoc Enil
                              j0 ([∗ list] i ∈ seq 0 (Z.to_nat n), meta_token (l >> i) ⊤))
                            j1 (l ↦∗ repeat #☠ (Z.to_nat n)))
                    j2 ⎡†l…sz⎤) Δ'
      = Some Δ'' ∧
    envs_entails Δ'' (WP fill K #l @ tid; E {{ Φ }})) →
  envs_entails Δ (WP fill K (Alloc #n) @ tid; E {{ Φ }}).
Proof.
  rewrite envs_entails_unseal=> ??? HΔ. rewrite -wp_bind; [|done].
  eapply wand_apply; first exact:wp_alloc.
  rewrite -persistent_and_sep. apply and_intro; first by auto.
  rewrite into_laterN_env_sound; apply later_mono, forall_intro=> l.
  destruct (HΔ l (Z.to_nat n)) as (Δ''&?&HΔ'); [rewrite Z2Nat.id //; lia|].
  rewrite envs_app_sound //; simpl. by rewrite right_id HΔ'.
Qed.

Lemma tac_wp_free K Δ Δ' Δ'' Δ''' E i1 i2 (n : Z) (n' : nat) l Φ tid :
  ↑histN ⊆ E → n = n' →
  MaybeIntoLaterNEnvs 1 Δ Δ' →
  (∃ vl, envs_lookup i1 Δ' = Some (false, l ↦∗ vl)%I ∧ n' = length vl) ∨
  (envs_lookup i1 Δ' = Some (false, own_loc_vec l 1 n')%I) →
  envs_delete false i1 false Δ' = Δ'' →
  envs_lookup i2 Δ'' = Some (false, ⎡†l…n'⎤)%I →
  envs_delete false i2 false Δ'' = Δ''' →
  envs_entails Δ''' (WP fill K #☠ @ tid; E {{ Φ }}) →
  envs_entails Δ (WP fill K (Free #n #l) @ tid; E {{ Φ }}).
Proof.
  rewrite envs_entails_unseal; intros ? -> ?[[vl[? ->]]|?] <- ? <- HΔ;
    (rewrite -wp_bind; [|done]); rewrite into_laterN_env_sound.
  - do 2 (rewrite envs_lookup_sound //). rewrite HΔ. iIntros "(H&?&WP) /=".
    iApply (wp_free with "[-WP]"); [done|lia| |by auto]. rewrite Nat2Z.id.
    iIntros "{$∗} !>". clear. iInduction vl as [|v vl] "IH" forall (l).
    + by rewrite own_loc_vec_nil.
    + rewrite /= own_loc_vec_S own_loc_na_vec_cons. iDestruct "H" as "[Hv Hlv]".
      iSplitR "Hlv"; [by iApply (own_loc_na_own_loc with "Hv")|by iApply "IH"].
  - do 2 (rewrite envs_lookup_sound //). rewrite HΔ. iIntros "(H&?&WP) /=".
    iApply (wp_free with "[-WP]"); [done|lia| |by auto]. rewrite Nat2Z.id. iFrame.
Qed.

Lemma tac_wp_read K Δ Δ' E i l q v Φ tid :
  ↑histN ⊆ E → MaybeIntoLaterNEnvs 1 Δ Δ' →
  envs_lookup i Δ' = Some (false, l ↦{q} v)%I →
  envs_entails Δ' (WP fill K v @ tid; E {{ Φ }}) →
  envs_entails Δ (WP fill K !#l @ tid; E {{ Φ }}).
Proof.
  rewrite envs_entails_unseal=>??? HΔ'.
  rewrite -wp_bind; [|done].
  rewrite into_laterN_env_sound envs_lookup_split // HΔ'; simpl.
  iIntros "[>??]". by iApply (wp_read with "[$]").
Qed.

Lemma tac_wp_write K Δ Δ' Δ'' E i l o e v' Φ tid :
  ↑histN ⊆ E → IntoVal e v' →
  MaybeIntoLaterNEnvs 1 Δ Δ' →
  (∃ v, envs_lookup i Δ' = Some (false, l ↦ v)%I) ∨
  envs_lookup i Δ' = Some (false, l ↦ ?)%I →
  envs_simple_replace i false (Esnoc Enil i (l ↦ v')) Δ' = Some Δ'' →
  envs_entails Δ'' (WP fill K #☠ @ tid; E {{ Φ }}) →
  envs_entails Δ (WP fill K (Write o #l e) @ tid; E {{ Φ }}).
Proof.
  intros ? <-. rewrite envs_entails_unseal; intros ?[[??]|?]? HΔ''.
  - rewrite -wp_bind // into_laterN_env_sound envs_simple_replace_sound //; simpl.
    rewrite HΔ'' right_id. iIntros "[>Hl ?]".
    iApply (wp_write with "[Hl]"); [done| |done].
    by iApply (own_loc_na_own_loc with "Hl").
  - rewrite -wp_bind // into_laterN_env_sound envs_simple_replace_sound //; simpl.
    rewrite HΔ'' right_id. iIntros "[>Hl ?]".
    by iApply (wp_write with "[Hl]").
Qed.
End heap.

(** The tactic [wp_apply_core lem tac_suc tac_fail] evaluates [lem] to a
hypothesis [H] that can be applied, and then runs [wp_bind_core K; tac_suc H]
for every possible evaluation context [K].

- The tactic [tac_suc] should do [iApplyHyp H] to actually apply the hypothesis,
  but can perform other operations in addition (see [wp_apply] and [awp_apply]
  below).
- The tactic [tac_fail cont] is called when [tac_suc H] fails for all evaluation
  contexts [K], and can perform further operations before invoking [cont] to
  try again.

TC resolution of [lem] premises happens *after* [tac_suc H] got executed. *)
Ltac wp_apply_core lem tac_suc tac_fail := first
  [iPoseProofCore lem as false (fun H =>
     lazymatch goal with
     | |- envs_entails _ (wp ?tid ?E ?e ?Q) =>
       reshape_expr e ltac:(fun K e' =>
         wp_bind_core K; tac_suc H)
     | _ => fail 1 "wp_apply: not a 'wp'"
     end)
  |tac_fail ltac:(fun _ => wp_apply_core lem tac_suc tac_fail)
  |let P := type of lem in
   fail "wp_apply: cannot apply" lem ":" P ].

Tactic Notation "wp_apply" open_constr(lem) :=
  wp_apply_core lem ltac:(fun H => iApplyHyp H; try iNext; simpl)
                    ltac:(fun cont => fail).
Tactic Notation "wp_smart_apply" open_constr(lem) :=
  wp_apply_core lem ltac:(fun H => iApplyHyp H; try iNext; simpl)
                  ltac:(fun cont => wp_pure _; []; cont ()).

(** Tactic tailored for atomic triples: just runs [iAuIntro] on the goal, as
atomic triples always have an atomic update as their premise. *)
Tactic Notation "awp_apply" open_constr(lem) :=
  wp_apply_core lem ltac:(fun H => iApplyHyp H) ltac:(fun cont => fail);
  last iAuIntro.

Tactic Notation "wp_alloc" ident(l) "as" constr(Hm) constr(H) constr(Hf) :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (wp ?tid ?E ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_wp_alloc K _ _ _ Hm H Hf);
                                [try solve [ fast_done | solve_ndisj ]|..])
      |fail 1 "wp_alloc: cannot find 'Alloc' in" e];
    [try fast_done
    |apply _
    |let sz := fresh "sz" in let Hsz := fresh "Hsz" in
     first [intros l sz Hsz | fail 1 "wp_alloc:" l "not fresh"];
     (* If Hsz is "constant Z = nat", change that to an equation on nat and
        potentially substitute away the sz. *)
     try (match goal with Hsz : ?x = _ |- _ => rewrite <-(Z2Nat.id x) in Hsz; last done end;
          apply Nat2Z.inj in Hsz;
          try (cbv [Z.to_nat Pos.to_nat] in Hsz;
               simpl in Hsz;
               (* Substitute only if we have a literal nat. *)
               match goal with Hsz : S _ = _ |- _ => subst sz end));
      eexists; split;
        [pm_reflexivity || fail "wp_alloc:" Hm "or" H "or" Hf "not fresh"
        |simpl; try wp_value_head]]
  | _ => fail "wp_alloc: not a 'wp'"
  end.

Tactic Notation "wp_alloc" ident(l) :=
  let Hm := iFresh in let H := iFresh in let Hf := iFresh in wp_alloc l as Hm H Hf.

Tactic Notation "wp_free" :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (wp ?tid ?E ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_wp_free K);
                         [try solve [ fast_done | solve_ndisj ]|..])
      |fail 1 "wp_free: cannot find 'Free' in" e];
    [try fast_done
    |apply _
    |first
       [left; eexists; split; [iAssumptionCore|fast_done]
       |right; iAssumptionCore
       |let l := match goal with |- _ = Some (_, own_loc_vec ?l _ _)%I => l end in
        fail 1 "wp_free: cannot find" l "↦∗ ?"]
    |pm_reflexivity
    |let l := match goal with |- _ = Some (_, ⎡† ?l … _⎤%I) => l end in
     iAssumptionCore || fail "wp_free: cannot find †" l "… ?"
    |pm_reflexivity
    |simpl; try first [wp_pure (Seq (Lit LitPoison) _)|wp_value_head]]
  | _ => fail "wp_free: not a 'wp'"
  end.

Tactic Notation "wp_read" :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (wp ?tid ?E ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_wp_read K);
                                [try solve [ fast_done | solve_ndisj ]|..])
      |fail 1 "wp_read: cannot find 'Read' in" e];
    [apply _
    |let l := match goal with |- _ = Some (_, (?l ↦{_} _)%I) => l end in
     iAssumptionCore || fail "wp_read: cannot find" l "↦ ?"
    |simpl; try wp_value_head]
  | _ => fail "wp_read: not a 'wp'"
  end.

Tactic Notation "wp_write" :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (wp ?tid ?E ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_wp_write K);
                                [try solve [ fast_done | solve_ndisj ]|apply _|..])
      |fail 1 "wp_write: cannot find 'Write' in" e];
    [apply _
    |first
       [left; eexists; iAssumptionCore |
        right; iAssumptionCore |
        right;
        let l := match goal with |- _ = Some (_, ?l ↦{_} ?)%I => l end in
        fail 1 "wp_write: cannot find" l "↦ ?"]
    |pm_reflexivity
    |simpl; try first [wp_pure (Seq (Lit LitPoison) _)|wp_value_head]]
  | _ => fail "wp_write: not a 'wp'"
  end.
