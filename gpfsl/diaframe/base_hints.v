
From diaframe Require Import proofmode_base.
From gpfsl.logic Require Import proofmode atomics invariants.
From gpfsl.base_logic Require Import meta_data.
From gpfsl.examples Require Import loc_helper uniq_token.
From gpfsl.examples Require Import sflib.
From Hammer Require Import Tactics.
From iris.proofmode Require Import coq_tactics ltac_tactics reduction.

Require Import iris.prelude.options.


#[global] Typeclasses Opaque prefix.


Section hints.

Context `{!noprolG Σ, !atomicG Σ}.


#[global] Instance biabd_atomic_pts_to_from_na l v E:
    HINT l ↦ v ✱ [V ; ⊒V ]
    ⊫ [fupd E E]
      γ ζ; l at↦{γ} ζ ✱
        [ ∃ t V', ⌜ ζ = {[t := (v, V')]} ⌝ ∗ ⌜ V ⊑ V' ⌝ ∗ ⊒V' ∗ l sy⊒{γ} ζ].
Proof.
  iStep 2 as (V) "⊒V l↦".
  iMod (AtomicPtsTo_from_na_rel with "⊒V l↦") as (γx t V') "(#⊒V' & %LE & SN & l↦)".
  iDestruct (AtomicPtsTo_SW_to_CON_1 with "l↦ SN") as "[l↦ sy⊒]".
  iSteps.
Qed.

#[global] Instance biabd_sn_obs_from_sy_obs p l γ ζ:
    HINT □⟨p⟩ l sy⊒{γ} ζ ✱ [- ; True ]
    ⊫ [id]
    ; l sn⊒{γ} ζ ✱  [ True ].
Proof.
  iStep as "sy⊒". rewrite bi.intuitionistically_if_elim.
  iDestruct (AtomicSync_AtomicSeen with "sy⊒") as "sn⊒".
  iSteps.
Qed.

(* copied from diaframe_heap_lang.loc_map *)
#[global] Instance mergable_consume_meta_agree (l : loc) (N : namespace) `{Countable A} (x1 x2 : A) :
    MergableConsume (meta l N x1) false (λ p Pin Pout,
      TCAnd (TCEq Pin (meta l N x2)) $
            TCEq Pout ⌜x1 = x2⌝%I).
Proof.
  intros p Pin Pout [-> ->].
  rewrite bi.intuitionistically_if_elim.
  iStep as "HN1 HN2".
  iDestruct (meta_agree with "HN1 HN2") as %->. auto.
Qed.


(* `MatchValue a b` equals to `a = b` and when it is introduced, diaframe will try to find a proposition `c = b` and induce `a = c`.
  This is useful when using equalities that cannot be substitued, such as `Some a = ~~`. *)
Definition MatchValue_def {PROP : bi} {A} (matchee v : A) : PROP := ⌜matchee = v⌝.
Definition MatchValue_aux : seal (@MatchValue_def). Proof. by eexists. Qed.
Definition MatchValue := MatchValue_aux.(unseal).
#[global] Opaque MatchValue.
#[global] Arguments MatchValue {_ _} _ _ : simpl never.

#[global] Lemma MatchValue_eq : @MatchValue = @MatchValue_def.
Proof. rewrite -MatchValue_aux.(seal_eq) //. Qed.


#[global] Instance MatchValue_objective {A} (matchee v : A) : Objective (@MatchValue (vProp Σ) A matchee v).
Proof. rewrite MatchValue_eq. apply _. Qed.
#[global] Instance MatchValue_timeless {PROP : bi} {A} (matchee v : A) : Timeless (@MatchValue PROP A matchee v).
Proof. rewrite MatchValue_eq. apply _. Qed.
#[global] Instance MatchValue_persistent {PROP : bi} {A} (matchee v : A) : Persistent (@MatchValue PROP A matchee v).
Proof. rewrite MatchValue_eq. apply _. Qed.

Class FindEq {A} (a b : A) := find_eq : a = b.
#[global] Hint Mode FindEq + - - : typeclass_instances.

#[global] Instance mergable_consume_simplify_match_value {PROP : bi} {A} (m m' v : A):
  MergableConsume (PROP := PROP) (MatchValue m v) true (λ p Pin Pout,
  TCAnd (TCEq Pin (ε₀)) $
  TCAnd (FindEq v m') $
    TCEq Pout ⌜ m = m' ⌝)%I.
Proof using All.
  intros p Pin Pout [-> [find ->]].
  rewrite bi.intuitionistically_if_elim MatchValue_eq. iIntros. sauto.
Qed.

#[global] Instance biabd_MatchValue_from_FindEq `{BiAffine PROP} {A} a b :
  FindEq a b →
  HINT ε₀ ✱ [-; emp ]
  ⊫ [id]
  ; @MatchValue PROP A a b ✱ [ emp ] | 50.
Proof. rewrite MatchValue_eq. intros. iSteps. Qed.

#[global] Instance biabd_MatchValue_from_pure `{BiAffine PROP} {A} a b :
  HINT ε₀ ✱ [-; ⌜a = b⌝ ]
  ⊫ [id]
  ; @MatchValue PROP A a b ✱ [ emp ] | 100.
Proof. rewrite MatchValue_eq. iSteps. Qed.

Definition ask_for_def {PROP : bi} {A} (a : A) : PROP := emp.
Definition ask_for_aux : seal (@ask_for_def). Proof. by eexists. Qed.
Definition ask_for := ask_for_aux.(unseal).
Lemma ask_for_eq : @ask_for = @ask_for_def.
Proof. rewrite -ask_for_aux.(seal_eq) //. Qed.
#[global] Arguments ask_for {_ _} _ : simpl never.

Definition ask_for'_def {PROP : bi} {A} (a : A) : PROP := emp.
Definition ask_for'_aux : seal (@ask_for_def). Proof. by eexists. Qed.
Definition ask_for' := ask_for'_aux.(unseal).
Lemma ask_for'_eq : @ask_for' = @ask_for_def.
Proof. rewrite -ask_for'_aux.(seal_eq) //. Qed.
#[global] Arguments ask_for' {_ _} _ : simpl never.

#[global] Opaque ask_for ask_for'.

#[global] Instance ask_for_Objective {I PROP A} (a : A) : Objective (I := I) (PROP := PROP) (ask_for a).
Proof. rewrite ask_for_eq. tc_solve. Qed.
#[global] Instance ask_for_Timeless `{BiAffine PROP} {A} (a : A) : Timeless (PROP := PROP) (ask_for a).
Proof. rewrite ask_for_eq. tc_solve. Qed.
#[global] Instance ask_for_Persistent {PROP} {A} (a : A)  : Persistent (PROP := PROP) (ask_for a).
Proof. rewrite ask_for_eq. tc_solve. Qed.  

#[global] Instance biabd_ask_for `{BiAffine PROP} {A} (a : A) :
  HINT ε₀ ✱ [-; ask_for' a  ]
  ⊫ [id]
  ; @ask_for PROP _ a ✱ [ emp ] | 10.
Proof. rewrite /BiAbd ask_for_eq /ask_for_def //=. iSteps. Qed.


#[global] Instance biabd_ask_for' `{BiAffine PROP} {A} (a : A) :
  (* SolveSepSideCondition below is to stop this hint from making 'a' into an existential variable... there should be a better way. *)
  SolveSepSideCondition (a = a) →
  HINT ε₀ ✱ [-; emp ]
  ⊫ [id]
  ; @ask_for' PROP _ a ✱ [ emp ] | 10.
Proof. rewrite /BiAbd ask_for'_eq /ask_for_def //=. iSteps. Qed.

#[global] Instance mergable_consume_remove_ask_for `{BiAffine PROP} {A} (a : A) :
  MergableConsume (PROP := PROP) (ask_for a) true (λ p Pin Pout,
    TCAnd (TCEq Pin (ε₀)) $
      TCEq Pout emp)%I.
Proof. intros p Pin Pout [-> ->]. iSteps. Qed.

Definition ask_optional {PROP : bi} {A} oa (a : A) : PROP :=
  ask_for oa ∗
  ⌜ match oa with
    | Some a' => a = a'
    | None => True
  end ⌝.

#[global] Instance biabd_big_sepL_app `{BiAffine PROP} {A} l1 l2 (Φ : nat → A → PROP) :
  HINT ε₀ ✱ [-; ([∗ list] k↦y ∈ l1, Φ k y) ∗ ([∗ list] k↦y ∈ l2, Φ (length l1 + k)%nat y) ]
  ⊫ [id]
  ; ([∗ list] k↦y ∈ (l1 ++ l2), Φ k y) ✱ [ emp ] | 30.
Proof. iStep. iSplitL; [|done]. iApply (big_sepL_app). iFrame. Qed.

#[global] Instance into_sep_careful_big_sepL_app `{BiAffine PROP} {A} l1 l2 (Φ : nat → A → PROP) :
  IntoSepCareful ([∗ list] k↦y ∈ (l1 ++ l2), Φ k y) ([∗ list] k↦y ∈ l1, Φ k y) ([∗ list] k↦y ∈ l2, Φ (length l1 + k)%nat y).
Proof. rewrite /IntoSepCareful. iIntros "A". iDestruct (big_sepL_app with "A") as "$". Qed.

#[global] Instance biabd_big_sepL_cons `{BiAffine PROP} {A} x l (Φ : nat → A → PROP) :
  HINT ε₁ ✱ [-;  Φ 0%nat x ∗ ([∗ list] k↦y ∈ l, Φ (S k) y) ]
  ⊫ [id]
  ; ([∗ list] k↦y ∈ (x :: l), Φ k y) ✱ [ emp ] | 30.
Proof. iSteps. Qed.

(* Todo: make this local to tstack? *)
#[global] Instance biabd_big_sepL_mono `{BiAffine PROP} {A} p l (Φ Ψ : nat → A → PROP) :
  HINT □⟨ p ⟩ [∗ list] k↦y ∈ l, Φ k y ✱ [-;  ⌜ ∀ (k : nat) (y : A), l !! k = Some y → Φ k y -∗ Ψ k y ⌝ ]
  ⊫ [id]
  ; ([∗ list] k↦y ∈ l, Ψ k y) ✱ [ emp ] | 980.
Proof. iStep as (?) "Hl". rewrite bi.intuitionistically_if_elim. iDestruct (big_sepL_mono with "Hl") as "$". done. Qed.

#[global] Instance biabd_big_sepM_insert `{BiAffine PROP} {A} (x : A) m (Φ : nat → A → PROP)
  `{!TCOr (∀ y, Affine (Φ i y)) (Absorbing (Φ i x))} :
  HINT ε₁ ✱ [-;  Φ i x ∗ [∗ map] k↦y ∈ m, Φ k y ]
  ⊫ [id]
  ; [∗ map] k↦y ∈ <[i:=x]> m, Φ k y ✱ [ emp ] | 30.
Proof. iStep as "A B". iDestruct (big_sepM_insert_2 with "A B") as "$". Qed.

#[global] Instance biabd_big_sepM_insert_later `{BiAffine PROP} {A} (x : A) m (Φ : nat → A → PROP)
  `{!TCOr (∀ y, Affine (Φ i y)) (Absorbing (Φ i x))} :
  HINT ε₁ ✱ [-;  ▷ Φ i x ∗ ▷ [∗ map] k↦y ∈ m, Φ k y ]
  ⊫ [id]
  ; ▷ [∗ map] k↦y ∈ <[i:=x]> m, Φ k y ✱ [ emp ] | 30.
Proof. iStep as "A B". iSplitL; [|done]. iModIntro. iDestruct (big_sepM_insert_2 with "A B") as "$". Qed.


#[global] Instance own_loc_into_exist_careful l q :
  IntoExistCareful (l ↦{q} ?) (λ t, ∃ m, l p↦{q} {[t := m]})%I.
Proof. rewrite own_loc_eq /own_loc_def //. Qed.

#[global] Instance own_loc_from_exist_careful l q :
  FromExistCareful ( l ↦{q} ?) (λ v, l ↦{q} v ∗ emp)%I.
Proof. rewrite /FromExistCareful. iIntros "(%v & l↦ & _)". iApply own_loc_na_own_loc. done. Qed.

#[global] Instance own_loc_na_any_into_exist_careful l q :
  IntoExistCareful (l ↦{q} -) (λ v, l ↦{q} v)%I.
Proof. done. Qed.

#[global] Instance own_loc_na_any_from_exist_careful l q :
  FromExistCareful (l ↦{q} -) (λ v, l ↦{q} v ∗ emp)%I.
Proof. rewrite /FromExistCareful /own_loc_na_any. iIntros "[%x [l↦ _]]". iExists _. done. Qed.

#[global] Instance mergable_persist_own_loc_na_agree l V1 V2 q1 q2 v1 v2 :
  MergablePersist (@{V1} l ↦{q1} v1) (λ p Pin Pout,
  TCAnd (TCEq Pin (@{V2} l ↦{q2} v2)) $
        TCEq Pout ⌜v1 = v2⌝%I)%I.
Proof.
  intros p Pin Pout [-> ->].
  rewrite bi.intuitionistically_if_elim.
  iIntros "[A B]".
  iDestruct (view_at_subjectively with "A") as "A".
  iDestruct (view_at_subjectively with "B") as "B".
  iDestruct (own_loc_na_agree_subjectively with "A B") as %->.  auto.
Qed.

#[global] Instance simplify_litv_eq a b :
  SimplifyPureHyp (LitV a = LitV b) (a = b).
Proof. by inversion 1. Qed.

#[global] Instance simplify_oloc_to_lit_eq_loc_l (l : loc) ol :
  SimplifyPureHyp (LitLoc l = (oloc_to_lit ol)) (ol = Some l).
Proof. destruct ol; inversion 1. done. Qed.

#[global] Instance simplify_oloc_to_lit_eq_loc_r (l : loc) ol :
  SimplifyPureHyp ((oloc_to_lit ol) = LitLoc l) (ol = Some l).
Proof. destruct ol; inversion 1. done. Qed.

#[global] Instance simplify_bool_decide P `{Decision P} :
  SimplifyPureHypSafe (Is_true (bool_decide P)) (P).
Proof. split; [by apply (bool_decide_unpack P)|by apply bool_decide_pack]. Qed.


Definition Peek {PROP : bi} (P : PROP) : PROP := emp.
#[global] Arguments Peek {_} _ : simpl never.

#[global] Instance Peek_objective (P : vProp Σ) : Objective (Peek P) := _.
#[global] Instance Peek_persistent {PROP : bi} (P : PROP) : Persistent (Peek P) := _.
#[global] Instance Peek_timeless `{BiAffine PROP} (P : PROP) : Timeless (Peek P) := _.
#[global] Typeclasses Opaque Peek.

#[global] Instance biabd_peek `{BiAffine PROP} (P : PROP) :
  HINT ε₀ ✱ [-; P]
    ⊫ [id]
  ; Peek P ✱ [ P ] .
Proof. unfold Peek. iSteps. Qed.

#[global] Instance mergable_consume_remove_Peek `{BiAffine PROP} (P : PROP):
  MergableConsume (Peek P) true (λ p Pin Pout,
    TCAnd (TCEq Pin (ε₀)) $
      TCEq Pout emp)%I.
Proof. intros ???[-> ->]. iSteps. Qed.

(* `If b P` is used for try_search technique. For a `If b P` goal, diaframe will try to acquire P, and if it fails it will just set b to false and move on. *)
Definition If_def {PROP : bi} (b : bool) P : PROP := if (b) then P else emp%I.
Definition If_aux : seal (@If_def). Proof. by eexists. Qed.
Definition If := If_aux.(unseal).
#[global] Opaque If.
#[global] Arguments If {_ _} _ : simpl never.
Lemma If_eq : @If = @If_def.
Proof. rewrite -If_aux.(seal_eq) //. Qed.
#[global] Opaque If.
#[global] Arguments If {_} _ _ : simpl never.

(* #[global] Instance If_persistent {PROP : bi} b (P : PROP) :
  Persistent P → Persistent (If b P).
Proof. rewrite If_eq. destruct b; [auto|apply _]. Qed.
#[global] Instance If_timeless `{BiAffine PROP} b (P : PROP) :
  Timeless P → Timeless (If b P).
Proof. rewrite If_eq. destruct b;[auto|apply _]. Qed. *)

#[global] Instance biabd_search_if_fail `{BiAffine PROP} (P : PROP) :
  HINT ε₁ ✱ [-; emp]
    ⊫ [id]
  ; If false P ✱ [ emp ] .
Proof. rewrite If_eq. iSteps. Qed.

(*
(* this might slow down search for other resources. *)
#[global] Instance biabd_search_if_success {PROP : bi} {TTl TTr : tele} (P : PROP) p Q Qg M R S :
  (TC∀.. (tt : TTr), TCEq (tele_app Qg tt) (If true (tele_app Q tt))) →
  BiAbd p P Q M R S →
  ModalityMono M →
  BiAbd (TTl := TTl) p P Qg M R S.
Proof.
  rewrite /BiAbd => /tforall_forall HEq /tforall_forall Parent HM . apply tforall_forall => ttl.
  iIntros "[P R]".
  iDestruct (Parent with "[$P $R]") as "QS". iApply (HM with "[$]"). apply bi_texist_mono => ttr.
  rewrite HEq If_eq //.
Qed. *)

#[global] Instance biabd_search_if_success_simple {PROP : bi} p P :
  HINT □⟨ p ⟩ P ✱ [-; emp ]
  ⊫ [id]
  ; @If PROP true P ✱ [ emp ] | 0.
Proof.
  iStep. rewrite If_eq bi.intuitionistically_if_elim. iSteps.
Qed.

Definition test_if l v :
  (l ↦ v) -∗
  ∃ b l v, If b (l ↦ v) ∗ ⌜ b = true ⌝.
Proof. iSteps. Qed.

#[global] Instance mergable_consume_destruct_If `{BiAffine PROP} b (P : PROP) :
  MergableConsume (If b P) true (λ p Pin Pout,
    TCAnd (TCEq Pin (ε₀)) $
      TCEq Pout (if b then P else emp))%I.
Proof. rewrite If_eq => p Pin Pout [-> ->]. iSteps. Qed.

#[global] Instance mergable_consume_destruct_If_later `{BiAffine PROP} b (P : PROP) :
  MergableConsume (▷ If b P) true (λ p Pin Pout,
    TCAnd (TCEq Pin (ε₀)) $
      TCEq Pout (▷ if b then P else emp))%I.
Proof. rewrite If_eq => p Pin Pout [-> ->]. destruct b; iSteps. Qed.

#[global] Instance biabd_points_to_leak_half l p v V1 V2 :
  SolveSepSideCondition (V1 ⊑ V2) →
  HINT @{V1} l ↦{p} v ✱ [-; emp ]
  ⊫ [id]
  ; @{V2} l ↦{p / 2} v ✱ [ @{V1} l ↦{p / 2} v ∗ emp ] | 0.
Proof.
  intros LE. iStep as "l↦".
  iDestruct "l↦" as "[l1 l2]".
  iFrame.
Qed.

#[global] Instance biabd_points_to_leak_half' V l p v :
  HINT @{V} l ↦{p} v ✱ [-; emp ]
  ⊫ [id]
  q v' V'; @{V'} l ↦{q} v' ✱ [ ⌜ q = (p / 2)%Qp ∧ V' = V ∧ v' = v ⌝ ∗ @{V} l ↦{q} v  ] | 0.
Proof.
  iStep as "l↦". iDestruct "l↦" as "[? ?]". iSteps.
Qed.

#[global] Instance simplify_lit_neq_same lt :
  SimplifyPureHypSafe (lit_neq lt lt) False.
Proof. split; [by inversion 1|done]. Qed.

#[global] Instance remove_emp_intuitionistically `{BiAffine PROP} :
  MergableConsume (PROP := PROP) (□ emp) true (λ p Pin Pout,
    TCAnd (TCEq Pin (ε₀)) $
          TCEq Pout (emp)%I)%I.
Proof. intros p Pin Pout [-> ->]. iSteps. Qed.

#[global] Instance mergable_consume_UTok_unique `{!uniqTokG Σ} γ :
  MergableConsume (UTok γ) true (λ p Pin Pout,
  TCAnd (TCEq Pin (UTok γ)) $
        TCEq Pout (False)%I)%I.
Proof.
  intros p Pin Pout [-> ->]. rewrite bi.intuitionistically_if_elim.
  iIntros "[A B]". iDestruct (UTok_unique with "A B") as "$".
Qed.

#[global] Instance simplify_list_lookup_singleton_Some {A} (a : A) (i : nat) v :
  SimplifyPureHypSafe (Some v = [a] !! i) (i = 0%nat ∧ v = a).
Proof using All. split; [|naive_solver]. intros. symmetry in H. rewrite list_lookup_singleton_Some in H. sauto. Qed.

#[global] Instance simplify_encode_eq {A} (a1 a2 : A) `{Countable A} :
  SimplifyPureHypSafe (encode a1 = encode a2) (a1 = a2).
Proof using All. split; [|naive_solver]. intros. by apply (inj encode) in H0. Qed.

(* Allow iSplit for SolveSep goals *)
#[global] Instance solvesep_fromand {PROP : bi} (L G : PROP) M MG :
  Persistent L →
  ModalityStrongMono M →
  AbsorbModal G M MG →
  FromAnd (SolveSep (TT := TeleO) M L G) (L) MG | 999. 
Proof. 
  rewrite /FromAnd. unseal_diaframe => /= PL [HM1 HM2] ->. iIntros "[A B]".
  iAssert (M (G ∗ L))%I with "[-]" as "A". { iApply HM2. iFrame. }
  iApply (HM1 with "A"). rewrite comm. eauto.
Qed.
  
End hints.

#[global] Hint Extern 5 (FindEq _ _) => fast_done : typeclass_instances.

#[global] Hint Extern 4 (_ ## _) => solve_ndisj : solve_pure_add.
#[global] Hint Extern 10 (BehindModal ?M (?a = ?b)) => fast_done : solve_pure_add.
(* Some extra hints. *)
#[global] Hint Extern 50 (@subseteq ?A _ ?a ?b) =>
  try (let ADef := eval unfold A in A in
  change ADef with A);
  change (@union A _) with (@join A _);
  progress (change (@subseteq A _) with (@sqsubseteq A _));
  solve [pure_solver.trySolvePure] : solve_pure_add.
  (* above used to be: 'enough (a ⊑ b); [done| pure_solver.trySolvePure]'
    which was enough for [solve_lat]. Changed to above to be better for [weak_lat_solver] *)

#[global] Hint Extern 50 (_ = _) => f_equal : solve_pure_eq_add.

#[global] Hint Extern 2 (oloc_to_lit ?a = ?b) =>
  match goal with
  | |- (oloc_to_lit ?a = oloc_to_lit ?b) => f_equal
  | |- (oloc_to_lit ?a = ?b) => is_evar a; assert_fails (is_evar b) ;
    match b with
    | LitInt 0 => assert (a = None); done
    | LitLoc ?l => assert (a = Some l); done
    | _ => fail
    end
  end : solve_pure_eq_add.


#[local] Definition is_anon (A : ident) :=
  match A with
  | IAnon _ => true
  | _ => false
  end.

(* Clear all anonymous resources in the intuitionistic context. *)
#[global] Ltac iClearAnonymousIntuitionistics :=
  lazymatch goal with
  | |- envs_entails ?Δ _ =>
    let Hs := pm_eval (filter is_anon (env_dom (env_intuitionistic Δ))) in
    let Hs := (eval cbv in Hs) in (* Not exactly sure what this does. Just putting it here following iElaborateSelPat_go. *)
    iClear Hs
  end.


#[global] Hint Extern 4 (oloc_to_lit ?l ≠ ☠%V) =>
  by destruct l : solve_pure_add.

(* [set_solver] uses naive_solver, which causes it to take a long time to fail.
Note: This is neither strictly weaker nor stronger than [set_solver-]. *)
Tactic Notation "fast_set_solver" :=
  try fast_done;
  intros; setoid_subst;
  set_unfold;
  intros; setoid_subst;
  try match goal with |- _ ∈ _ => apply dec_stable end;
  by auto 12.

#[global] Hint Extern 250 (_ ∈ _) => fast_set_solver : solve_pure_add.
#[global] Hint Extern 250 (_ ⊆ _) => fast_set_solver : solve_pure_add.
#[global] Hint Extern 0 (Is_true (bool_decide _)) => apply bool_decide_pack; pure_solver.trySolvePure : core solve_pure_add.
#[global] Hint Extern 0 (NW _) => unfold NW; pure_solver.trySolvePure : solve_pure_add.