From gpfsl.examples Require Import sflib.

From iris.algebra Require Import auth gset gmap agree.
From iris.proofmode Require Import tactics.
From iris.base_logic.lib Require Import ghost_var.

From gpfsl.base_logic Require Import meta_data.
From gpfsl.logic Require Import logatom atomics invariants.

From gpfsl.logic Require Import repeat_loop new_delete.
From gpfsl.examples Require Import map_seq loc_helper.
From gpfsl.examples.algebra Require Import set.
From gpfsl.examples.folly Require Import spec_turnSequencer_composition spec_singleElementQueue_composition code_turnSequencer code_singleElementQueue.
From gpfsl.examples.omo Require Import omo omo_preds omo_preds_diaframe append_only_loc.

From gpfsl.diaframe Require Import vprop_weakestpre spec_notation
 vprop_weakestpre_logatom atom_spec_notation proof_automation omo_specs omo_hints.

From diaframe Require Import proofmode_base lib.except_zero own_hints steps.verify_tac util_instances.
From diaframe.symb_exec Require Import weakestpre_logatom.

Require Import iris.prelude.options.

Class seqG Σ := SeqG {
  seq_omoGeneralG :> omoGeneralG Σ;
  seq_omoG :> omoSpecificG Σ seq_event seq_state;
  seq_tseqG :> omoSpecificG Σ tseq_event tseq_state;
  seq_aolocG :> appendOnlyLocG Σ;
  seq_data_gvarG :> ghost_varG Σ Z;
  seq_ticketG :> inG Σ (setUR nat);
}.

Definition seqΣ : gFunctors := #[
  omoGeneralΣ;
  omoSpecificΣ seq_event seq_state;
  omoSpecificΣ tseq_event tseq_state;
  appendOnlyLocΣ;
  ghost_varΣ Z;
  GFunctor (setUR nat)
].

Global Instance subG_seqΣ {Σ} : subG seqΣ Σ → seqG Σ.
Proof. solve_inG. Qed.

Section Seq.
Context `{!noprolG Σ, !atomicG Σ, !seqG Σ}.

Local Notation iProp := (iProp Σ).
Local Notation vProp := (vProp Σ).

Implicit Types
  (γg γq γts γs γsq γsts γv γti : gname)
  (omo omot : omoT)
  (q tsloc : loc) (ty : seq_perm_type)
  (E : history seq_event) (Et : history tseq_event) (Es : history loc_event)
  (P : nat → bool).

Hypothesis (ts : tseq_composition_spec Σ).

Local Open Scope nat_scope.

Definition SeqPerm γg q ty P : vProp :=
  ∃ γts γv γsts γti tsloc,
    meta q nroot (γts,γsts,γv,γti,tsloc) ∗
    match ty with
    | EnqP => TSeqPerm ts γts tsloc (λ n, Nat.even n && P (Z.to_nat (n `quot` 2)%Z)) ∗ ⎡own γti (set_cf (λ n, Nat.even n && P (Z.to_nat (n `quot` 2)%Z)))⎤
    | DeqP => TSeqPerm ts γts tsloc (λ n, Nat.odd n && P (Z.to_nat ((n - 1) `quot` 2)%Z)) ∗ ⎡own γti (set_cf (λ n, Nat.odd n && P (Z.to_nat ((n - 1) `quot` 2)%Z)))⎤
    end.

Definition TSeqRes γv q (_ : nat) : vProp :=
  ∃ (z : Z),
    (q >> 1) ↦ #z ∗ ⎡ghost_var γv (1/2)%Qp z⎤.

Definition field_info γg q tsloc : vProp :=
  ∃ (eV0 : omo_event seq_event) qp,
    OmoEinfo γg 0 eV0 ∗
    @{eV0.(sync)} (q ↦{qp} #tsloc).

Definition last_msg_info (qg : Qp) γg γv γti omo (stlist : list seq_state) (tstlist : list tseq_state) : vProp :=
  ∃ stf tstf,
    MatchValue (Some stf) (last stlist) ∗
    MatchValue (Some tstf) (last tstlist) ∗
    ((⌜ qg = (1/2)%Qp ⌝ ∗ ⎡own γti (set_cf (λ n, n =? tstf.1.1.2))⎤) ∨
    ( ⌜ qg = 1%Qp ∧ stf = [] ∧ Nat.Even tstf.1.1.2 ⌝ ∗ ⎡ghost_var γv (1/2)%Qp 0%Z⎤) ∨
    ( ∃ stfh (eVf : omo_event seq_event),
      ⌜ qg = 1%Qp ⌝ ∗ MatchValue [stfh] stf ∗ OmoEinfo γg stfh.1.1.1.1 eVf ∗ ⎡ghost_var γv (1/2)%Qp stfh.1.1.1.2⎤ ∗
      ⌜ last (omo_write_op omo) = Some stfh.1.1.1.1
      ∧ Nat.Odd tstf.1.1.2 ∧ stfh.1.1.2 = Z.to_nat ((tstf.1.1.2 - 1) `quot` 2)%Z
      ∧ (0 < stfh.1.1.1.2)%Z
      ∧ stfh.1.2 = tstf.1.2 (* Relation between out views *)
      ∧ stfh.1.2 = eVf.(sync)
      ∧ stfh.2 = eVf.(eview) ⌝)).

Definition SeqInv γg γs q E omo stlist : vProp :=
  ∃ γts γsts γv γti tsloc (qg : Qp) Et omot tstlist (eV0 : omo_event seq_event) qp,
    meta q nroot (γts,γsts,γv,γti,tsloc) ∗

    try_update_OmoAuth_to γts Et omot tstlist ∗
    try_update_OmoAuth_to γg E omo stlist ∗

    ask_for qg ∗
    last_msg_info qg γg γv γti omo stlist tstlist ∗
    OmoEinfo γg 0 eV0 ∗ @{eV0.(sync)} (q ↦{qp} #tsloc) ∗
    field_info γg q tsloc ∗

    TSeqInv ts γts γsts tsloc Et omot tstlist (TSeqRes γv q) ∗
    OmoAuth γg γs qg E omo stlist _ ∗

    ⌜ length stlist = length tstlist ⌝.

Definition SeqLocal (N : namespace) γg q M : vProp :=
  ∃ γts γsts γv γti tsloc Mt (eV0 : omo_event seq_event),
    meta q nroot (γts,γsts,γv,γti,tsloc) ∗

    (* local observation of events *)
    OmoEview γg M ∗
    TSeqLocal ts N γts tsloc Mt ∗

    OmoEinfo γg 0 eV0 ∗ ⊒(eV0.(sync)).

Local Instance last_msg_info_timeless qg γg γv γti omo stlist tstlist : Timeless (last_msg_info qg γg γv γti omo stlist tstlist).
Proof. repeat (apply @bi.exist_timeless; intros). destruct x; apply _. Qed.
Local Instance last_msg_info_objective qg γg γv γti omo stlist tstlist : Objective (last_msg_info qg γg γv γti omo stlist tstlist).
Proof. repeat (apply exists_objective; intros). destruct x; apply _. Qed.
Global Instance SeqInv_objective γg γs q E omo stlist : Objective (SeqInv γg γs q E omo stlist) := _.
Global Instance SeqPerm_objective γg q ty P : Objective (SeqPerm γg q ty P).
Proof. repeat (apply exists_objective; intros). destruct ty; apply _. Qed.
Global Instance SeqLocal_persistent N γg q M : Persistent (SeqLocal N γg q M) := _.
Global Instance field_info_timeless γg q tsloc : Timeless (field_info γg q tsloc) := _.
Global Instance field_info_objective γg q tsloc : Objective (field_info γg q tsloc) := _.

Local Tactic Notation "simplify_meta" "with" constr(Hs) :=
  iDestruct (meta_agree with Hs) as %[[[[-> ->]%pair_inj ->]%pair_inj ->]%pair_inj ->]%pair_inj.

Lemma SeqPerm_equiv γg q ty P1 P2 :
  (∀ n, P1 n = P2 n) →
  SeqPerm γg q ty P1 -∗ SeqPerm γg q ty P2.
Proof.
  iIntros "%Equiv (%&%&%&%&%& #HM & Hty)". destruct ty; iDestruct "Hty" as "[Hγts Hγti]".
  - have H : ∀ n, (λ n', Nat.even n' && P1 (Z.to_nat (n' `quot` 2))) n = Nat.even n && P2 (Z.to_nat (n `quot` 2)).
    { intros. simpl. specialize (Equiv (Z.to_nat (n `quot` 2))). rewrite Equiv. done. }
    iDestruct (TSeqPerm_Equiv ts _ _ _ (λ n : nat, Nat.even n && P2 (Z.to_nat (n `quot` 2))) with "Hγts") as "Hγts"; [done|].
    rewrite set_cf_equiv; [|exact H]. repeat iExists _. iFrame "HM Hγts Hγti".
  - have H : ∀ n, (λ n', Nat.odd n' && P1 (Z.to_nat ((n' - 1) `quot` 2))) n = Nat.odd n && P2 (Z.to_nat ((n - 1) `quot` 2)).
    { intros. simpl. specialize (Equiv (Z.to_nat ((n - 1) `quot` 2))). rewrite Equiv /=. done. }
    iDestruct (TSeqPerm_Equiv ts _ _ _ (λ n : nat, Nat.odd n && P2 (Z.to_nat ((n - 1) `quot` 2))) with "Hγts") as "Hγts"; [done|].
    rewrite set_cf_equiv; [|exact H]. repeat iExists _. iFrame "HM Hγts Hγti".
Qed.

Lemma SeqPerm_split γg q ty P1 P2 :
  SeqPerm γg q ty P1 -∗ SeqPerm γg q ty (λ n, P1 n && P2 n) ∗ SeqPerm γg q ty (λ n, P1 n && negb (P2 n)).
Proof.
  iIntros "(%&%&%&%&%& #HM & Hty)".
  destruct ty; iDestruct "Hty" as "[Hγts Hγti]".
  - iDestruct (TSeqPerm_Split ts _ _ _ (λ n, P2 (Z.to_nat (n `quot` 2))) with "Hγts") as "[Hγts1 Hγts2]".
    rewrite (set_cf_split (λ n, Nat.even n && P1 (Z.to_nat (n `quot` 2))) (λ n, P2 (Z.to_nat (n `quot` 2)))).
    iDestruct "Hγti" as "[Hγti1 Hγti2]". iSplitL "Hγts1 Hγti1"; repeat iExists _; iFrame "HM".
    + iSplitL "Hγts1"; [iApply TSeqPerm_Equiv; [|done]|rewrite set_cf_equiv; [done|]]; intros; by rewrite /= andb_assoc.
    + iSplitL "Hγts2"; [iApply TSeqPerm_Equiv; [|done]|rewrite set_cf_equiv; [done|]]; intros; by rewrite /= andb_assoc.
  - iDestruct (TSeqPerm_Split ts _ _ _ (λ n, P2 (Z.to_nat ((n - 1) `quot` 2))) with "Hγts") as "[Hγts1 Hγts2]".
    rewrite (set_cf_split (λ n, Nat.odd n && P1 (Z.to_nat ((n - 1) `quot` 2))) (λ n, P2 (Z.to_nat ((n - 1) `quot` 2)))).
    iDestruct "Hγti" as "[Hγti1 Hγti2]". iSplitL "Hγts1 Hγti1"; repeat iExists _; iFrame "HM".
    + iSplitL "Hγts1"; [iApply TSeqPerm_Equiv; [|done]|rewrite set_cf_equiv; [done|]]; intros; by rewrite /= andb_assoc.
    + iSplitL "Hγts2"; [iApply TSeqPerm_Equiv; [|done]|rewrite set_cf_equiv; [done|]]; intros; by rewrite /= andb_assoc.
Qed.

Lemma SeqPerm_combine γg q ty P1 P2 :
  SeqPerm γg q ty P1 -∗ SeqPerm γg q ty P2 -∗ SeqPerm γg q ty (λ n, P1 n || P2 n).
Proof.
  iIntros "(%&%&%&%&%& #HM & Hty) (%&%&%&%&%& #HM' & Hty')".
  simplify_meta with "HM' HM". destruct ty; iDestruct "Hty" as "[Hγts Hγti]"; iDestruct "Hty'" as "[Hγts' Hγti']".
  - iDestruct (TSeqPerm_Combine with "Hγts Hγts'") as "Hγts". iCombine "Hγti Hγti'" as "Hγti".
    iDestruct (own_valid with "Hγti") as %valid. rewrite set_cf_combine; [|done].
    have H : ∀ n, (λ n', Nat.even n' && P1 (Z.to_nat (n' `quot` 2)) || Nat.even n' && P2 (Z.to_nat (n' `quot` 2))) n
        = Nat.even n && (P1 (Z.to_nat (n `quot` 2)) || P2 (Z.to_nat (n `quot` 2))) by intros; simpl; destruct (Nat.even n).
    iDestruct (TSeqPerm_Equiv ts _ _ _ (λ n, Nat.even n && (P1 (Z.to_nat (n `quot` 2)) || (P2 (Z.to_nat (n `quot` 2))))) with "Hγts") as "Hγts"; [done|].
    rewrite set_cf_equiv; [|exact H]. repeat iExists _. iFrame "HM Hγts Hγti".
  - iDestruct (TSeqPerm_Combine with "Hγts Hγts'") as "Hγts". iCombine "Hγti Hγti'" as "Hγti".
    iDestruct (own_valid with "Hγti") as %valid. rewrite set_cf_combine; [|done].
    have H : ∀ n, (λ n', Nat.odd n' && P1 (Z.to_nat ((n' - 1) `quot` 2)) || Nat.odd n' && P2 (Z.to_nat ((n' - 1) `quot` 2))) n
        = Nat.odd n && (P1 (Z.to_nat ((n - 1) `quot` 2)) || P2 (Z.to_nat ((n - 1) `quot` 2))) by intros; simpl; destruct (Nat.odd n).
    iDestruct (TSeqPerm_Equiv ts _ _ _ (λ n, Nat.odd n && (P1 (Z.to_nat ((n - 1) `quot` 2)) || (P2 (Z.to_nat ((n - 1) `quot` 2))))) with "Hγts") as "Hγts"; [done|].
    rewrite set_cf_equiv; [|exact H]. repeat iExists _. iFrame "HM Hγts Hγti".
Qed.

(* For the [lia] tactic. *)
(* To support Z.div, Z.modulo, Z.quot, and Z.rem: *)
Ltac Zify.zify_post_hook ::= Z.to_euclidean_division_equations.

Lemma SeqPerm_excl γg q ty P1 P2 n :
  P1 n = true → P2 n = true →
  SeqPerm γg q ty P1 -∗ SeqPerm γg q ty P2 -∗ False.
Proof.
  iIntros "%P1n %P2n (%&%&%&%&%& #HM & Hty1) (%&%&%&%&%& #HM' & Hty2)".
  simplify_meta with "HM' HM". destruct ty; iDestruct "Hty1" as "[Hγts1 Hγti1]"; iDestruct "Hty2" as "[Hγts2 Hγti2]".
  - iDestruct (TSeqPerm_Excl _ _ _ _ _ (n * 2) with "Hγts1 Hγts2") as %?; [..|done].
    + simpl. replace (Nat.even (n * 2)) with true; [|symmetry; rewrite Nat.even_spec; apply Nat.Even_mul_r; by rewrite -Nat.even_spec].
      have EQ : n = Z.to_nat ((n * 2)%nat `quot` 2) by lia. by rewrite -EQ P1n.
    + simpl. replace (Nat.even (n * 2)) with true; [|symmetry; rewrite Nat.even_spec; apply Nat.Even_mul_r; by rewrite -Nat.even_spec].
      have EQ : n = Z.to_nat ((n * 2)%nat `quot` 2) by lia. by rewrite -EQ P2n.
  - iDestruct (TSeqPerm_Excl _ _ _ _ _ (n * 2 + 1) with "Hγts1 Hγts2") as %?; [..|done].
    + simpl. replace (Nat.odd (n * 2 + 1)) with true; last first.
      { symmetry. rewrite Nat.odd_spec. apply Nat.Odd_add_r; [|by rewrite -Nat.odd_spec]. apply Nat.Even_mul_r. by rewrite -Nat.even_spec. }
      have EQ : n = Z.to_nat (((n * 2 + 1)%nat - 1) `quot` 2) by lia. by rewrite -EQ P1n.
    + simpl. replace (Nat.odd (n * 2 + 1)) with true; last first.
      { symmetry. rewrite Nat.odd_spec. apply Nat.Odd_add_r; [|by rewrite -Nat.odd_spec]. apply Nat.Even_mul_r. by rewrite -Nat.even_spec. }
      have EQ : n = Z.to_nat (((n * 2 + 1)%nat - 1) `quot` 2) by lia. by rewrite -EQ P2n.
Qed.

#[local] Typeclasses Opaque last_msg_info.

Lemma SeqInv_Linearizable_instance :
  ∀ γg γs q E omo stlist, SeqInv γg γs q E omo stlist ⊢ ⌜ Linearizability_omo E omo stlist ⌝.
Proof. iSteps as "???????? M●". by iDestruct (OmoAuth_Linearizable with "M●") as %?. Qed.

Lemma SeqInv_OmoAuth_acc_instance :
  ∀ γg γs q E omo stlist,
    SeqInv γg γs q E omo stlist ⊢ ∃ qp, OmoAuth γg γs qp E omo stlist _ ∗ (OmoAuth γg γs qp E omo stlist _ -∗ SeqInv γg γs q E omo stlist).
Proof. iSteps as "???????? M●". rewrite try_update_OmoAuth_to_eq. oSteps. iExists x10. oSteps. Qed.

#[local] Typeclasses Transparent last_msg_info.

Lemma SeqLocal_OmoEview_instance :
  ∀ N γg q M, SeqLocal N γg q M ⊢ OmoEview γg M.
Proof. oSteps. Qed.

Lemma field_info_dup γg q tsloc (eV0 : omo_event seq_event) :
  field_info γg q tsloc -∗ OmoEinfo γg 0 eV0 -∗ ∃ qp, @{eV0.(sync)} q ↦{qp} #tsloc ∗ field_info γg q tsloc.
Proof. oSteps. Qed.

Lemma eqb_same (n : nat) :
  n =? n = true.
Proof. by rewrite Nat.eqb_eq. Qed.

Lemma last_lookup' `{A : Type} (l : list A) :
  last l = l !! (length l - 1).
Proof. rewrite last_lookup. replace (Init.Nat.pred (length l)) with (length l - 1) by lia. done. Qed.

Notation newTS := (spec_turnSequencer_composition.newTS ts).
Notation waitForTurn := (spec_turnSequencer_composition.waitForTurn ts).
Notation completeTurn := (spec_turnSequencer_composition.completeTurn ts).

#[global] Instance hint_TSeqInv γts γsts tsloc Et omot tstlist γv q :
  MergableConsume (▷ TSeqInv ts γts γsts tsloc Et omot tstlist (TSeqRes γv q)) true (λ p Pin Pout,
    TCAnd (TCEq Pin (ε₀)) $
      TCEq Pout (▷ OmoAuth γts γsts 1 Et omot tstlist _ ∗ ▷ (OmoAuth γts γsts 1 Et omot tstlist _ -∗ TSeqInv ts γts γsts tsloc Et omot tstlist (TSeqRes γv q))))%I.
Proof.
  intros p Pin Pout [-> ->]. rewrite bi.intuitionistically_if_elim. iIntros "[A _]". iDestruct (TSeqInv_OmoAuth_acc with "A") as "[A B]". iFrame "∗".
Qed.

#[global] Instance my_hint γg q tsloc (eV0 : omo_event seq_event) :
  HINT field_info γg q tsloc ✱ [-; OmoEinfo γg 0 eV0]
  ⊫ [id]
  ; ∃ qp, @{eV0.(sync)} q ↦{qp} #tsloc ✱ [ field_info γg q tsloc ].
Proof. iStep as "e0✓eV0 [q↦ q↦']". iSplitL "q↦'"; oSteps. Qed.

#[global] Instance wait_dspec N γg γs l V M n P R :
  SPEC ⟨ ⊤ , ↑N , ↑histN⟩ Et omot tstlist, <<
    ⊒V ∗ TSeqLocal ts N γg l M ∗ TSeqPerm ts γg l P ∗
    ⌜ N ## histN ∧ P n = true ⌝
  ¦
    ▷ TSeqInv ts γg γs l Et omot tstlist R > >
      waitForTurn [ #l; #n ]
  << RET #☠;
      R n ∗ TSeqPerm ts γg l (λ m, P m && negb (m =? n)) ∗ TSeqComplete ts γg l n
      ¦
      (
      ∃ V' M' omot' tstlist' tstf,
      let eVwait := mkOmoEvent (Take n) V' M' in
      let Et' := Et ++ [eVwait] in
      let opId := length Et in
      ▷ TSeqInv ts γg γs l Et' omot' tstlist' R ∗ ⊒V' ∗ @{V'} TSeqLocal ts N γg l M' ∗
      ⌜ V ⊑ V' ∧ M ⊆ M' ∧ omot' = omo_insert_r omot (length omot - 1) opId ∧ tstlist' = tstlist
      ∧ last tstlist = Some tstf ∧ tstf.1.1.2 = n ∧ omo.step opId eVwait tstf tstf ⌝)
    > >.
Proof using All.
  iSteps as "⊒V ⊒M Perm AU". iDestruct (TSeqPerm_Split _ _ _ _ (λ m, m =? n) with "Perm") as "[Perm PermReturn]".
  awp_apply (wait_spec ts _ H l _ _ γs M V n R with "⊒V ⊒M [Perm]").
  { iApply TSeqPerm_Equiv; [|done]. intros m. simpl. destruct (m =? n) eqn:Heq; [by rewrite Nat.eqb_eq in Heq; rewrite Heq H0|by rewrite andb_comm]. }
  iApply (aacc_aupd with "AU"); [done|]. iSteps as (E omo stlist) "M●". iAaccIntro with "M●"; [oSteps|]. iStep 3 as "⊒V ⊒M M●".
  iDestruct (TSeqInv_OmoAuth_acc with "M●") as "[>M● Close]". iDestruct (OmoAuth_wf with "M●") as %[OMO_GOOD _].
  iDestruct (OmoAuth_omo_nonempty with "M●") as %Nomo. have NZomo : length omo ≠ 0 by destruct omo.
  apply omo_stlist_length in OMO_GOOD as EQlenST. rewrite omo_rewrite_hints in EQlenST.
  have [stf Hstf] : is_Some (last stlist) by rewrite last_is_Some; unfold not; intros; rewrite H3 in EQlenST.
  have [es Hes] : is_Some (omo_read_op omo !! (length omo - 1)) by rewrite lookup_lt_is_Some -omo_read_op_length; lia.
  eapply (omo_read_op_step _ _ _ (length omo - 1) (length es) (length E)) in OMO_GOOD as STEP; last first.
  { by rewrite last_lookup' -EQlenST in Hstf. } { by rewrite lookup_app_1_eq. }
  { by rewrite lookup_omo_ro_event omo_insert_r_read_op list_lookup_alter Hes /= lookup_app_1_eq. }
  oSteps. iRight. oSteps. inversion STEP; try done. inversion TAKE. done.
Qed.

#[global] Instance complete_dspec N γg γs l V M n R :
  SPEC ⟨ ⊤ , ↑N , ↑histN⟩ Et omot tstlist, <<
    ⊒V ∗ TSeqLocal ts N γg l M ∗ R (n + 1)%nat ∗ TSeqComplete ts γg l n ∗
    ⌜ N ## histN ⌝
  ¦
    ▷ TSeqInv ts γg γs l Et omot tstlist R  > >
      completeTurn [ #l; #n ]
  << RET #☠;
      emp
      ¦
      (
      ∃ V' M' omot' tstlist',
      let Et' := Et ++ [mkOmoEvent (Complete n) V' M'] in
      ▷ TSeqInv ts γg γs l Et' omot' tstlist' R ∗ OmoTokenW γg (length Et) ∗ ⊒V' ∗ @{V'} TSeqLocal ts N γg l M' ∗
      ⌜ V ⊑ V' ∧ M ⊆ M' ∧ omot' = omo_append_w omot (length Et) [] ∧ tstlist' = tstlist ++ [(length Et, (n + 1)%nat, V', M')] ⌝)
    > >.
Proof using All.
  iSteps as "⊒V ⊒M Res Complete AU". awp_apply (complete_spec ts _ H l _ _ γs M V n R with "⊒V ⊒M Res Complete").
  iApply (aacc_aupd with "AU"); [done|]. iSteps as "M●". iAaccIntro with "M●"; oSteps. iRight. oSteps.
Qed.

#[global] Instance read_NonAtomic (l: loc) (E : coPset):
  SolveSepSideCondition (↑histN ⊆ E) →
  SPEC [ε₀] ⟨E⟩ (q : Qp) v V, {{  ▷ @{V} l ↦{q} v ∗ ⊒V }}
    !#l
  {{ RET v; l ↦{q} v }} | 15.
Proof. move => HE. iSteps. Qed.

Lemma new_seq_spec :
  new_seq_spec' (newSEQ newTS) SeqLocal SeqInv SeqPerm.
Proof using All.
  iSteps as (N ? V ? q) "⊒V ?? q↦ Hm ? q↦1". rewrite omo_rewrite_hints. iMod (ghost_var_alloc 0%Z) as (γv) "Hγv". iDestruct "Hγv" as "[Hγv Hγv']".
  wp_apply (new_tseq_spec ts N _ V (TSeqRes γv q) with "[$⊒V q↦1 Hγv']"); [oSteps|]. iStep 14 as "????? q↦".
  iDestruct (view_at_intro_incl with "q↦ [$]") as "H". iDecompose "H".

  set eVinit := mkOmoEvent Init x6 {[0%nat]}.

  iMod (@OmoAuth_alloc _ _ _ _ _ eVinit [] _ _ seq_interpretable with "[$]") as (γg γs) "[M● H]"; [by apply seq_step_Init|done|iDecompose "H"].
  iDestruct (OmoHbToken_finish with "M●") as "M●".

  iMod (own_alloc (set_cf (λ (n : nat), true))) as (γti) "Hγti"; [done|]. iMod (meta_set _ _ (x,x1,γv,γti,x3) nroot with "Hm") as "#HM"; [done|].
  rewrite /SeqInv !try_update_OmoAuth_to_eq. iExists _,_,_,x6. oSteps. iExists 1%Qp. oSteps. iExists (0, 0, x5, x4).
  instantiate (1 := [(0, 0, x5, x4)]). oSteps. iLeft. oSteps; [by rewrite -Nat.even_spec|].
  iDestruct (TSeqPerm_Split _ _ _ _ Nat.even with "[$]") as "[H1 H2]". rewrite (set_cf_split _ Nat.even). iDestruct "Hγti" as "[H3 H4]".
  iSplitL "H1"; last iSplitL "H3"; [..|oSteps; iSplitL "H2"; last iSplitL "H4"; [..|oSteps; solve_lat]]; iModIntro;
  try (iApply TSeqPerm_Equiv; [|done]); try (rewrite set_cf_equiv; [done|]); intros; simpl; try (rewrite andb_comm); try (rewrite Nat.negb_even); done.
Qed.

#[local] Typeclasses Opaque last_msg_info field_info.

#[global] Instance enqueueWithTicket_dspec N γg γs q V M (v : Z) n :
  SPEC ⟨ ⊤ , ↑N , ↑histN⟩ E omo stlist, <<
    ⊒V ∗ SeqLocal N γg q M ∗ SeqPerm γg q EnqP (λ m, m =? n) ∗
    ⌜ N ## histN ∧ (0 < v)%Z ⌝
  ¦
    ▷ SeqInv γg γs q E omo stlist > >
      (enqueueWithTicket waitForTurn completeTurn) [ #q; #n; #v ]
  << RET #☠;
      emp
      ¦
      (
      ∃ V', ask_for V' ∗ (* ask for dv_out *)
      ∃ M' omo' stlist',
      let E' := E ++ [mkOmoEvent (Enq v n) V' M'] in
      let opId := length E in
      let st := [(opId, v, n, V', M')] in
      ▷ SeqInv γg γs q E' omo' stlist' ∗ OmoTokenW γg opId ∗
      ⊒V' ∗ @{V'} SeqLocal N γg q M' ∗ ⌜ V ⊑ V' ∧ M ⊆ M' ∧ omo' = omo_append_w omo opId [] ∧ stlist' = stlist ++ [st] ⌝)
    > >.
Proof using All.
  oSteps. iRight. oSteps. iExists x19. oSteps.
  replace (Z.of_nat n * 2)%Z with (Z.of_nat (n * 2)) by lia. oSteps.
  { rewrite (_: Z.to_nat ((n * 2)%nat `quot` 2) = n); [|lia]. rewrite eqb_same.
    rewrite (_: Nat.even (n * 2) = true); [done|]. rewrite Nat.even_spec. apply Nat.Even_mul_r. by rewrite -Nat.even_spec. }
  iRename select (atomic_update _ _ _ _ _)%I into "AU". iMod "AU" as (???) "[SeqInv HAUcl]". iDecompose "SeqInv".
  iDestruct (atomic.diaframe_close_left with "HAUcl") as "HAU". oSteps; [iExists x23; oSteps|].

  iRename select (last_msg_info _ _ _ _ _ _ _)%I into "H1". iRename select (⎡own _ _⎤)%I into "H2".
  rewrite (set_cf_split _ (λ m, m =? n * 2)). iDestruct "H2" as "[H2 H3]". rewrite (set_cf_equiv _ (λ m, m =? n * 2)); last first.
  { intros. destruct (a =? n * 2) eqn:Ha; [|by rewrite andb_comm /=]. rewrite Nat.eqb_eq in Ha. subst a.
    rewrite (_: Nat.even (n * 2) = true); [|by rewrite Nat.even_spec; apply Nat.Even_mul_r; rewrite -Nat.even_spec].
    rewrite (_: Z.to_nat ((n * 2)%nat `quot` 2) = n); [|lia]. rewrite eqb_same. done. }
  #[local] Typeclasses Transparent last_msg_info. iDecompose "H1"; swap 2 3.
  { iRename select (⎡own _ _⎤)%I into "H1". iCombine "H1 H2" as "H". rewrite H10.
    iDestruct (own_valid with "H") as %VALID%(set_cf_excl _ _ (n * 2)). rewrite /= eqb_same in VALID. done. }
  { rewrite H10 in H14. apply Nat.Odd_mul_inv_r in H14. rewrite -Nat.odd_spec in H14. done. }

  iExists (1/2)%Qp. iApply (bi.wand_elim_r do_intro_view_forall). oSteps. iLeft.
  rewrite H10. oSteps. instantiate (1 := TSeqRes x3 q). oSteps.
  iDestruct (ghost_var_agree _ x17 _ 0%Z with "[$] [$]") as %->.
  iMod (ghost_var_update_halves v with "[$] [$]") as "[? ?]". oSteps.
  iRename select (atomic_update _ _ _ _ _)%I into "AU". iMod "AU" as (???) "[SeqInv HAUcl]". iDecompose "SeqInv".
  all: iDestruct (OmoAuth_frac_valid (eventT := seq_event) γg with "[$]") as %Hf;
   try (rewrite -{3}Qp.half_half -Qp.add_le_mono_r -{1}Qp.half_half in Hf; by apply Qp.not_add_le_l in Hf).

  iStepSafest. iRename select (_ ∧ _)%I into "HAUcl". iStepSafest.
  { iDestruct (atomic.diaframe_close_left with "HAUcl") as "?"; oSteps. iExists (1/2)%Qp. iSteps. }
  iDestruct (atomic.diaframe_close_right with "HAUcl") as "HAU". oSteps.
  iExists x17. oSteps. rewrite -H12 in H15. inversion H15. subst. iExists _. iSplitR.
  { iPureIntro. apply seq_step_Enq; try done. simpl. instantiate (1 := M). set_solver-. }
  oSteps. iExists 1%Qp. oSteps. iRight. oSteps; iPureIntro; [|by rewrite !app_length /=; lia].
  apply Nat.Odd_add_r; [|by rewrite -Nat.odd_spec]. apply Nat.Even_mul_r. by rewrite -Nat.even_spec.
Qed.

#[local] Typeclasses Opaque last_msg_info.

#[global] Instance dequeueWithTicket_dspec N γg γs q V M n :
  SPEC ⟨ ⊤ , ↑N , ↑histN⟩ E omo stlist, <<
    ⊒V ∗ SeqLocal N γg q M ∗ SeqPerm γg q DeqP (λ m, m =? n) ∗
    ⌜ N ## histN ⌝
  ¦
    ▷ SeqInv γg γs q E omo stlist > >
      (dequeueWithTicket waitForTurn completeTurn) [ #q; #n ]
  << (v : Z), RET #v;
      emp
      ¦
      (
      ∃ V', ask_for V' ∗ (* ask for dv_out *)
      ∃ M' omo' stlist',
      let E' := E ++ [mkOmoEvent (Deq v n) V' M'] in
      let opId := length E in
      ▷ SeqInv γg γs q E' omo' stlist' ∗ OmoTokenW γg opId ∗
      ⊒V' ∗ @{V'} SeqLocal N γg q M' ∗ ⌜ V ⊑ V' ∧ M ⊆ M' ∧ omo' = omo_append_w omo opId [] ∧ stlist' = stlist ++ [[]] ∧ (0 < v)%Z ⌝)
    > >.
Proof using All.
  oSteps. iRight. oSteps. iExists x19. oSteps.
  have Hodd : Nat.odd (n * 2 + 1) = true.
  { rewrite Nat.odd_spec. apply Nat.Odd_add_r; [by apply Nat.Even_mul_r; rewrite -Nat.even_spec|by rewrite -Nat.odd_spec]. }
  replace (Z.of_nat n * 2 + 1)%Z with (Z.of_nat (n * 2 + 1)) by lia. oSteps.
  { rewrite (_: Z.to_nat (((n * 2 + 1)%nat - 1)%Z `quot` 2)%Z = n); [|lia]. by rewrite eqb_same Hodd. }
  iRename select (atomic_update _ _ _ _ _)%I into "AU". iMod "AU" as (???) "[SeqInv HAUcl]". iDecompose "SeqInv".
  iDestruct (atomic.diaframe_close_left with "HAUcl") as "HAU". oSteps; [iExists x23; oSteps|].

  iRename select (last_msg_info _ _ _ _ _ _ _)%I into "H1". iRename select (⎡own _ _⎤)%I into "H2".
  rewrite (set_cf_split _ (λ m, m =? n * 2 + 1)). iDestruct "H2" as "[H2 H3]". rewrite (set_cf_equiv _ (λ m, m =? n * 2 + 1)); last first.
  { intros. destruct (a =? n * 2 + 1) eqn:Ha; [|by rewrite andb_comm /=]. rewrite Nat.eqb_eq in Ha. subst a. rewrite Hodd.
    rewrite (_: Z.to_nat (((n * 2 + 1)%nat - 1) `quot` 2) = n); [|lia]. rewrite eqb_same. done. }
  #[local] Typeclasses Transparent last_msg_info. iDecompose "H1".
  { iRename select (⎡own _ _⎤)%I into "H1". iCombine "H1 H2" as "H". rewrite H9.
    iDestruct (own_valid with "H") as %VALID%(set_cf_excl _ _ (n * 2 + 1)). rewrite /= eqb_same in VALID. done. }
  { rewrite H9 in H12. have H13 : Nat.Even (n * 2) by apply Nat.Even_mul_r; rewrite -Nat.even_spec.
    eapply Nat.Even_add_Even_inv_r in H13; [|done]. rewrite -Nat.even_spec in H13. done. }

  iExists (1/2)%Qp. iApply (bi.wand_elim_r do_intro_view_forall). oSteps. rewrite H9. iSteps. rewrite -[Z.to_nat 1]/(1%nat).
  iRename select ((q >> 1) ↦ _)%I into "H". iDestruct (view_at_intro with "H") as "H". iDecompose "H". iStep 2 as "A B".
  iDestruct (view_at_elim with "[] A") as "A"; [iSteps|]. iCombine "A B" as "?". oSteps. instantiate (1 := TSeqRes x3 q). oSteps.

  iRename select (⎡ghost_var _ _ _.1.1.1.2⎤)%I into "H1". iRename select (⎡ghost_var _ _ _⎤)%I into "H2".
  iDestruct (ghost_var_agree with "H1 H2") as %<-. iCombine "H1 H2" as "H1". iMod (ghost_var_update 0%Z with "H1") as "[H1 H2]". oSteps.
  iRename select (atomic_update _ _ _ _ _)%I into "AU". iMod "AU" as (???) "[SeqInv HAUcl]". iDecompose "SeqInv";
  iDestruct (OmoAuth_frac_valid (eventT := seq_event) γg with "[$]") as %Hf;
  try (rewrite -{3}Qp.half_half -Qp.add_le_mono_r -{1}Qp.half_half in Hf; by apply Qp.not_add_le_l in Hf).
  iRename select (_ ∧ _)%I into "HAUcl". do 2 iStepSafest.
  { iDestruct (atomic.diaframe_close_left with "HAUcl") as "?". oSteps. iExists (1/2)%Qp. iSteps. }

  iDestruct (atomic.diaframe_close_right_quant with "HAUcl") as "?". oSteps. iExists x16. oSteps. iExists x17.1.1.1.2,_.
  inversion H10; try done. subst x18. simpl in *. subst. iSplitR.
  { iPureIntro. rewrite -H11 in H20. inversion H20. subst x33. destruct x17 as [[[[? ?] ?] ?] ?]. apply seq_step_Deq; try done; simpl in *; [|solve_lat|].
    - replace (Z.to_nat (((n * 2 + 1)%nat - 1) `quot` 2)%Z) with n in H14 by lia. subst n0. done.
    - instantiate (1 := {[x17.1.1.1.1]} ∪ x17.2 ∪ M). set_solver-. }

  iDestruct (OmoEview_get_from_Einfo (eventT := seq_event) γg x17.1.1.1.1 with "[$]") as "H'". iDecompose "H'".  rewrite -H18.
  have ? : x28.(sync) ⊑ x16 by rewrite -H17; solve_lat. oSteps. iExists 1%Qp. oSteps. iLeft. oSteps; iPureIntro; [|by rewrite !app_length /=; lia].
  replace (n * 2 + 1 + 1) with ((n + 1) * 2) by lia. apply Nat.Even_mul_r. by rewrite -Nat.even_spec.
Qed.

#[local] Typeclasses Opaque SeqLocal SeqInv SeqPerm.

Lemma enqueueWithTicket_spec :
  enqueueWithTicket_spec' (enqueueWithTicket waitForTurn completeTurn) SeqLocal SeqInv SeqPerm.
Proof using All. oSteps; [iRight; oSteps|]. iLeft. unseal_diaframe. oSteps. Qed.

Lemma dequeueWithTicket_spec :
  dequeueWithTicket_spec' (dequeueWithTicket waitForTurn completeTurn) SeqLocal SeqInv SeqPerm.
Proof using All. oSteps; [iRight; oSteps|]. iLeft. unseal_diaframe. oSteps. Qed.
End Seq.

Definition seq_composition_impl `{!noprolG Σ, !atomicG Σ, !seqG Σ} (ts : tseq_composition_spec Σ)
  : seq_composition_spec Σ := {|
    spec_singleElementQueue_composition.SeqInv_Linearizable := SeqInv_Linearizable_instance ts;
    spec_singleElementQueue_composition.SeqInv_OmoAuth_acc := SeqInv_OmoAuth_acc_instance ts;
    spec_singleElementQueue_composition.SeqLocal_OmoEview := SeqLocal_OmoEview_instance ts;
    spec_singleElementQueue_composition.SeqPerm_Equiv := SeqPerm_equiv ts;
    spec_singleElementQueue_composition.SeqPerm_Split := SeqPerm_split ts;
    spec_singleElementQueue_composition.SeqPerm_Combine := SeqPerm_combine ts;
    spec_singleElementQueue_composition.SeqPerm_Excl := SeqPerm_excl ts;

    spec_singleElementQueue_composition.new_seq_spec := new_seq_spec ts;
    spec_singleElementQueue_composition.enqueueWithTicket_spec := enqueueWithTicket_spec ts;
    spec_singleElementQueue_composition.dequeueWithTicket_spec := dequeueWithTicket_spec ts;
  |}.
