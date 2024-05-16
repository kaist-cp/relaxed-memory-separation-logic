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
From gpfsl.examples.omo Require Import omo omo_preds append_only_loc.

Require Import iris.prelude.options.

Class seqG Σ := SeqG {
  seq_omoGeneralG :> omoGeneralG Σ;
  seq_omoG :> omoSpecificG Σ seq_event seq_state;
  seq_tseqG :> omoSpecificG Σ tseq_event tseq_state;
  seq_aolocG :> appendOnlyLocG Σ;
  seq_data_gvarG :> ghost_varG Σ Z;
  seq_ticketG :> inG Σ (setUR nat);
}.

Definition seqΣ : gFunctors := #[omoGeneralΣ; omoSpecificΣ seq_event seq_state; omoSpecificΣ tseq_event tseq_state; appendOnlyLocΣ; ghost_varΣ Z; GFunctor (setUR nat)].

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
    ⌜ length stlist = length tstlist ∧
      last stlist = Some stf ∧
      last tstlist = Some tstf ⌝ ∗
    ((⌜ qg = (1/2)%Qp ⌝ ∗ ⎡own γti (set_cf (λ n, n =? tstf.1.1.2))⎤) ∨
    ( ⌜ qg = 1%Qp ⌝ ∗
      match stf with
      | [] => ⎡ghost_var γv (1/2)%Qp 0%Z⎤ ∗ ⌜ Nat.Even tstf.1.1.2 ⌝
      | stfh :: stft =>
        ∃ (eVf : omo_event seq_event),
          OmoEinfo γg stfh.1.1.1.1 eVf ∗
          ⎡ghost_var γv (1/2)%Qp stfh.1.1.1.2⎤ ∗
          ⌜ last (omo_write_op omo) = Some stfh.1.1.1.1 ∧ stft = []
          ∧ Nat.Odd tstf.1.1.2 ∧ stfh.1.1.2 = Z.to_nat ((tstf.1.1.2 - 1) `quot` 2)%Z
          ∧ (0 < stfh.1.1.1.2)%Z
          ∧ stfh.1.2 = tstf.1.2 (* Relation between out views *)
          ∧ stfh.1.2 = eVf.(sync)
          ∧ stfh.2 = eVf.(eview) ⌝
      end)).

Definition SeqInv γg γs q E omo stlist : vProp :=
  ∃ γts γsts γv γti tsloc (qg : Qp) Et omot tstlist,
    meta q nroot (γts,γsts,γv,γti,tsloc) ∗

    OmoAuth γg γs qg E omo stlist _ ∗
    TSeqInv ts γts γsts tsloc Et omot tstlist (TSeqRes γv q) ∗

    field_info γg q tsloc ∗
    last_msg_info qg γg γv γti omo stlist tstlist.

Definition SeqLocal (N : namespace) γg q M : vProp :=
  ∃ γts γsts γv γti tsloc Mt (eV0 : omo_event seq_event),
    meta q nroot (γts,γsts,γv,γti,tsloc) ∗

    (* local observation of events *)
    OmoEview γg M ∗
    TSeqLocal ts N γts tsloc Mt ∗

    OmoEinfo γg 0 eV0 ∗ ⊒(eV0.(sync)).

Local Instance last_msg_info_timeless qg γg γv γti omo stlist tstlist : Timeless (last_msg_info qg γg γv γti omo stlist tstlist).
Proof.
  repeat (apply @bi.exist_timeless; intros).
  destruct x; apply _.
Qed.
Local Instance last_msg_info_objective qg γg γv γti omo stlist tstlist : Objective (last_msg_info qg γg γv γti omo stlist tstlist).
Proof.
  repeat (apply exists_objective; intros).
  destruct x; apply _.
Qed.
Global Instance SeqInv_objective γg γs q E omo stlist : Objective (SeqInv γg γs q E omo stlist) := _.
Global Instance SeqPerm_objective γg q ty P : Objective (SeqPerm γg q ty P).
Proof. repeat (apply exists_objective; intros). destruct ty; apply _. Qed.
Global Instance SeqLocal_persistent N γg q M : Persistent (SeqLocal N γg q M) := _.

Local Tactic Notation "simplify_meta" "with" constr(Hs) :=
  iDestruct (meta_agree with Hs) as %[[[[-> ->]%pair_inj ->]%pair_inj ->]%pair_inj ->]%pair_inj.

Lemma SeqPerm_equiv γg q ty P1 P2 :
  (∀ n, P1 n = P2 n) →
  SeqPerm γg q ty P1 -∗ SeqPerm γg q ty P2.
Proof.
  iIntros "%Equiv (%&%&%&%&%& #HM & Hty)".
  destruct ty; iDestruct "Hty" as "[Hγts Hγti]".
  - have H : ∀ n, (λ n', Nat.even n' && P1 (Z.to_nat (n' `quot` 2))) n = Nat.even n && P2 (Z.to_nat (n `quot` 2)).
    { intros. simpl. specialize (Equiv (Z.to_nat (n `quot` 2))). rewrite Equiv. done. }
    iDestruct (TSeqPerm_Equiv ts _ _ _ (λ n : nat, Nat.even n && P2 (Z.to_nat (n `quot` 2))) with "Hγts") as "Hγts"; [done|].
    rewrite set_cf_equiv; [|exact H].
    repeat iExists _. iFrame "HM Hγts Hγti".
  - have H : ∀ n, (λ n', Nat.odd n' && P1 (Z.to_nat ((n' - 1) `quot` 2))) n = Nat.odd n && P2 (Z.to_nat ((n - 1) `quot` 2)).
    { intros. simpl. specialize (Equiv (Z.to_nat ((n - 1) `quot` 2))). rewrite Equiv /=. done. }
    iDestruct (TSeqPerm_Equiv ts _ _ _ (λ n : nat, Nat.odd n && P2 (Z.to_nat ((n - 1) `quot` 2))) with "Hγts") as "Hγts"; [done|].
    rewrite set_cf_equiv; [|exact H].
    repeat iExists _. iFrame "HM Hγts Hγti".
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
  - iDestruct (TSeqPerm_Combine with "Hγts Hγts'") as "Hγts".
    iCombine "Hγti Hγti'" as "Hγti".
    iDestruct (own_valid with "Hγti") as %valid.
    rewrite set_cf_combine; [|done].
    have H : ∀ n, (λ n', Nat.even n' && P1 (Z.to_nat (n' `quot` 2)) || Nat.even n' && P2 (Z.to_nat (n' `quot` 2))) n
        = Nat.even n && (P1 (Z.to_nat (n `quot` 2)) || P2 (Z.to_nat (n `quot` 2))).
    { intros. simpl. by destruct (Nat.even n). }
    iDestruct (TSeqPerm_Equiv ts _ _ _ (λ n, Nat.even n && (P1 (Z.to_nat (n `quot` 2)) || (P2 (Z.to_nat (n `quot` 2))))) with "Hγts") as "Hγts"; [done|].
    rewrite set_cf_equiv; [|exact H].
    repeat iExists _. iFrame "HM Hγts Hγti".
  - iDestruct (TSeqPerm_Combine with "Hγts Hγts'") as "Hγts".
    iCombine "Hγti Hγti'" as "Hγti".
    iDestruct (own_valid with "Hγti") as %valid.
    rewrite set_cf_combine; [|done].
    have H : ∀ n, (λ n', Nat.odd n' && P1 (Z.to_nat ((n' - 1) `quot` 2)) || Nat.odd n' && P2 (Z.to_nat ((n' - 1) `quot` 2))) n
        = Nat.odd n && (P1 (Z.to_nat ((n - 1) `quot` 2)) || P2 (Z.to_nat ((n - 1) `quot` 2))).
    { intros. simpl. by destruct (Nat.odd n). }
    iDestruct (TSeqPerm_Equiv ts _ _ _ (λ n, Nat.odd n && (P1 (Z.to_nat ((n - 1) `quot` 2)) || (P2 (Z.to_nat ((n - 1) `quot` 2))))) with "Hγts")
      as "Hγts"; [done|].
    rewrite set_cf_equiv; [|exact H].
    repeat iExists _. iFrame "HM Hγts Hγti".
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
    + simpl. replace (Nat.even (n * 2)) with true; last first.
      { symmetry. rewrite Nat.even_spec. apply Nat.Even_mul_r. by rewrite -Nat.even_spec. }
      have EQ : n = Z.to_nat ((n * 2)%nat `quot` 2) by lia.
      by rewrite -EQ P1n.
    + simpl. replace (Nat.even (n * 2)) with true; last first.
      { symmetry. rewrite Nat.even_spec. apply Nat.Even_mul_r. by rewrite -Nat.even_spec. }
      have EQ : n = Z.to_nat ((n * 2)%nat `quot` 2) by lia.
      by rewrite -EQ P2n.
  - iDestruct (TSeqPerm_Excl _ _ _ _ _ (n * 2 + 1) with "Hγts1 Hγts2") as %?; [..|done].
    + simpl. replace (Nat.odd (n * 2 + 1)) with true; last first.
      { symmetry. rewrite Nat.odd_spec. apply Nat.Odd_add_r; [|by rewrite -Nat.odd_spec].
        apply Nat.Even_mul_r. by rewrite -Nat.even_spec. }
      have EQ : n = Z.to_nat (((n * 2 + 1)%nat - 1) `quot` 2) by lia.
      by rewrite -EQ P1n.
    + simpl. replace (Nat.odd (n * 2 + 1)) with true; last first.
      { symmetry. rewrite Nat.odd_spec. apply Nat.Odd_add_r; [|by rewrite -Nat.odd_spec].
        apply Nat.Even_mul_r. by rewrite -Nat.even_spec. }
      have EQ : n = Z.to_nat (((n * 2 + 1)%nat - 1) `quot` 2) by lia.
      by rewrite -EQ P2n.
Qed.

Lemma SeqInv_Linearizable_instance :
  ∀ γg γs q E omo stlist, SeqInv γg γs q E omo stlist ⊢ ⌜ Linearizability_omo E omo stlist ⌝.
Proof.
  intros. iDestruct 1 as (?????????) "(_ & M● & _)".
  by iDestruct (OmoAuth_Linearizable with "M●") as %H.
Qed.

Lemma SeqInv_OmoAuth_acc_instance :
  ∀ γg γs q E omo stlist,
    SeqInv γg γs q E omo stlist ⊢ ∃ qp, OmoAuth γg γs qp E omo stlist _ ∗ (OmoAuth γg γs qp E omo stlist _ -∗ SeqInv γg γs q E omo stlist).
Proof.
  intros. iDestruct 1 as (?????????) "(H1 & M● & H2)".
  iExists qg. iFrame "M●". iIntros "M●". repeat iExists _. iFrame.
Qed.

Lemma SeqLocal_OmoEview_instance :
  ∀ N γg q M, SeqLocal N γg q M ⊢ OmoEview γg M.
Proof.
  intros. iDestruct 1 as (???????) "(_ & M◯ & _)". iFrame.
Qed.

Lemma field_info_lookup γg q tsloc (eV0 : omo_event seq_event) :
  field_info γg q tsloc -∗ OmoEinfo γg 0 eV0 -∗ ⊒(eV0.(sync)) -∗ ∃ qp, q ↦{qp} #tsloc ∗ field_info γg q tsloc.
Proof.
  iIntros "Field #e0✓eV0 #⊒SYNC". iDestruct "Field" as (??) "[#e0✓eV0' [q↦ q↦']]".
  iDestruct (OmoEinfo_agree with "e0✓eV0 e0✓eV0'") as %<-. iDestruct (view_at_elim with "⊒SYNC q↦") as "q↦".
  iExists _. iFrame "q↦". repeat iExists _. iFrame "e0✓eV0' q↦'".
Qed.

Notation newTS := (spec_turnSequencer_composition.newTS ts).
Notation waitForTurn := (spec_turnSequencer_composition.waitForTurn ts).
Notation completeTurn := (spec_turnSequencer_composition.completeTurn ts).

Lemma new_seq_spec :
  new_seq_spec' (newSEQ newTS) SeqLocal SeqInv SeqPerm.
Proof.
  iIntros (N tid V0 Φ) "#⊒V0 Post".
  wp_lam. wp_apply wp_new; [done..|].
  iIntros (q) "([H†|%] & q↦ & Hmq & _)"; [|done].
  rewrite own_loc_na_vec_cons own_loc_na_vec_singleton.
  iDestruct "q↦" as "[q↦ q↦1]". wp_let. wp_op. rewrite -[Z.to_nat 1]/(1%nat). wp_write. wp_op. rewrite shift_0.

  iMod (ghost_var_alloc 0%Z) as (γv) "Hγv". iDestruct "Hγv" as "[Hγv Hγv']".
  wp_apply (new_tseq_spec ts N _ _ (TSeqRes γv q) with "[$⊒V0 q↦1 Hγv']"). { iExists 0%Z. iFrame. }
  iIntros (γts γsts tsloc Mts V1) "(#⊒V1 & #TSeq◯ & TSeq● & WCOMMIT & TSeqPerm & %LeV0V1)".
  wp_apply wp_fupd. wp_write. iDestruct (view_at_intro_incl with "q↦ ⊒V1") as (V2) "(#⊒V2 & %LeV1V2 & q↦@V2)".

  have LeV0V2 : V0 ⊑ V2 by solve_lat.
  set M : eView := {[0%nat]}.
  set eVinit := mkOmoEvent Init V2 M.
  set initst : seq_state := [].

  iMod (@OmoAuth_alloc _ _ _ _ _ eVinit initst _ _ seq_interpretable with "WCOMMIT") as (γg γs)
    "(M● & #M◯ & _ & #e0✓eVinit & #e0↪initst & WCOMMIT)".
  { by apply seq_step_Init. } { done. }
  iDestruct (OmoHbToken_finish with "M●") as "M●".

  iMod (own_alloc (set_cf (λ (n : nat), true))) as (γti) "Hγti"; [done|].
  iMod (meta_set _ _ (γts,γsts,γv,γti,tsloc) nroot with "Hmq") as "#HM"; [done|].

  iAssert (SeqPerm γg q EnqP (λ _, true) ∗ SeqPerm γg q DeqP (λ _, true))%I with "[Hγti TSeqPerm]" as "[EnqPerm DeqPerm]".
  { iDestruct (TSeqPerm_Split _ _ _ _ Nat.even with "TSeqPerm") as "[TSeqPermEnq TSeqPermDeq]".
    rewrite (set_cf_split _ Nat.even). iDestruct "Hγti" as "[HγtiEnq HγtiDeq]".
    iSplitL "TSeqPermEnq HγtiEnq"; repeat iExists _; iFrame "HM".
    - iDestruct (TSeqPerm_Equiv _ _ _ _ (λ n, Nat.even n && true) with "TSeqPermEnq") as "TSeqPermEnq".
      { intros. simpl. by destruct (Nat.even n). }
      rewrite (set_cf_equiv _ (λ n, Nat.even n && true)); last first.
      { intros. simpl. by destruct (Nat.even a). }
      iFrame.
    - iDestruct (TSeqPerm_Equiv _ _ _ _ (λ n, Nat.odd n && true) with "TSeqPermDeq") as "TSeqPermDeq".
      { intros. simpl. rewrite Nat.negb_even. by destruct (Nat.odd n). }
      rewrite (set_cf_equiv _ (λ n, Nat.odd n && true)); last first.
      { intros. simpl. rewrite Nat.negb_even. by destruct (Nat.odd a). }
      iFrame. }

  iDestruct ("Post" $! γg γs q {[0]} V2 with "[-]") as "HΦ"; [|iModIntro; by iApply "HΦ"].
  iFrame "⊒V2 EnqPerm DeqPerm WCOMMIT". iSplitR; last iSplitL; [..|done].
  - repeat iExists _. iFrame "HM TSeq◯ M◯ e0✓eVinit". subst eVinit. simpl. done.
  - repeat iExists _. iFrame "HM M● TSeq●". iSplitL "q↦@V2".
    + repeat iExists _. iFrame "e0✓eVinit q↦@V2".
    + iExists initst,(0,0,V1,Mts). iSplitR; [done|].
      iRight. iSplitR; [done|]. subst initst. iFrame "Hγv". iPureIntro. simpl. by rewrite -Nat.even_spec.
Qed.

Lemma enqueueWithTicket_spec :
  enqueueWithTicket_spec' (enqueueWithTicket waitForTurn completeTurn) SeqLocal SeqInv SeqPerm.
Proof.
  intros N DISJ q tid γg γs M V0 v n vPos. iIntros "#⊒V0 #SeqLocal Perm" (Φ) "AU".
  iDestruct "SeqLocal" as (????? Mt0 eV0) "(HM & M◯0 & TSeq◯0 & e0✓eV0 & ⊒eV0SYNC)".
  iCombine "M◯0 TSeq◯0 ⊒eV0SYNC" as "Frags".
  iDestruct (view_at_intro_incl with "Frags ⊒V0") as (V0') "(⊒V0' & %LeV0V0' & (M◯0@V0' & TSeq◯0@V0' & ⊒eV0SYNC@V0'))".
  wp_lam. wp_op. rewrite -[Z.to_nat 0]/(0%nat) shift_0. wp_bind (! _)%E.

  (* Inv access 1 *)
  iMod "AU" as (E1 omo1 stlist1) "[SeqInv [Abort1 _]]".
  iDestruct "SeqInv" as (????? qg1 Et1 omot1 tstlist1) "(>HM' & >M●1 & TSeq●1 & >Field1 & >LAST1)".
  simplify_meta with "HM' HM". iClear "HM'". iDestruct (field_info_lookup with "Field1 e0✓eV0 ⊒eV0SYNC") as (qp) "[q↦ Field1]".
  iMod ("Abort1" with "[-Perm q↦]") as "AU"; [repeat iExists _; iFrame "∗#%"|].

  wp_read. iApply fupd_mask_intro_subseteq; [done|]. wp_pures.
  iDestruct (SeqPerm_split _ _ _ _ (λ m, m =? n) with "Perm") as "[Perm PermReturn]".
  iAssert (TSeqPerm ts γts tsloc (λ m, m =? n * 2) ∗ ⎡own γti (set_cf (λ m, m =? n * 2))⎤)%I
    with "[Perm]" as "[TSeqPerm PermInternal]".
  { iDestruct "Perm" as (?????) "[HM' [Perm PermInternal]]". simplify_meta with "HM' HM". iClear "HM'".
    have H : ∀ m, (λ m', Nat.even m' && ((Z.to_nat (m' `quot` 2) =? n) && (Z.to_nat (m' `quot` 2) =? n))) m = (m =? n * 2).
    { intros. destruct (decide (m = n * 2)) as [->|NEQ].
      - have EQ1 : Nat.even (n * 2) = true.
        { rewrite Nat.even_spec. apply Nat.Even_mul_r. by rewrite -Nat.even_spec. }
        have EQ2 : Z.to_nat ((n * 2)%nat `quot` 2) = n by lia.
        have EQ3 : n =? n = true by rewrite Nat.eqb_eq.
        have EQ4 : n * 2 =? n * 2 = true by rewrite Nat.eqb_eq.
        by rewrite EQ1 EQ2 EQ3 EQ4.
      - destruct (decide (m = n * 2 + 1)) as [->|NEQ2].
        + destruct (Nat.even (n * 2 + 1)) eqn:Hn21.
          { rewrite Nat.even_spec in Hn21.
            have EVEN : Nat.Even (n * 2).
            { apply Nat.Even_mul_r. by rewrite -Nat.even_spec. }
            apply (Nat.Even_add_Even_inv_r _ 1) in EVEN; [|done].
            by rewrite -Nat.even_spec in EVEN. }
          have EQ : n * 2 + 1 =? n * 2 = false by rewrite Nat.eqb_neq.
          by rewrite EQ.
        + have EQ1 : Z.to_nat (m `quot` 2) =? n = false by rewrite Nat.eqb_neq; lia.
          have EQ2 : m =? n * 2 = false by rewrite Nat.eqb_neq.
          by rewrite EQ1 EQ2 andb_assoc andb_comm. }
    iDestruct (TSeqPerm_Equiv _ _ _ _ (λ m, m =? n * 2) with "Perm") as "Perm"; [done|].
    rewrite set_cf_equiv; [|exact H]. iFrame. }

  wp_bind (waitForTurn _)%E. replace (Z.of_nat n * 2)%Z with (Z.of_nat (n * 2)) by lia.
  awp_apply (wait_spec ts _ DISJ tsloc _ _ γsts Mt0 V0' (n * 2) (TSeqRes γv q) with "⊒V0' TSeq◯0 TSeqPerm").

  (* Inv access 2 *)
  iApply (aacc_aupd with "AU"); [solve_ndisj|]. iIntros (E2 omo2 stlist2) "SeqInv".
  iDestruct "SeqInv" as (????? qg2 Et2 omot2 tstlist2) "(>HM' & >M●2 & TSeq●2 & >Field2 & >LAST2)".
  simplify_meta with "HM' HM". iClear "HM'".
  iDestruct (TSeqInv_OmoAuth_acc with "TSeq●2") as "[>Mts● Close]".
  iDestruct (OmoAuth_wf with "Mts●") as %[OMO_GOODts2 _].
  iDestruct (OmoAuth_wf with "M●2") as %[OMO_GOOD2 _].
  iDestruct ("Close" with "[Mts●]") as "TSeq●2"; [iFrame|].

  iAaccIntro with "TSeq●2".
  { (* Peeking case *)
    iIntros "TSeq●2 !>". iSplitR "PermReturn PermInternal q↦"; [|iIntros "$ !>"; iFrame].
    repeat iExists _. iFrame "HM M●2 TSeq●2 Field2 LAST2". }

  iIntros (V2 Mt2) "(TSeq●2 & _ & #⊒V2 & #TSeq◯2@V2 & [%LeV0'V2 %SubMt0Mt2])".
  set eVwait := mkOmoEvent (Take (n * 2)) V2 Mt2.
  set omot2' := omo_insert_r omot2 (length omot2 - 1) (length Et2).
  iDestruct (TSeqInv_OmoAuth_acc with "TSeq●2") as "[>Mts● Close]".
  iDestruct (OmoAuth_wf with "Mts●") as %[OMO_GOODts2' _].
  iDestruct ("Close" with "[Mts●]") as "TSeq●2"; [iFrame|].

  iDestruct "LAST2" as (stf2 tstf2) "[(%LENeq2 & %LASTstf2 & %LASTtstf2) CASE]".
  iAssert (⌜ tstf2.1.1.2 = (n * 2)%nat ∧ tstf2.1.2 ⊑ V2 ⌝)%I with "[-]" as %[Eqtstf2_1_1_2 Letstf2_1_2V2].
  { rewrite !last_lookup in LASTtstf2.
    replace (Init.Nat.pred (length tstlist2)) with (length tstlist2 - 1) in LASTtstf2 by lia.
    rewrite -(omo_stlist_length _ _ _ OMO_GOODts2) in LASTtstf2.
    have LOOKUP1 : (Et2 ++ [eVwait]) !! (length Et2) = Some eVwait by apply lookup_app_1_eq.
    have [es Hes] : is_Some (omo_read_op omot2 !! (length omot2 - 1)).
    { rewrite lookup_lt_is_Some -omo_read_op_length.
      apply lookup_lt_Some in LASTtstf2.
      rewrite -(omo_stlist_length _ _ _ OMO_GOODts2) in LASTtstf2. done. }
    have LOOKUP2 : lookup_omo omot2' (ro_event (length omot2 - 1) (length es)) = Some (length Et2).
    { subst omot2'. rewrite lookup_omo_ro_event omo_insert_r_read_op.
      rewrite list_lookup_alter Hes /= lookup_app_1_eq. done. }
    specialize (omo_read_op_step _ _ _ _ _ _ _ _ OMO_GOODts2' LOOKUP2 LOOKUP1 LASTtstf2) as STEP.
    inversion STEP; subst eVwait; try done.
    inversion TAKE. subst v0. simpl in *. done. }

  iDestruct "CASE" as "[[-> PermInternal']|[-> Hstf2]]".
  { rewrite Eqtstf2_1_1_2. iCombine "PermInternal PermInternal'" as "PermInternal".
    iDestruct (own_valid with "PermInternal") as %valid.
    apply (set_cf_excl _ _ (n * 2)) in valid. simpl in valid.
    have EQ : n * 2 =? n * 2 = true by rewrite Nat.eqb_eq.
    by rewrite EQ in valid. }

  (* Take half ownership of OmoAuth and close Inv *)
  iDestruct "M●2" as "[M●2 M●2']".
  iModIntro. iLeft. iSplitR "PermReturn M●2 Hstf2".
  { repeat iExists _. iFrame "HM M●2' TSeq●2 Field2". repeat iExists _. iSplitR; [done|]. iLeft. rewrite Eqtstf2_1_1_2. by iFrame. }
  iIntros "AU !> [RES TSeqComplete]".
  iDestruct "RES" as (z2) "[q↦1 Hγv]".
  wp_pures. rewrite -[Z.to_nat 1]/(1%nat). wp_write.

  destruct stf2; last first.
  { iDestruct "Hstf2" as (?) "(_ & _ & (_ & _ & %Odd & _))".
    rewrite Eqtstf2_1_1_2 in Odd. apply Nat.Odd_mul_inv_r in Odd. rewrite -Nat.odd_spec in Odd. done. }
  iDestruct "Hstf2" as "[Hγv' _]".
  iDestruct (ghost_var_agree with "Hγv Hγv'") as %->. iCombine "Hγv Hγv'" as "Hγv".
  iMod (ghost_var_update v with "Hγv") as "Hγv". iDestruct "Hγv" as "[Hγv Hγv']".

  replace (Z.of_nat n * 2)%Z with (Z.of_nat (n * 2)) by lia.
  awp_apply (complete_spec ts _ DISJ tsloc _ _ γsts Mt0 V2 (n * 2) (TSeqRes γv q)
    with "⊒V2 TSeq◯0 [q↦1 Hγv'] TSeqComplete").
  { iExists v. iFrame. }

  (* Inv access 3 *)
  iApply (aacc_aupd with "AU"); [solve_ndisj|]. iIntros (E3 omo3 stlist3) "SeqInv".
  iDestruct "SeqInv" as (????? qg3 Et3 omot3 tstlist3) "(>HM' & >M●3 & TSeq●3 & >Field3 & >LAST3)".
  simplify_meta with "HM' HM". iClear "HM'".

  iAaccIntro with "TSeq●3".
  { (* Peeking case *)
    iIntros "TSeq●3 !>". iSplitR "PermReturn M●2 Hγv"; [|iIntros "$ !>"; iFrame].
    repeat iExists _. iFrame "HM M●3 TSeq●3 Field3 LAST3". }

  (* Committing case *)
  iIntros (V3 Mt3) "(TSeq●3 & WCOMMIT & #⊒V3 & #TSeq◯3@V3 & [%LeV2V3 %SubMt0Mt3])".
  set eVcomp := mkOmoEvent (Complete (n * 2)) V3 Mt3.
  set omot3' := omo_append_w omot3 (length Et3) [].
  set ntst := (length Et3, n * 2 + 1, eVcomp.(sync), eVcomp.(eview)).

  iDestruct (OmoAuth_agree with "M●3 M●2") as %(_ & -> & -> & ->).
  iAssert (⌜ qg3 = (1/2)%Qp ⌝)%I with "[-]" as %->.
  { iDestruct "LAST3" as (stf3 tstf3) "[_ [[-> _]|[-> _]]]"; [done|].
    iCombine "M●2 M●3" as "M●3". by iDestruct (OmoAuth_frac_valid with "M●3") as %?. }
  iCombine "M●3 M●2" as "M●3".

  have LeV0V3 : V0 ⊑ V3 by solve_lat.
  set enqId := length E2.
  set M' := {[enqId]} ∪ M.
  set eVenq := mkOmoEvent (Enq v n) V3 M'.
  set E2' := E2 ++ [eVenq].
  set enqst : seq_state := [(enqId, v, n, eVenq.(sync), eVenq.(eview))].

  iDestruct (view_at_mono_2 _ V3 with "M◯0@V0'") as "M◯0@V3"; [solve_lat|].
  iMod (OmoAuth_insert_last with "M●3 M◯0@V3 WCOMMIT []")
    as "(M●3 & #M◯3@V3 & #enqId↦etn3 & #enqId✓eVenq & #enqId↪enqst & WCOMMIT)".
  { have ? : step enqId eVenq [] enqst by apply seq_step_Enq; try done; subst eVenq M'; set_solver-.
    iPureIntro. by split_and!. }
  iDestruct (OmoHbToken_finish with "M●3") as "M●3".

  iModIntro. iRight. iExists V3,M'. iFrame "⊒V3 WCOMMIT". iSplitR "PermReturn"; last first.
  { iIntros "HΦ !> _". by iApply "HΦ". }
  iSplitL; last iSplit.
  - repeat iExists _. iFrame "HM M●3 TSeq●3 Field3".
    iDestruct "LAST3" as (??) "[[%LENeq3 _] _]". clear stf tstf. iExists enqst,ntst. iSplitR.
    + iPureIntro. split_and!; try by rewrite last_app. by rewrite /= !app_length LENeq3 /=.
    + iRight. iSplitR; [done|]. subst enqst. simpl.
      iExists eVenq. iFrame "enqId✓eVenq Hγv". iPureIntro. split_and!; try done.
      * by rewrite omo_append_w_write_op last_app /=.
      * apply Nat.Odd_add_r; [|by rewrite -Nat.odd_spec]. apply Nat.Even_mul_r. by rewrite -Nat.even_spec.
      * lia.
  - repeat iExists _. iFrame "HM TSeq◯3@V3 M◯3@V3 e0✓eV0 ⊒eV0SYNC@V0'".
  - iPureIntro. split_and!; try done. subst M'. set_solver-.
Qed.

Lemma dequeueWithTicket_spec :
  dequeueWithTicket_spec' (dequeueWithTicket waitForTurn completeTurn) SeqLocal SeqInv SeqPerm.
Proof.
  intros N DISJ q tid γg γs M V0 n. iIntros "#⊒V0 #SeqLocal Perm" (Φ) "AU".
  iDestruct "SeqLocal" as (????? Mt0 eV0) "(HM & M◯0 & TSeq◯0 & e0✓eV0 & ⊒eV0SYNC)".
  iCombine "M◯0 TSeq◯0 ⊒eV0SYNC" as "Frags".
  iDestruct (view_at_intro_incl with "Frags ⊒V0")
    as (V0') "(⊒V0' & %LeV0V0' & (M◯0@V0' & TSeq◯0@V0' & ⊒eV0SYNC@V0'))".
  wp_lam. wp_op. rewrite -[Z.to_nat 0]/(0%nat) shift_0. wp_bind (! _)%E.

  (* Inv access 1 *)
  iMod "AU" as (E1 omo1 stlist1) "[SeqInv [Abort1 _]]".
  iDestruct "SeqInv" as (????? qg1 Et1 omot1 tstilst1) "(>HM' & >M●1 & TSeq●1 & >Field1 & >LAST1)".
  simplify_meta with "HM' HM". iClear "HM'".
  iDestruct (field_info_lookup with "Field1 e0✓eV0 ⊒eV0SYNC") as (qp) "[q↦ Field1]".
  iMod ("Abort1" with "[-Perm q↦]") as "AU"; [repeat iExists _; iFrame "∗#%"|].

  wp_read. iApply fupd_mask_intro_subseteq; [done|]. wp_pures.
  iDestruct (SeqPerm_split _ _ _ _ (λ m, m =? n) with "Perm") as "[Perm PermReturn]".
  iAssert (TSeqPerm ts γts tsloc (λ m, m =? n * 2 + 1) ∗ ⎡own γti (set_cf (λ m, m =? n * 2 + 1))⎤)%I
    with "[Perm]" as "[TSeqPerm PermInternal]".
  { iDestruct "Perm" as (?????) "[HM' [Perm PermInternal]]". simplify_meta with "HM' HM". iClear "HM'".
    have H : ∀ m, (λ m', Nat.odd m' && ((Z.to_nat ((m' - 1) `quot` 2) =? n) && (Z.to_nat ((m' - 1) `quot` 2) =? n))) m = (m =? n * 2 + 1).
    { intros. destruct (decide (m = n * 2 + 1)) as [->|NEQ].
      - have EQ1 : Nat.odd (n * 2 + 1) = true.
        { rewrite Nat.odd_spec. apply Nat.Odd_add_r; [|by rewrite -Nat.odd_spec].
          apply Nat.Even_mul_r. by rewrite -Nat.even_spec. }
        have EQ2 : Z.to_nat (((n * 2 + 1)%nat - 1) `quot` 2) = n by lia.
        have EQ3 : n =? n = true by rewrite Nat.eqb_eq.
        have EQ4 : n * 2 + 1 =? n * 2 + 1 = true by rewrite Nat.eqb_eq.
        by rewrite EQ1 EQ2 EQ3 EQ4.
      - destruct (decide (m = n * 2 + 2)) as [->|NEQ2].
        + destruct (Nat.odd (n * 2 + 2)) eqn:Hn2.
          { rewrite Nat.odd_spec in Hn2. replace (n * 2 + 2) with ((n + 1) * 2) in Hn2 by lia.
            apply Nat.Odd_mul_inv_r in Hn2. by rewrite -Nat.odd_spec in Hn2. }
          have EQ : n * 2 + 2 =? n * 2 + 1 = false by rewrite Nat.eqb_neq.
          by rewrite EQ.
        + rewrite andb_comm -andb_assoc andb_comm.
          have EQ1 : (Z.to_nat ((m - 1) `quot` 2) =? n) && Nat.odd m = false.
          { destruct m.
            - destruct (Nat.odd 0) eqn:H0; [done|]. by rewrite andb_comm.
            - have EQ : Z.to_nat ((S m - 1) `quot` 2) =? n = false by rewrite Nat.eqb_neq; lia.
              by rewrite EQ. }
          have EQ2 : m =? n * 2 + 1 = false by rewrite Nat.eqb_neq.
          by rewrite EQ1 EQ2. }
    iDestruct (TSeqPerm_Equiv _ _ _ _ (λ m, m =? n * 2 + 1) with "Perm") as "Perm"; [done|].
    rewrite set_cf_equiv; [|exact H]. iFrame. }

  wp_bind (waitForTurn _)%E. replace (Z.of_nat n * 2 + 1)%Z with (Z.of_nat (n * 2 + 1)) by lia.
  awp_apply (wait_spec ts _ DISJ tsloc _ _ γsts Mt0 V0' (n * 2 + 1) (TSeqRes γv q)
    with "⊒V0' TSeq◯0 TSeqPerm").

  (* Inv access 2 *)
  iApply (aacc_aupd with "AU"); [solve_ndisj|]. iIntros (E2 omo2 stlist2) "SeqInv".
  iDestruct "SeqInv" as (????? qg2 Et2 omot2 tstlist2) "(>HM' & >M●2 & TSeq●2 & >Field2 & >LAST2)".
  simplify_meta with "HM' HM". iClear "HM'".
  iDestruct (TSeqInv_OmoAuth_acc with "TSeq●2") as "[>Mts● Close]".
  iDestruct (OmoAuth_wf with "Mts●") as %[OMO_GOODts2 _].
  iDestruct (OmoAuth_wf with "M●2") as %[OMO_GOOD2 _].
  iDestruct ("Close" with "[Mts●]") as "TSeq●2"; [iFrame|].

  iAaccIntro with "TSeq●2".
  { (* Peeking case *)
    iIntros "TSeq●2 !>". iSplitR "PermReturn PermInternal q↦"; [|iIntros "$ !>"; iFrame].
    repeat iExists _. iFrame "HM M●2 TSeq●2 Field2 LAST2". }

  iIntros (V2 Mt2) "(TSeq●2 & _ & #⊒V2 & #TSeq◯2@V2 & [%LeV0'V2 %SubMt0Mt2])".
  set eVwait := mkOmoEvent (Take (n * 2 + 1)) V2 Mt2.
  set omot2' := omo_insert_r omot2 (length omot2 - 1) (length Et2).
  iDestruct (TSeqInv_OmoAuth_acc with "TSeq●2") as "[>Mts● Close]".
  iDestruct (OmoAuth_wf with "Mts●") as %[OMO_GOODts2' _].
  iDestruct ("Close" with "[Mts●]") as "TSeq●2"; [iFrame|].

  iDestruct "LAST2" as (stf2 tstf2) "[(%LENeq2 & %LASTstf2 & %LASTtstf2) CASE]".
  iAssert (⌜ tstf2.1.1.2 = (n * 2 + 1)%nat ∧ tstf2.1.2 ⊑ V2 ⌝)%I
    with "[-]" as %[Eqtstf2_1_1_2 Letstf2_1_2V2].
  { rewrite !last_lookup in LASTtstf2.
    replace (Init.Nat.pred (length tstlist2)) with (length tstlist2 - 1) in LASTtstf2 by lia.
    rewrite -(omo_stlist_length _ _ _ OMO_GOODts2) in LASTtstf2.
    have LOOKUP1 : (Et2 ++ [eVwait]) !! (length Et2) = Some eVwait by apply lookup_app_1_eq.
    have [es Hes] : is_Some (omo_read_op omot2 !! (length omot2 - 1)).
    { rewrite lookup_lt_is_Some -omo_read_op_length.
      apply lookup_lt_Some in LASTtstf2.
      rewrite -(omo_stlist_length _ _ _ OMO_GOODts2) in LASTtstf2. done. }
    have LOOKUP2 : lookup_omo omot2' (ro_event (length omot2 - 1) (length es)) = Some (length Et2).
    { subst omot2'. rewrite lookup_omo_ro_event omo_insert_r_read_op.
      rewrite list_lookup_alter Hes /= lookup_app_1_eq. done. }
    specialize (omo_read_op_step _ _ _ _ _ _ _ _ OMO_GOODts2' LOOKUP2 LOOKUP1 LASTtstf2) as STEP.
    inversion STEP; subst eVwait; try done.
    inversion TAKE. subst v. simpl in *. done. }

  iDestruct "CASE" as "[[-> PermInternal']|[-> Hstf2]]".
  { rewrite Eqtstf2_1_1_2. iCombine "PermInternal PermInternal'" as "PermInternal".
    iDestruct (own_valid with "PermInternal") as %valid.
    apply (set_cf_excl _ _ (n * 2 + 1)) in valid. simpl in valid.
    have EQ : n * 2 + 1 =? n * 2 + 1 = true by rewrite Nat.eqb_eq.
    by rewrite EQ in valid. }

  (* Take half ownership of OmoAuth and close Inv *)
  iDestruct "M●2" as "[M●2 M●2']".
  iModIntro. iLeft. iSplitR "PermReturn M●2 Hstf2".
  { repeat iExists _. iFrame "HM M●2' TSeq●2 Field2". repeat iExists _. iSplitR; [done|]. iLeft. rewrite Eqtstf2_1_1_2. by iFrame. }
  iIntros "AU !> [RES TSeqComplete]".
  iDestruct "RES" as (z2) "[q↦1 Hγv]".
  wp_pures. rewrite -[Z.to_nat 1]/(1%nat). wp_read. wp_let. wp_write.

  destruct stf2 as [|stfh2 stft2].
  { iDestruct "Hstf2" as "[_ %Even]". rewrite Eqtstf2_1_1_2 in Even.
    have Even' : Nat.Even (n * 2) by apply Nat.Even_mul_r; rewrite -Nat.even_spec.
    eapply Nat.Even_add_Even_inv_r in Even'; [|exact Even]. rewrite -Nat.even_spec in Even'. done. }
  iDestruct "Hstf2" as (eVf2)
    "(#ef2✓eVf2 & Hγv' & (%LASTef2 & % & %Oddtstf2 & %EqTurn & %GT & %Eqstfh2tstf2 & %EqViewstfh2 & %EqLviewstfh2))".
  subst stft2. iDestruct (ghost_var_agree with "Hγv Hγv'") as %->. iCombine "Hγv Hγv'" as "Hγv".
  iMod (ghost_var_update 0%Z with "Hγv") as "Hγv". iDestruct "Hγv" as "[Hγv Hγv']".

  awp_apply (complete_spec ts _ DISJ tsloc _ _ γsts Mt0 V2 (n * 2 + 1) (TSeqRes γv q) with "⊒V2 TSeq◯0 [q↦1 Hγv'] TSeqComplete").
  { iExists 0%Z. iFrame. }

  (* Inv access 3 *)
  iApply (aacc_aupd with "AU"); [solve_ndisj|]. iIntros (E3 omo3 stlist3) "SeqInv".
  iDestruct "SeqInv" as (????? qg3 Et3 omot3 tstlist3) "(>HM' & >M●3 & TSeq●3 & >Field3 & >LAST3)".
  simplify_meta with "HM' HM". iClear "HM'".

  iAaccIntro with "TSeq●3".
  { (* Peeking case *)
    iIntros "TSeq●3 !>". iSplitR "PermReturn M●2 Hγv"; [|iIntros "$ !>"; iFrame].
    repeat iExists _. iFrame "HM M●3 TSeq●3 Field3 LAST3". }

  (* Committing case *)
  iIntros (V3 Mt3) "(TSeq●3 & WCOMMIT & #⊒V3 & #TSeq◯3@V3 & [%LeV2V3 %SubMt0Mt3])".
  set eVcomp := mkOmoEvent (Complete (n * 2 + 1)) V3 Mt3.
  set omot3' := omo_append_w omot3 (length Et3) [].
  set ntst := (length Et3, n * 2 + 1 + 1, eVcomp.(sync), eVcomp.(eview)).

  iDestruct (OmoAuth_agree with "M●3 M●2") as %(_ & -> & -> & ->).
  iAssert (⌜ qg3 = (1/2)%Qp ⌝)%I with "[-]" as %->.
  { iDestruct "LAST3" as (stf3 tstf3) "[_ [[-> _]|[-> _]]]"; [done|].
    iCombine "M●2 M●3" as "M●3". by iDestruct (OmoAuth_frac_valid with "M●3") as %?. }
  iCombine "M●3 M●2" as "M●3".

  have LeV0V3 : V0 ⊑ V3 by solve_lat.
  set deqId := length E2.
  set M' := {[deqId; stfh2.1.1.1.1]} ∪ eVf2.(eview) ∪ M.
  set eVdeq := mkOmoEvent (Deq stfh2.1.1.1.2 n) V3 M'.
  set E2' := E2 ++ [eVdeq].
  set deqst : seq_state := [].

  iDestruct (view_at_mono_2 _ V3 with "M◯0@V0'") as "M◯0@V3"; [solve_lat|].
  iDestruct (OmoEview_insert_new_obj with "M◯0@V3 ef2✓eVf2") as "M◯0'@V3".
  { rewrite -EqViewstfh2 Eqstfh2tstf2. clear -Letstf2_1_2V2 LeV2V3. solve_lat. }
  iMod (OmoAuth_insert_last with "M●3 M◯0'@V3 WCOMMIT []")
    as "(M●3 & #M◯3@V3 & #enqId↦etn3 & #enqId✓eVenq & #enqId↪enqst & WCOMMIT)".
  { have ? : step deqId eVdeq [stfh2] deqst.
    { destruct stfh2 as [[[[a b] c] d] e]. simpl in *. subst. apply seq_step_Deq; try done.
      - subst eVdeq. rewrite Eqtstf2_1_1_2.
        by replace (Z.to_nat (((n * 2 + 1)%nat - 1) `quot` 2)) with n by lia.
      - subst eVdeq. simpl. solve_lat.
      - subst eVdeq M'. simpl. set_solver-. }
    iPureIntro. split_and!; try done. subst eVdeq M' deqId. simpl. set_solver-. }
  iDestruct (OmoHbToken_finish with "M●3") as "M●3".

  iModIntro. iRight. iExists V3,M',stfh2.1.1.1.2. iFrame "⊒V3 WCOMMIT". iSplitL; last first.
  { iIntros "HΦ !> _". wp_pures. by iApply "HΦ". }

  iSplitL; last iSplit.
  - repeat iExists _. iFrame "HM M●3 TSeq●3 Field3".
    iDestruct "LAST3" as (??) "[[%LENeq3 _] _]". clear stf tstf. iExists deqst,ntst. iSplitR.
    + iPureIntro. split_and!; try by rewrite last_app. rewrite !app_length LENeq3 /=. done.
    + iRight. iSplitR; [done|]. subst deqst. iFrame "Hγv". iPureIntro. subst ntst. simpl.
      replace (n * 2 + 1 + 1) with ((n + 1) * 2) by lia. apply Nat.Even_mul_r. by rewrite -Nat.even_spec.
  - repeat iExists _. iFrame "HM TSeq◯3@V3 e0✓eV0 ⊒eV0SYNC@V0'".
    replace ({[length E2]} ∪ ({[stfh2.1.1.1.1]} ∪ eVf2.(eview) ∪ M)) with M' by set_solver. iFrame "M◯3@V3".
  - iPureIntro. split_and!; try done. subst M'. set_solver-.
Qed.
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
