From gpfsl.examples Require Import sflib.

From iris.algebra Require Import auth gset gmap agree.
From iris.proofmode Require Import tactics.
From iris.base_logic.lib Require Import ghost_var.

From gpfsl.base_logic Require Import meta_data.
From gpfsl.logic Require Import logatom atomics invariants.

From gpfsl.logic Require Import repeat_loop new_delete.
From gpfsl.examples Require Import uniq_token map_seq loc_helper.
From gpfsl.examples.algebra Require Import set mono_list.
From gpfsl.examples.folly Require Import spec_turnSequencer_composition spec_singleElementQueue_composition spec_mpmcqueue_history.
From gpfsl.examples.folly Require Import code_singleElementQueue code_mpmcqueue.
From gpfsl.examples.omo Require Import omo omo_preds append_only_loc.

Require Import iris.prelude.options.
From Coq Require Import ZArith.
From Coq.ZArith Require Import Zquot.

Inductive helping_state := Pending | Accepted | Acked.
Local Instance helping_state_inhabited : Inhabited helping_state := populate Pending.

Class mpmcqueueG Σ := MpmcQueueG {
  mpmc_omoGeneralG :> omoGeneralG Σ;
  mpmc_omoG :> omoSpecificG Σ qevent queue_state;
  mpmc_seqG :> omoSpecificG Σ seq_event seq_state;
  mpmc_aolocG :> appendOnlyLocG Σ;
  mpmc_nodes_monoG :> mono_listG (event_id * Z * view * eView) Σ;
  mpmc_helping_monoG :> mono_listG gname Σ;
  mpmc_helping_stateG :> ghost_varG Σ helping_state;
  mpmc_uniqTokG :> uniqTokG Σ;
}.

Definition mpmcqueueΣ : gFunctors := #[omoGeneralΣ; omoSpecificΣ qevent queue_state; omoSpecificΣ seq_event seq_state; appendOnlyLocΣ; mono_listΣ (event_id * Z * view * eView); mono_listΣ gname; ghost_varΣ helping_state; uniqTokΣ].

Global Instance subG_mpmcqueueΣ {Σ} : subG mpmcqueueΣ Σ → mpmcqueueG Σ.
Proof. solve_inG. Qed.

Section MpmcQueue.
Context `{!noprolG Σ, !atomicG Σ, !mpmcqueueG Σ}.

Local Notation iProp := (iProp Σ).
Local Notation vProp := (vProp Σ).

Implicit Types
  (γg γq γs γsq γn γl γsl γh : gname) (sz enqcnt deqcnt : nat)
  (hst : helping_state)
  (aols : list (gname * gname))
  (seqs : list (gname * gname * loc))
  (nodes : queue_state) (hlist : list gname)
  (omo omol omos : omoT)
  (q sloc : loc)
  (E : history qevent) (Es : history seq_event) (El : history loc_event).

Hypothesis (seq : seq_composition_spec Σ).

Local Open Scope nat_scope.

Definition mpmcqN (N : namespace) := N .@ "mpmc".
Definition seqN (N : namespace) := N .@ "seq".
Definition helpN (N : namespace) := N .@ "helping".

Definition ticket_info q aols (idx cnt : nat) : vProp :=
  ∃ γl γsl El omol mo,
    ⌜ aols !! idx = Some (γl, γsl) ∧ cnt = length omol - 1 ∧ length omol ≠ 0 ⌝ ∗
    OmoAuth γl γsl (1/2) El omol mo _ ∗
    (∃ Vb, @{Vb} append_only_loc (q >> idx) γl ∅ cas_only) ∗
    [∗ list] i↦el ∈ (omo_write_op omol),
      ∃ (eVl : omo_event loc_event),
        OmoEinfo γl el eVl ∗
        ⌜ (loc_event_msg eVl.(type)).1 = #i ⌝.

Definition field_info_inner qp q seqs sz : vProp :=
  (q >> 2) ↦{qp} #sz ∗ [∗ list] idx↦x ∈ seqs, (q >> (idx + 3)) ↦{qp} #(LitLoc x.2).

Definition field_info γg q seqs sz : vProp :=
  ∃ (eV0 : omo_event qevent) qp,
    OmoEinfo γg 0 eV0 ∗ @{eV0.(sync)} field_info_inner qp q seqs sz.

Definition slot_info γn γseq γseqs sloc (sz idx : nat) : vProp :=
  ∃ Es omos (seq_stlist : list seq_state) stf,
  SeqInv seq γseq γseqs sloc Es omos seq_stlist ∗
  ⌜ last seq_stlist = Some stf ⌝ ∗
  match stf with
  | [] => emp
  | stfh :: stft =>
    ∃ (enqId : event_id) (V : view) (lV : eView),
      let nidx := sz * stfh.1.1.2 + idx in
      ⎡mono_list_idx_own γn nidx (enqId, stfh.1.1.1.2, V, lV)⎤ ∗
      ⌜ stft = [] ∧ V ⊑ stfh.1.2 ⌝
  end.

Definition slot_field γn seqs sz : vProp :=
  [∗ list] idx↦x ∈ seqs, ∃ γseq γseqs sloc, ⌜ x = (γseq, γseqs, sloc) ⌝ ∗ slot_info γn γseq γseqs sloc sz idx.

Definition perm_bank seqs (sz cnt : nat) (ty : seq_perm_type) : vProp :=
  [∗ list] idx↦x ∈ seqs,
    ∃ γseq γseqs sloc, ⌜ x = (γseq, γseqs, sloc) ⌝ ∗ SeqPerm seq γseq sloc ty (λ m, Z.to_nat ((cnt + sz - idx - 1) `quot` sz)%Z <=? m).

Definition QueueInv γg q E : vProp :=
  ∃ γs omo stlist, OmoAuth γg γs (1/2) E omo stlist _.

Definition QueueLocal_inner (N : namespace) γg q M : vProp :=
  ∃ γs γn γh aols seqs (sz : nat),
    meta q nroot (γs,γn,γh,aols,seqs,sz) ∗
    OmoEview γg M ∗
    ([∗ list] x ∈ aols,
      ∃ γl γsl Ml, OmoEview γl Ml ∗ ⌜ x = (γl, γsl) ⌝) ∗
    ([∗ list] x ∈ seqs,
      ∃ γseq γseqs sloc Mseq, SeqLocal seq (seqN N) γseq sloc Mseq ∗ ⌜ x = (γseq, γseqs, sloc) ⌝) ∗
    (∃ (eV0 : omo_event qevent), OmoEinfo γg 0 eV0 ∗ ⊒(eV0.(sync))).

Definition atomic_update_deq (N : namespace) γg q (V : view) (M : eView) (Q : Z → vProp) : vProp :=
  atomic_update (⊤ ∖ ↑N) (↑histN)
    (tele_app (TT:= [tele _]) (λ E, ▷ QueueInv γg q E)%I)
    (tele_app (TT:= [tele _])
      (λ E, tele_app (TT:= [tele _ _ _ _])
        (λ (v : Z) V' E' M',
          ▷ QueueInv γg q E' ∗ ⊒V' ∗ @{V'} QueueLocal_inner N γg q M' ∗ OmoSnapHistory γg E' ∗
          ⌜ V ⊑ V' ∧
          E' = E ++ [mkOmoEvent (Deq v) V' M'] ∧ M ⊆ M' ∧ (0 < v)%Z ⌝)%I))
    (tele_app (TT:= [tele _])
      (λ E, tele_app (TT:= [tele _ _ _ _])
        (λ v V' E' M', Q v)%I)).

Definition helping_res γn γi γu idx Vb (Q : Z → vProp) : vProp :=
  ∃ hst,
    ⎡ghost_var γi (1/2)%Qp hst⎤ ∗
    match hst with
    | Pending => emp
    | Accepted => ∃ enqId v V lV, ⎡mono_list_idx_own γn idx (enqId, v, V, lV)⎤ ∗ @{Vb ⊔ V} (Q v)
    | Acked => UTok γu
    end.

Definition helping_info (N : namespace) γg γn q enqcnt hlist : vProp :=
  ([∗ list] γi ∈ take enqcnt hlist, ∃ hst, ⎡ghost_var γi (1/2)%Qp hst⎤ ∗ ⌜ hst ≠ Pending ⌝) ∗
  ([∗ list] i↦γi ∈ drop enqcnt hlist,
    ∃ γl el γu Vb Vi M Q,
      ⌜ Vi ⊑ Vb ⌝ ∗
      ⎡ghost_var γi (1/2)%Qp Pending⎤ ∗
      OmoTokenW γl el ∗
      @{Vb} (atomic_update_deq N γg q Vi M Q ∗ QueueLocal_inner N γg q M) ∗
      inv (helpN N) (helping_res γn γi γu (enqcnt + i) Vb Q)).

Definition nodes_info γg nodes : vProp :=
  [∗ list] node ∈ nodes,
    ∃ enqId v (eV : omo_event qevent),
      ⌜ node = (enqId, v, eV.(sync), eV.(eview)) ∧ (0 < v)%Z ⌝ ∗ OmoEinfo γg enqId eV.

Definition QueueInternalInv (N : namespace) γg q E : vProp :=
  ∃ γs γn γh aols seqs (sz enqcnt deqcnt : nat) omo stlist nodes hlist,
    meta q nroot (γs,γn,γh,aols,seqs,sz) ∗

    OmoAuth γg γs (1/2)%Qp E omo stlist _ ∗
    ⎡mono_list_auth_own γn 1 nodes⎤ ∗
    ⎡mono_list_auth_own γh 1 hlist⎤ ∗

    ticket_info q aols 0 enqcnt ∗
    ticket_info q aols 1 deqcnt ∗
    field_info γg q seqs sz ∗
    slot_field γn seqs sz ∗
    perm_bank seqs sz enqcnt EnqP ∗
    perm_bank seqs sz deqcnt DeqP ∗
    helping_info N γg γn q enqcnt hlist ∗
    nodes_info γg nodes ∗

    ⌜ last stlist = Some (drop deqcnt nodes)
    ∧ length nodes = enqcnt
    ∧ length hlist = deqcnt
    ∧ length seqs = sz
    ∧ (length aols = 2)%nat
    ∧ sz ≠ 0 ⌝.

Definition InternalInv_inner N γg q : vProp := ∃ E, QueueInternalInv N γg q E.
Definition InternInv N γg q := inv (mpmcqN N) (InternalInv_inner N γg q).

Definition QueueLocal (N : namespace) γg q E M : vProp :=
  QueueLocal_inner N γg q M ∗
  InternInv N γg q ∗
  OmoSnapHistory γg E.

Local Instance slot_info_objective γn γseq γseqs slot sz idx : Objective (slot_info γn γseq γseqs slot sz idx).
Proof. repeat (apply exists_objective; intros). destruct x2; apply _. Qed.
Local Instance QueueInternalInv_objective N γg q E : Objective (QueueInternalInv N γg q E) := _.
Local Instance helping_res_objective γn γi γu idx Vb Q : Objective (helping_res γn γi γu idx Vb Q).
Proof. apply exists_objective; intros. destruct x; apply _. Qed.
Global Instance QueueInv_objective γg q E : Objective (QueueInv γg q E) := _.
Global Instance QueueInv_timeless γg q E : Timeless (QueueInv γg q E) := _.
Global Instance QueueLocal_persistent N γg q E M : Persistent (QueueLocal N γg q E M) := _.

Local Tactic Notation "simplify_meta" "with" constr(Hs) :=
  iDestruct (meta_agree with Hs) as %[[[[[-> ->]%pair_inj ->]%pair_inj ->]%pair_inj ->]%pair_inj ->]%pair_inj.

Notation newSEQ := (spec_singleElementQueue_composition.newSEQ seq).
Notation enqueueWithTicket := (spec_singleElementQueue_composition.enqueueWithTicket seq).
Notation dequeueWithTicket := (spec_singleElementQueue_composition.dequeueWithTicket seq).

Lemma QueueInv_Linearizable_instance :
  ∀ γg q E, QueueInv γg q E ⊢ ⌜ Linearizability E ⌝.
Proof.
  intros. iDestruct 1 as (???) "M●".
  iDestruct (OmoAuth_Linearizable with "M●") as %H. by apply omo_compatible in H.
Qed.

Lemma QueueInv_history_wf_instance :
  ∀ γg q E, QueueInv γg q E ⊢ ⌜ history_wf E ⌝.
Proof.
  intros. iDestruct 1 as (???) "M●".
  by iDestruct (OmoAuth_wf with "M●") as "[_ %H]".
Qed.

Lemma QueueInv_QueueLocal_instance :
  ∀ N γg q E E' M',
    QueueInv γg q E -∗ QueueLocal N γg q E' M' -∗ ⌜ E' ⊑ E ⌝.
Proof.
  intros. iDestruct 1 as (???) "M●". iDestruct 1 as "(_ & _ & E◯)".
  by iDestruct (OmoAuth_OmoSnapHistory with "M● E◯") as %?.
Qed.

Lemma QueueLocal_lookup_instance :
  ∀ N γg q E M e V,
    sync <$> E !! e = Some V → e ∈ M →
    QueueLocal N γg q E M -∗ ⊒V.
Proof.
  intros. iDestruct 1 as "((%&%&%&%&%&%& _ & M◯ & _) & _ & E◯)".
  by iApply (OmoSnapHistory_OmoEview with "E◯ M◯").
Qed.

(* For the [lia] tactic. *)
(* To support Z.div, Z.modulo, Z.quot, and Z.rem: *)
Ltac Zify.zify_post_hook ::= Z.to_euclidean_division_equations.

Lemma extract_one_ticket seqs sz cnt ty (turn := (Z.of_nat cnt `quot` Z.of_nat sz)%Z) (idx := (Z.of_nat cnt `rem` Z.of_nat sz)%Z)  :
  length seqs = sz → sz ≠ 0 →
  perm_bank seqs sz cnt ty -∗
  ∃ γseq γseqs sloc,
    perm_bank seqs sz (cnt + 1) ty ∗
    SeqPerm seq γseq sloc ty (λ m, m =? (Z.to_nat turn)) ∗ ⌜ seqs !! (Z.to_nat idx) = Some (γseq, γseqs, sloc) ⌝.
Proof.
  iIntros "%LENseqs %NZ Perms".
  have [[[γseq γseqs] sloc] Hseqs] : is_Some (seqs !! (Z.to_nat idx)) by rewrite lookup_lt_is_Some; lia.
  iExists γseq,γseqs,sloc.
  iDestruct (big_sepL_take_drop _ _ (S (Z.to_nat idx)) with "Perms") as "[Perms Perms']".
  rewrite /perm_bank (take_S_r _ _ (γseq, γseqs, sloc)); [|done]. rewrite big_sepL_snoc.
  iDestruct "Perms" as "[Perms (%&%&%&%& Perm)]".
  inversion H. subst γseq0 γseqs0 sloc0. clear H.

  rewrite take_length Nat.min_l; [|lia].
  replace (Z.of_nat (Z.to_nat idx)) with idx by lia.
  have TurnEQ : ((Z.of_nat cnt + Z.of_nat sz - idx - 1) `quot` (Z.of_nat sz) = turn)%Z; [|rewrite TurnEQ].
  { have ? : (turn ≤ (Z.of_nat cnt + Z.of_nat sz - idx - 1) `quot` (Z.of_nat sz))%Z by apply Zquot_le_lower_bound; lia.
    have ? : ((Z.of_nat cnt + Z.of_nat sz - idx - 1) `quot` (Z.of_nat sz) ≤ turn)%Z; [|lia].
    apply Zquot_le_lower_bound; try lia.
    rewrite {1}(Z.quot_rem' (Z.of_nat cnt) (Z.of_nat sz)).
    replace (Z.of_nat sz * (Z.of_nat cnt `quot` Z.of_nat sz) + Z.of_nat cnt `rem` Z.of_nat sz + Z.of_nat sz - idx - 1)%Z
      with ((Z.of_nat cnt `quot` Z.of_nat sz) * Z.of_nat sz + (Z.of_nat sz - 1))%Z by lia.
    rewrite Z_quot_plus_l; try lia; last first.
    { have ? : (0 ≤ Z.of_nat cnt `quot` Z.of_nat sz)%Z by apply Zquot_le_lower_bound; lia.
      have ? : (0 ≤ Z.of_nat cnt `quot` Z.of_nat sz * Z.of_nat sz)%Z by lia.
      have ? : (0 ≤ (Z.of_nat sz - 1) * (Z.of_nat sz - 1))%Z; by destruct sz; lia. }
    replace ((Z.of_nat sz - 1) `quot` Z.of_nat sz)%Z with 0%Z; [lia|].
    have ? : (0 ≤ (Z.of_nat sz - 1) `quot` (Z.of_nat sz))%Z by apply Zquot_le_lower_bound; lia.
    have ? : ((Z.of_nat sz - 1) `quot` (Z.of_nat sz) < 1)%Z; [by apply Zquot_lt_upper_bound; lia|lia]. }

  have NextTurnEQ : ((Z.of_nat (cnt + 1) + Z.of_nat sz - idx - 1) `quot` (Z.of_nat sz) = turn + 1)%Z.
  { replace (Z.of_nat (cnt + 1) + Z.of_nat sz - idx - 1)%Z with ((Z.of_nat cnt - idx) + Z.of_nat sz)%Z by lia.
    replace (Z.of_nat cnt + Z.of_nat sz - idx - 1)%Z with ((Z.of_nat cnt - idx) + (Z.of_nat sz - 1))%Z in TurnEQ by lia.
    have DIV : ((Z.of_nat cnt - idx) `rem` (Z.of_nat sz) = 0)%Z.
    { rewrite {1}(Z.quot_rem' (Z.of_nat cnt) (Z.of_nat sz)).
      replace (Z.of_nat sz * (Z.of_nat cnt `quot` Z.of_nat sz) + Z.of_nat cnt `rem` Z.of_nat sz - idx)%Z
        with (0 + (Z.of_nat cnt `quot` Z.of_nat sz) * Z.of_nat sz)%Z by lia.
      rewrite Z_rem_plus; lia. }
    apply Zrem_divides in DIV. destruct DIV as [z Hz]. rewrite Hz.
    replace (Z.of_nat sz * z + Z.of_nat sz)%Z with (Z.of_nat sz + z * Z.of_nat sz)%Z by lia.
    rewrite Z_quot_plus; try lia; last first.
    { replace (z * Z.of_nat sz)%Z with (Z.of_nat sz * z)%Z by lia. rewrite -Hz.
      have ? : (idx ≤ Z.of_nat cnt)%Z by subst idx; apply Zrem_le; lia.
      have ? : (0 ≤ Z.of_nat sz + (Z.of_nat cnt - idx))%Z by lia.
      have ? : (0 ≤ Z.of_nat sz)%Z by lia.
      destruct (Z.of_nat sz), (Z.of_nat cnt), idx; try done; try lia. }
    have EQ : (Z.of_nat sz `quot` Z.of_nat sz = 1)%Z.
    { have ? : (1 ≤ Z.of_nat sz `quot` Z.of_nat sz)%Z by apply Zquot_le_lower_bound; lia.
      have ? : (Z.of_nat sz `quot` Z.of_nat sz ≤ 1)%Z; [apply Zquot_le_upper_bound; lia|lia]. }
    rewrite EQ -TurnEQ Hz. clear EQ.
    replace (Z.of_nat sz * z + (Z.of_nat sz - 1))%Z with ((Z.of_nat sz - 1) + z * Z.of_nat sz)%Z by lia.
    rewrite Z_quot_plus; try lia; last first.
    { replace (z * Z.of_nat sz)%Z with (Z.of_nat sz * z)%Z by lia. rewrite -Hz.
      have ? : (idx ≤ Z.of_nat cnt)%Z by subst idx; apply Zrem_le; lia.
      have ? : (0 ≤ Z.of_nat sz - 1 + (Z.of_nat cnt - idx))%Z by lia.
      have ? : (0 ≤ Z.of_nat sz - 1)%Z by lia.
      destruct (Z.of_nat sz - 1)%Z, (Z.of_nat cnt - idx + (Z.of_nat cnt - idx))%Z; try lia. }
    have EQ : ((Z.of_nat sz - 1) `quot` Z.of_nat sz = 0)%Z; [|rewrite EQ; lia].
    have ? : (0 ≤ (Z.of_nat sz - 1) `quot` Z.of_nat sz)%Z by lia.
    have ? : ((Z.of_nat sz - 1) `quot` Z.of_nat sz < 1)%Z; [apply Zquot_lt_upper_bound; lia|lia]. }

  have ValSame : ∀ (n : nat), n ≠ Z.to_nat idx → (n < sz)%Z →
    ((Z.of_nat cnt + Z.of_nat sz - Z.of_nat n - 1) `quot` (Z.of_nat sz) = (Z.of_nat (cnt + 1) + Z.of_nat sz - Z.of_nat n - 1) `quot` (Z.of_nat sz))%Z.
  { intros. replace (Z.of_nat (cnt + 1) + Z.of_nat sz - Z.of_nat n - 1)%Z with (Z.of_nat cnt + Z.of_nat sz - Z.of_nat n)%Z by lia.
    set x := (Z.of_nat cnt + Z.of_nat sz - Z.of_nat n)%Z.
    have GE : (1 ≤ x)%Z by lia.
    have ? : ((x - 1) `quot` (Z.of_nat sz) ≤ x `quot` (Z.of_nat sz))%Z by apply Zquot_le_lower_bound; lia.
    have ? : (x `quot` (Z.of_nat sz) ≤ (x - 1) `quot` (Z.of_nat sz))%Z; [|lia].

    rewrite {2}(Z.quot_rem' x (Z.of_nat sz)).
    specialize (Zrem_lt_pos_pos x (Z.of_nat sz)) as LT.
    have LTcond1 : (0 ≤ x)%Z by lia.
    have LTcond2 : (0 < Z.of_nat sz)%Z by lia.
    specialize (Zrem_lt_pos_pos x (Z.of_nat sz) LTcond1 LTcond2) as Hx.
    have NEQx : (x `rem` Z.of_nat sz ≠ 0)%Z.
    { unfold not. intros. apply Zrem_divides in H1. destruct H1 as [c Hc]. subst x.
      have EQ : (Z.of_nat n = Z.of_nat cnt + Z.of_nat sz - Z.of_nat sz * c)%Z by lia.
      have EQ' : (Z.of_nat n `rem` Z.of_nat sz = (Z.of_nat cnt + Z.of_nat sz - Z.of_nat sz * c) `rem` Z.of_nat sz)%Z by rewrite EQ.
      replace (Z.of_nat cnt + Z.of_nat sz - Z.of_nat sz * c)%Z with (Z.of_nat cnt + (1 - c) * Z.of_nat sz)%Z in EQ' by lia.
      rewrite Z_rem_plus in EQ'; last first.
      { replace (Z.of_nat cnt + (1 - c) * Z.of_nat sz)%Z with (Z.of_nat cnt + Z.of_nat sz - Z.of_nat sz * c)%Z by lia.
        rewrite -Hc. lia. }
      have EQ'' : (Z.of_nat n = Z.of_nat n `rem` Z.of_nat sz)%Z; [|rewrite -EQ'' in EQ'; clear EQ''].
      { rewrite {1}(Z.quot_rem' (Z.of_nat n) (Z.of_nat sz)).
        replace (Z.of_nat n `quot` Z.of_nat sz)%Z with 0%Z; [lia|].
        have ? : (0 ≤ Z.of_nat n `quot` Z.of_nat sz)%Z by apply Zquot_le_lower_bound; lia.
        have ? : (Z.of_nat n `quot` Z.of_nat sz < 1)%Z; [by apply Zquot_lt_upper_bound; lia|lia]. }
      subst idx. rewrite -EQ' in H. clear -H. lia. }
    replace (Z.of_nat sz * (x `quot` Z.of_nat sz) + x `rem` Z.of_nat sz - 1)%Z
      with ((x `quot` Z.of_nat sz) * Z.of_nat sz + (x `rem` Z.of_nat sz - 1))%Z by lia.
    have LE1 : (1 ≤ x `rem` Z.of_nat sz)%Z by lia.
    rewrite Z_quot_plus_l; try lia; last first.
    { have H1 : (0 ≤ x `rem` Z.of_nat sz - 1)%Z by lia.
      have H2 : (0 ≤ x `quot` Z.of_nat sz * Z.of_nat sz + (x `rem` Z.of_nat sz - 1))%Z by lia. clear -H1 H2.
      destruct (x `quot` Z.of_nat sz * Z.of_nat sz + (x `rem` Z.of_nat sz - 1))%Z, (x `rem` Z.of_nat sz - 1)%Z; lia. }
    have LE : (0 ≤ (x `rem` Z.of_nat sz - 1) `quot` Z.of_nat sz)%Z by apply Zquot_le_lower_bound; lia. lia. }

  iDestruct (SeqPerm_Split _ _ _ _ _ (λ m, m =? Z.to_nat turn) with "Perm") as "[Perm Perm']".
  iDestruct (SeqPerm_Equiv _ _ _ _ _ (λ m, m =? Z.to_nat turn) with "Perm") as "Perm".
  { intros. simpl. destruct (n =? Z.to_nat turn) eqn:Heq; [|by rewrite andb_comm].
    rewrite andb_comm /=. apply leb_correct. rewrite Nat.eqb_eq in Heq. subst n. done. }
  iDestruct (SeqPerm_Equiv _ _ _ _ _ (λ m, Z.to_nat (turn + 1) <=? m) with "Perm'") as "Perm'".
  { intros. simpl. destruct (n =? Z.to_nat turn) eqn:Heq; rewrite andb_comm /=; symmetry.
    - apply leb_iff_conv. rewrite Nat.eqb_eq in Heq. subst n. lia.
    - rewrite Nat.eqb_neq in Heq. destruct (Z.to_nat turn <=? n) eqn:Hn.
      + apply leb_complete in Hn. apply leb_correct. lia.
      + rewrite leb_iff_conv in Hn. rewrite leb_iff_conv. lia. }

  iFrame "Perm". iSplitL; [|done].
  rewrite (big_sepL_take_drop _ seqs (S (Z.to_nat idx))). iSplitR "Perms'".
  - rewrite (take_S_r _ _ (γseq,γseqs,sloc)); [|done]. rewrite big_sepL_snoc. iSplitR "Perm'".
    + iApply (big_sepL_impl with "Perms []"). iIntros "!> %%% (%&%&%&%& H)". rewrite ValSame; last first.
      { apply lookup_lt_Some in H. rewrite take_length in H. lia. }
      { unfold not. intros. subst k. apply lookup_lt_Some in H. rewrite take_length in H. lia. }
      repeat iExists _. iFrame "H". done.
    + repeat iExists _. rewrite -NextTurnEQ take_length Nat.min_l; [|lia].
      replace (Z.of_nat (Z.to_nat idx)) with idx by lia. iFrame "Perm'". done.
  - iApply (big_sepL_impl with "Perms' []"). iIntros "!> %%% (%&%&%&%& H)". rewrite ValSame; [|lia|]; last first.
    { apply lookup_lt_Some in H. rewrite drop_length in H. lia. }
    repeat iExists _. iFrame "H". done.
Qed.

Lemma perm_bank_insert seqs sz ty γseq γseqs sloc :
  (length seqs < sz)%nat →
  perm_bank seqs sz 0 ty -∗ SeqPerm seq γseq sloc ty (λ _ : nat, true) -∗ perm_bank (seqs ++ [(γseq,γseqs,sloc)]) sz 0 ty.
Proof.
  iIntros "%LT Perms Perm".
  rewrite /perm_bank big_sepL_snoc. iFrame "Perms". repeat iExists _. iSplitR; [done|].
  iApply (SeqPerm_Equiv with "Perm"). intros. symmetry. apply leb_correct.
  replace ((Z.of_nat 0 + Z.of_nat sz - Z.of_nat (length seqs) - 1) `quot` Z.of_nat sz)%Z with 0%Z; [lia|].
  replace (Z.of_nat 0 + Z.of_nat sz - Z.of_nat (length seqs) - 1)%Z with (Z.of_nat sz - (Z.of_nat (length seqs) + 1))%Z; try lia.
  have ? : (0 ≤ (Z.of_nat sz - (Z.of_nat (length seqs) + 1)) `quot` Z.of_nat sz)%Z by apply Zquot_le_lower_bound; lia.
  have ? : ((Z.of_nat sz - (Z.of_nat (length seqs) + 1)) `quot` Z.of_nat sz < 1)%Z by apply Zquot_lt_upper_bound; lia. lia.
Qed.

Lemma field_info_dup γg q seqs sz :
  field_info γg q seqs sz -∗ field_info γg q seqs sz ∗ field_info γg q seqs sz.
Proof.
  iDestruct 1 as (??) "[#e0✓eV0 ([q↦ q↦'] & BIG)]".
  iAssert (@{eV0.(sync)} (([∗ list] idx↦x ∈ seqs, (q >> (idx + 3)) ↦{qp/2} #(LitLoc x.2)) ∗
    ([∗ list] idx↦x ∈ seqs, (q >> (idx + 3)) ↦{qp/2} #(LitLoc x.2))))%I with "[BIG]" as "[BIG BIG']".
  { iApply (view_at_mono with "BIG"); [done|]. iIntros "BIG". rewrite -big_sepL_sep. iApply (big_sepL_impl with "BIG").
    iIntros "%idx %x %Lookup !> [q↦ q↦']". iFrame "q↦ q↦'". }
  iSplitL "q↦ BIG"; iExists _,_; iFrame "∗#%".
Qed.

Lemma new_queue_spec :
  new_queue_spec' (newQueue newSEQ) QueueLocal QueueInv.
Proof.
  iIntros (N tid sz NZSZ Φ) "_ Post".
  wp_lam. wp_op. wp_apply wp_new; [done|lia|done|].
  iIntros (q) "([_|%] & q↦ & Hmq)"; [|lia]. wp_let. wp_op.
  replace (Z.to_nat (sz + 3)) with (3 + sz)%nat by lia. rewrite repeat_app !own_loc_na_vec_cons shift_0.
  iDestruct "q↦" as "(q0↦ & q1↦ & q2↦ & q↦)". iDestruct "Hmq" as "[Hmq _]". rewrite shift_0.
  wp_write. wp_op. rewrite -[Z.to_nat 1]/(1%nat). wp_write. wp_op. rewrite -[Z.to_nat 2]/(2%nat).
  rewrite !shift_nat_assoc /=. wp_write. wp_op. rewrite -[Z.to_nat 3]/(3%nat).

  iMod (append_only_loc_cas_only_from_na with "q0↦") as (γl0 γsl0 V0 eVl0) "(#⊒V0 & Ml0● & #⊒Ml0 & omol0↦ & WCOMMIT & #el0✓eVl0 & [%eVl0EV _])"; [done|].
  iMod (append_only_loc_cas_only_from_na_rel with "⊒V0 q1↦") as (γl1 γsl1 V1 eVl1)
    "(#⊒V1 & Ml1● & [#⊒Ml1 #⊒V1@V0] & omol1↦ & _ & #el1✓eVl1 & [%eVl1EV _])"; [done|].
  (* iMod (append_only_loc_cas_only_from_na_rel with "⊒V1 q2↦") as (γl2 γsl2 V2 eVl2)
    "(#⊒V2 & Ml2● & [#⊒Ml2 #⊒V2@V1] & omol2↦ & _ & #el2✓eVl2 & [%eVl2EV _])"; [done|]. *)

  set aols := [(γl0,γsl0); (γl1,γsl1)].
  set seqs : list (gname * gname * loc) := [].
  set nodes : queue_state := [].
  set hlist : list gname := [].

  iMod (mono_list_own_alloc nodes) as (γn) "[Hγn #Hγn◯]".
  iMod (mono_list_own_alloc hlist) as (γh) "[Hγh #Hγh◯]".

  iAssert (ticket_info q aols 0 0)%I with "[omol0↦ Ml0●]" as "Tenq".
  { repeat iExists _. iFrame "Ml0●". iSplitR; [done|]. iSplitL.
    - iDestruct (view_at_intro with "omol0↦") as (?) "[_ omol0↦]". iExists _. rewrite shift_0. iFrame.
    - rewrite big_sepL_singleton. iExists _. iFrame "el0✓eVl0". rewrite eVl0EV. done. }
  iAssert (ticket_info q aols 1 0)%I with "[omol1↦ Ml1●]" as "Tdeq".
  { repeat iExists _. iFrame "Ml1●". iSplitR; [done|]. iSplitL.
    - iDestruct (view_at_intro with "omol1↦") as (?) "[_ omol1↦]". iExists _. iFrame.
    - rewrite big_sepL_singleton. iExists _. iFrame "el1✓eVl1". rewrite eVl1EV. done. }
  iAssert (field_info_inner 1%Qp q seqs sz)%I with "[q2↦]" as "Field"; [by iFrame "q2↦"|].
  (* NOTE: we deliberately put [meta_token] to prevent [SF] being recognized as persistent. Same for [Penq], [Pdeq] *)
  iAssert (slot_field γn seqs sz ∗ meta_token q ⊤)%I with "[$Hmq]" as "[SF Hmq]"; [by rewrite /slot_field|].
  iAssert (perm_bank seqs sz 0 EnqP ∗ meta_token q ⊤)%I with "[$Hmq]" as "[Penq Hmq]"; [rewrite /perm_bank;done|].
  iAssert (perm_bank seqs sz 0 DeqP ∗ meta_token q ⊤)%I with "[$Hmq]" as "[Pdeq Hmq]"; [rewrite /perm_bank;done|].
  iAssert (∃ V, @{V} (([∗ list] x ∈ aols, ∃ γl γsl Ml, OmoEview γl Ml ∗ ⌜ x = (γl, γsl)⌝) ∗
    ([∗ list] x ∈ seqs, ∃ γseq γseqs sloc Mseq, SeqLocal seq (seqN N) γseq sloc Mseq ∗ ⌜ x = (γseq, γseqs, sloc) ⌝)) ∗ ⊒V ∗ ⌜ V0 ⊑ V ⌝)%I
      with "[]" as "⊒AOLSEQ".
  { iAssert (⌜ V0 ⊑ V1 ⌝)%I with "[]" as %LeV0V1.
    { rewrite !view_at_unfold !monPred_at_in. by iDestruct "⊒V1@V0" as %?. }
    iExists V1. subst aols. repeat iSplit; [..|by rewrite big_sepL_nil|by rewrite big_sepL_nil|iFrame "#"|iPureIntro;solve_lat].
    - iExists γl0,γsl0,{[0]}. by iFrame "#".
    - iExists γl1,γsl1,{[0]}. by iFrame "#". }

  have [i [Hi [Hi' Hi'']]] : ∃ i, i ≤ sz ∧ Lit 0%Z = #i ∧ i = 0 by exists 0; split_and!; [lia|done|done].
  subst aols seqs.
  have [aols [Haols LENaols]] : ∃ aols, aols = [(γl0,γsl0); (γl1,γsl1)] ∧ (length aols = 2)%nat.
  { eexists. split; [done|]. simpl. lia. }
  have [seqs [Hseqs LENseqs]] : ∃ seqs : list (gname * gname * loc), seqs = [] ∧ (length seqs = i)%nat.
  { eexists. split; [done|]. simpl. lia. }
  rewrite Hi' -!Haols -!Hseqs. clear Hi' Haols Hseqs.
  iAssert ((q >> (3 + i)) ↦∗ repeat #☠ (sz - i))%I with "[q↦]" as "q↦".
  { subst i. rewrite Nat.add_0_r Nat.sub_0_r. iFrame "q↦". }
  clear Hi''. iLöb as "IH" forall (i aols seqs Hi LENaols LENseqs) "⊒AOLSEQ Tenq Tdeq SF Pdeq Penq".

  wp_lam. wp_op. destruct (decide (i = sz)) as [->|NEQ]; last first.
  { rewrite bool_decide_false; [|lia]. wp_if.
    replace (sz - i) with (1 + (sz - i - 1)) by lia.
    rewrite repeat_app own_loc_na_vec_cons. iDestruct "q↦" as "[q↦ q↦']".
    wp_op. rewrite !shift_nat_assoc. replace (Z.to_nat (Z.of_nat i)) with i by lia.
    iDestruct "⊒AOLSEQ" as (V) "([⊒AOLs@V ⊒SEQs@V] & ⊒V & %LeV0V)".
    wp_apply (new_seq_spec with "⊒V").
    iIntros (γseq γseqs sloc Mseq V') "(#⊒V' & #⊒Mseq & Mseq● & _ & EnqPerm & DeqPerm & %LeVV')".
    wp_write. wp_op. replace (Z.of_nat i + 1)%Z with (Z.of_nat (i + 1)) by lia.
    replace (sz - i - 1) with (sz - (i + 1)) by lia.

    set seqs' := seqs ++ [(γseq,γseqs,sloc)].
    iApply ("IH" $! (i + 1) aols seqs'
      with "[] [] [] Post WCOMMIT Hγn Hγh [Field q↦] Hmq q↦' [] [Tenq] [Tdeq] [SF Mseq●] [Pdeq DeqPerm] [Penq EnqPerm]"); try done.
    - iPureIntro. lia.
    - iPureIntro. subst seqs'. rewrite app_length /=. lia.
    - iDestruct "Field" as "[q↦2 BIG]". iFrame "q↦2". subst seqs'. rewrite big_sepL_snoc. iFrame "BIG".
      replace (S (S (S i))) with (length seqs + 3) by lia. iFrame "q↦".
    - iModIntro. iExists V'. subst seqs'. rewrite !big_sepL_snoc. iFrame "⊒AOLs@V ⊒SEQs@V ⊒V'". iSplit; [|solve_lat].
      iExists γseq,γseqs,sloc,Mseq. iFrame "⊒Mseq". done.
    - rewrite /slot_field big_sepL_snoc. iFrame "SF". iExists γseq,γseqs,sloc. iSplit; [done|]. repeat iExists _. iFrame "Mseq●". iSplit; [done|]. done.
    - iApply (perm_bank_insert with "Pdeq DeqPerm"). lia.
    - iApply (perm_bank_insert with "Penq EnqPerm"). lia. }

  iDestruct "⊒AOLSEQ" as (V) "([⊒AOLs@V ⊒SEQs@V] & ⊒V & %LeV0V)".
  iDestruct (view_at_intro_incl with "Field ⊒V") as (V') "(#⊒V' & %LeVV' & Field)".
  have LeEmpV' : ∅ ⊑ V' by done.
  set M := {[0%nat]}.
  set eVinit := mkOmoEvent Init V' M.

  iMod (@OmoAuth_alloc _ _ _ _ _ eVinit [] _ _ queue_interpretable with "WCOMMIT") as (γg γs) "(M● & #⊒M & _ & #e0✓eVinit & _)".
  { by apply queue_step_Init. } { done. }
  iDestruct (OmoHbToken_finish with "M●") as "[M● M●']".
  iDestruct (OmoSnapHistory_get with "M●") as "#E◯".

  iAssert (field_info γg q seqs sz)%I with "[Field]" as "Field"; [by repeat iExists _; iFrame "e0✓eVinit Field"|].
  iAssert (helping_info N γg γn q 0 hlist)%I with "[]" as "Helping".
  { rewrite /helping_info take_ge; [|done]. rewrite drop_ge; [|done]. by rewrite !big_sepL_nil. }
  iAssert (nodes_info γg [])%I with "[]" as "Nodes"; [rewrite /nodes_info;done|].

  rewrite bool_decide_true; [|done]. wp_if. iClear "IH".
  iMod (meta_set _ _ (γs,γn,γh,aols,seqs,sz) nroot with "Hmq") as "#HM"; [done|].
  iMod (inv_alloc (mpmcqN N) _ (InternalInv_inner N γg q)  with "[-M●' Post]") as "#I".
  { iExists _. repeat iExists _. iFrame "HM M● Hγn Hγh Tenq Tdeq SF Penq Pdeq Helping Nodes Field".
    iPureIntro. split_and!; try done. lia. }
  wp_pures. iApply ("Post" $! γg q V' [eVinit] {[0]}). iFrame "⊒V'". iSplitR; last iSplit.
  - iFrame "I E◯". repeat iExists _. iFrame "HM ⊒AOLs@V ⊒SEQs@V ⊒M". iExists eVinit. iFrame "e0✓eVinit". done.
  - repeat iExists _. iFrame "M●'".
  - iPureIntro. done.
Qed.

(* TODO: Probably we need LAT spec of FAA. Condition: uf = ∅ ∧ last msg = number *)
Lemma enqueue_spec :
  enqueue_spec' (enqueue enqueueWithTicket) QueueLocal QueueInv.
Proof.
  intros N DISJ q tid γg E0 M V0 v NZ. iIntros "#⊒V0 #QueueLocal" (Φ) "AU".
  iDestruct "QueueLocal" as "(Inner & QInv & E◯0)".
  iDestruct "Inner" as (??????) "(HM & ⊒M & ⊒AOLs & ⊒SEQs & ⊒eV0)".
  iCombine "⊒M ⊒AOLs ⊒SEQs ⊒eV0" as "⊒MAOLSEQ".
  iDestruct (view_at_intro_incl with "⊒MAOLSEQ ⊒V0") as (V0') "(⊒V0' & %LeV0V0' & (⊒M@V0' & ⊒AOLs@V0' & ⊒SEQs@V0' & ⊒eV0@V0'))".

  wp_lam. wp_op. rewrite -[Z.to_nat 0]/(0%nat).
  iLöb as "IH". wp_lam. wp_bind (!ʳˡˣ _)%E.

  (* Inv access 1 *)
  iInv "QInv" as (E1) "H" "Hclose".
  iDestruct "H" as (?????? enqcnt1 deqcnt1 omo1 stlist1) "(%nodes1 & %hlist1 & >HM' & >M●1 & >NL●1 & >HL●1 & >Tenq1 & H)".
  simplify_meta with "HM' HM". iClear "HM'".
  iDestruct "Tenq1" as (γl1 γsl1 El1 omol1 mol1) "((%AOLs0 & %EQenqcnt1 & %NZomol1) & Ml1● & [%Vb1 omol1↦] & #MSG1)".
  iDestruct (big_sepL_lookup with "⊒AOLs") as (?? Ml1) "[⊒Ml1 %EQ]"; [exact AOLs0|]. inversion EQ. subst γl γsl. clear EQ.

  wp_apply (append_only_loc_relaxed_read with "[$Ml1● $⊒Ml1 $omol1↦ $⊒V0']"); [solve_ndisj|].
  iIntros (el1 genl1 vl1 Vl1 V1 eVl1 eVln1)
    "(Pures & Ml1● & _ & _ & #el1✓eVl1 & _ & _ & #⊒V1 & _ & #⊒Ml1'@V1 & omol1↦)".
  iDestruct "Pures" as %(Eqgenl1 & eVl1EV & LEV0'V1 & eVln1EV & eVln1SYNC).
  iDestruct (big_sepL_lookup with "MSG1") as (eVl1') "[el1✓eVl1' %eVl1'EV]"; [exact Eqgenl1|].
  iDestruct (OmoEinfo_agree with "el1✓eVl1 el1✓eVl1'") as %<-. iClear "el1✓eVl1'".
  rewrite eVl1EV /= in eVl1'EV. subst vl1.

  iMod ("Hclose" with "[M●1 NL●1 HL●1 H Ml1● omol1↦]") as "_".
  { iExists E1. do 6 (iExists _). iExists enqcnt1, deqcnt1, omo1, stlist1, nodes1, hlist1.
    iFrame "M●1 NL●1 HL●1 HM H". repeat iExists _. iFrame "Ml1●". rewrite omo_insert_r_write_op. iFrame "MSG1".
    iSplitR; [|eauto with iFrame]. rewrite omo_insert_r_length. done. }

  iModIntro. wp_pures. wp_bind (casʳˡˣ(_, _, _))%E.

  (* Inv access 2 *)
  iInv "QInv" as (E2) "H" "Hclose".
  iDestruct "H" as (?????? enqcnt2 deqcnt2 omo2 stlist2) "(%nodes2 & %hlist2 & >HM' & >M●2 & >NL●2 & >HL●2 & >Tenq2 & H)".
  simplify_meta with "HM' HM". iClear "HM'".
  iDestruct "Tenq2" as (γl2 γsl2 El2 omol2 mol2) "((%AOLs0' & %EQenqcnt2 & %NZomol2) & Ml2● & [%Vb2 omol2↦] & #MSG2)".
  rewrite AOLs0 in AOLs0'. inversion AOLs0'. subst γl2 γsl1. clear AOLs0'.

  iMod (rel_objectively_intro (⊒∅) tid with "[]") as "⊒∅".
  { iApply objective_objectively. iApply monPred_in_bot. }

  wp_apply (append_only_loc_cas_only_cas _ _ _ _ _ _ _ ∅ _ _ _ (LitInt genl1) (genl1 + 1)%Z _ ∅
    with "[$Ml2● $⊒Ml1 $omol2↦ $⊒V1 ⊒∅]"); try done; [solve_ndisj|].
  iIntros (b2 el2 genl2 vl2 Vl2 V2 mol2' omol2' eVl2 eVln2)
    "(Pures & _ & #el2✓eVl2 & #eln2✓eVln2 & Ml2● & #⊒V2 & #⊒Ml2@V3 & omol2↦ & CASE)".
  iDestruct "Pures" as %(Eqgenl2 & eVl2EV & LeV1V2).
  iDestruct "CASE" as "[(Pures & _) | [Pures sVw2]]".
  { (* CAS in FAA failed, retry FAA *)
    iDestruct "Pures" as %(-> & NEq & -> & Homol2 & eVln2EV & eVln2SYNC).
    iMod ("Hclose" with "[-AU]") as "_".
    { iExists E2. do 6 (iExists _). iExists enqcnt2, deqcnt2, omo2, stlist2, nodes2, hlist2.
      iFrame "M●2 NL●2 HL●2 HM H". repeat iExists _. iFrame "Ml2●". subst omol2'. rewrite omo_insert_r_write_op. iFrame "MSG2".
      iSplitR; [|eauto with iFrame]. rewrite omo_insert_r_length. done. }
    iModIntro. wp_if. iApply ("IH" with "AU"). }

  (* CAS in FAA succeed, commit point *)
  iDestruct "Pures" as %(-> & -> & ->).
  iDestruct "sVw2" as (Vw2 (Eqmol2 & Homol2 & eVln2EV & eVln2SYNC & LeVl2Vw3 & NEqVl2Vw2 & NLeV2Vl2 & NEqV1V2 & LeEmpVw2))
    "(_ & _ & WCOMMIT)".
  iClear "IH". iDestruct "H" as
    "(Tdeq2 & Field2 & Slot2 & Penq2 & Pdeq2 & Helping2 & #Hnodes2 & (%LASTst2 & %LENnodes2 & %LENhlist2 & %LENseqs & %LENaols & %NZsz))".
  iDestruct (field_info_dup with "Field2") as "[Field2 Field2']".

  have LeV0V2 : V0 ⊑ V2 by solve_lat.
  set enqId := length E2.
  set M' := {[enqId]} ∪ M.
  set eVenq := mkOmoEvent (Enq v) V2 M'.
  set E2' := E2 ++ [eVenq].
  set enqst : queue_state := (drop deqcnt2 nodes2) ++ [(enqId, v, eVenq.(sync), eVenq.(eview))].

  iMod "AU" as (E2'') "[>QInv' [_ Commit]]".
  iDestruct "QInv'" as (???) "M●2'".
  iDestruct (OmoAuth_agree with "M●2 M●2'") as %(<- & <- & <- & <-).
  iCombine "M●2 M●2'" as "M●2".

  iDestruct (view_at_mono_2 _ V2 with "⊒M@V0'") as "⊒M@V2"; [solve_lat|].
  iMod (OmoAuth_insert_last with "M●2 ⊒M@V2 WCOMMIT []") as "(M●2 & #⊒M'@V2 & #enqId↦eln2 & #enqId✓eVenq & #enqId↪enqst & _)".
  { have ? : step enqId eVenq (drop deqcnt2 nodes2) enqst by apply queue_step_Enq; try done; subst eVenq M'; set_solver-.
    iPureIntro. by split_and!. }
  iDestruct (OmoHbToken_finish with "M●2") as "M●2".
  iDestruct (OmoSnapHistory_get with "M●2") as "#E◯2'".

  iDestruct "M●2" as "[M●2 M●2']".
  iMod ("Commit" $! V2 E2' M' with "[M●2']") as "HΦ".
  { iFrame "⊒V2". iSplitL; last iSplit; [repeat iExists _; iFrame|..].
    - iFrame "QInv E◯2'". repeat iExists _. iFrame "HM ⊒M'@V2 ⊒AOLs@V0' ⊒SEQs@V0' ⊒eV0@V0'".
    - iPureIntro. split_and!; try done. subst M'. set_solver-. }

  iAssert (⌜ genl1 = enqcnt2 ⌝)%I with "[-]" as %->.
  { iDestruct (big_sepL_lookup with "MSG2") as (eVl2') "[el2✓eVl2' %eVl2'EV]"; [exact Eqgenl2|].
    iDestruct (OmoEinfo_agree with "el2✓eVl2 el2✓eVl2'") as %<-.
    rewrite eVl2EV /= in eVl2'EV. inversion eVl2'EV. iPureIntro. lia. }

  set turn := (enqcnt2 `quot` sz).
  set idx := (enqcnt2 `rem` sz).
  set nodes2' := nodes2 ++ [(enqId, v, eVenq.(sync), eVenq.(eview))].
  iMod (mono_list_auth_own_update nodes2' with "NL●2") as "[NL●2' #NL◯2']"; [by subst nodes2'; apply prefix_app_r|].

  iDestruct (extract_one_ticket with "Penq2") as (???) "(Penq2 & Perm & %Hidx)"; [done|done|].

  iAssert (|={_}=> ∃ E2'' omo2'' stlist2'',
    helping_info N γg γn q (enqcnt2 + 1)%nat hlist2 ∗
    OmoAuth γg γs (1/2) E2'' omo2'' stlist2'' _ ∗
    ⌜ last stlist2'' = Some (drop deqcnt2 nodes2') ⌝)%I with "[Helping2 M●2]" as ">Helping2".
  { destruct (le_lt_dec deqcnt2 enqcnt2) as [LE|LT].
    { iDestruct "Helping2" as "[Done _]". iModIntro.
      rewrite take_ge; [|rewrite LENhlist2; lia].
      rewrite /helping_info take_ge; [|rewrite LENhlist2; lia].
      rewrite drop_ge; [|rewrite LENhlist2; lia].
      repeat iExists _. iFrame "Done M●2". iSplit; [done|]. iPureIntro. rewrite last_app /=.
      subst enqst nodes2'. rewrite drop_app_le; [|lia]. done. }
    iDestruct "Helping2" as "[Done Pending]".
    rewrite /helping_info.
    replace (enqcnt2 + 1)%nat with (S enqcnt2) by lia.
    have [γi Lookup] : is_Some (hlist2 !! enqcnt2) by rewrite lookup_lt_is_Some; lia.
    rewrite (take_S_r _ _ γi); [|done].
    rewrite (drop_S _ γi); [|done].
    iDestruct "Pending" as "[(%&%&%&%&%&%&%& %LeViVb & Hγi & WCOMMIT & [AU #⊒M0] & #HInv) Pending']".
    rewrite Nat.add_0_r.
    iInv "HInv" as (?) "[>Hγi' _]" "HInvClose".
    iCombine "Hγi Hγi'" as "Hγi". clear hst.

    iAssert (|={_}=> @{Vb ⊔ V2} (▷ Q v ∗ ⎡ghost_var γi 1 Accepted⎤ ∗
      (∃ E2'' omo2'' stlist2'', OmoAuth γg γs (1/2) E2'' omo2'' stlist2'' _ ∗
        ⌜ last stlist2'' = Some (drop deqcnt2 nodes2') ⌝)))%I with "[AU Hγi WCOMMIT M●2]" as ">(HQ & [Hγi Hγi'] & (%&%&%& M● & %LAST))".
    { rewrite -view_at_fupd.
      iDestruct (view_at_mono_2 _ (Vb ⊔ V2) with "AU") as "AU"; [solve_lat|].
      iCombine "Hγi WCOMMIT M●2" as "RES".
      iDestruct (view_at_objective_iff _ (Vb ⊔ V2) with "RES") as "RES".
      iAssert (@{Vb ⊔ V2} QueueLocal_inner N γg q ({[enqId]} ∪ eVenq.(eview) ∪ M0))%I with "[-]" as "#⊒M0'".
      { iDestruct "⊒M0" as (??????) "(H1 & H2 & H3 & H4)". repeat iExists _. iFrame "H1 H3 H4".
        iDestruct (view_at_mono_2 _ (Vb ⊔ V2) with "H2") as "H2'"; [solve_lat|].
        iDestruct (OmoEview_insert_new_obj with "H2' enqId✓eVenq") as "H2''"; [solve_lat|iFrame "H2''"]. }
      iDestruct (view_at_view_at _ (Vb ⊔ V2) with "⊒M0'") as "⊒M0''".
      iAssert (@{Vb ⊔ V2} ⊒(Vb ⊔ V2))%I as "⊒V". { by iPureIntro. }
      iCombine "AU RES ⊒M0'' ⊒V" as "RES".
      iApply (view_at_mono with "RES"); [done|].
      iIntros "(AU & (Hγi & WCOMMIT & M●) & #⊒M & #⊒V)".
      iMod "AU" as (E) "[>(%&%&%& M●') [_ Commit]]".
      iDestruct (OmoAuth_agree with "M● M●'") as %(<- & -> & -> & <-).
      iCombine "M● M●'" as "M●".
      iDestruct "⊒M" as (??????) "(H1 & ⊒M & H3 & H4)".

      have LeViV : Vi ⊑ Vb ⊔ V2 by solve_lat.
      set deqId := length E.
      set M0' := (({[enqId]} ∪ eVenq.(eview)) ⊔ M0).
      set M0'' := {[deqId]} ∪ M0'.
      set eVdeq := mkOmoEvent (Deq v) (Vb ⊔ V2) M0''.
      set E' := E ++ [eVdeq].

      iMod (OmoAuth_insert_last with "M● ⊒M WCOMMIT []") as "(M● & #⊒M' & _)".
      { have ? : step deqId eVdeq enqst (drop deqcnt2 nodes2).
        { subst enqst. rewrite drop_ge; [|lia]. simpl. apply queue_step_Deq; try done; [solve_lat|set_solver-]. }
        iPureIntro. split_and!; try done. by rewrite last_app. }
      iDestruct (OmoHbToken_finish with "M●") as "M●".
      iDestruct (OmoSnapHistory_get with "M●") as "#E◯".
      iDestruct "M●" as "[M● M●']".
      iMod (ghost_var_update Accepted with "Hγi") as "Hγi".

      iMod ("Commit" $! v (Vb ⊔ V2) E' M0'' with "[M●']") as "HΦ".
      { iFrame "E◯ ⊒V". iSplitL "M●'"; last iSplit.
        - repeat iExists _. iFrame "M●'".
        - repeat iExists _. iFrame "H1 H3 H4 ⊒M'".
        - iPureIntro. split_and!; try done. set_solver-. }
      iModIntro. iFrame "HΦ Hγi". repeat iExists _. iFrame "M●". iPureIntro.
      rewrite last_app /=. rewrite drop_ge; [|lia]. rewrite drop_ge; [done|].
      subst nodes2'. rewrite app_length /=. lia. }

    iMod ("HInvClose" with "[HQ Hγi]") as "_".
    { repeat iExists _. iFrame.
      iDestruct (mono_list_idx_own_get enqcnt2 with "NL◯2'") as "IDX".
      { subst nodes2'. by rewrite -LENnodes2 lookup_app_1_eq. }
      repeat iExists _. iFrame "IDX". iModIntro. done. }

    iModIntro. repeat iExists _. rewrite !view_at_objective_iff. iFrame "M●". iSplitL; [|done].
    iSplitL "Done Hγi'".
    - rewrite big_sepL_app. iFrame "Done". rewrite big_sepL_singleton. iExists _. by iFrame "Hγi'".
    - iApply (big_sepL_impl with "Pending' []"). iIntros "!> %%% (%&%&%&%&%&%&%&%& H)".
      replace (enqcnt2 + S k) with (S enqcnt2 + k) by lia. repeat iExists _. iFrame "H". done. }

  iMod ("Hclose" with "[-HΦ Perm Field2]") as "_".
  { iDestruct "Helping2" as (???) "(Helping2 & M● & %LAST)".
    iExists E2''. repeat iExists _. iFrame "HM M● NL●2' HL●2 Helping2 Field2' Slot2 Pdeq2 Tdeq2 Penq2 Hnodes2". iSplitL; last iSplit.
    - repeat iExists _. iFrame "Ml2●". iSplitR.
      + iPureIntro. subst omol2' enqcnt2. rewrite omo_append_w_length. split_and!; try done; lia.
      + iSplitL; [eauto with iFrame|]. iModIntro. subst omol2'. rewrite omo_append_w_write_op big_sepL_snoc. iFrame "MSG2".
        iExists eVln2. iFrame "eln2✓eVln2". iPureIntro. rewrite eVln2EV -omo_write_op_length. simpl. subst enqcnt2.
        have EQ : ((Z.of_nat (length omol2 - 1)) + 1)%Z = Z.of_nat (length omol2) by lia.
        rewrite EQ. done.
    - rewrite big_sepL_singleton. repeat iExists _. iFrame "enqId✓eVenq". iPureIntro. done.
    - iPureIntro. split_and!; try done. subst nodes2'. rewrite app_length /=. lia. }

  iDestruct "Field2" as (??) "[#e0✓eV0 [q↦sz BIGq]]". iDestruct "⊒eV0" as (?) "[e0✓eV0' ⊒eV0OUT]".
  iDestruct (OmoEinfo_agree with "e0✓eV0 e0✓eV0'") as %<-. iDestruct (view_at_elim with "⊒eV0OUT q↦sz") as "q↦sz".
  iAssert (@{eV0.(sync)} (q >> (Z.to_nat idx + 3)) ↦{qp} #(LitLoc sloc))%I with "[BIGq]" as "q↦sloc".
  { iApply (view_at_mono with "BIGq"); [done|]. iIntros "BIG". iDestruct (big_sepL_lookup with "BIG") as "H"; [done|]. done. }
  iDestruct (view_at_elim with "⊒eV0OUT q↦sloc") as "q↦sloc".

  iModIntro. wp_pures. rewrite -[Z.to_nat 2]/(2%nat).
  wp_read. wp_pures. rewrite -[Z.to_nat 3]/(3%nat) shift_nat_assoc.
  replace (3 + Z.to_nat (enqcnt2 `rem` sz)) with (Z.to_nat (enqcnt2 `rem` sz) + 3) by lia. wp_read.

  iDestruct (big_sepL_lookup with "⊒SEQs") as (??? Mseq2) "[⊒Mseq2 %]"; [exact Hidx|].
  inversion H. subst γseq0 γseqs0 sloc0. clear H.
  replace (Z.of_nat enqcnt2 `quot` Z.of_nat sz) with (Z.of_nat (Z.to_nat turn)); last first.
  { have ? : (0 ≤ enqcnt2 `quot` sz)%Z; [by apply Zquot_le_lower_bound; lia|lia]. }

  (* Inv access 3 *)
  have NDISJ' : (seqN N) ## histN by solve_ndisj.
  awp_apply (enqueueWithTicket_spec seq _ NDISJ' sloc tid γseq γseqs _ V2 v (Z.to_nat (enqcnt2 `quot` sz)) NZ with "⊒V2 ⊒Mseq2 [Perm]").
  { rewrite (_: Z.to_nat (Z.to_nat turn) = Z.to_nat turn); [done|lia]. }

  iInv "QInv" as (E3) "H".
  iDestruct "H" as (?????? enqcnt3 deqcnt3 omo3 stlist3)
    "(%nodes3 & %hlist3 & >HM' & >M●3 & >NL●3 & >HL●3 & >Tenq3 & >Tdeq3 & Field3 & Slot3 & Penq3 & Pdeq3 & Helping3 & #Hnodes3 & >Pures)".
  iDestruct "Pures" as %(LASTst3 & LENnodes3 & LENhlist3 & _).
  simplify_meta with "HM' HM". iClear "HM'".

  iDestruct (big_sepL_lookup_acc _ _ (Z.to_nat idx) with "Slot3") as "[H Slot3Close]"; [done|].
  iDestruct "H" as (???) "[>% Slot]". inversion H. subst γseq0 γseqs0 sloc0. clear H.
  iDestruct "Slot" as (Es3 omos3 sts3 stfs3) "(Ms3● & >%Hstfs3 & Hstfs3)".

  iAaccIntro with "Ms3●".
  { (* Peeking case *)
    iIntros "Ms3●". iModIntro. iFrame "HΦ q↦sz q↦sloc". iModIntro.
    iExists E3. repeat iExists _. iFrame "HM M●3 NL●3 HL●3 Tenq3 Tdeq3 Field3 Penq3 Pdeq3 Helping3 Hnodes3". iSplitL; last first.
    { iPureIntro. split_and!; try done. }
    iApply "Slot3Close". repeat iExists _. iSplit; [done|]. repeat iExists _. iFrame "Ms3● Hstfs3". done. }

  iIntros (V3 Mseq3) "(Ms3● & _ & #⊒V3 & #⊒Mseq3 & [%LeV2V3 %InclMseq2Mseq3])".
  iModIntro. iSplitR "HΦ"; last first. { iIntros "_". by iApply "HΦ". } iModIntro.

  iDestruct (SeqInv_OmoAuth_acc with "Ms3●") as (qp3) "[Ms3● Close]".
  iDestruct (OmoEinfo_get _ _ _ _ _ _ (length Es3) with "Ms3●") as "#es3✓eVs3"; [by rewrite lookup_app_1_eq|].
  iDestruct ("Close" with "Ms3●") as "Ms3●".

  iExists E3. repeat iExists _. iFrame "HM M●3 NL●3 HL●3 Tenq3 Tdeq3 Field3 Penq3 Pdeq3 Helping3 Hnodes3".
  iSplitL; last first. {iPureIntro. split_and!; try done. }
  iApply "Slot3Close". repeat iExists _. iSplit; [done|]. repeat iExists _. iFrame "Ms3●". iSplitR.
  { iPureIntro. rewrite last_app. done. }
  simpl. iDestruct (mono_list_idx_own_get enqcnt2 with "NL◯2'") as "IDX".
  { subst nodes2'. by rewrite -LENnodes2 lookup_app_1_eq. }
  replace (sz * Z.to_nat (enqcnt2 `quot` sz) + Z.to_nat idx) with enqcnt2; last first.
  { have EQ : (Z.of_nat enqcnt2 = Z.of_nat sz * turn + idx)%Z by lia.
    apply (f_equal Z.to_nat) in EQ.
    replace (Z.to_nat (Z.of_nat enqcnt2)) with enqcnt2 in EQ by lia. rewrite {1}EQ.
    replace (Z.to_nat (Z.of_nat sz * turn + idx)) with (Z.to_nat (Z.of_nat sz) * Z.to_nat (Z.of_nat enqcnt2 `quot` Z.of_nat sz) + Z.to_nat idx); [lia|].
    have ? : (0 ≤ turn)%Z; [|lia].
    subst turn. apply Zquot_le_lower_bound; try lia. }
  repeat iExists _. iFrame "IDX". iPureIntro. split_and!; try done.
Qed.

Lemma dequeue_spec :
  dequeue_spec' (dequeue dequeueWithTicket) QueueLocal QueueInv.
Proof.
  intros N DISJ q tid γg E0 M V0. iIntros "#⊒V0 #QueueLocal" (Φ) "AU".
  iDestruct "QueueLocal" as "(Inner & QInv & E◯0)".
  iDestruct "Inner" as (??????) "(HM & ⊒M & ⊒AOLs & ⊒SEQs & ⊒eV0)".
  iCombine "⊒M ⊒AOLs ⊒SEQs ⊒eV0" as "⊒MAOLSEQ".
  iDestruct (view_at_intro_incl with "⊒MAOLSEQ ⊒V0") as (V0') "(⊒V0' & %LeV0V0' & (⊒M@V0' & ⊒AOLs@V0' & ⊒SEQs@V0' & ⊒eV0@V0'))".

  wp_lam. wp_op. rewrite -[Z.to_nat 1]/(1%nat).
  iLöb as "IH". wp_lam. wp_bind (!ʳˡˣ _)%E.

  (* Inv access 1 *)
  iInv "QInv" as (E1) "H" "Hclose".
  iDestruct "H" as (?????? enqcnt1 deqcnt1 omo1 stlist1) "(%nodes1 & %hlist1 & >HM' & >M●1 & >NL●1 & >HL●1 & >Tenq1 & >Tdeq1 & H)".
  simplify_meta with "HM' HM". iClear "HM'".
  iDestruct "Tdeq1" as (γl1 γsl1 El1 omol1 mol1) "((%AOLs0 & %EQdeqcnt1 & %NZomol1) & Ml1● & [%Vb1 omol1↦] & #MSG1)".
  iDestruct (big_sepL_lookup with "⊒AOLs") as (?? Ml1) "[⊒Ml1 %EQ]"; [exact AOLs0|]. inversion EQ. subst γl γsl. clear EQ.

  wp_apply (append_only_loc_relaxed_read with "[$Ml1● $⊒Ml1 $omol1↦ $⊒V0']"); [solve_ndisj|].
  iIntros (el1 genl1 vl1 Vl1 V1 eVl1 eVln1)
    "(Pures & Ml1● & _ & _ & #el1✓eVl1 & _ & _ & #⊒V1 & _ & #⊒Ml1'@V1 & omol1↦)".
  iDestruct "Pures" as %(Eqgenl1 & eVl1EV & LEV0'V1 & eVln1EV & eVln1SYNC).
  iDestruct (big_sepL_lookup with "MSG1") as (eVl1') "[el1✓eVl1' %eVl1'EV]"; [exact Eqgenl1|].
  iDestruct (OmoEinfo_agree with "el1✓eVl1 el1✓eVl1'") as %<-. iClear "el1✓eVl1'".
  rewrite eVl1EV /= in eVl1'EV. subst vl1.

  iMod ("Hclose" with "[M●1 NL●1 HL●1 Tenq1 H Ml1● omol1↦]") as "_".
  { iExists E1. do 6 (iExists _). iExists enqcnt1, deqcnt1, omo1, stlist1, nodes1, hlist1.
    iFrame "M●1 NL●1 HL●1 HM Tenq1 H". repeat iExists _. iFrame "Ml1●". rewrite omo_insert_r_write_op. iFrame "MSG1".
    iSplitR; [|eauto with iFrame]. rewrite omo_insert_r_length. done. }

  iModIntro. wp_pures. wp_bind (casʳˡˣ(_, _, _))%E.

  (* Inv access 2 *)
  iInv "QInv" as (E2) "H" "Hclose".
  iDestruct "H" as (?????? enqcnt2 deqcnt2 omo2 stlist2) "(%nodes2 & %hlist2 & >HM' & >M●2 & >NL●2 & >HL●2 & >Tenq2 & >Tdeq2 & H)".
  simplify_meta with "HM' HM". iClear "HM'".
  iDestruct "Tdeq2" as (γl2 γsl2 El2 omol2 mol2) "((%AOLs0' & %EQdeqcnt2 & %NZomol2) & Ml2● & [%Vb2 omol2↦] & #MSG2)".
  rewrite AOLs0 in AOLs0'. inversion AOLs0'. subst γl2 γsl1. clear AOLs0'.

  iMod (rel_objectively_intro (⊒∅) tid with "[]") as "⊒∅".
  { iApply objective_objectively. iApply monPred_in_bot. }

  wp_apply (append_only_loc_cas_only_cas _ _ _ _ _ _ _ ∅ _ _ _ (LitInt genl1) (genl1 + 1)%Z _ ∅
    with "[$Ml2● $⊒Ml1 $omol2↦ $⊒V1 ⊒∅]"); try done; [solve_ndisj|].
  iIntros (b2 el2 genl2 vl2 Vl2 V2 mol2' omol2' eVl2 eVln2)
    "(Pures & _ & #el2✓eVl2 & #eln2✓eVln2 & Ml2● & #⊒V2 & #⊒Ml2@V3 & omol2↦ & CASE)".
  iDestruct "Pures" as %(Eqgenl2 & eVl2EV & LeV1V2).
  iDestruct "CASE" as "[(Pures & _) | [Pures sVw2]]".
  { (* CAS in FAA failed, retry FAA *)
    iDestruct "Pures" as %(-> & NEq & -> & Homol2 & eVln2EV & eVln2SYNC).
    iMod ("Hclose" with "[-AU]") as "_".
    { iExists E2. do 6 (iExists _). iExists enqcnt2, deqcnt2, omo2, stlist2, nodes2, hlist2.
      iFrame "M●2 NL●2 HL●2 HM H Tenq2". repeat iExists _. iFrame "Ml2●". subst omol2'. rewrite omo_insert_r_write_op. iFrame "MSG2".
      iSplitR; [|eauto with iFrame]. rewrite omo_insert_r_length. done. }
    iModIntro. wp_if. iApply ("IH" with "AU"). }

  (* CAS in FAA succeed, either commit or register helping *)
  iDestruct "Pures" as %(-> & -> & ->).
  iDestruct "sVw2" as (Vw2 (Eqmol2 & Homol2 & eVln2EV & eVln2SYNC & LeVl2Vw3 & NEqVl2Vw2 & NLeV2Vl2 & NEqV1V2 & LeEmpVw2))
    "(_ & _ & WCOMMIT)".
  iClear "IH". iDestruct "H" as "(Field2 & Slot2 & Penq2 & Pdeq2 & Helping2 & #Hnodes2 & (%LASTst2 & %LENnodes2 & %LENhlist2 & %LENseqs & %LENaols & %NZsz))".
  iDestruct (field_info_dup with "Field2") as "[Field2 Field2']".

  set deqcnt2' := deqcnt2 + 1.
  set Q := λ (x : Z), Φ #x.
  iDestruct (mono_list_lb_own_get with "NL●2") as "#NL◯2".
  iAssert (|={_}=> ∃ (γi γu : gname) (V2' : view) E2' omo2' stlist2',
    OmoAuth γg γs (1/2)%Qp E2' omo2' stlist2' _ ∗ ⌜ last stlist2' = Some (drop deqcnt2' nodes2) ⌝ ∗
    ⎡mono_list_auth_own γh 1 (hlist2 ++ [γi])⎤ ∗ UTok γu ∗ ⊒V2' ∗
    helping_info N γg γn q enqcnt2 (hlist2 ++ [γi]) ∗ inv (helpN N) (helping_res γn γi γu deqcnt2 V2' Q) ∗ ⌜ V2 ⊑ V2' ⌝)%I
      with "[AU WCOMMIT Helping2 HL●2 M●2]" as ">(%&%&%&%&%&%& M●2 & %LASTst2' & HL●2 & Hγu & #⊒V2' & Helping2 & #HInv & %LeV2V2')".
  { destruct (le_lt_dec enqcnt2 deqcnt2) as [LE|LT].
    - (* Matching enq has not been committed → need helping *)
      iAssert (atomic_update_deq N γg q V0 M Q)%I with "[AU]" as "AU".
      { rewrite /atomic_update_deq. iAuIntro. iApply (aacc_aupd with "AU"); [done|].
        iIntros (E) "H". iAaccIntro with "H".
        { iIntros "H !>". iFrame. iIntros "AU !>". iFrame. }
        iIntros (v V' E' M') "(H & #⊒V' & #LocalInner & #E'◯ & %) !>". iRight.
        iExists v, V', E', M'. iFrame. iFrame "⊒V'". iSplit; [iSplit; [|done]|by iIntros "H !>"; iApply "H"].
        by iFrame "LocalInner E'◯ QInv". }
      iDestruct (view_at_intro_incl with "AU ⊒V2") as (V2') "(#⊒V2' & %LeV2V2' & AU@V2')".
      iMod (ghost_var_alloc Pending) as (γi) "[Hγi Hγi']".
      iMod UTok_alloc as (γu) "Hγu".
      iMod (mono_list_auth_own_update with "HL●2") as "[HL●2 #HL◯2]".
      { have ? : hlist2 ⊑ (hlist2 ++ [γi]); [|done]. by apply prefix_app_r. }
      iMod (inv_alloc (helpN N) _ (helping_res γn γi γu deqcnt2 V2' Q) with "[Hγi']") as "#HInv"; [iExists Pending;iFrame "Hγi'"|].

      iModIntro. iExists γi,γu,V2',E2,omo2,stlist2. iFrame "M●2 HL●2 Hγu HInv ⊒V2'". iSplitR.
      { iPureIntro. rewrite LASTst2. do 2 (rewrite drop_ge; [|lia]). done. }
      iSplitL; [|iPureIntro;solve_lat]. iDestruct "Helping2" as "[H1 H2]".
      rewrite /helping_info take_app_le; [|lia]. iFrame "H1".
      rewrite drop_app_le; [|lia]. rewrite big_sepL_snoc. iFrame "H2".
      iExists γl1,(length El2),γu,V2',V0,M,Q. iFrame "Hγi AU@V2' WCOMMIT". iSplitR; [solve_lat|]. iSplit.
      + repeat iExists _. iFrame "HM ⊒M@V0' ⊒AOLs@V0' ⊒SEQs@V0' ⊒eV0@V0'".
      + replace (enqcnt2 + length (drop enqcnt2 hlist2)) with deqcnt2; [iFrame "HInv"|].
        rewrite drop_length. lia.
    - (* Matching enq has already been committed → commit immediately *)
      have [[[[enqId v] V] lV] Hnode] : is_Some (nodes2 !! deqcnt2) by rewrite lookup_lt_is_Some; lia.
      iDestruct (mono_list_idx_own_get with "NL◯2") as "IDX"; [exact Hnode|].
      iDestruct (big_sepL_lookup with "Hnodes2") as (?? eVenq) "[[% %NZ] #enqId✓eVenq]"; [exact Hnode|].
      inversion H. subst enqId0 v0 V lV. clear H.

      iCombine "AU M●2 WCOMMIT enqId✓eVenq QInv HM" as "RES".
      iDestruct (view_at_intro_incl with "RES ⊒V2") as (V2') "(#⊒V2' & %LeV2V2' & RES)".
      set V2'' := V2' ⊔ (eVenq.(sync)).
      iDestruct (view_at_mono_2 _ V2'' with "RES") as "RES"; [solve_lat|].
      iCombine "⊒M@V0' ⊒AOLs@V0' ⊒SEQs@V0' ⊒eV0@V0'" as "⊒@V0'".
      iDestruct (view_at_mono_2 _ V2'' with "⊒@V0'") as "⊒@V2''"; [solve_lat|].
      iDestruct (view_at_view_at _ _ V2'' with "⊒@V2''") as "⊒@V2''@V2''".
      iAssert (@{V2''} ⊒V2'')%I as "⊒V2''@V2''". { by iPureIntro. }
      iCombine "RES ⊒V2''@V2'' ⊒@V2''@V2''" as "RES".

      iAssert (|={_}=> @{V2''} (Q v ∗
        (∃ E2' omo2' stlist2', OmoAuth γg γs (1/2)%Qp E2' omo2' stlist2' _ ∗ ⌜ last stlist2' = Some (drop deqcnt2' nodes2) ⌝)))%I
          with "[RES]" as ">[Qv (%&%&%& M● & %LASTst2')]".
      { rewrite -view_at_fupd.
        iApply (view_at_mono with "RES"); [done|].
        iIntros "[(AU & M● & WCOMMIT & #enqId✓eVenq & #QInv & #HM) (#⊒V2'' & #⊒M@V2'' & #⊒AOLs@V2'' & #⊒SEQs@V2'' & #⊒eV0@V2'')]".

        iDestruct (OmoEview_insert_new_obj with "⊒M@V2'' enqId✓eVenq") as "⊒M'@V2''"; [solve_lat|].
        set M' := {[enqId]} ∪ eVenq.(eview) ∪ M.

        have LeV0V2'' : V0 ⊑ V2'' by solve_lat.
        set deqId := length E2.
        set M'' := {[deqId]} ∪ M'.
        set eVdeq := mkOmoEvent (Deq v) V2'' M''.
        set E2' := E2 ++ [eVdeq].
        have [deqst Hdeqst] : ∃ deqst, drop deqcnt2 nodes2 = (enqId, v, eVenq.(sync), eVenq.(eview)) :: deqst.
        { destruct (drop deqcnt2 nodes2) eqn:Heq.
          - apply (f_equal length) in Heq. rewrite drop_length /= in Heq. lia.
          - apply (f_equal ((!!) 0)) in Heq. rewrite lookup_drop Nat.add_0_r Hnode /= in Heq. inversion Heq. by eexists. }

        iMod "AU" as (E2'') "[>QInv' [_ Commit]]".
        iDestruct "QInv'" as (???) "M●'". iDestruct (OmoAuth_agree with "M● M●'") as %(<- & <- & <- & <-).
        iCombine "M● M●'" as "M●".
        iMod (OmoAuth_insert_last with "M● ⊒M'@V2'' WCOMMIT []") as "(M● & #⊒M''@V2'' & _)".
        { have ? : step deqId eVdeq ((enqId, v, eVenq.(sync), eVenq.(eview)) :: deqst) deqst.
          - apply queue_step_Deq; try done; [solve_lat|set_solver-].
          - rewrite Hdeqst in LASTst2. iPureIntro. split_and!; try done. }
        iDestruct (OmoHbToken_finish with "M●") as "M●".
        iDestruct (OmoSnapHistory_get with "M●") as "#E◯".
        iDestruct "M●" as "[M● M●']".

        iMod ("Commit" $! v V2'' E2' M'' with "[M●']") as "HΦ".
        { iFrame "⊒V2''". iSplitL; last iSplit.
          - repeat iExists _. iFrame "M●'".
          - iFrame "E◯ QInv". repeat iExists _. iFrame "HM ⊒M''@V2'' ⊒AOLs@V2'' ⊒SEQs@V2'' ⊒eV0@V2''".
          - iPureIntro. split_and!; try done. set_solver-. }

        iModIntro. iDestruct ("HΦ" with "[]") as "HΦ"; [done|]. iFrame "HΦ".
        repeat iExists _. iFrame "M●". iPureIntro. rewrite last_app.
        replace (drop deqcnt2' nodes2) with deqst; [done|]. symmetry. subst deqcnt2'.
        replace (deqcnt2 + 1) with (S deqcnt2) by lia.
        rewrite (drop_S _ (enqId, v, eVenq.(sync), eVenq.(eview))) in Hdeqst; try done. by inversion Hdeqst. }

      rewrite (view_at_objective_iff (OmoAuth γg γs (1/2) E2' omo2' stlist2' _)).

      iMod (ghost_var_alloc Accepted) as (γi) "[Hγi Hγi']".
      iMod UTok_alloc as (γu) "Hγu".
      iMod (mono_list_auth_own_update with "HL●2") as "[HL●2 #HL◯2]".
      { have ? : hlist2 ⊑ (hlist2 ++ [γi]); [|done]. by apply prefix_app_r. }
      iMod (inv_alloc (helpN N) _ (helping_res γn γi γu deqcnt2 V2' Q) with "[Hγi' Qv]") as "#HInv".
      { iExists _. iFrame "Hγi'". repeat iExists _. iFrame "IDX Qv". }

      iModIntro. iExists γi,γu,V2',E2',omo2',stlist2'. iFrame "M● HL●2 HInv ⊒V2' Hγu". iSplitR; [done|]. iSplitL; [|done].
      iDestruct "Helping2" as "[H1 H2]".
      rewrite /helping_info (drop_ge (hlist2 ++ [γi])); [|rewrite app_length /=; lia]. iSplitL; [|done].
      rewrite take_app_ge; [|lia]. rewrite (take_ge [γi]); [|simpl;lia]. rewrite take_ge; [|lia].
      rewrite big_sepL_snoc. iFrame "H1". iExists _. iFrame "Hγi". done. }

  iDestruct (mono_list_lb_own_get with "HL●2") as "#HL◯2".
  iDestruct (mono_list_idx_own_get with "HL◯2") as "HL@deqcnt2".
  { have ? : (hlist2 ++ [γi]) !! deqcnt2 = Some γi; [|done]. rewrite -LENhlist2 lookup_app_1_eq. done. }

  set turn := (Z.of_nat deqcnt2 `quot` Z.of_nat sz)%Z.
  set idx := (Z.of_nat deqcnt2 `rem` Z.of_nat sz)%Z.
  iDestruct (extract_one_ticket with "Pdeq2") as (???) "(Pdeq2 & Perm & %Hidx)"; [done|done|].

  iAssert (⌜ genl1 = deqcnt2 ⌝)%I with "[-]" as %->.
  { iDestruct (big_sepL_lookup with "MSG2") as (eVl2') "[el2✓eVl2' %eVl2'EV]"; [exact Eqgenl2|].
    iDestruct (OmoEinfo_agree with "el2✓eVl2 el2✓eVl2'") as %<-.
    rewrite eVl2EV /= in eVl2'EV. inversion eVl2'EV. iPureIntro. lia. }

  iMod ("Hclose" with "[-Perm Hγu Field2]") as "_".
  { iExists E2'. repeat iExists _. iFrame "HM M●2 HL●2 NL●2 Tenq2 Field2' Slot2 Penq2 Pdeq2 Helping2 Hnodes2". iSplitL; last first.
    { iPureIntro. split_and!; try done. rewrite app_length /=. lia. }
    repeat iExists _. iFrame "Ml2●". subst omol2'. rewrite omo_append_w_length omo_append_w_write_op. iSplitR.
    { iPureIntro. split_and!; try done; try lia. }
    iSplitL; [eauto with iFrame|]. iModIntro. rewrite big_sepL_snoc. iFrame "MSG2".
    iExists eVln2. iFrame "eln2✓eVln2". rewrite eVln2EV -omo_write_op_length EQdeqcnt2 /=. iPureIntro.
    have EQ : (Z.of_nat (length omol2 - 1) + 1 = Z.of_nat (length omol2))%Z; [|by rewrite EQ].
    replace (Z.of_nat (length omol2 - 1) + 1)%Z with (Z.of_nat (length omol2))%Z by lia. done. }

  iDestruct "Field2" as (??) "[#e0✓eV0 [q↦sz BIGq]]". iDestruct "⊒eV0" as (?) "[e0✓eV0' ⊒eV0OUT]".
  iDestruct (OmoEinfo_agree with "e0✓eV0 e0✓eV0'") as %<-. iDestruct (view_at_elim with "⊒eV0OUT q↦sz") as "q↦sz".
  iAssert (@{eV0.(sync)} (q >> (Z.to_nat idx + 3)) ↦{qp} #(LitLoc sloc))%I with "[BIGq]" as "q↦sloc".
  { iApply (view_at_mono with "BIGq"); [done|]. iIntros "BIG". iDestruct (big_sepL_lookup with "BIG") as "H"; [done|]. done. }
  iDestruct (view_at_elim with "⊒eV0OUT q↦sloc") as "q↦sloc".

  iModIntro. wp_pures. rewrite -[Z.to_nat 2]/(2%nat).
  wp_read. wp_pures. rewrite -[Z.to_nat 3]/(3%nat) shift_nat_assoc.
  replace (3 + Z.to_nat (deqcnt2 `rem` sz)) with (Z.to_nat (deqcnt2 `rem` sz) + 3) by lia. wp_read.

  iDestruct (big_sepL_lookup with "⊒SEQs") as (??? Mseq2) "[⊒Mseq2 %]"; [exact Hidx|].
  inversion H. subst γseq0 γseqs0 sloc0. clear H.
  replace (Z.of_nat deqcnt2 `quot` Z.of_nat sz) with (Z.of_nat (Z.to_nat turn)); last first.
  { have ? : (0 ≤ deqcnt2 `quot` sz)%Z; [by apply Zquot_le_lower_bound; lia|lia]. }

  (* Inv access 3 *)
  have NDISJ' : (seqN N) ## histN by solve_ndisj.
  awp_apply (dequeueWithTicket_spec seq _ NDISJ' sloc tid γseq γseqs _ V2 (Z.to_nat (deqcnt2 `quot` sz)) with "⊒V2 ⊒Mseq2 [Perm]").
  { rewrite (_: Z.to_nat (Z.to_nat turn) = Z.to_nat turn); [done|lia]. }

  iInv "QInv" as (E3) "H".
  iDestruct "H" as (?????? enqcnt3 deqcnt3 omo3 stlist3)
    "(%nodes3 & %hlist3 & >HM' & >M●3 & >NL●3 & >HL●3 & >Tenq3 & >Tdeq3 & Field3 & Slot3 & Penq3 & Pdeq3 & Helping3 & >#Hnodes3 & >Pures)".
  iDestruct "Pures" as %(LASTst3 & LENnodes3 & LENhlist3 & _).
  simplify_meta with "HM' HM". iClear "HM'".

  iDestruct (big_sepL_lookup_acc with "Slot3") as "[H Slot3Close]"; [done|].
  iDestruct "H" as (???) "[>% Slot]". inversion H. subst γseq0 γseqs0 sloc0. clear H.
  iDestruct "Slot" as (Es3 omos3 sts3 stfs3) "(Ms3● & >%Hstfs3 & Hstfs3)".
  rewrite SeqInv_OmoAuth_acc. iDestruct "Ms3●" as (qp') "[>Ms3● Ms3●Close]".
  iDestruct (OmoAuth_wf with "Ms3●") as %[OMO_GOOD _].
  iDestruct (OmoAuth_omo_nonempty with "Ms3●") as %NZomos3.
  iDestruct ("Ms3●Close" with "[Ms3●]") as "Ms3●"; [iFrame "Ms3●"|].

  iAaccIntro with "Ms3●".
  { (* Peeking case *)
    iIntros "Ms3●". iModIntro. iFrame "Hγu q↦sz q↦sloc". iModIntro.
    iExists E3. repeat iExists _. iFrame "HM M●3 NL●3 HL●3 Tenq3 Tdeq3 Field3 Penq3 Pdeq3 Helping3 Hnodes3". iSplitL; last first.
    { iPureIntro. split_and!; try done. }
    iApply "Slot3Close". repeat iExists _. iSplit; [done|]. repeat iExists _. iFrame "Ms3● Hstfs3". done. }

  iIntros (V3 Mseq3 v3) "(Ms3● & _ & #⊒V3 & #⊒Mseq3 & (%LeV2V3 & %InclMseq2Mseq3 & %V3NZ))".
  iInv "HInv" as (hst) "[>Hγi Hhst]".
  iDestruct "Helping3" as "[>Helping3 Helping3']".

  (* Use [omo_write_op_step] to get info of latest op on SEQ *)
  rewrite SeqInv_OmoAuth_acc. iDestruct "Ms3●" as (qp'') "[>Ms3● Ms3●Close]".
  iDestruct (OmoAuth_wf with "Ms3●") as %[OMO_GOOD' _].
  iDestruct ("Ms3●Close" with "[Ms3●]") as "Ms3●"; [iFrame "Ms3●"|].
  set eVsdeq := mkOmoEvent (spec_singleElementQueue_composition.Deq v3 (Z.to_nat (deqcnt2 `quot` sz))) V3 Mseq3.
  set omos3' := omo_append_w omos3 (length Es3) [].
  have STEP : step (length Es3) eVsdeq stfs3 [].
  { eapply (omo_write_op_step _ _ _ (length omos3 - 1)); [apply OMO_GOOD'|..].
    - rewrite omo_append_w_write_op omo_write_op_length Nat.sub_add; [by rewrite lookup_app_1_eq|].
      rewrite -omo_write_op_length. destruct omos3; [done|]. simpl. lia.
    - by rewrite lookup_app_1_eq.
    - rewrite (omo_stlist_length _ _ _ OMO_GOOD). rewrite lookup_app_l; [|destruct sts3; [done|simpl;lia]].
      rewrite -Hstfs3 last_lookup. replace (Init.Nat.pred (length sts3)) with (length sts3 - 1)%nat by lia. done.
    - rewrite Nat.sub_add; [|destruct omos3; [done|simpl;lia]]. rewrite (omo_stlist_length _ _ _ OMO_GOOD) lookup_app_1_eq. done. }

  inversion STEP; [|inversion INIT].
  inversion DEQ. subst v3 n. simpl.
  iDestruct "Hstfs3" as (???) ">[#NL@deqcnt2 [_ %LeV4V]]".
  have EQ : (sz * Z.to_nat (Z.of_nat deqcnt2 `quot` Z.of_nat sz) + Z.to_nat idx) = deqcnt2.
  { have EQ : (Z.of_nat deqcnt2 = Z.of_nat sz * turn + idx)%Z by lia.
    apply (f_equal Z.to_nat) in EQ. replace (Z.to_nat (Z.of_nat deqcnt2)) with deqcnt2 in EQ by lia. rewrite {2}EQ.
    replace (Z.to_nat (Z.of_nat sz * turn + idx))%Z with (Z.to_nat (Z.of_nat sz) * Z.to_nat turn + Z.to_nat idx); [lia|].
    have ? : (0 ≤ turn)%Z; [|lia]. subst turn. apply Zquot_le_lower_bound; lia. }
  rewrite EQ. clear EQ.
  iDestruct (mono_list_auth_idx_lookup with "NL●3 NL@deqcnt2") as %NL3deqcnt2.
  apply lookup_lt_Some in NL3deqcnt2 as LTdeqcnt2enqcnt3. rewrite LENnodes3 in LTdeqcnt2enqcnt3.

  iDestruct (mono_list_auth_idx_lookup with "HL●3 HL@deqcnt2") as %HL3deqcnt2.
  iDestruct (big_sepL_lookup_acc _ _ deqcnt2 with "Helping3") as "[(%& Hγi' & %NEQ) Helping3Close]"; [by rewrite lookup_take|].
  iDestruct (ghost_var_agree with "Hγi Hγi'") as %<-.
  destruct hst; [done|..]; last first.
  { iDestruct "Hhst" as ">Hγu'". by iDestruct (UTok_unique with "Hγu Hγu'") as %?. }
  iCombine "Hγi Hγi'" as "Hγi".
  iMod (ghost_var_update Acked with "Hγi") as "[Hγi Hγi']".

  iModIntro. iSplitL "Hγi' Hγu". { iExists _. iFrame "Hγi'". iFrame "Hγu". }
  iModIntro. iSplitR "Hhst".
  { iModIntro. iExists E3. repeat iExists _. iFrame "HM M●3 NL●3 HL●3 Tenq3 Tdeq3 Field3 Penq3 Pdeq3 Hnodes3".
    iSplitR "Helping3' Helping3Close Hγi"; last iSplitL.
    - iApply "Slot3Close". repeat iExists _. iSplit; [done|]. repeat iExists _. iFrame "Ms3●". iSplit; [by rewrite last_app|]. done.
    - iFrame "Helping3'". iApply "Helping3Close". iExists _. iFrame "Hγi". done.
    - iPureIntro. split_and!; try done. }

  iIntros "_". wp_pures.
  iDestruct "Hhst" as (????) "[#NL@deqcnt2' Q]".
  iDestruct (mono_list_idx_agree with "NL@deqcnt2 NL@deqcnt2'") as %[[[<- <-]%pair_inj <-]%pair_inj <-]%pair_inj.

  have ? : V4 ⊑ V3. { subst eVsdeq. solve_lat. }
  have ? : (V2' ⊔ V4) ⊑ (V2' ⊔ V3) by solve_lat.
  iCombine "⊒V2' ⊒V3" as "⊒V2'V3". rewrite monPred_in_view_op.
  iDestruct (view_at_mono_2 _ (V2' ⊔ V3) with "Q") as "Q"; [done|].
  iDestruct (view_at_elim with "⊒V2'V3 Q") as "Q".
  by iApply "Q".
Qed.
End MpmcQueue.

Definition mpmcqueue_impl `{!noprolG Σ, !atomicG Σ, !mpmcqueueG Σ} (seq : seq_composition_spec Σ)
  : mpmcqueue_spec Σ := {|
    spec_mpmcqueue_history.QueueInv_Linearizable := QueueInv_Linearizable_instance;
    spec_mpmcqueue_history.QueueInv_history_wf := QueueInv_history_wf_instance;
    spec_mpmcqueue_history.QueueInv_QueueLocal := QueueInv_QueueLocal_instance seq;
    spec_mpmcqueue_history.QueueLocal_lookup := QueueLocal_lookup_instance seq;

    spec_mpmcqueue_history.new_queue_spec := new_queue_spec seq;
    spec_mpmcqueue_history.enqueue_spec := enqueue_spec seq;
    spec_mpmcqueue_history.dequeue_spec := dequeue_spec seq;
  |}.
