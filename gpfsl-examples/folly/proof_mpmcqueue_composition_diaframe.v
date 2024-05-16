From gpfsl.examples Require Import sflib.

From iris.algebra Require Import auth gset gmap agree.
From iris.proofmode Require Import tactics.
From iris.base_logic.lib Require Import ghost_var.

From gpfsl.base_logic Require Import meta_data.
From gpfsl.logic Require Import logatom atomics invariants.

From gpfsl.logic Require Import repeat_loop new_delete.
From gpfsl.examples Require Import uniq_token map_seq loc_helper.
From gpfsl.examples.algebra Require Import set mono_list.
From gpfsl.examples.folly Require Import spec_turnSequencer_composition spec_singleElementQueue_composition spec_mpmcqueue_composition.
From gpfsl.examples.folly Require Import code_singleElementQueue code_mpmcqueue.
From gpfsl.examples.omo Require Import omo omo_preds omo_preds_diaframe append_only_loc.

From gpfsl.diaframe Require Import vprop_weakestpre spec_notation
 vprop_weakestpre_logatom atom_spec_notation proof_automation omo_specs omo_hints.

From diaframe Require Import proofmode_base lib.except_zero own_hints steps.verify_tac util_instances.
From diaframe.symb_exec Require Import weakestpre_logatom.


Require Import iris.prelude.options.
From Coq Require Import ZArith.
From Coq.ZArith Require Import Zquot.

Inductive helping_state := Pending | Accepted | Acked.
Local Instance helping_state_inhabited : Inhabited helping_state := populate Pending.
Definition queue_state_inner := (event_id * Z * view * eView)%type.

Class mpmcqueueG Σ := MpmcQueueG {
  mpmc_omoGeneralG :> omoGeneralG Σ;
  mpmc_omoG :> omoSpecificG Σ qevent queue_state;
  mpmc_seqG :> omoSpecificG Σ seq_event seq_state;
  mpmc_aolocG :> appendOnlyLocG Σ;
  mpmc_nodes_monoG :> mono_listG queue_state_inner Σ;
  mpmc_helping_monoG :> mono_listG gname Σ;
  mpmc_helping_stateG :> ghost_varG Σ helping_state;
  mpmc_uniqTokG :> uniqTokG Σ;
}.

Definition mpmcqueueΣ : gFunctors := #[omoGeneralΣ; omoSpecificΣ qevent queue_state; omoSpecificΣ seq_event seq_state; appendOnlyLocΣ; mono_listΣ queue_state_inner; mono_listΣ gname; ghost_varΣ helping_state; uniqTokΣ].

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

Definition elem_of_aol aols idx x : vProp := ⌜ aols !! idx = Some x ⌝.

Definition ticket_info q aols (idx cnt : nat) : vProp :=
  ∃ γl γsl El omol mo,
    try_update_OmoAuth_to γl El omol mo ∗
    ⌜ cnt = length omol - 1 ∧ length omol ≠ 0 ⌝ ∗
    elem_of_aol aols idx (γl, γsl) ∗
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

Definition slot_info_case γn (sz idx : nat) (stf : seq_state) : vProp :=
  ( ⌜ stf = [] ⌝
  ∨ (∃ stfh (enqId : event_id) (V : view) (lV : eView),
      let nidx := sz * stfh.1.1.2 + idx in
      MatchValue [stfh] stf ∗
      ⎡mono_list_idx_own γn nidx (enqId, stfh.1.1.1.2, V, lV)⎤ ∗ ⌜ V ⊑ stfh.1.2 ⌝)).

Definition slot_info γn γseq γseqs sloc (sz idx : nat) : vProp :=
  ∃ Es omos (seq_stlist : list seq_state) stf,
  SeqInv seq γseq γseqs sloc Es omos seq_stlist ∗
  MatchValue (Some stf) (last seq_stlist) ∗
  slot_info_case γn sz idx stf.

Definition slot_field γn seqs sz : vProp :=
  [∗ list] idx↦x ∈ seqs, ∃ γseq γseqs sloc, ⌜ x = (γseq, γseqs, sloc) ⌝ ∗ slot_info γn γseq γseqs sloc sz idx.

Definition perm_bank seqs (sz cnt : nat) (ty : seq_perm_type) : vProp :=
  [∗ list] idx↦x ∈ seqs,
    ∃ γseq γseqs sloc, ⌜ x = (γseq, γseqs, sloc) ⌝ ∗ SeqPerm seq γseq sloc ty (λ m, Z.to_nat ((cnt + sz - idx - 1) `quot` sz)%Z <=? m).

Definition QueueInv γg γs q E omo stlist : vProp :=
  try_update_OmoAuth_to γg E omo stlist ∗
  OmoAuth γg γs (1/2)%Qp E omo stlist _.

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
    (tele_app (TT:= [tele _ _ _ _]) (λ γs E omo stlist, ▷ QueueInv γg γs q E omo stlist)%I)
    (tele_app (TT:= [tele _ _ _ _])
      (λ γs E omo stlist, tele_app (TT:= [tele _])
        (λ (v: Z), ∃ V', ask_for V' ∗
          ∃ M' omo' stlist' st,
            let eVdeq := mkOmoEvent (Deq v) V' M' in
            let E' := E ++ [eVdeq] in
            (* PUBLIC POST *)
            ⊒V' ∗ ▷ QueueInv γg γs q E' omo' stlist' ∗ @{V'} QueueLocal_inner N γg q M' ∗
            OmoTokenW γg (length E) ∗ OmoUB γg M (length E) ∗
            ⌜ V ⊑ V' ∧ M ⊆ M' ∧ omo' = omo_append_w omo (length E) [] ∧ stlist' = stlist ++ [st] ∧ (0 < v)%Z ⌝)%I))
    (tele_app (TT:= [tele _ _ _ _])
      (λ γs E omo stlist, tele_app (TT:= [tele _])
        (λ v, Q v)%I)).

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
      @{Vb} (atomic_update_deq N γg q Vi M Q ∗ QueueLocal_inner N γg q M) ∗
      ⎡ghost_var γi (1/2)%Qp Pending⎤ ∗
      OmoTokenW γl el ∗
      inv (helpN N) (helping_res γn γi γu (enqcnt + i) Vb Q) ∗ ⌜ Vi ⊑ Vb ⌝).

Definition nodes_info γg nodes : vProp :=
  [∗ list] node ∈ nodes,
    ∃ enqId v (eV : omo_event qevent),
      ⌜ node = (enqId, v, eV.(sync), eV.(eview)) ∧ (0 < v)%Z ⌝ ∗ OmoEinfo γg enqId eV.

Definition QueueInternalInv (N : namespace) γg q E : vProp :=
  ∃ γs γn γh aols seqs omo stlist nodes hlist,
    meta q nroot (γs,γn,γh,aols,seqs,length seqs) ∗

    OmoAuth γg γs (1/2)%Qp E omo stlist _ ∗
    ⎡mono_list_auth_own γn 1 nodes⎤ ∗
    ⎡mono_list_auth_own γh 1 hlist⎤ ∗

    ticket_info q aols 0 (length nodes) ∗
    ticket_info q aols 1 (length hlist) ∗
    field_info γg q seqs (length seqs) ∗
    slot_field γn seqs (length seqs) ∗
    perm_bank seqs (length seqs) (length nodes) EnqP ∗
    perm_bank seqs (length seqs) (length hlist) DeqP ∗
    helping_info N γg γn q (length nodes) hlist ∗
    nodes_info γg nodes ∗

    ⌜ last stlist = Some (drop (length hlist) nodes)
    ∧ length seqs ≠ 0
    ∧ (length aols = 2)%nat ⌝.

Definition InternalInv_inner N γg q : vProp := ∃ E, QueueInternalInv N γg q E ∗ emp.
Definition InternInv N γg q := inv (mpmcqN N) (InternalInv_inner N γg q).

Definition QueueLocal (N : namespace) γg q M : vProp :=
  QueueLocal_inner N γg q M ∗ InternInv N γg q.

Local Instance slot_info_objective γn γseq γseqs slot sz idx : Objective (slot_info γn γseq γseqs slot sz idx).
Proof. repeat (apply exists_objective; intros). destruct x2; apply _. Qed.
Local Instance QueueInternalInv_objective N γg q E : Objective (QueueInternalInv N γg q E) := _.
Local Instance helping_res_objective γn γi γu idx Vb Q : Objective (helping_res γn γi γu idx Vb Q).
Proof. apply exists_objective; intros. destruct x; apply _. Qed.
Global Instance QueueLocal_persistent N γg q M : Persistent (QueueLocal N γg q M) := _.

Local Tactic Notation "simplify_meta" "with" constr(Hs) :=
  iDestruct (meta_agree with Hs) as %[[[[[-> ->]%pair_inj ->]%pair_inj ->]%pair_inj ->]%pair_inj ->]%pair_inj.

Notation newSEQ := (spec_singleElementQueue_composition.newSEQ seq).
Notation enqueueWithTicket := (spec_singleElementQueue_composition.enqueueWithTicket seq).
Notation dequeueWithTicket := (spec_singleElementQueue_composition.dequeueWithTicket seq).

Lemma QueueInv_Linearizable_instance :
  ∀ γg γs q E omo stlist, QueueInv γg γs q E omo stlist ⊢ ⌜ Linearizability_omo E omo stlist ⌝.
Proof. intros. iIntros "[_ M●]". by iDestruct (OmoAuth_Linearizable with "M●") as %?. Qed.

Lemma QueueInv_OmoAuth_acc_instance :
  ∀ γg γs q E omo stlist,
    QueueInv γg γs q E omo stlist ⊢ OmoAuth γg γs (1/2)%Qp E omo stlist _ ∗ (OmoAuth γg γs (1/2)%Qp E omo stlist _ -∗ QueueInv γg γs q E omo stlist).
Proof. intros. iIntros "[H M●]". iFrame. iIntros "M●". iFrame. Qed.

Lemma QueueLocal_OmoEview_instance :
  ∀ N γg q M, QueueLocal N γg q M ⊢ OmoEview γg M.
Proof. oSteps. Qed.

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
    replace (Z.of_nat sz * (x `quot` Z.of_nat sz) + x `rem` Z.of_nat sz - 1)%Z with ((x `quot` Z.of_nat sz) * Z.of_nat sz + (x `rem` Z.of_nat sz - 1))%Z by lia.
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

Lemma plus_1_S (n : nat) : n + 1 = S n.
Proof. lia. Qed.

#[local] Instance elem_of_aol_acc_aols aols idx x :
  MergablePersist (elem_of_aol aols idx x) (λ p Pin Pout,
    TCAnd (TCEq Pin ([∗ list] x ∈ aols, ∃ γl' γsl' Ml, OmoEview γl' Ml ∗ ⌜ x = (γl', γsl') ⌝)) $
      TCEq Pout (∃ Ml, OmoEview x.1 Ml ∗ ⌜ aols !! idx = Some x ⌝))%I.
Proof using All.
  intros p Pin Pout [-> ->]. rewrite bi.intuitionistically_if_elim. iIntros "[% #BIG]". iModIntro.
  iDestruct (big_sepL_lookup with "BIG") as "Inner"; [done|]. iDecompose "Inner". oSteps.
Qed.

#[local] Instance elem_of_aol_acc_aols' aols idx x V :
  MergablePersist (elem_of_aol aols idx x) (λ p Pin Pout,
    TCAnd (TCEq Pin (@{V} ([∗ list] x ∈ aols, ∃ γl' γsl' Ml, OmoEview γl' Ml ∗ ⌜ x = (γl', γsl') ⌝))) $
      TCEq Pout (∃ Ml, @{V} OmoEview x.1 Ml ∗ ⌜ aols !! idx = Some x ⌝))%I.
Proof using All.
  intros p Pin Pout [-> ->]. rewrite bi.intuitionistically_if_elim. iIntros "[% #BIG]". iModIntro.
  rewrite big_sepL_lookup; [|done]. iDecompose "BIG". oSteps.
Qed.

#[local] Instance big_sepL_sep_na V q seqs (qp : Qp) :
  HINT (@{V} ([∗ list] idx↦x∈seqs, (q >> (idx + 3)) ↦{qp} #(LitLoc x.2))) ✱ [-; emp]
  ⊫ [id]
  ; @{V} ([∗ list] idx↦x∈seqs, (q >> (idx + 3)) ↦{qp / 2} #(LitLoc x.2)) ✱ [@{V} ([∗ list] idx↦x∈seqs, (q >> (idx + 3)) ↦{qp / 2} #(LitLoc x.2))] | 10.
Proof using All.
  iSteps as "H". unseal_diaframe. rewrite /= -view_at_sep -big_sepL_sep. iApply (view_at_mono with "H"); [done|]. iIntros "H".
  iApply (big_sepL_impl with "H"). iSteps as "H". iDestruct "H" as "[H1 H2]". oSteps.
Qed.

(* try_update rules *)
#[local] Instance biabd_OmoAuth_as_is' γe γs qp E omo omo' stlist stlist'  :
  let master := OmoAuth γe γs qp E omo stlist _ in
  HINT master ✱ [-; ⌜omo' = omo ∧ stlist' = stlist⌝]
  ⊫ [id]
  (* Todo: omo' and stlist' to existential quantifier. *)
  ; try_update_OmoAuth_to γe E omo' stlist'✱ [ master ] | 1.
Proof. rewrite try_update_OmoAuth_to_eq => ?. iSteps. Qed.

Lemma fupd_intro_goal (E1 E2 : coPset) (P Q : vProp) :
  ⊢ (|={E1,E2}=> (P ∗ (P ={E2}=∗ Q))) ={E1,E2}=∗ Q.
Proof. iIntros ">[H1 H2]". iMod ("H2" with "H1") as "Q". done. Qed.

#[local] Instance enqueueWithTicket_dspec N γg γs q V M (v : Z) n :
  SPEC ⟨ ⊤ , ↑N , ↑histN⟩ Es omos stlist, <<
    ⊒V ∗ SeqLocal seq N γg q M ∗ SeqPerm seq γg q EnqP (λ m, m =? n) ∗
    ⌜ N ## histN ∧ (0 < v)%Z ⌝
  ¦
    ▷ SeqInv seq γg γs q Es omos stlist > >
      enqueueWithTicket [ #q; #n; #v ]
  << RET #☠;
      emp
      ¦
      (
      ∃ V' M' omos' stlist',
      let Es' := Es ++ [mkOmoEvent (spec_singleElementQueue_composition.Enq v n) V' M'] in
      let opId := length Es in
      let st := [(opId, v, n, V', M')] in
      ▷ SeqInv seq γg γs q Es' omos' stlist' ∗ OmoTokenW γg opId ∗
      ⊒V' ∗ @{V'} SeqLocal seq N γg q M' ∗ ⌜ V ⊑ V' ∧ M ⊆ M' ∧ omos' = omo_append_w omos opId [] ∧ stlist' = stlist ++ [st] ⌝)
    > >.
Proof using All.
  iSteps as "⊒V ⊒M Perm AU". awp_apply (enqueueWithTicket_spec seq _ H q _ _ γs _ _ v n H0 with "⊒V ⊒M Perm"). iApply (aacc_aupd with "AU"); [done|].
  iSteps as (E omo stlist) "M●". iAaccIntro with "M●"; [oSteps|]. iSteps as "⊒V ⊒M M●".
Qed.

#[local] Instance dequeueWithTicket_dspec N γg γs q V M n :
  SPEC ⟨ ⊤ , ↑N , ↑histN⟩ Es omos stlist, <<
    ⊒V ∗ SeqLocal seq N γg q M ∗ SeqPerm seq γg q DeqP (λ m, m =? n) ∗
    ⌜ N ## histN ⌝
  ¦
    ▷ SeqInv seq γg γs q Es omos stlist > >
      dequeueWithTicket [ #q; #n ]
  << (v : Z), RET #v;
      emp
      ¦
      (
      ∃ V' M' omos' stlist' est Vst lVst,
      let Es' := Es ++ [mkOmoEvent (spec_singleElementQueue_composition.Deq v n) V' M'] in
      let opId := length Es in
      ▷ SeqInv seq γg γs q Es' omos' stlist' ∗ OmoTokenW γg opId ∗ ⊒V' ∗ @{V'} SeqLocal seq N γg q M' ∗
      ⌜ V ⊑ V' ∧ M ⊆ M' ∧ omos' = omo_append_w omos opId [] ∧ stlist' = stlist ++ [[]] ∧ last stlist = Some [(est, v, n, Vst, lVst)] ∧ Vst ⊑ V' ⌝)
    > >.
Proof using All.
  iSteps as "⊒V ⊒M Perm AU". awp_apply (dequeueWithTicket_spec seq _ H q _ _ γs with "⊒V ⊒M Perm"). iApply (aacc_aupd with "AU"); [done|].
  iSteps as (E omo stlist) "M●". iDestruct (SeqInv_OmoAuth_acc with "M●") as (?) "[>M● Close]". iDestruct (OmoAuth_wf with "M●") as %[OMO_GOOD _].
  iDestruct (OmoAuth_omo_nonempty with "M●") as %Nomo. have NZomo : length omo ≠ 0 by destruct omo. iDestruct ("Close" with "[M●]") as "M●"; [done|].
  iAaccIntro with "M●"; [oSteps|]. iStep 4 as "⊒V ⊒M M●". iDestruct (SeqInv_OmoAuth_acc with "M●") as (?) "[>M● Close]".
  iDestruct (OmoAuth_wf with "M●") as %[OMO_GOOD' _]. apply omo_stlist_length in OMO_GOOD as EQlenST.
  have [st Hst] : is_Some (stlist !! (length omo - 1)) by rewrite lookup_lt_is_Some -EQlenST; lia.
  eapply (omo_write_op_step _ _ _ (length omo - 1) (length E)) in OMO_GOOD' as STEP; last first.
  { by rewrite Nat.sub_add; [|lia]; rewrite EQlenST lookup_app_1_eq. } { by rewrite lookup_app_l; [|lia]. } { by rewrite lookup_app_1_eq. }
  { by rewrite Nat.sub_add; [|lia]; rewrite omo_append_w_write_op omo_write_op_length lookup_app_1_eq. } inversion STEP; subst; try done. inversion DEQ. subst.
  oSteps. iRight. iExists v. oSteps. rewrite last_lookup (_: Init.Nat.pred (length stlist) = length omo - 1); [|lia]. oSteps.
Qed.

Lemma new_queue_spec :
  new_queue_spec' (newQueue newSEQ) QueueLocal QueueInv.
Proof using All.
  iSteps as (N ? sz V ?? q) "⊒V Post _ q↦ HM". replace (Z.to_nat (sz + 3)) with (3 + sz)%nat by lia. rewrite repeat_app !own_loc_na_vec_cons shift_0.
  rewrite !shift_nat_assoc. iDecompose "q↦" as "q0↦ q1↦ q2↦ q↦". iStep 27 as "q0↦ q1↦ q2↦". iDestruct "HM" as "[Hmq _]". rewrite shift_0.

  iMod (append_only_loc_cas_only_from_na_rel with "⊒V q0↦") as (γl0 γsl0 V0 eVl0) "(#⊒V0 & Ml0● & [#⊒Ml0 #H1] & omol0↦ & W1 & #el0✓eVl0 & [%eVl0EV _])"; [done|].
  iMod (append_only_loc_cas_only_from_na_rel with "⊒V0 q1↦") as (γl1 γsl1 V1 eVl1) "(#⊒V1 & Ml1● & [#⊒Ml1 #H2] & omol1↦ & _ & #el1✓eVl1 & [%eVl1EV _])"; [done|].
  iAssert (⌜ V ⊑ V0 ∧ V0 ⊑ V1 ⌝)%I with "[]" as %[LeVV0 LeV0V1]; [rewrite !view_at_unfold !monPred_at_in; iDestruct "H1" as %?; by iDestruct "H2" as %?|].

  set aols := [(γl0,γsl0); (γl1,γsl1)]. set seqs : list (gname * gname * loc) := []. set nodes : queue_state := []. set hlist : list gname := [].
  iMod (mono_list_own_alloc nodes) as (γn) "[Hγn #Hγn◯]". iMod (mono_list_own_alloc hlist) as (γh) "[Hγh #Hγh◯]".
  iAssert (ticket_info q aols 1 0 ∗ ticket_info q aols 0 0)%I with "[omol0↦ omol1↦ Ml0● Ml1●]" as "[Tdeq Tenq]".
  { oSteps. iCombine "omol0↦ omol1↦" as "H". iDestruct (view_at_intro with "H") as "H". iDecompose "H". oSteps; [by rewrite eVl1EV|by rewrite eVl0EV]. }
  iAssert (field_info_inner 1%Qp q seqs sz)%I with "[q2↦]" as "Field"; [by iFrame "q2↦"|].
  (* NOTE: we deliberately put [meta_token] to prevent [SF] being recognized as persistent. Same for [Penq], [Pdeq] *)
  iAssert (slot_field γn seqs sz ∗ meta_token q ⊤)%I with "[$Hmq]" as "[SF Hmq]"; [by rewrite /slot_field|].
  iAssert (perm_bank seqs sz 0 EnqP ∗ meta_token q ⊤)%I with "[$Hmq]" as "[Penq Hmq]"; [rewrite /perm_bank;done|].
  iAssert (perm_bank seqs sz 0 DeqP ∗ meta_token q ⊤)%I with "[$Hmq]" as "[Pdeq Hmq]"; [rewrite /perm_bank;done|].
  iAssert (∃ V, @{V} (([∗ list] x ∈ aols, ∃ γl γsl Ml, OmoEview γl Ml ∗ ⌜ x = (γl, γsl)⌝) ∗
    ([∗ list] x ∈ seqs, ∃ γseq γseqs sloc Mseq, SeqLocal seq (seqN N) γseq sloc Mseq ∗ ⌜ x = (γseq, γseqs, sloc) ⌝)) ∗ ⊒V ∗ ⌜ V0 ⊑ V ⌝)%I with "[]" as "⊒AOLSEQ".
  { iExists V1. subst aols. repeat iSplit; [..|by rewrite big_sepL_nil|by rewrite big_sepL_nil|iFrame "#"|iPureIntro;solve_lat];
    [iExists γl0,γsl0,{[0]}|iExists γl1,γsl1,{[0]}]; by iFrame "#". }

  have [i [Hi [Hi' Hi'']]] : ∃ i, i ≤ sz ∧ Lit 0%Z = #i ∧ i = 0 by exists 0; split_and!; [lia|done|done]. subst aols seqs.
  have [aols [Haols LENaols]] : ∃ aols, aols = [(γl0,γsl0); (γl1,γsl1)] ∧ (length aols = 2)%nat by eexists; split; [done|]; simpl; lia.
  have [seqs [Hseqs LENseqs]] : ∃ seqs : list (gname * gname * loc), seqs = [] ∧ (length seqs = i)%nat by eexists; split; [done|]; simpl; lia.
  rewrite Hi' -!Haols -!Hseqs. clear Hi' Haols Hseqs. iAssert ((q >> (3 + i)) ↦∗ repeat #☠ (sz - i))%I with "[q↦]" as "q↦".
  { subst i. rewrite Nat.add_0_r Nat.sub_0_r. iFrame "q↦". } clear Hi''. iLöb as "IH" forall (i aols seqs Hi LENaols LENseqs) "⊒AOLSEQ Tenq Tdeq SF Pdeq Penq".
  iDecompose "⊒V0". iDecompose "⊒AOLSEQ" as "?? ⊒V". wp_lam. wp_op. destruct (decide (length seqs = sz)) as [<-|NEQ]; last first.
  { rewrite bool_decide_false; [|lia]. oSteps. replace (sz - length seqs) with (1 + (sz - length seqs - 1)) by lia. rewrite repeat_app own_loc_na_vec_cons.
    iDestruct "q↦" as "[q↦ q↦']". rewrite !shift_nat_assoc. replace (Z.to_nat (Z.of_nat (length seqs))) with (length seqs) by lia. wp_apply (new_seq_spec with "⊒V").
    iStep 15 as "?? M● W EnqP DeqP q↦". replace (Z.of_nat (length seqs) + 1)%Z with (Z.of_nat (length seqs + 1)) by lia. set seqs' := seqs ++ [(x1,x2,x5)].
    iApply ("IH" $! (length seqs + 1) aols seqs' with "[] [] [] Post W1 Hγn Hγh [Field q↦] Hmq [q↦'] [] [Tenq] [Tdeq] [SF M●] [Pdeq DeqP] [Penq EnqP]"); try done.
    { iPureIntro. lia. } { iPureIntro. subst seqs'. rewrite app_length /=. lia. } { oSteps. rewrite (_: length seqs + 3 = S (S (S (length seqs)))); [oSteps|lia]. }
    { rewrite (_: sz - length seqs - 1 = sz - (length seqs + 1)); [oSteps|lia]. } { iModIntro. iExists x7. oSteps. rewrite big_sepL_snoc. oSteps. } { oSteps. }
    { iApply (perm_bank_insert with "Pdeq DeqP"). lia. } iApply (perm_bank_insert with "Penq EnqP"). lia. }

  iDestruct (view_at_intro_incl with "Field ⊒V") as "H". iDecompose "H" as "⊒V F1 F2".
  have LeVx1 : V ⊑ x1 by solve_lat.
  set M := {[0%nat]}. set eVinit := mkOmoEvent Init x1 M.

  iMod (@OmoAuth_alloc _ _ _ _ _ eVinit [] _ _ queue_interpretable with "W1") as "H"; [by apply queue_step_Init|done|].
  iDecompose "H" as "????? M●". iDestruct (OmoHbToken_finish with "M●") as "[M● M●']".

  iAssert (field_info x2 q seqs (length seqs))%I with "[F1 F2]" as "Field"; [oSteps|]. iAssert (helping_info N x2 γn q 0 hlist)%I with "[]" as "Helping"; [oSteps|].
  rewrite bool_decide_true; [|done]. iStep 8. iExists _,_,x1. iMod (meta_set _ _ (x5,γn,γh,aols,seqs,length seqs) nroot with "Hmq") as "#HM"; [done|].
  #[local] Typeclasses Opaque ticket_info field_info perm_bank. oSteps. subst nodes. rewrite /nodes_info. oSteps.
Qed.

Local Instance elem_of_aol_persistent aols idx x : Persistent (elem_of_aol aols idx x) := _.
Local Instance elem_of_aol_timeless aols idx x : Timeless (elem_of_aol aols idx x) := _.
#[local] Typeclasses Opaque elem_of_aol slot_info_case.
#[local] Typeclasses Transparent ticket_info field_info perm_bank.
#[local] Remove Hints biabd_big_sepL_mono : typeclass_instances.

#[global] Instance enqueue_dspec N γg q V M (v : Z) :
  SPEC ⟨ ⊤ , ↑N , ↑histN⟩ γs E omo stlist, <<
    ⊒V ∗ QueueLocal N γg q M ∗
    ⌜ N ## histN ∧ (0 < v)%Z ⌝
  ¦
    ▷ QueueInv γg γs q E omo stlist > >
      (enqueue enqueueWithTicket) [ #q; #v ]
  << RET #☠;
      emp
      ¦
      (
      ∃ V', ask_for V' ∗ (* ask for dv_out *)
      ∃ M' omo' stlist' st,
      let E' := E ++ [mkOmoEvent (Enq v) V' M'] in
      let opId := length E in
      ▷ QueueInv γg γs q E' omo' stlist' ∗ OmoTokenW γg opId ∗ OmoUB γg M opId ∗
      ⊒V' ∗ @{V'} QueueLocal N γg q M' ∗ ⌜ V ⊑ V' ∧ M ⊆ M' ∧ omo' = omo_append_w omo opId [] ∧ stlist' = stlist ++ [st] ⌝)
    > >.
Proof using All.
  iStep 9 as "?????? Inv". iLöb as "IH". iSteps as "? HM ?????????????? M●". iExists None. iStep 11 as "?? BIGx5 ???????????? AU". iDecompose "M●".
  oSteps. rewrite -H16 /= in H18. subst x11. oSteps. iInv "Inv" as "H". oSteps. iDecompose "H" as "????????????????????????? BIG1 BIG2".
  rewrite shift_0. oSteps. iExists None. iStep 15 as "?"|"??????????????? BIG2"; [oSteps|]. iDestruct (view_at_elim with "[] AU") as "AU"; [oSteps|].

  iApply (fupd_intro_goal _ _ (x0 #☠)%I). iStep. iMod "AU" as (????) "[>H HAUcl]".
  iDestruct (atomic.diaframe_close_right with "HAUcl") as "HAU". iDecompose "H".
  iStep. iExists x63. oSteps. iExists _. iSplitR; [iPureIntro; apply queue_step_Enq; try done; instantiate (1 := M); set_solver-|].
  iStep as "?????? M●". iSplitR; [iModIntro; iApply big_sepS_subseteq; [|by iApply (@OmoUB_singleton qevent)]; set_solver-|]. iStep.
  set x45' := x45 ++ [(length x11, v, x63, {[length x11]} ∪ M)].
  iMod (mono_list_auth_own_update x45' with "[$]") as "[●x45 #◯x45']"; [by apply prefix_app_r|].
  iDestruct (@mono_list_idx_own_get _ _ _ _ x45' (length x45) with "[$]") as "#IDX"; [by subst; rewrite lookup_app_1_eq|].
  iAssert (|={_}=> ∃ E omo stlist, helping_info N γg x2 q (length x45 + 1)%nat x46 ∗ OmoAuth γg x1 (1/2) E omo stlist _ ∗
    ⌜ last stlist = Some (drop (length x46) x45') ⌝)%I with "[M● BIG1 BIG2]" as ">H"; [|iDecompose "H"].
  { destruct (le_lt_dec (length x46) (length x45)) as [LE|LT].
    { oSteps. do 2 (rewrite take_ge; [|lia]). oSteps. do 2 (rewrite (drop_ge x46); [|lia]). oSteps. by subst x45'; rewrite drop_app_le. }
    have [γi Hγi] : is_Some (x46 !! (length x45)) by rewrite lookup_lt_is_Some. oSteps.
    rewrite plus_1_S. erewrite take_S_r; [|done]. oSteps. erewrite (drop_S x46); [|done]. iDecompose "BIG2" as "H1 H2 H3 H4 H5 H6 H7 H8 H9 BIG2".
    rewrite !view_at_objective_iff. iDecompose "H1" as "H1 H3". iInv "H6" as "H". iDecompose "H" as "Hγi".

    iAssert (|={_}=> @{x67 ⊔ x63} (▷ x71 v ∗ ⎡ghost_var γi 1 Accepted⎤ ∗ (∃ E omo stlist, OmoAuth γg x1 (1/2) E omo stlist _ ∗
      ⌜ last stlist = Some (drop (length x46) x45') ⌝)))%I with "[HM H7 H8 H9 M● Hγi]" as ">H".
    { iDestruct (view_at_mono_2 _ (x67 ⊔ x63) with "H7") as "H7"; [solve_lat|].
      iRename select (@{x8} OmoEview_or_empty _ M)%I into "⊒M". iRename select (OmoEinfo _ (length x11) _)%I into "H".
      iCombine "M● H1 H2 H3 H5 H8 H9 HM ⊒M H Hγi ◯x45'" as "RES". iDestruct (view_at_objective_iff _ (x67 ⊔ x63) with "RES") as "RES".
      iAssert (@{x67 ⊔ x63} ⊒(x67 ⊔ x63))%I with "[]" as "#H'"; [done|]. iCombine "H' H7 RES" as "RES". rewrite -view_at_fupd.
      iApply (view_at_mono with "RES"); [done|]. iStepSafest as "?????????? AU ? Hγi ? [Hγi' #◯x47']".
      iDestruct (ghost_var_agree with "Hγi Hγi'") as %<-. iCombine "Hγi Hγi'" as "Hγi".
      iMod "AU" as (????) "[>H HAUcl]". iDestruct (atomic.diaframe_close_right_quant with "HAUcl") as "HAU". iDecompose "H".
      iStepSafest. iExists (x67 ⊔ x63). oSteps. iExists _. iSplitR.
      { iPureIntro. rewrite drop_ge; [|lia]. simpl. apply queue_step_Deq; try done; simpl; [solve_lat|].
        rewrite !app_length /=. instantiate (1 := ({[length x11]} ∪ x70 ∪ M)). set_solver-. }

      oSteps. rewrite !app_length /=. iDestruct (@OmoEview_get_from_Einfo qevent _ _ _ _ _ (length x11 + 1) with "[$]") as "H".
      iDecompose "H". iSplitR. { iApply big_sepS_subseteq; [|by iApply (@OmoUB_singleton qevent)]; set_solver-. }
      oSteps. iMod (ghost_var_update Accepted with "[$]") as "H"; oSteps.

      subst x45'. rewrite drop_ge; [done|]. rewrite app_length /=. lia. }

    iDecompose "H" as "? [Hγi Hγi']". rewrite !view_at_objective_iff. oSteps. iSplitL "BIG2"; [iModIntro|oSteps;rewrite view_at_later;oSteps].
    iApply (big_sepL_impl with "BIG2"). iModIntro. iIntros (???) "H". iDestruct "H" as (???????) "H".
    replace (S (length x45 + k)) with (length x45 + S k) by lia. repeat iExists _. iFrame "H". }

  iAssert (⌜ (x10 + 1 = length x41)%nat ⌝)%I with "[-]" as "%EQlen".
  { rewrite -H43 in H42. inversion H42. have ? : x10 = length x41 - 1 by lia. subst x10. rewrite Nat.sub_add; [|lia]. done. }

  oSteps; [iPureIntro; rewrite app_length /=; lia|by replace (Z.of_nat x10 + 1)%Z with (Z.of_nat (length x41)) by lia|].
  iDestruct (extract_one_ticket _ _ _ EnqP with "[$]") as "H"; [done..|]. iDecompose "H". rewrite app_length /=. oSteps.
  do 2 (iSplitR; [shelve|]). oSteps. iAssert (⌜ x10 = length x45 ⌝)%I with "[-]" as %?; [iPureIntro; lia|]. subst x10.

  rewrite (big_sepL_lookup (λ idx x10, ((q >> (idx + 3)) ↦{x24/2} #(LitLoc x10.2))%I) x5); [|exact H52]. simpl.
  rewrite shift_nat_assoc (_: Z.to_nat 3 + Z.to_nat (length x45 `rem` length x5) = Z.to_nat (length x45 `rem` length x5) + 3); [|lia].
  have ? : (0 ≤ Z.of_nat (length x45) `quot` Z.of_nat (length x5))%Z by apply Zquot_le_lower_bound; lia. oSteps.

  set turn := Z.to_nat ((length x45) `quot` (length x5)). replace (Z.of_nat (length x45) `quot` Z.of_nat (length x5))%Z with (Z.of_nat turn); [|lia].
  rewrite (big_sepL_lookup _ x5); [|exact H52]. iDecompose "BIGx5". oSteps. iInv "Inv" as "H".
  iDecompose "H" as "???????????????? M● ????? SF". iDestruct (big_sepL_lookup_acc with "SF") as "SF"; [exact H52|]. iDecompose "SF". iDecompose "M●".
  oSteps. iSplitR; [|oSteps]. #[local] Typeclasses Transparent slot_info_case. iRight. oSteps.
  rewrite (_: length x5 * turn + Z.to_nat (length x45 `rem` length x5) = length x45); [oSteps|lia].
  Unshelve. all: try pure_solver.trySolvePure. all: try (simpl; done).
Qed.

#[global] Instance dequeue_dspec N γg q V M :
  SPEC ⟨ ⊤ , ↑N , ↑histN⟩ γs E omo stlist, <<
    ⊒V ∗ QueueLocal N γg q M ∗
    ⌜ N ## histN ⌝
  ¦
    ▷ QueueInv γg γs q E omo stlist > >
      (dequeue dequeueWithTicket) [ #q ]
  << (v : Z), RET #v;
      emp
      ¦
      (
      ∃ V', ask_for V' ∗ (* ask for dv_out *)
      ∃ M' omo' stlist' st,
      let E' := E ++ [mkOmoEvent (Deq v) V' M'] in
      let opId := length E in
      ▷ QueueInv γg γs q E' omo' stlist' ∗ OmoTokenW γg opId ∗ OmoUB γg M opId ∗
      ⊒V' ∗ @{V'} QueueLocal N γg q M' ∗ ⌜ V ⊑ V' ∧ M ⊆ M' ∧ omo' = omo_append_w omo opId [] ∧ stlist' = stlist ++ [st] ∧ (0 < v)%Z ⌝)
    > >.
Proof using All.
  iStep 9 as "???? He0 ? Inv". iLöb as "IH". iSteps as "? HM ?????????????? M● ?? M●x6". iExists None. iStep 11 as "⊒M BIGx4 BIGx5 ???????????? AU".
  iDecompose "M●x6". oSteps. rewrite -H15 /= in H17. subst x11. iSteps as "?????????????? M● ?? M●x43 ?????? BIG1". iExists None.
  iStep 15 as "?"|"??????????????? BIG2 W"; iDecompose "M●x43"; [oSteps|]. iMod UTok_alloc as (γu) "Hγu". iMod (ghost_var_alloc Pending) as (γi) "Hγi".
  set x50' := x50 ++ [γi]. iMod (mono_list_auth_own_update x50' with "[$]") as "[●x50' #◯x50']"; [by apply prefix_app_r|].
  iDestruct (@mono_list_lb_own_get queue_state_inner with "[$]") as "#◯x49".

  iAssert (|={_}=> ∃ E omo stlist, inv (helpN N) (helping_res x2 γi γu (length x50) x8 (λ (x : Z), x0 #x)) ∗ OmoAuth γg x1 (1/2)%Qp E omo stlist _ ∗
    ⌜ last stlist = Some (drop (length x50') x49) ⌝ ∗ helping_info N γg x2 q (length x49) x50')%I with "[AU W BIG1 BIG2 M● Hγi]" as ">H"; [|iDecompose "H"].
  { destruct (le_lt_dec (length x49) (length x50)) as [LE|LT].
    - iAssert (@{x8} atomic_update_deq N γg q V M (λ (x : Z), x0 #x))%I with "[AU]" as "AU"; [|iDestruct "Hγi" as "[Hγi Hγi']"; subst x50'].
      { iDestruct (view_at_objective_iff _ x8 with "Inv") as "Inv@x8". iCombine "Inv@x8 AU" as "RES". iApply (view_at_mono with "RES"); [done|].
        oSteps; [iRight|iLeft; iExists x64]; oSteps. }
      iMod (inv_alloc (helpN N) _ (helping_res x2 γi γu (length x50) x8 (λ (x : Z), x0 #x)) with "[Hγi']") as "#HInv"; oSteps.
      { iPureIntro. rewrite app_length /= drop_ge; [|lia]. rewrite drop_ge in H26; [|lia]. done. }
      rewrite take_app_le; [|done]. oSteps. rewrite drop_app_le; [|lia].
      rewrite (_: length x50 = length x49 + length (drop (length x49) x50)); [|by rewrite drop_length; lia]. iModIntro. oSteps.
    - have [nenq Henq] : is_Some (x49 !! (length x50)) by rewrite lookup_lt_is_Some. iDestruct (mono_list_idx_own_get with "◯x49") as "IDX"; [exact Henq|].
      iDestruct (big_sepL_lookup _ x49 with "[$]") as "H"; [exact Henq|]. iDecompose "H" as "? H1".

      set V' := x8 ⊔ (x65.(sync)). iCombine "Inv HM M● H1 W ⊒M BIGx4 BIGx5 He0" as "RES". iDestruct (view_at_objective_iff _ V' with "RES") as "RES".
      iDestruct (view_at_mono_2 _ V' with "AU") as "AU"; [solve_lat|]. iAssert (@{V'} ⊒V')%I with "[]" as "H6"; [done|]. iCombine "RES AU H6" as "RES".
      iAssert (|={_}=> @{V'} (x0 #x64 ∗ (∃ E omo stlist, OmoAuth γg x1 (1/2)%Qp E omo stlist _ ∗ ⌜ last stlist = Some (drop (length x50') x49) ⌝)))%I
        with "[RES]" as ">H"; [|iDecompose "H" as "HΦ"; iMod (ghost_var_update Accepted with "Hγi") as "[Hγi Hγi']"; iClear "BIG2"].
      { rewrite -view_at_fupd. iApply (view_at_mono with "RES"); [done|]. iStep as "???????????? AU".
        iMod "AU" as (????) "[>H HAUcl]". iDestruct (atomic.diaframe_close_right_quant with "HAUcl") as "HAU". iDecompose "H".
        oSteps. iExists V'. oSteps. iExists _. iSplitR; [instantiate (2 := {[x61]} ∪ x65.(eview) ∪ M)|]; [|oSteps].
        { iPureIntro. erewrite drop_S; [|done]. apply queue_step_Deq; try done; simpl; [solve_lat|set_solver-]. }
        iSplitR; [iModIntro; iApply big_sepS_subseteq; [|by iApply (@OmoUB_singleton qevent)]; set_solver-|oSteps].
        { iPureIntro. solve_lat. } { solve_lat. } { subst x50'. rewrite app_length /= plus_1_S. done. } }
      iMod (inv_alloc (helpN N) _ (helping_res x2 γi γu (length x50) x8 (λ (x : Z), x0 #x)) with "[Hγi' HΦ]") as "#HInv"; [oSteps|].
      rewrite view_at_objective_iff. iModIntro. oSteps. subst x50'. rewrite take_app_ge; [|lia]. rewrite take_ge; [|lia].
      rewrite drop_app_ge; [|lia]. rewrite take_ge; [|simpl; lia]. rewrite drop_ge; [|simpl; lia]. oSteps. }

  iAssert (⌜ (x10 + 1 = length x57)%nat ⌝)%I with "[-]" as "%EQlen"; [|oSteps; [iPureIntro; subst x50'; rewrite app_length /=; lia|..]].
  { rewrite -H42 in H41. inversion H41. have ? : x10 = length x57 - 1 by lia. subst x10. rewrite Nat.sub_add; [|lia]. done. }
  { replace (Z.of_nat x10 + 1)%Z with (Z.of_nat (length x57)) by lia. done. }
  iDestruct (extract_one_ticket _ _ _ DeqP with "[$]") as "H"; [done..|]. rewrite app_length /=. oSteps; [iPureIntro;subst x50';by rewrite app_length /= in H45|].

  have ? : x10 = length x50 by lia. subst x10. rewrite (big_sepL_lookup (λ idx x10, ((q >> (idx + 3)) ↦{x24/2} #(LitLoc x10.2))%I) x5); [|exact H50]. simpl.
  rewrite shift_nat_assoc (_: Z.to_nat 3 + Z.to_nat (length x50 `rem` length x5) = Z.to_nat (length x50 `rem` length x5) + 3); [|lia].
  have ? : (0 ≤ Z.of_nat (length x50) `quot` Z.of_nat (length x5))%Z by apply Zquot_le_lower_bound; lia. oSteps.

  set turn := Z.to_nat ((length x50) `quot` (length x5)). replace (Z.of_nat (length x50) `quot` Z.of_nat (length x5))%Z with (Z.of_nat turn); [|lia].
  rewrite (big_sepL_lookup _ x5); [|exact H50]. iDecompose "BIGx5". oSteps. iInv "Inv" as "H".
  iDecompose "H" as "?????????????? ●x80 ? M● ????? SF ?? BIG1". iDecompose "M●". iDestruct (big_sepL_lookup_acc with "SF") as "SF"; [exact H50|].
  iDecompose "SF"; [oSteps;rewrite -H63 in H66;inversion H66|]. iStep 2; [oSteps|]. iStep 3. rewrite -H63 in H67. inversion H67. subst x96. simpl.
  rewrite (_: length x5 * turn + Z.to_nat (length x50 `rem` length x5) = length x50); [|lia]. iDestruct (mono_list_auth_idx_lookup with "●x80 [$]") as %Hx80.
  apply lookup_lt_Some in Hx80 as LT. iDestruct (mono_list_auth_lb_valid with "[$] ◯x50'") as %[_ Hx50'].
  iDestruct (big_sepL_lookup_acc _ _ (length x50) with "BIG1") as "[Inner BIG1]"; [|iDecompose "Inner" as "Hγi"].
  { rewrite lookup_take; [|done]. eapply prefix_lookup_Some; try done. subst x50'. rewrite lookup_app_1_eq. done. }

  iRename select (inv (helpN N) _)%I into "HInv". iInv "HInv" as "H". iDecompose "H" as "Hγi' CASE". iDestruct (ghost_var_agree with "Hγi Hγi'") as %<-.
  iCombine "Hγi Hγi'" as "Hγi". iMod (ghost_var_update Acked with "Hγi") as "[Hγi Hγi']".
  destruct x96; [done|iDecompose "CASE"|by iDestruct (UTok_unique with "Hγu CASE") as ">%"].
  iDestruct (mono_list_idx_agree _ _ (x97, x95, x98, x99) (x96, x102, x103, x107) with "[$] [$]") as "H". iDecompose "H". oSteps.
  have ? : x8 ⊔ x103 ⊑ x63 ⊔ x100 by solve_lat. oSteps.
Qed.

#[local] Typeclasses Opaque QueueLocal QueueInv.

Lemma enqueue_spec :
  enqueue_spec' (enqueue enqueueWithTicket) QueueLocal QueueInv.
Proof using All. oSteps; [iRight; oSteps|]. iLeft. unseal_diaframe. rewrite (_: x5 ⊔ x9 = x9); [|solve_lat]. oSteps. Qed.

Lemma dequeue_spec :
  dequeue_spec' (dequeue dequeueWithTicket) QueueLocal QueueInv.
Proof using All. oSteps; [iRight; oSteps|]. iLeft. unseal_diaframe. rewrite (_: x5 ⊔ x8 = x8); [|solve_lat]. oSteps. Qed.

End MpmcQueue.

Definition mpmcqueue_impl `{!noprolG Σ, !atomicG Σ, !mpmcqueueG Σ} (seq : seq_composition_spec Σ)
  : mpmcqueue_spec Σ := {|
    spec_mpmcqueue_composition.QueueInv_Linearizable := QueueInv_Linearizable_instance;
    spec_mpmcqueue_composition.QueueInv_OmoAuth_acc := QueueInv_OmoAuth_acc_instance;
    spec_mpmcqueue_composition.QueueLocal_OmoEview := QueueLocal_OmoEview_instance seq;

    spec_mpmcqueue_composition.new_queue_spec := new_queue_spec seq;
    spec_mpmcqueue_composition.enqueue_spec := enqueue_spec seq;
    spec_mpmcqueue_composition.dequeue_spec := dequeue_spec seq;
  |}.
