From iris.bi.lib Require Import fractional.
From iris.algebra Require Export auth gmap agree lib.dfrac_agree.
From iris.proofmode Require Import proofmode.

From gpfsl.base_logic Require Import vprop history.
From gpfsl.logic Require Import atomic_cmra.
From gpfsl.lang Require Import notation.

Require Import iris.prelude.options.

Implicit Types (ζ : absHist) (t : time) (v : val) (V : view) (q: Qp).

Local Existing Instance atomic_inG.

Section ghost_defs.
Context `{!noprolG Σ, !atomicG Σ}.
Local Notation iProp := (iProp Σ).
Local Notation vProp := (vProp Σ).

Definition at_last_na γ (Va : view) : iProp :=
  own γ ((ε, (ε, Some $ to_agree Va)) : atomicR).

(* TODO: we might also want a counting permission here *)
Definition at_exclusive_write γ (tx: time) q : iProp :=
  own γ ((ε, (◯F{q} (to_agree tx), ε)) : atomicR).
Definition at_auth_exclusive_write γ (tx : time) : iProp :=
  own γ ((ε, (●F (to_agree tx), ε)) : atomicR).

(* ◯ toHistBaseUR ζ is needed here so that at_writer implies at_reader, instead
  of needing a bupd to fork at_reader. *)
Definition at_writer_base γ ζ q : iProp :=
  own γ ((●{#q} toHistBaseUR ζ ⋅ ◯ toHistBaseUR ζ, (ε,ε)) : atomicR).
Definition at_writer γ ζ      : iProp := at_writer_base γ ζ (3/4).
Definition at_auth_writer γ ζ : iProp := at_writer_base γ ζ (1/4).

Definition at_reader γ ζ      : iProp := own γ ((◯ toHistBaseUR ζ, (ε,ε)) : atomicR).

Definition at_auth γ ζ (tx : time) (Va : view): iProp :=
  at_auth_writer γ ζ ∗ at_auth_exclusive_write γ tx ∗ at_last_na γ Va.

End ghost_defs.

Section props.
Context `{!noprolG Σ, !atomicG Σ}.
Local Notation iProp := (iProp Σ).
Local Notation vProp := (vProp Σ).

Implicit Types (P Q R : vProp).

#[global] Instance at_reader_persistent γ ζ: Persistent (at_reader γ ζ) := _.

#[local] Ltac rewrite_own_op :=
  rewrite -?own_op -?pair_op -?auth_auth_dfrac_op
          -?Some_op -?frac_auth_frag_op -?pair_op
          ?histBase_idemp ?agree_idemp ?left_id ?right_id.
#[local] Ltac intro_own_valid :=
  apply bi.wand_intro_r; rewrite_own_op; rewrite own_valid.

Lemma at_full_auth_unfold γ ζ tx Va :
  at_auth γ ζ tx Va ⊣⊢
    own γ ((●{#1/4} toHistBaseUR ζ ⋅ ◯ toHistBaseUR ζ,
           (●F (to_agree tx), Some $ to_agree Va)) : atomicR).
Proof.
  rewrite /at_auth /at_auth_writer /at_auth_exclusive_write /at_last_na
          /at_writer_base.
  by rewrite_own_op.
Qed.

(* at_exclusive_write *)
#[global] Instance at_exclusive_write_fractional γ t :
  Fractional (at_exclusive_write γ t)%I.
Proof. intros ??. by rewrite_own_op. Qed.
#[global] Instance at_exclusive_write_asfractional γ t q :
  AsFractional (at_exclusive_write γ t q) (λ q, at_exclusive_write γ t q)%I q.
Proof. by apply : Build_AsFractional. Qed.

Lemma at_exclusive_write_agree γ (t1 t2: time)q1 q2 : 
  at_exclusive_write γ t1 q1 -∗ at_exclusive_write γ t2 q2 -∗
  ⌜(q1 + q2 ≤ 1)%Qp ∧ t1 = t2⌝.
Proof.
  intro_own_valid.
  by iDestruct 1 as %(_ & [? ?%to_agree_op_valid_L]%frac_auth_frag_valid & _).
Qed.
Lemma at_auth_exclusive_write_agree γ (t1 t2: time) q :
  at_auth_exclusive_write γ t1 -∗ at_exclusive_write γ t2 q -∗
  ⌜t1 = t2⌝.
Proof.
  intro_own_valid.
  by iDestruct 1 as %(_ & ?%frac_auth_included_total%to_agree_included & _).
Qed.
Lemma at_full_auth_exclusive_write_agree γ (t1 t2: time) ζ1 V q :
  at_auth γ ζ1 t1 V -∗ at_exclusive_write γ t2 q -∗ ⌜t1 = t2 ⌝.
Proof. iIntros "(_ & SA & _)". by iApply at_auth_exclusive_write_agree. Qed.

Lemma at_exclusive_write_exclusive γ t1 t2 :
  at_exclusive_write γ t1 1 -∗ at_exclusive_write γ t2 1 -∗ False.
Proof.
  iIntros "E1 E2". by iDestruct (at_exclusive_write_agree with "E1 E2") as %[].
Qed.

Lemma at_exclusive_write_join γ t1 t2 q1 q2 :
  at_exclusive_write γ t1 q1 -∗ at_exclusive_write γ t2 q2 -∗
  at_exclusive_write γ t1 (q1 + q2).
Proof.
  iIntros "S1 S2". iDestruct (at_exclusive_write_agree with "S1 S2") as %[? <-].
  iCombine "S1" "S2" as "S". iFrame.
Qed.

Lemma at_exclusive_write_update γ t t':
  at_auth_exclusive_write γ t -∗ at_exclusive_write γ t 1%Qp
  ==∗ at_auth_exclusive_write γ t' ∗ at_exclusive_write γ t' 1%Qp.
Proof.
  apply bi.wand_intro_r. rewrite_own_op.
  apply own_update. apply prod_update; [done|]. apply prod_update; [|done].
  by apply frac_auth_update_1.
Qed.

Lemma at_auth_exclusive_write_update γ t ζ Va t':
  at_auth γ ζ t Va -∗ at_exclusive_write γ t 1%Qp
  ==∗ at_auth γ ζ t' Va ∗ at_exclusive_write γ t' 1%Qp.
Proof. iIntros "($ & SA & $)". by iApply at_exclusive_write_update. Qed.

(* at_last_na *)
#[global] Instance at_last_na_persistent γ V : Persistent (at_last_na γ V) := _.

Lemma at_last_na_agree γ (V1 V2: view) :
  at_last_na γ V1 -∗ at_last_na γ V2 -∗ ⌜V1 = V2⌝.
Proof.
  intro_own_valid. iDestruct 1 as %(_&_&VAL). move: VAL=> /to_agree_op_inv_L //.
Qed.

Lemma at_last_na_dup γ V :
  at_last_na γ V ∗ at_last_na γ V ⊣⊢ at_last_na γ V.
Proof. by rewrite -bi.persistent_sep_dup. Qed.

Lemma at_auth_at_last_na_agree γ ζ tx Va Va':
  at_auth γ ζ tx Va -∗ at_last_na γ Va' -∗ ⌜Va = Va'⌝.
Proof. iIntros "(_&_&NA)". by iApply at_last_na_agree. Qed.

Lemma at_auth_fork_at_last_na γ ζ tx Va :
  at_auth γ ζ tx Va -∗ at_last_na γ Va.
Proof. by iIntros "(_&_&$)". Qed.

(* at_writer *)
Instance at_writer_base_fractional γ ζ : Fractional (at_writer_base γ ζ)%I.
Proof.
  intros ??. rewrite_own_op.
  by rewrite -cmra_assoc (cmra_assoc (◯ _)) (cmra_comm (◯ _)) -cmra_assoc
            (cmra_assoc (●{_} _) (●{_} _)) -auth_auth_dfrac_op -auth_frag_op
            histBase_idemp.
Qed.

Lemma at_writer_base_valid γ ζ1 ζ2 q1 q2 :
  at_writer_base γ ζ1 q1 -∗ at_writer_base γ ζ2 q2 -∗
  ⌜(q1 + q2 ≤ 1)%Qp ∧ ζ1 = ζ2⌝.
Proof.
  intro_own_valid.
  rewrite -cmra_assoc (cmra_assoc (◯ _)) (cmra_comm (◯ _)) -cmra_assoc
          (cmra_assoc (●{_} _) (●{_} _)).
  by iDestruct 1 as %[(?&?%toHistBase_inj&_)%cmra_valid_op_l%auth_auth_dfrac_op_valid _].
Qed.

Lemma at_writer_exclusive γ ζ1 ζ2 : at_writer γ ζ1 -∗ at_writer γ ζ2 -∗ False.
Proof. iIntros "W1 W2". by iDestruct (at_writer_base_valid with "W1 W2") as %[]. Qed.

Lemma at_auth_writer_exact γ ζ ζ' :
  at_auth_writer γ ζ -∗ at_writer γ ζ' -∗ ⌜ζ = ζ'⌝.
Proof. iIntros "W1 W2". by iDestruct (at_writer_base_valid with "W1 W2") as %[]. Qed.

Lemma at_auth_all_writer_exact γ ζ ζ' tx Va:
  at_auth γ ζ tx Va -∗ at_writer γ ζ' -∗ ⌜ζ = ζ'⌝.
Proof. iIntros "(AW & EX & NA)". by iApply at_auth_writer_exact. Qed.

Lemma at_writer_base_update γ ζ ζ' (Sub: ζ ⊆ ζ'):
  at_writer_base γ ζ 1 ==∗ at_writer_base γ ζ' 1.
Proof.
  apply own_update, prod_update; simpl; [|done].
  by apply auth_update, toHistBase_local_update.
Qed.
Lemma at_writer_update γ ζ ζ' (Sub: ζ ⊆ ζ'):
  at_auth_writer γ ζ -∗ at_writer γ ζ ==∗ at_auth_writer γ ζ' ∗ at_writer γ ζ'.
Proof.
  apply bi.wand_intro_r. rewrite -!fractional Qp.quarter_three_quarter.
  by apply at_writer_base_update.
Qed.
Lemma at_writer_update' γ ζ0 ζ ζ' (Sub: ζ ⊆ ζ'):
  at_auth_writer γ ζ0 -∗ at_writer γ ζ ==∗ at_auth_writer γ ζ' ∗ at_writer γ ζ'.
Proof.
  iIntros "oA W". iDestruct (at_auth_writer_exact with "oA W") as %->.
  by iApply (at_writer_update with "oA W").
Qed.

(* writers and readers *)
Lemma at_writer_base_latest γ q ζ1 ζ2 :
  at_writer_base γ ζ2 q -∗ at_reader γ ζ1 -∗ ⌜ζ1 ⊆ ζ2⌝.
Proof.
  intro_own_valid.
  rewrite -(cmra_assoc (●{_} toHistBaseUR ζ2)).
  iDestruct 1 as %[(?&INCL&_)%auth_both_dfrac_valid_discrete _].
  iPureIntro. apply toHistBase_included.
  by etrans; [apply cmra_included_r|apply INCL].
Qed.

Lemma at_writer_latest γ ζ1 ζ2 : at_writer γ ζ2 -∗ at_reader γ ζ1 -∗ ⌜ζ1 ⊆ ζ2⌝.
Proof. by apply at_writer_base_latest. Qed.

Lemma at_auth_writer_latest γ ζ1 ζ2 :
  at_auth_writer γ ζ2 -∗ at_reader γ ζ1 -∗ ⌜ζ1 ⊆ ζ2⌝.
Proof. by apply at_writer_base_latest. Qed.

Lemma at_auth_reader_latest γ tx Va ζ1 ζ2 :
  at_auth γ ζ2 tx Va -∗ at_reader γ ζ1 -∗ ⌜ζ1 ⊆ ζ2⌝.
Proof. iIntros "[? _]". by iApply at_auth_writer_latest. Qed.

Lemma at_reader_extract γ ζ1 ζ2 (Sub: ζ2 ⊆ ζ1) :
  at_reader γ ζ1 -∗ at_reader γ ζ2.
Proof.
  apply own_mono, prod_included. split; [|done].
  by apply auth_frag_mono, toHistBase_included.
Qed.

Lemma at_reader_join γ ζ1 ζ2 :
  at_reader γ ζ1 -∗ at_reader γ ζ2 -∗ at_reader γ (ζ1 ∪ ζ2).
Proof.
  iIntros "R1 R2". iCombine "R1 R2" as "R".
  iDestruct (own_valid with "R") as %[VAL _].
  move : VAL => /= /auth_frag_valid => VAL.
  by rewrite toHistBase_op_valid //.
Qed.
Lemma at_reader_union_eq γ ζ1 ζ2 :
  at_reader γ ζ1 -∗ at_reader γ ζ2 -∗ ⌜ ζ1 ∪ ζ2 = ζ2 ∪ ζ1 ⌝.
Proof.
  iIntros "R1 R2". iCombine "R1 R2" as "R".
  iDestruct (own_valid with "R") as %[VAL _].
  move : VAL => /= /auth_frag_valid => VAL.
  iPureIntro. by apply toHistBase_valid_union.
Qed.

Lemma at_writer_base_fork_at_reader γ q ζ :
  at_writer_base γ ζ q -∗ at_reader γ ζ.
Proof. by iIntros "[_ $]". Qed.
Lemma at_writer_base_fork_at_reader_sub γ q ζ ζ' (Sub: ζ' ⊆ ζ):
  at_writer_base γ ζ q -∗ at_reader γ ζ'.
Proof. rewrite at_writer_base_fork_at_reader. by apply at_reader_extract. Qed.
Lemma at_writer_base_fork_at_reader_singleton γ q ζ t vV
  (HL: ζ !! t = Some vV):
  at_writer_base γ ζ q -∗ at_reader γ {[t:= vV]}.
Proof. by apply at_writer_base_fork_at_reader_sub, map_singleton_subseteq_l. Qed.
Lemma at_writer_base_at_reader_singleton_sub γ q ζ t vV:
  at_writer_base γ ζ q -∗ at_reader γ {[t := vV]} -∗ ⌜ζ !! t = Some vV⌝.
Proof.
  iIntros "W R". iDestruct (at_writer_base_latest with "W R") as %SUB.
  iPureIntro. move : (SUB t). rewrite lookup_singleton.
  by case lookup eqn:Eq => [/=->|//].
Qed.

Lemma at_writer_fork_at_reader γ ζ : at_writer γ ζ -∗ at_reader γ ζ.
Proof. by apply at_writer_base_fork_at_reader. Qed.
Lemma at_writer_fork_at_reader_sub γ ζ ζ' (Sub: ζ' ⊆ ζ):
  at_writer γ ζ -∗ at_reader γ ζ'.
Proof. by apply at_writer_base_fork_at_reader_sub. Qed.
Lemma at_writer_fork_at_reader_singleton γ ζ t vV (HL: ζ !! t = Some vV):
  at_writer γ ζ -∗ at_reader γ {[t:= vV]}.
Proof. by apply at_writer_base_fork_at_reader_singleton. Qed.
Lemma at_writer_at_reader_singleton_sub γ ζ t vV:
  at_writer γ ζ -∗ at_reader γ {[t := vV]} -∗ ⌜ζ !! t = Some vV⌝.
Proof. by apply at_writer_base_at_reader_singleton_sub. Qed.

Lemma at_auth_writer_fork_at_reader γ ζ :
  at_auth_writer γ ζ -∗ at_reader γ ζ.
Proof. by apply at_writer_base_fork_at_reader. Qed.
Lemma at_auth_writer_fork_at_reader_sub γ ζ ζ' (Sub: ζ' ⊆ ζ) :
  at_auth_writer γ ζ -∗ at_reader γ ζ'.
Proof. by apply at_writer_base_fork_at_reader_sub. Qed.
Lemma at_auth_writer_fork_at_reader_singleton γ ζ t vV
  (HL: ζ !! t = Some vV) :
  at_auth_writer γ ζ -∗ at_reader γ {[t:= vV]}.
Proof. by apply at_writer_base_fork_at_reader_singleton. Qed.
Lemma at_auth_writer_at_reader_singleton_sub γ ζ t vV :
  at_auth_writer γ ζ -∗ at_reader γ {[t := vV]} -∗ ⌜ζ !! t = Some vV⌝.
Proof. by apply at_writer_base_at_reader_singleton_sub. Qed.

Lemma at_auth_fork_at_reader γ ζ tx Va :
  at_auth γ ζ tx Va -∗ at_reader γ ζ.
Proof. iIntros "(?&_)". by iApply at_auth_writer_fork_at_reader. Qed.

Lemma at_auth_at_reader_singleton_sub γ ζ tx Va t vV:
  at_auth γ ζ tx Va -∗ at_reader γ {[t := vV]} -∗ ⌜ζ !! t = Some vV⌝.
Proof. iIntros "[? ?]". by iApply at_auth_writer_at_reader_singleton_sub. Qed.

Lemma at_writer_base_update_insert γ ζ t vV (FRESH: ζ !! t = None) :
  at_writer_base γ ζ 1 ==∗
  at_writer_base γ (<[t := vV]> ζ) 1 ∗ at_reader γ ({[ t := vV ]}).
Proof.
  iIntros "W". iMod (at_writer_base_update _ _ (<[t := vV]> ζ) with "W") as "W".
  - by apply insert_subseteq.
  - iDestruct (at_writer_base_fork_at_reader_sub with "W") as "#$";
      last by iFrame "W".
    by apply insert_mono, gmap_subseteq_empty.
Qed.

Lemma at_writer_update_insert_at_reader γ ζ0 ζ t vV (FRESH: ζ !! t = None) :
  at_auth_writer γ ζ0 -∗ at_writer γ ζ ==∗
    at_auth_writer γ (<[t := vV]> ζ) ∗ at_writer γ (<[t := vV]> ζ) ∗
    at_reader γ ({[ t := vV ]}).
Proof.
  iIntros "A W". iDestruct (at_writer_base_valid with "A W") as %[? ->].
  iDestruct (fractional with "[$A $W]") as "W".
  rewrite assoc -fractional Qp.quarter_three_quarter.
  by iApply at_writer_base_update_insert.
Qed.

Lemma at_full_auth_join γ ζ t V :
  at_auth γ ζ t V ∗ at_writer γ ζ ∗
  at_exclusive_write γ t 1%Qp ∗ at_last_na γ V
  ⊣⊢ at_writer_base γ ζ 1 ∗
    (at_auth_exclusive_write γ t ∗ at_exclusive_write γ t 1) ∗ at_last_na γ V.
Proof.
  rewrite /at_auth bi.sep_assoc (bi.sep_comm _ (at_writer _ _)).
  rewrite (bi.sep_assoc (at_writer _ _) (at_auth_writer _ _)) -fractional.
  rewrite bi.sep_assoc -(bi.sep_comm _ (at_auth_exclusive_write _ _)).
  rewrite bi.sep_assoc -(bi.sep_assoc _ (at_auth_exclusive_write _ _)).
  rewrite Qp.three_quarter_quarter.
  rewrite 2!(bi.sep_comm _ (at_last_na _ _)) 3!bi.sep_assoc.
  rewrite at_last_na_dup.
  rewrite (bi.sep_comm (at_last_na _ _)) -2!bi.sep_assoc.
  by rewrite (bi.sep_comm (at_last_na _ _)).
Qed.

Lemma at_full_auth_alloc_cofinite ζ t V (G : gset gname) :
  ⊢ |==> ∃ γ, ⌜γ ∉ G⌝ ∗ at_auth γ ζ t V ∗ at_writer γ ζ ∗
              at_exclusive_write γ t 1%Qp ∗ at_last_na γ V.
Proof.
  setoid_rewrite at_full_auth_join.
  do 3 setoid_rewrite <- own_op. apply own_alloc_cofinite.
  rewrite_own_op. simpl. split; last split; [..|done]; simpl.
  - apply auth_both_valid_discrete. split; [done|by apply toHistBase_valid].
  - by apply frac_auth_valid.
Qed.

Lemma at_full_auth_alloc ζ t V:
  ⊢ |==> ∃ γ, at_auth γ ζ t V ∗ at_writer γ ζ ∗
              at_exclusive_write γ t 1%Qp ∗ at_last_na γ V.
Proof.
  iMod (at_full_auth_alloc_cofinite ζ t V ∅) as (γ) "[_ ?]".
  iIntros "!>". iExists γ. by iFrame.
Qed.

End props.
