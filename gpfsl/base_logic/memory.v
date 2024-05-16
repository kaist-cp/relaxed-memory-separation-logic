From gpfsl.lang Require Import lang.

Require Import iris.prelude.options.

Implicit Types (l : loc) (t : time) (V : view) (M : memory).

(* TODO: properties of the semantics, should be moved to orc11. *)

(* Local simple view predicates *)
Definition seen_local l t V := Some t ⊑ V !!w l.
Definition alloc_local (l: loc) (C: cell) V :=
  ∃ t m, C !! t = Some m ∧ m.(mval) ≠ DVal ∧ seen_local l t V.

Definition atw_local l rs V := Some rs ⊑ V !!aw l.
Definition atr_local l rs V := Some rs ⊑ V !!ar l.
Definition na_local l rs V := Some rs ⊑ V !!nr l.

Global Instance : Params (@seen_local) 2 := {}.
Global Instance seen_local_mono l t: Proper ((⊑) ==> impl) (seen_local l t).
Proof.
  move => ?? Ext. rewrite /seen_local => seen. etrans; [apply seen|].
  by apply view_sqsubseteq, Ext.
Qed.

Global Instance : Params (@alloc_local) 1 := {}.
Global Instance alloc_local_mono l: Proper ((⊆) ==> (⊑) ==> impl) (alloc_local l).
Proof.
  move => C1 C2 ? V1 V2 LEV [t' [m' [Eqt' [? ?]]]]. exists t', m'.
  repeat split; [by eapply lookup_weaken|done|by eapply seen_local_mono].
Qed.

Global Instance : Params (@na_local) 1 := {}.
Global Instance na_local_mono l : Proper (flip (⊑) ==> (⊑) ==> impl) (na_local l).
Proof.
  move => rs1 rs2 LE V1 V2 LEV LEr. rewrite /na_local.
  rewrite /flip in LE. etrans; last first.
  - apply view_sqsubseteq. apply LEV. - etrans; [|apply LEr]. done.
Qed.

Global Instance : Params (@atw_local) 1 := {}.
Global Instance atw_local_mono l : Proper (flip (⊑) ==> (⊑) ==> impl) (atw_local l).
Proof.
  move => rs1 rs2 LE V1 V2 LEV LEr. rewrite /atw_local.
  rewrite /flip in LE. etrans; last first.
  - apply view_sqsubseteq. apply LEV. - etrans; [|apply LEr]. done.
Qed.

Global Instance : Params (@atr_local) 1 := {}.
Global Instance atr_local_mono l : Proper (flip (⊑) ==> (⊑) ==> impl) (atr_local l).
Proof.
  move => rs1 rs2 LE V1 V2 LEV LEr. rewrite /atr_local.
  rewrite /flip in LE. etrans; last first.
  - apply view_sqsubseteq. apply LEV. - etrans; [|apply LEr]. done.
Qed.

Lemma na_local_join' l rs1 rs2 V1 V2:
  na_local l rs1 V1 → na_local l rs2 V2 → na_local l (rs1 ∪ rs2) (V1 ⊔ V2).
Proof.
  rewrite /na_local => ??.
  rewrite (_: Some (rs1 ∪ rs2) = Some rs1 ⊔ Some rs2); [|done].
  rewrite view_lookup_nr_join. solve_lat.
Qed.
Lemma na_local_join l V rs1 rs2:
  na_local l rs1 V → na_local l rs2 V → na_local l (rs1 ∪ rs2) V.
Proof.
  intros NA1 NA2.
  assert (NA := na_local_join' _ _ _ _ _ NA1 NA2). clear NA1 NA2.
  eapply na_local_mono; last exact NA; [done|solve_lat].
Qed.

Lemma atw_local_join l V rs1 rs2:
  atw_local l rs1 V → atw_local l rs2 V → atw_local l (rs1 ∪ rs2) V.
Proof.
  rewrite /atw_local => ??.
  rewrite (_: Some (rs1 ∪ rs2) = Some rs1 ⊔ Some rs2); [solve_lat|done].
Qed.

Lemma atr_local_join l V rs1 rs2:
  atr_local l rs1 V → atr_local l rs2 V → atr_local l (rs1 ∪ rs2) V.
Proof.
  rewrite /atr_local => ??.
  rewrite (_: Some (rs1 ∪ rs2) = Some rs1 ⊔ Some rs2); [solve_lat|done].
Qed.


(** Properties of local predicates *)

Lemma alloc_local_cut l ta Cf V
  (ALLOC : alloc_local l (cell_cut ta Cf) V) :
  Some ta ⊑ V !!w l.
Proof.
  destruct ALLOC as [t' [m' [[Eqm' Le']%cell_cut_lookup_Some [_ SEEN]]]].
  by etrans; last apply SEEN.
Qed.

(** Lots of utility lemmas *)
Lemma alloc_local_cut_singleton l t m ta Cf V (M: memory) (𝓝: view)
  (ALLOC : alloc_local l (cell_cut ta Cf) V)
  (CUT: cell_cut ta Cf = {[t := m]})
  (EqCf : M !!c l = Cf)
  (Eqta : 𝓝 !!w l = Some ta) :
  ∀ 𝑚, 𝑚 ∈ M → 𝑚.(mloc) = l → Some 𝑚.(mto) ⊑ V !!w l.
Proof.
  move => 𝑚 EqC' Eql'.
  destruct ALLOC as [t1 [m1 [Eqm1 [_ SEEN]]]].
  etrans; last apply SEEN.
  move: Eqm1. rewrite CUT lookup_singleton_Some => [[? ?]]. subst t1 m1.
  apply (cell_cut_singleton _ _ _ _  CUT).
  rewrite -EqCf -memory_lookup_cell -Eql'. by eexists.
Qed.

Lemma read_helper_na_local 𝓥 o l t tr R 𝓥' rs Vna
  (RH: read_helper 𝓥 o l t tr R 𝓥')
  (NA: na_local l rs Vna) :
  let rs' := if decide (Relaxed ⊑ o) then rs else rs ∪ {[tr]} in
  na_local l rs' (Vna ⊔ 𝓥'.(cur)).
Proof.
  move => rs'.
  have NA': na_local l rs (Vna ⊔ cur 𝓥').
  { eapply na_local_mono; [..|exact NA]; [done|solve_lat]. }
  rewrite /rs'. case decide => RLX; [done|].
  apply na_local_join; [done|].
  inversion RH. rewrite /= /V (decide_False _ _ RLX) /na_local.
  rewrite decide_False; last (by move => RE; apply RLX; rewrite -RE).
  rewrite /= 2!view_lookup_nr_join view_lookup_nr_insert /=. solve_lat.
Qed.

Lemma read_helper_atr_local Va 𝓥 o l t tr R 𝓥' rs
  (RH: read_helper 𝓥 o l t tr R 𝓥')
  (AT: atr_local l rs Va) :
  let rs' := if decide (Relaxed ⊑ o) then rs ∪ {[tr]} else rs in
  atr_local l rs' (Va ⊔ 𝓥'.(cur)).
Proof.
  move => rs'.
  have AT': atr_local l rs (Va ⊔ 𝓥'.(cur)).
  { eapply atr_local_mono; [done|..|done]. solve_lat. }
  rewrite /rs'. case decide => RLX; [|done].
  apply atr_local_join; [done|].
  eapply atr_local_mono; [done|by apply lat_join_sqsubseteq_r|].
  inversion RH. rewrite /= /V (decide_True _ _ RLX) /atr_local.
  case decide => ? /=;
    rewrite !view_lookup_ar_join view_lookup_ar_insert /=; solve_lat.
Qed.

Lemma write_helper_atw_local 𝓥 Va o l t R oV 𝓥' ws
  (WH: write_helper 𝓥 o l t R oV 𝓥')
  (AT: atw_local l ws Va) (RLX: Relaxed ⊑ o):
  atw_local l (ws ∪ {[t]}) (Va ⊔ 𝓥'.(cur)).
Proof.
  have AT': atw_local l ws (Va ⊔ 𝓥'.(cur)).
  { eapply atw_local_mono; [done|..|done]. solve_lat. }
  apply atw_local_join; [done|].
  inversion WH. rewrite /= (decide_True _ _ RLX) /atw_local.
  rewrite !view_lookup_aw_join view_lookup_aw_insert /=; solve_lat.
Qed.

Lemma read_helper_seen_local o l t tr 𝓥 𝓥' V (OR: Relaxed ⊑ o)
  (RH : read_helper 𝓥 o l t tr V 𝓥'):
  seen_local l t 𝓥'.(cur).
Proof.
  inversion RH. rewrite /seen_local /=.
  destruct o=>//; rewrite !view_lookup_w_join view_lookup_w_insert; solve_lat.
Qed.

Lemma write_helper_seen_local {𝓥 l o t Rr Rw 𝓥'}
  (WH: write_helper 𝓥 o l t Rr Rw 𝓥') :
  seen_local l t 𝓥'.(cur).
Proof.
  inversion_clear WH. rewrite /seen_local view_lookup_w_join /=.
  case_decide; rewrite view_lookup_w_insert /=; solve_lat.
Qed.

Lemma write_helper_strict {𝓥 l o t Rr Rw 𝓥'}
  (WH: write_helper 𝓥 o l t Rr Rw 𝓥') :
  𝓥.(cur) ≠ 𝓥'.(cur).
Proof.
  assert (SL:= write_helper_seen_local WH).
  assert (FR:= write_helper_fresh WH).
  rewrite /seen_local in SL. intros Eq. rewrite Eq in FR.
  apply : (irreflexivity (⊏) (Some t)). eapply strict_transitive_r; eauto.
Qed.

Lemma write_helper_seen_local_write {𝓥 l o t Rr Rw 𝓥'}
  (OR: Relaxed ⊑ o)
  (WH: write_helper 𝓥 o l t Rr Rw 𝓥') :
  seen_local l t (default ∅ Rw).
Proof.
  inversion_clear WH. rewrite /write_Rw (decide_True _ _ OR) /seen_local /=.
  case_match; rewrite !view_lookup_w_join;
    case_match; rewrite view_lookup_w_insert; solve_lat.
Qed.
