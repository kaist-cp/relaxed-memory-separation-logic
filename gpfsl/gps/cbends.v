From Coq.QArith Require Import Qcanon.
From gpfsl.lang Require Import lang.
From gpfsl.gps Require Export block_ends.

Require Import iris.prelude.options.

(* Lemmas for block ends *)

Section cbends.
Context {A : Type}.

Local Notation cell := (gmap time A).
Implicit Types (C : cell).

Definition cell_adj (tm tm': time * A) := tm'.1 = (tm.1 + 1)%positive.
Instance cell_adj_dec (tm tm': time * A): Decision (cell_adj tm tm').
Proof. unfold cell_adj. apply _. Qed.

Definition cbends (C : cell) : cell := mblock_ends cell_adj C.

Lemma cbends_ins_update t m (C: cell)
  (FRESH: C !! t = None) :
  mblock_ends_ins_spec cell_adj C t m (mblock_ends cell_adj C)
  (mblock_ends cell_adj (<[t:=m]> C)).
Proof.
  apply mblock_ends_ins; [done|]. rewrite /cell_adj /=.
  move => k1 v1 k2 v2 i a Hk1 Hk2 Adj1 Adj2.
  case (decide (k1 = k2)) => [//|NEq].
  exfalso. apply NEq. subst i. lia.
Qed.

Lemma cbends_ins_extend_subseteq_1 t m t' m' (C: cell)
  (FRESH: C !! t = None)
  (IN: mblock_ends cell_adj C !! t' = Some m') (ADJ: t = (t' + 1)%positive)
  (INS: mblock_ends_ins_spec cell_adj C t m (mblock_ends cell_adj C)
                             (mblock_ends cell_adj (<[t:=m]> C))):
  mblock_ends cell_adj (<[t:=m]>C) ⊆
  <[t:=m]> (delete t' (mblock_ends cell_adj C)).
Proof.
  have IN' : C !! t' = Some m' by move : IN => /map_filter_lookup_Some [].
  inversion INS; clear INS; subst.
  - exfalso. by eapply nL.
  - rewrite /cell_adj /= in sL. rewrite (_: k' = t'); [done|lia].
  - exfalso. by eapply nL.
  - rewrite /cell_adj /= in sL. rewrite (_: k' = t'); [|lia].
    apply insert_subseteq. rewrite lookup_delete_None. right.
    rewrite map_filter_lookup_None. by left.
Qed.

Lemma cbends_ins_extend_subseteq t m t' m' (C: cell)
  (FRESH: C !! t = None)
  (IN: mblock_ends cell_adj C !! t' = Some m') (ADJ: t = (t'+1)%positive):
  mblock_ends cell_adj (<[t:=m]>C) ⊆
  <[t:=m]> (delete t' (mblock_ends cell_adj C)).
Proof.
  eapply cbends_ins_extend_subseteq_1; [done..|by apply cbends_ins_update].
Qed.

Lemma cbends_ins_top_eq_1 (t: time) m t' m' (C: cell)
  (FRESH: C !! t = None)
  (IN: mblock_ends cell_adj C !! t' = Some m') (ADJ: t = (t'+1)%positive)
  (MAX: ∀ (t0: time) m0, C !! t0 = Some m0 → (t0 < t)%positive)
  (INS: mblock_ends_ins_spec cell_adj C t m (mblock_ends cell_adj C)
                             (mblock_ends cell_adj (<[t:=m]> C))):
  mblock_ends cell_adj (<[t:=m]>C) =
  <[t:=m]> (delete t' (mblock_ends cell_adj C)).
Proof.
  have IN' : C !! t' = Some m' by move : IN => /map_filter_lookup_Some [].
  inversion INS; clear INS; subst.
  - exfalso. by eapply nL.
  - rewrite /cell_adj /= in sL. rewrite (_: k' = t'); [done|lia].
  - exfalso. by eapply nL.
  - exfalso. destruct sR as (t0&  m0 & Eq0 & Eqt0). rewrite /cell_adj /= in Eqt0.
    subst t0. specialize (MAX _ _ Eq0). lia.
Qed.

Lemma cbends_ins_top_eq t m t' m' (C: cell)
  (FRESH: C !! t = None)
  (MAX: ∀ (t0: time) m0, C !! t0 = Some m0 → (t0 < t)%positive)
  (IN: mblock_ends cell_adj C !! t' = Some m') (ADJ: t = (t'+1)%positive):
  mblock_ends cell_adj (<[t:=m]>C) =
  <[t:=m]> (delete t' (mblock_ends cell_adj C)).
Proof.
  eapply cbends_ins_top_eq_1; [done..|by apply cbends_ins_update].
Qed.
End cbends.
