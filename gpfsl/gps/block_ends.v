From stdpp Require Import gmap.
From iris.bi Require Import bi big_op.

From orc11 Require Import base.

Require Import iris.prelude.options.

(* Map's block ends *)
Section Mblock_ends.
  Context `{FinMap K M} {A}
  (R: relation (K * A)) {DecR : ∀ x y, Decision (R x y)}.

  Implicit Types (m: M A) (k : K) (a b: A).

  Definition mblock_ends m : M A
    := filter (λ kv, map_Forall (λ k' v', k' ≠ (kv.1) → ¬ R kv (k',v')) m) m.

  Lemma mblock_ends_singleton k v : mblock_ends {[k := v]} = {[k := v]}.
  Proof.
    apply map_filter_singleton_True, map_Forall_insert; [by rewrite lookup_empty|].
    split; [done|by apply map_Forall_empty].
  Qed.

  Lemma mblock_ends_ins_fresh_mono k v m
    (FRESH: m !! k = None):
    mblock_ends (<[k:=v]> m) ⊆ <[k:=v]> (mblock_ends m).
  Proof.
    move => k'.
    destruct (mblock_ends (<[k:=v]> m) !! k') as [v'|] eqn:HK.
    - rewrite /mblock_ends in HK.
      apply map_filter_lookup_Some in HK as [HK%lookup_insert_Some ALL].
      rewrite (_: (<[k:=v]> (mblock_ends m)) !! k' = Some v'); first done.
      destruct HK as [[? ?]|[ ? ?]].
      + subst k' v'. by apply lookup_insert.
      + rewrite lookup_insert_ne; last done.
        apply map_filter_lookup_Some. split; first done.
        move => k0 v0 IN NE. apply ALL; last done.
        rewrite lookup_insert_ne; first done.
        move => ?. subst k0. by rewrite FRESH in IN.
    - simpl. by case lookup.
  Qed.

  Inductive mblock_ends_ins_spec : M A → K → A → M A → M A → Prop :=
  (* prepend a block *)
  | be_ins_nL_sR m k v B
                 (nL: map_Forall (λ k' v', ¬ R (k',v') (k,v)) m)
                 (sR: ∃ k' v', m !! k' = Some v' ∧ R (k,v) (k',v'))
    : mblock_ends_ins_spec m k v B B
  (* extend a block *)
  | be_ins_sL_nR m k v B k' v'
                 (sL: R (k',v') (k,v))
                 (nR: map_Forall (λ k0 v0, ¬ R (k,v) (k0,v0)) m)
                 (In: m !! k' = Some v')
    : mblock_ends_ins_spec m k v B (<[k := v]> (delete k' B))
  (* fresh block *)
 | be_ins_nL_nR m k v B
                 (nL: map_Forall (λ k' v', ¬ R (k',v') (k,v)) m)
                 (nR: map_Forall (λ k' v', ¬ R (k,v) (k',v')) m)
    : mblock_ends_ins_spec m k v B (<[k := v]> B)
  (* connect 2 blocks *)
  | be_ins_sL_sR m k v B k' v'
                 (sL: R (k',v') (k,v))
                 (sR: ∃ k0 v0, m !! k0 = Some v0 ∧ R (k,v) (k0,v0))
                 (In: m !! k' = Some v')
    : mblock_ends_ins_spec m k v B (delete k' B).

  Lemma mblock_ends_insert_prepend m k v
    (nL: map_Forall (λ k' v', ¬ R (k',v') (k,v)) m)
    (sR: ∃ k' v', m !! k' = Some v' ∧ R (k,v) (k',v'))
    (NIn: m !! k = None) :
    mblock_ends (<[k := v]> m) = mblock_ends m.
  Proof.
    apply map_eq => i.
    destruct (mblock_ends m !! i) as [a|] eqn:Ha.
    - move : Ha. rewrite !map_filter_lookup_Some.
      move => [Hi FA].
      have ?: k ≠ i by naive_solver.
      split; [by rewrite lookup_insert_ne|].
      move => k' v' Hk'.
      case (decide (k' = k)) => ?.
      + subst k'. rewrite lookup_insert in Hk'. inversion Hk'. subst v'.
        move => _. by apply nL.
      + apply FA. by rewrite lookup_insert_ne in Hk'.
    - move : Ha. rewrite !map_filter_lookup_None => Hi.
      right. move => v' Hv'.
      case (decide (k = i)) => ?;
        [subst i; rewrite lookup_insert in Hv'
        |rewrite lookup_insert_ne in Hv'; [|done]].
      + inversion Hv'. subst v'.
        destruct sR as [k' [v' [Hk' HR]]].
        move => /(_ k' v') HE.
        have ?: k ≠ k' by naive_solver.
        apply HE; [|done|done]. by rewrite lookup_insert_ne.
      + destruct Hi as [Hi|FAi]; [by rewrite Hi in Hv'|].
        move => FA. apply (FAi _ Hv').
        move => k1 v1 /=. case (decide (k1 = k)) => ?.
        * subst k1. by rewrite NIn.
        * move => ?. apply FA. by rewrite lookup_insert_ne.
  Qed.

  Lemma mblock_ends_insert_fresh m k v
    (nL: map_Forall (λ k' v', ¬ R (k',v') (k,v)) m)
    (nR: map_Forall (λ k' v', ¬ R (k,v) (k',v')) m)
    (NIn: m !! k = None) :
    mblock_ends (<[k := v]> m) = <[k := v]> (mblock_ends m).
  Proof.
    rewrite {1}/mblock_ends map_filter_insert_True; last first.
    { simpl. move => ?? Hk' ?.
      rewrite lookup_insert_ne in Hk'; [by apply nR|done]. }
    f_equal. apply map_eq => i.
    destruct (mblock_ends m !! i) as [a|] eqn:Ha.
    - move : Ha. rewrite !map_filter_lookup_Some.
      move => [Hi FA]. split; [done|].
      move => k' v' /=. case (decide (k' = k)) => ?.
      + subst k'. rewrite lookup_insert => [[?]] _. subst v'. by apply nL.
      + rewrite lookup_insert_ne; [apply FA|done].
    - move : Ha. rewrite !map_filter_lookup_None.
      move => [?|FAi]; [by left|].
      right => vi Hi FA. apply (FAi _ Hi). clear FAi.
      move => k' v' /=. case (decide (k' = k)) => ?.
      + subst k'. by rewrite NIn.
      + move => ?. apply FA. by rewrite lookup_insert_ne.
  Qed.

  Lemma mblock_ends_insert_extend m k v k' v'
    (sL: R (k',v') (k,v))
    (nR: map_Forall (λ k0 v0, ¬ R (k,v) (k0,v0)) m)
    (In: m !! k' = Some v')
    (NIn: m !! k = None)
    (PART: ∀ k1 v1 k2 v2 i a, m !! k1 = Some v1
            → m !! k2 = Some v2
            → R (k1,v1) (i,a) → R (k2,v2) (i,a)
            → k1 = k2):
    mblock_ends (<[k := v]> m) = <[k := v]> (delete k' (mblock_ends m)).
  Proof.
    apply map_eq => i.
    case (decide (k = i)) => ?;
      [subst i; rewrite lookup_insert
      |rewrite lookup_insert_ne;
        [destruct (delete k' (mblock_ends m) !! i) as [a|] eqn:Ha|done]].
    - apply map_filter_lookup_Some.
      split; first by rewrite lookup_insert.
      move => k1 v1 Hk1 ?. rewrite lookup_insert_ne in Hk1; [|done].
      by apply nR.
    - move : Ha. rewrite lookup_delete_Some 2!map_filter_lookup_Some.
      move => [Hv' [Hi FA]]. split; first by rewrite lookup_insert_ne.
      move => k1 v1 /= Hk1 ?.
      case (decide (k1 = k)) => ?;
        [subst k1; rewrite lookup_insert in Hk1
        |rewrite lookup_insert_ne in Hk1; [by apply FA|done]].
      inversion Hk1. subst v1.
      move => HR1. by have ? := (PART _ _ _ _ _ _ Hi In HR1 sL).
    - move : Ha. rewrite lookup_delete_None 2!map_filter_lookup_None.
      move => [?|[NONE|FA]].
      + right. move => a. rewrite lookup_insert_ne; [|done].
        move => Hi FAi. subst k'.
        rewrite In in Hi. inversion Hi. subst a.
        apply (FAi k v); [by rewrite lookup_insert|done|done].
      + left.  by rewrite lookup_insert_ne.
      + right. move => a. rewrite lookup_insert_ne; [|done].
        move => Hi FAi. apply (FA _ Hi). clear FA.
        move => k1 v1 /= Hk1 ?.
        case (decide (k1 = k)) => ?;
          [subst k1;by rewrite NIn in Hk1
          |apply FAi;[by rewrite lookup_insert_ne|done]].
  Qed.

  Lemma mblock_ends_insert_connect m k v k' v'
    (sL: R (k',v') (k,v))
    (sR: ∃ k0 v0, m !! k0 = Some v0 ∧ R (k,v) (k0,v0))
    (In: m !! k' = Some v')
    (NIn: m !! k = None)
    (PART: ∀ k1 v1 k2 v2 i a, m !! k1 = Some v1
            → m !! k2 = Some v2
            → R (k1,v1) (i,a) → R (k2,v2) (i,a)
            → k1 = k2) :
   mblock_ends (<[k := v]> m) = delete k' (mblock_ends m).
  Proof.
    apply map_eq => i.
    destruct (delete k' (mblock_ends m) !! i) as [a|] eqn:Ha.
    - move : Ha. rewrite lookup_delete_Some 2!map_filter_lookup_Some.
      move => [Hv' [Hi FA]]. split.
      { rewrite lookup_insert_ne; [done|].
        move => ?. subst i. by rewrite NIn in Hi. }
      move => k1 v1 /= Hk1 ?.
      case (decide (k1 = k)) => ?;
        [subst k1; rewrite lookup_insert in Hk1
        |rewrite lookup_insert_ne in Hk1; [by apply FA|done]].
      inversion Hk1. subst v1. clear Hk1. move => HR1.
      by have ? := (PART _ _ _ _ _ _ Hi In HR1 sL).
    - move : Ha. rewrite lookup_delete_None 2!map_filter_lookup_None.
      move => [?|[NONE|FA]].
      + right => a. subst k'.
        case (decide (k = i)) => ?;
          [subst i;rewrite lookup_insert|rewrite lookup_insert_ne; [|done]].
        * inversion 1. subst a => FAi.
          destruct sR as [k1 [v1 [Hk1 HR1]]].
          have ?: k1 ≠ k. { move => ?. subst k1. by rewrite Hk1 in NIn. }
          apply (FAi k1 v1); by [rewrite lookup_insert_ne|done|done].
        * move => Hi FAi.
          rewrite In in Hi. inversion Hi. subst a.
          apply (FAi k v); [by rewrite lookup_insert|done|done].
      + case (decide (k = i)) => ?;
          [subst i|by left; rewrite lookup_insert_ne].
        right.
        move => b. rewrite lookup_insert => [[?]] FA. subst b.
        destruct sR as [k1 [v1 [Hk1 HR1]]].
        have ?: k1 ≠ k. { move => ?. subst k1. by rewrite Hk1 in NIn. }
        apply (FA k1 v1); by [rewrite lookup_insert_ne|done|done].
      + right => a.
        case (decide (k = i)) => ?;
          [subst i;rewrite lookup_insert|rewrite lookup_insert_ne; [|done]].
        * inversion 1. subst a => FAi.
          destruct sR as [k1 [v1 [Hk1 HR1]]].
          have ?: k1 ≠ k. { move => ?. subst k1. by rewrite Hk1 in NIn. }
          apply (FAi k1 v1); by [rewrite lookup_insert_ne|done|done].
        * move => Hi FAi. apply (FA _ Hi).
          move => k1 v1 /= Hk1 ?.
          case (decide (k1 = k)) => ?;
            [subst k1;by rewrite NIn in Hk1
            |apply FAi;[by rewrite lookup_insert_ne|done]].
  Qed.

  Lemma mblock_ends_ins m k v (NIn: m !! k = None)
    (PART: ∀ k1 v1 k2 v2 i a, m !! k1 = Some v1
            → m !! k2 = Some v2
            → R (k1,v1) (i,a) → R (k2,v2) (i,a)
            → k1 = k2) :
    mblock_ends_ins_spec m k v (mblock_ends m) (mblock_ends (<[k:=v]> m)).
  Proof.
    case (decide (map_Forall (λ k' v', ¬ R (k',v') (k,v)) m))
      => [NL|/map_not_Forall SL];
    case (decide (map_Forall (λ k' v', ¬ R (k,v) (k',v')) m))
      => [NR|/map_not_Forall SR].
    - rewrite mblock_ends_insert_fresh; [by constructor|auto|auto|auto].
    - destruct SR as [i [vi [Hi HR]]]. apply dec_stable in HR.
      rewrite mblock_ends_insert_prepend; [|auto|by do 2 eexists|auto].
      constructor; [auto|by do 2 eexists].
    - destruct SL as [i [vi [Hi HR]]]. apply dec_stable in HR.
      erewrite mblock_ends_insert_extend; [|eauto|auto|auto|auto|auto].
      by eapply be_ins_sL_nR.
    - destruct SL as [i1 [v1 [Hi1 HR1]]]. apply dec_stable in HR1.
      destruct SR as [i2 [v2 [Hi2 HR2]]]. apply dec_stable in HR2.
      erewrite mblock_ends_insert_connect;
        [|eauto|by do 2 eexists|done|done|done].
      eapply be_ins_sL_sR; [done|by do 2 eexists|done].
  Qed.

End Mblock_ends.

(* gmap block ends *)
Section Gmblock_ends.
  Context `{BiAffine PROP} `{Countable K} {A}
          (R: relation (K * A)) {DecR : ∀ x y, Decision (R x y)}.

  Lemma gmblock_ends_ins_update (Ψ: K → A → PROP) k v (m: gmap K A)
   (NIn: m !! k = None)
   (BI: mblock_ends_ins_spec R m k v (mblock_ends R m) (mblock_ends R (<[k := v]> m))) :
    Ψ k v ∗ ([∗ map] k' ↦ v' ∈ mblock_ends R m, Ψ k' v')
    ⊢ ([∗ map] k' ↦ v' ∈ mblock_ends R (<[k := v]> m), Ψ k' v').
  Proof using All.
    rewrite -big_sepM_insert; last (apply map_filter_lookup_None; by left).
    apply: big_sepM_subseteq. inversion BI; subst.
    - apply insert_subseteq, map_filter_lookup_None. by left.
    - apply insert_mono, delete_subseteq.
    - done.
    - etrans; [apply delete_subseteq|].
      apply insert_subseteq, map_filter_lookup_None. by left.
  Qed.
End Gmblock_ends.
