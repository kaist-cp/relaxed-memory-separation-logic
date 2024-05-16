From stdpp Require Import fin_maps coPset.
From iris.algebra Require Import big_op gmap cmra_big_op auth.
From iris.algebra.lib Require Import excl_auth dfrac_agree.
From iris.algebra Require Export frac.
From iris.bi Require Import big_op fractional.
From iris.proofmode Require Export proofmode.
From iris.base_logic.lib Require Export own.
From iris.base_logic.lib Require Import gen_heap invariants.
From iris.program_logic Require Import ownp.

From gpfsl.algebra Require Export lattice_cmra.
From gpfsl.base_logic Require Export history_cmra.
From gpfsl.base_logic Require Export memory.
From gpfsl.lang Require Export lang.

Require Import iris.prelude.options.

Open Scope Z_scope.

(* TODO move stdpp? *)
Global Instance gmap_sqsubseteq_insert_proper
  `{Countable K, SqSubsetEq A, Reflexive A sqsubseteq } (k: K) (v: A) :
  Proper (@sqsubseteq (gmap K A) _ ==> sqsubseteq) (insert k v).
Proof.
  move => m1 m2 Le k'.
  case (decide (k = k')) => [->|?];
    [rewrite 2!lookup_insert|do 2 (rewrite lookup_insert_ne; last done); done].
  by cbn.
Qed.

(** DEFINITIONS --------------------------------------------------------------*)

Definition thread_id := gname.

Implicit Types
  (l : loc) (V : view) (t : time) (σ : state) (M : memory) (C : cell).

(* Some properties of history cells *)
Record good_hist C := {
  good_alloc: ¬ cell_deallocated C;
  good_nempty: C ≠ ∅;
  good_alloc_min: ∀ t m, C !! t = Some m ∧ mval m = AVal → cell_min C = Some (t, m);
  good_dealloc_max: ∀ t m, C !! t = Some m ∧ mval m = DVal → cell_max C = Some (t, m);
}.

(* Invariant for freeable blocks of location *)
Definition hist_freeable_rel M (hF : hist_freeableUR) : Prop :=
  ∀ blk qs, hF !! blk = Some qs →
    qs.2 ≠ ∅ ∧ ∀ i, M !!c (blk, i) ≠ ∅ ↔ is_Some (qs.2 !! i).

Fixpoint inter (i0 : Z) (n : nat) : gmapR Z (exclR unitO) :=
  match n with O => ∅ | S n => <[i0 := Excl ()]>(inter (i0+1) n) end.

(* NOTE on monotonicity for WP:
  Previously, in order to prove that WP is downward-monotone
  (i.e ∀ V1 ⊑ V2, wp e at V2 -∗ wp e at V1), we need the ghost state to be
  a lower bound for the physical state, i.e, in hist_ctx σ, we have
  ∃ M, ⌜memory_le M (mem_cut σ.(mem) σ.(na))⌝, and then we put constraints
  on M.
  Afterwards, we switch to indexing WP with thread ids, in order to unify
  the 3-view logic (tvProp) and the 1-view logic (vProp), this closure is not
  useful anymore, as we need to explicitly monotonize WP anyway.

  Later we ran into a problem with this scheme, because we did not keep the
  lower bound consistent: in CAS, we make the new message's ghost view to
  include the physical view of the message read, which creates discrepancies
  down the road, because the constraints are only applied to ghost views, not
  physical views. If one attempts to do this again, make sure keep the lower
  bound consistent in ghost views. **)

Local Existing Instances
  histGpreS_hist histGpreS_freeable histGpreS_read histGpreS_na_view
  histGpreS_at_write histGpreS_tview
  hist_inG
  ownP_inG
  .

Section definitions.
  Context `{!histGS Σ}.

  (* Ghost history ownership *)
  Definition hist_def (l : loc) (q : Qp) (C : cell) : iProp Σ
    := mapsto l (DfracOwn q) (Some C).
  Definition hist_aux : seal (@hist_def). Proof. by eexists. Qed.
  Definition hist := unseal hist_aux.
  Definition hist_eq : @hist = @hist_def := seal_eq hist_aux.

  (* Freeable block tokens *)
  Definition hist_freeable_def (l : loc) (q : Qp) (n: nat) : iProp Σ :=
    own hist_freeable_name (◯ {[ l.1 := (q, inter (l.2) n) ]}).
  Definition hist_freeable_aux : seal (@hist_freeable_def). Proof. by eexists. Qed.
  Definition hist_freeable := unseal hist_freeable_aux.
  Definition hist_freeable_eq : @hist_freeable = @hist_freeable_def :=
    seal_eq hist_freeable_aux.

  (* Non-atomic reads *)
  Definition naread_def (l : loc) (q : Qp) (rs : time_ids) : iProp Σ
    := own hist_naread_name (◯ {[ l := (q, to_latT rs) ]}).
  Definition naread_aux : seal (@naread_def). Proof. by eexists. Qed.
  Definition naread := unseal naread_aux.
  Definition naread_eq : @naread = @naread_def := seal_eq naread_aux.

  (* Atomic reads *)
  Definition atread_def (l : loc) (q : Qp) (rs : time_ids) : iProp Σ
    := own hist_atread_name (◯ {[ l := (q, to_latT rs) ]}).
  Definition atread_aux : seal (@atread_def). Proof. by eexists. Qed.
  Definition atread := unseal atread_aux.
  Definition atread_eq : @atread = @atread_def := seal_eq atread_aux.

  (* Atomic write *)
  Definition atwrite_def (l : loc) (q : Qp) (ws : time_ids) : iProp Σ
    := own hist_atwrite_name (◯ {[ l := to_frac_agree q (ws : gset.gsetO _) ]}).
  Definition atwrite_aux : seal (@atwrite_def). Proof. by eexists. Qed.
  Definition atwrite := unseal atwrite_aux.
  Definition atwrite_eq : @atwrite = @atwrite_def
    := seal_eq atwrite_aux.

  (* Logical state invariant *)
  Definition hist_ctx (σ : state) : iProp Σ :=
    (∃ hF (V Vc: view),
      gen_heap_interp (to_hist (mem_cut σ.(mem) Vc))
      ∗ own hist_freeable_name (● hF)
      ∗ own hist_naread_name (● to_nar σ.(na))
      ∗ own hist_atwrite_name (● to_atw σ.(na))
      ∗ own hist_atread_name (● to_atr σ.(na))
      ∗ own hist_sc_name (● (to_latT σ.(sc))) (* global SC view *)
      ∗ own hist_gtime_name (● (to_latT V))   (* global simple view *)
      ∗ ⌜Wf σ ∧ hist_freeable_rel σ.(mem) hF ∧ V ∈ σ.(mem) ∧ σ.(na) ⊑ Vc⌝)%I.

  (* Local thread view *)
  Definition seen_def 𝓥 : iProp Σ :=
    own hist_gtime_name (◯ (to_latT 𝓥.(acq))).
  Definition seen_aux : seal (@seen_def). Proof. by eexists. Qed.
  Definition seen := unseal seen_aux.
  Definition seen_eq : @seen = @seen_def := seal_eq seen_aux.

  (* Exclusive SC view *)
  Definition sc_view_def (V: view) : iProp Σ :=
     own hist_sc_name (◯ (to_latT V)).
  Definition sc_view_aux : seal (@sc_view_def). Proof. by eexists. Qed.
  Definition sc_view := unseal sc_view_aux.
  Definition sc_view_eq : @sc_view = @sc_view_def := seal_eq sc_view_aux.

End definitions.

#[global] Typeclasses Opaque hist hist_freeable seen sc_view.

Notation "†{ q } l … n" := (hist_freeable l q n)
  (at level 20, q at level 50, format "†{ q } l … n") : bi_scope.
Notation "† l … n" := (hist_freeable l 1 n) (at level 20) : bi_scope.

(** State interpretation *)
(* Final bit of ghost state: we also need [ownPGS] for invariants ([invGS])
  and [ownP]. *)
Class noprolG Σ := NoProLG {
  noprolG_ownpG : ownPGS nopro_lang Σ;
  noprolG_histG :> histGS Σ;
}.
Local Existing Instance noprolG_ownpG.

(** [hist_inv_content] is a trick to allow access to [hist_ctx] even without WP.
  In particular, this allows [hist_ctx_hist_drop_singleton] to be used without a
  WP, e.g., in a viewshift. This allows moving a location from atomic mode to
  non-atomic mode with just a viewshift, as used in GPS_SWWriter_dealloc. *)
Definition hist_inv_content `{!noprolG Σ} : iProp Σ :=
  (∃ σ', ownP σ' ∗ hist_ctx σ')%I.

(** To realize the trick, we need a global namespace to allocate the invariant
  for the state interp *)
Definition histN : namespace := nroot .@ "history".

Definition hist_inv `{!noprolG Σ} : iProp Σ :=
  @inv _ _ (ownP_invG) histN hist_inv_content.

Definition hist_interp `{!noprolG Σ} σ : iProp Σ :=
  (own ownP_name (●E σ) ∗ hist_inv)%I.

Global Instance noprolG_irisG `{!noprolG Σ} : irisGS nopro_lang Σ := {
  iris_invGS := ownP_invG;
  state_interp σ _ _ n := hist_interp σ;
  num_laters_per_step _ := 0%nat;
  fork_post := (λ _, True)%I;
  state_interp_mono _ _ _ _ := fupd_intro _ _
}.

Global Opaque iris_invGS.

(** PROPERTIES ---------------------------------------------------------------*)

(** Properties of inter *)
Lemma inter_lookup_Some i j (n : nat):
  i ≤ j < i+n → inter i n !! j = Excl' ().
Proof.
  revert i. induction n as [|n IH]=>/= i; first lia.
  rewrite lookup_insert_Some. destruct (decide (i = j)); naive_solver lia.
Qed.

Lemma inter_lookup_None i j (n : nat):
  j < i ∨ i+n ≤ j → inter i n !! j = None.
Proof.
  revert i. induction n as [|n IH]=>/= i; first by rewrite lookup_empty.
  rewrite lookup_insert_None. naive_solver lia.
Qed.

Lemma inter_op i n n' : inter i n ⋅ inter (i+n) n' ≡ inter i (n+n').
Proof.
  intros j. rewrite lookup_op.
  destruct (decide (i ≤ j < i+n)); last destruct (decide (i+n ≤ j < i+n+n')).
  - by rewrite (inter_lookup_None (i+n) j n') ?inter_lookup_Some; try lia.
  - by rewrite (inter_lookup_None i j n) ?inter_lookup_Some; try lia.
  - by rewrite !inter_lookup_None; try lia.
Qed.

Lemma inter_valid i n : ✓ inter i n.
Proof. revert i. induction n as [|n IH]=>i; first done. by apply insert_valid. Qed.

(** Properties of hist_freeable_rel *)
Lemma hist_freeable_rel_None M l hF :
  (∀ m : Z, M !!c (l.1, m) = ∅) → hist_freeable_rel M hF →
  hF !! l.1 = None.
Proof.
  intros FRESH REL. apply eq_None_not_Some. intros [[q s] [Hsne REL']%REL].
  destruct (map_choose s Hsne) as [i NE%REL']. apply NE, FRESH.
Qed.

Lemma hist_freeable_is_Some M hF l n :
  hist_freeable_rel M hF →
  hF !! l.1 = Some (1%Qp, inter (l.2) n) →
  (0 < n)%nat ∧ (∀ i, M !!c (l >> i) ≠ ∅ ↔ 0 ≤ i ∧ i < n).
Proof.
  destruct l as [b j]; rewrite /shift_lblock /=. intros REL Hl.
  destruct (REL b (1%Qp, inter j n)) as [NEMP Iff]; [done|].
  split; [destruct n; [done|lia]|]. intros i.
  rewrite /location.shift /= Iff. destruct (decide (0 ≤ i ∧ i < n)).
  - rewrite is_Some_alt inter_lookup_Some; lia.
  - rewrite is_Some_alt inter_lookup_None; lia.
Qed.

Lemma hist_freeable_rel_stable M h l C (NE: C ≠ ∅):
  hist_freeable_rel M h → M !!c l ≠ ∅ →
  hist_freeable_rel (<[l := C]>M) h.
Proof.
  intros REL HM blk qs Hqs. destruct (REL blk qs) as [? REL']; first done.
  split; [done|]=> i. rewrite -REL'.
  rewrite /memory_cell_lookup memory_uncurry_insert_nonempty ; last done.
  case (decide (l = (blk, i))) => ?;
    [subst; by rewrite lookup_insert|by rewrite lookup_insert_ne].
Qed.

Lemma hist_freeable_rel_alloc l n h M1 M2 𝓥1 𝓥2 𝑚s
  (ALLOC: alloc_step 𝓥1 M1 l (Pos.to_nat n) 𝑚s 𝓥2 M2)
  (FRESH: ∀ m : Z, M1 !!c (l.1, m) = ∅) :
  hist_freeable_rel M1 h →
  hist_freeable_rel M2
                    (<[l.1 := (1%Qp, inter (l.2) (Pos.to_nat n))]> h).
Proof.
  move=> REL blk qs /lookup_insert_Some [[<- <-]|[??]]; first split.
  - destruct (Pos.to_nat n) eqn:?; [lia|apply: insert_non_empty].
  - intros i.
    destruct (decide (l.2 ≤ i < l.2 + (Pos.to_nat n))).
    + rewrite inter_lookup_Some //.
      have Inl: (l.1,i) ∈ dom M2 ∖ dom M1.
      { replace (l.1,i) with (l >> Z.to_nat (i - l.2))
          by (rewrite /location.shift /=; f_equal; lia).
        eapply alloc_step_mem_fresh; [by eauto|]. lia. }
      move : Inl => /elem_of_difference [/(elem_of_dom (M:=gmap loc)) Inl _].
      by rewrite is_Some_alt memory_cell_lookup_non_empty.
    + rewrite inter_lookup_None; [|lia].
      eapply alloc_step_mem_old in ALLOC; [|eauto].
      by rewrite ALLOC FRESH is_Some_alt.
  - destruct (REL blk qs) as [? Hs]; auto.
    split; [done|] => i. rewrite -Hs. erewrite alloc_step_mem_old_2; eauto.
Qed.

Lemma hist_freeable_rel_stable_list_addins (𝑚s: list message) M1 M2 h
  (ADD : mem_list_addins 𝑚s M1 M2)
  (IND : ∀ 𝑚 , 𝑚 ∈ 𝑚s → 𝑚.(mloc) ∈ dom M1) :
  hist_freeable_rel M1 h →
  hist_freeable_rel M2 h.
Proof.
  move => HF. revert M2 ADD.
  induction 𝑚s as [|𝑚 𝑚s IH] => M3 ADD; inversion ADD; subst; first done.
  rewrite (memory_addins_eq _ _ _ ADD0).
  apply hist_freeable_rel_stable.
  - apply insert_non_empty.
  - apply IH; [|done] => ??. apply IND. by right.
  - rewrite memory_cell_lookup_non_empty.
    apply elem_of_dom, (mem_list_addins_dom_mono _ _ _  NEXT), IND. by left.
Qed.

Lemma hist_freeable_rel_dealloc l n h M1 M2 𝓥1 𝓥2 𝑚s
  (DEALLOC: dealloc_step 𝓥1 M1 l (Pos.to_nat n) 𝑚s 𝓥2 M2) :
  hist_freeable_rel M1 h →
  hist_freeable_rel M2 h.
Proof.
  have IND: ∀ n' : nat, (n' < Pos.to_nat n)%nat → l >> n' ∈ dom M1.
  { move => n' /(dealloc_step_remove _ _ _ _ _ _ _ DEALLOC).
    by rewrite elem_of_intersection elem_of_difference => [[[? ?] ?]]. }
  have EQL:= dealloc_step_loc_eq _ _ _ _ _ _ _ DEALLOC.
  have INDM: ∀ 𝑚, 𝑚 ∈ 𝑚s → 𝑚.(mloc) ∈ dom M1.
  { move => 𝑚 /elem_of_list_lookup [n' Eqn'].
    rewrite (EQL _ _ Eqn'). apply IND. apply lookup_lt_Some in Eqn'.
    by rewrite -(dealloc_step_length _ _ _ _ _ _ _ DEALLOC). }
  inversion_clear DEALLOC. inversion_clear MEMALL.
  by eapply hist_freeable_rel_stable_list_addins.
Qed.

Section hist.
  Context `{!noprolG Σ}.
  Implicit Types (P Q : iProp Σ) (E : coPset).

  Global Instance hist_inv_timeless: Timeless hist_inv_content.
  Proof. rewrite /hist_inv_content. apply _. Qed.

  (** General properties of hist *)
  Global Instance hist_timeless l q C : Timeless (hist l q C).
  Proof. rewrite hist_eq. apply _. Qed.

  Global Instance hist_fractional l C: Fractional (λ q, hist l q C)%I.
  Proof. rewrite hist_eq. apply _. Qed.
  Global Instance hist_as_fractional l q C:
    AsFractional (hist l q C) (λ q, hist l q C)%I q.
  Proof. split; [done|apply _]. Qed.
  Global Instance frame_hist p l C q1 q2 RES :
    FrameFractionalHyps p (hist l q1 C) (λ q, hist l q C)%I RES q1 q2 →
    Frame p (hist l q1 C) (hist l q2 C) RES | 5.
  Proof. apply: frame_fractional. Qed.

  Lemma hist_agree l p1 p2 C1 C2:
    hist l p1 C1 ∗ hist l p2 C2 ⊢ ⌜C1 = C2⌝.
  Proof.
    rewrite hist_eq. iIntros "[h1 h2]".
    iDestruct (mapsto_agree with "h1 h2") as %?. iPureIntro. by simplify_eq.
  Qed.

  Lemma hist_combine l p1 p2 C1 C2:
    hist l p1 C1 ∗ hist l p2 C2 ⊢ hist l (p1 + p2) C1 ∗ ⌜ C1 = C2 ⌝.
  Proof.
    rewrite hist_eq. iIntros "[h1 h2]".
    iDestruct (mapsto_combine with "h1 h2") as "[$ %]".
    iPureIntro. by simplify_eq.
  Qed.

  Lemma hist_frac_1 l p C:
    hist l p C ⊢ ⌜ ✓ p ⌝.
  Proof. by rewrite hist_eq /hist_def mapsto_valid. Qed.

  (** Properties of freeable blocks *)
  Global Instance hist_freeable_timeless q l n : Timeless (†{q}l…n).
  Proof. rewrite hist_freeable_eq /hist_freeable_def. apply _. Qed.

  Lemma hist_freeable_op_eq l q1 q2 n n' :
    †{q1}l…n ∗ †{q2}l>>n … n' ⊣⊢ †{q1+q2}l…(n+n').
  Proof.
    by rewrite hist_freeable_eq /hist_freeable_def -own_op -auth_frag_op
      singleton_op -pair_op inter_op.
  Qed.

  Lemma hist_freeable_valid l n n' :
    †l…n -∗ †l…n' -∗ False.
  Proof.
    iIntros "†l †l'". iCombine "†l †l'" as "†l".
    rewrite hist_freeable_eq /hist_freeable_def -own_op -auth_frag_op singleton_op -pair_op own_valid.
    iDestruct "†l" as %H. rewrite auth_frag_valid singleton_valid pair_valid in H.
    destruct H as [H _]. rewrite frac_op frac_valid in H. done.
  Qed.

  Lemma hist_ctx_hist_freeable_agree l n hF :
    own hist_freeable_name (● hF) ∗ †l…n
    ⊢ ⌜hF !! l.1 = Some (1%Qp, inter (l.2) n)⌝.
  Proof.
    rewrite hist_freeable_eq -own_op. iIntros "own".
    iDestruct (own_valid with "own")
      as %[[[??] [Eq INCL]]%singleton_included_l ?]%auth_both_valid_discrete.
    apply Some_included_exclusive in INCL as [Eq1 Eq2];
      [|eauto with typeclass_instances|by apply (lookup_valid_Some hF (l.1))].
    simpl in Eq1, Eq2.
    iPureIntro. move : Eq. by rewrite -Eq1 -Eq2 leibniz_equiv_iff.
  Qed.

  Lemma hist_ctx_hist_freeable_blk l n σ:
    hist_ctx σ -∗ †l…n -∗
    ⌜(0 < n)%nat ∧ ∀ n' : nat, l >> n' ∈ dom σ.(mem) ↔ (n' < n)%nat⌝.
  Proof.
    iDestruct 1 as (???) "(_ & oHF & _ & _ & _ & _ & _ & WF)".
    iDestruct "WF" as %(_ & REL & _). iIntros "hf".
    iDestruct (hist_ctx_hist_freeable_agree with "[$oHF $hf]") as %Eq.
    iPureIntro. move : Eq => /(hist_freeable_is_Some _ _ _ _ REL) [? EQDOM].
    split; [done|]=> ?.
    rewrite (elem_of_dom (M:=gmap loc)) -memory_cell_lookup_non_empty EQDOM. lia.
  Qed.

  (** Properties of naread *)
  Global Instance naread_timeless l q rs : Timeless (naread l q rs).
  Proof. rewrite naread_eq. apply _. Qed.

  Global Instance naread_fractional l rs: Fractional (λ q, naread l q rs)%I.
  Proof.
    intros ??.
    by rewrite naread_eq -own_op -auth_frag_op singleton_op frac_lat_op lat_join_idem_L.
  Qed.
  Global Instance naread_as_fractional l q rs:
    AsFractional (naread l q rs) (λ q, naread l q rs)%I q.
  Proof. split; [done|apply _]. Qed.
  Global Instance frame_naread p l rs q1 q2 RES :
    FrameFractionalHyps p (naread l q1 rs) (λ q, naread l q rs)%I RES q1 q2 →
    Frame p (naread l q1 rs) (naread l q2 rs) RES | 5.
  Proof. apply: frame_fractional. Qed.

  Lemma naread_combine l q1 q2 rs1 rs2:
    naread l q1 rs1 -∗ naread l q2 rs2 -∗ naread l (q1 + q2) (rs1 ∪ rs2).
  Proof.
    iIntros "H1 H2". rewrite naread_eq. iCombine "H1" "H2" as "H".
    by rewrite lat_op_join'.
  Qed.

  Lemma hist_ctx_naread_included 𝓝  l q rs:
    own hist_naread_name (● to_nar 𝓝) ∗ naread l q rs
    ⊢ ⌜Some rs ⊑ 𝓝 !!nr l⌝.
  Proof.
    rewrite naread_eq /naread_def -own_op. iIntros "own".
    iDestruct (own_valid with "own")
      as %[[[q' rs'] [Eqp INCL%Some_included]]%singleton_included_l ?]%auth_both_valid_discrete.
    iPureIntro. move : Eqp.
    destruct (to_nar 𝓝 !! l) as [[q1 rs1]|] eqn:Eq ; rewrite Eq; last by inversion 1.
    intros [Eq1 Eq2]%(inj Some). simpl in Eq1, Eq2. inversion Eq1. subst q1.
    apply leibniz_equiv_iff in Eq2. subst rs1. clear Eq1.
    move :Eq. rewrite lookup_fmap /=.
    destruct (𝓝 !! l) as [[]|] eqn:Eq2; rewrite Eq2 /=; [|done].
    inversion 1. subst. rewrite (view_lookup_nr _ _ _ _ _ _ Eq2).
    move : INCL => [[_ /to_latT_inj /leibniz_equiv_iff -> //]|
                     /frac_lat_included [_ //]].
  Qed.

  Lemma hist_ctx_naread_full 𝓝  l rs:
    own hist_naread_name (● to_nar 𝓝) ∗ naread l 1 rs
    ⊢ ⌜Some rs = 𝓝 !!nr l⌝.
  Proof.
    rewrite naread_eq /naread_def -own_op. iIntros "own".
    iDestruct (own_valid with "own")
      as %[[[q' rs'] [Eqp INCL%Some_included]]%singleton_included_l ?]%auth_both_valid_discrete.
    iPureIntro. move : Eqp.
    destruct (to_nar 𝓝 !! l) as [[q1 rs1]|] eqn:Eq ; rewrite Eq; last by inversion 1.
    intros [Eq1 Eq2]%(inj Some). simpl in Eq1, Eq2. inversion Eq1. subst q1.
    apply leibniz_equiv_iff in Eq2. subst rs1. clear Eq1.
    move :Eq. rewrite lookup_fmap /=.
    destruct (𝓝 !! l) as [[]|] eqn:Eq2; rewrite Eq2 /=; [|done].
    inversion 1. subst. rewrite (view_lookup_nr _ _ _ _ _ _ Eq2).
    move : INCL => [[_ /to_latT_inj /leibniz_equiv_iff -> //]|
                     /prod_included [/= /frac_included INCL //]].
  Qed.

  (** Properties of atread *)
  Global Instance atread_timeless l q rs : Timeless (atread l q rs).
  Proof. rewrite atread_eq. apply _. Qed.

  Global Instance atread_fractional l rs: Fractional (λ q, atread l q rs)%I.
  Proof.
    intros ??.
    by rewrite atread_eq -own_op -auth_frag_op singleton_op frac_lat_op lat_join_idem_L.
  Qed.
  Global Instance atread_as_fractional l q rs:
    AsFractional (atread l q rs) (λ q, atread l q rs)%I q.
  Proof. split; [done|apply _]. Qed.
  Global Instance frame_atread p l rs q1 q2 RES :
    FrameFractionalHyps p (atread l q1 rs) (λ q, atread l q rs)%I RES q1 q2 →
    Frame p (atread l q1 rs) (atread l q2 rs) RES | 5.
  Proof. apply: frame_fractional. Qed.

  Lemma atread_combine l q1 q2 rs1 rs2:
    atread l q1 rs1 -∗ atread l q2 rs2 -∗ atread l (q1 + q2) (rs1 ∪ rs2).
  Proof.
    iIntros "H1 H2". rewrite atread_eq. iCombine "H1" "H2" as "H".
    by rewrite lat_op_join'.
  Qed.

  Lemma hist_ctx_atread_included 𝓝  l q rs:
    own hist_atread_name (● to_atr 𝓝) ∗ atread l q rs
    ⊢ ⌜Some rs ⊑ 𝓝 !!ar l⌝.
  Proof.
    rewrite atread_eq /atread_def -own_op. iIntros "own".
    iDestruct (own_valid with "own")
      as %[[[q' rs'] [Eqp INCL%Some_included]]%singleton_included_l ?]%auth_both_valid_discrete.
    iPureIntro. move : Eqp.
    destruct (to_atr 𝓝 !! l) as [[q1 rs1]|] eqn:Eq; rewrite Eq; last by inversion 1.
    intros [Eq1 Eq2]%(inj Some). simpl in Eq1, Eq2. inversion Eq1. subst q1.
    apply leibniz_equiv_iff in Eq2. subst rs1. clear Eq1.
    move :Eq. rewrite lookup_fmap /=.
    destruct (𝓝 !! l) as [[]|] eqn:Eq2; rewrite Eq2 /=; [|done].
    inversion 1. subst. rewrite (view_lookup_ar _ _ _ _ _ _ Eq2).
    move : INCL => [[_ /to_latT_inj /leibniz_equiv_iff -> //]|
                     /frac_lat_included [_ //]].
  Qed.

  Lemma hist_ctx_atread_full 𝓝  l rs:
    own hist_atread_name (● to_atr 𝓝) ∗ atread l 1 rs
    ⊢ ⌜Some rs = 𝓝 !!ar l⌝.
  Proof.
    rewrite atread_eq /atread_def -own_op. iIntros "own".
    iDestruct (own_valid with "own")
      as %[[[q' rs'] [Eqp INCL%Some_included]]%singleton_included_l ?]%auth_both_valid_discrete.
    iPureIntro. move : Eqp.
    destruct (to_atr 𝓝 !! l) as [[q1 rs1]|] eqn:Eq ; rewrite Eq; last by inversion 1.
    intros [Eq1 Eq2]%(inj Some). simpl in Eq1, Eq2. inversion Eq1. subst q1.
    apply leibniz_equiv_iff in Eq2. subst rs1. clear Eq1.
    move :Eq. rewrite lookup_fmap /=.
    destruct (𝓝 !! l) as [[]|] eqn:Eq2; rewrite Eq2 /=; [|done].
    inversion 1. subst. rewrite (view_lookup_ar _ _ _ _ _ _ Eq2).
    move : INCL => [[_ /to_latT_inj /leibniz_equiv_iff -> //]|
                     /prod_included [/= /frac_included INCL //]].
  Qed.

  (** Properties of atwrite *)
  Global Instance atwrite_timeless l q ws : Timeless (atwrite l q ws).
  Proof. rewrite atwrite_eq. apply _. Qed.

  Global Instance atwrite_fractional l rs:
    Fractional (λ q, atwrite l q rs)%I.
  Proof.
    intros ??.
    by rewrite atwrite_eq -own_op -auth_frag_op singleton_op -frac_agree_op.
  Qed.
  Global Instance atwrite_as_fractional l q rs:
    AsFractional (atwrite l q rs) (λ q, atwrite l q rs)%I q.
  Proof. split; [done|apply _]. Qed.
  Global Instance frame_atwrite p l rs q1 q2 RES :
    FrameFractionalHyps p (atwrite l q1 rs) (λ q, atwrite l q rs)%I RES q1 q2 →
    Frame p (atwrite l q1 rs) (atwrite l q2 rs) RES | 5.
  Proof. apply: frame_fractional. Qed.

  Lemma atwrite_agree l q1 q2 rs1 rs2:
    atwrite l q1 rs1 ∗ atwrite l q2 rs2 -∗ ⌜rs1 = rs2⌝.
  Proof.
    rewrite atwrite_eq -own_op -auth_frag_op singleton_op own_valid.
    by iDestruct 1
      as %[_ ?%leibniz_equiv]%auth_frag_valid_1%singleton_valid%frac_agree_op_valid.
  Qed.

  Lemma atwrite_combine l q1 q2 rs1 rs2:
    atwrite l q1 rs1 ∗ atwrite l q2 rs2
    ⊢ atwrite l (q1 + q2) rs1.
  Proof.
    iIntros "[H1 H2]".
    iDestruct (atwrite_agree with "[$H1 $H2]") as %<-. iFrame.
  Qed.

  Lemma hist_ctx_atwrite_agree_1 𝓝 l q rs:
    own hist_atwrite_name (● to_atw 𝓝) ∗ atwrite l q rs
    ⊢ ⌜to_atw 𝓝 !! l = Some (to_frac_agree 1 (rs : gset.gsetO _))⌝.
  Proof.
    rewrite atwrite_eq /atwrite_def -own_op own_valid.
    iDestruct 1 as
      %[[y [HL INCL%Some_included]]%singleton_included_l ?]%auth_both_valid_discrete.
    iPureIntro. revert HL INCL. rewrite !lookup_fmap.
    destruct lookup; [|by inversion 1]=> /= HL.
    apply (inj Some) in HL. rewrite <- HL. move=>/= [|].
    - by intros [_ ->%leibniz_equiv]%to_dfrac_agree_inj.
    - by intros [? ->]%frac_agree_included_L.
  Qed.

  Lemma hist_ctx_atwrite_agree 𝓝 l q rs:
    own hist_atwrite_name (● to_atw 𝓝) ∗ atwrite l q rs
    ⊢ ⌜𝓝 !!aw l = Some rs⌝.
  Proof.
    rewrite hist_ctx_atwrite_agree_1.
    iIntros (Eq). iPureIntro. move :Eq.
    rewrite /to_atw lookup_fmap /view_lookup_awrite.
    destruct (𝓝 !! l) eqn:Eql; rewrite Eql /= //. by move => [->].
  Qed.

  (** Properties of seen *)
  Global Instance seen_timeless 𝓥: Timeless (seen 𝓥).
  Proof. rewrite seen_eq. apply _. Qed.

  Global Instance seen_persistent 𝓥: Persistent (seen 𝓥).
  Proof. rewrite seen_eq. apply _. Qed.

  Global Instance seen_mono : Proper ((⊑) ==> flip (⊢)) seen.
  Proof.
    rewrite seen_eq /seen_def. iIntros (?? Ext) "own".
    iApply (@own_lat_auth_downclosed with "own"). apply Ext.
  Qed.
  Global Instance seen_mono_flip : Proper (flip (⊑) ==> (⊢)) seen.
  Proof. intros ???. by apply seen_mono. Qed.

  (** Properties of sc_view *)
  Global Instance sc_view_timeless 𝓢: Timeless (sc_view 𝓢).
  Proof. rewrite sc_view_eq. apply _. Qed.

  Global Instance sc_view_persistent 𝓢: Persistent (sc_view 𝓢).
  Proof. rewrite sc_view_eq. apply _. Qed.

  (** Wellformedness *)

  Lemma hist_ctx_seen_closed σ 𝓥: hist_ctx σ -∗ seen 𝓥 -∗ ⌜𝓥 ∈ σ.(mem)⌝.
  Proof.
    iDestruct 1 as (hF V Vc) "(_ & _ & _ & _ & _ & _ & oA & wf)".
    iDestruct "wf" as %(_ & ? & ? & ?).
    rewrite seen_eq. iIntros "oV".
    iCombine "oA oV"
      gives %[Le%latT_included _]%auth_both_valid_discrete. simpl in Le.
    iPureIntro. apply closed_tview_acq_inv. by rewrite Le.
  Qed.

  Lemma hist_ctx_wf_state σ : hist_ctx σ -∗ ⌜Wf σ⌝.
  Proof. by iDestruct 1 as (???) "(_ & _ & _ & _ & _ & _ & _ & ? & _)". Qed.

  Lemma hist_ctx_seen_wf σ 𝓥 :
    hist_ctx σ -∗ seen 𝓥 -∗ ⌜Wf σ ∧ 𝓥 ∈ σ.(mem)⌝.
  Proof.
    iIntros "Hσ H𝓥".
    iDestruct (hist_ctx_wf_state with "Hσ") as %?.
    by iDestruct (hist_ctx_seen_closed with "Hσ H𝓥") as %?.
  Qed.

  Lemma hist_ctx_seen_config_wf σ 𝓥:
    hist_ctx σ -∗ seen 𝓥 -∗ ⌜Wf (mkCFG 𝓥 σ)⌝.
  Proof.
    iIntros "Hσ H𝓥".
    iDestruct (hist_ctx_seen_wf with "Hσ H𝓥") as %(?&?).
    iPureIntro. by constructor.
  Qed.

  Lemma hist_ctx_sc_view_included σ 𝓢:
    hist_ctx σ -∗ sc_view 𝓢 -∗ ⌜𝓢 ⊑ σ.(sc)⌝.
  Proof.
    iDestruct 1 as (???) "(_ & _ & _ &_ & _ & HSC & _)". iIntros "SC".
    rewrite sc_view_eq. iApply (@own_lat_auth_max with "HSC SC").
  Qed.

  Lemma hist_ctx_sc_view σ :
    hist_ctx σ ==∗ hist_ctx σ ∗ sc_view σ.(sc).
  Proof.
    iDestruct 1 as (hF V M) "(MEM & HF & ? & ? & ? & SC & VT & WF)".
    rewrite sc_view_eq.
    iMod (own_lat_auth_update _ _ σ.(sc) with "SC") as "[? $]"; [done|].
    iModIntro. iExists _,_,_. by iFrame.
  Qed.


  (** Properties of hist *)
  Lemma hist_own_to_hist_lookup M l q C :
    gen_heap_interp (to_hist M) -∗ hist l q C -∗ ⌜ to_hist M !! l = Some (Some C) ⌝.
  Proof.
    rewrite hist_eq. iIntros "H h". iApply (gen_heap_valid with "H h").
  Qed.

  Lemma hist_own_hist_cut M 𝓝 l q C :
    gen_heap_interp (to_hist (mem_cut M 𝓝)) -∗ hist l q C -∗
      ⌜∃ t, 𝓝 !!w l = Some t ∧ C = cell_cut t (M !!c l)
          ∧ ¬ cell_deallocated C ∧ ¬ cell_deallocated (M !!c l)
          ∧ (M !!c l) ≠ ∅
          ∧ C ≠ ∅⌝.
  Proof.
    iIntros "HA hist".
    iDestruct (hist_own_to_hist_lookup with "HA hist") as %Eq.
    edestruct to_hist_lookup_Some as (HL & ALLOC & NEMP); first by apply reflexive_eq.
    iPureIntro. rewrite /memory_cell_lookup in HL. clear Eq.
    destruct (gmap_curry (mem_cut M 𝓝) !! l) as [Cc|] eqn:Eq; subst C; last done.
    have EqC := (mem_cut_lookup M 𝓝 l).
    rewrite /memory_cell_lookup in EqC. rewrite Eq /= in EqC. simpl in NEMP.
    destruct (𝓝 !!w l) as [t|] eqn:Eqt; simpl in EqC; last done.
    exists t. repeat split; [by subst Cc|done|..|done].
    - destruct (map_choose _ NEMP) as [te [me Eqe]].
      move => /cell_deallocated_correct1 [tm [mm [Eqmm [Vmm MAX]]]].
      apply ALLOC, cell_deallocated_correct2. exists tm, mm. simpl.
      repeat split; [|done|].
      + move : Eqe.  rewrite EqC 2!cell_cut_lookup_Some => [[Eqe Le]].
        split; [done|]. etrans; [exact Le|]. apply MAX, elem_of_dom. by eexists.
      + move => t' /elem_of_dom [m' Eqm']. apply MAX, (cell_cut_dom t).
        rewrite -EqC. apply elem_of_dom. by eexists.
    - rewrite /memory_cell_lookup. intros EMP. by rewrite EMP in EqC.
  Qed.

  Lemma hist_ctx_hist_cut σ l q C :
    hist_ctx σ -∗ hist l q C -∗
    ⌜∃ Vc, σ.(na) ⊑ Vc ∧
      ∃ t, Vc !!w l = Some t ∧ C = cell_cut t (σ.(mem) !!c l)
      ∧ ¬ cell_deallocated C ∧ ¬ cell_deallocated (σ.(mem) !!c l)
      ∧ (σ.(mem) !!c l) ≠ ∅
      ∧ C ≠ ∅⌝.
  Proof.
    iIntros "Ctx hist".
    iDestruct "Ctx" as (hF V Vc) "(HA & _ & _ & _ & _ & _ &(_&_&_&_&%))".
    iDestruct (hist_own_hist_cut with "HA hist") as %?.
    iPureIntro. by exists Vc.
  Qed.

  Lemma hist_ctx_hist_allocated σ l q C:
    hist_ctx σ -∗ hist l q C -∗ ⌜allocated l σ.(mem)⌝.
  Proof.
    iIntros "ctx hist".
    iDestruct (hist_ctx_hist_cut with "ctx hist") as %(?&_&?&_&_&_&ALLOC&_).
    iDestruct (hist_ctx_wf_state with "ctx") as %WF. iPureIntro.
    apply (allocated_cell_deallocated _ _ ALLOC), WF.
  Qed.

  Lemma hist_ctx_hist_loc_cell_wf σ l q C:
    hist_ctx σ -∗ hist l q C -∗ ⌜loc_cell_wf l C⌝.
  Proof.
    iIntros "ctx hist".
    iDestruct (hist_ctx_hist_cut with "ctx hist") as %(?&_&t&_&EqC&_).
    iDestruct (hist_ctx_wf_state with "ctx") as %WF. iPureIntro.
    assert (WFl := mem_wf_loc_cell _ (global_wf_mem _ WF) l).
    rewrite EqC. clear -WFl.
    intros t0 m0 [Eqt0 ?]%cell_cut_lookup_Some. revert Eqt0. apply WFl.
  Qed.

  Lemma hist_own_lookup M l q C :
    gen_heap_interp (to_hist M) -∗ hist l q C -∗ ⌜M !!c l = C⌝.
  Proof.
    iIntros "H h".
    by iDestruct (hist_own_to_hist_lookup with "H h") as %[]%to_hist_lookup_Some.
  Qed.

  Lemma hist_ctx_alloc_local_drf σ V l q C
    (ALLOC: alloc_local l C V) :
    hist_ctx σ -∗ hist l q C -∗ ⌜σ.(na) !!w l ⊑ V !!w l⌝.
  Proof.
    iIntros "ctx hist".
    iDestruct (hist_ctx_hist_cut with "ctx hist") as %[?[Le[?[Eqt [CUT _]]]]].
    iPureIntro. etrans; [by apply view_sqsubseteq,Le|].
    rewrite Eqt. subst C. by eapply alloc_local_cut.
  Qed.

  Lemma hist_ctx_naread_eq σ l rs:
    hist_ctx σ -∗ naread l 1 rs -∗ ⌜σ.(na) !!nr l = Some rs⌝.
  Proof.
    iDestruct 1 as (???) "(?&?&NA&_)". iIntros "na".
    by iDestruct (hist_ctx_naread_full with "[$NA $na]") as %?.
  Qed.

  Lemma hist_ctx_na_local_drf σ V l rs
    (NAL: na_local l rs V):
    hist_ctx σ -∗ naread l 1 rs -∗ ⌜σ.(na) !!nr l ⊑ V !!nr l⌝.
  Proof.
    iIntros "ctx na". by iDestruct (hist_ctx_naread_eq with "ctx na") as %->.
  Qed.

  Lemma hist_ctx_atread_eq σ l rs:
    hist_ctx σ -∗ atread l 1 rs -∗ ⌜σ.(na) !!ar l = Some rs⌝.
  Proof.
    iDestruct 1 as (???) "(?&?&_&_&AT&_)". iIntros "at".
    by iDestruct (hist_ctx_atread_full with "[$AT $at]") as %?.
  Qed.

  Lemma hist_ctx_atread_local_drf σ V l rs
    (ATL: atr_local l rs V):
    hist_ctx σ -∗ atread l 1 rs -∗ ⌜σ.(na) !!ar l ⊑ V !!ar l⌝.
  Proof.
    iIntros "ctx at". by iDestruct (hist_ctx_atread_eq with "ctx at") as %->.
  Qed.

  Lemma hist_ctx_atwrite_eq σ l q rs:
    hist_ctx σ -∗ atwrite l q rs -∗ ⌜σ.(na) !!aw l = Some rs⌝.
  Proof.
    iDestruct 1 as (???) "(?&?&_&AT&_)". iIntros "at".
    by iDestruct (hist_ctx_atwrite_agree with "[$AT $at]") as %?.
  Qed.

  Lemma hist_ctx_atwrite_local_drf σ V l q rs
    (ATL: atw_local l rs V):
    hist_ctx σ -∗ atwrite l q rs -∗ ⌜σ.(na) !!aw l ⊑ V !!aw l⌝.
  Proof.
    iIntros "ctx at". by iDestruct (hist_ctx_atwrite_eq with "ctx at") as %->.
  Qed.

  Lemma hist_ctx_hist_good σ l q C :
    hist_ctx σ -∗ hist l q C -∗ ⌜good_hist C⌝.
  Proof.
    iIntros "ctx hist".
    iDestruct (hist_ctx_hist_cut with "ctx hist")as % (?&_&?&_&?&?&_&_&?).
    iDestruct (hist_ctx_wf_state with "ctx") as %WFs%global_wf_alloc. subst C.
    iPureIntro. constructor; [done..| |].
    - by apply cell_cut_cell_alloc_inv, WFs.
    - by apply cell_cut_cell_dealloc_inv, WFs.
  Qed.

  (** hist_ctx ghost updates *)
  Lemma seen_own_join V (𝓥: threadView) :
    own hist_gtime_name (◯ (to_latT (V ⊔ 𝓥.(acq)))) -∗ seen 𝓥.
  Proof.
    iIntros "HV". rewrite seen_eq.
    iDestruct (own_lat_auth_downclosed _ _ 𝓥.(acq) with "HV")
      as "$"; first solve_lat.
  Qed.

  (* This rule is not the strongest one we can get, but it is enough for
    gaining non-atomic permission *)
  Lemma hist_ctx_hist_drop_singleton σ l C (t: time) m
    (MAX: ∀ (t': time), is_Some (C !! t') → (t' ≤ t)%positive)
    (Eqv: m.(mval) ≠ DVal) :
    hist_ctx σ -∗ hist l 1 (<[t:=m]> C) ==∗ hist_ctx σ ∗ hist l 1 {[t := m]}.
  Proof.
    iDestruct 1 as (hF V Vc) "(own & HhF & Hna & Haw & Har & Hsc & HV & HF)".
    iDestruct "HF" as %(WF & HhF & HC & LE). iIntros "hist".
    iDestruct (hist_own_hist_cut with "own hist") as %(tc&Eqt&EqC&?&?&?&?).
    iDestruct (hist_own_to_hist_lookup with "own hist") as %EqC'.
    rewrite hist_eq.
    iMod (gen_heap_update with "own hist") as "[own $]".
    iModIntro. iExists _,_,(set_write_time Vc l t). iFrame. iSplitL.
    - rewrite -to_hist_insert_alloc;
        [rewrite (mem_cut_max_time _ _ m _ (<[t:=m]> C) _ tc)|..];
        [done|done| |by rewrite lookup_insert|..].
      + move => t0. case (decide (t0 = t)) => [->//|?].
        rewrite lookup_insert_ne; [by apply MAX|done].
      + destruct (view_lookup_of_wp _ _ _ Eqt) as [? [? ?]]. by eexists.
      + by apply cell_deallocated_neg_singleton.
      + move => Eq. apply (f_equal (lookup t)) in Eq.
        by rewrite lookup_insert in Eq.
    - iPureIntro. split; last split; last split; [done..|]. rewrite LE => l'.
      rewrite /set_write_time.
      case (decide (l' = l)) =>[->|?];
        [rewrite lookup_partial_alter|by rewrite lookup_partial_alter_ne].
      destruct (Vc !! l) as [[t' ? ? ?]|] eqn:EqVc; rewrite EqVc; [|done].
      split; simpl; last done.
      rewrite (view_lookup_w _ _ _ _ _ _ EqVc) in Eqt. inversion Eqt. subst t'.
      apply (cell_cut_lookup_Some (σ.(mem) !!c l) _ _ m).
      by rewrite -EqC lookup_insert.
  Qed.

  (* alloc *)
  Lemma hist_ctx_alloc_vs M M' 𝓢 𝓢' 𝓝 𝓝' 𝓥 𝓥' l n Vc 𝑚s
    (STEP: machine_step 𝓥 M 𝓢 (event.Alloc l n) None 𝑚s 𝓥' M' 𝓢')
    (DRFPost: drf_post 𝓝 (event.Alloc l n) None 𝑚s 𝓝')
    (LE: 𝓝 ⊑ Vc) (INM: 𝓝 ∈ M) (WFM: Wf M):
    gen_heap_interp (to_hist (mem_cut M Vc)) ∗
    own hist_atread_name (● to_atr 𝓝) ∗
    own hist_atwrite_name (● to_atw 𝓝) ∗
    own hist_naread_name (● to_nar 𝓝)
    ==∗ ∃ Vc', ⌜𝓝' ⊑ Vc'⌝
      ∗ (gen_heap_interp (to_hist (mem_cut M' Vc'))
        ∗ [∗ list] i ↦ C ∈ (cell_list l (Pos.to_nat n) M'),
            (hist (l >> i) 1 C ∗ meta_token (l >> i) ⊤))
      ∗ (own hist_atread_name (● to_atr 𝓝')
        ∗ ([∗ list] i ∈ seq 0 (Pos.to_nat n),
            own hist_atread_name (◯ {[l >> i := (1%Qp, to_latT ∅)]})))
      ∗ (own hist_atwrite_name (● to_atw 𝓝')
        ∗ ([∗ list] i ∈ seq 0 (Pos.to_nat n),
          own hist_atwrite_name (◯ {[l >> i := to_frac_agree 1 ∅]})))
      ∗ (own hist_naread_name (● to_nar 𝓝')
        ∗ ([∗ list] i ∈ seq 0 (Pos.to_nat n),
          own hist_naread_name (◯ {[l >> i := (1%Qp, to_latT ∅)]}))).
  Proof.
    inversion_clear STEP.
    have FRESH := alloc_step_mem_fresh _ _ _ _ _ _ _ ALLOC.
    rewrite -(alloc_step_length _ _ _ _ _ _ _ ALLOC) in FRESH.
    have DISJ := alloc_step_disjoint  _ _ _ _ _ _ _ ALLOC.
    rewrite (alloc_step_cell_list_map _ _ _ _ _ _ _ ALLOC).
    inversion_clear ALLOC. inversion_clear MEMALL. rewrite -LEN.
    inversion_clear DRFPost. clear ALLOC LEN VALL n.
    revert l M' Vc AMES ADD FRESH LE.
    induction 𝑚s as [|𝑚 𝑚s IH] => l M3 Vc AMES ADD FRESH LE.
    { inversion ADD; subst; simpl in *. iIntros "(o1 & o2 & o3 & o4)".
      iExists Vc. iSplitL""; [done|]. by iFrame. }
    rewrite fmap_cons big_opL_cons.
    have Eq𝑚: 𝑚.(mloc) = l >> 0 by apply AMES.
    have NEqL := mem_list_disj_cons_rest _ _ DISJ.
    inversion_clear ADD.
    assert (HN: M2 !!c mloc 𝑚 = ∅).
    { rewrite -(mem_list_addins_old _ _ _ _ NEXT) /=; last done.
      rewrite memory_cell_lookup_empty Eq𝑚. move : (FRESH 0%nat).
      rewrite elem_of_difference => /= HL. apply HL. clear. by lia. }
    etrans; [apply (IH (mem_list_disj_cons _ _ DISJ) (l >> 1%nat))|];
      [|done| |done|]; clear IH.
    - intros. rewrite shift_nat_assoc. by apply AMES.
    - move => n' Lt. rewrite shift_nat_assoc elem_of_difference. split.
      + assert (is_Some ((𝑚 :: 𝑚s) !! (1 + n')%nat)) as [𝑚' Eq𝑚'].
        { apply lookup_lt_is_Some. simpl. by lia. }
        move : (AMES (1+n')%nat 𝑚' Eq𝑚') => [<- _].
        apply (mem_list_addins_dom _ _ _ NEXT), elem_of_list_lookup.
        by exists n'.
       + assert (l >> (1 + n')%nat ∈ dom M3 ∖ dom M)
          as [_ ?]%elem_of_difference; [apply FRESH; simpl; lia|done].
    - simpl.
      iMod 1 as (Vc' LE') "((o&o') & (or&or') & (owa&owa') & (on&on'))".
      iExists (<[𝑚.(mloc):= [{ 𝑚.(mto),∅,∅,∅ }] ]> Vc'). iSplitL "".
      { iPureIntro. by rewrite -> LE'. }
      rewrite (mem_cut_addins_na _ _ _ _ _ _ _ ADD0).
      iDestruct (big_sepL_mono with "o'") as "$".
      { intros k' ? _. by rewrite /= shift_nat_assoc. }
      rewrite HN cell_cut_empty_2 -Eq𝑚.
      iSplitL "o"; last iSplitL "or or'"; last iSplitL "owa owa'".
      + rewrite to_hist_insert_alloc; [..|by apply insert_non_empty]; last first.
        { rewrite /cell_deallocated /cell_max gmap_top_singleton.
          destruct (AMES 0%nat 𝑚) as [_ [EqA _]]; [done|by rewrite EqA]. }
        rewrite hist_eq.
        iMod (gen_heap_alloc with "o") as "($ & $ & $)"; [|done].
        apply to_hist_lookup_None. rewrite mem_cut_lookup HN /=.
        destruct (Vc' !!w _); [apply cell_cut_empty_2|done].
      + rewrite bi.sep_assoc -own_op. iSplitR "or'".
        * iMod (own_update with "or") as "$"; [|done]. rewrite to_atr_insert.
          apply auth_update_alloc, alloc_local_update; [|done].
          apply to_atr_lookup_None, (closed_view_memory_None _ _ _ HN).
          by apply (closed_na_view_list_addins _ _ _ _ INM NEXT).
        * rewrite -(fmap_S_seq 0) big_sepL_fmap.
          iApply (big_sepL_mono with "or'") => ? i  ? /=.
          by rewrite shift_lblock_assoc.
      + rewrite bi.sep_assoc -own_op. iSplitR "owa'".
        * iMod (own_update with "owa") as "$"; [|done]. rewrite to_atw_insert.
          apply auth_update_alloc, (alloc_local_update (to_atw _)); [|done].
          apply to_atw_lookup_None, (closed_view_memory_None _ _ _ HN).
          by apply (closed_na_view_list_addins _ _ _ _ INM NEXT).
        * rewrite -(fmap_S_seq 0) big_sepL_fmap.
          iApply (big_sepL_mono with "owa'") => ? i  ? /=.
          by rewrite shift_lblock_assoc.
      + rewrite bi.sep_assoc -own_op. iSplitR "on'".
        * iMod (own_update with "on") as "$"; [|done]. rewrite to_nar_insert.
          apply auth_update_alloc, alloc_local_update; [|done].
          apply to_nar_lookup_None, (closed_view_memory_None _ _ _ HN).
          by apply (closed_na_view_list_addins _ _ _ _ INM NEXT).
        * rewrite -(fmap_S_seq 0) big_sepL_fmap.
          iApply (big_sepL_mono with "on'") => ? i  ? /=.
          by rewrite shift_lblock_assoc.
  Qed.

  Lemma hist_ctx_alloc σ σ' 𝓥 𝓥' l n 𝑚s
    (STEP: machine_step 𝓥 σ.(mem) σ.(sc) (event.Alloc l n) None 𝑚s 𝓥' σ'.(mem) σ'.(sc))
    (DRFPost: drf_post σ.(na) (event.Alloc l n) None 𝑚s σ'.(na))
    (CLOSED: 𝓥 ∈ σ.(mem)) (AINV: alloc_inv σ.(mem)):
    hist_ctx σ ==∗
      hist_ctx σ' ∗ †l…(Pos.to_nat n)
      ∗ ([∗ list] i ↦ C ∈ cell_list l (Pos.to_nat n) σ'.(mem),
            hist (l >> i) 1 C ∗ meta_token (l >> i) ⊤ ∗ ⌜good_hist C⌝)
      ∗ ([∗ list] i ∈ seq 0%nat (Pos.to_nat n),
            atread (l >> i) 1%Qp ∅)
      ∗ ([∗ list] i ∈ seq 0%nat (Pos.to_nat n),
            atwrite (l >> i) 1%Qp ∅)
      ∗ ([∗ list] i ∈ seq 0%nat (Pos.to_nat n),
            naread (l >> i) 1%Qp ∅)
      ∗ seen 𝓥' ∗ ⌜𝓥 ⊑ 𝓥'⌝.
  Proof.
    iDestruct 1 as (hF V Vc) "(Hhσ & HhF & Hna & Haw & Har & Hsc & HV & HF)".
    iDestruct "HF" as %(WF & HhF & HC & LE).
    have FRESH: ∀ m, σ.(mem) !!c (l.1, m) = ∅.
    { move => ?. rewrite memory_cell_lookup_empty.
      inversion_clear STEP. inversion_clear ALLOC. apply MEMALL. }
    iMod (hist_ctx_alloc_vs _ _ _ _ _ _ _ _ _ _ _ _ STEP DRFPost LE
      with "[$Hhσ $Har $Haw $Hna]") as (Vc' LE')
        "((Hhσ'&Hh) & (Har'&Har) & (Haw'&Haw) & Hna' & Hn)"; [apply WF..|].
    iMod (own_update _ (● hF) with "HhF") as "[HhF Hfreeable]".
    { apply auth_update_alloc,
        (alloc_singleton_local_update _ (l.1) (1%Qp, inter (l.2) (Pos.to_nat n))).
      - by eapply hist_freeable_rel_None.
      - split; [done|apply inter_valid]. }
    iMod (own_lat_auth_update_join _ _ 𝓥'.(acq) with "HV")
      as "[HV' HV]".
    iAssert (hist_ctx σ')%I with "[Hna' Har' Haw' HV' Hhσ' HhF Hsc]" as "Hσ'".
    { iExists _, _, Vc'. iFrame "Hhσ' Hna' Har' Haw' HV' HhF".
      iSplitL "Hsc"; [by inversion STEP|iPureIntro].
      split; [..|split];[..|split];[..|done].
      - apply (machine_step_global_wf _ _ _ _ _ _ _ STEP); eauto. constructor.
      - inversion STEP. by eapply hist_freeable_rel_alloc.
      - by eapply machine_step_view_join_update. }
    iAssert (⌜∀ i C, cell_list l (Pos.to_nat n) σ'.(mem) !! i = Some C
                 → good_hist C⌝)%I as %GH.
    { iIntros (t C EqC).
      iApply (hist_ctx_hist_good with "Hσ'").
      iDestruct (big_sepL_lookup _ _ _ _ EqC with "Hh") as "[$ ?]". }
    iModIntro. iFrame "Hσ'".
    iDestruct (seen_own_join with "HV") as "$".
    rewrite hist_freeable_eq. iFrame.
    iSplitL "Hh"; [|iSplitL "Har"; last iSplitL "Haw"]; last iSplit.
    + iApply (big_sepL_mono with "Hh").
      intros k' C' HC'%GH. by iIntros "[$ $]".
    + by rewrite atread_eq.
    + by rewrite atwrite_eq.
    + by rewrite naread_eq.
    + iPureIntro. by apply (machine_step_tview_sqsubseteq _ _ _ _ _ _ _ _ _ STEP).
  Qed.

  (* dealloc *)
  Lemma hist_ctx_dealloc_vs M M' 𝓢 𝓢' 𝓝 𝓝' 𝓥 𝓥' l n Vc 𝑚s
    (STEP: machine_step 𝓥 M 𝓢 (event.Dealloc l n) None 𝑚s 𝓥' M' 𝓢')
    (DRFPost: drf_post 𝓝 (event.Dealloc l n) None 𝑚s 𝓝')
    (LE: 𝓝 ⊑ Vc):
    (gen_heap_interp (to_hist (mem_cut M Vc))
    ∗ ([∗ list] i ∈ seq 0 (Pos.to_nat n), ∃ C, hist (l >> i) 1 C))
    ∗ own hist_atread_name (● to_atr 𝓝)
    ∗ ([∗ list] i ∈ seq 0 (Pos.to_nat n), ∃ rs, atread (l >> i) 1 rs)
    ∗ own hist_atwrite_name (● to_atw 𝓝)
    ∗ ([∗ list] i ∈ seq 0 (Pos.to_nat n), ∃ rs, atwrite (l >> i) 1 rs)
    ∗ own hist_naread_name (● to_nar 𝓝)
    ∗ ([∗ list] i ∈ seq 0 (Pos.to_nat n), ∃ rs, naread (l >> i) 1 rs)
    ==∗ ∃ Vc', ⌜𝓝' ⊑ Vc'⌝
        ∗ (gen_heap_interp (to_hist (mem_cut M' Vc'))
        ∗ ([∗ list] i ∈ seq 0 (Pos.to_nat n), mapsto (l >> i) DfracDiscarded None))
        ∗ (own hist_atread_name (● to_atr 𝓝')
          ∗ ([∗ list] i ∈ seq 0 (Pos.to_nat n), atread (l >> i) 1 ∅))
        ∗ (own hist_atwrite_name (● to_atw 𝓝')
          ∗ ([∗ list] i ∈ seq 0 (Pos.to_nat n), atwrite (l >> i) 1 ∅))
        ∗ (own hist_naread_name (● to_nar 𝓝')
          ∗ ([∗ list] i ∈ seq 0 (Pos.to_nat n), naread (l >> i) 1 ∅)).
  Proof.
    inversion_clear STEP. subst. simpl in *.
    have DISJ := dealloc_step_disjoint  _ _ _ _ _ _ _ DEALLOC.
    inversion_clear DEALLOC. inversion_clear MEMALL. inversion_clear DRFPost.
    rewrite -LEN. clear DEALLOC LEN VALL n.
    revert l M' Vc DMES ADD LE.
    induction 𝑚s as [|𝑚 𝑚s IH] => l M3 Vc DMES ADD LE.
    { inversion ADD; subst; simpl in *.
      iIntros "(own & oar & _ & oaw & _ & ona &_)".
      iExists Vc. iSplitL ""; [done|]. by iFrame. }
    iIntros "((own1 & ownl) & oar & oarl & oaw & oawl & ona & onal)".
    have Eqseq : seq 0 (length (𝑚 :: 𝑚s)) = 0%nat :: seq (S 0) (length 𝑚s) by done.
    iAssert ((∃ C, hist (l >> 0) 1 C) ∗
      [∗ list] i ∈ seq 0 (length 𝑚s), ∃ C, hist ((l >> 1) >> i) 1 C)%I
      with "[ownl]" as "[hist ownl]".
    { rewrite Eqseq -fmap_S_seq big_sepL_cons. iDestruct "ownl" as "[$ ownl]".
      rewrite big_sepL_fmap big_sepL_mono; [done|] => ? n ? /=.
      iDestruct 1 as (?) "?". iExists _. by rewrite shift_nat_assoc. }
    iAssert ((∃ rs, atread (l >> 0) 1 rs) ∗
      [∗ list] i ∈ seq 0 (length 𝑚s), ∃ rs, atread ((l >> 1) >> i) 1 rs)%I
      with "[oarl]" as "[atr oarl]".
    { rewrite Eqseq -fmap_S_seq big_sepL_cons. iDestruct "oarl" as "[$ oarl]".
      rewrite big_sepL_fmap big_sepL_mono; [done|] => ? n ? /=.
      iDestruct 1 as (?) "?". iExists _. by rewrite shift_nat_assoc. }
    iAssert ((∃ rs, atwrite (l >> 0) 1 rs) ∗
      [∗ list] i ∈ seq 0 (length 𝑚s), ∃ rs, atwrite ((l >> 1) >> i) 1 rs)%I
      with "[oawl]" as "[atw oawl]".
    { rewrite Eqseq -fmap_S_seq big_sepL_cons. iDestruct "oawl" as "[$ oawl]".
      rewrite big_sepL_fmap big_sepL_mono; [done|] => ? n ? /=.
      iDestruct 1 as (?) "?". iExists _. by rewrite shift_nat_assoc. }
    iAssert ((∃ rs, naread (l >> 0) 1 rs) ∗
      [∗ list] i ∈ seq 0 (length 𝑚s), ∃ rs, naread ((l >> 1) >> i) 1 rs)%I
      with "[onal]" as "[nar onal]".
    { rewrite Eqseq -fmap_S_seq big_sepL_cons. iDestruct "onal" as "[$ onal]".
      rewrite big_sepL_fmap big_sepL_mono; [done|] => ? n ? /=.
      iDestruct 1 as (?) "?". iExists _. by rewrite shift_nat_assoc. }
    inversion_clear ADD.
    specialize (IH (mem_list_disj_cons _ _ DISJ) (l >> 1)).
    iMod (IH with "[$own1 $ownl $oar $oarl $oaw $oawl $ona $onal]")
      as (Vc' LE') "((own1&ownl) & (oar&oarl) & (oaw&oawl) & ona & onal)";
      [|exact NEXT|done|].
    { move => ???. rewrite shift_nat_assoc. by apply DMES. }
    clear IH. rewrite Eqseq -fmap_S_seq. setoid_rewrite big_sepL_cons.
    iAssert ([∗ list] i ∈ (S <$> seq 0 (length 𝑚s)), mapsto (l >> i) _ None)%I
      with "[ownl]" as "$".
    { rewrite big_sepL_fmap big_sepL_mono; [done|] => ???.
      by rewrite shift_nat_assoc. }
    iAssert ([∗ list] i ∈ (S <$> seq 0 (length 𝑚s)), atread (l >> i) 1 ∅)%I
      with "[oarl]" as "$".
    { rewrite big_sepL_fmap big_sepL_mono; [done|] => ???.
      by rewrite shift_nat_assoc. }
    iAssert ([∗ list] i ∈ (S <$> seq 0 (length 𝑚s)), atwrite (l >> i) 1 ∅)%I
      with "[oawl]" as "$".
    { rewrite big_sepL_fmap big_sepL_mono; [done|] => ???.
      by rewrite shift_nat_assoc. }
    iAssert ([∗ list] i ∈ (S <$> seq 0 (length 𝑚s)), naread (l >> i) 1 ∅)%I
      with "[onal]" as "$".
    { rewrite big_sepL_fmap big_sepL_mono; [done|] => ???.
      by rewrite shift_nat_assoc. }
    rewrite shift_0.
    iDestruct "hist" as (C) "hist".
    iDestruct "atr" as (rsa) "atr". iDestruct "atw" as (ws) "atw".
    iDestruct "nar" as (rsn) "nar".
    iExists (<[𝑚.(mloc):= [{ 𝑚.(mto),∅,∅,∅ }] ]> Vc'). iSplitL "".
    { iPureIntro. by rewrite /= LE'. }
    destruct (DMES 0%nat 𝑚) as (EqLoc&EqVal&EqV&MAX &_); [done|].
    iSplitL "hist own1"; last iSplitL "atr oar"; last iSplitL "atw oaw".
    - rewrite (mem_cut_addins_na _ _ _ _ _ _ _ ADD0).
      have MAX2: ∀ t', is_Some ((M2 !!c 𝑚.(mloc)) !! t') → Pos.lt t' 𝑚.(mto).
      { rewrite -(mem_list_addins_old _ _ _ _ NEXT);
          last by apply mem_list_disj_cons_rest.
        move => ? [m' ?]. apply (MAX _ m'). by rewrite memory_lookup_cell. }
      have EMP: cell_cut (mto 𝑚) (M2 !!c mloc 𝑚) = ∅ by rewrite cell_cut_empty.
      rewrite hist_eq.
      rewrite to_hist_insert_dealloc;
        last by (rewrite EMP; apply cell_deallocated_singleton).
      rewrite EqLoc shift_0.
      iMod (gen_heap_update with "own1 hist") as "[$ hist]".
      iApply (mapsto_persist with "hist").
    - iDestruct (hist_ctx_atread_full with "[$oar $atr]") as %Eqrs.
      rewrite atread_eq -own_op. iApply (own_update_2 with "oar atr").
      apply auth_update. rewrite /= to_atr_insert EqLoc shift_0.
      eapply (singleton_local_update), exclusive_local_update; [|done].
      by apply to_atr_lookup_r_Some.
    - iDestruct (hist_ctx_atwrite_agree_1 with "[$oaw $atw]") as %Eqrs.
      rewrite atwrite_eq -own_op. iApply (own_update_2 with "oaw atw").
      apply auth_update. rewrite /= to_atw_insert EqLoc shift_0.
      eapply singleton_local_update; [done|by apply exclusive_local_update].
    - iDestruct (hist_ctx_naread_full with "[$ona $nar]") as %Eqrs.
      rewrite naread_eq -own_op. iApply (own_update_2 with "ona nar").
      apply auth_update. rewrite /= to_nar_insert EqLoc shift_0.
      eapply singleton_local_update, exclusive_local_update; [|done].
      by apply to_nar_lookup_r_Some.
  Qed.

  Lemma hist_ctx_dealloc σ σ' 𝓥 𝓥' l n 𝑚s
    (STEP: machine_step 𝓥 σ.(mem) σ.(sc) (event.Dealloc l (Z.to_pos n)) None 𝑚s 𝓥' σ'.(mem) σ'.(sc))
    (DRFPre: drf_pre σ.(na) 𝓥 σ.(mem) (event.Dealloc l (Z.to_pos n)))
    (DRFPost: drf_post σ.(na) (event.Dealloc l (Z.to_pos n)) None 𝑚s σ'.(na))
    (CLOSED: 𝓥 ∈ σ.(mem)) (AINV: alloc_inv σ.(mem)) (Lt: 0 < n):
    hist_ctx σ ∗
    ([∗ list] i ∈ seq 0 (Z.to_nat n),
      ∃ C ws rsa rsn, hist (l >> i) 1 C ∗
        atread (l >> i) 1 rsa ∗
        atwrite (l >> i) 1 ws ∗
        naread (l >> i) 1 rsn)
    ==∗ hist_ctx σ' ∗ seen 𝓥' ∗ ⌜𝓥 ⊑ 𝓥'⌝.
  Proof.
    iIntros "[ctx hists]".
    iDestruct "ctx" as (hF V Vc) "(Hhσ & HhF & Hna & Haw & Har & Hsc & HV & HF)".
    iDestruct "HF" as %(WF & HhF & HC & LE).
    rewrite (_: Z.to_nat n = Pos.to_nat (Z.to_pos n));
      last by rewrite -Z2Nat.inj_pos Z2Pos.id.
    iMod (hist_ctx_dealloc_vs _ _ _ _ _ _ _ _ _ _ _ _ STEP DRFPost LE
      with "[$Hhσ hists $Har $Haw $Hna]") as (Vc' LE')
        "([Hhσ' Hh] & (Har' & Har) & (Haw' & Haw) & Hna' & Hn)".
    { rewrite -3!big_sepL_sep. iApply (big_sepL_mono with "hists").
      iIntros (???). simpl. iDestruct 1 as (????) "(H1&H2&H3&H4)".
      iSplitL "H1"; last iSplitL "H2"; last iSplitL "H3"; by iExists _. }
    iMod (own_lat_auth_update_join _ _ 𝓥'.(acq) with "HV") as "[HV' HV]".
    iModIntro. iSplitL "HV' Hna' Har' Haw' Hhσ' HhF Hsc".
    - iExists _, _, Vc'. iFrame. iSplitL "Hsc"; [by inversion STEP|iPureIntro].
      split; last split; last split; [..|done].
      + by apply (machine_step_global_wf _ _ _ _ _ _ _ STEP).
      + inversion_clear STEP. eapply hist_freeable_rel_dealloc; eauto.
      + by eapply machine_step_view_join_update.
    - iDestruct (seen_own_join with "HV") as "$".
      iPureIntro. by apply (machine_step_tview_sqsubseteq _ _ _ _ _ _ _ _ _ STEP).
  Qed.

  Lemma hist_ctx_hists_free σ l n V:
    hist_ctx σ -∗
    ([∗ list] i ∈ seq 0 n,
        ∃ t m ws rsa rsn,
          hist (l >> i) 1 {[t := m]} ∗
          atread (l >> i) 1 rsa ∗
          atwrite (l >> i) 1 ws ∗
          naread (l >> i) 1 rsn ∗
          ⌜alloc_local (l >> i) {[t := m]} V ∧
            atr_local  (l >> i) rsa V ∧
            atw_local  (l >> i) ws V ∧
            na_local (l >> i) rsn V⌝)
    -∗ ⌜∀ (n' : nat), (n' < n)%nat
        →  σ.(na) !! (l >> n') ⊑ V !! (l >> n')
          ∧ ¬ cell_deallocated (σ.(mem) !!c (l >> n'))
          ∧ σ.(mem) !!c (l >> n') ≠ ∅
          ∧ ∀ 𝑚', 𝑚' ∈ σ.(mem) → 𝑚'.(mloc) = l >> n' → Some 𝑚'.(mto) ⊑ V !!w (l >> n')⌝.
  Proof.
    iIntros "ctx hists".
    iAssert (∀ n', ⌜(n' < n)%nat⌝
              -∗ ∃ t m ws rsa rsn,
                hist (l >> n') 1 {[t := m]} ∗
                atread (l >> n') 1 rsa ∗
                atwrite (l >> n') 1 ws ∗
                naread (l >> n') 1 rsn ∗
                ⌜alloc_local (l >> n') {[t := m]} V ∧
                atr_local (l >> n') rsa V ∧
                atw_local (l >> n') ws V ∧
                na_local (l >> n') rsn V⌝)%I
      with "[hists]" as "hists".
    { iIntros (n' Le). iApply (big_sepL_elem_of with "hists").
      apply elem_of_list_lookup. exists n'. by rewrite lookup_seq. }
    iIntros (n' Le).
    iDestruct ("hists" $! n' with "[]")
      as (t m ws rsa rsn) "(hist & ar & aw & na & %&%&%&%)"; [done|].
    iDestruct (hist_ctx_alloc_local_drf with "ctx hist") as %DRF; [done|].
    iDestruct (hist_ctx_atread_local_drf with "ctx ar") as %DRFAR; [done|].
    iDestruct (hist_ctx_atwrite_local_drf with "ctx aw") as %DRFAW; [done|].
    iDestruct (hist_ctx_na_local_drf with "ctx na") as %DRFNR; [done|].
    iDestruct (hist_ctx_hist_cut with "ctx hist") as %(?&?&?&?&Eq&?&?&?&?).
    iPureIntro. split; last split; last split; [|done..|].
    - apply view_sqsubseteq. split; [|done].
      etrans; [apply DRF|]. by apply view_sqsubseteq.
    - eapply alloc_local_cut_singleton; eauto. by rewrite -Eq.
  Qed.

  (* read *)
  Lemma hist_ctx_read_msg σ l C q  :
    hist_ctx σ -∗ hist l q C -∗
    □ ∀ 𝓥 𝓥' 𝑚 o tr,
      ⌜𝑚.(mloc) = l ∧
        read_step 𝓥 σ.(mem) tr 𝑚 o 𝓥' ∧
        alloc_local 𝑚.(mloc) C 𝓥.(cur) ∧
        𝓥 ∈ σ.(mem)⌝ -∗
      ⌜𝓥 ⊑ 𝓥' ∧ good_hist C ∧
        C !! 𝑚.(mto) = Some 𝑚.(mbase) ∧
        read_helper 𝓥 o 𝑚.(mloc) 𝑚.(mto) tr
                    (default ∅ 𝑚.(mbase).(mrel)) 𝓥' ∧
                    𝑚.(mbase).(mval) ≠ DVal⌝ ∗
      (hist_ctx σ ==∗ hist_ctx σ ∗ seen 𝓥').
  Proof.
    iIntros "ctx hist".
    iDestruct (hist_ctx_hist_cut with "ctx hist") as %[Vc1 [LE1 [t [Eqtc [EqC ?]]]]].
    iDestruct (hist_ctx_hist_good with "ctx hist") as %WFC.
    iDestruct "ctx" as (hF V Vc) "(Hhσ & HhF & Hna & Haw & Har & Hsc & HV & HF)".
    iDestruct "HF" as %(WF & HhF & HC & LE).
    iIntros "!>" (𝓥 𝓥' 𝑚 o tr (Eql & STEP & ALL & CLOSED)). subst l.
    have EXT: 𝓥 ⊑ 𝓥' by eapply read_step_tview_sqsubseteq.
    iSplitL "".
    - iPureIntro. split; [done|]. inversion_clear STEP.
      have Eq𝑚 : C !! 𝑚.(mto) = Some 𝑚.(mbase).
      { rewrite EqC cell_cut_lookup_Some -memory_lookup_cell. split; [done|].
        change (Some t ⊑ Some 𝑚.(mto)). etrans; last (inversion READ; apply PLN).
        destruct ALL as (t'&m'&Eqt'&Eqv'&SL'). etrans; last apply SL'.
        apply (cell_cut_lookup_Some (σ.(mem) !!c 𝑚.(mloc)) _ _ m').
        by rewrite -EqC. }
      do 3 (split; [done|]). by eapply ALLOC.
    - iDestruct 1 as (???) "(Hhσ & HhF & Hna & Haw & Har & Hsc & HV & HF)".
      iMod (own_lat_auth_update_join _ _ 𝓥'.(acq) with "HV")
        as "[HV' HV]".
      iModIntro. iDestruct (seen_own_join with "HV") as "$".
      iExists _, _, _. iFrame "Hhσ HhF Hna Haw Har Hsc HV'".
      iDestruct "HF" as %(WF' & HhF' & HC' & LE').
      iPureIntro. split; [by destruct σ|split; [done|split; [|done]]].
      apply join_closed_view; first done.
      apply (read_step_closed_tview _ _ _ _ _ _ STEP); [done|apply WF].
  Qed.

  Lemma hist_ctx_naread_update_1 𝓝 l q rs tr:
    own hist_naread_name (● to_nar 𝓝) -∗ naread l q rs
    ==∗ own hist_naread_name (● to_nar (add_nread_id 𝓝 l tr)) ∗ naread l q (rs ∪ {[tr]}).
  Proof.
    iIntros "oA or".
    iDestruct (hist_ctx_naread_included with "[$oA $or]") as %SUB.
    destruct (𝓝 !! l) as [[?? rsm]|] eqn:Eql; last first.
    { by rewrite (view_lookup_nr' _ _ _ Eql) in SUB. }
    rewrite naread_eq -own_op. iApply (own_update_2 with "oA or").
    apply auth_update.
    rewrite (to_nar_add_nread_id _ _ _ rsm); last by eapply view_lookup_nr.
    eapply singleton_local_update; first by eapply to_nar_lookup_Some.
    by apply (frac_lat_local_update _ _ rsm rs {[tr]}).
  Qed.

  Lemma hist_ctx_naread_update σ l q rs tr:
    hist_ctx σ -∗ naread l q rs
    ==∗ hist_ctx (mkGB σ.(sc) (add_nread_id σ.(na) l tr) σ.(mem)) ∗
        naread l q (rs ∪ {[tr]}).
  Proof.
    iDestruct 1 as (?? Vc) "(H1 & H2 & Hna & H4 & H5 & H6 & H7 & WF)".
    iDestruct "WF" as %(WF & Hrel & In & LE).
    iIntros "nar". iMod (hist_ctx_naread_update_1 with "Hna nar") as "[Hna' $]".
    iExists _,_, (add_nread_id Vc l tr).
    rewrite /= mem_cut_add_nread_id to_atr_add_nread_id to_atw_add_nread_id.
    iFrame. iPureIntro.
    split; last split; last split; [|done|done|by apply add_nread_id_mono].
    constructor; simpl;
      [apply WF..|apply add_nread_id_dealloc_agree, WF|apply WF
      |apply add_nread_id_memory, WF].
  Qed.

  Lemma hist_ctx_atread_update_1 𝓝 l q rs tr:
    own hist_atread_name (● to_atr 𝓝) -∗ atread l q rs
    ==∗ own hist_atread_name (● to_atr (add_aread_id 𝓝 l tr)) ∗
        atread l q (rs ∪ {[tr]}).
  Proof.
    iIntros "oA or".
    iDestruct (hist_ctx_atread_included with "[$oA $or]") as %SUB.
    destruct (𝓝 !! l) as [[??? rsm]|] eqn:Eql; last first.
    { by rewrite (view_lookup_ar' _ _ _ Eql) in SUB. }
    rewrite atread_eq -own_op.
    iApply (own_update_2 with "oA or"). apply auth_update.
    rewrite (to_atr_add_aread_id _ _ _ rsm); last by eapply view_lookup_ar.
    eapply singleton_local_update; first by eapply to_atr_lookup_Some.
    by apply (frac_lat_local_update _ _ rsm rs {[tr]}).
  Qed.

  Lemma hist_ctx_atread_update σ l q rs tr:
    hist_ctx σ -∗ atread l q rs
    ==∗ hist_ctx (mkGB σ.(sc) (add_aread_id σ.(na) l tr) σ.(mem)) ∗
        atread l q (rs ∪ {[tr]}).
  Proof.
    iDestruct 1 as (?? Vc) "(H1 & H2 & H3 & H4 & Har & H5 & H6 & WF)".
    iDestruct "WF" as %(WF & Hrel & In & LE).
    iIntros "atr". iMod (hist_ctx_atread_update_1 with "Har atr") as "[Hat' $]".
    iExists _,_, (add_aread_id Vc l tr).
    rewrite mem_cut_add_aread_id to_nar_add_aread_id to_atw_add_aread_id.
    iFrame. iPureIntro.
    split; last split; last split; [|done|done|by apply add_aread_id_mono].
    constructor; simpl;
      [apply WF..|apply add_aread_id_dealloc_agree, WF|apply WF|
       apply add_aread_id_memory, WF].
  Qed.

  Lemma hist_ctx_read σ l C q :
    hist_ctx σ -∗ hist l q C -∗
    □ ∀ σ' 𝓥 𝓥' v o q' tr rs,
      ⌜machine_step 𝓥 σ.(mem) σ.(sc) (event.Read l v o) (Some tr) [] 𝓥' σ'.(mem) σ'.(sc) ∧
        drf_post σ.(na) (event.Read l v o) (Some tr) [] σ'.(na) ∧
        alloc_local l C 𝓥.(cur) ∧ 𝓥 ∈ σ.(mem)⌝ -∗
        (if decide (Relaxed ⊑ o) then atread l q' rs else naread l q' rs) -∗
      ⌜𝓥 ⊑ 𝓥' ∧ good_hist C ∧
        ∃ t m, C !! t = Some m ∧ m.(mval) = v ∧
        read_helper 𝓥 o l t tr (default ∅ m.(mrel)) 𝓥' ∧
        m.(mval) ≠ DVal⌝ ∗
       (hist_ctx σ ==∗ hist_ctx σ' ∗ seen 𝓥' ∗
                        (if decide (Relaxed ⊑ o)
                         then atread l q' (rs ∪ {[tr]})
                         else naread l q' (rs ∪ {[tr]}))).
  Proof.
    iIntros "ctx hist".
    iDestruct (hist_ctx_read_msg with "ctx hist") as "#VS".
    iIntros "!>" (σ' 𝓥 𝓥' v o q' tr rs (STEP & DRF & ALL & CLOSED)).
    inversion STEP. subst; clear STEP. simpl in *.
    iDestruct ("VS" $! 𝓥 𝓥' 𝑚 o tr with "[//]") as "{VS} [Ext VS]".
    iDestruct "Ext" as %[? [? [? [? ?]]]]. iIntros "or".
    iSplitR "VS or".
    - iPureIntro. do 2 (split; [done|]). by exists 𝑚.(mto), 𝑚.(mbase).
    - iIntros "Hσ". iMod ("VS" with "Hσ") as "[Hσ $]".
      inversion_clear DRF. inversion_clear DRF0.
      case_decide; destruct POST as [POST1 POST2]; destruct σ'; simpl in *; subst.
      + iApply (hist_ctx_atread_update with "Hσ or").
      + iApply (hist_ctx_naread_update with "Hσ or").
  Qed.

  (* write *)
  Lemma hist_ctx_write_vs (M1: memory) Vc l (C: cell) :
    let C' o 𝑚 : cell
        := <[𝑚.(mto) := 𝑚.(mbase)]> (if decide (Relaxed ⊑ o) then C else ∅) in
    let Vc' o 𝑚 : view
      := (if decide (Relaxed ⊑ o)
          then add_awrite_id Vc l 𝑚.(mto) else set_write_time Vc l 𝑚.(mto)) in
    gen_heap_interp (to_hist (mem_cut M1 Vc)) -∗ hist l 1 C -∗
    □ ∀ o 𝑚 (Vr: view) (M2: memory) 𝓥1 𝓥2 𝓝1 𝓝2,
      ⌜𝑚.(mloc) = l ∧
        write_step 𝓥1 M1 𝑚 o Vr 𝓥2 M2 ∧
        drf_pre_write 𝑚.(mloc) 𝓝1 𝓥1 M1 o ∧
        drf_post_write 𝑚.(mloc) 𝑚.(mto) o 𝓝1 𝓝2 ∧
        alloc_local l C 𝓥1.(cur) ∧ 𝓝1 ⊑ Vc ∧
        isval 𝑚.(mbase).(mval)⌝ -∗
      ⌜mem_cut M2 (Vc' o 𝑚) = <[l:= C' o 𝑚]> (mem_cut M1 Vc)
        ∧ (if (decide (Relaxed ⊑ o))
           then cell_addins 𝑚.(mto) 𝑚.(mbase) C (C' o 𝑚) else True)
        ∧ 𝓝2 ⊑ (Vc' o 𝑚) ∧ Wf 𝑚⌝ ∗
      (gen_heap_interp (to_hist (mem_cut M1 Vc)) -∗ hist l 1 C ==∗
        gen_heap_interp (to_hist (<[l:= C' o 𝑚]>(mem_cut M1 Vc))) ∗
        hist l 1 (C' o 𝑚)).
  Proof.
    iIntros (C' Vc') "own hist".
    iDestruct (hist_own_hist_cut with "own hist") as %[t [Eqt [EqC [? [? [? ?]]]]]].
    iDestruct (hist_own_to_hist_lookup with "own hist") as %EqC'.
    iDestruct (hist_own_lookup with "own hist") as %EqCL.
    iIntros "!>" (o 𝑚 Vr M2 L1 L2 𝓝1 𝓝2
                  (EQLOC & WRITE & DRFR & DRFP & ALL & LE & ISVAL)).
    iSplitL "".
    { iPureIntro. inversion_clear WRITE. inversion_clear WRITE0.
      subst.
      destruct (mem_cut_write 𝑚.(mloc) _ _ _ _ _ _ Vc _ t (M1 !!c 𝑚.(mloc))
                          MEM DRFR DRFP LE) as [C0[Eq2 [LE' Eq3]]];
        [done| |done|by inversion WVIEW|split; last split];
        [..|split; last done]; last done.
      - change (Some t ⊏ Some (mto 𝑚)). inversion_clear WVIEW.
        eapply strict_transitive_r; [|apply RLX].
        etrans; [|by apply view_sqsubseteq].
        destruct ALL as (t'&m'&?&?&SL). etrans; [|apply SL].
        by apply (cell_cut_lookup_Some (M1 !!c mloc 𝑚) _ _ m').
      - rewrite Eq2 /Vc' /C'.
        have ?: is_Some (Vc !! 𝑚.(mloc)).
        { destruct (view_lookup_of_wp _ _ _ Eqt) as [?[??]]. by eexists. }
        case_decide.
        + rewrite Eq3 mem_cut_add_awrite_id mem_cut_insert_set_write; [|done].
          by rewrite (set_write_time_id _ _ _ Eqt).
        + by rewrite Eq3 -mem_cut_insert_set_write.
      - rewrite /C'. case_decide; [|done]. apply cell_addins_cell_cut.
        inversion MEM. by inversion ADD. }
    iIntros "own hist".
    rewrite hist_eq.
    iMod (gen_heap_update with "own hist") as "[own $]".
    rewrite to_hist_insert_alloc; [done| |by apply insert_non_empty].
    rewrite /C'. inversion ISVAL as [? EqV].
    case_match; [apply cell_deallocated_neg_insert; [done|by rewrite -EqV]
                |apply cell_deallocated_neg_singleton; by rewrite -EqV].
  Qed.

  Lemma hist_ctx_atwrite_update_1 𝓝 l rs tr:
    own hist_atwrite_name (● to_atw 𝓝) -∗ atwrite l 1 rs
    ==∗ own hist_atwrite_name (● to_atw (add_awrite_id 𝓝 l tr)) ∗
        atwrite l 1 (rs ∪ {[tr]}).
  Proof.
    iIntros "oA ow".
    iDestruct (hist_ctx_atwrite_agree with "[$oA $ow]") as %SUB.
    destruct (𝓝 !! l) as [[? rsm]|] eqn:Eql; last first.
    { by rewrite (view_lookup_aw' _ _ _ Eql) in SUB. }
    rewrite atwrite_eq -own_op.
    iApply (own_update_2 with "oA ow"). apply auth_update.
    rewrite (to_atw_add_awrite_id _ _ _ rs); last done.
    eapply singleton_local_update; first by eapply to_atw_lookup_Some.
    by apply exclusive_local_update.
  Qed.

  Lemma hist_ctx_atwrite_update σ l ws tw:
    hist_ctx σ -∗ atwrite l 1 ws
    ==∗ hist_ctx (mkGB σ.(sc) (add_awrite_id σ.(na) l tw) σ.(mem)) ∗
        atwrite l 1 (ws ∪ {[tw]}).
  Proof.
    iDestruct 1 as (?? Vc) "(H1 & H2 & H3 & Haw & H4 & H5 & H6 & WF)".
    iDestruct "WF" as %(WF & Hrel & In & LE).
    iIntros "atw".
    iMod (hist_ctx_atwrite_update_1 with "Haw atw") as "[Hat' $]".
    iExists _,_, (add_awrite_id Vc l tw).
    rewrite mem_cut_add_awrite_id to_nar_add_awrite_id to_atr_add_awrite_id.
    iFrame. iPureIntro.
    split; last split; last split; [|done|done|by apply add_awrite_id_mono].
    constructor; simpl;
      [apply WF..|apply add_awrite_id_dealloc_agree, WF|apply WF|
       apply add_awrite_id_memory, WF].
  Qed.

  Lemma hist_ctx_write_msg σ l C :
    hist_ctx σ -∗ hist l 1 C -∗
    □ ∀ 𝑚 v o σ' (Vr: view) 𝓥 𝓥' ws,
      ⌜𝑚.(mloc) = l ∧
        write_step 𝓥 σ.(mem) 𝑚 o Vr 𝓥' σ'.(mem) ∧
        drf_pre_write 𝑚.(mloc) σ.(na) 𝓥 σ.(mem) o ∧
        drf_post_write 𝑚.(mloc) 𝑚.(mto) o σ.(na) σ'.(na) ∧
        alloc_local 𝑚.(mloc) C 𝓥.(cur) ∧ 𝓥 ∈ σ.(mem) ∧ 𝑚.(mbase).(mval) = VVal v ∧
        σ'.(sc) = σ.(sc)⌝ -∗
        atwrite l 1 ws -∗
      ∃ C',
      ⌜𝓥 ⊑ 𝓥'
        ∧ C' = <[𝑚.(mto):= 𝑚.(mbase)]> (if (decide (Relaxed ⊑ o)) then C else ∅)
        ∧ (if (decide (Relaxed ⊑ o)) then cell_addins 𝑚.(mto) 𝑚.(mbase) C C' else True)
        ∧ C !! 𝑚.(mto) = None
        ∧ write_helper 𝓥 o 𝑚.(mloc) 𝑚.(mto) Vr 𝑚.(mbase).(mrel) 𝓥'⌝ ∗
      (hist_ctx σ -∗ hist l 1 C ==∗
        hist_ctx σ' ∗ hist 𝑚.(mloc) 1 C' ∗
        (if decide (Relaxed ⊑ o) then atwrite l 1 (ws ∪ {[𝑚.(mto)]})
         else atwrite l 1 ws) ∗
        seen 𝓥').
  Proof.
    iIntros "ctx hist".
    iDestruct (hist_ctx_hist_cut with "ctx hist") as %[? [? [t [? [EqC HL]]]]].
    iDestruct "ctx" as (hF V Vc) "(Hhσ & HhF & Hna & Haw & Har & Hsc & HV & #HF)".
    iDestruct (hist_ctx_write_vs σ.(mem) Vc l C with "Hhσ hist") as "#VS".
    iIntros "!>" (𝑚 v o σ' Vr 𝓥 𝓥' ws
                  (EQLOC & WRITE & DRFR & DRFP & ALL & CLOSED & EQv & EQSC)).
    iIntros "ATW".
    subst l. iExists _. iSplitL "VS".
    - iDestruct "HF" as %(WF & HhF & HC & LE).
      iDestruct ("VS" $! o 𝑚 with "[%]") as "[FACT VS1]".
      { rewrite EQv. do 5 (split; [done|]). done. }
      iDestruct "FACT" as %(Eq & ? & LE2 & WF𝑚).
      have EXT : 𝓥 ⊑ 𝓥' by eapply write_step_tview_sqsubseteq.
      iPureIntro. do 3 (split; [done|]). split; [|by inversion WRITE].
      rewrite EqC cell_cut_lookup_None -memory_lookup_cell. left.
      by apply (write_step_addins_fresh _ _ _ _ _ _ _ WRITE), WF.
    - iIntros "{HF VS} ctx hist".
      iDestruct "ctx" as (hF' V' Vc') "(Hhσ & HhF & Hna & Haw & Hat & Hsc & HV & HF)".
      iDestruct "HF" as %(WF & HhF & HC & LE).
      iDestruct (hist_ctx_write_vs σ.(mem) Vc' 𝑚.(mloc) C with "Hhσ hist") as "#VS".
      iDestruct ("VS" $! o 𝑚 with "[%]") as "{VS} [FACT VS]".
      { rewrite EQv. do 5 (split; [done|]). done. }
      iDestruct "FACT" as %(Eq & ? & LE' & WF𝑚).
      iMod ("VS" with "Hhσ hist") as "{VS} [Hσ' $]".
      iMod (own_lat_auth_update_join _ _ 𝓥'.(acq) with "HV") as "[HV' HV]".
      iDestruct (seen_own_join with "HV") as "$".
      iAssert (|==> own hist_atwrite_name (● to_atw σ'.(na)) ∗
                    if decide (Relaxed ⊑ o)
                    then atwrite 𝑚.(mloc) 1 (ws ∪ {[𝑚.(mto)]})
                    else atwrite 𝑚.(mloc) 1 ws)%I
        with "[Haw ATW]" as ">(Haw & $)".
      { clear -DRFP. inversion DRFP. subst. case_decide; rewrite POST.
        - by iMod (hist_ctx_atwrite_update_1 with "Haw ATW") as "[$ $]".
        - rewrite to_atw_set_write_time. by iFrame. }
      iExists _, _, _. rewrite EQSC -Eq.
      rewrite (_: to_atr σ'.(na) = to_atr σ.(na)); last first.
      { clear -DRFP. inversion DRFP. subst. case_decide; rewrite POST.
        - by rewrite to_atr_add_awrite_id. - by rewrite to_atr_set_write_time. }
      rewrite (_: to_nar σ'.(na) = to_nar σ.(na)); last first.
      { clear -DRFP. inversion DRFP. subst. case_decide; rewrite POST.
        - by rewrite to_nar_add_awrite_id. - by rewrite to_nar_set_write_time. }
      iFrame. iPureIntro. split; last split; last split; [..|done].
      + by eapply write_step_global_wf.
      + rewrite (write_step_addins_eq _ _ _ _ _ _ _ WRITE).
        apply hist_freeable_rel_stable; [by apply insert_non_empty|done|apply HL].
      + apply join_closed_view.
        * by eapply write_step_closed_view.
        * by eapply write_step_closed_tview.
  Qed.

  Lemma hist_ctx_write σ l C:
    hist_ctx σ -∗ hist l 1 C -∗
    □ ∀ σ' 𝓥 𝓥' 𝑚 v o ws,
      ⌜machine_step 𝓥 σ.(mem) σ.(sc) (event.Write l v o) None [𝑚] 𝓥' σ'.(mem) σ'.(sc) ∧
        drf_pre_write l σ.(na) 𝓥 σ.(mem) o ∧
        drf_post_write l 𝑚.(mto) o σ.(na) σ'.(na) ∧
        alloc_local l C 𝓥.(cur) ∧ 𝑚.(mloc) = l ∧ 𝓥 ∈ σ.(mem)⌝ -∗
        atwrite l 1 ws -∗
      ∃ C' t,
      ⌜𝓥 ⊑ 𝓥'
        ∧ ∃ m, C' = <[t:= m]> (if (decide (Relaxed ⊑ o)) then C else ∅)
        ∧ C !! t = None ∧ m.(mval) = VVal v
        ∧ (if (decide (Relaxed ⊑ o)) then cell_addins t m C C' else True)
        ∧ 𝓥.(cur) ≠ 𝓥'.(cur)
        ∧ write_helper 𝓥 o l t ∅ m.(mrel) 𝓥'⌝ ∗
      (hist_ctx σ -∗ hist l 1 C ==∗ hist_ctx σ' ∗ hist l 1 C' ∗
        (if decide (Relaxed ⊑ o) then atwrite l 1 (ws ∪ {[t]})
         else atwrite l 1 ws) ∗ seen 𝓥').
  Proof.
    iIntros "ctx hist".
    iDestruct (hist_ctx_write_msg with "ctx hist") as "#VS".
    iIntros "!>" (σ' 𝓥 𝓥' 𝑚 v o ws (STEP & DRFR & DRFP & ALL & EQL & CLOSED)) "AT".
    inversion STEP. subst; clear STEP. simpl in *.
    iDestruct ("VS" $! 𝑚 v o (mkGB σ'.(sc) σ'.(na) σ'.(mem)) with "[%] AT")
      as (C') "[Ext VS1]"; [done|].
    iDestruct "Ext" as %(?&?&?&?&WH). iExists _, _.
    iSplitR "VS1"; [|by destruct σ'].
    iPureIntro. split; [done|]. exists 𝑚.(mbase).
    do 4 (split; [done|]). split; [|done]. by apply (write_helper_strict WH).
  Qed.

  Lemma hist_ctx_cas_msg σ l C :
    hist_ctx σ -∗ hist l 1 C -∗
    □ ∀ σ' 𝓥1 𝓥2 𝓥3 𝓝2 𝑚1 𝑚2 or ow tr (vr : lit) (vw: val) q rs ws,
      ⌜𝑚1.(mloc) = l ∧ 𝑚2.(mloc) = l ∧
        alloc_local 𝑚1.(mloc) C 𝓥1.(cur) ∧ 𝓥1 ∈ σ.(mem) ∧
        𝑚1.(mbase).(mval) = VVal (LitV vr) ∧ 𝑚2.(mbase).(mval) = VVal vw ∧
        read_step 𝓥1 σ.(mem) tr 𝑚1 or 𝓥2 ∧
        (* drf_read 𝑚1 or tr σ.(na) 𝓥1 σ.(mem) 𝓝2 ∧ *)
        drf_post_read l or tr σ.(na) 𝓝2 ∧
        write_step 𝓥2 σ.(mem) 𝑚2 ow (default ∅ 𝑚1.(mbase).(mrel)) 𝓥3 σ'.(mem) ∧
        (* drf_write 𝑚2 ow 𝓝2 𝓥2 σ.(mem) σ'.(na) ∧ *)
        drf_pre_write 𝑚2.(mloc) 𝓝2 𝓥2 σ.(mem) ow ∧
        drf_post_write l 𝑚2.(mto) ow 𝓝2 σ'.(na) ∧
        Relaxed ⊑ or ∧ Relaxed ⊑ ow ∧ σ'.(sc) = σ.(sc) ∧ Wf σ'⌝ -∗
        atread l q rs -∗
        atwrite l 1 ws -∗
      ∃ C',
      ⌜𝓥1 ⊑ 𝓥2 ∧ 𝓥2 ⊑ 𝓥3 ∧ good_hist C ∧
        C !! 𝑚1.(mto) = Some 𝑚1.(mbase) ∧
        read_helper 𝓥1 or 𝑚1.(mloc) 𝑚1.(mto) tr
                    (default ∅ 𝑚1.(mbase).(mrel)) 𝓥2 ∧
        C !! 𝑚2.(mto) = None ∧
        C' = <[𝑚2.(mto):= 𝑚2.(mbase)]> C ∧
        cell_addins 𝑚2.(mto) 𝑚2.(mbase) C C' ∧
        write_helper 𝓥2 ow 𝑚2.(mloc) 𝑚2.(mto)
                     (default ∅ 𝑚1.(mbase).(mrel)) 𝑚2.(mbase).(mrel) 𝓥3 ⌝ ∗
      (hist_ctx σ -∗ hist l 1 C ==∗
        hist_ctx σ' ∗ hist l 1 C' ∗
        atread l q (rs ∪ {[tr]}) ∗ atwrite l 1 (ws ∪ {[𝑚2.(mto)]}) ∗ seen 𝓥3).
  Proof.
    iIntros "ctx hist".
    iDestruct (hist_ctx_read_msg with "ctx hist") as "#VSR".
    iDestruct (hist_ctx_hist_cut with "ctx hist") as %[? [? [t [? [EqC HL]]]]].
    iDestruct "ctx" as (hF V Vc) "(Hhσ & HhF & Hna & Haw & Hat & Hsc & HV & #HF)".
    iDestruct "HF" as %(WFσ & _ & InM' & LE).
    set C' : memOrder → message → cell :=
      λ o 𝑚, <[𝑚.(mto) := 𝑚.(mbase)]> (if decide (Relaxed ⊑ o) then C else ∅).
    set Vc' : time_id → memOrder → message → view :=
      λ tr o 𝑚,
       if decide (Relaxed ⊑ o) then add_awrite_id (add_aread_id Vc l tr) l 𝑚.(mto)
       else set_write_time (add_aread_id Vc l tr) l 𝑚.(mto).
    iAssert (∀ tr, □ ∀ o 𝑚 (Vr: view) (M2: memory) 𝓥1 𝓥2 𝓝1 𝓝2,
      ⌜𝑚.(mloc) = l ∧
        write_step 𝓥1 σ.(mem) 𝑚 o Vr 𝓥2 M2 ∧
        drf_pre_write 𝑚.(mloc) 𝓝1 𝓥1 σ.(mem) o ∧
        drf_post_write 𝑚.(mloc) 𝑚.(mto) o 𝓝1 𝓝2 ∧
        alloc_local l C 𝓥1.(cur) ∧ 𝓝1 ⊑ (add_aread_id Vc l tr) ∧
        isval 𝑚.(mbase).(mval)⌝ -∗
      ⌜mem_cut M2 (Vc' tr o 𝑚) = <[l:= C' o 𝑚]> (mem_cut σ.(mem) (add_aread_id Vc l tr))
        ∧ (if decide (Relaxed ⊑ o)
           then cell_addins 𝑚.(mto) 𝑚.(mbase) C (C' o 𝑚) else True)
        ∧ 𝓝2 ⊑ (Vc' tr o 𝑚) ∧ Wf 𝑚⌝ ∗
      (gen_heap_interp (to_hist (mem_cut σ.(mem) (add_aread_id Vc l tr))) -∗
        hist l 1 C ==∗
        gen_heap_interp(to_hist (<[l:= C' o 𝑚]> (mem_cut σ.(mem) (add_aread_id Vc l tr)))) ∗
        hist l 1 (C' o 𝑚)))%I with "[Hhσ hist]" as "#VS".
    { iIntros (tr).
      iApply (hist_ctx_write_vs σ.(mem) (add_aread_id Vc l tr) l C with "[Hhσ] hist").
      by rewrite mem_cut_add_aread_id. }
    iIntros "!>" (σ' 𝓥1 𝓥2 𝓥3 𝓝2 𝑚1 𝑚2 or ow tr vr vw).
    iIntros (qr rs ws) "FACT AR AW".
    iDestruct "FACT" as %(EqL1 & EqL2 & ALL & InM & Eqvr & Eqvw & RS & DRFR
                          & WS & DRFWR & DRFWP & RLXR & RLXW & EQSC & WF').
    iDestruct ("VSR" $! 𝓥1 𝓥2 𝑚1 or tr with "[%//]") as "[FACT _] {VSR}".
    have ALL2: alloc_local l C 𝓥2.(cur).
    { eapply alloc_local_mono; [done|..|by rewrite -EqL1].
      by eapply read_step_tview_sqsubseteq. }
    iDestruct ("VS" $! tr ow 𝑚2 _ _ 𝓥2 𝓥3 𝓝2 σ'.(na) with "[%]") as "[FACT2 _] {VS}".
    { do 3 (split; [done|]). split; [by rewrite EqL2|]; split; [done|].
      split; [|by rewrite Eqvw].
      clear -DRFR RLXR LE EqL1. inversion DRFR.
      rewrite (decide_True _ _ RLXR) in POST. destruct POST.
      subst. by apply add_aread_id_mono. }
    iDestruct "FACT" as %(Ext1 & GH & Eqt1 & RH & ?).
    iDestruct "FACT2" as %(EqCut & ADD & LE' & WF2).
    rewrite /C' 2!(decide_True _ _ RLXW) in ADD.
    rewrite /C' /Vc' 2!(decide_True _ _ RLXW) in EqCut.
    iExists (<[𝑚2.(mto):= 𝑚2.(mbase)]> C). iSplit.
    { iPureIntro. split; [done|]. split; [by eapply write_step_tview_sqsubseteq|].
      do 3 (split; [done|]). split. { by eapply lookup_cell_addins_fresh. }
      do 2 (split; [done|]). by inversion WS. }
    clear -EqL1 EqL2 ALL RS WS DRFR DRFWR DRFWP RLXR RLXW ALL2 Eqvw EQSC HL InM WF'.
    iIntros "ctx hist".
    iDestruct "ctx" as (hF' V' Vc') "(Hhσ & HhF & Hna & Haw & Har & Hsc & HV & HF)".
    iDestruct "HF" as %(WF & ? & InM' & LE).
    iDestruct (hist_ctx_write_vs σ.(mem) (add_aread_id Vc' l tr) l C
      with "[Hhσ] hist") as "#VS"; [by rewrite mem_cut_add_aread_id|].
    iDestruct ("VS" $! ow 𝑚2 _ _ 𝓥2 𝓥3 𝓝2 σ'.(na) with "[%]") as "{VS} [FACT2 VS]".
    { do 3 (split; [done|]). split; [by rewrite EqL2|]. split; [done|].
      split; [|by rewrite Eqvw].
      clear -DRFR RLXR LE EqL1. inversion DRFR.
      rewrite (decide_True _ _ RLXR) in POST. destruct POST.
      subst. by apply add_aread_id_mono. }
    iMod ("VS" with "[Hhσ] hist") as "[Hhσ' hist] {VS}".
    { by rewrite mem_cut_add_aread_id. }
    rewrite 3!(decide_True _ _ RLXW).
    iFrame "hist". iMod (hist_ctx_atread_update_1 with "Har AR") as "[Har' $]".
    iMod (hist_ctx_atwrite_update_1 with "Haw AW") as "[Haw' $]".
    iMod (own_lat_auth_update_join _ _ 𝓥3.(acq) with "HV") as "[HV' HV]".
    iDestruct (seen_own_join with "HV") as "$".
    iDestruct "FACT2" as %(EqCut & ADD & LE' & WFm).
    iModIntro. iExists _,_, (add_awrite_id (add_aread_id Vc' l tr) l 𝑚2.(mto)).
    rewrite -EqCut mem_cut_add_awrite_id EQSC.
    iFrame "Hhσ' HhF HV'".
    have Eqna' : σ'.(na) = add_awrite_id (add_aread_id σ.(na) l tr) l 𝑚2.(mto).
    { clear -DRFR DRFWR DRFWP RLXW RLXR EqL1 EqL2. inversion DRFWP.
      rewrite (decide_True _ _ RLXW) in POST. rewrite POST -EqL2. clear POST.
      f_equal. inversion DRFR. rewrite (decide_True _ _ RLXR) in POST.
      destruct POST as [POST _]. by rewrite POST EqL2. }
    rewrite Eqna' to_nar_add_awrite_id to_nar_add_aread_id to_atr_add_awrite_id.
    iFrame "Hna Har' Hsc". iSplitL "Haw'".
    { by rewrite add_aread_awrite_comm to_atw_add_aread_id. } rewrite -Eqna'.
    have ? : 𝓥2 ∈ σ.(mem) by eapply read_step_closed_tview; [eauto..|apply WF].
    iPureIntro. split; last split; last split; [done|..|done].
    - rewrite (write_step_addins_eq _ _ _ _ _ _ _ WS).
      apply hist_freeable_rel_stable; [by apply insert_non_empty|done|].
      rewrite EqL2. by apply HL.
    - apply join_closed_view.
      + by eapply write_step_closed_view.
      + by eapply write_step_closed_tview.
  Qed.

  Lemma hist_ctx_cas σ l C:
    hist_ctx σ -∗ hist l 1 C -∗
    □ ∀ σ' 𝓥 𝓥' vr vw or ow q tr 𝑚 rs ws,
      ⌜machine_step 𝓥 σ.(mem) σ.(sc) (Update l (LitV vr) vw or ow) (Some tr) [𝑚] 𝓥' σ'.(mem) σ'.(sc) ∧
        drf_pre σ.(na) 𝓥 σ.(mem) (Update l (LitV vr) vw or ow) ∧
        drf_post σ.(na) (Update l (LitV vr) vw or ow) (Some tr) [𝑚] σ'.(na) ∧
        alloc_local l C 𝓥.(cur) ∧ 𝑚.(mloc) = l ∧ 𝓥 ∈ σ.(mem) ∧
        Relaxed ⊑ or ∧ Relaxed ⊑ ow⌝ -∗
        atread l q rs -∗
        atwrite l 1 ws -∗
      ∃ C',
      ⌜good_hist C
        ∧ ∃ t' m' 𝓥x, C !! t' = Some m' ∧ m'.(mval) = VVal (LitV vr)
        ∧ 𝓥 ⊑ 𝓥x ∧ 𝓥x ⊑ 𝓥'
        ∧ read_helper 𝓥 or l t' tr (default ∅ m'.(mrel)) 𝓥x
        ∧ ∃ (m: baseMessage), C' = <[𝑚.(mto) := m]> C
        ∧ 𝑚.(mto) = (t'+1)%positive
        ∧ C !! 𝑚.(mto) = None ∧ m.(mval) = VVal vw
        ∧ m'.(mrel) ⊏ m.(mrel)
        ∧ 𝓥.(cur) !!w l ⊏ Some 𝑚.(mto) ∧ Some 𝑚.(mto) ⊑ 𝓥'.(cur) !!w l
        ∧ (default ∅ m'.(mrel)) !!w l ⊏ Some 𝑚.(mto)
        ∧ (¬ 𝓥'.(cur) ⊑ (default ∅ m'.(mrel)))
        ∧ cell_addins 𝑚.(mto) m C C'
        ∧ (if decide (Relaxed = or) then m.(mrel) ⊑ Some 𝓥'.(acq) else True)
        ∧ (if decide (AcqRel = or) then m.(mrel) ⊑ Some 𝓥'.(cur) else True)
        ∧ write_helper 𝓥x ow l 𝑚.(mto) (default ∅ m'.(mrel)) m.(mrel) 𝓥'⌝ ∗
      (hist_ctx σ -∗ hist l 1 C ==∗
        hist_ctx σ' ∗ hist l 1 C' ∗
        atread l q (rs ∪ {[tr]}) ∗ atwrite l 1 (ws ∪ {[𝑚.(mto)]}) ∗ seen 𝓥').
  Proof.
    iIntros "ctx hist".
    iDestruct (hist_ctx_cas_msg with "ctx hist") as "#VS".
    iDestruct (hist_ctx_wf_state with "ctx") as %WFσ.
    iDestruct (hist_ctx_hist_loc_cell_wf with "ctx hist") as %WFL.
    iIntros "!>" (σ' 𝓥 𝓥' vr vw or ow q tr 𝑚 rs ws).
    iIntros ((STEP & DRFR & DRFP & ALL & EQL & CLOSED & RLXR & RLXW)) "AR AW".
    have ? := machine_step_global_wf _ _ _ _ _ _ _ STEP DRFR DRFP WFσ CLOSED.
    inversion STEP. subst; clear STEP.
    inversion_clear DRFP. inversion_clear DRF. simplify_eq.
    set 𝓝2 := (add_aread_id (na σ) (mloc 𝑚) tr). destruct POST as [POST1 POST2].
    iDestruct ("VS" $! (mkGB σ'.(sc) σ'.(na) σ'.(mem)) 𝓥 𝓥2 𝓥' 𝓝2 𝑚1 𝑚 with "[%] AR AW")
      as (C') "{VS} [FACTS VS]".
    { rewrite SAME. do 7 (split; [done|]). split.
      { constructor. by rewrite (decide_True _ _ RLXR). } split; [done|]. split.
      { inversion_clear DRFR. inversion_clear DRFW.
        constructor; last by rewrite decide_True.
        - rewrite add_aread_id_eqnr ReadNA.
          by eapply view_sqsubseteq, read_step_tview_sqsubseteq.
        - rewrite add_aread_id_eqw AllW.
          by eapply view_sqsubseteq, read_step_tview_sqsubseteq. } split.
      { constructor. by rewrite decide_True. } do 2 (split; [done|]).
      by destruct σ'. }
    iDestruct "FACTS" as %(Ext1 & Ext2 & GC & Eq1 & RH & Eq2 & EqC' & INS & WH).
    assert (NEQ: default ∅ 𝑚1.(mbase).(mrel) !!w 𝑚.(mloc) ⊏ Some (mto 𝑚)).
    { destruct 𝑚1.(mbase).(mrel) as [Vm1|] eqn:EqVm1.
      - simpl. assert (EqL:=WFL _ _ Eq1 _ EqVm1).
        simpl in EqL. rewrite -EqL ADJ. clear.
        (* TODO reduction? *)
        change (𝑚1.(mto) ⊏ 𝑚1.(mto) + 1)%positive.
        apply strict_spec_alt. split; [|lia].
        change (𝑚1.(mto) ≤ 𝑚1.(mto) + 1)%positive. lia.
      - rewrite /= /view_lookup_write -lookup_fmap fmap_empty lookup_empty.
        by apply strict_spec_alt. }
    assert (LE: 𝑚1.(mbase).(mrel) ⊑ 𝑚.(mbase).(mrel)).
    { assert (Le := write_helper_read_write_relaxed' WH RLXW). clear -Le.
      destruct 𝑚1.(mbase).(mrel); [solve_lat|done]. }
    assert (LEt := write_helper_seen_local WH).
    iExists C'. iSplitL""; last by destruct σ'.
    iPureIntro. split; [done|]. do 2 eexists. exists 𝓥2.
    do 5 (split; [done|]). eexists.
    do 4 (split; [done|]). split.
    { apply strict_spec_alt. split; [done|].
      assert (SL:= write_helper_seen_local_write RLXW WH).
      clear -NEQ SL. rewrite /seen_local in SL. intros Eq. rewrite Eq in NEQ.
      apply : (irreflexivity (⊏) (_ !!w _)). eapply strict_transitive_l; eauto. } split.
    { assert (FR := write_helper_fresh WH). rewrite SAME. clear -Ext1 FR.
      eapply strict_transitive_r; by [apply view_sqsubseteq, Ext1|]. } split.
    { by rewrite SAME. } split.
    { by rewrite SAME. } split.
    { clear -LEt NEQ. intros Le. apply : (irreflexivity (⊏) (_ !!w _)).
      eapply strict_transitive_l; [|exact LEt]. eapply strict_transitive_r; [|exact NEQ].
      by apply view_sqsubseteq, Le. }
    repeat split; [done|..|by rewrite SAME].
    - case decide => [?|//]. subst or.
      by apply (write_helper_acq_tview_include WH), (read_helper_view_relaxed RH).
    - case decide => [?|//]. subst or.
      by apply (write_helper_cur_tview_include WH), (read_helper_view_acq RH).
  Qed.

  (* fences *)
  Lemma hist_ctx_acq_fence σ 𝓥 𝓥'
    (STEP: machine_step 𝓥 σ.(mem) σ.(sc) (event.Fence AcqRel Relaxed) None [] 𝓥' σ.(mem) σ.(sc))
    (CLOSED: 𝓥 ∈ σ.(mem)) :
    hist_ctx σ ==∗
      hist_ctx σ ∗ seen 𝓥'
      ∗ ⌜𝓥 ⊑ 𝓥' ∧ 𝓥'.(cur) = 𝓥'.(acq)⌝.
  Proof.
    iDestruct 1 as (hF V ?) "(Hhσ & HhF & Hna & Haw & Har & Hsc & HV & WF)".
    iDestruct "WF" as %(WF & HhF & HC & ?).
    have EXT := machine_step_tview_sqsubseteq _ _ _ _ _ _ _ _ _ STEP.
    iMod (own_lat_auth_update_join _ _ 𝓥'.(acq) with "HV") as "[HV' HV]".
    iModIntro. iSplitR "HV".
    - iExists _, _,_. inversion STEP. subst. iFrame.
      iPureIntro. do 2 (split; [done|]). split;[|done].
      by apply (machine_step_view_join_update _ _ _ _ _ _ _ _ STEP).
    - iDestruct (seen_own_join with "HV") as "$".
      iPureIntro. split; [done|by inversion STEP; inversion FACQ].
  Qed.

  Lemma hist_ctx_rel_fence σ 𝓥 𝓥'
    (STEP: machine_step 𝓥 σ.(mem) σ.(sc) (event.Fence Relaxed AcqRel) None [] 𝓥' σ.(mem) σ.(sc))
    (CLOSED: 𝓥 ∈ σ.(mem)) :
    hist_ctx σ ==∗
      hist_ctx σ ∗ seen 𝓥'
      ∗ ⌜𝓥 ⊑ 𝓥' ∧ 𝓥'.(frel) = 𝓥'.(cur)⌝.
  Proof.
    iDestruct 1 as (hF V ?) "(Hhσ & HhF & Hna & Haw & Hat & Hsc & HV & WF)".
    iDestruct "WF" as %(WF & HhF & HC & ?).
    inversion STEP. subst. simpl in *.
    have EXT := machine_step_tview_sqsubseteq _ _ _ _ _ _ _ _ _ STEP.
    iMod (own_lat_auth_update_join _ _ 𝓥'.(acq) with "HV")
      as "[HV' HV]".
    iModIntro. iSplitR "HV".
    - iExists _, _,_. iFrame. iPureIntro. do 2 (split; [done|]). split; [|done].
      by apply (machine_step_view_join_update _ _ _ _ _ _ _ _ STEP).
    - iDestruct (seen_own_join with "HV") as "$".
      iPureIntro. split; [done|by inversion FREL].
  Qed.

  Lemma hist_ctx_sc_fence σ σ' 𝓥 𝓥' 𝓢
    (STEP: machine_step 𝓥 σ.(mem) σ.(sc) (event.Fence SeqCst SeqCst) None [] 𝓥' σ'.(mem) σ'.(sc))
    (CLOSED: 𝓥 ∈ σ.(mem)) (EQNA: σ.(na) = σ'.(na)) :
    hist_ctx σ ∗ sc_view 𝓢 ==∗
      hist_ctx σ' ∗ sc_view (σ'.(sc)) ∗ seen 𝓥'
      ∗ ⌜𝓥 ⊑ 𝓥' ∧ 𝓢 ⊑ σ'.(sc)⌝.
  Proof.
    iDestruct 1 as "[Hσ SC]".
    iDestruct (hist_ctx_sc_view_included with "Hσ SC") as %SIn.
    iDestruct "Hσ" as (hF V ?) "(Hhσ & HhF & Hna & Haw & Hat & HSC & HV & HF)".
    iDestruct "HF" as %(WF & HhF & HC & ?).
    inversion STEP. subst.
    match goal with H : mem _ = mem _ |- _ => rename H into Eqm end.
    have ?: σ.(sc) ⊑ σ'.(sc).
    { inversion FSC. by eapply sc_fence_helper_sc_sqsubseteq. }
    iMod (own_lat_auth_update _ _ σ'.(sc) with "HSC") as "[HSC SC']"; first done.
    have EXT := machine_step_tview_sqsubseteq _ _ _ _ _ _ _ _ _ STEP.
    iMod (own_lat_auth_update_join _ _ 𝓥'.(acq) with "HV") as "[HV' HV]".
    iModIntro. iSplitR "HV SC'".
    - iExists _,_,_. rewrite -EQNA -Eqm. iFrame.
      iPureIntro. split; last (split; [done|split; last done]).
      + constructor; [..|eapply sc_fence_step_closed_sc; eauto|];
          rewrite -Eqm; auto; try apply WF; rewrite -EQNA; apply WF.
      + rewrite Eqm. by apply (machine_step_view_join_update _ _ _ _ _ V _ _ STEP).
    - rewrite sc_view_eq. iFrame "SC'".
      iDestruct (seen_own_join with "HV") as "$".
      iPureIntro. split; [done|by etrans].
  Qed.

  Lemma hist_ctx_sc_fence' σ σ' 𝓥 𝓥'
    (STEP: machine_step 𝓥 σ.(mem) σ.(sc) (event.Fence SeqCst SeqCst) None [] 𝓥' σ'.(mem) σ'.(sc))
    (CLOSED: 𝓥 ∈ σ.(mem)) (EQNA: σ.(na) = σ'.(na)) :
    hist_ctx σ ==∗
      hist_ctx σ' ∗ sc_view (σ'.(sc)) ∗ seen 𝓥'
      ∗ ⌜𝓥 ⊑ 𝓥'⌝.
  Proof.
    iDestruct 1 as (hF V ?) "(Hhσ & HhF & Hna & Haw & Hat & HSC & HV & HF)".
    iDestruct "HF" as %(WF & HhF & HC & ?).
    inversion STEP. subst.
    match goal with H : mem _ = mem _ |- _ => rename H into Eqm end.
    have ?: σ.(sc) ⊑ σ'.(sc).
    { inversion FSC. by eapply sc_fence_helper_sc_sqsubseteq. }
    iMod (own_lat_auth_update _ _ σ'.(sc) with "HSC") as "[HSC SC']"; first done.
    have EXT := machine_step_tview_sqsubseteq _ _ _ _ _ _ _ _ _ STEP.
    iMod (own_lat_auth_update_join _ _ 𝓥'.(acq) with "HV") as "[HV' HV]".
    iModIntro. iSplitR "HV SC'".
    - iExists _,_,_. rewrite -EQNA -Eqm. iFrame.
      iPureIntro. split; last (split; [done|split; last done]).
      + constructor; [..|eapply sc_fence_step_closed_sc; eauto|];
          rewrite -Eqm; auto; try apply WF; rewrite -EQNA; apply WF.
      + rewrite Eqm. by apply (machine_step_view_join_update _ _ _ _ _ V _ _ STEP).
    - rewrite sc_view_eq. iFrame "SC'".
      by iDestruct (seen_own_join with "HV") as "$".
  Qed.

End hist.

Section hist_interp.
  Context `{!noprolG Σ}.

  Lemma hist_interp_open σ E :
    ↑histN ⊆ E →
    hist_interp σ ={E,E∖↑histN}=∗
      hist_ctx σ ∗ (∀ σ', hist_ctx σ' ={E ∖ ↑histN,E}=∗ hist_interp σ').
  Proof.
    iIntros (?) "[oA #inv]". iInv histN as ">Inv" "HClose".
    iDestruct "Inv" as (σ') "[ownP ctx]".
    (* TODO: we cannot use [ownP_eq] because it fixes a state_interp. *)
    iDestruct (own_valid_2 with "oA ownP") as %<-%excl_auth_agree_L.
    iFrame "ctx". iModIntro. iIntros (σ') "ctx".
    iMod (own_update_2 _ _ _ (●E σ' ⋅ ◯E σ') with "oA ownP") as "[oA ownP]".
    { by apply excl_auth_update. }
    iMod ("HClose" with "[ownP ctx]") as "_".
    { iNext. iExists _. by iFrame. }
    by iFrame.
  Qed.

  Lemma hist_interp_seen_wf σ 𝓥 E:
    ↑histN ⊆ E → hist_interp σ -∗ seen 𝓥 ={E}=∗ hist_interp σ ∗ ⌜Wf σ ∧ 𝓥 ∈ σ.(mem)⌝.
  Proof.
    iIntros (SUB) "Hσ s".
    iMod (hist_interp_open _ _ SUB with "Hσ") as "[Hσ HClose]".
    iDestruct (hist_ctx_seen_wf with "Hσ s") as %?.
    by iMod ("HClose" with "Hσ") as "$".
  Qed.

  Lemma hist_interp_sc_view σ E:
    ↑histN ⊆ E → hist_interp σ ={E}=∗ hist_interp σ ∗ sc_view σ.(sc).
  Proof.
    iIntros (SUB) "Hσ".
    iMod (hist_interp_open _ _ SUB with "Hσ") as "[Hσ HClose]".
    iMod (hist_ctx_sc_view with "Hσ") as "[Hσ $]".
    by iMod ("HClose" with "Hσ") as "$".
  Qed.

  Lemma hist_interp_sc_view_included σ 𝓢 E:
    ↑histN ⊆ E → hist_interp σ -∗ sc_view 𝓢 ={E}=∗ hist_interp σ ∗ ⌜𝓢 ⊑ σ.(sc)⌝.
  Proof.
    iIntros (SUB) "Hσ sc".
    iMod (hist_interp_open _ _ SUB with "Hσ") as "[Hσ HClose]".
    iDestruct (hist_ctx_sc_view_included with "Hσ sc") as "#$".
    by iMod ("HClose" with "Hσ") as "$".
  Qed.
End hist_interp.
