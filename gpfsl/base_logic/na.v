From iris.bi Require Import monpred fractional.
From iris.base_logic Require Export lib.own.

From gpfsl.base_logic Require Export history vprop local_preds.

Require Import iris.prelude.options.

(* TODO: move *)
Lemma big_sepL_seq {PROP : bi} {A} (P : nat → PROP) (l : list A) :
  ([∗ list] i↦_ ∈ l, P i) ⊣⊢ ([∗ list] i ∈ seq 0 (length l), P i).
Proof.
  induction l using rev_ind; first done.
  rewrite app_length /= Nat.add_1_r seq_S !big_sepL_app /=.
  by rewrite IHl Nat.add_0_r.
Qed.

Local Existing Instances
  histGpreS_hist histGpreS_freeable histGpreS_read histGpreS_na_view
  histGpreS_at_write histGpreS_tview
  hist_inG
  .

Section na_defs.
  Context `{!noprolG Σ}.
  Local Notation vProp := (vProp Σ).

  Definition own_loc_prim l q C : vProp :=
    ∃ rsa rsn ws, ⌜ good_hist C ⌝ ∗
      AllocLocal l C ∗ AtRLocal l rsa ∗ AtWLocal l ws ∗ (∃ Va, NaLocal l rsn Va) ∗
      ⎡ hist l q C ∗  atread l q rsa ∗ atwrite l q ws ∗ naread l q rsn ⎤.

  Definition own_loc_na_def l q v : vProp :=
    ∃ t m, own_loc_prim l q {[t := m]} ∗ ⌜memval_val_rel m.(mval) v⌝ ∗ ⊒(default ∅ m.(mrel)).
  Definition own_loc_na_aux : seal (@own_loc_na_def). Proof. by eexists. Qed.
  Definition own_loc_na := unseal (@own_loc_na_aux).
  Definition own_loc_na_eq : @own_loc_na = _ := seal_eq _.
  Definition own_loc_na_any l q : vProp := (∃ v, own_loc_na l q v)%I.

  Definition own_loc_def l q : vProp :=
    (∃ t m, own_loc_prim l q {[t := m]})%I.
  Definition own_loc_aux : seal (@own_loc_def). Proof. by eexists. Qed.
  Definition own_loc := unseal (@own_loc_aux).
  Definition own_loc_eq : @own_loc = _ := seal_eq _.

  Definition own_loc_na_vec (l : loc) (q : Qp) (vl : list val) : vProp :=
    ([∗ list] i ↦ v ∈ vl, own_loc_na (l >> i) q v)%I.
  Definition own_loc_vec (l : loc) (q : Qp) (n : nat) : vProp :=
    ([∗ list] i ∈ seq 0 n, own_loc (l >> i) q)%I.
End na_defs.

Notation "l p↦ C" := (own_loc_prim l 1 C)
  (at level 20, format "l  p↦  C")  : bi_scope.
Notation "l p↦{ q } C" := (own_loc_prim l q C)
  (at level 20, format "l  p↦{ q }  C")  : bi_scope.

Notation "l ↦ v" := (own_loc_na l 1 v)
  (at level 20, format "l  ↦  v") : bi_scope.
Notation "l ↦ -" := (own_loc_na_any l 1)
  (at level 20, format "l  ↦  -") : bi_scope.
Notation "l ↦ ?" := (own_loc l 1) (at level 20, format "l  ↦  ?")  : bi_scope.
Notation "l ↦∗ vl" := (own_loc_na_vec l 1 vl) (at level 20) : bi_scope.
Notation "l ↦∗: P " := (∃ vl, l ↦∗ vl ∗ P vl)%I
  (at level 20, format "l  ↦∗:  P") : bi_scope.

Notation "l ↦{ q } v" := (own_loc_na l q v)
  (at level 20, format "l  ↦{ q }  v") : bi_scope.
Notation "l ↦{ q } -" := (own_loc_na_any l q)
  (at level 20, format "l  ↦{ q }  -") : bi_scope.
Notation "l ↦{ q } ?" := (own_loc l q) (at level 20, format "l  ↦{ q }  ?").
Notation "l ↦∗{ q } vl" := (own_loc_na_vec l q vl)
  (at level 20, q at level 50, format "l  ↦∗{ q }  vl") : bi_scope.
Notation "l ↦∗{ q }: P" := (∃ vl, l ↦∗{ q } vl ∗ P vl)%I
  (at level 20, q at level 50, format "l  ↦∗{ q }:  P") : bi_scope.

#[global] Typeclasses Opaque own_loc_na_vec own_loc_vec.

Section na_props.
  Context `{!noprolG Σ}.
  Local Notation vProp := (vProp Σ).

  Global Instance own_loc_na_into_exist l q v :
    IntoExist (l ↦{q} v)
              (λ t, ∃ m, l p↦{q} {[t := m]}
                      ∗ ⌜memval_val_rel m.(mval) v⌝ ∗ ⊒(default ∅ m.(mrel)))%I
              (to_ident_name t).
  Proof. rewrite own_loc_na_eq //. Qed.
  Global Instance own_loc_na_from_exist l q v :
    FromExist (l ↦{q} v)
              (λ t, ∃ m, l p↦{q} {[t := m]}
                      ∗ ⌜memval_val_rel m.(mval) v⌝ ∗ ⊒(default ∅ m.(mrel)))%I.
  Proof. rewrite own_loc_na_eq //. Qed.

  Global Instance own_loc_into_exist l q :
    IntoExist (l ↦{q} ?) (λ t, ∃ m, l p↦{q} {[t := m]})%I (to_ident_name t).
  Proof. rewrite own_loc_eq /own_loc_def //. Qed.
  Global Instance own_loc_from_exist l q :
    FromExist (l ↦{q} ?) (λ t, ∃ m, l p↦{q} {[t := m]})%I.
  Proof. rewrite own_loc_eq /own_loc_def //. Qed.

  Global Instance own_loc_prim_fractional l C : Fractional (λ q, l p↦{q} C)%I.
  Proof.
    rewrite /Fractional =>p q. iSplit.
    - iDestruct 1 as (rsa rsn ws GH)
        "(#AL & #ARL & #AWL & #NAL & [Hp Hq] & [Ap Aq] & [Wp Wq] & [Np Nq])".
      iSplitL "Hp Ap Wp Np"; iExists rsa, rsn, ws; by iFrame "#∗".
    - iDestruct 1 as "[Hp Hq]".
      iDestruct "Hp" as (rsa1 rsn1 ws1) "(GH & AL & ARLp & AWLp & [%Vap NALp] & Hp&Ap&Wp&Np)".
      iDestruct "Hq" as (rsa2 rsn2 ws2) "(_ & _ & ARLq & AWLq & [%Vaq NALq] & Hq&Aq&Wq&Nq)".
      iExists (rsa1 ∪ rsa2), (rsn1 ∪ rsn2), (ws1 ∪ ws2). iFrame "GH AL".
      iFrame "Hp Hq". iSplitL "ARLp ARLq"; last iSplitL "AWLp AWLq"; last iSplitL "NALp NALq".
      + iApply AtRLocal_join. by iFrame.
      + iApply AtWLocal_join. by iFrame.
      + iExists _. iApply NaLocal_join. by iFrame.
      + iDestruct (atread_combine with "Ap Aq") as "$".
        iDestruct (naread_combine with "Np Nq") as "$".
        iDestruct (atwrite_agree with "[$Wp $Wq]") as %?. subst ws2.
        rewrite union_idemp_L.
        by iDestruct (atwrite_combine with "[$Wp $Wq]") as "$".
  Qed.

  Global Instance own_loc_prim_asfractional l q C :
    AsFractional (l p↦{q} C) (λ q, l p↦{q} C)%I q.
  Proof. split; [done|apply _]. Qed.

  Global Instance frame_own_loc_prim p l v q1 q2 RES :
    FrameFractionalHyps p (l p↦{q1} v) (λ q, l p↦{q} v)%I RES q1 q2 →
    Frame p (l p↦{q1} v) (l p↦{q2} v) RES | 5.
  Proof. apply: frame_fractional. Qed.

  Global Instance own_loc_prim_timeless l q C : Timeless (l p↦{q} C) := _.

  Lemma own_loc_prim_agree_subjectively l q1 q2 C1 C2 :
    <subj> l p↦{q1} C1 -∗ <subj> l p↦{q2} C2 -∗ ⌜C1 = C2⌝.
  Proof.
    iDestruct 1 as (??? _) "(_ & _ & _ & _ & Hp & _)".
    iDestruct 1 as (??? _) "(_ & _ & _ & _ & Hq & _)".
    rewrite !objective_subjectively.
    by iDestruct (hist_agree with "[$Hp $Hq]") as %?.
  Qed.
  Lemma own_loc_prim_agree l q1 q2 C1 C2 :
    l p↦{q1} C1 -∗ l p↦{q2} C2 -∗ ⌜C1 = C2⌝.
  Proof.
    iIntros "H1 H2".
    iApply (own_loc_prim_agree_subjectively with "[H1] [H2]");
      by iApply monPred_subjectively_intro.
  Qed.

  Lemma own_loc_prim_frac_1 l q C: l p↦{q} C ⊢ ⌜✓ q ⌝.
  Proof.
    iDestruct 1 as (??? _) "(_ & _ & _ & _ & Hp & _)".
    by iDestruct (hist_frac_1 with "Hp") as %?.
  Qed.

  Lemma own_loc_prim_combine l q1 q2 C1 C2 :
    l p↦{q1} C1 -∗ l p↦{q2} C2 -∗ l p↦{q1 + q2} C1.
  Proof.
    iIntros "H1 H2". iDestruct (own_loc_prim_agree with "H1 H2") as %<-. iFrame.
  Qed.

  Global Instance own_loc_na_fractional l v : Fractional (λ q, (l ↦{q} v)%I).
  Proof.
    unfold Fractional=>p q. iSplit.
    - iDestruct 1 as (??) "[[Hp Hq] #?]". by iSplitL "Hp"; iExists _, _; iFrame.
    - iDestruct 1 as "[Hp Hq]".
      iDestruct "Hp" as (??) "[Hp ?]". iDestruct "Hq" as (??) "[Hq ?]".
      iExists _, _. iSplit; [iApply (own_loc_prim_combine with "Hp Hq")|done].
  Qed.
  Global Instance own_loc_na_asfractional l q v :
    AsFractional (l ↦{q} v) (λ q, (l ↦{q} v)%I) q.
  Proof. split; [done|apply _]. Qed.
  Global Instance frame_own_loc_na p l v q1 q2 RES :
    FrameFractionalHyps p (l ↦{q1} v) (λ q, l ↦{q} v)%I RES q1 q2 →
    Frame p (l ↦{q1} v) (l ↦{q2} v) RES | 5.
  Proof. apply: frame_fractional. Qed.

  Global Instance own_loc_na_timeless l q v: Timeless (l ↦{q} v).
  Proof. rewrite own_loc_na_eq. apply _. Qed.

  Lemma own_loc_na_frac_1 l q v: l ↦{q} v ⊢ ⌜✓ q ⌝.
  Proof.
    rewrite own_loc_na_eq. iDestruct 1 as (t m) "[Hp _]". by rewrite own_loc_prim_frac_1.
  Qed.
  Lemma own_loc_na_agree_subjectively l q1 q2 v1 v2 :
    <subj> l ↦{q1} v1 -∗ <subj> l ↦{q2} v2 -∗ ⌜v1 = v2⌝.
  Proof.
    rewrite own_loc_na_eq /own_loc_na_def.
    iDestruct 1 as (t m) "(H1 & %Hrel1 & _)".
    iDestruct 1 as (t' m') "(H2 & %Hrel2 & _)".
    iDestruct (own_loc_prim_agree_subjectively with "H1 H2") as %Eq.
    apply (f_equal (lookup t)) in Eq. rewrite lookup_singleton in Eq.
    destruct (decide (t = t')) as [<-|]; last by rewrite lookup_singleton_ne in Eq.
    rewrite lookup_singleton in Eq. iPureIntro. inversion Eq. subst. simpl in *.
    by destruct Hrel1; inversion Hrel2; subst.
  Qed.
  Lemma own_loc_na_agree l q1 q2 v1 v2 : l ↦{q1} v1 -∗ l ↦{q2} v2 -∗ ⌜v1 = v2⌝.
  Proof.
    iIntros "H1 H2".
    iApply (own_loc_na_agree_subjectively with "[H1] [H2]");
      by iApply monPred_subjectively_intro.
  Qed.

  Lemma own_loc_na_combine l q1 q2 v1 v2 :
    l ↦{q1} v1 -∗ l ↦{q2} v2 -∗ l ↦{q1 + q2} v1.
  Proof.
    iIntros "H1 H2". iDestruct (own_loc_na_agree with "H1 H2") as %<-. iFrame.
  Qed.

  Lemma own_loc_na_combine' l q1 q2 v1 v2 :
    l ↦{q1} v1 ∗ l ↦{q2} v2 ⊢ l ↦{q1 + q2} v1.
  Proof. iIntros "[H1 H2]". by iApply (own_loc_na_combine with "H1 H2"). Qed.

  Lemma own_loc_na_own_loc l v q : l ↦{q} v -∗ l ↦{q} ?.
  Proof.
    rewrite own_loc_na_eq own_loc_eq.
    iDestruct 1 as (t m) "[own ?]". iExists _,_. by iFrame.
  Qed.

  Lemma own_loc_own_loc_prim l q : l ↦{q} ? ⊢ ∃ C, l p↦{q} C.
  Proof. rewrite own_loc_eq. iDestruct 1 as (??) "?". eauto with iFrame. Qed.

  Lemma own_loc_na_own_loc_prim l v q :
    l ↦{q} v ⊢ ∃ C, l p↦{q} C.
  Proof. rewrite -own_loc_own_loc_prim. apply own_loc_na_own_loc. Qed.

  Lemma own_loc_prim_hist l q C : l p↦{q} C ⊢ ⎡ hist l q C ⎤.
  Proof. iDestruct 1 as (??? _) "(_ & _ & _ & _ & $ & _)". Qed.

  Lemma own_loc_na_own_any l v q : l ↦{q} v ⊢ l ↦{q} -.
  Proof. iIntros "own". by iExists _. Qed.

  Lemma own_loc_na_view_at_own_loc_prim_subjectively n q v V :
    @{V} n ↦{q} v ⊢ ∃ C', ▷ <subj> n p↦{q} C'.
  Proof.
    rewrite own_loc_na_own_loc_prim. iDestruct 1 as (C) "En".
    iExists C. iNext. iApply (view_at_subjectively with "En").
  Qed.
  Lemma own_loc_na_own_loc_prim_subjectively n q v :
    n ↦{q} v ⊢ ∃ C', ▷ <subj> n p↦{q} C'.
  Proof.
    rewrite own_loc_na_own_loc_prim. iDestruct 1 as (C) "En".
    iExists C. iNext. by iApply monPred_subjectively_intro.
  Qed.

  Lemma own_loc_any_own_loc_prim_subjectively n q :
    n ↦{q} - ⊢ ∃ C', ▷ <subj> n p↦{q} C'.
  Proof.
    iDestruct 1 as (?) "O".
    rewrite own_loc_na_own_loc_prim. iDestruct "O" as (C) "En".
    iExists C. iNext. by iApply monPred_subjectively_intro.
  Qed.

  Global Instance own_loc_fractional l : Fractional (own_loc l).
  Proof.
    unfold Fractional=>p q. iSplit.
    - iDestruct 1 as (??) "[Hp Hq]". iSplitL "Hp"; iExists _,_; iFrame.
    - iDestruct 1 as "[Hp Hq]". iDestruct "Hp" as (??) "Hp". iDestruct "Hq" as (??) "Hq".
      iExists _,_. iApply (own_loc_prim_combine with "Hp Hq").
  Qed.
  Global Instance own_loc_asfractional l q :
    AsFractional (own_loc l q) (own_loc l) q.
  Proof. split; [done|apply _]. Qed.

  Global Instance own_loc_timeless l q : Timeless (l ↦{q} ?).
  Proof. rewrite own_loc_eq. apply _. Qed.

  Global Instance own_loc_na_vec_fractional l vl: Fractional (λ q, l ↦∗{q} vl)%I.
  Proof.
    intros p q. rewrite /own_loc_na_vec -big_sepL_sep. do 3 f_equiv.
    by setoid_rewrite (fractional (Φ := λ q, own_loc_na _ q _)%I).
  Qed.
  Global Instance own_loc_na_vec_as_fractional l q vl:
    AsFractional (l ↦∗{q} vl) (λ q, l ↦∗{q} vl)%I q.
  Proof. split; [done|apply _]. Qed.

  Global Instance own_loc_na_vec_timeless l q vl : Timeless (l ↦∗{q} vl).
  Proof. rewrite /own_loc_na_vec. apply _. Qed.

  Global Instance own_loc_vec_timeless l q n : Timeless (own_loc_vec l q n).
  Proof. rewrite /own_loc_vec. apply _. Qed.

  Global Instance own_loc_vec_fractional l n : Fractional (λ q, own_loc_vec l q n)%I.
  Proof.
    intros p q. rewrite /own_loc_vec -big_sepL_sep. do 3 f_equiv. apply fractional.
  Qed.
  Global Instance own_loc_vec_as_fractional l q n :
    AsFractional (own_loc_vec l q n) (λ q, own_loc_vec l q n)%I q.
  Proof. split; [done|apply _]. Qed.
  Global Instance frame_own_loc_vec p l v q1 q2 RES :
    FrameFractionalHyps p (l ↦∗{q1} v) (λ q, l ↦∗{q} v)%I RES q1 q2 →
    Frame p (l ↦∗{q1} v) (l ↦∗{q2} v) RES | 5.
  Proof. apply: frame_fractional. Qed.

  Lemma own_loc_na_vec_nil l q : l ↦∗{q} [] ⊣⊢ True.
  Proof. rewrite /own_loc_na_vec bi.True_emp //. Qed.

  Lemma own_loc_na_vec_app l q vl1 vl2 :
    l ↦∗{q} (vl1 ++ vl2) ⊣⊢ l ↦∗{q} vl1 ∗ (l >> length vl1) ↦∗{q} vl2.
  Proof.
    rewrite /own_loc_na_vec big_sepL_app.
    do 2 f_equiv. intros k v. by rewrite shift_nat_assoc.
  Qed.

  Lemma own_loc_na_vec_singleton l q v : l ↦∗{q} [v] ⊣⊢ l ↦{q} v.
  Proof. rewrite /own_loc_na_vec  /= shift_0 right_id //. Qed.

  Lemma own_loc_na_vec_cons l q v vl:
    l ↦∗{q} (v :: vl) ⊣⊢ l ↦{q} v ∗ (l >> 1) ↦∗{q} vl.
  Proof.
    rewrite (own_loc_na_vec_app l q [v] vl) own_loc_na_vec_singleton //.
  Qed.

  Lemma own_loc_na_vec_repeat l q n v :
    l ↦∗{q} repeat v n ⊢ [∗ list] i ∈ seq 0 n, (l >> i) ↦{q} v.
  Proof.
    rewrite -{2}(repeat_length v n) -(big_sepL_seq _ (repeat v n)).
    revert l. induction n; simpl; intros l; first by iIntros "_".
    rewrite own_loc_na_vec_cons. iIntros "[H0 IH]".
    iSplitL "H0"; first by rewrite shift_0.
    iDestruct (IHn with "IH") as "IH".
    iApply (big_sepL_mono with "IH"). simpl.
    iIntros (i v' Eq). rewrite (_: l >> 1 >> i = l >> S i); [done|].
    rewrite /location.shift /=. f_equal. lia.
  Qed.

  Lemma own_loc_na_vec_agree l q1 q2 vl1 vl2 :
    length vl1 = length vl2 →
    l ↦∗{q1} vl1 -∗ l ↦∗{q2} vl2 -∗ ⌜vl1 = vl2⌝.
  Proof.
    revert l vl2. induction vl1 as [|v1 vl1 IH]; intros l [|v2 vl2] [=]; [by auto|].
    rewrite !own_loc_na_vec_cons. iIntros "[Hv1 Hvl1] [Hv2 Hvl2]".
    iDestruct (IH with "Hvl1 Hvl2") as %->; [done|].
      by iDestruct (own_loc_na_agree with "Hv1 Hv2") as %[=->].
  Qed.

  Lemma own_loc_na_vec_combine l q1 q2 vl1 vl2 :
    length vl1 = length vl2 →
    l ↦∗{q1} vl1 -∗ l ↦∗{q2} vl2 -∗ l ↦∗{q1+q2} vl1.
  Proof.
    iIntros (Hlen) "H1 H2".
    iDestruct (own_loc_na_vec_agree with "H1 H2") as %->; [done|]. iFrame.
  Qed.

  Global Instance own_loc_na_pred_fractional l (P : list val → vProp):
    (∀ vl, Persistent (P vl)) → Fractional (λ q, l ↦∗{q}: P)%I.
  Proof.
    intros p q q'. iSplit.
    - iIntros "H". iDestruct "H" as (vl) "[[Hown1 Hown2] #HP]".
      iSplitL "Hown1"; eauto.
    - iIntros "[H1 H2]". iDestruct "H1" as (vl1) "[Hown1 #HP1]".
      iDestruct "H2" as (vl2) "[Hown2 #HP2]".
      set (ll := min (length vl1) (length vl2)).
      rewrite -[vl1](firstn_skipn ll) -[vl2](firstn_skipn ll) 2!own_loc_na_vec_app.
      iDestruct "Hown1" as "[Hown1 _]". iDestruct "Hown2" as "[Hown2 _]".
      assert (length (take ll vl1) = length (take ll vl2)).
      { rewrite !firstn_length /ll. lia. }
      iDestruct (own_loc_na_vec_agree with "Hown1 Hown2") as %Hl; [done|].
      rewrite -Hl. iCombine "Hown1" "Hown2" as "Hown".
      iExists (take ll vl1). iFrame.
      destruct (Nat.min_spec (length vl1) (length vl2)) as [[Hne Heq]|[Hne Heq]].
      + iClear "HP2". rewrite take_ge; last by rewrite -Heq.
        rewrite drop_ge; first by rewrite app_nil_r. by rewrite -Heq.
      + iClear "HP1". rewrite Hl take_ge; last by rewrite -Heq.
        rewrite drop_ge; first by rewrite app_nil_r. by rewrite -Heq.
  Qed.
  Global Instance own_loc_na_pred_as_fractional l q (P : list val → vProp):
    (∀ vl, Persistent (P vl)) → AsFractional (l ↦∗{q}: P) (λ q, l ↦∗{q}: P)%I q.
  Proof. split; [done|apply _]. Qed.

  Lemma own_loc_na_pred_combine l q1 q2 n (Φ : list val → vProp) :
    (∀ vl, Φ vl -∗ ⌜length vl = n⌝) →
    l ↦∗{q1}: Φ ∗ l ↦∗{q2}: (λ vl, ⌜length vl = n⌝) ⊣⊢ l ↦∗{q1+q2}: Φ.
  Proof.
    intros Hlen. iSplit.
    - iIntros "[Hmt1 Hmt2]".
      iDestruct "Hmt1" as (vl) "[Hmt1 Hown]". iDestruct "Hmt2" as (vl') "[Hmt2 %]".
      iDestruct (Hlen with "Hown") as %?. subst. iExists _. iFrame "Hown".
      by iApply (own_loc_na_vec_combine with "Hmt1 Hmt2").
    - iIntros "Hmt". iDestruct "Hmt" as (vl) "[[Hmt1 Hmt2] Hown]".
      iDestruct (Hlen with "Hown") as %?.
      iSplitL "Hmt1 Hown"; iExists _; by iFrame.
  Qed.

  Lemma own_loc_na_pred_wand l q Φ1 Φ2 :
    l ↦∗{q}: Φ1 -∗ (∀ vl, Φ1 vl -∗ Φ2 vl) -∗ l ↦∗{q}: Φ2.
  Proof.
    iIntros "Hm Hwand". iDestruct "Hm" as (vl) "[Hm HΦ]". iExists vl.
    iFrame "Hm". by iApply "Hwand".
  Qed.

  Lemma own_loc_na_pred_iff_proper l q Φ1 Φ2 :
    □ (∀ vl, Φ1 vl ↔ Φ2 vl) -∗ □ (l ↦∗{q}: Φ1 ↔ l ↦∗{q}: Φ2).
  Proof.
    iIntros "#HΦ !>".
    iSplit; iIntros; iApply (own_loc_na_pred_wand with "[-]"); try done;
    iIntros; by iApply "HΦ".
  Qed.

  Lemma own_loc_vec_nil l q : own_loc_vec l q 0 ⊣⊢ True.
  Proof. rewrite /own_loc_vec bi.True_emp //. Qed.

  Lemma own_loc_vec_app l q n1 n2 :
    own_loc_vec l q (n1 + n2) ⊣⊢ own_loc_vec l q n1 ∗ own_loc_vec (l >> n1) q n2.
  Proof.
    rewrite /own_loc_vec -!(big_sepL_fmap (λ i:nat, _ >> i) (λ _ l, l ↦{q} ?))
            -big_sepL_app.
    f_equiv. apply reflexive_eq, list_eq=>i.
    destruct (decide (i < n1)%nat).
    - rewrite lookup_app_l ?fmap_length ?seq_length // !list_lookup_fmap
              !lookup_seq_lt //. lia.
    - rewrite lookup_app_r ?fmap_length ?seq_length ?Nat.le_ngt // !list_lookup_fmap.
      destruct (decide (i < n1 + n2)%nat).
      + rewrite !lookup_seq_lt /= ?shift_nat_assoc; repeat f_equal; lia.
      + rewrite !lookup_seq_ge //; lia.
  Qed.

  Lemma own_loc_vec_singleton l q : own_loc_vec l q 1 ⊣⊢ l ↦{q} ?.
  Proof. rewrite /own_loc_vec /= shift_0 right_id //. Qed.

  Lemma own_loc_vec_S l q n :
    own_loc_vec l q (S n) ⊣⊢ l ↦{q} ? ∗ own_loc_vec (l >> 1) q n.
  Proof. rewrite (own_loc_vec_app l q 1 n) own_loc_vec_singleton //. Qed.

End na_props.
