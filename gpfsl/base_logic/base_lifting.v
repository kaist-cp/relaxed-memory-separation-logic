From iris.program_logic Require Import weakestpre.
From iris.program_logic Require Import ectx_lifting.
From iris.proofmode Require Import proofmode.

From gpfsl.lang Require Export notation tactics.
From gpfsl.base_logic Require Export history vprop na meta_data.

Require Import iris.prelude.options.

Local Hint Constructors head_step bin_op_eval un_op_eval lit_eq lit_neq : core.

Class AsRec (e : expr) (f : binder) (xl : list binder) (erec : expr) :=
  as_rec : e = Rec f xl erec.
Global Instance AsRec_rec f xl e : AsRec (Rec f xl e) f xl e := eq_refl.
Global Instance AsRec_rec_locked_val v f xl e :
  AsRec (of_val v) f xl e → AsRec (of_val (locked v)) f xl e.
Proof. by unlock. Qed.

Class DoSubst (x : binder) (es : expr) (e er : expr) :=
  do_subst : subst' x es e = er.
Global Hint Extern 0 (DoSubst _ _ _ _) =>
  rewrite /DoSubst; simpl_subst; reflexivity : typeclass_instances.

Class DoSubstL (xl : list binder) (esl : list expr) (e er : expr) :=
  do_subst_l : subst_l xl esl e = Some er.
Global Instance do_subst_l_nil e : DoSubstL [] [] e e.
Proof. done. Qed.
Global Instance do_subst_l_cons x xl es esl e er er' :
  DoSubstL xl esl e er' → DoSubst x es er' er →
  DoSubstL (x :: xl) (es :: esl) e er.
Proof. rewrite /DoSubstL /DoSubst /= => -> <- //. Qed.
Global Instance do_subst_vec xl (vsl : vec val (length xl)) e :
  DoSubstL xl (of_val <$> vec_to_list vsl) e (subst_v xl vsl e).
Proof. by rewrite /DoSubstL subst_v_eq. Qed.

Section base_lifting.

Context `{!noprolG Σ}.

(* Pure steps *)

Local Ltac solve_exec_safe :=
  intros; destruct_and?; subst; eexists _, _, []; do 2 econstructor;
  simpl; eauto with lia.
Local Ltac solve_exec_puredet :=
  simpl; intros; destruct_and?; inv_head_step; inv_bin_op_eval;
  inv_un_op_eval; inv_lit; done.
Local Ltac solve_pure_exec :=
  intros ?; apply nsteps_once, pure_head_step_pure_step;
    constructor; [ solve_exec_safe | solve_exec_puredet ].

Global Instance pure_rec e f xl erec erec' el 𝓥 :
  AsRec e f xl erec →
  TCForall AsVal el →
  Closed (f :b: xl +b+ []) erec →
  DoSubstL (f :: xl) (e :: el) erec erec' →
  PureExec True 1 (App e el at 𝓥) (erec' at 𝓥).
Proof.
  rewrite /AsRec /DoSubstL=> -> /TCForall_Forall ???. solve_pure_exec.
  eapply Forall_impl; [done|]. intros e' [v <-]. rewrite to_of_val; eauto.
Qed.

Global Instance pure_le (n1 n2 : Z) 𝓥 :
  PureExec True 1 (#n1 ≤ #n2 at 𝓥) (#(bool_decide (n1 ≤ n2)) at 𝓥).
Proof. solve_pure_exec. Qed.

Global Instance pure_lt (n1 n2 : Z) 𝓥 :
  PureExec True 1 (#n1 < #n2 at 𝓥) (#(bool_decide (n1 < n2)) at 𝓥).
Proof. solve_pure_exec. Qed.

Global Instance pure_eq_int (n1 n2 : Z) 𝓥 :
  PureExec True 1 (#n1 = #n2 at 𝓥) (#(bool_decide (n1 = n2)) at 𝓥).
Proof. case_bool_decide; solve_pure_exec. Qed.

Global Instance pure_eq_loc_0_r (l : loc) 𝓥 :
  PureExec True 1 (#l = #0 at 𝓥) (#false at 𝓥).
Proof. solve_pure_exec. Qed.

Global Instance pure_eq_loc_0_l (l : loc) 𝓥 :
  PureExec True 1 (#0 = #l at 𝓥) (#false at 𝓥).
Proof. solve_pure_exec. Qed.

Global Instance pure_plus (z1 z2 : Z) 𝓥 :
  PureExec True 1 (#z1 + #z2 at 𝓥) (#(z1 + z2) at 𝓥).
Proof. solve_pure_exec. Qed.

Global Instance pure_minus (z1 z2 : Z) 𝓥 :
  PureExec True 1 (#z1 - #z2 at 𝓥) (#(z1 - z2) at 𝓥).
Proof. solve_pure_exec. Qed.

Global Instance pure_mult (z1 z2 : Z) 𝓥 :
  PureExec True 1 (#z1 * #z2 at 𝓥) (#(z1 * z2) at 𝓥).
Proof. solve_pure_exec. Qed.

Global Instance pure_quot (z1 z2 : Z) 𝓥 :
  PureExec True 1 (#z1 `quot` #z2 at 𝓥) (#(z1 `quot` z2) at 𝓥).
Proof. solve_pure_exec. Qed.

Global Instance pure_div (z1 z2 : Z) 𝓥 :
  PureExec True 1 (#z1 `div` #z2 at 𝓥) (#(z1 `div` z2) at 𝓥).
Proof. solve_pure_exec. Qed.

Global Instance pure_rem (z1 z2 : Z) 𝓥 :
  PureExec True 1 (#z1 `rem` #z2 at 𝓥) (#(z1 `rem` z2) at 𝓥).
Proof. solve_pure_exec. Qed.

Global Instance pure_mod (z1 z2 : Z) 𝓥 :
  PureExec True 1 (#z1 `mod` #z2 at 𝓥) (#(z1 `mod` z2) at 𝓥).
Proof. solve_pure_exec. Qed.

Global Instance pure_offset (l : loc) (z : Z) 𝓥 :
  PureExec True 1 (#l +ₗ #z at 𝓥) (#(l >> Z.to_nat z) at 𝓥).
Proof. solve_pure_exec. Qed.

Global Instance pure_case (i : Z) e el 𝓥 :
  PureExec (0 ≤ i ∧ el !! (Z.to_nat i) = Some e) 1
           (case: #i of el at 𝓥) (e at 𝓥) | 10.
Proof. solve_pure_exec. Qed.

Global Instance pure_if (b : bool) e1 e2 𝓥 :
  PureExec True 1 (If #b e1 e2 at 𝓥) ((if b then e1 else e2) at 𝓥) | 1.
Proof. destruct b; solve_pure_exec. Qed.

Global Instance pure_neg (z : Z) 𝓥 :
  PureExec True 1 (UnOp NegOp #z at 𝓥) (#(bool_decide (z = 0)) at 𝓥).
Proof. solve_pure_exec. Qed.

Global Instance pure_uminus (z : Z) 𝓥 :
  PureExec True 1 (UnOp MinusUnOp #z at 𝓥) (#(-z) at 𝓥).
Proof. solve_pure_exec. Qed.

(* Stateful reductions *)
Lemma iwp_alloc E n 𝓥:
  ↑histN ⊆ E → 0 < n →
  {{{ ▷ seen 𝓥 }}} Alloc #n at 𝓥 @ E
  {{{ (l: loc) 𝓥', RET #l at 𝓥';
        ⌜𝓥 ⊑ 𝓥'⌝ ∗ seen 𝓥'
      ∗ †l…(Z.to_nat n)
      ∗ (l ↦∗ repeat #☠ (Z.to_nat n)
      ∗ [∗ list] i ∈ seq 0 (Z.to_nat n), meta_token (l >> i) ⊤) 𝓥'.(cur) }}}.
Proof.
  iIntros (SUB ? Φ) ">Seen HΦ". iApply wp_lift_atomic_head_step_no_fork; auto.
  iIntros (σ1 ? κ κs ?) "Hσ".
  iMod (hist_interp_seen_wf _ _ _ SUB with "Hσ Seen") as "[Hσ [%WF %HC]]".
  iModIntro. iSplit; [iPureIntro|iNext].
  - destruct (alloc_fresh_head_step n _ _ HC) as [σ2 [𝓥2 STEP]]; first done.
    econstructor. do 3 eexists. exact STEP.
  - iIntros (v2 σ2 efs Hstep) "_"; inv_head_step.
    (* accessing hist_ctx *)
    iMod (hist_interp_open _ _ SUB with "Hσ") as "[Hσ HClose]".
    have ?: ot = None by inversion DRFPost. subst ot.
    iMod (hist_ctx_alloc _ (mkGB 𝓢' 𝓝' M') _ _ _ _ _ PStep with "Hσ")
      as "(Hσ' & hF & Hists & Hars & Haws & Hnas & Seen' & Ext)";
      eauto; first by apply WF.
    iMod ("HClose" with "Hσ'") as "$".
    (* done accessing hist_ctx *)
    iModIntro; iSplit; [done|]. iApply "HΦ".
    have Eqn: Pos.to_nat (Z.to_pos n) = Z.to_nat n
      by rewrite -Z2Nat.inj_pos Z2Pos.id.
    rewrite Eqn. iFrame.
    inversion_clear PStep. rewrite Eqn /= in ALLOC.
    rewrite cell_list_fmap big_sepL_fmap /=.
    rewrite (_:∀ n l, (l ↦∗{1} repeat #☠ n) ⊣⊢
       [∗ list] k↦_ ∈ seq 0 n, ((l >> k) ↦ #☠)); last first.
    { clear. induction n=>/= l.
      - rewrite own_loc_na_vec_nil. iSplit; auto.
      - rewrite own_loc_na_vec_cons shift_0 IHn. f_equiv.
        rewrite -!(big_sepL_fmap (λ _ : nat, tt) (λ _ _, (_ ↦ #☠)%I)). f_equiv.
        + intros ? []. by rewrite (shift_nat_assoc _ 1).
        + apply list_eq=>i. rewrite !list_lookup_fmap.
          destruct (decide (i < n)%nat).
          * rewrite !lookup_seq_lt //. * rewrite !lookup_seq_ge //; lia. }
    iCombine "Hists Hars Haws Hnas" as "Hists".
    rewrite -4!big_sepL_sep monPred_at_big_sepL.
    iApply (big_sepL_mono with "Hists").
    move => n1 n2 /lookup_seq [/= -> Lt].
    destruct (lookup_lt_is_Some_2 𝑚s n1) as [𝑚 Eq𝑚];
      first by rewrite (alloc_step_length _ _ _ _ _ _ _ ALLOC).
    rewrite -(alloc_step_loc_eq _ _ _ _ _ _ _ ALLOC _ _ Eq𝑚)
            (alloc_step_mem_lookup _ _ _ _ _ _ _ ALLOC 𝑚
                                   (elem_of_list_lookup_2 _ _ _ Eq𝑚)).
    have EqVal := alloc_step_AVal _ _ _ _ _ _ _ ALLOC _ _ Eq𝑚.
    iIntros "((Hist & Meta & %) & ar & aw & na)".
    rewrite meta_token_eq. iFrame "Meta".
    iExists _, _. iSplitL "Hist ar aw na".
    + iExists ∅,∅,∅. iFrame. iPureIntro.
      split; last split; [done| |split]; last split.
      * eexists (mto 𝑚), (mbase 𝑚). split; [by rewrite lookup_insert|].
        rewrite EqVal. split; [done|]. inversion ALLOC.
        apply (alloc_helper_cur_sqsubseteq _ _ _ VALL), elem_of_list_lookup.
        by eexists.
      * eapply alloc_helper_aread_ids; [by inversion ALLOC|].
        by eapply elem_of_list_lookup_2.
      * eapply alloc_helper_awrite_ids; [by inversion ALLOC|].
        by eapply elem_of_list_lookup_2.
      * exists 𝓥'.(cur); split; [|done].
        eapply alloc_helper_nread_ids; [by inversion ALLOC|].
        by eapply elem_of_list_lookup_2.
    + iPureIntro. rewrite EqVal. split; [constructor|].
      by rewrite (alloc_step_view_None  _ _ _ _ _ _ _ ALLOC _ _ Eq𝑚).
Qed.

Lemma iwp_free E (n : Z) (l: loc) 𝓥 :
  ↑histN ⊆ E → 0 ≤ n →
  {{{ ▷ seen 𝓥 ∗ ▷ own_loc_vec l 1 (Z.to_nat n) 𝓥.(cur) ∗ ▷ †l…(Z.to_nat n)  }}}
    Free #n #l at 𝓥 @ E
  {{{ 𝓥', RET #☠ at 𝓥'; ⌜𝓥 ⊑ 𝓥'⌝ ∗ seen 𝓥' }}}.
Proof.
  iIntros (SUB ? Φ) "(>Seen & >Hmt & >Hf) HΦ".
  iApply wp_lift_atomic_head_step_no_fork; auto.
  iIntros (σ1 ? κ κs ?) "Hσ".
  (* accessing hist_ctx *)
  iMod (hist_interp_open _ _ SUB with "Hσ") as "[Hσ HClose]".
  iDestruct (hist_ctx_hist_freeable_blk with "Hσ Hf") as %[Hn EQD].
  iDestruct (hist_ctx_seen_wf with "Hσ Seen") as %(WF & HC).
  iDestruct (hist_ctx_hists_free with "Hσ [Hmt]") as %PRE.
  { rewrite /own_loc_vec monPred_at_big_sepL. iApply (big_sepL_mono with "Hmt").
    move=>??? /=. rewrite own_loc_eq.
    iDestruct 1 as (?????????(?&?&?)) "(? &?&?&?)".
    iExists _,_,_,_,_. iFrame. iPureIntro. do 3 (split; [done|]).
    by eapply na_local_mono; eauto. }
  iMod ("HClose" with "Hσ") as "Hσ".
  (* done accessing hist_ctx *)
  iModIntro. iSplit.
  - iPureIntro.
    destruct (dealloc_head_step (Z.to_nat n) l σ1 𝓥) as [σ2 [𝓥2 STEP]];
      [| | |exact EQD| |apply WF|exact HC|done|..
       |econstructor; eexists; exists σ2, []; rewrite Z2Nat.id // in STEP;
          exact STEP]; move => ??; by apply PRE.
  - iNext. iIntros (v2 σ2 efs Hstep) "_"; inv_head_step.
    (* accessing hist_ctx *)
    iMod (hist_interp_open _ _ SUB with "Hσ") as "[Hσ HClose]".
    have ?: ot = None by inversion DRFPost. subst ot.
    iMod (hist_ctx_dealloc _ (mkGB 𝓢' 𝓝' M') _ _ _ _ _ PStep with "[$Hσ Hmt]")
      as "(Hσ' & seen' & Ext)"; [|done|done|apply WF|..|done| |].
    { eapply (DRFPre _ _ []); eauto. }
    { rewrite /own_loc_vec monPred_at_big_sepL. iApply (big_sepL_mono with "Hmt").
      move => ??? /=. iDestruct 1 as (?????) "(_&_&_&_&_&?)".
      iExists _,_,_,_. by iFrame. }
    iMod ("HClose" with "Hσ'") as "$".
    (* done accessing hist_ctx *)
    iModIntro; iSplit; [done|]. iApply "HΦ". iFrame.
Qed.

Lemma read_head_reducible σ l q C o 𝓥:
  alloc_local l C 𝓥.(cur) →
  (o = NonAtomic → σ.(na) !!aw l ⊑ 𝓥.(cur) !!aw l ∧ ∃ t m, C = {[t := m]}) →
  seen 𝓥 -∗ hist_ctx σ -∗ hist l q%Qp C -∗ ⌜head_reducible (Read o #l at 𝓥)%E σ⌝.
Proof.
  iIntros (ALLOC NASGL) "seen Hσ hist".
  iDestruct (hist_ctx_hist_allocated with "Hσ hist") as %MALLOC.
  iDestruct (hist_ctx_hist_cut with "Hσ hist") as %(Vc&LE&ta&Eqta&EqC&?&?&?&?).
  iDestruct (hist_ctx_seen_wf with "Hσ seen") as %(WF & HC). subst C.
  destruct (read_head_step l o _ _ HC) as [σ2 [𝓥2 [v' STEP]]];
    [apply WF|apply WF|exact MALLOC|done|..].
  - specialize (LE l). apply view_sqsubseteq in LE as [LE1 LE2].
      rewrite LE1 Eqta. by eapply alloc_local_cut.
  - move => /NASGL [? [to [mo EqCo]]]. split; [|done].
    by eapply (alloc_local_cut_singleton _ _ _  _ _ _ _ Vc ALLOC).
  - iPureIntro. econstructor. do 3 eexists. exact STEP.
Qed.

Lemma iwp_read l q C rs ws o E Va 𝓥 :
  alloc_local l C 𝓥.(cur) →
  (if decide (Relaxed ⊑ o) then atr_local l rs Va else True) →
  (o = NonAtomic → ∃ t m, C = {[t := m]}) →
  ↑histN ⊆ E →
  {{{ ▷ seen 𝓥 ∗ ▷ hist l q C ∗
      (if decide (Relaxed ⊑ o) then atread l q rs else naread l q rs) ∗
      (if decide (Relaxed ⊑ o) then True
       else atwrite l q ws ∗ ⌜atw_local l ws 𝓥.(cur)⌝) }}}
    Read o #l at 𝓥 @ E
  {{{ 𝓥' v tr, RET v at 𝓥'; seen 𝓥'
        ∗ hist l q C
        ∗ (if decide (Relaxed ⊑ o)
           then atread l q (rs ∪ {[tr]}) else naread l q (rs ∪ {[tr]}))
        ∗ (if decide (Relaxed ⊑ o)
           then True else atwrite l q ws)
        ∗ ⌜𝓥 ⊑ 𝓥' ∧ good_hist C
          ∧ ∃ t m, C !! t = Some m
          ∧ memval_val_rel m.(mval) v
          ∧ read_helper 𝓥 o l t tr (default ∅ m.(mrel)) 𝓥'
          ∧ (if decide (Relaxed ⊑ o)
              then atr_local l (rs ∪ {[tr]}) (Va ⊔ 𝓥'.(cur))
              else ∀ Vna, na_local l rs Vna → na_local l (rs ∪ {[tr]}) (join Vna 𝓥'.(cur)))⌝ }}}.
Proof.
  iIntros (ALLOC DRF NASGL SUB Φ) "(>seen & >hist & ana & Haw) HΦ".
  iApply wp_lift_atomic_head_step_no_fork; first auto.
  iIntros (σ1 ? κ κs ?) "Hσ".
  (* accessing hist_ctx *)
  iMod (hist_interp_open _ _ SUB with "Hσ") as "[Hσ HClose]".
  iDestruct (hist_ctx_seen_wf with "Hσ seen") as %(WF & HC).
  iAssert (⌜o = NonAtomic → atw_local l ws 𝓥.(cur) ∧ σ1.(na) !!aw l = Some ws⌝)%I
    with "[Hσ Haw]" as %NA.
  { iIntros (?). subst o. simpl. iDestruct "Haw" as "(Haw & %)".
    by iDestruct (hist_ctx_atwrite_eq with "Hσ Haw") as %?. }
  iDestruct (read_head_reducible _ _ _ _ o with "seen Hσ hist") as %?; [done|..].
  { move => ISNA. specialize (NASGL ISNA). destruct (NA ISNA) as [ATL Eqws].
    split; [|done]. by rewrite Eqws. }
  iMod ("HClose" with "Hσ") as "Hσ".
  (* done accessing hist_ctx *)
  iModIntro; iSplit; [done|].
  iNext. iIntros (v2 σ2 efs Hstep) "_"; inv_head_step.
  (* accessing hist_ctx *)
  iMod (hist_interp_open _ _ SUB with "Hσ") as "[Hσ HClose]".
  iDestruct (hist_ctx_read with "Hσ hist") as "#VS".
  assert (∃ tr, ot = Some tr ∧ 𝑚s = []) as [tr [? ?]].
  { inversion_clear DRFPost. by eexists. } subst ot 𝑚s.
  iDestruct ("VS" $! (mkGB 𝓢' 𝓝' M') with "[%] ana") as "{VS} [FACTS VS]"; [done|].
  iMod ("VS" with "Hσ") as "(Hσ' & seen' & ana')".
  iMod ("HClose" with "Hσ'") as "$".
  iModIntro; iSplit; [done|].
  iDestruct "FACTS" as %(LEV&?&t&m&?&Eqv&RH&?).
  rewrite /= /nopro_lang.to_val to_of_val /=. iApply "HΦ"; iFrame.
  iSplitL "Haw". { case_decide; [done|]. by iDestruct "Haw" as "($&?)". }
  iPureIntro; (do 2 (split; [done|])). exists t, m. rewrite Eqv.
  do 3 (split; [done|]). case decide => EQP.
  - rewrite (decide_True _ _ EQP) in DRF.
    have ATL:= read_helper_atr_local _ _ _ _ _ _ _ _ _ RH DRF.
    by rewrite decide_True in ATL.
  - intros Vna NAL.
    have NAL':= read_helper_na_local _ _ _ _ _ _ _ _ _ RH NAL.
    by rewrite decide_False in NAL'.
Qed.

Lemma iwp_read_non_atomic l q v E 𝓥:
  ↑histN ⊆ E →
  {{{ ▷ seen 𝓥 ∗ (▷ l ↦{q} v) 𝓥.(cur) }}}
    !(#l) at 𝓥 @ E
  {{{ 𝓥', RET v at 𝓥'; ⌜𝓥 ⊑ 𝓥'⌝ ∗ seen 𝓥' ∗ (l ↦{q} v) 𝓥'.(cur) }}}.
Proof.
  iIntros (? Φ) "(>seen & >Hp) HΦ". rewrite own_loc_na_eq.
  iDestruct "Hp" as (t m) "[hist [%Hv %Hrel]]".
  iDestruct "hist" as (rsa rsn ws GH ALLOC AR AW (Vna & NA & LeVna))
                      "(hist & ar & aw & na)".
  iApply (iwp_read _ _ {[t := m]} rsn ws NonAtomic _ 𝓥.(cur)
          with "[$seen $hist na aw]"); [done|done|by eauto|done|by iFrame|].
  iNext. iIntros (𝓥' v' tr) "(seen' & hist & na & aw & HL)".
  iDestruct "HL" as %(Ext & ? & t' & m' & [??]%lookup_singleton_Some
                      & Hv' & READ & NA').
  subst t' m'. assert (v = v') as <- by by destruct Hv; inversion Hv'.
  iApply "HΦ". iFrame (Ext) "seen'".
  iExists t, m. rewrite -> Ext in Hrel. iSplit; [|done]. iExists _,_,_.
  iFrame "hist ar aw na". iPureIntro. simpl in NA'.
  split; last split; last split; last split; [done|..|].
  - eapply alloc_local_mono; [done|apply Ext|eauto].
  - by eapply atr_local_mono; [|apply Ext|eauto].
  - by eapply atw_local_mono; [|apply Ext|eauto].
  - eexists. split; first apply (NA' _ NA).
    clear -Ext LeVna. apply cur_mono in Ext. solve_lat.
Qed.

Lemma iwp_read_atomic l q C rs o E Va 𝓥 :
  Relaxed ⊑ o → alloc_local l C 𝓥.(cur) →
  atr_local l rs Va → ↑histN ⊆ E →
  {{{ ▷ seen 𝓥 ∗ ▷ hist l q C ∗ atread l q rs }}}
    Read o #l at 𝓥 @ E
  {{{ 𝓥' v tr, RET v at 𝓥'; seen 𝓥'
        ∗ hist l q C ∗ atread l q (rs ∪ {[tr]})
        ∗ ⌜𝓥 ⊑ 𝓥' ∧ good_hist C
          ∧ ∃ t m, C !! t = Some m
          ∧ memval_val_rel m.(mval) v
          ∧ read_helper 𝓥 o l t tr (default ∅ m.(mrel)) 𝓥'
          ∧ atr_local l (rs ∪ {[tr]}) (Va ⊔ 𝓥'.(cur))⌝ }}}.
Proof.
  iIntros (RLX ALL ATR SUB Φ) "(s & hist & at) Post".
  iApply (iwp_read _ _ _ _ ∅ with "[$s $hist at]");
    [done|by rewrite decide_True|move => ?; by subst o|done|..].
  { rewrite 2!(decide_True _ _ RLX). by iFrame. }
  iIntros "!>" (???) "(s' & hist & at & _ & FACT)".
  rewrite 2!(decide_True _ _ RLX).
  by iApply ("Post" with "[$s' $hist $at $FACT]").
Qed.

Lemma write_head_reducible l (v : val) o C rs ws σ 𝓥:
  alloc_local l C 𝓥.(cur) →
  na_local l rs 𝓥.(cur) →
  (o = NonAtomic → ∃ t m, C = {[t := m]}) →
  seen 𝓥 -∗ hist_ctx σ -∗ hist l 1 C -∗ naread l 1 rs -∗ atwrite l 1 ws -∗
  (if decide (Relaxed ⊑ o) then True
   else ∃ rsa, atread l 1 rsa ∗
        ⌜atr_local l rsa 𝓥.(cur) ∧ atw_local l ws 𝓥.(cur)⌝) -∗
  ⌜head_reducible (Write o #l v at 𝓥)%E σ⌝.
Proof.
  iIntros (ALLOC NA NASGL) "seen Hσ hist na ag at".
  iDestruct (hist_ctx_hist_allocated with "Hσ hist") as %MALLOC.
  iDestruct (hist_ctx_hist_cut with "Hσ hist") as %[Vc [LE [ta [Eqta [? _]]]]].
  iDestruct (hist_ctx_seen_wf with "Hσ seen") as %(WF & HC).
  iDestruct (hist_ctx_naread_eq with "Hσ na") as %Eqna.
  iAssert (⌜o = NonAtomic → ∃ rsa, σ.(na) !!ar l = Some rsa ∧
            σ.(na) !!aw l = Some ws ∧ atr_local l rsa 𝓥.(cur) ∧
            atw_local l ws 𝓥.(cur)⌝)%I as %AT.
  { iIntros (?). subst o. iDestruct "at" as (rst) "(ar & % & %)".
    iDestruct (hist_ctx_atread_eq with "Hσ ar") as %?.
    iDestruct (hist_ctx_atwrite_eq with "Hσ ag") as %?.
    iPureIntro. by do 2 eexists. }
  iPureIntro. subst C. have ALLOC2 := ALLOC.
  destruct ALLOC as [t' [m' [[Eqm' Le']%cell_cut_lookup_Some [_ SEEN]]]].
  destruct (write_head_step l v v o σ 𝓥) as [σ2 [𝓥2 STEP]];
    [done|apply WF|exact MALLOC| |by rewrite to_of_val|..].
  - do 2 eexists. by rewrite memory_lookup_cell.
  - by rewrite Eqna.
  - specialize (LE l). apply view_sqsubseteq in LE as [LE1 LE2].
    rewrite LE1 Eqta. by etrans; last apply SEEN.
  - move => ISNA. destruct (NASGL ISNA) as [to [mo EqCo]]. split.
    * by eapply (alloc_local_cut_singleton _ _ _  _ _ _ _ Vc ALLOC2).
    * move : ISNA => /AT [? [-> [-> [//]]]].
  - econstructor. do 3 eexists. exact STEP.
Qed.

Lemma iwp_write l (v: val) C Va rs ws o E 𝓥:
  alloc_local l C 𝓥.(cur) → na_local l rs 𝓥.(cur) →
  (if decide (Relaxed ⊑ o) then atw_local l ws Va else atw_local l ws 𝓥.(cur)) →
  (o = NonAtomic → ∃ t m, C = {[t := m]}) → ↑histN ⊆ E →
  {{{ ▷ seen 𝓥 ∗ ▷ hist l 1 C ∗ naread l 1 rs ∗ atwrite l 1 ws ∗
      (if decide (Relaxed ⊑ o) then True
        else ∃ rsa, atread l 1 rsa ∗ ⌜atr_local l rsa 𝓥.(cur)⌝) }}}
    Write o #l v at 𝓥 @ E
  {{{ 𝓥' C' t, RET #☠ at 𝓥'; seen 𝓥'
        ∗ hist l 1 C' ∗ naread l 1 rs
        ∗ (if decide (Relaxed ⊑ o)
           then atwrite l 1 (ws ∪ {[t]}) ∗
                ⌜atw_local l (ws ∪ {[t]}) (Va ⊔ 𝓥'.(cur))⌝
           else atwrite l 1 ws ∗
                ∃ rsa, atread l 1 rsa ∗ ⌜atr_local l rsa 𝓥'.(cur)⌝)
        ∗ ⌜𝓥 ⊑ 𝓥' ∧ good_hist C ∧ good_hist C'
            ∧ ∃ m, C' = <[t:= m]> (if (decide (Relaxed ⊑ o)) then C else ∅)
            ∧ C !! t = None ∧ m.(mval) = VVal v
            ∧ (if (decide (Relaxed ⊑ o)) then cell_addins t m C C' else True)
            ∧ 𝓥.(cur) ≠ 𝓥'.(cur)
            ∧ write_helper 𝓥 o l t ∅ m.(mrel) 𝓥'⌝ }}}.
Proof.
  iIntros (ALLOC NA AT NASGL SUB Φ) "(>seen & >hist & na & aw & ar) HΦ".
  iApply wp_lift_atomic_head_step_no_fork; first auto.
  iIntros (σ1 ? κ κs ?) "Hσ".
  (* accessing hist_ctx *)
  iMod (hist_interp_open _ _ SUB with "Hσ") as "[Hσ HClose]".
  iDestruct (hist_ctx_seen_wf with "Hσ seen") as %(WF & HC).
  iDestruct (hist_ctx_hist_good with "Hσ hist") as %WFC.
  iDestruct (hist_ctx_write with "Hσ hist") as "#VS".
  iDestruct (write_head_reducible with "seen Hσ hist na aw [ar]") as %?; [done..| |].
  { case_decide; [done|]. iDestruct "ar" as (rsa) "[? %]". iExists rsa. by iFrame. }
  iMod ("HClose" with "Hσ") as "Hσ".
  (* done accessing hist_ctx *)
  iModIntro. iSplit; [done|].
  iIntros (v2 σ2 efs Hstep) "!> _"; inv_head_step.
  assert (∃ 𝑚, ot = None ∧ 𝑚s = [𝑚]) as [𝑚 [? ?]].
  { inversion_clear DRFPost. by eexists. } subst ot 𝑚s.
  iDestruct ("VS" $! (mkGB 𝓢' 𝓝' M') with "[%] aw") as (C' t' [Ext1 Ext2]) "{VS} VS".
  { split; [done|]. split; last split; last split;
        [..|done|split]; [..|by inversion DRFPost|by inversion DRFPost|done].
    assert (DRF: drf_pre σ1.(na) 𝓥 σ1.(mem) (event.Write l v o)).
    { eapply (DRFPre _ _ []); eauto. constructor. by apply to_of_val. }
    by inversion DRF. }
  (* accessing hist_ctx *)
  iMod (hist_interp_open _ _ SUB with "Hσ") as "[Hσ HClose]".
  iMod ("VS" with "Hσ hist") as "(Hσ' & hist' & aw & seen')".
  iDestruct (hist_ctx_hist_good with "Hσ' hist'") as %WFC'.
  iMod ("HClose" with "Hσ'") as "$".
  (* done accessing hist_ctx *)
  iModIntro. iSplit; [done|].
  iApply "HΦ". iFrame. iSplitL; last by iPureIntro.
  case_decide; iFrame "aw".
  - iPureIntro. destruct Ext2 as (?&?&?&?&?&?&?).
    eapply write_helper_atw_local; eauto.
  - iDestruct "ar" as (?) "[? %]". iExists _. iFrame. iPureIntro.
    by eapply atr_local_mono; [..|apply Ext1|done].
Qed.

Lemma iwp_write_non_atomic l v E 𝓥 :
  ↑histN ⊆ E →
  {{{ ▷ seen 𝓥 ∗ (▷ l ↦ ?) 𝓥.(cur) }}} #l <- v at 𝓥 @ E
  {{{ 𝓥', RET #☠ at 𝓥'; ⌜𝓥 ⊑ 𝓥'⌝ ∗ seen 𝓥' ∗ (l ↦ v) 𝓥'.(cur) }}}.
Proof.
  iIntros (? Φ) "[>seen >hist] HΦ". rewrite own_loc_eq.
  iDestruct "hist" as (t ?? rsn ws GH AL ARL AWL (Vna & NAL & LeVna)) "(hist & at & aw & na)".
  iApply (iwp_write _ _ _ ∅ with "[$seen $hist $na $aw at]");
    [done|by eapply na_local_mono|done..
    |move => _; by do 2 eexists|done|iExists _;by iFrame|].
  iIntros "!>" (𝓥' C' t') "(seen' & hist' & na & [aw ar] & %F)".
  destruct F as (Ext & WF & WF' & m & -> & FRESH & Eqv & ? & ? & WH).
  iDestruct "ar" as (rsa') "(at & %)".
  iApply "HΦ". iFrame (Ext) "seen'". rewrite own_loc_na_eq.
  iExists t', m. iSplit.
  - iExists _,_,_. iFrame.
    iPureIntro; split; last split; last split; last split; [done| |done..| |].
    + exists t', m. rewrite lookup_insert Eqv. do 2 (split; [done|]).
      by eapply write_helper_seen_local.
    + eapply (atw_local_mono _ ws ws); [done|apply Ext|done].
    + eexists; split; [exact NAL|].
      clear -LeVna Ext. apply cur_mono in Ext. solve_lat.
  - rewrite Eqv. iPureIntro. split; [by constructor|by inversion WH].
Qed.

Lemma iwp_write_atomic l (v: val) C Va rs ws o E 𝓥:
  Relaxed ⊑ o → alloc_local l C 𝓥.(cur) → na_local l rs 𝓥.(cur) →
  atw_local l ws Va → ↑histN ⊆ E →
  {{{ ▷ seen 𝓥 ∗ ▷ hist l 1 C ∗ naread l 1 rs ∗ atwrite l 1 ws }}}
    Write o #l v at 𝓥 @ E
  {{{ 𝓥' C' t, RET #☠ at 𝓥'; seen 𝓥'
        ∗ hist l 1 C' ∗ naread l 1 rs
        ∗ atwrite l 1 (ws ∪ {[t]})
        ∗ ⌜𝓥 ⊑ 𝓥' ∧ good_hist C ∧ good_hist C'
            ∧ atw_local l (ws ∪ {[t]}) (Va ⊔ 𝓥'.(cur))
            ∧ ∃ m, C' = <[t:= m]> C
            ∧ C !! t = None ∧ m.(mval) = VVal v
            ∧ cell_addins t m C C'
            ∧ 𝓥.(cur) ≠ 𝓥'.(cur)
            ∧ (¬ default ∅ m.(mrel) ⊑ 𝓥.(cur))
            ∧ write_helper 𝓥 o l t ∅ m.(mrel) 𝓥'⌝ }}}.
Proof.
  iIntros (RLX ALL NA AW SUB Φ) "(>s & >hist & na & aw) Post".
  iApply (iwp_write with "[$s $hist $na $aw]");
    [done|done|by rewrite decide_True|by move => ?; subst o|
    done|by rewrite decide_True|..].
  iIntros (𝓥' C' t). rewrite !(decide_True _ _ RLX).
  iIntros "!> (s & hist & na & [aw %] & %F)". iApply "Post". iFrame.
  iPureIntro.
  destruct F as (Ext & WF & WF' & m & EqC & FRESH & Eqv & ADD & NEQ & WH).
  rewrite (decide_True _ _ RLX) in ADD.
  do 4 (split; [done|]). exists m. do 5 (split; [done|]). split; [|done].
  clear -WH RLX. intros LE.
  assert (SL:= write_helper_seen_local_write RLX WH). rewrite /seen_local in SL.
  assert (FR := write_helper_fresh WH).
  apply : (irreflexivity (⊏) (Some t)). eapply strict_transitive_r; [|exact FR].
  etrans; [exact SL|]. apply view_sqsubseteq, LE.
Qed.

Lemma cas_head_reducible σ l q C rs vr (vw: val) orf or ow 𝓥
  (ORF: Relaxed ⊑ orf) (OR: Relaxed ⊑ or) (OW: Relaxed ⊑ ow)
  (ALLOC: alloc_local l C 𝓥.(cur))
  (NA: na_local l rs 𝓥.(cur))
  (COMP: ∀ t m v, C !! t = Some m → 𝓥.(cur) !!w l ⊑ Some t →
                memval_val_rel m.(mval) v → ∃ vl, v = #vl ∧ lit_comparable vr vl) :
  seen 𝓥 -∗ hist_ctx σ -∗ hist l q C -∗ naread l 1 rs
  -∗ ⌜head_reducible (CAS #l #vr vw orf or ow at 𝓥)%E σ⌝.
Proof.
  iIntros "seen Hσ hist na".
  iDestruct (hist_ctx_hist_allocated with "Hσ hist") as %MALLOC.
  iDestruct (hist_ctx_hist_cut with "Hσ hist") as %(?&LE&ta&Eqta&EqC&?&?&?&?).
  iDestruct (hist_ctx_seen_wf with "Hσ seen") as %(WF & HC).
  iDestruct (hist_ctx_hist_good with "Hσ hist") as %GOOD.
  iDestruct (hist_ctx_naread_eq with "Hσ na") as %Eqna.
  destruct (update_head_step l #vr vw vr vw orf or ow _ _ (global_wf_mem _ WF) HC)
    as [σ2 [𝓥2 [b STEP]]]; [apply WF|exact MALLOC| | |by apply to_of_val|..];
    [done..|by rewrite Eqna| | | |].
  - specialize (LE l). apply view_sqsubseteq in LE as [LE1 LE2].
    rewrite LE1 Eqta. subst C. by eapply alloc_local_cut.
  - subst C. destruct ALLOC as (t & m & [? _]%cell_cut_lookup_Some & _).
    eexists _, _. by rewrite memory_lookup_cell.
  - move => t m Eqm LEt.
    destruct ALLOC as [ti [mi [Eqi [Eqvi SLi]]]].
    have LEta: ta ⊑ t.
    { change (Some ta ⊑ Some t). etrans; [|apply LEt]. etrans; [|apply SLi].
      subst C. by apply cell_cut_lookup_Some in Eqi as [_ ?]. }
    have CE: C !! t = Some m.
    { rewrite EqC. apply cell_cut_lookup_Some.
      split; [by rewrite -memory_lookup_cell|done]. }
    destruct m.(mval) as [| |v] eqn:Eqv.
    + destruct (COMP t m #☠ CE LEt) as [vl [[=<-] ?]]; [by rewrite Eqv; constructor|].
      eexists _. split; [|done]. econstructor.
    + exfalso. apply (good_alloc _ GOOD).
      have EqM: cell_max C = Some (t, m) by apply GOOD.
      by rewrite /cell_deallocated EqM.
    + destruct (COMP t m v CE LEt) as [vl [[=->] ?]]; [by rewrite Eqv; constructor|].
      eexists _. split; [|done]. econstructor.
  - iPureIntro. econstructor. do 3 eexists. exact STEP.
Qed.

(* FIXME : this specification is slightly weaker than the best we
   could. Only a fraction of [hist] is needed in the case [vr ≠ v']. *)
Lemma iwp_cas l vr vw orf or ow C q
  rsa rsn ws Va Vw E E' (El: loc → coPset) 𝓥 Φ
  (ORF: Relaxed ⊑ orf) (OR: Relaxed ⊑ or) (OW: Relaxed ⊑ ow)
  (ALL: alloc_local l C 𝓥.(cur))
  (ATR: atr_local l rsa Va)
  (ATW: atw_local l ws Vw)
  (NA: na_local l rsn 𝓥.(cur))
  (COMP: ∀ t m v, C !! t = Some m → 𝓥.(cur) !!w l ⊑ Some t →
                memval_val_rel m.(mval) v → ∃ vl, v = #vl ∧ lit_comparable vr vl)
  (SUB: ↑histN ⊆ E)  (SUBl: ∀ l', ↑histN ⊆ El l') :
  ▷ seen 𝓥 -∗ ▷ hist l 1 C -∗ atread l q rsa -∗ naread l 1 rsn -∗ atwrite l 1 ws -∗
  (∀ (b: bool) tr v' 𝓥' C' t',
    let t := (t'+1)%positive in
    ⌜good_hist C
        ∧ ∃ m' 𝓥x, C !! t' = Some m' ∧ m'.(mval) = VVal #v'
        ∧ 𝓥 ⊑ 𝓥x ∧ 𝓥x ⊑ 𝓥'
        ∧ atr_local l (rsa ∪ {[tr]}) (Va ⊔ 𝓥'.(cur))
        ∧ (  b = false ∧ C' = C ∧ lit_neq vr v'
             ∧ atw_local l ws (Vw ⊔ 𝓥'.(cur))
             ∧ read_helper 𝓥 orf l t' tr (default ∅ m'.(mrel)) 𝓥x
           ∨ b = true
             ∧ read_helper 𝓥 or l t' tr (default ∅ m'.(mrel)) 𝓥x
             ∧ ∃ (m: baseMessage), C' = <[t:= m]> C
             ∧ C !! t = None ∧ m.(mval) = VVal vw
             ∧ m'.(mrel) ⊏ m.(mrel)
             ∧ 𝓥.(cur) !!w l ⊏ Some t ∧ Some t ⊑ 𝓥'.(cur) !!w l
             ∧ default ∅ m'.(mrel) !!w l ⊏ Some t
             ∧ (¬ 𝓥'.(cur) ⊑ default ∅ m'.(mrel))
             ∧ cell_addins t m C C'
             ∧ (if decide (Relaxed = or) then m.(mrel) ⊑ Some 𝓥'.(acq) else True)
             ∧ (if decide (AcqRel = or) then m.(mrel) ⊑ Some 𝓥'.(cur) else True)
             ∧ atw_local l (ws ∪ {[t]}) (Vw ⊔ 𝓥'.(cur))
             ∧ write_helper 𝓥x ow l t (default ∅ m'.(mrel)) m.(mrel) 𝓥')⌝
    -∗ ( ⌜if b then v' = vr else true⌝ -∗
        seen 𝓥' -∗
        hist l 1 C' -∗ atread l q (rsa ∪ {[tr]}) -∗ naread l 1 rsn -∗
        (if b then atwrite l 1 (ws ∪ {[t]}) else atwrite l 1 ws) -∗
        ⌜good_hist C'⌝ ={E}[E']▷=∗
        Φ (mkVal #b 𝓥')))
  -∗ WP CAS #l #vr vw orf or ow at 𝓥 @ E {{ Φ }}.
Proof.
  iIntros ">seen >hist ar na aw HΦ".
  iApply wp_lift_atomic_head_step_no_fork_fupd; first auto.
  iIntros (σ1 ? κ κs ?) "Hσ".
  (* accessing hist_ctx *)
  iMod (hist_interp_open _ _ SUB with "Hσ") as "[Hσ HClose]".
  iDestruct (hist_ctx_seen_wf with "Hσ seen") as %(WF & HC).
  iDestruct (cas_head_reducible _ _ _ _ _ _ vw orf or
                with "seen Hσ hist na") as %?; [done..|].
  iDestruct (hist_ctx_read with "Hσ hist") as "#VSR".
  iDestruct (hist_ctx_cas with "Hσ hist") as "#VSC".
  iMod ("HClose" with "Hσ") as "Hσ".
  (* done accessing hist_ctx *)
  iModIntro. iSplit; [done|]. iIntros (v2 σ2 efs Hstep) "_"; inv_head_step.
  - iClear "VSC".
    assert (∃ tr, ot = Some tr ∧ 𝑚s = []) as [tr [? ?]].
    { inversion_clear DRFPost. by eexists. } subst ot 𝑚s.
    iDestruct ("VSR" $! (mkGB 𝓢' 𝓝' M') with "[%] [ar]") as "[FACTS VS] {VSR}";
      [done|by rewrite decide_True|..].
    iDestruct "FACTS" as %(Ext & ? & t & m & Eqm & Eqvo & RH & ?).
    iSpecialize ("HΦ" $! false _ _ _ C with "[%]").
    { split; [done|]. do 2 eexists. do 4 (split; [done|]). split; [|left].
      - have ATL:= read_helper_atr_local _ _ _ _ _ _ _ _ _ RH ATR.
        by rewrite decide_True in ATL.
      - repeat split; auto.
        eapply (atw_local_mono _ ws ws); [done| |apply ATW]. by solve_lat. }
    (* iDestruct "HΦ" as (P) "(P & _ & HΦ)". *)
    (* accessing hist_ctx *)
    iMod (hist_interp_open _ _ SUB with "Hσ") as "[Hσ HClose]".
    iMod ("VS" with "Hσ") as "[Hσ' [seen' ar]]". rewrite decide_True; [|done].
    iMod ("HClose" with "Hσ'") as "$".
    (* done accessing hist_ctx *)
    iMod ("HΦ" with "[%//] seen' hist ar na aw [%//]") as "HΦ".
    iIntros "!> !>". by iMod "HΦ" as "$".
  - iClear "VSR".
    assert (∃ tr 𝑚, ot = Some tr ∧ 𝑚s = [𝑚]) as [tr [𝑚 [? ?]]].
    { inversion_clear DRFPost. by do 2 eexists. } subst ot 𝑚s.
    iDestruct ("VSC" $! (mkGB 𝓢' 𝓝' M') with "[%] ar aw") as (C') "[FACTS VS] {VSC}".
    { split; [done|]. split; last split; last split;
        [..|done|done|split]; [..|by inversion DRFPost|done].
      eapply (DRFPre _ _ []); eauto. eapply CasSucS; eauto. by apply to_of_val. }
    iDestruct "FACTS" as
      %(GH&t'&m'&𝓥x&Eqm&?&?&Extx&RH&m&?&EQT&?&?&?&?&?&?&?&?&RLX&ACQ&WH).
    have ?: atw_local l (ws ∪ {[𝑚.(mto)]}) (Vw ⊔ 𝓥'.(cur)).
    { by eapply write_helper_atw_local; eauto. }
    iSpecialize ("HΦ" with "[%]").
    { split; [done|]. do 2 eexists. do 4 (split; [done|]). split; [|right].
      - have ATL:= read_helper_atr_local _ _ _ _ _ _ _ _ _ RH ATR.
        rewrite decide_True in ATL; [|done].
        eapply atr_local_mono; [done|..|apply ATL]. by rewrite Extx.
      - do 2 (split; [done|]). rewrite -EQT. by eexists. }
    (* iDestruct "HΦ" as (P) "(P & HP & HΦ)". *)
    match goal with
    | H : lit_eq _ _ _ |- _ => inversion H; clear H
    end.
    + (* accessing hist_ctx *)
      iMod (hist_interp_open _ _ SUB with "Hσ") as "[Hσ HClose]".
      iMod ("VS" with "Hσ hist") as "(Hσ' & hist' & at' & aw' & seen')".
      iDestruct (hist_ctx_hist_good with "Hσ' hist'") as %WFC'.
      iMod ("HClose" with "Hσ'") as "$". rewrite EQT.
      (* done accessing hist_ctx *)
      iMod ("HΦ" with "[%//] seen' hist' at' na aw' [%//]") as "HΦ".
      iIntros "!> !>". by iMod "HΦ" as "$".
    + (* accessing hist_ctx *)
      iMod (hist_interp_open _ _ SUB with "Hσ") as "[Hσ HClose]".
      iMod ("VS" with "Hσ hist") as "(Hσ' & hist' & at' & aw' & seen')".
      iDestruct (hist_ctx_hist_good with "Hσ' hist'") as %WFC'.
      iMod ("HClose" with "Hσ'") as "$". rewrite EQT.
      (* done accessing hist_ctx *)
      iMod ("HΦ" with "[%//] seen' hist' at' na aw' [%//]") as "HΦ".
      iIntros "!> !>". by iMod "HΦ" as "$".
Qed.

Lemma iwp_acq_fence E 𝓥 (SUB: ↑histN ⊆ E) :
  {{{ ▷ seen 𝓥 }}}
    FenceAcq at 𝓥 @ E
  {{{ 𝓥', RET #☠ at 𝓥'; seen 𝓥' ∗ ⌜𝓥 ⊑ 𝓥' ∧ 𝓥'.(cur) = 𝓥'.(acq)⌝ }}}.
Proof.
  iIntros (Φ) ">seen HΦ". iApply wp_lift_atomic_head_step_no_fork; auto.
  iIntros (σ1 ? κ κs ?) "Hσ !>". iSplit.
  - iPureIntro. destruct (acq_fence_head_step σ1 𝓥) as [σ2 [𝓥2 STEP]].
    econstructor. do 3 eexists. exact STEP.
  - iNext. iIntros (v2 σ2 efs Hstep) "_"; inv_head_step.
    (* accessing hist_ctx *)
    iMod (hist_interp_open _ _ SUB with "Hσ") as "[Hσ HClose]".
    iDestruct (hist_ctx_seen_wf with "Hσ seen") as %(WF & HC).
    assert (ot = None ∧ 𝑚s = [] ∧ 𝓝' = σ1.(na)) as [?[??]].
    { by inversion DRFPost. } subst ot 𝑚s 𝓝'.
    assert (M' = σ1.(mem)). { by inversion PStep. } subst M'.
    assert (𝓢' = σ1.(sc)). { by inversion PStep. } subst 𝓢'.
    iMod (hist_ctx_acq_fence _ _ _ PStep HC with "Hσ") as "(Hσ & ? & ?)".
    rewrite (_: (mkGB σ1.(sc) σ1.(na) σ1.(mem)) = σ1); [|by destruct σ1].
    iMod ("HClose" with "Hσ") as "$".
    (* done accessing hist_ctx *)
    iModIntro; iSplit; [done|]. iApply "HΦ". by iFrame.
Qed.

Lemma iwp_rel_fence E 𝓥 (SUB: ↑histN ⊆ E) :
  {{{ ▷ seen 𝓥 }}}
    FenceRel at 𝓥 @ E
  {{{ 𝓥', RET #☠ at 𝓥'; seen 𝓥' ∗ ⌜𝓥 ⊑ 𝓥' ∧ 𝓥'.(frel) = 𝓥'.(cur)⌝}}}.
Proof.
  iIntros (Φ) "seen HΦ". iApply wp_lift_atomic_head_step_no_fork; auto.
  iIntros (σ1 ? κ κs ?) "Hσ !>". iSplit.
  - iPureIntro. destruct (rel_fence_head_step σ1 𝓥) as [σ2 [𝓥2 STEP]].
    econstructor. do 3 eexists. exact STEP.
  - iNext. iIntros (v2 σ2 efs Hstep) "_"; inv_head_step.
    (* accessing hist_ctx *)
    iMod (hist_interp_open _ _ SUB with "Hσ") as "[Hσ HClose]".
    iDestruct (hist_ctx_seen_wf with "Hσ seen") as %(WF & HC).
    assert (ot = None ∧ 𝑚s = [] ∧ 𝓝' = σ1.(na)) as [?[??]].
    { by inversion DRFPost. } subst ot 𝑚s 𝓝'.
    assert (M' = σ1.(mem)). { by inversion PStep. } subst M'.
    assert (𝓢' = σ1.(sc)). { by inversion PStep. } subst 𝓢'.
    iMod (hist_ctx_rel_fence _ _ _ PStep HC with "Hσ") as "(Hσ & ? & ?)".
    rewrite (_: (mkGB σ1.(sc) σ1.(na) σ1.(mem)) = σ1); [|by destruct σ1].
    iMod ("HClose" with "Hσ") as "$".
    iModIntro; iSplit; [done|]. iApply "HΦ". by iFrame.
Qed.

Lemma iwp_sc_fence E 𝓥 𝓢 (SUB: ↑histN ⊆ E) :
  {{{ ▷ seen 𝓥 ∗ ▷ sc_view 𝓢 }}}
    FenceSC at 𝓥 @ E
  {{{ 𝓢' 𝓥', RET #☠ at 𝓥';
    seen 𝓥' ∗ sc_view 𝓢' ∗ ⌜𝓥 ⊑ 𝓥' ∧ ∃ 𝓢0, 𝓢 ⊑ 𝓢0 ∧ sc_fence_helper 𝓥 𝓢0 𝓥' 𝓢'⌝}}}.
Proof.
  iIntros (Φ) "[>seen >SC] HΦ". iApply wp_lift_atomic_head_step_no_fork; auto.
  iIntros (σ1 ? κ κs ?) "Hσ !>". iSplit.
  - iPureIntro. destruct (sc_fence_head_step σ1 𝓥) as [σ2 [𝓥2 STEP]].
    econstructor. do 3 eexists. exact STEP.
  - iNext. iIntros (v2 σ2 efs Hstep) "_"; inv_head_step.
    (* accessing hist_ctx *)
    iMod (hist_interp_open _ _ SUB with "Hσ") as "[Hσ HClose]".
    iDestruct (hist_ctx_seen_wf with "Hσ seen") as %(WF & HC).
    assert (ot = None ∧ 𝑚s = [] ∧ 𝓝' = σ1.(na)) as [?[??]].
    { by inversion DRFPost. } subst ot 𝑚s 𝓝'.
    assert (M' = σ1.(mem)). { by inversion PStep. } subst M'.
    iDestruct (hist_ctx_sc_view_included with "Hσ SC") as %?.
    iMod (hist_ctx_sc_fence _ (mkGB 𝓢' σ1.(na) σ1.(mem)) _ _ _ PStep HC with "[$Hσ $SC]")
      as "(Hσ&?&?&%&_)"; [done|].
    iMod ("HClose" with "Hσ") as "$".
    (* done accessing hist_ctx *)
    iModIntro; iSplit; [done|].
    iApply "HΦ". iFrame. iPureIntro. split; [done|]. eexists. split; [done|].
    inversion PStep. inversion FSC. simpl in *. by subst.
Qed.

Lemma iwp_sc_fence' E 𝓥 (SUB: ↑histN ⊆ E) :
  {{{ ▷ seen 𝓥 }}}
    FenceSC at 𝓥 @ E
  {{{ 𝓢' 𝓥', RET #☠ at 𝓥';
    seen 𝓥' ∗ sc_view 𝓢' ∗ ⌜𝓥 ⊑ 𝓥' ∧ ∃ 𝓢0, sc_fence_helper 𝓥 𝓢0 𝓥' 𝓢'⌝}}}.
Proof.
  iIntros (Φ) "seen HΦ". iApply wp_lift_atomic_head_step_no_fork; auto.
  iIntros (σ1 ? κ κs n) "Hσ !>". iSplit.
  - iPureIntro. destruct (sc_fence_head_step σ1 𝓥) as [σ2 [𝓥2 STEP]].
    econstructor. do 3 eexists. exact STEP.
  - iNext. iIntros (v2 σ2 efs Hstep) "_"; inv_head_step.
    (* accessing hist_ctx *)
    iMod (hist_interp_open _ _ SUB with "Hσ") as "[Hσ HClose]".
    iDestruct (hist_ctx_seen_wf with "Hσ seen") as %(WF & HC).
    assert (ot = None ∧ 𝑚s = [] ∧ 𝓝' = σ1.(na)) as [?[??]].
    { by inversion DRFPost. } subst ot 𝑚s 𝓝'.
    assert (M' = σ1.(mem)). { by inversion PStep. } subst M'.
    iMod (hist_ctx_sc_fence' _ (mkGB 𝓢' σ1.(na) σ1.(mem)) _ _ PStep HC with "Hσ")
      as "(Hσ&?&?&%)"; [done|].
    iMod ("HClose" with "Hσ") as "$".
    (* done accessing hist_ctx *)
    iModIntro; iSplit; [done|].
    iApply "HΦ". iFrame. iPureIntro. split; [done|]. eexists.
    inversion PStep. inversion FSC. simpl in *. by subst.
Qed.

(* TODO: add syscall to the language *)

End base_lifting.
