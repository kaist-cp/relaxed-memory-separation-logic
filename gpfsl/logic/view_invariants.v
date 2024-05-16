From iris.algebra Require Import lib.frac_auth.
From iris.proofmode Require Import proofmode monpred.
From iris.bi Require Import fractional monpred.

From gpfsl.algebra Require Import lattice_cmra.
From gpfsl.base_logic Require Import frame_instances.
From gpfsl.logic Require Export invariants.

Require Import iris.prelude.options.

Class view_invG Σ := {
  view_inv_inG : inG Σ (frac_authR (latR view_Lat))
}.
Local Existing Instance view_inv_inG.

Definition view_invΣ : gFunctors :=
  #[ GFunctor (constRF (frac_authR (latR view_Lat))) ].

Global Instance subG_view_invG Σ : subG (view_invΣ) Σ → view_invG Σ.
Proof. solve_inG. Qed.

Definition view_inv_pool_name := gname.

Section defs.
Context `{invGS Σ, view_invG Σ}.
#[local] Notation vProp := (vProp Σ).

Implicit Types (γ : view_inv_pool_name) (q : frac) (N : namespace) (P : vProp).

Definition view_tok_def γ q : vProp :=
  (∃ V, ⊒V ∧ ⎡ own γ (◯F{q} (to_latT V)) ⎤)%I.
Definition view_tok_aux : seal (@view_tok_def). Proof. by eexists. Qed.
Definition view_tok := unseal (@view_tok_aux).
Definition view_tok_eq : @view_tok = _ := seal_eq _.

Definition view_inv_def γ N P : vProp :=
  inv N (∃ V, @{V}(view_tok γ 1 ∨ ⎡ own γ (●F (to_latT V)) ⎤ ∗ P))%I.
Definition view_inv_aux : seal (@view_inv_def). Proof. by eexists. Qed.
Definition view_inv := unseal (@view_inv_aux).
Definition view_inv_eq : @view_inv = _ := seal_eq _.
End defs.

#[global] Instance: Params (@view_inv) 5 := {}.
#[global] Typeclasses Opaque view_tok view_inv.

Section view_inv_props.
Context `{invGS Σ, view_invG Σ}.
#[local] Notation vProp := (vProp Σ).

#[global] Instance view_tok_timeless γ q : Timeless (view_tok γ q).
Proof. rewrite view_tok_eq. apply _. Qed.

#[global] Instance view_inv_contractive γ N : Contractive (view_inv γ N).
Proof. rewrite view_inv_eq. solve_contractive. Qed.
#[global] Instance view_inv_ne γ N : NonExpansive (view_inv γ N).
Proof. rewrite view_inv_eq. solve_proper. Qed.
#[global] Instance view_inv_proper γ N : Proper ((≡) ==> (≡)) (view_inv γ N).
Proof. apply (ne_proper _). Qed.

#[global] Instance view_inv_persistent γ N P : Persistent (view_inv γ N P).
Proof. rewrite view_inv_eq; apply _. Qed.

#[global] Instance view_tok_fractional γ : Fractional (view_tok γ).
Proof.
  rewrite /Fractional view_tok_eq =>p q. iSplit.
  - iDestruct 1 as (V1) "[#In [Hp Hq]]". iSplitL "Hp"; iExists V1; by iFrame.
  - iDestruct 1 as "[Hp Hq]".
    iDestruct "Hp" as (V1) "[In1 Hp]". iDestruct "Hq" as (V2) "[In2 Hq]".
    iCombine "Hp Hq" as "H". rewrite lat_op_join'.
    iExists _. iFrame. rewrite -monPred_in_view_op. by iFrame.
Qed.

#[global] Instance view_tok_asfractional γ q :
  AsFractional (view_tok γ q) (view_tok γ) q.
Proof. split; [done|apply _]. Qed.

#[global] Instance frame_view_tok p γ q1 q2 RES :
  FrameFractionalHyps p (view_tok γ q1) (view_tok γ) RES q1 q2 →
  Frame p (view_tok γ q1) (view_tok γ q2) RES | 5.
Proof. apply: frame_fractional. Qed.

Lemma view_tok_valid γ q : view_tok γ q -∗ ⌜ ✓ q ⌝.
Proof.
  rewrite view_tok_eq. iDestruct 1 as (V) "[_ own]".
  by iDestruct (own_valid with "own") as %[? ?]%frac_auth_frag_valid.
Qed.

Lemma view_tok_split_unit γ q q' :
  view_tok γ (q + q') -∗ view_tok γ q ∗ <obj> view_tok γ q'.
Proof.
  rewrite view_tok_eq.
  iDestruct 1 as (V) "[? own]".
  rewrite -{2}(lat_join_bottom_rightid_L V) -lat_op_join' frac_auth_frag_op.
  iDestruct "own" as "[own1 own2]".
  iSplitR "own2".
  - iExists _. by iFrame.
  - iExists ∅. iIntros "!>". iFrame. by iApply monPred_in_bot.
Qed.

Lemma view_inv_alloc_frac N E (q q': frac) (Eq: (q + q' = 1)%Qp):
  ⊢ |={E}=> ∃ γ, view_tok γ q ∗
    ∀ (P: vProp), ▷ P ={E}=∗ view_inv γ N P ∧ view_tok γ q'.
Proof.
  iDestruct (view_at_intro True%I with "[//]") as (V) "[InV _]".
  iMod (own_alloc (●F (to_latT V) ⋅ ◯F (to_latT V)))
    as (γ) "[oA oN]"; [by apply frac_auth_valid|].
  rewrite -{1}Eq. iDestruct "oN" as "[oN oN']".
  iExists γ. rewrite view_tok_eq. iSplitL "oN".
  { iExists V. by iFrame. }
  iIntros "!>" (P) "P".
  iDestruct (view_at_intro_incl with "P InV") as (V') "(#InV' & % & P)".
  set V0 := V ⊔ V'.
  iMod (own_update_2 _ _ _ (●F (to_latT V0) ⋅ ◯F{q'} (to_latT V0))
         with "oA oN'") as "[oA tok]".
  { apply frac_auth_update, latT_local_update. }
  iSplitR "tok".
  - rewrite view_inv_eq. iApply inv_alloc.
    iExists V0. iNext. iRight. by iFrame.
  - iExists V0. rewrite -monPred_in_view_op. by iFrame "#∗".
Qed.

Lemma view_inv_alloc_half N E :
  ⊢ |={E}=> ∃ γ, view_tok γ (1/2) ∗
    ∀ (P: vProp), ▷ P ={E}=∗ view_inv γ N P ∧ view_tok γ (1/2).
Proof. apply view_inv_alloc_frac. by rewrite Qp.div_2. Qed.

Lemma view_inv_alloc N E :
  ⊢ |={E}=> ∃ γ, ∀ (P: vProp), ▷ P ={E}=∗ view_inv γ N P ∧ view_tok γ 1%Qp.
Proof.
  iMod view_inv_alloc_half as (γ) "[tok Inv]".
  iExists γ. iIntros "!>" (P) "P". iFrame "tok". by iApply ("Inv" with "P").
Qed.

Lemma view_inv_alloc_open N E :
  ↑N ⊆ E →
  ⊢ |={E}=> ∃ γ, ∀ P, |={E,E ∖ ↑N}=> view_inv γ N P
                                      ∧ (▷ P ={E ∖ ↑N,E}=∗ view_tok γ 1%Qp).
Proof.
  intros.
  iDestruct (view_at_intro True%I with "[//]") as (V) "[InV _]".
  iMod (own_alloc (●F (to_latT V) ⋅ ◯F (to_latT V)))
    as (γ) "[oA oN]"; [by apply frac_auth_valid|].
  iExists γ. iIntros "!>" (P). rewrite view_inv_eq.
  iMod (inv_alloc_open N E) as "[$ Closed]"; [done|].
  iIntros "!> P".
  iDestruct (view_at_intro_incl with "P InV") as (V1) "(InV1 & % & P)".
  set V' := V ⊔ V1.
  iMod (own_update_2 _ _ _ (●F (to_latT V') ⋅ ◯F (to_latT V')) with "oA oN")
    as "[oA tok]"; [by apply frac_auth_update_1|].
  iMod ("Closed" with "[oA P]").
  + iExists V'. iRight. iNext. by iFrame.
  + iModIntro. rewrite view_tok_eq. iExists V'.
    rewrite -monPred_in_view_op. by iFrame "#∗".
Qed.

Lemma view_inv_dealloc γ N (P: vProp) E :
  ↑N ⊆ E → view_inv γ N P ∧ view_tok γ 1%Qp ={E}=∗ ▷ P.
Proof.
  iIntros (SUB) "[#Inv tok]".
  rewrite view_inv_eq view_tok_eq /view_inv_def.
  iDestruct "tok" as (V1) "[#InV1 tok]".
  iMod (inv_acc with "Inv") as "[VI Closed]"; [done|].
  iDestruct "VI" as (V') "[>tok'|[>oA P]]".
  { rewrite view_tok_eq. iDestruct "tok'" as (V2) "[_ tok']".
    rewrite view_at_embed.
    by iCombine "tok tok'" gives %[? _]%frac_auth_frag_valid. }
  iDestruct (own_valid_2 with "[$oA] tok")
    as %->%frac_auth_agree%to_latT_inj%leibniz_equiv_iff.
  iMod ("Closed" with "[tok]").
  - iExists V1. iLeft. rewrite view_tok_eq. iNext. iExists V1. by iFrame "tok".
  - iIntros "!> !>". iApply (view_at_elim with "InV1 P").
Qed.

Lemma view_inv_acc_base_slow' γ N P E :
  ↑N ⊆ E → view_inv γ N P ={E,E∖↑N}=∗
    ∀ Vb q,
    (⊔{Vb} view_tok γ q) ={∅}=∗
    (⊔{Vb} view_tok γ q) ∗
    ∃ V (R: vProp), (⊔{V} ▷ P) ∗ R ∗
    (□ (view_tok γ 1%Qp -∗ R -∗ ⊒V)) ∗
    (R -∗
      (⊔{Vb} view_tok γ q -∗ ⊔{V} ▷ P ={∅}=∗
        ⊔{Vb} view_tok γ q ∗ |={E∖↑N,E}=> True) ∧
      (∀ V' (Q: vProp), @{V'} view_tok γ q -∗
            (@{V'} view_tok γ q ={E∖↑N}=∗ @{V'} (⊔{V} ▷ P) ∗ Q) ={E∖↑N,E}=∗ Q) ∧
      (view_tok γ 1%Qp -∗ ⊒V ∧ |={E∖↑N,E}=> True)).
Proof.
  iIntros (SUB) "#Inv". rewrite view_inv_eq view_tok_eq.
  iMod (inv_acc with "Inv") as "[VI Closed]"; [done|].
  iIntros "!>" (Vb q). iDestruct 1 as (V1) "[#In1 tok]".
  iDestruct "VI" as (V') "[>tok'|[>oA P]]".
  { rewrite view_tok_eq. rewrite {1}/view_tok_def. iDestruct "tok'" as (V2) "[? tok']".
    iDestruct (own_valid_2 with "[$tok'] [$tok]")
      as %[[]%Qp.not_add_le_l _]%frac_auth_frag_op_valid. }
  iModIntro. iSplitL "tok". { iExists V1. by iFrame "#∗". }
  iExists V', ⎡ own γ (●F (to_latT V')) ⎤%I.
  iSplitL "P". { rewrite view_join_later. by iFrame. }
  iFrame "oA". iSplitL "".
  { iIntros "!>". iDestruct 1 as (V3) "[In3 tok]". iIntros "oA".
    iCombine "oA tok"
      gives %->%frac_auth_agree%to_latT_inj%leibniz_equiv_iff.
    by iFrame. }
  iIntros "oA". iSplit; last iSplit.
  - iDestruct 1 as (V3) "[#In3 tok]". iIntros "P".
    rewrite (view_join_mono_view (▷ P)%I (▷ P)%I _ (Vb ⊔ V')); [|solve_lat|eauto].
    rewrite -view_join_op. iCombine "P In3" as "PI".
    iDestruct (view_join_mono_I _ _  with "[] PI") as "P".
    { iIntros "[P I]". by iApply (view_join_elim' with "P I"). }
    iDestruct "P" as (V4) "(In4 & % & P)".
    rewrite view_join_embed.
    iMod (own_update_2 _ _ _ (●F (to_latT (V' ⊔ V4)) ⋅ ◯F{q} (to_latT (V3 ⊔ V4)))
           with "oA tok") as "[oA tok]".
    { apply frac_auth_update, latT_local_update. }
    iModIntro. iSplitL "tok In4".
    + iExists V4. rewrite lat_le_join_r_L //. iSplit; by iFrame.
    + iMod ("Closed" with "[oA P]"); [|done].
      iExists _. iNext. iRight. rewrite view_join_view_at. by iFrame.
  - iIntros (V3 Q). iDestruct 1 as (V3') "[% tok]". iIntros "P".
    rewrite view_at_embed.
    iMod (own_update_2 _ _ _ (●F (to_latT (V' ⊔ V3)) ⋅ ◯F{q} (to_latT (V3' ⊔ V3)))
           with "oA tok") as "[oA tok]".
    { apply frac_auth_update, latT_local_update. }
    iMod ("P" with "[tok]") as "[P $]".
    { iExists _. iFrame "tok". iPureIntro. solve_lat. }
    iMod ("Closed" with "[oA P]"); last done.
    iExists (V' ⊔ V3). iRight. rewrite view_at_view_join.
    iNext. by iFrame.
  - iDestruct 1 as (V3) "[#In3 tok]". iSplit.
    + iCombine "oA tok"
        gives %->%frac_auth_agree%to_latT_inj%leibniz_equiv_iff.
      by iFrame.
    + iMod ("Closed" with "[tok]"); [|done].
      iExists V3. iLeft. rewrite view_tok_eq. iExists V3. by iFrame "tok".
Qed.

Lemma view_inv_acc_base_1' γ N P E :
  ↑N ⊆ E → view_inv γ N P ={E,E∖↑N}=∗
    ∀ Vb q,
    (⊔{Vb} view_tok γ q) ={∅}=∗
    (⊔{Vb} view_tok γ q) ∗ ∃ V, (⊔{V} ▷ P) ∗
    (((⊔{Vb} view_tok γ q) -∗
      (⊔{V} ▷ P) ={∅}=∗
      (⊔{Vb} view_tok γ q) ∗ |={E∖↑N,E}=> True) ∧
    (∀ V' (Q: vProp), @{V'} view_tok γ q -∗
          (@{V'} view_tok γ q ={E∖↑N}=∗ @{V'} (⊔{V} ▷ P) ∗ Q)
          ={E∖↑N,E}=∗ Q) ∧
    (view_tok γ 1%Qp -∗ ⊒V ∧ |={E∖↑N,E}=> True)).
Proof.
  iIntros (?) "#Inv".
  iMod (view_inv_acc_base_slow' with "Inv") as "VI"; [done|].
  iIntros "!>" (Vb q) "I". iMod ("VI" with "I") as "[$ VI]".
  iDestruct "VI" as (V R) "(I & R & IR & VI)".
  iModIntro. iExists V. iFrame "I". iApply ("VI" with "R").
Qed.

Lemma view_inv_acc_base_2' γ N P q E :
  ↑N ⊆ E → view_inv γ N P ∧ view_tok γ q ={E,E∖↑N}=∗
    view_tok γ q ∗ ∃ V (R: vProp), (⊔{V} ▷ P) ∗ R ∗
    (□ (view_tok γ 1%Qp -∗ R -∗ ⊒V)) ∗
    (R -∗
    ((view_tok γ q -∗ (⊔{V} ▷ P) ={E∖↑N,E}=∗ view_tok γ q) ∧
    (∀ V' (Q: vProp),
        @{V'} view_tok γ q -∗
          (@{V'} view_tok γ q ={E∖↑N}=∗ @{V'} (⊔{V} ▷ P) ∗ Q)
          ={E∖↑N,E}=∗ Q) ∧
    (view_tok γ 1%Qp -∗ ⊒V ∧ |={E∖↑N,E}=> True))).
Proof.
  iIntros (?) "[#Inv tok]".
  iDestruct (view_at_intro with "tok") as (Vb) "[#In tok]".
  iMod (view_inv_acc_base_slow' with "Inv") as "VS"; [done|].
  iSpecialize ("VS" $! Vb with "[$tok //]"). (* TODO better frame instance? *)
  iMod (fupd_mask_mono with "VS") as "[tok VS]"; [set_solver|].
  iDestruct (view_join_elim with "tok In") as "$".
  iDestruct "VS" as (V R) "(P & R & IR & Closed)". iExists V, R; iFrame "P R IR".
  iIntros "!> R". iSpecialize ("Closed" with "R").
  iSplit; last iSplit.
  - rewrite bi.and_elim_l. iIntros "tok P".
    iSpecialize ("Closed" with "[$tok //] P").
    iMod (fupd_mask_mono with "Closed") as "[tok >_]"; [set_solver|].
    by iDestruct (view_join_elim with "tok In") as "$".
  - by rewrite bi.and_elim_r bi.and_elim_l.
  - by rewrite bi.and_elim_r bi.and_elim_r.
Qed.

Lemma view_inv_acc_base' γ N P q E :
  ↑N ⊆ E → view_inv γ N P ∧ view_tok γ q ={E,E∖↑N}=∗
    view_tok γ q ∗ ∃ V, (⊔{V} ▷ P) ∗
    ((view_tok γ q -∗ (⊔{V} ▷ P) ={E∖↑N,E}=∗ view_tok γ q) ∧
    (∀ V' (Q: vProp),
        @{V'} view_tok γ q -∗
          (@{V'} view_tok γ q ={E∖↑N}=∗ @{V'} (⊔{V} ▷ P) ∗ Q)
          ={E∖↑N,E}=∗ Q) ∧
    (view_tok γ 1%Qp -∗ ⊒V ∧ |={E∖↑N,E}=> True)).
Proof.
  iIntros (?) "[#Inv tok]".
  iDestruct (view_at_intro with "tok") as (Vb) "[#In tok]".
  iMod (view_inv_acc_base_1' with "Inv") as "VS"; [done|].
  iSpecialize ("VS" $! Vb with "[$tok //]").
  iMod (fupd_mask_mono with "VS") as "[tok VS]"; [set_solver|].
  iDestruct (view_join_elim with "tok In") as "$".
  iDestruct "VS" as (V) "[P Closed]". iExists V; iFrame "P". iModIntro.
  iSplit; last iSplit.
  - rewrite bi.and_elim_l. iIntros "tok P".
    iSpecialize ("Closed" with "[$tok//] P").
    iMod (fupd_mask_mono with "Closed") as "[tok >_]"; [set_solver|].
    by iDestruct (view_join_elim with "tok In") as "$".
  - by rewrite bi.and_elim_r bi.and_elim_l.
  - by rewrite bi.and_elim_r bi.and_elim_r.
Qed.

Lemma view_inv_acc_consume' γ N P q E :
  ↑N ⊆ E → view_inv γ N P ∧ view_tok γ q ={E,E∖↑N}=∗
    ∃ V, (⊔{V} ▷ P) ∗ ((⊔{V} ▷ P) ={E∖↑N,E}=∗ view_tok γ q).
Proof.
  iIntros (?) "VI".
  iMod (view_inv_acc_base' with "VI") as "[tok VI]"; [done|].
  iDestruct "VI" as (V) "[P Closed]". iExists V. iFrame "P".
  rewrite bi.and_elim_l. iIntros "!> P".
  iApply ("Closed" with "tok P").
Qed.

(* With a (⊒Vb → view_tok γ q), get
  - (⊒Vb → view_tok γ q) back
  - ∃ V, (⊒V → ▷ P) the invariant content
  - A closing-viewshift with 3 choices
    + give back the token (⊒Vb → view_tok γ q) and the content (⊒V → ▷ P), and
      receive a closing viewshift to close the invariant later
    + give back a @{V'} view_tok γ q, and
      then the invariant content and Q conditional on @{V'} view_tok γ q,
      and receive a closing viewshift that returns Q
    + do not give back the invariant content, instead give back the full token
      to cancel the invariant *)
Lemma view_inv_acc_base_1 γ N P E :
  ↑N ⊆ E → view_inv γ N P ={E,E∖↑N}=∗
    ∀ Vb q,
    (⊒Vb → view_tok γ q) ={∅}=∗
    (⊒Vb → view_tok γ q) ∗ ∃ V, (⊒V → ▷ P) ∗
    (((⊒Vb → view_tok γ q) -∗
      (⊒V → ▷ P) ={∅}=∗
      (⊒Vb → view_tok γ q) ∗ |={E∖↑N,E}=> True) ∧
    (∀ V' (Q: vProp), ⎡ view_tok γ q V' ⎤ -∗
          (⎡ view_tok γ q V' ⎤ ={E∖↑N}=∗ ⎡ (⊒V → ▷ P) V' ⎤ ∗ Q)
          ={E∖↑N,E}=∗ Q) ∧
    (view_tok γ 1%Qp -∗ ⊒V ∧ |={E∖↑N,E}=> True)).
Proof.
  setoid_rewrite <-view_join_unfold.
  move : view_inv_acc_base_1'. rewrite view_at_eq. eauto.
Qed.

Lemma view_inv_acc_base_2 γ N P q E :
  ↑N ⊆ E → view_inv γ N P ∧ view_tok γ q ={E,E∖↑N}=∗
    view_tok γ q ∗ ∃ V (R: vProp), (⊒V → ▷ P) ∗ R ∗
    (□ (view_tok γ 1%Qp -∗ R -∗ ⊒V)) ∗
    (R -∗
    ((view_tok γ q -∗ (⊒V → ▷ P) ={E∖↑N,E}=∗ view_tok γ q) ∧
    (∀ V' (Q: vProp),
        ⎡ view_tok γ q V' ⎤ -∗
          (⎡ view_tok γ q V' ⎤ ={E∖↑N}=∗ ⎡ (⊒V → ▷ P) V' ⎤ ∗ Q)
          ={E∖↑N,E}=∗ Q) ∧
    (view_tok γ 1%Qp -∗ ⊒V ∧ |={E∖↑N,E}=> True))).
Proof.
  setoid_rewrite <-view_join_unfold.
  move : view_inv_acc_base_2'. rewrite view_at_eq. eauto.
Qed.

Lemma view_inv_acc_base γ N P q E :
  ↑N ⊆ E → view_inv γ N P ∧ view_tok γ q ={E,E∖↑N}=∗
    view_tok γ q ∗ ∃ V, (⊒V → ▷ P) ∗
    ((view_tok γ q -∗ (⊒V → ▷ P) ={E∖↑N,E}=∗ view_tok γ q) ∧
    (∀ V' (Q: vProp),
        ⎡ view_tok γ q V' ⎤ -∗
          (⎡ view_tok γ q V' ⎤ ={E∖↑N}=∗ ⎡ (⊒V → ▷ P) V' ⎤ ∗ Q)
          ={E∖↑N,E}=∗ Q) ∧
    (view_tok γ 1%Qp -∗ ⊒V ∧ |={E∖↑N,E}=> True)).
Proof.
  setoid_rewrite <-view_join_unfold.
  move : view_inv_acc_base'. rewrite view_at_eq. eauto.
Qed.

Lemma view_inv_acc_consume γ N P q E :
  ↑N ⊆ E → view_inv γ N P ∧ view_tok γ q ={E,E∖↑N}=∗
    ∃ V, (⊒V → ▷ P) ∗ ((⊒V → ▷ P) ={E∖↑N,E}=∗ view_tok γ q).
Proof. setoid_rewrite <-view_join_unfold. by apply view_inv_acc_consume'. Qed.
End view_inv_props.

(* TODO: more proofmode instance *)
Section proofmode.
Context `{invGS Σ, view_invG Σ}.
#[local] Notation vProp := (vProp Σ).

Implicit Types (γ : view_inv_pool_name) (p : frac) (N : namespace) (P : vProp).

#[global] Instance into_inv_view_inv γ P N : IntoInv (view_inv γ N P) N := {}.

#[global] Instance into_acc_view_inv E N γ P p :
    IntoAcc (X:=view) (view_inv γ N P)
            (↑N ⊆ E) (view_tok γ p) (fupd E (E∖↑N)) (fupd (E∖↑N) E)
            (λ Vb, (⊔{Vb} ▷ P))%I (λ Vb, (⊔{Vb} ▷ P))%I
            (λ _, Some (view_tok γ p))%I.
Proof.
  rewrite /IntoAcc /accessor. iIntros (SUB) "#Hinv Hown".
  iMod (view_inv_acc_consume' with "[$Hinv $Hown]") as (Vb) "[P Close]";
    first done.
  iIntros "!>". iExists Vb. by iFrame.
Qed.
End proofmode.
