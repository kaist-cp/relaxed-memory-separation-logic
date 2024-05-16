From gpfsl.examples Require Import sflib.

From iris.algebra Require Import auth gset gmap agree.
From iris.algebra Require Import lib.mono_list.
From iris.proofmode Require Import tactics.
From iris.bi Require Import fractional.

From gpfsl.base_logic Require Import meta_data.
From gpfsl.examples.algebra Require Import mono_list mono_list_list.
From gpfsl.logic Require Import logatom atomics invariants.

From gpfsl.logic Require Import repeat_loop new_delete.
From gpfsl.examples Require Import map_seq loc_helper.

From stdpp Require Import namespaces.
From gpfsl.logic Require Import logatom.
From gpfsl.examples.omo Require Import omo omo_event omo_history omo_preds.

From diaframe Require Import proofmode_base.

Require Import iris.prelude.options.

Definition gen_id := Qp.

Section omo_pred_diaframe.
Context {Σ : gFunctors} `{!omoGeneralG Σ} `{!omoSpecificG Σ eventT absStateT}.

Notation iProp := (iProp Σ).
Notation vProp := (vProp Σ).

Implicit Types
  (γe γs γtl γel γh γg γwl γrl γgl γsl γq γb γm γn γx : gname)
  (q qg : Qp)
  (M : eView)
  (einfo : (gname * option gname * view * eView * Qp * gname))
  (EL : list (gname * option gname * view * eView * Qp * gname)) (* mono_list for all event info excluding event type *)
  (WL : list (event_id * gname * Qp)) (* mono_list for γs *)
  (RL : list event_id) (* mono_list for each generation *)
  (GL : list (gname * event_id)) (* mono_list for commit-with relation or seen_event *)
  (QM : gmap Qp nat)
  (eidx : event_idx).

(* gid: generation id (unique for each generation) *)
Definition OmoGid_def (γe : gname) (e : event_id) (gid : gen_id) : vProp :=
  ∃ γtl γel γh γg γn einfo,
    ⌜ γe = encode (γtl,γel,γh,γg,γn) ∧ gid = einfo.1.2 ⌝ ∗

    ⎡mono_list_idx_own γel e einfo⎤.
Definition OmoGid_aux : seal (@OmoGid_def). Proof. by eexists. Qed.
Definition OmoGid := unseal (@OmoGid_aux).
Definition OmoGid_eq : @OmoGid = _ := seal_eq _.

(* joy *)
Definition OmoGidState_def (γe γs : gname) (gid : gen_id) (st : absStateT) : vProp :=
  (∃ γtl γel γh γg γn γwl γsl γq (i : nat),
      ⌜γe = encode (γtl, γel, γh, γg, γn) ∧ γs = encode (γwl, γsl, γq)⌝ ∗
     ⎡ ghost_map.ghost_map_elem γq gid DfracDiscarded i ⎤ ∗
     ⎡ mono_list_idx_own γsl i st ⎤)%I.
Definition OmoGidState_aux : seal (@OmoGidState_def). Proof. by eexists. Qed.
Definition OmoGidState := unseal (@OmoGidState_aux).
Definition OmoGidState_eq : @OmoGidState = _ := seal_eq _.

Global Instance OmoGid_persistent γe e gid : Persistent (OmoGid γe e gid).
Proof. rewrite OmoGid_eq. apply _. Qed.
Global Instance OmoGid_timeless γe e gid : Timeless (OmoGid γe e gid).
Proof. rewrite OmoGid_eq. apply _. Qed.
Global Instance OmoGid_objective γe e gid : Objective (OmoGid γe e gid).
Proof. rewrite OmoGid_eq. apply _. Qed.

Global Instance OmoGidState_persistent γe γs gid st : Persistent (OmoGidState γe γs gid st).
Proof. rewrite OmoGidState_eq. apply _. Qed.
Global Instance OmoGidState_timeless γe γs gid st : Timeless (OmoGidState γe γs gid st).
Proof. rewrite OmoGidState_eq. apply _. Qed.
Global Instance OmoGidState_objective γe γs gid st : Objective (OmoGidState γe γs gid st).
Proof. rewrite OmoGidState_eq. apply _. Qed.


Lemma OmoGid_agree γe e gid gid' :
  OmoGid γe e gid -∗ OmoGid γe e gid' -∗ ⌜ gid = gid' ⌝.
Proof.
  iIntros "#GID1 #GID2". rewrite OmoGid_eq.
  iDestruct "GID1" as (??????) "[[%Hγe %EQ1] #EL@e]".
  iDestruct "GID2" as (??????) "[[%Hγe' %EQ2] #EL@e']". encode_agree Hγe.
  iDestruct (mono_list_idx_agree with "EL@e EL@e'") as %<-.
  rewrite EQ1 EQ2. done.
Qed.

Lemma OmoEq_internal γe e1 e2 :
  OmoEq γe e1 e2 -∗
  ∃ gid, OmoGid γe e1 gid ∗ OmoGid γe e2 gid.
Proof.
  iIntros "#e1=e2". rewrite OmoEq_eq OmoGid_eq.
  iDestruct "e1=e2" as (???????) "([%Hγe %EQ] & #EL@e1 & #EL@e2)".
  iExists einfo1.1.2. iSplit.
  - iExists γtl,γel,γh,γg,γn,einfo1. iFrame "#". done.
  - iExists γtl,γel,γh,γg,γn,einfo2. iFrame "#". done.
Qed.

Lemma OmoLe_internal γe e1 e2 :
  OmoLe γe e1 e2 -∗
  ∃ gid1 gid2, OmoGid γe e1 gid1 ∗ OmoGid γe e2 gid2 ∗ ⌜ (gid1 ≤ gid2)%Qp ⌝.
Proof.
  iIntros "#e1≤e2". rewrite OmoLe_eq OmoGid_eq.
  iDestruct "e1≤e2" as (???????) "([%Hγe %LE] & #EL@e1 & #EL@e2)".
  iExists einfo1.1.2,einfo2.1.2. iSplit; last iSplit.
  - iExists γtl,γel,γh,γg,γn,einfo1. iFrame "#". done.
  - iExists γtl,γel,γh,γg,γn,einfo2. iFrame "#". done.
  - done.
Qed.

Lemma OmoLt_internal γe e1 e2 :
  OmoLt γe e1 e2 -∗
  ∃ gid1 gid2, OmoGid γe e1 gid1 ∗ OmoGid γe e2 gid2 ∗ ⌜ (gid1 < gid2)%Qp ⌝.
Proof.
  iIntros "#e1<e2". rewrite OmoLt_eq OmoGid_eq.
  iDestruct "e1<e2" as (???????) "([%Hγe %LT] & #EL@e1 & #EL@e2)".
  iExists einfo1.1.2,einfo2.1.2. iSplit; last iSplit.
  - iExists γtl,γel,γh,γg,γn,einfo1. iFrame "#". done.
  - iExists γtl,γel,γh,γg,γn,einfo2. iFrame "#". done.
  - done.
Qed.

Lemma OmoEq_from_Gid γe e1 e2 gid :
  OmoGid γe e1 gid -∗ OmoGid γe e2 gid -∗
  OmoEq γe e1 e2.
Proof.
  iIntros "#GID1 #GID2". rewrite OmoGid_eq OmoEq_eq.
  iDestruct "GID1" as (??????) "[[%Hγe %EQ1] #EL@e]".
  iDestruct "GID2" as (??????) "[[%Hγe' %EQ2] #EL@e']". encode_agree Hγe.
  iExists γtl,γel,γh,γg,γn,einfo,einfo0. iFrame "#". rewrite -EQ1 -EQ2. done.
Qed.

Lemma OmoLe_from_Gid γe e1 e2 gid1 gid2 :
  (gid1 ≤ gid2)%Qp →
  OmoGid γe e1 gid1 -∗ OmoGid γe e2 gid2 -∗
  OmoLe γe e1 e2.
Proof.
  iIntros "%LE #GID1 #GID2". rewrite OmoGid_eq OmoLe_eq.
  iDestruct "GID1" as (??????) "[[%Hγe %EQ1] #EL@e]".
  iDestruct "GID2" as (??????) "[[%Hγe' %EQ2] #EL@e']". encode_agree Hγe.
  iExists γtl,γel,γh,γg,γn,einfo,einfo0. iFrame "#". rewrite -EQ1 -EQ2. done.
Qed.

Lemma OmoLt_from_Gid γe e1 e2 gid1 gid2 :
  (gid1 < gid2)%Qp →
  OmoGid γe e1 gid1 -∗ OmoGid γe e2 gid2 -∗
  OmoLt γe e1 e2.
Proof.
  iIntros "%LT #GID1 #GID2". rewrite OmoGid_eq OmoLt_eq.
  iDestruct "GID1" as (??????) "[[%Hγe %EQ1] #EL@e]".
  iDestruct "GID2" as (??????) "[[%Hγe' %EQ2] #EL@e']". encode_agree Hγe.
  iExists γtl,γel,γh,γg,γn,einfo,einfo0. iFrame "#". rewrite -EQ1 -EQ2. done.
Qed.

Lemma OmoGidState_agree γe γs gid st st' :
  OmoGidState γe γs gid st -∗
  OmoGidState γe γs gid st' -∗
  ⌜ st = st' ⌝.
Proof.
  rewrite OmoGidState_eq /OmoGidState_def.
  iStep 2 as (??????????) "Hγel1 Hmon1 Hγel2 Hmon2".
  iDestruct (ghost_map.ghost_map_elem_agree with "Hγel1 Hγel2") as %->.
  by iDestruct (mono_list_idx_agree with "Hmon1 Hmon2") as %->.
Qed.

Lemma OmoSnap_internal γe γs e st :
  @OmoSnap _ _ _ _ _ γe γs e st -∗
  ∃ gid, OmoGid γe e gid ∗ OmoGidState γe γs gid st.
Proof.
  rewrite OmoSnap_eq OmoGid_eq OmoGidState_eq
         /OmoSnap_def /OmoGid_def /OmoGidState_def.
  iSteps.
Qed.

Lemma OmoSnap_from_GidState γe γs e gid st :
  OmoGid γe e gid -∗
  OmoGidState γe γs gid st -∗
  @OmoSnap _ _ _ _ _ γe γs e st.
Proof.
  rewrite OmoSnap_eq OmoGid_eq OmoGidState_eq
         /OmoSnap_def /OmoGid_def /OmoGidState_def.
  iSteps.
Qed.

End omo_pred_diaframe.

#[global] Opaque OmoGid OmoGidState.
