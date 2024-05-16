From gpfsl.examples Require Import sflib.

From iris.algebra Require Import auth gset gmap agree.
From iris.base_logic Require Import lib.mono_nat.
From iris.proofmode Require Import tactics.

From gpfsl.base_logic Require Import meta_data.
From gpfsl.examples.algebra Require Import mono_list.
From gpfsl.logic Require Import logatom atomics invariants.

From gpfsl.logic Require Import repeat_loop new_delete.
From gpfsl.examples Require Import map_seq loc_helper.
From gpfsl.examples.queue Require Import spec_history code_ms_tailcas.
From gpfsl.examples.omo Require Import omo omo_preds append_only_loc.

Require Import iris.prelude.options.

#[local] Notation link := 0%nat (only parsing).
#[local] Notation data := 1%nat (only parsing).
#[local] Notation head := 0%nat (only parsing).
#[local] Notation tail := 1%nat (only parsing).
#[local] Notation null := 0%nat (only parsing).

(** Namespace for our internal invariant. See `QueueInternalInv`. *)
Definition msqN (N : namespace) (q: loc) := N .@ q.

Implicit Types
  (qu st : queue_state) (node : event_id * Z * view * eView)
  (M : eView) (Eh Et El : history loc_event)
  (tid : thread_id) (γh γt γs γsh γst γcl γl γsl γm : gname)
  (e et : event_id)
  (es : list event_id)
  (ninfo : event_id * gname * gname * val * loc)
  (nidx : nat)
  (CL : list (event_id * gname * gname * val * loc)).

(** * Ghost state construction *)

Class msqueueG Σ := MSQueueG {
  ms_generalG :> omoGeneralG Σ;
  ms_omoG :> omoSpecificG Σ qevent queue_state;
  ms_aolocG :> appendOnlyLocG Σ;
  ms_enq_list_monoG :> mono_listG (event_id * gname * gname * val * loc) Σ;
}.

Definition msqueueΣ : gFunctors := #[omoGeneralΣ; omoSpecificΣ qevent queue_state; appendOnlyLocΣ; mono_listΣ (event_id * gname * gname * val * loc)].

Global Instance subG_msqueueΣ {Σ} : subG msqueueΣ Σ → msqueueG Σ.
Proof. solve_inG. Qed.

(** * The invariant and local assertions *)
Section msqueue.
Context `{!noprolG Σ, !msqueueG Σ, !atomicG Σ}.
Local Existing Instances ms_omoG ms_aolocG ms_enq_list_monoG.

#[local] Notation iProp := (iProp Σ).
#[local] Notation vProp := (vProp Σ).
Local Open Scope nat_scope.

Definition AllTailMsgInner γg γt γcl et : vProp :=
  ∃ eVt gen enqid γl γsl (v : val) (l : loc) V (eVenq : omo_event qevent),
    OmoEinfo γt et eVt ∗
    OmoEinfo γg enqid eVenq ∗
    ⎡mono_list_idx_own γcl gen (enqid, γl, γsl, v, l)⎤ ∗
    ⌜ loc_event_msg eVt.(type) = (#l, V) ∧ eVenq.(sync) ⊑ V ⌝ ∗
    @{V} OmoEview γl {[0]}.

Definition AllTailMsg γg γt γcl es : vProp :=
  [∗ list] e ∈ es, AllTailMsgInner γg γt γcl e.

Definition AllHeadMsgInner γg γh γs γcl γm genh eh : vProp :=
  ∃ deqid eVh enqid γl γsl (v : val) (l : loc) (V : view) st Ml,
    OmoEinfo γh eh eVh ∗
    OmoCW γg γh deqid eh ∗ CWMonoValid γm deqid ∗
    OmoLe γg enqid deqid ∗ (* gen of enq ≤ gen of deq *)
    OmoSnap γg γs deqid st ∗
    ⎡mono_list_idx_own γcl genh (enqid, γl, γsl, v, l)⎤ ∗
    ⌜ loc_event_msg eVh.(type) = (#l, V) ⌝ ∗
    @{V} OmoEview γl Ml ∗
    match st with
    | [] => emp
    | hd :: _ => ∃ enqid' γl' γsl' (v' : val) (l' : loc) el omol',
      OmoSnapOmo γl γsl omol' ∗
      ⎡mono_list_idx_own γcl (genh + 1) (enqid', γl', γsl', v', l')⎤ ∗
      ⌜ Ml = {[el; 0]} ∧ omo_write_op omol' = [0; el] ⌝
    end.

Definition AllHeadMsg γg γh γs γcl γm es : vProp :=
  [∗ list] gen↦e ∈ es, AllHeadMsgInner γg γh γs γcl γm gen e.

(* All [Enq] events in [M] are exactly ones in [CL] *)
Definition eView_Enq_exact γg M CL : vProp :=
  ([∗ list] ninfo ∈ CL, ⌜ ninfo.1.1.1.1 ∈ M ⌝) ∗
  ([∗ set] e ∈ M,
      ∃ eV,
        OmoEinfo γg e eV ∗
        match eV.(type) with
        | Enq _ => ⌜ e ∈ CL.*1.*1.*1.*1 ⌝
        | _ => True
        end).

Definition HeadLastMsg γg γh γs γcl es esh CL : vProp :=
  ∃ eh deqid st gen CLh (eVh : omo_event loc_event) M',
    OmoCW γg γh deqid eh ∗
    OmoSnap γg γs deqid st ∗
    OmoEinfo γh eh eVh ∗

    ⎡mono_list_lb_own γcl CLh⎤ ∗ ⌜ (length CLh = length esh + length st)%nat ⌝ ∗
    @{(loc_event_msg eVh.(type)).2} OmoEview γg M' ∗
    eView_Enq_exact γg M' CLh ∗
    OmoUB γg M' deqid ∗

    ⌜ last esh = Some eh
    ∧ es !! gen = Some deqid
    ∧ st.*1.*1.*1 ++ drop (gen + 1) es = drop (length esh) CL.*1.*1.*1.*1 ⌝ ∗

    ([∗ list] gen↦state ∈ st,
      ∃ enqid' γl' γsl' (z' : Z) l' eV',
        OmoEinfo γg enqid' eV' ∗
        ⎡mono_list_idx_own γcl (length esh + gen) (enqid', γl', γsl', #z', l')⎤ ∗
        ⌜ state = (enqid', z', eV'.(sync), eV'.(eview))
        ∧ eV'.(type) = Enq z'
        ∧ (z' > 0)%Z ⌝).

Definition NextFieldInfo γg γl γsl γcl es gen : vProp :=
  ∃ eVl0,
    OmoEinfo γl 0 eVl0 ∗ ⌜ (loc_event_msg eVl0.(type)).1 = #0 ⌝ ∗
    (⌜ es = [0] ⌝ ∨
    (∃ el eVl enqid' γl' γsl' (v' : val) (l' : loc) (eVenq' : omo_event qevent) (V' : view),
        ⌜ es = [0; el] ∧ el ≠ 0 ∧ loc_event_msg eVl.(type) = (#l', V') ⌝ ∗
        meta l' nroot (enqid', γl', γsl', v') ∗
        ⎡mono_list_idx_own γcl (gen + 1) (enqid', γl', γsl', v', l')⎤ ∗
        OmoEinfo γl el eVl ∗
        OmoEinfo γg enqid' eVenq' ∗ ⌜ V' = eVenq'.(sync) ⌝ ∗
        OmoCW γg γl enqid' el ∗
        OmoHb γg γl enqid' el ∗
        @{V'} (OmoEview γl {[el; 0]} ∗ OmoEview γl' {[0]}) ∗
        (∃ q, @{V'} (l' >> data) ↦{q} v'))).

Definition AllNodesInner γg γcl gen ninfo : vProp :=
  ∃ enqid eVenq γl γsl v l El omol mol,
    ⌜ ninfo = (enqid, γl, γsl, v, l) ⌝ ∗
    meta l nroot (enqid, γl, γsl, v) ∗
    OmoAuth γl γsl (1/2) El omol mol _ ∗
    OmoEinfo γg enqid eVenq ∗
    (∃ Vbl, @{Vbl} append_only_loc (l >> link) γl ∅ cas_only) ∗
    NextFieldInfo γg γl γsl γcl (omo_write_op omol) gen ∗
    ⌜ ∃ (z : Z), v = #z ∧ eVenq.(type) = Enq z ∧ (z > 0)%Z ⌝.

Definition AllNodes γg γcl CL : vProp :=
  [∗ list] gen↦ninfo ∈ CL, AllNodesInner γg γcl gen ninfo.

(* This is used to derive the fact that every non-last node has nonnull value written in next field *)
Definition PrevLinkInfo γg γcl gen ninfo : vProp :=
  match gen with
  | 0 => emp
  | S gen' => ∃ enqid γl γsl v l enqid' γl' γsl' (v' : val) (l' : loc) omol',
      ⌜ ninfo = (enqid, γl, γsl, v, l) ⌝ ∗
      ⎡mono_list_idx_own γcl gen' (enqid', γl', γsl', v', l')⎤ ∗
      OmoLe γg enqid' enqid ∗
      OmoSnapOmo γl' γsl' omol' ∗
      ⌜ length omol' = 2 ⌝
  end.

Definition AllPrevLinks γg γcl CL : vProp :=
  [∗ list] gen↦ninfo ∈ CL, PrevLinkInfo γg γcl gen ninfo.

(* Each [enq] event observes all previous [enq] events *)
Definition EnqSeen γg γcl CL : vProp :=
  [∗ list] gen↦ninfo ∈ CL,
    ∃ CL' (eVl : omo_event qevent) M,
      ⎡mono_list_lb_own γcl CL'⎤ ∗ ⌜ length CL' = (gen + 1)%nat ⌝ ∗
      OmoEinfo γg ninfo.1.1.1.1 eVl ∗
      OmoUB γg ({[ninfo.1.1.1.1]} ∪ eVl.(eview) ∪ M) ninfo.1.1.1.1 ∗
      @{eVl.(sync)} OmoEview γg ({[ninfo.1.1.1.1]} ∪ eVl.(eview) ∪ M) ∗
      eView_Enq_exact γg ({[ninfo.1.1.1.1]} ∪ eVl.(eview) ∪ M) CL'.

Definition AllEvents γg γh γcl γm E : vProp :=
  [∗ list] e↦eV ∈ E,
    match eV.(type) with
    | Enq _ => emp
    | _ => ∃ e' eh eh',
      OmoHb γg γh e eh ∗ OmoEq γg e e' ∗ OmoEq γh eh eh' ∗
      OmoCW γg γh e' eh' ∗ CWMonoValid γm e'
    end.

Definition QueueInternalInv γg q E : vProp :=
  ∃ γh γt γs γsh γst γcl γm Eh Et omo omoh omot stlist moh mot CL Mono,
    meta q nroot (γh,γt,γsh,γst,γcl,γm) ∗

    OmoAuth γg γs (1/2) E omo stlist _ ∗
    OmoAuth γh γsh (1/2) Eh omoh moh _ ∗
    OmoAuth γt γst (1/2) Et omot mot _ ∗
    ⎡mono_list_auth_own γcl 1 CL⎤ ∗

    (∃ Vbh, @{Vbh} append_only_loc (q >> head) γh ∅ cas_only) ∗
    (∃ Vbt, @{Vbt} append_only_loc (q >> tail) γt ∅ cas_only) ∗

    AllNodes γg γcl CL ∗ AllPrevLinks γg γcl CL ∗
    AllHeadMsg γg γh γs γcl γm (omo_write_op omoh) ∗
    HeadLastMsg γg γh γs γcl (omo_write_op omo) (omo_write_op omoh) CL ∗
    AllTailMsg γg γt γcl (omo_write_op omot) ∗
    CWMono γg γh γm Mono ∗
    EnqSeen γg γcl CL ∗
    AllEvents γg γh γcl γm E.

Definition QueueInv (γg : gname) (q : loc) (E : history qevent) : vProp :=
  ∃ γs omo stlist, OmoAuth γg γs (1/2) E omo stlist _.

Definition InternalInv_inner γg q : vProp := ∃ E, QueueInternalInv γg q E.
Definition InternInv N γg q := inv (msqN N q) (InternalInv_inner γg q).

Definition QueueLocal (N : namespace) γg q (E : history qevent) M : vProp :=
  ∃ γh γt γsh γst γcl γm Mh Mt CL,
    meta q nroot (γh,γt,γsh,γst,γcl,γm) ∗
    InternInv N γg q ∗

    OmoSnapHistory γg E ∗
    OmoEview γg M ∗
    OmoEview γh Mh ∗
    OmoEview γt Mt ∗
    ⎡mono_list_lb_own γcl CL⎤ ∗

    eView_Enq_exact γg M CL ∗
    ⌜ CL ≠ [] ⌝.

Local Instance eView_Enq_exact_persistent γg M CL : Persistent (eView_Enq_exact γg M CL).
Proof.
  apply @bi.sep_persistent; [apply _|].
  apply big_sepS_persistent. intros. apply @bi.exist_persistent. intros.
  apply @bi.sep_persistent; [apply _|]. destruct (x0.(type)); apply _.
Qed.
Local Instance eView_Enq_exact_objective γg M CL : Objective (eView_Enq_exact γg M CL).
Proof.
  apply sep_objective; try apply _.
  apply big_sepS_objective; intros. apply exists_objective; intros.
  apply sep_objective; try apply _. destruct (x.(type)); apply _.
Qed.
Local Instance eView_Enq_exact_timeless γg M CL : Timeless (eView_Enq_exact γg M CL).
Proof.
  apply @bi.sep_timeless; try apply _.
  apply big_sepS_timeless; intros. apply @bi.exist_timeless; intros.
  apply @bi.sep_timeless; try apply _. destruct (x0.(type)); apply _.
Qed.
Local Instance PrevLinkInfo_objective γg γcl gen ninfo : Objective (PrevLinkInfo γg γcl gen ninfo).
Proof. destruct gen; apply _. Qed.
Local Instance PrevLinkInfo_persistent γg γcl gen ninfo : Persistent (PrevLinkInfo γg γcl gen ninfo).
Proof. destruct gen; apply _. Qed.
Local Instance PrevLinkInfo_timeless γg γcl gen ninfo : Timeless (PrevLinkInfo γg γcl gen ninfo).
Proof. destruct gen; apply _. Qed.
Local Instance AllHeadMsgInner_persistent γg γh γs γcl γm genh eh : Persistent (AllHeadMsgInner γg γh γs γcl γm genh eh).
Proof.
  repeat (apply @bi.exist_persistent; intros).
  repeat (apply @bi.sep_persistent; [apply _|]).
  destruct x7; apply _.
Qed.
Local Instance AllHeadMsgInner_objective γg γh γs γcl γm genh eh : Objective (AllHeadMsgInner γg γh γs γcl γm genh eh).
Proof.
  repeat (apply exists_objective; intros).
  repeat (apply sep_objective; try apply _).
  destruct x7; apply _.
Qed.
Local Instance AllHeadMsgInner_timeless γg γh γs γcl γm genh eh : Timeless (AllHeadMsgInner γg γh γs γcl γm genh eh).
Proof.
  repeat (apply @bi.exist_timeless; intros).
  repeat (apply @bi.sep_timeless; try apply _).
  destruct x7; apply _.
Qed.
Local Instance QueueInternalInv_objective γg q E : Objective (QueueInternalInv γg q E).
Proof.
  repeat (apply exists_objective; intros).
  repeat (apply sep_objective; [apply _|]).
  apply big_sepL_objective. intros. destruct (x16.(type)); apply _.
Qed.
Local Instance QueueInternalInv_timeless γg q E : Timeless (QueueInternalInv γg q E).
Proof.
  repeat (apply @bi.exist_timeless; intros).
  repeat (apply @bi.sep_timeless; [apply _|]).
  apply big_sepL_timeless. intros. destruct (x16.(type)); apply _.
Qed.
Local Instance AllEvents_persistent γg γh γcl γm E : Persistent (AllEvents γg γh γcl γm E).
Proof. apply big_sepL_persistent. intros. destruct (x.(type)); apply _. Qed.
Global Instance QueueInv_objective γg q E : Objective (QueueInv γg q E) := _.
Global Instance QueueInv_timeless γg q E : Timeless (QueueInv γg q E) := _.
Global Instance QueueLocal_persistent N γg q E M : Persistent (QueueLocal N γg q E M) := _.

Lemma NextFieldInfo_dup γg γl γsl γcl es gen :
  NextFieldInfo γg γl γsl γcl es gen -∗ NextFieldInfo γg γl γsl γcl es gen ∗ NextFieldInfo γg γl γsl γcl es gen.
Proof.
  iDestruct 1 as (eV0) "(#e0✓eV0 & %eV0EV & [%Hes|CASE2])".
  - iSplitL; repeat iExists _; iFrame "∗#%".
  - iDestruct "CASE2" as (el eVl enqid' γl' γsl' v' l' eVenq' V' EQ) "(#H1 & #H2 & #H3 & #H4 & %H4 & #H5 & #H7 & #H8 & [%q [l'↦1 l'↦2]])".
    iSplitL "l'↦1"; iExists eV0; iFrame "#%"; iRight; iExists el,eVl,enqid',γl',γsl',v',l',eVenq';
    iExists V'; iFrame "#%"; eauto with iFrame.
Qed.

Lemma gen_le_enq_deq γg γh γs γsh γcl γl γsl γm q Eh v l CL omoh moh gen1 gen2 enqid deqid eh Mono :
  CL !! gen1 = Some (enqid, γl, γsl, v, l) →
  omo_write_op omoh !! gen2 = Some eh →
  gen1 ≤ gen2 →
  AllHeadMsg γg γh γs γcl γm (omo_write_op omoh) -∗
  OmoCW γg γh deqid eh -∗
  CWMonoValid γm deqid -∗
  OmoAuth γh γsh q Eh omoh moh _ -∗
  CWMono γg γh γm Mono -∗
  ⎡mono_list_auth_own γcl 1 CL⎤ -∗
  OmoLe γg enqid deqid.
Proof.
  iIntros "%Hgen1 %Hgen2 %LE".
  iInduction LE as [|gen2'] "IH" forall (eh deqid Hgen2); iIntros "AllHeadMsg #deqid↦eh #MONO✓deqid Mh● MONO CL●".
  - iDestruct (big_sepL_lookup with "AllHeadMsg") as "Inner"; [exact Hgen2|].
    iDestruct "Inner" as (??????????) "(_ & #deqid'↦eh & _ & #enqid≤deqid' & _ & #CL@gen1 & _)".
    iDestruct (mono_list_auth_idx_lookup with "CL● CL@gen1") as %Hgen1'.
    rewrite Hgen1 in Hgen1'. inversion Hgen1'. subst enqid0 γl0 γsl0 v0 l0. clear Hgen1'.
    iDestruct (OmoCW_agree_2 with "deqid↦eh deqid'↦eh") as %[_ <-]. done.
  - have [eh' Hgen2'] : is_Some (omo_write_op omoh !! gen2').
    { rewrite lookup_lt_is_Some. apply lookup_lt_Some in Hgen2. lia. }
    iDestruct (big_sepL_lookup with "AllHeadMsg") as "#Inner"; [exact Hgen2'|].
    iDestruct "Inner" as (deqid' ?????????) "(_ & deqid'↦eh' & #MONO✓deqid' & _ & #CL@gen2' & _)".
    iDestruct ("IH" with "[] AllHeadMsg deqid'↦eh' MONO✓deqid' Mh● MONO CL●") as "#enqid≤deqid'"; [done|].
    iDestruct (OmoLe_get _ _ _ _ _ _ (wr_event gen2') (wr_event (S gen2')) with "Mh●") as "#eh'≤eh".
    { by rewrite lookup_omo_wr_event. } { by rewrite lookup_omo_wr_event. } { simpl. lia. }
    iDestruct (CWMono_acc with "MONO MONO✓deqid' MONO✓deqid deqid'↦eh' deqid↦eh eh'≤eh") as "#deqid'≤deqid".
    iDestruct (OmoLe_trans with "enqid≤deqid' deqid'≤deqid") as "#enqid≤deqid". iFrame "#".
Qed.

Lemma gen_le_enq_enq γg γs γcl q (E : history qevent) omo stlist CL eidx1 eidx2 gen1 gen2 enqid1 enqid2 γl1 γl2 γsl1 γsl2 v1 v2 l1 l2 :
  CL !! gen1 = Some (enqid1, γl1, γsl1, v1, l1) →
  CL !! gen2 = Some (enqid2, γl2, γsl2, v2, l2) →
  gen1 ≤ gen2 →
  lookup_omo omo eidx1 = Some enqid1 →
  lookup_omo omo eidx2 = Some enqid2 →
  AllPrevLinks γg γcl CL -∗
  OmoAuth γg γs q E omo stlist _ -∗
  ⎡mono_list_auth_own γcl 1 CL⎤ -∗
  ⌜ gen_of eidx1 ≤ gen_of eidx2 ⌝.
Proof.
  iIntros "%Hgen1 %Hgen2 %LE %Heidx1 %Heidx2 #AllPrevLinks M● CL●".
  iDestruct (OmoAuth_wf with "M●") as %[OMO_GOOD _].
  iInduction LE as [|gen2'] "IH" forall (eidx2 enqid2 γl2 γsl2 v2 l2 Hgen2 Heidx2).
  - rewrite Hgen1 in Hgen2. inversion Hgen2. subst enqid2 γl2 γsl2 v2 l2.
    by specialize (lookup_omo_inj _ _ _ _ _ _ OMO_GOOD Heidx1 Heidx2) as <-.
  - have [ninfo Hgen2'] : is_Some (CL !! gen2').
    { rewrite lookup_lt_is_Some. apply lookup_lt_Some in Hgen2. lia. }
    destruct ninfo as [[[[enqid3 γl3] γsl3] v3] l3].

    iDestruct (big_sepL_lookup with "AllPrevLinks") as "Sgen2Info"; [exact Hgen2|].
    iDestruct "Sgen2Info" as (??????????) "(%& %EQ & CL@gen2' & enqid3≤enqid2 & _)".
    inversion EQ. subst enqid γl γsl v l. clear EQ.
    iDestruct (mono_list_auth_idx_lookup with "CL● CL@gen2'") as %Hgen2''.
    rewrite Hgen2' in Hgen2''. inversion Hgen2''. subst enqid' γl' γsl' v' l'. clear Hgen2''.
    iDestruct (OmoAuth_OmoLe_l with "M● enqid3≤enqid2") as %[eidx3 Heidx3].
    iDestruct ("IH" with "[] [] M● CL●") as %LE1; [iPureIntro; exact Hgen2'|iPureIntro; exact Heidx3|].
    iDestruct (OmoLe_Le with "M● enqid3≤enqid2") as %LE2; try done. iPureIntro. lia.
Qed.

Lemma eView_Enq_exact_insert_nonenq γg M CL e eV :
  (∀ v, eV.(type) ≠ Enq v) →
  eView_Enq_exact γg M CL -∗
  OmoEinfo γg e eV -∗
  eView_Enq_exact γg ({[e]} ∪ M) CL.
Proof.
  iIntros "%NEQEnq [#M_CL1 M_CL2] #e✓eV".
  destruct (decide (e ∈ M)) as [IN|NIN].
  { replace ({[e]} ∪ M) with M; [|set_solver]. iFrame "∗#". }
  iSplitL "M_CL1".
  - iApply big_sepL_intro. iIntros "!> % % %".
    iDestruct (big_sepL_lookup with "M_CL1") as "%"; [done|]. iPureIntro. set_solver.
  - rewrite big_sepS_union; [|set_solver]. iFrame.
    rewrite big_sepS_singleton. iExists eV. iFrame "#". destruct (eV.(type)); try done.
    by specialize (NEQEnq v).
Qed.

Lemma eView_Enq_exact_union γg γcl M1 M2 CL1 CL2 :
  eView_Enq_exact γg M1 CL1 -∗
  eView_Enq_exact γg M2 CL2 -∗
  ⎡mono_list_lb_own γcl CL1⎤ -∗
  ⎡mono_list_lb_own γcl CL2⎤ -∗
  ∃ CL, eView_Enq_exact γg (M1 ∪ M2) CL ∗ ⎡mono_list_lb_own γcl CL⎤ ∗ ⌜ (length CL = (length CL1) `max` (length CL2))%nat ⌝.
Proof.
  iIntros "#M1_CL1 #M2_CL2 #CL1◯ #CL2◯".
  iDestruct (mono_list_lb_valid with "CL1◯ CL2◯") as %[LECL1CL2|LECL2CL1].
  - iExists CL2. iFrame "CL2◯". iSplitR; [|by apply prefix_length in LECL1CL2; iPureIntro; lia]. iSplit.
    + rewrite big_sepL_forall. iIntros "%gen %ninfo %Hninfo".
      iDestruct "M2_CL2" as "[M2_CL2 _]". iDestruct (big_sepL_lookup with "M2_CL2") as %M2INCL; [done|]. iPureIntro. set_solver.
    + iApply big_sepS_intro. iIntros "%e %eIncl !>". rewrite elem_of_union in eIncl. destruct eIncl as [eIncl|eIncl].
      * iDestruct "M1_CL1" as "[_ M1_CL1]". iDestruct (big_sepS_elem_of with "M1_CL1") as (eV) "[e✓eV CASE]"; [done|].
        iExists eV. iFrame "e✓eV". destruct (eV.(type)); try done. iDestruct "CASE" as %eInclCL. iPureIntro.
        eapply elem_of_prefix; [done|]. do 4 apply fmap_prefix. done.
      * iDestruct "M2_CL2" as "[_ M2_CL2]". iDestruct (big_sepS_elem_of with "M2_CL2") as "H"; [done|]. iFrame "H".
  - iExists CL1. iFrame "CL1◯". iSplitR; [|by apply prefix_length in LECL2CL1; iPureIntro; lia]. iSplit.
    + rewrite big_sepL_forall. iIntros "%gen %ninfo %Hninfo".
      iDestruct "M1_CL1" as "[M1_CL1 _]". iDestruct (big_sepL_lookup with "M1_CL1") as %M2INCL; [done|]. iPureIntro. set_solver.
    + iApply big_sepS_intro. iIntros "%e %eIncl !>". rewrite elem_of_union in eIncl. destruct eIncl as [eIncl|eIncl].
      * iDestruct "M1_CL1" as "[_ M1_CL1]". iDestruct (big_sepS_elem_of with "M1_CL1") as "H"; [done|]. iFrame "H".
      * iDestruct "M2_CL2" as "[_ M2_CL2]". iDestruct (big_sepS_elem_of with "M2_CL2") as (eV) "[e✓eV CASE]"; [done|].
        iExists eV. iFrame "e✓eV". destruct (eV.(type)); try done. iDestruct "CASE" as %eInclCL. iPureIntro.
        eapply elem_of_prefix; [done|]. do 4 apply fmap_prefix. done.
Qed.

Local Tactic Notation "simplify_meta6" "with" constr(Hs) :=
  iDestruct (meta_agree with Hs) as %[[[[[-> ->]%pair_inj ->]%pair_inj ->]%pair_inj ->]%pair_inj ->]%pair_inj.

Local Tactic Notation "simplify_meta4" "with" constr(Hs) :=
  iDestruct (meta_agree with Hs) as %[[[-> ->]%pair_inj ->]%pair_inj ->]%pair_inj.

Lemma QueueInv_Linearizable_instance :
  ∀ γg q E, QueueInv γg q E ⊢ ⌜ Linearizability E ⌝.
Proof.
  intros. iDestruct 1 as (???) "M●".
  iDestruct (OmoAuth_Linearizable with "M●") as %H. by apply omo_compatible in H.
Qed.

Lemma QueueInv_history_wf_instance :
  ∀ γg q E, QueueInv γg q E ⊢ ⌜ history_wf E ⌝.
Proof.
  intros. iDestruct 1 as (???) "M●".
  by iDestruct (OmoAuth_wf with "M●") as "[_ %H2]".
Qed.

Lemma QueueInv_QueueLocal_instance :
  ∀ N γg q E E' M',
    QueueInv γg q E -∗ QueueLocal N γg q E' M' -∗ ⌜ E' ⊑ E ⌝.
Proof.
  intros. iDestruct 1 as (???) "M●".
  iDestruct 1 as (?????????) "(_ & _ & E◯ & _)".
  by iDestruct (OmoAuth_OmoSnapHistory with "M● E◯") as %?.
Qed.

Lemma QueueLocal_lookup_instance :
  ∀ N γg q E M e V,
    sync <$> E !! e = Some V → e ∈ M →
    QueueLocal N γg q E M -∗ ⊒V.
Proof.
  intros. iDestruct 1 as (?????????) "(_ & _ & E◯ & M◯ & _)".
  by iApply (OmoSnapHistory_OmoEview with "E◯ M◯").
Qed.

Lemma new_queue_spec :
  new_queue_spec' new_queue QueueLocal QueueInv.
Proof.
  iIntros (N tid Φ) "_ Post". wp_lam.
  (* Allocate sentinel node *)
  wp_apply wp_new; [done..|].
  iIntros (n) "([n†|%] & n↦ & Hmn & _)"; [|done]. rewrite own_loc_na_vec_singleton.
  wp_pures. rewrite -[Z.to_nat 0]/(0%nat) shift_0. wp_write.
  (* Allocate head/tail location *)
  wp_apply wp_new; [done..|].
  iIntros (q) "([q†|%] & q↦ & Hmq & _)"; [|done].
  rewrite own_loc_na_vec_cons own_loc_na_vec_singleton. iDestruct "q↦" as "[hd↦ tl↦]".
  wp_pures. rewrite -[Z.to_nat 0]/(0%nat) shift_0. wp_write. wp_pures. rewrite -[Z.to_nat 1]/(1%nat). wp_apply wp_fupd. wp_write.

  (* Create [append_only_loc] *)
  iMod (append_only_loc_cas_only_from_na with "n↦") as (γln γsn Vn eVn0) "(#⊒Vn & Mn● & #Mn◯ & omon↦ & WCOMMITn & #en0✓eVn0 & [%eVn0EV _])"; [done|].
  iMod (append_only_loc_cas_only_from_na_rel with "⊒Vn tl↦")
    as (γt γst Vt eVt0) "(#⊒Vt & Mt● & [#Mt◯ #⊒Vn@Vt] & omot↦ & WCOMMITt & #et0✓eVt0 & [%eVt0EV _])"; [done|].
  iMod (append_only_loc_cas_only_from_na_rel with "⊒Vt hd↦")
    as (γh γsh Vh eVh0) "(#⊒Vh & Mh● & [#Mh◯ #⊒Vt@Vh] & omoh↦ & WCOMMITh & #eh0✓eVh0 & [%eVh0EV %eVh0SYNC])"; [done|].

  iAssert (⌜ Vn ⊑ Vt ∧ Vt ⊑ Vh ⌝)%I with "[-]" as %[LeVnVt LeVtVh].
  { rewrite !view_at_unfold !monPred_at_in. iDestruct "⊒Vn@Vt" as %?. by iDestruct "⊒Vt@Vh" as %?. }

  set Menq := {[0%nat]}.
  set eVenq := mkOmoEvent (Enq 1) Vt Menq.

  (* Initial events are two consecutive events: Dummy Enqueue & Dummy Dequeue *)
  iMod (@OmoAuth_alloc _ _ _ _ _ eVenq ([] ++ [(0, 1%Z, eVenq.(sync), eVenq.(eview))]) _ _ queue_interpretable with "WCOMMITn")
    as (γg γs) "(M● & #M◯1@Vt & #e0↦en0 & #e0✓eVenq & #e0↪st0 & _)".
  { by eapply queue_step_Enq. } { done. }
  iDestruct (OmoHbToken_finish with "M●") as "M●".

  set Mdeq := {[1%nat]} ∪ Menq.
  set eVdeq := mkOmoEvent (Deq 1) Vh Mdeq.

  iDestruct (view_at_mono_2 _ Vh with "M◯1@Vt") as "#M◯1@Vh"; [by subst eVenq|].
  iMod (OmoAuth_insert_last with "M● M◯1@Vh WCOMMITh []") as "(M● & #M◯2@Vh & #e1↦eh0 & #e1✓eVdeq & #e1↪st1 & _)".
  { have ? : step 1%nat eVdeq [(0, 1%Z, eVenq.(sync), eVenq.(eview))] []; [|by iPureIntro; split_and!].
    eapply queue_step_Deq; try done. subst eVenq eVdeq Mdeq Menq. simpl. set_solver-. }
  iMod (OmoHb_new_1 with "M● e1✓eVdeq eh0✓eVh0") as "[M● #e1⊒eh0]"; [rewrite eVh0SYNC; solve_lat|].
  iDestruct (OmoHbToken_finish with "M●") as "M●".
  iDestruct (OmoLe_get_append_w with "M● e0✓eVenq") as "#e0≤e1".
  iDestruct (OmoSnapHistory_get with "M●") as "#E◯".
  iMod (CWMono_new γg γh) as (γm) "MONO".
  iMod (CWMono_insert_last_last (wr_event 1) with "MONO M● Mh● e1↦eh0") as "(MONO & #MONO✓e1 & M● & Mh●)"; [done|done|].

  set CL := [(0, γln, γsn, #1, n)].
  iMod (mono_list_own_alloc CL) as (γcl) "[CL● #CL◯]".
  iMod (meta_set _ _ (γh,γt,γsh,γst,γcl,γm) nroot with "Hmq") as "#HM"; [done|].
  iMod (meta_set _ _ (0,γln,γsn,#1) nroot with "Hmn") as "#HMn"; [done|].

  iAssert (eView_Enq_exact γg Mdeq CL)%I with "[-]" as "#M_CL".
  { subst Mdeq Menq CL. iSplit.
    - rewrite big_sepL_singleton. iPureIntro. set_solver-.
    - iApply big_sepS_intro. iIntros "%e %eIn". destruct (decide (e = 0)) as [->|NEQ]; iModIntro.
      + iExists eVenq. iFrame "e0✓eVenq". subst eVenq. iPureIntro. set_solver-.
      + have EQ : e = 1 by set_solver. subst e. iExists eVdeq. iFrame "e1✓eVdeq". }

  iAssert (OmoUB γg Mdeq 1)%I with "[-]" as "#MAXgen_e1".
  { subst Mdeq Menq. rewrite /OmoUB big_sepS_forall.
    iIntros "%e %eIn". destruct (decide (e = 0)) as [->|NEQ]; [done|].
    have EQ : e = 1 by set_solver. subst e.
    iDestruct (OmoEq_get_from_Einfo with "e1✓eVdeq") as "e1=e1".
    iDestruct (OmoLe_get_from_Eq with "e1=e1") as "e1≤e1". done. }

  iDestruct "M●" as "[M● M●']".
  iMod (inv_alloc (msqN N q) _ (InternalInv_inner γg q) with "[-M●' Post]") as "#I".
  { iNext. repeat iExists _. iFrame "HM Mh● MONO". iFrame.
    iDestruct (view_at_intro with "omon↦") as (Vbn) "[_ omon↦]".
    iDestruct (view_at_intro with "omoh↦") as (Vbh) "[_ omoh↦]".
    iDestruct (view_at_intro with "omot↦") as (Vbt) "[_ omot↦]".
    iSplitL "omoh↦"; [rewrite shift_0; eauto with iFrame|]. iSplitL "omot↦"; [eauto with iFrame|].
    rewrite !omo_append_w_write_op /=. subst CL.
    iSplitL; repeat iSplit; try by rewrite big_sepL_nil.
    - rewrite /AllNodes big_sepL_singleton. repeat iExists _. iFrame "HMn Mn● e0✓eVenq". iSplitR; [done|].
      iSplitL "omon↦"; [rewrite shift_0; eauto with iFrame|]. iSplitL; [|by iPureIntro; exists 1; split_and!].
      repeat iExists _. iFrame "en0✓eVn0". iSplitL; [by rewrite eVn0EV|]. iLeft. rewrite omo_append_w_write_op /=. done.
    - done.
    - iExists 1,eVh0,0,γln,γsn,#1,n,Vh. iExists [],{[0]}.
      rewrite (@mono_list_idx_own_get _ _ _ _ _ 0); [|done].
      iFrame "#". by rewrite eVh0EV.
    - iExists 0,1,[],1,[(0,γln,γsn,#1,n)],eVh0,Mdeq. rewrite eVh0EV. simpl. by iFrame "#".
    - iExists eVt0,0,0,γln,γsn,#1,n,Vt. iExists eVenq.
      rewrite (@mono_list_idx_own_get _ _ _ _ _ 0); [|done].
      iFrame "#". iPureIntro. rewrite eVt0EV. done.
    - iExists [(0,γln,γsn,#1,n)],eVenq,{[0]}. subst eVenq. simpl. iFrame "#".
      have EQ : {[0]} ∪ Menq ∪ {[0]} = {[0]} by set_solver. rewrite !EQ. clear EQ.
      iFrame "#". iSplit; [done|]. iSplit; last iSplit.
      + rewrite /OmoUB big_sepS_singleton.
        iDestruct (OmoEq_get_from_Einfo with "e0✓eVenq") as "e0=e0".
        by iDestruct (OmoLe_get_from_Eq with "e0=e0") as "e0≤e0".
      + rewrite big_sepL_singleton. set_solver-.
      + rewrite big_sepS_singleton. iExists _. iFrame "e0✓eVenq". iPureIntro. set_solver-.
    - by subst eVenq.
    - repeat iExists _. iFrame "e1↦eh0 MONO✓e1 e1⊒eh0".
      by iSplit; [iApply OmoEq_get_from_Einfo|iApply (@OmoEq_get_from_Einfo loc_event)]. }

  iDestruct ("Post" $! γg q Vt Vh [eVenq; eVdeq] Menq Mdeq with "[M●']") as "HΦ"; [|iModIntro; by iApply "HΦ"].
  iFrame "⊒Vh". iSplitR; last iSplitL; [..|done].
  - repeat iExists _. by iFrame "#".
  - repeat iExists _. iFrame.
Qed.

Lemma try_enq_spec :
  try_enq_spec' try_enq QueueLocal QueueInv.
Proof.
  intros N DISJ q tid γg E0 M V0 v VGTZ. iIntros "#⊒V0 #QueueLocal" (Φ) "AU".
  iDestruct "QueueLocal" as (?????? Mh Mt CL0) "(HM & QInv & E◯0 & M◯ & Mh◯ & Mt◯ & CL◯0 & M_CL0 & %CL0NEQ)".
  iCombine "M◯ Mh◯" as "MMh◯".
  iDestruct (view_at_intro_incl with "MMh◯ ⊒V0") as (V0') "(#⊒V0' & %LEV0V0' & [#M◯@V0' #Mh◯@V0'])".
  wp_lam. wp_apply wp_new; [done..|].
  iIntros (n) "([n†|%] & n↦ & Hms & _)"; [|done].
  rewrite own_loc_na_vec_cons own_loc_na_vec_singleton. iDestruct "n↦" as "[n↦ n_1↦]".
  wp_pures. rewrite -[Z.to_nat 1]/(1%nat). wp_write. wp_pures. rewrite -[Z.to_nat 0]/(0%nat). rewrite shift_0. wp_write.
  iLöb as "IH". wp_pures. rewrite -[Z.to_nat 1]/(1%nat). wp_bind (!ᵃᶜ #(q >> tail))%E.

  (* Inv access 1 *)
  iInv "QInv" as (E1) ">H" "Hclose".
  iDestruct "H" as (?? γs1 ???? Eh1 Et1 omo1)
    "(%omoh1 & %omot1 & %stlist1 & %moh1 & %mot1 & %CL1 & %Mono1 & HM' & M●1 & Mh●1 & Mt●1 & CL●1 & omoh↦1 & (%Vbt1 & omot↦1) & H)".
  iDestruct "H" as "(AllNodes1 & AllPrevLinks & AllHeadMsg1 & HeadLastMsg1 & #AllTailMsg1 & MONO1 & EnqSeen1 & AllEvents1)".
  simplify_meta6 with "HM' HM". iClear "HM'".
  iDestruct (OmoSnapOmo_get with "Mt●1") as "#OMOt1◯".

  wp_apply (append_only_loc_acquire_read with "[$Mt●1 $Mt◯ $omot↦1 $⊒V0']"); [solve_ndisj|].
  iIntros (et1 gent1 vt1 Vt1 V1 eVt1 eVtn1)
    "(Pures & Mt●1 & _ & #MAXgen_et1 & #et1✓eVt1 & #etn1✓eVtn1 & #et1=etn1 & #⊒V1 & #Mt◯1'@V1 & omot↦1)".
  iDestruct "Pures" as %(Eqgent1 & eVt1EV & LEV0'Vt1V1 & eVtn1EV & eVtn1SYNC).

  iDestruct (big_sepL_lookup with "AllTailMsg1")
    as (eVt1' gen1 enqid1 γl1 γsl1 v1 l1 Vt1' eVenq1)
      "(#et1✓eVt1' & #enqid1✓eVenq1 & #CL@gen1 & [%eVt1'EV %LeSYNCVtl] & #Ml1◯@Vt1)"; [exact Eqgent1|].
  iDestruct (OmoEinfo_agree with "et1✓eVt1 et1✓eVt1'") as %<-. rewrite eVt1EV in eVt1'EV. inversion eVt1'EV. subst vt1 Vt1'. clear eVt1'EV.
  iMod ("Hclose" with "[-AU n† n↦ n_1↦ Hms]") as "_".
  { repeat iExists _. iFrame "HM". iFrame. rewrite omo_insert_r_write_op. iFrame "AllTailMsg1". eauto with iFrame. }

  iModIntro. wp_pures. rewrite -[Z.to_nat 0]/(0%nat). wp_bind (!ᵃᶜ #(l1 >> link))%E.

  (* Inv access 2 *)
  iInv "QInv" as (E2) ">H" "Hclose".
  iDestruct "H" as (?? γs2 ???? Eh2 Et2 omo2)
    "(%omoh2 & %omot2 & %stlist2 & %moh2 & %mot2 & %CL2 & %Mono2 & HM' & M●2 & Mh●2 & Mt●2 & CL●2 & omoh↦2 & omot↦2 & H)".
  iDestruct "H" as "(AllNodes2 & AllPrevLinks2 & AllHeadMsg2 & HeadLastMsg2 & AllTailMsg2 & MONO2 & EnqSeen2 & AllEvents2)".
  simplify_meta6 with "HM' HM". iClear "HM'".

  iDestruct (mono_list_auth_idx_lookup with "CL●2 CL@gen1") as %HCL2gen1.
  iDestruct (big_sepL_lookup_acc with "AllNodes2") as "[Inner Close]"; [exact HCL2gen1|].
  iDestruct "Inner" as (? eVenq1' ???? El1 omol1 mol1) "(%EQ & #HMl1 & Ml1● & #enqid1✓eVenq1' & (%Vbl1 & omol1↦) & Fieldl1 & Hgen1)".
  inversion EQ. subst enqid γl γsl v0 l. clear EQ.
  iDestruct (OmoEinfo_agree with "enqid1✓eVenq1 enqid1✓eVenq1'") as %<-.

  have LEVt1V1 : Vt1 ⊑ V1 by solve_lat.
  iDestruct (view_at_mono_2 _ V1 with "Ml1◯@Vt1") as "#Ml1◯@V1"; [done|].
  iDestruct (view_at_elim with "⊒V1 Ml1◯@V1") as "Ml1◯".

  wp_apply (append_only_loc_acquire_read with "[$Ml1● $Ml1◯ $omol1↦ $⊒V1]"); [solve_ndisj|].
  iIntros (el2 genl2 vl2 Vl2 V2 eVl2 eVln2)
    "(Pures & Ml1● & _ & #MAXgen_el2 & #el2✓eVl2 & #eln2✓eVln2 & #el2=eln2 & #⊒V2 & #Ml1◯'@V2 & omol1↦)".
  iDestruct "Pures" as %(Eqgenl2 & eVl2EV & LEV1Vl2V2 & eVln2EV & eVln2SYNC).

  destruct genl2; last first.
  { (* Read pointer to next node from next field. Retry *)
    iDestruct (NextFieldInfo_dup with "Fieldl1") as "[Fieldl1 Fieldl1']".
    iDestruct "Fieldl1" as (eVl0) "(#e0✓eVl0 & %eVl0EV & [%Homol1|CASE2])".
    { rewrite Homol1 in Eqgenl2. inversion Eqgenl2. }
    iDestruct "CASE2" as (?? enqid2 γl2 γsl2 v2 l2 eVenq2 ?)
      "((%Homol1 & %NZel2 & %eVl2EV') & _ & #CL@Sgen1 & #el2✓eVl2' & #enqid2✓eVenq2 & %EQ & _ & _ & [_ #Ml2◯@Vl2] & _)".
    iAssert (⌜ el = el2 ⌝)%I with "[-]" as %->. { rewrite Homol1 /= in Eqgenl2. by destruct genl2; inversion Eqgenl2. }
    iDestruct (OmoEinfo_agree with "el2✓eVl2 el2✓eVl2'") as %<-.
    rewrite eVl2EV in eVl2EV'. inversion eVl2EV'. subst vl2 V' Vl2. clear eVl2EV'.

    iDestruct ("Close" with "[Ml1● omol1↦ Fieldl1' Hgen1]") as "AllNodes2".
    { repeat iExists _. iFrame "HMl1 enqid1✓eVenq1 Ml1●".
      rewrite omo_insert_r_write_op. iFrame. iSplitR; [done|eauto with iFrame]. }
    iMod ("Hclose" with "[-AU n† n↦ n_1↦ Hms]") as "_". { repeat iExists _. iFrame "HM". iFrame. }
    iModIntro. wp_pures. rewrite -[Z.to_nat 1]/(1%nat). wp_bind (casʳᵉˡ(_, _, _))%E.

    (* Inv access 3 *)
    iInv "QInv" as (E3) ">H" "Hclose".
    iDestruct "H" as (?? γs3 ???? Eh3 Et3 omo3)
      "(%omoh3 & %omot3 & %stlist3 & %moh3 & %mot3 & %CL3 & %Mono3 & HM' & M●3 & Mh●3 & Mt●3 & CL●3 & omoh↦3 & [%Vbt3 omot↦3] & H)".
    iDestruct "H" as "(AllNodes3 & AllPrevLinks3 & AllHeadMsg3 & HeadLastMsg3 & #AllTailMsg3 & MONO3 & EnqSeen3 & AllEvents3)".
    simplify_meta6 with "HM' HM". iClear "HM'".
    iDestruct (OmoAuth_OmoSnapOmo with "Mt●3 OMOt1◯") as %[_ LEomot1wr].
    iDestruct (OmoAuth_wf with "Mt●3") as %[OMO_GOODt3 _].

    wp_apply (append_only_loc_cas_only_cas_live_loc _ _ _ _ _ _ _ ∅ _ _ _ l1 l2 _ ∅
      with "[$Mt●3 $Mt◯ $omot↦3 $⊒V2]"); try done; [solve_ndisj|..].

    iIntros (b3 et3 gent3 vt3 Vt3 V3 mot3' omot3' eVt3 eVtn3)
      "(Pures & #MAXgen_et3 & #et3✓eVt3 & #etn3✓eVtn3 & Mt●3 & #⊒V3 & #Mt◯3@V3 & omot↦3 & CASE)".
    iDestruct "Pures" as %(Eqgent3 & eVt3EV & LeV2V3).

    iAssert (AllTailMsg γg γt γcl (omo_write_op omot3'))%I with "[-]" as "#AllTailMsg3'".
    { iDestruct "CASE" as "[(Pures & _) | [Pures sVw3]]".
      - (* CAS failed, nothing to update *)
        iDestruct "Pures" as %(-> & NEq & -> & Homot3' & eVtn3EV & eVtn3SYNC).
        subst omot3'. rewrite omo_insert_r_write_op. done.
      - (* CAS success *)
        iDestruct "Pures" as %(-> & -> & ->).
        iDestruct "sVw3" as (Vw3 (Eqmot3' & Homot3' & eVtn3EV & eVtn3SYNC & LeVt3Vw3 & NEqVt3Vw3 & NLeV3Vt3 & NEqV2V3 & LEV3Vw3)) "_".
        subst omot3'. rewrite omo_append_w_write_op /AllTailMsg big_sepL_snoc. iFrame "AllTailMsg3".
        iExists eVtn3,(gen1 + 1),enqid2,γl2,γsl2,v2,l2,Vw3. iExists eVenq2.
        iFrame "#". iPureIntro. rewrite eVtn3EV. split; [done|solve_lat]. }

    iMod ("Hclose" with "[-AU n† n↦ n_1↦ Hms]") as "_".
    { repeat iExists _. iFrame "HM AllTailMsg3'". iFrame. eauto with iFrame. }
    iModIntro. wp_let. wp_let. wp_op. wp_if. iApply ("IH" with "AU n† n↦ n_1↦ Hms"). }

  (* Read [None] from next field. Proceed *)
  iDestruct (NextFieldInfo_dup with "Fieldl1") as "[Fieldl1 Fieldl1']".
  iDestruct "Fieldl1" as (eVl0) "(#e0✓eVl0 & %eVl0EV & CASE)".
  iAssert (⌜ el2 = 0 ⌝)%I with "[-]" as %->.
  { iDestruct "CASE" as "[%Homol1|(%&%&%&%&%&%&%&%&%& (%Homol1 & _) & _)]";
    rewrite Homol1 in Eqgenl2; by inversion Eqgenl2. }
  iDestruct (OmoEinfo_agree with "el2✓eVl2 e0✓eVl0") as %<-.
  rewrite eVl2EV in eVl0EV. simpl in eVl0EV. subst vl2.

  iDestruct ("Close" with "[Ml1● omol1↦ Fieldl1' Hgen1]") as "AllNodes2".
  { repeat iExists _. iFrame "HMl1 enqid1✓eVenq1 Ml1●". rewrite omo_insert_r_write_op. iFrame. iSplitR; [done|eauto with iFrame]. }
  iMod ("Hclose" with "[-AU n† n↦ n_1↦ Hms]") as "_". { repeat iExists _. iFrame "HM". iFrame. }
  iClear "IH". iModIntro. wp_pures. rewrite -[Z.to_nat 0]/(0%nat). wp_bind (casʳᵃ(_, _, _))%E.

  (* Inv access 3 *)
  iInv "QInv" as (E3) ">H" "Hclose".
  iDestruct "H" as (?? γs3 ???? Eh3 Et3 omo3)
    "(%omoh3 & %omot3 & %stlist3 & %moh3 & %mot3 & %CL3 & %Mono3 & HM' & M●3 & Mh●3 & Mt●3 & CL●3 & omoh↦3 & omot↦3 & H)".
  iDestruct "H" as "(AllNodes3 & #AllPrevLinks3 & AllHeadMsg3 & HeadLastMsg3 & #AllTailMsg3 & MONO3 & #EnqSeen3 & AllEvents3)".
  simplify_meta6 with "HM' HM". iClear "HM'".

  iDestruct (mono_list_auth_idx_lookup with "CL●3 CL@gen1") as %HCL3gen1.
  iDestruct (big_sepL_lookup_acc with "AllNodes3") as "[Inner Close]"; [exact HCL3gen1|].
  iDestruct "Inner" as (? eVenq1' ???? El1' omol1' mol1') "(%EQ & _ & Ml1● & #enqid1✓eVenq1'' & (%Vbl1' & omol1↦) & Fieldl1 & Hgen1)".
  inversion EQ. subst enqid γl γsl v0 l. clear EQ.
  iDestruct (OmoEinfo_agree with "enqid1✓eVenq1 enqid1✓eVenq1''") as %<-.

  iAssert (⌜ if decide (gen1 = (length CL3 - 1)%nat) then length (omo_write_op omol1') = 1
              else length (omo_write_op omol1') = 2 ⌝)%I with "[-]" as %Hgen1.
  { iDestruct "Fieldl1" as (eVl0) "(#e0✓eVl0' & %eVl0EV & CASE)".
    destruct (decide (gen1 = (length CL3 - 1)%nat)) as [->|NEQ].
    - iDestruct "CASE" as "[%Homol1'|(%&%&%&%&%&%&%&%&%& _ & _ & #CL@next & _)]"; [by rewrite Homol1'|].
      rewrite (Nat.sub_add 1 (length CL3)); [|by destruct CL3; simpl; try lia].
      iDestruct (mono_list_auth_idx_lookup with "CL●3 CL@next") as %HCL3Lookup%lookup_lt_Some. lia.
    - have [ninfo Hninfo] : is_Some (CL3 !! (S gen1)).
      { rewrite lookup_lt_is_Some. apply lookup_lt_Some in HCL3gen1. lia. }
      iDestruct (big_sepL_lookup with "AllPrevLinks3") as "PrevLinkInfo"; [exact Hninfo|].
      iDestruct "PrevLinkInfo" as (??????????) "(%& _ & CL@gen1' & _ & OMOl'◯ & %LEN)".
      iDestruct (mono_list_idx_agree with "CL@gen1 CL@gen1'") as %[[[[<- <-]%pair_inj <-]%pair_inj <-]%pair_inj <-]%pair_inj.
      iDestruct "CASE" as "[%Homol1'|(%&%&%&%&%&%&%&%&%& [%Homol1' _] & _ & #CL@next & _)]"; [|by rewrite Homol1'].
      iDestruct (OmoAuth_OmoSnapOmo with "Ml1● OMOl'◯") as %[_ LEwr%prefix_length].
      rewrite Homol1' -omo_write_op_length LEN /= in LEwr. lia. }

  iMod (append_only_loc_cas_only_from_na_rel _ _ ((n >> 1) ↦ #v) with "n_1↦ n↦")
    as (γln γsn V2' eVn0) "(#⊒V2' & Mn● & [#Mn◯ n_1↦] & omon↦ & WCOMMITn & #en0✓eVn0 & [%eVn0EV _])"; [done|].

  set V2'' := V2 ⊔ V2'.
  iCombine "⊒V2 ⊒V2'" as "⊒V2''".
  rewrite monPred_in_view_op. replace (V2 ⊔ V2') with V2'' by done.
  wp_apply (append_only_loc_cas_only_cas _ _ _ _ _ _ _ ∅ _ _ _ (LitInt 0%Z) n _ ∅
    with "[$Ml1● $Ml1◯ $omol1↦ $⊒V2'']"); try done; [solve_ndisj|].

  iIntros (b3 el3 genl3 vl3 Vl3 V3 mol3 omol3 eVl3 eVln3)
    "(Pures & #MAXgen_el3 & #el3✓eVl3 & #eln3✓eVln3 & Ml1● & #⊒V3 & #Ml1◯3@V3 & omol1↦ & CASE)".
  iDestruct "Pures" as %(Eqgenl3 & eVl3EV & LeV2V3).

  have LeV1V3 : V1 ⊑ V3 by solve_lat.
  have LeV0'V1 : V0' ⊑ V1 by clear -LEV0'Vt1V1; solve_lat.
  have LeV0'V3 : V0' ⊑ V3 by solve_lat.
  iDestruct (view_at_mono_2 _ V3 with "M◯@V0'") as "#M◯@V3"; [done|].
  iDestruct (view_at_mono_2 _ V3 with "Mh◯@V0'") as "#Mh◯@V3"; [done|].
  iDestruct (view_at_mono_2 _ V3 with "Mt◯1'@V1") as "#Mt◯1'@V3"; [done|].

  iDestruct "CASE" as "[(Pures & _) | [Pures sVw3]]".
  { (* CAS failed *)
    iDestruct "Pures" as %(-> & NEq & -> & Homol3 & eVln3EV & eVln3SYNC).
    iDestruct ("Close" with "[Ml1● omol1↦ Fieldl1 Hgen1]") as "AllNodes3".
    { repeat iExists _. iFrame "HMl1 Ml1● enqid1✓eVenq1". subst omol3. rewrite omo_insert_r_write_op. iFrame.
      iSplitR; [done|eauto with iFrame]. }

    iMod ("Hclose" with "[-AU n† omon↦ Mn● WCOMMITn n_1↦ Hms]") as "_".
    { repeat iExists _. iFrame "HM AllTailMsg3 AllPrevLinks3 EnqSeen3". iFrame. }

    iMod "AU" as (E3') "[>QInv' [_ Commit]]".
    iDestruct "QInv'" as (???) "M●3".
    iDestruct (OmoSnapHistory_get with "M●3") as "#E◯3".

    iMod ("Commit" $! false V3 E3' M with "[M●3]") as "HΦ".
    { iFrame "⊒V3". iSplitL; last iSplit; [..|done].
      - repeat iExists _. iFrame.
      - repeat iExists _. iFrame "HM QInv E◯3". by iFrame "#". }

    iModIntro. wp_if. iApply wp_hist_inv; [done|]. iIntros "HINV".
    iMod (append_only_loc_to_na with "HINV Mn● omon↦") as (???) "[n↦ _]"; [solve_ndisj|].
    have LeV2'V3 : V2' ⊑ V3. { clear -LeV2V3. subst V2''. solve_lat. }
    iDestruct (view_at_mono_2 _ V3 with "n_1↦") as "n_1↦"; [done|].
    iDestruct (view_at_elim with "⊒V3 n_1↦") as "n_1↦".
    wp_apply (wp_delete _ tid 2 _ [ v0; #v] with "[$n† n↦ n_1↦]"); [done|done|..].
    { rewrite own_loc_na_vec_cons own_loc_na_vec_singleton. iFrame. }
    iIntros "_". wp_pures. by iApply "HΦ". }

  (* CAS success, commit [Enq] *)
  iDestruct "Pures" as %(-> & -> & ->).
  iDestruct "sVw3" as (Vw3 (Eqmol3 & Homol3 & eVln3EV & eVln3SYNC & LeVl3V3 & NEqVl3V3 & NLeV3Vl3 & NEqV2''V3 & ->))
    "(_ & _ & WCOMMIT)".

  iDestruct "Fieldl1" as (eVl0) "(#e0✓eVl0' & %eVl0EV & CASE)".
  iDestruct (OmoEinfo_agree with "e0✓eVl0 e0✓eVl0'") as %<-.
  iDestruct "CASE" as "[%Homol1'|(%&%&%&%&%&%&%&%&%& (%Homol1' & _ & %eVlEV) & _ & _ & #el✓eVl & _)]"; last first.
  { rewrite omo_write_op_length !Homol1' /= in Eqgenl3. inversion Eqgenl3. subst el.
    iDestruct (OmoEinfo_agree with "el3✓eVl3 el✓eVl") as %<-.
    rewrite eVl3EV in eVlEV. inversion eVlEV. }

  destruct (decide (gen1 = (length CL3 - 1)%nat)) as [->|NEQ]; [|rewrite Homol1' /= in Hgen1; lia].
  iDestruct (big_sepL_lookup with "EnqSeen3") as "Info"; [exact HCL3gen1|].
  iDestruct "Info" as (CLp eVenq1' Mp) "(CLp◯ & %LENeq & enqid1✓eVenq1''' & _ & Mp◯@SYNC & Mp_CLp)".
  iDestruct (OmoEinfo_agree with "enqid1✓eVenq1 enqid1✓eVenq1'''") as %<-. simpl.
  iDestruct (view_at_mono_2 _ V3 with "Mp◯@SYNC") as "#Mp◯@V3"; [solve_lat|].

  iDestruct (OmoEview_union_obj with "M◯@V3 Mp◯@V3") as "M◯'@V3".
  iDestruct (eView_Enq_exact_union with "M_CL0 Mp_CLp CL◯0 CLp◯") as (CLp') "(#Mp'_CLp' & #CLp◯' & %LENCLp')".
  iAssert (⌜ length CLp' = length CL3 ⌝)%I with "[-]" as %LENCLp''.
  { rewrite Nat.sub_add in LENeq; [|by destruct CL3; simpl; try lia]. rewrite LENeq in LENCLp'.
    iDestruct (mono_list_auth_lb_valid with "CL●3 CL◯0") as %[_ LECL3CL0%prefix_length].
    iPureIntro. lia. }

  have LeV0V3 : V0 ⊑ V3 by solve_lat.
  set enqId := length E3.
  set M' := {[enqId]} ∪ (M ∪ ({[enqid1]} ∪ eVenq1.(eview) ∪ Mp)).
  set egV' := mkOmoEvent (Enq v) V3 M'.
  set E3' := E3 ++ [egV'].
  have SubE3E3' : E3 ⊑ E3' by apply prefix_app_r.

  iMod "AU" as (E3'') "[>QInv' [_ Commit]]".
  iDestruct "QInv'" as (???) "M●3'".
  iDestruct (OmoAuth_agree with "M●3 M●3'") as %(<- & <- & <- & <-).
  iCombine "M●3 M●3'" as "M●3".

  iDestruct (OmoAuth_stlist_nonempty with "M●3") as %NEQstlist3.
  have [st Hst] : is_Some (last stlist3) by rewrite last_is_Some.
  iMod (OmoAuth_insert_last with "M●3 M◯'@V3 WCOMMIT []")
    as "(M●3 & #M◯''@V3 & #enqId↦eln3 & #enqId✓egV' & #enqId↪st & _)".
  { have ? : step enqId egV' st (st ++ [(enqId, v, egV'.(sync), egV'.(eview))]); [|by iPureIntro; split_and!].
    eapply queue_step_Enq; try done. subst egV' M'. set_solver-. }
  iMod (OmoHb_new_1 with "M●3 enqId✓egV' eln3✓eVln3") as "[M●3 #enqId⊒eln3]"; [rewrite eVln3SYNC;solve_lat|].
  iDestruct (OmoHbToken_finish with "M●3") as "M●3".
  iDestruct (OmoSnapHistory_get with "M●3") as "#E◯3".
  iDestruct (OmoLe_get_append_w with "M●3 enqid1✓eVenq1") as "#enqid1≤enqId".
  iMod (meta_set _ _ (enqId,γln,γsn,#v) nroot with "Hms") as "#HMn"; [done|].

  iDestruct "HeadLastMsg3" as (eh deqid st' gen CLh eVh M'')
    "(#deqid↦eh & #deqid↪st' & #eh✓eVh & #CLh◯ & %LENCLh & #M''◯ & #M''_CLh & #MAXgen_deqid & (%LAST & %Hgen & %Hst'dropdrop) & BIG1)".
  iDestruct (mono_list_auth_lb_valid with "CL●3 CLh◯") as %[_ LECLhCL3%prefix_length].

  set CL3' := CL3 ++ [(enqId, γln, γsn, #v, n)].
  iMod (mono_list_auth_own_update with "CL●3") as "[CL●3 #CL◯3]".
  { have ? : CL3 ⊑ CL3' by apply prefix_app_r. done. }
  iDestruct (mono_list_idx_own_get with "CL◯3") as "CL@new"; [by apply lookup_app_1_eq|].

  iAssert (⌜ length El1' ≠ 0 ⌝)%I with "[-]" as %NEQlenEl1'.
  { destruct El1'; [|done]. iDestruct (OmoAuth_wf with "Ml1●") as %[OMO_GOOD _].
    have EQ1 : lookup_omo omol3 (wr_event 0) = Some 0 by rewrite lookup_omo_wr_event Homol3 omo_append_w_write_op Homol1'.
    have EQ2 : lookup_omo omol3 (wr_event 1) = Some 0 by rewrite lookup_omo_wr_event Homol3 omo_append_w_write_op Homol1'.
    eapply lookup_omo_inj in EQ2 as INJ; [|exact OMO_GOOD|exact EQ1]. inversion INJ. }
  iDestruct "n_1↦" as "[n_1↦ n_1↦']".
  iDestruct (OmoSnapOmo_get with "Ml1●") as "#OMOl3◯".
  iDestruct ("Close" with "[Ml1● omol1↦ Hgen1 n_1↦']") as "AllNodes3".
  { repeat iExists _. iFrame "HMl1 enqid1✓eVenq1". iFrame. iSplitR; [done|]. iSplitL "omol1↦"; [eauto with iFrame|].
    iExists eVl2. iFrame "e0✓eVl0". iSplit; [by rewrite eVl2EV|]. iRight.
    iExists (length El1'),eVln3,enqId,γln,γsn,#v,n,egV'. iExists V3. subst omol3. rewrite omo_append_w_write_op.
    rewrite (Nat.sub_add 1 (length CL3)); [|by destruct CL3; simpl; try lia].
    iDestruct (view_at_mono_2 _ V3 with "Mn◯") as "Mn◯@V3". { clear -LeV2V3. subst V2''. solve_lat. }
    iFrame "#". iSplit; last iSplit; try done.
    - iPureIntro. split_and!; [|done|by rewrite eVln3EV]. rewrite Homol1'. clear. by simplify_list_eq.
    - iExists _. iDestruct (view_at_mono_2 _ V3 with "n_1↦'") as "n_1↦"; [clear -LeV2V3; solve_lat|iFrame]. }

  iAssert (AllNodes γg γcl CL3')%I with "[Mn● omon↦ AllNodes3]" as "AllNodes3".
  { subst CL3'. rewrite /AllNodes big_sepL_snoc. iFrame.
    repeat iExists _. iFrame "HMn enqId✓egV'". iFrame "Mn●". iSplitR; [done|]. iSplitL.
    { iDestruct (view_at_intro with "omon↦") as (?) "[_ omon↦]". iExists _. rewrite shift_0. iFrame "omon↦". }
    iSplit; last first.
    { iPureIntro. exists v. split_and!; try done. lia. }
    iExists eVn0. iFrame "en0✓eVn0". iSplit; [by rewrite eVn0EV|]. by iLeft. }

  iAssert (AllPrevLinks γg γcl CL3')%I with "[-]" as "#AllPrevLinks3'".
  { subst CL3'. rewrite /AllPrevLinks big_sepL_snoc. iFrame "AllPrevLinks3".
    replace (length CL3) with (S (length CL3 - 1)); last first.
    { destruct CL3; [done|]. rewrite cons_length /=. lia. }
    replace (S (length CL3 - 1) - 1) with (length CL3 - 1) by lia.
    repeat iExists _. iFrame "CL@gen1 enqid1≤enqId OMOl3◯". iSplit; [done|].
    iPureIntro. subst omol3. rewrite omo_append_w_length omo_write_op_length Hgen1. lia. }

  set omo3' := omo_append_w omo3 enqId [].
  iAssert (HeadLastMsg γg γh γs3 γcl (omo_write_op omo3') (omo_write_op omoh3) CL3')%I with "[BIG1 WCOMMITn]" as "HeadLastMsg3".
  { repeat iExists _. iFrame "deqid↦eh deqid↪st' eh✓eVh CLh◯ M''◯ M''_CLh MAXgen_deqid BIG1".
    iSplitR; [done|].
    have Hgen' : omo_write_op omo3' !! gen = Some deqid.
    { subst omo3'. rewrite omo_append_w_write_op. by apply lookup_app_l_Some. }
    iPureIntro. split_and!; try done. subst omo3' CL3'. rewrite omo_append_w_write_op.
    rewrite (drop_app_le (omo_write_op omo3)); [|by apply lookup_lt_Some in Hgen; lia].
    do 4rewrite -fmap_drop. rewrite drop_app_le; [|lia].
    clear -Hst'dropdrop. simplify_list_eq. rewrite -Hst'dropdrop. simplify_list_eq. done. }

  iAssert (eView_Enq_exact γg M' CL3')%I with "[-]" as "#M'_CL3'".
  { iDestruct (mono_list_auth_lb_valid with "CL●3 CLp◯'") as %[_ SubCLp'CL3']. iSplit.
    - subst CL3'. rewrite big_sepL_forall. iIntros "%i %ninfo %Hi".
      destruct (decide (i = length CL3)) as [->|NEQ].
      + rewrite lookup_app_1_eq in Hi. inversion Hi. subst M'. iPureIntro. set_solver-.
      + apply (prefix_lookup_inv CLp') in Hi; [..|done]; last first.
        { rewrite lookup_lt_is_Some LENCLp''. apply lookup_lt_Some in Hi. rewrite app_length /= in Hi. lia. }
        iDestruct "Mp'_CLp'" as "[Mp'_CLp' _]". iDestruct (big_sepL_lookup with "Mp'_CLp'") as %INCL; [exact Hi|].
        iPureIntro. subst M'. clear -INCL. set_solver.
    - iApply big_sepS_intro. iIntros "%e %eIncl". subst M'.
      destruct (decide (e = enqId)) as [->|NEQ].
      + iModIntro. iExists egV'. iFrame "enqId✓egV'". subst egV' CL3'. simpl. iPureIntro. rewrite !fmap_app /=. set_solver-.
      + have INCL : e ∈ (M ∪ {[enqid1]} ∪ eVenq1.(eview) ∪ Mp) by clear -eIncl NEQ; set_solver.
        iDestruct "Mp'_CLp'" as "[_ Mp'_CLp']".
        iDestruct (big_sepS_elem_of _ _ e with "Mp'_CLp'") as (eV) "[e✓eV HeV]"; [clear -INCL; set_solver|].
        iModIntro. iExists eV. iFrame "e✓eV". destruct (eV.(type)); try done;
        iDestruct "HeV" as %HeV; iPureIntro; eapply elem_of_prefix; try done; do 4 apply fmap_prefix; done. }
  replace ({[length E3]} ∪ (M ∪ ({[enqid1]} ∪ eVenq1.(eview) ∪ Mp))) with M' by set_solver-.
  iAssert (OmoUB γg M' enqId)%I with "[-]" as "#MAXgen_enqId".
  { rewrite /OmoUB (big_sepS_forall _ M'). iIntros "%e %eIncl".
    iDestruct (OmoAuth_OmoEview_obj with "M●3 M◯''@V3") as %MIncl.
    specialize (MIncl _ eIncl).
    iDestruct (OmoEinfo_get' with "M●3") as (eV) "#e✓eV"; [exact MIncl|].
    iDestruct (OmoLe_get_append_w with "M●3 e✓eV") as "#e≤enqId". done. }

  iDestruct "M●3" as "[M●3 M●3']".
  iMod ("Commit" $! true V3 E3' M' with "[M●3']") as "HΦ".
  { iFrame "⊒V3". iSplitL; last iSplit.
    - repeat iExists _. iFrame.
    - repeat iExists _. iFrame "HM QInv M◯''@V3 E◯3 Mh◯@V3 Mt◯1'@V3 CL◯3 M'_CL3'". iPureIntro.
      unfold not. intros H. apply (f_equal length) in H. subst CL3'. rewrite app_length /= in H. lia.
    - iPureIntro. split_and!; try done. subst M'. set_solver-. }
  iMod ("Hclose" with "[-HΦ]") as "_".
  { repeat iExists _. iFrame "HM M●3 AllPrevLinks3' AllTailMsg3". iFrame. iNext. iSplitL.
    - subst CL3'. rewrite /EnqSeen big_sepL_snoc. iFrame "EnqSeen3". iExists (CL3 ++ [(enqId, γln, γsn, #v, n)]),egV',M'. simpl.
      replace ({[enqId]} ∪ M' ∪ M') with M' by set_solver-.
      iFrame "CL◯3 enqId✓egV' MAXgen_enqId M◯''@V3 M'_CL3'". iPureIntro. rewrite app_length /=. done.
    - rewrite big_sepL_singleton. by subst egV'. }

  iModIntro. wp_pures. rewrite -[Z.to_nat 1]/(1%nat). wp_bind (casʳᵉˡ(_, _, _))%E.

  (* Inv access 4 *)
  iInv "QInv" as (E4) ">H" "Hclose".
  iDestruct "H" as (?? γs4 ???? Eh4 Et4 omo4)
    "(%omoh4 & %omot4 & %stlist4 & %moh4 & %mot4 & %CL4 & %Mono4 & HM' & M●4 & Mh●4 & Mt●4 & CL●4 & omoh↦4 & [%Vbt4 omot↦4] & H)".
  iDestruct "H" as "(AllNodes4 & AllPrevLinks4 & AllHeadMsg4 & HeadLastMsg4 & #AllTailMsg4 & MONO4 & EnqSeen4 & AllEvents4)".
  simplify_meta6 with "HM' HM". iClear "HM'".
  iDestruct (OmoAuth_OmoSnapOmo with "Mt●4 OMOt1◯") as %[_ LEomot1wr].

  wp_apply (append_only_loc_cas_only_cas_live_loc _ _ _ _ _ _ _ ∅ _ _ _ l1 n _ ∅
    with "[$Mt●4 $Mt◯ $omot↦4 $⊒V3]"); try done; [solve_ndisj|..].

  iIntros (b4 et4 gent4 vt4 Vt4 V4 mot4' omot4' eVt4 eVtn4)
    "(Pures & #MAXgen_et4 & #et4✓eVt4 & #etn4✓eVtn4 & Mt●4 & #⊒V4 & #Mt◯4@V4 & omot↦4 & CASE)".
  iDestruct "Pures" as %(Eqgent4 & eVt4EV & LeV3V4).

  iAssert (AllTailMsg γg γt γcl (omo_write_op omot4'))%I with "[-]" as "#AllTailMsg4'".
  { iDestruct "CASE" as "[(Pures & _) | [Pures sVw3]]".
    - (* CAS failed, nothing to update *)
      iDestruct "Pures" as %(-> & NEq & -> & Homot4' & eVtn4EV & eVtn4SYNC).
      subst omot4'. rewrite omo_insert_r_write_op. done.
    - (* CAS success *)
      iDestruct "Pures" as %(-> & -> & ->).
      iDestruct "sVw3" as (Vw4 (Eqmot4' & Homot4' & eVtn4EV & eVtn4SYNC & LeVt4Vw4 & NEqVt4Vw4 & NLeV4Vt4 & NEqV3V4 & LEV4Vw4)) "_".
      subst omot4'. rewrite omo_append_w_write_op /AllTailMsg big_sepL_snoc. iFrame "AllTailMsg4".
      have LeV2'Vw4 : V2' ⊑ Vw4 by clear -LeV2V3 LeV3V4 LEV4Vw4; solve_lat.
      iExists eVtn4,(length CL3),enqId,γln,γsn,#v,n,Vw4. iExists egV'. iFrame "#". iPureIntro. rewrite eVtn4EV. split; [done|].
      subst egV'. simpl. clear -LeV3V4 LEV4Vw4. solve_lat. }

  iMod ("Hclose" with "[-HΦ]") as "_".
  { repeat iExists _. iFrame "HM AllTailMsg4'". iFrame. eauto with iFrame. }
  iModIntro. wp_pures. by iApply "HΦ".
Qed.

Lemma enqueue_spec :
  enqueue_spec' enqueue QueueLocal QueueInv.
Proof.
  intros N DISJ q tid γg E0 M0 V0 z LTz. iIntros "#⊒V0 #M◯0" (Φ) "AU".
  iLöb as "IH". wp_lam.
  awp_apply (try_enq_spec with "⊒V0 M◯0"); [eauto..|].
  iApply (aacc_aupd with "AU"); [done|].
  iIntros (E1) "QInv".
  iAaccIntro with "QInv"; [eauto with iFrame|].
  iIntros (b V1 E2 M1) "(QInv & #⊒V1 & #M◯1 & %CASE) !>".

  destruct b.
  - iRight. iExists V1,E2,M1. iFrame "QInv ⊒V1 M◯1". iSplit; [done|].
    iIntros "HΦ !> _". wp_pures. by iApply "HΦ".
  - iLeft. destruct CASE as [-> ->]. iFrame "QInv". iIntros "AU !> _". wp_if. by iApply "IH".
Qed.

Lemma try_deq_spec :
  try_deq_spec' try_deq QueueLocal QueueInv.
Proof.
  intros N DISJ q tid γg E0 M V0. iIntros "#⊒V0 #QueueLocal" (Φ) "AU".
  iDestruct "QueueLocal" as (?????? Mh Mt CL0) "(HM & QInv & E◯0 & M◯ & Mh◯ & Mt◯ & CL◯0 & M_CL0 & %CL0NEQ)".
  iCombine "M◯ Mt◯" as "MMt◯".
  iDestruct (view_at_intro_incl with "MMt◯ ⊒V0") as (V0') "(#⊒V0' & %LEV0V0' & [#M◯' #Mt◯'])".
  wp_lam. wp_op. rewrite -[Z.to_nat 0]/(0%nat). wp_bind (!ᵃᶜ #(q >> head))%E.

  (* Inv access 1 *)
  iInv "QInv" as (E1) ">H" "Hclose".
  iDestruct "H" as (?? γs1 ???? Eh1 Et1 omo1)
    "(%omoh1 & %omot1 & %stlist1 & %moh1 & %mot1 & %CL1 & %Mono1 & HM' & M●1 & Mh●1 & Mt●1 & CL●1 & (%Vbh1 & omoh↦1) & omot↦1 & H)".
  iDestruct "H" as "(AllNodes1 & AllPrevLinks1 & AllHeadMsg1 & H)".
  simplify_meta6 with "HM' HM". iClear "HM'".

  iDestruct (OmoSnapOmo_get with "Mh●1") as "#OMOh1◯".
  iDestruct (OmoEview_update with "M●1 M◯ Mh◯") as (Mh') "(M●1 & #Mh◯' & M⊢Mh' & %SubMhMh')".
  wp_apply (append_only_loc_acquire_read with "[$Mh●1 $Mh◯' $omoh↦1 $⊒V0']"); [solve_ndisj|].
  iIntros (eh1 genh1 vh1 Vh1 V1 eVh1 eVhn1)
    "(Pures & Mh●1 & _ & #MAXgen_eh1 & #eh1✓eVh1 & #ehn1✓eVhn1 & #eh1=ehn1 & #⊒V1 & #Mh◯1' & omoh↦1)".
  iDestruct "Pures" as %(Eqgenh1 & eVh1EV & LEV0'Vh1V1 & eVhn1EV & eVhn1SYNC).
  iDestruct (big_sepL_lookup with "AllHeadMsg1") as "#HMsg_eh1"; [exact Eqgenh1|].
  iDestruct "HMsg_eh1" as (deqid1 eVh1' enqid1 γl1 γsl1 vl1 l1 Vh1' st1 ?) "(eh1✓eVh1' & _ & _ & _ & _ & CL@genh1 & %eVh1'EV & _)".
  iDestruct (OmoEinfo_agree with "eh1✓eVh1 eh1✓eVh1'") as %<-.
  rewrite eVh1EV in eVh1'EV. inversion eVh1'EV. subst vh1 Vh1'. clear eVh1'EV st1 deqid1 Ml. iClear "eh1✓eVh1'".

  iMod ("Hclose" with "[-AU M⊢Mh']") as "_".
  { iExists E1. do 7 iExists _. iExists (Eh1 ++ [eVhn1]),_,_,(omo_insert_r omoh1 genh1 (length Eh1)),_,_,_,_. iExists _,_.
    rewrite omo_insert_r_write_op. iFrame "H AllHeadMsg1 HM". iFrame "∗". eauto with iFrame. }

  iModIntro. wp_pures. rewrite -[Z.to_nat 0]/(0%nat). wp_bind (!ᵃᶜ #(l1 >> 0))%E.

  (* Inv access 2 *)
  iInv "QInv" as (E2) ">H" "Hclose".
  iDestruct "H" as (?? γs2 ???? Eh2 Et2 omo2)
    "(%omoh2 & %omot2 & %stlist2 & %moh2 & %mot2 & %CL2 & %Mono2 & HM' & M●2 & Mh●2 & Mt●2 & CL●2 & (%Vbh2 & omoh↦2) & omot↦2 & H)".
  iDestruct "H" as "(AllNodes2 & #AllPrevLinks2 & AllHeadMsg2 & H)".
  simplify_meta6 with "HM' HM". iClear "HM'".

  iDestruct (OmoAuth_OmoSnapOmo with "Mh●2 OMOh1◯") as %[_ LEomoh2wr].
  iDestruct (big_sepL_lookup with "AllHeadMsg2") as "#HMsg_eh2"; [by eapply prefix_lookup_Some in Eqgenh1|].
  iDestruct "HMsg_eh2" as (deqid1 eVh1' enqid1' γl1' γsl1' vl1' l1' Vh1' st1 Ml1)
    "(eh1✓eVh1' & deqid1↦eh1 & MONO✓deqid1 & _ & deqid1↪st1 & CL@genh1' & %eVh1'EV & Ml1◯A & Hst1)".
  iDestruct (OmoEinfo_agree with "eh1✓eVh1 eh1✓eVh1'") as %<-.
  rewrite eVh1EV in eVh1'EV. inversion eVh1'EV. subst l1' Vh1'. clear eVh1'EV.
  iDestruct (mono_list_idx_agree with "CL@genh1 CL@genh1'") as %[[[[<- <-]%pair_inj <-]%pair_inj <-]%pair_inj _]%pair_inj.
  iClear "CL@genh1'".

  iDestruct (view_at_mono_2 _ V1 with "Ml1◯A") as "#Ml1◯A'"; [solve_lat|].
  iDestruct (view_at_elim with "⊒V1 Ml1◯A'") as "#Ml1◯".

  iDestruct (mono_list_auth_idx_lookup with "CL●2 CL@genh1") as %HCL2genh1.
  iDestruct (big_sepL_lookup_acc with "AllNodes2") as "[AllNodesInner AllNodesClose]"; [exact HCL2genh1|].
  iDestruct "AllNodesInner" as (? eVenq1 ???? El1 omol1 mol1) "(%Hninfo & #HMl1 & Ml1● & #enqid1✓eVenq1 & [%Vbl1 omol1↦] & Fieldl1 & Hgenh1)".
  inversion Hninfo. subst enqid γl γsl v l. clear Hninfo.
  iDestruct (OmoEview_update with "M●2 M◯ Ml1◯") as (Ml1') "(M●2 & #Ml1◯' & M⊢Ml1' & %SubMl1Ml1')".
  iDestruct (OmoSnapOmo_get with "Ml1●") as "#OMOl1◯".

  wp_apply (append_only_loc_acquire_read with "[$Ml1● $Ml1◯' $omol1↦ $⊒V1]"); [solve_ndisj|].
  iIntros (el1 genl1 vl1' Vl1 V2 eVl1 eVl1n)
    "(Pures & Ml1● & RCOMMIT & #MAXgen_el1 & #el1✓eVl1 & #el1n✓eVl1n & #el1=el1n & #⊒V2 & #Ml1◯'' & omol1↦)".
  iDestruct "Pures" as %(Hgenl1 & eVl1EV & LEV1Vl1'V2 & eVl1nEV & eVl1nSYNC).

  destruct genl1.
  { (* Read None value from next field. [EmpDeq] case *)
    iAssert (⌜ st1 = [] ∧ vl1' = #0 ∧ el1 = 0 ⌝)%I with "[Ml1● Fieldl1]" as %(-> & -> & ->).
    { iDestruct "Fieldl1" as (eVl0) "(#e0✓eVl0 & %eVl0EV & CASE)".
      destruct st1.
      - iAssert (⌜ el1 = 0 ⌝)%I with "[CASE]" as %->.
        { by iDestruct "CASE" as "[%Homol1|(%&%&%&%&%&%&%&%&%& [%Homol1 _] & _)]";
          rewrite Homol1 in Hgenl1; inversion Hgenl1. }
        iDestruct (OmoEinfo_agree with "e0✓eVl0 el1✓eVl1") as %<-.
        rewrite eVl1EV /= in eVl0EV. by subst vl1'.
      - iDestruct "Hst1" as (???????) "(OMOl1◯' & _ & [-> %Homol1'])".
        iDestruct (OmoAuth_OmoSnapOmo with "Ml1● OMOl1◯'") as %[_ LEomol1wr].
        iDestruct "CASE" as "[%Homol1|CASE2]".
        + rewrite omo_insert_r_write_op Homol1 Homol1' in LEomol1wr.
          apply prefix_length in LEomol1wr. simpl in *. lia.
        + iDestruct "CASE2" as (?????????) "[(%Homol1 & %NEQ & _) _]".
          rewrite omo_insert_r_write_op Homol1 Homol1' in LEomol1wr.
          rewrite Homol1 /= in Hgenl1. inversion Hgenl1. subst el1. clear Hgenl1.
          have EQ : el = el0; [|subst el0].
          { have Lookup : [0; el] !! 1 = Some el by done.
            eapply prefix_lookup_Some in Lookup; [|exact LEomol1wr]. by inversion Lookup. }
          iDestruct (big_sepS_elem_of _ _ el with "MAXgen_el1") as "#el≤e0"; [set_solver|].
          set omol1n := omo_insert_r omol1 0 (length El1).
          have Lookup1 : lookup_omo omol1n (wr_event 0) = Some 0 by rewrite lookup_omo_wr_event omo_insert_r_write_op Homol1.
          have Lookup2 : lookup_omo omol1n (wr_event 1) = Some el by rewrite lookup_omo_wr_event omo_insert_r_write_op Homol1.
          iDestruct (OmoLe_Le with "Ml1● el≤e0") as %LE; [done|done|simpl in *; lia]. }

    iAssert (OmoUB γg M deqid1)%I with "[-]" as "#MAXgen_deqid1".
    { iApply big_sepS_forall. iIntros "%e %eM".
      iDestruct (OmoAuth_OmoEview with "M●2 M◯") as %MIncl.
      specialize (MIncl _ eM) as [eV He].
      iDestruct "H" as "(_ & _ & MONO2 & #EnqSeen2 & #AllEvents2)".
      iDestruct (big_sepL_lookup with "AllEvents2") as "eInfo"; [exact He|].
      destruct (eV.(type)) eqn:HeVev.
      - iAssert (∃ gen γl γsl v l, ⌜ CL0 !! gen = Some (e, γl, γsl, v, l) ⌝)%I with "[-]" as (????) "(% & %HCL0gen)".
        { iDestruct "M_CL0" as "[M_CL0 M_CL0']".
          iDestruct (big_sepS_elem_of with "M_CL0'") as (eV0) "[e✓eV0 HeV0]"; [exact eM|].
          iDestruct (OmoAuth_OmoEinfo with "M●2 e✓eV0") as %He'.
          rewrite He in He'. inversion He'. subst eV0. clear He'. rewrite HeVev.
          iDestruct "HeV0" as %eIn. rewrite elem_of_list_lookup in eIn.
          destruct eIn as [gen Hgen]. rewrite !list_lookup_fmap in Hgen.
          destruct (CL0 !! gen) eqn:Heq; [|done].
          destruct p as [[[[p γl] γsl] v'] l]. inversion Hgen. subst p.
          iPureIntro. by exists gen, γl, γsl, v', l. }
        iDestruct (mono_list_auth_lb_valid with "CL●2 CL◯0") as %[_ LECL0CL2].
        apply (prefix_lookup_Some _ CL2) in HCL0gen as HCL2gen; [|done].
        destruct (le_lt_dec gen genh1) as [LE|LT].
        { iApply (gen_le_enq_deq with "AllHeadMsg2 deqid1↦eh1 MONO✓deqid1 Mh●2 MONO2 CL●2"); try done.
          by eapply prefix_lookup_Some in Eqgenh1. }

        have [ninfo Hlookup] : is_Some (CL0 !! (genh1 + 1)).
        { rewrite lookup_lt_is_Some. apply lookup_lt_Some in HCL0gen. lia. }
        destruct ninfo as [[[[e' γl'] γsl'] v'] l'].
        iAssert (∃ omol', OmoSnapOmo γl1 γsl1 omol' ∗ ⌜ length omol' = 2 ⌝)%I with "[-]" as (?) "[#OMOl1◯n %LEN]".
        { iDestruct (big_sepL_lookup with "AllPrevLinks2") as "Info"; [by eapply prefix_lookup_Some in Hlookup|].
          replace (genh1 + 1) with (S genh1) by lia.
          iDestruct "Info" as (??????????) "(%omol' & _ & CL@genh1' & _ & Ml1◯n & %LEN)".
          iDestruct (mono_list_idx_agree with "CL@genh1 CL@genh1'") as %[[[[<- <-]%pair_inj <-]%pair_inj <-]%pair_inj <-]%pair_inj.
          iExists omol'. by iFrame "Ml1◯n". }

        iDestruct "Fieldl1" as (eVl0) "(_ & _ & [%Homol1|CASE2])".
        { iDestruct (OmoAuth_OmoSnapOmo with "Ml1● OMOl1◯n") as %[_ LE].
          rewrite omo_insert_r_write_op Homol1 in LE. apply prefix_length in LE.
          rewrite -omo_write_op_length LEN /= in LE. lia. }

        iDestruct "CASE2" as (?????????) "((%Homol1 & %NEQ & _) & _ & #CL@Sgenh1 & #el✓eVl & _ & _ & #enqid'↦el & #enqid'⊒el & _)".
        iDestruct (mono_list_auth_idx_lookup with "CL●2 CL@Sgenh1") as %Hlookup'.
        apply (prefix_lookup_Some _ CL2) in Hlookup as HCL2lookup; [|done].
        rewrite HCL2lookup in Hlookup'. inversion Hlookup'. subst enqid' γl'0 γsl'0 v'0 l'0. clear Hlookup'.

        iAssert (⌜ el ∈ Ml1' ⌝)%I with "[-]" as %elMl1'.
        { iDestruct "M_CL0" as "[M_CL0 _]".
          iDestruct (big_sepL_lookup with "M_CL0") as %?; [exact Hlookup|].
          by iDestruct (OmoHb_HbIncluded with "enqid'⊒el M⊢Ml1'") as %?. }
        iDestruct (big_sepS_elem_of with "MAXgen_el1") as "#el≤e0"; [exact elMl1'|].
        iDestruct (OmoLe_Le _ _ _ _ _ _ (wr_event 1) (wr_event 0) with "Ml1● el≤e0") as %LE;
          try by rewrite lookup_omo_wr_event omo_insert_r_write_op Homol1. simpl in LE. lia.
      - iDestruct "eInfo" as (???) "(e⊒eh & e=e' & eh=eh' & e'↦eh' & MONO✓e')".
        iDestruct (OmoHb_HbIncluded with "e⊒eh M⊢Mh'") as %ehMh'; [done|].
        iDestruct (big_sepS_elem_of with "MAXgen_eh1") as "#eh≤eh1"; [exact ehMh'|].
        iDestruct (OmoEq_Le_trans with "[] eh≤eh1") as "eh'≤eh1"; [by iApply OmoEq_sym|].
        iApply OmoEq_Le_trans; [done|].
        iApply (CWMono_acc with "MONO2 MONO✓e' MONO✓deqid1 e'↦eh' deqid1↦eh1 eh'≤eh1").
      - iDestruct "eInfo" as (???) "(e⊒eh & e=e' & eh=eh' & e'↦eh' & MONO✓e')".
        iDestruct (OmoHb_HbIncluded with "e⊒eh M⊢Mh'") as %ehMh'; [done|].
        iDestruct (big_sepS_elem_of with "MAXgen_eh1") as "#eh≤eh1"; [exact ehMh'|].
        iDestruct (OmoEq_Le_trans with "[] eh≤eh1") as "eh'≤eh1"; [by iApply OmoEq_sym|].
        iApply OmoEq_Le_trans; [done|].
        iApply (CWMono_acc with "MONO2 MONO✓e' MONO✓deqid1 e'↦eh' deqid1↦eh1 eh'≤eh1"). }

    iMod "AU" as (E1') "[QInv' [_ Commit]]".
    iDestruct "QInv'" as (???) ">M●2'".
    iDestruct (OmoAuth_agree with "M●2 M●2'") as %(<- & <- & <- & <-).
    iCombine "M●2 M●2'" as "M●2".

    have LeV0V2 : V0 ⊑ V2 by solve_lat.
    set deqId := length E2.
    set M' := {[deqId]} ∪ M.
    set egV' := mkOmoEvent EmpDeq V2 M'.
    set E2' := E2 ++ [egV'].
    have SubE2E2' : E2 ⊑ E2' by apply prefix_app_r.

    have LEV1V2 : V1 ⊑ V2 by clear -LEV1Vl1'V2; solve_lat.
    iDestruct (view_at_mono_2 _ V2 with "M◯'") as "#M◯''"; [solve_lat|].
    iDestruct (view_at_mono_2 _ V2 with "Mh◯1'") as "#Mh◯1''"; [solve_lat|].

    iMod (OmoAuth_insert_ro with "M●2 M◯'' RCOMMIT deqid1↪st1 MAXgen_deqid1 []")
      as (gen) "(M●2 & #M◯n & #deqId↦el1n & #deqid1=deqId & #deqId✓egV' & _)".
    { have ? : step deqId egV' [] [] by subst; apply queue_step_EmpDeq; [done|set_solver-].
      iPureIntro. by split_and!. }
    iMod (OmoHb_new_1 with "M●2 deqId✓egV' ehn1✓eVhn1") as "[M●2 #deqId⊒ehn1]"; [rewrite eVhn1SYNC;solve_lat|].
    iDestruct (OmoHbToken_finish with "M●2") as "[M●2 M●2']".
    iDestruct (OmoSnapHistory_get with "M●2") as "#E◯2".

    iMod ("Commit" $! 0%Z V2 E2' EmpDeq M' with "[M●2']") as "HΦ".
    { iFrame "⊒V2". iSplitL; last iSplit.
      - repeat iExists _. iFrame "M●2'".
      - repeat iExists _. iFrame "HM".
        iDestruct (eView_Enq_exact_insert_nonenq with "M_CL0 deqId✓egV'") as "#M_CL0'"; [by subst egV'|by iFrame "∗#"].
      - simpl. iPureIntro. split_and!; try done. subst M'. set_solver-. }

    iMod ("Hclose" with "[-HΦ]") as "_".
    { iDestruct ("AllNodesClose" with "[Ml1● Fieldl1 Hgenh1 omol1↦]") as "AllNodes2".
      { iExists enqid1,eVenq1,γl1,γsl1,vl1,l1,(El1 ++ [eVl1n]),(omo_insert_r omol1 0 (length El1)). iExists mol1. rewrite omo_insert_r_write_op.
        iFrame "∗". iSplitR; [done|eauto with iFrame]. }
      iExists E2'. iExists γh,γt,γs2,γsh,γst,γcl,γm,Eh2. iExists Et2,(omo_insert_r omo2 _ _),omoh2,omot2,stlist2,moh2,mot2,CL2. iExists _.
      iDestruct "H" as "(HeadLastMsg & AllTailMsg & MONO & EnqSeen & AllEvents)".
      rewrite omo_insert_r_write_op. iFrame "∗".
      iFrame "HM AllPrevLinks2". iSplitL; [eauto with iFrame|].
      rewrite big_sepL_singleton. subst egV'. simpl. repeat iExists _. rewrite Nat.add_0_r.
      iFrame "deqId⊒ehn1 MONO✓deqid1 deqid1↦eh1". by iSplit; iApply OmoEq_sym. }
    iModIntro. wp_pures. by iApply "HΦ". }

  (* Successfully read nonnull value from next field. Prepare for CAS and close the invariant *)
  iDestruct (NextFieldInfo_dup with "Fieldl1") as "[Fieldl1 Fieldl1']".
  iDestruct "Fieldl1" as (eVl0) "(_ & _ & [%Homol1|CASE2])"; [by rewrite Homol1 /= in Hgenl1|clear eVl0].
  iDestruct "CASE2" as (el1' eVl1' enqid2 γl2 γsl2 vl2 l2 eVenq2 Vl1')
    "((%Homol1' & %NEQel1 & %eVl1EV') & #HMl2 & #CL@Sgenh1 & #el1'✓eVl1' & #enqid2✓eVenq2 & %EQeVenq2SYNC & #enqid2↦el2 & #enqid2⊒el2 & [_ #Ml2◯] & l2↦)".
  iAssert (⌜ el1' = el1 ∧ genl1 = 0 ∧ eVl1' = eVl1 ∧ vl1' = #l2 ∧ Vl1' = Vl1 ⌝)%I with "[-]" as %(-> & -> & -> & -> & ->).
  { rewrite Homol1' /= in Hgenl1. destruct genl1; [|done]. inversion Hgenl1. subst el1'.
    iDestruct (OmoEinfo_agree with "el1✓eVl1 el1'✓eVl1'") as %<-.
    rewrite eVl1EV in eVl1EV'. by inversion eVl1EV'. }

  iDestruct ("AllNodesClose" with "[Hgenh1 Fieldl1' Ml1● omol1↦]") as "AllNodes2".
  { iExists enqid1,eVenq1,γl1,γsl1,vl1,l1,(El1 ++ [eVl1n]),(omo_insert_r omol1 1 (length El1)). iExists mol1.
      rewrite omo_insert_r_write_op. iFrame "∗". iSplitR; [done|eauto with iFrame]. }

  iDestruct (mono_list_auth_idx_lookup with "CL●2 CL@Sgenh1") as %HCL2Sgenh1.
  iDestruct (big_sepL_lookup_acc with "AllNodes2") as "[AllNodesInner AllNodesClose]"; [exact HCL2Sgenh1|].
  iDestruct "AllNodesInner" as (?????????) "(%H1 & _ & H3 & H4 & H5 & H6 & (%zl2 & -> & %eVenq2EV & %GTzl2))". inversion H1. subst enqid γl γsl l.
  iDestruct (OmoEinfo_agree with "enqid2✓eVenq2 H4") as %<-.

  iMod ("Hclose" with "[-AU l2↦ M⊢Mh']") as "_".
  { iDestruct ("AllNodesClose" with "[H3 H4 H5 H6]") as "AllNodes2".
    { iExists enqid2,eVenq2,γl2,γsl2,#zl2,l2,El,omol. iExists mol. iFrame "∗". iFrame "HMl2". iSplit; [done|]. by iExists _. }
    iExists E2. iExists γh,γt,γs2,γsh,γst,γcl,γm,Eh2.
    iExists Et2,omo2,omoh2,omot2,stlist2,moh2,mot2,CL2. iExists _.
    iFrame "∗". iSplitR; [iFrame "HM"|eauto with iFrame]. }
  iModIntro. wp_pures. rewrite -[Z.to_nat 0]/(0%nat). wp_bind (casʳᵃ(_, _, _))%E.

  (* Inv access 3 *)
  iInv "QInv" as (E3) ">H" "Hclose".
  iDestruct "H" as (?? γs3 ???? Eh3 Et3 omo3)
    "(%omoh3 & %omot3 & %stlist3 & %moh3 & %mot3 & %CL3 & %Mono3 & HM' & M●3 & Mh●3 & Mt●3 & CL●3 & (%Vbh3 & omoh↦3) & omot↦3 & H)".
  iDestruct "H" as "(AllNodes3 & #AllPrevLinks3 & #AllHeadMsg3 & H)".
  simplify_meta6 with "HM' HM". iClear "HM'".
  iDestruct (OmoAuth_OmoSnapOmo with "Mh●3 OMOh1◯") as %[_ LEh1h3wr].

  wp_apply (append_only_loc_cas_only_cas_live_loc _ _ _ _ _ _ _ ∅ _ _ _ l1 l2 _ ∅
    with "[$Mh●3 $Mh◯' $omoh↦3 $⊒V2]"); try done; [solve_ndisj|..].

  iIntros (b3 eh3 genh3 vh3 Vh3 V3 moh3' omoh3' eVh3 eVhn3)
    "(Pures & #MAXgen_eh3 & #eh3✓eVh3 & #ehn3✓eVhn3 & Mh●3 & #⊒V3 & #Mh◯3 & omoh↦3 & CASE)".
  iDestruct "Pures" as %(Eqgenh3 & eVh3EV & LeV2V3).

  iDestruct "CASE" as "[(Pures & _) | [Pures sVw3]]".
  { (* CAS failed, FAIL_RACE case *)
    iDestruct "Pures" as %(-> & NEq & -> & Homoh3' & eVhn3EV & eVhn3SYNC).

    iMod ("Hclose" with "[-AU]") as "_".
    { iExists E3. iExists γh,γt,γs3,γsh,γst,γcl,γm,(Eh3 ++ [eVhn3]). iExists Et3,omo3,omoh3',omot3,stlist3,moh3,mot3,CL3. iExists _.
      subst omoh3'. rewrite omo_insert_r_write_op. iFrame "∗". iFrame "HM AllHeadMsg3". eauto with iFrame. }

    have LeV0V3 : V0 ⊑ V3 by solve_lat.

    iMod "AU" as (E3') "[QInv' [_ Commit]]".
    iDestruct "QInv'" as (???) ">M●3".
    iDestruct (OmoSnapHistory_get with "M●3") as "#E◯3".
    iMod ("Commit" $! FAIL_RACE V3 E3' dummy_qevt M with "[M●3]") as "HΦ".
    { iFrame "⊒V3". iSplitL; last iSplit; [..|done]. { repeat iExists _. iFrame. }
      have LEV0'V3 : V0' ⊑ V3 by clear -LEV0'Vh1V1 LEV1Vl1'V2 LeV2V3; solve_lat.
      iDestruct (view_at_mono_2 _ V3 with "M◯'") as "#M◯3'"; [done|].
      iDestruct (view_at_mono_2 _ V3 with "Mt◯'") as "#Mt◯''"; [done|].
      repeat iExists _. by iFrame "HM CL◯0 M_CL0 M◯3' QInv E◯3 Mh◯3 Mt◯''". }

    iModIntro. wp_pures. by iApply "HΦ". }

  iDestruct "Pures" as %(-> & -> & ->).
  iDestruct "sVw3" as (Vw3 (Eqmoh3' & Homoh3' & eVhn3EV & eVhn3SYNC & LeVh3V3 & NEqVh3V3 & NLeV3Vh3 & NEqV2V3 & ->))
    "(_ & _ & WCOMMIT)".
  iDestruct "H" as "(HeadLastMsg3 & AllTailMsg3 & MONO3 & #EnqSeen3 & #AllEvents3)".

  iDestruct (big_sepL_lookup with "AllHeadMsg3") as "HMsg_eh3"; [exact Eqgenh3|].
  iDestruct "HMsg_eh3" as (deqid3 eVh3' enqid3 γl3 γsl3 vl3 l3 Vh3' st3)
    "(%Ml3 & eh3✓eVh3' & deqid3↦eh3 & MONO✓deqid3 & _ & deqid3↪st3 & CL@genh3 & %eVh3'EV & Ml3◯A & Hst3)".
  iDestruct (OmoEinfo_agree with "eh3✓eVh3 eh3✓eVh3'") as %<-.
  rewrite eVh3EV in eVh3'EV. inversion eVh3'EV. subst l3 Vh3'. clear eVh3'EV.

  iDestruct (mono_list_auth_idx_lookup with "CL●3 CL@genh3") as %HCL3genh3.
  iDestruct (big_sepL_lookup_acc with "AllNodes3") as "[AllNodesInner AllNodesClose]"; [exact HCL3genh3|].
  iDestruct "AllNodesInner" as (? eVenq3 ???? El3 omol3 mol3) "(%Hninfo & #HMl1' & Ml1● & #enqid3✓eVenq3 & [%Vbl3 omol1↦] & Fieldl3 & Hgenh3)".
  inversion Hninfo. subst enqid γl γsl v l. clear Hninfo. simplify_meta4 with "HMl1' HMl1".

  iDestruct (NextFieldInfo_dup with "Fieldl3") as "[Fieldl3 Fieldl3']".
  iDestruct "Fieldl3" as (eVl0) "(_ & _ & [%Homol3|CASE2])".
  { iDestruct (OmoAuth_OmoSnapOmo with "Ml1● OMOl1◯") as %[_ LEwr].
    apply prefix_length in LEwr. rewrite Homol1' Homol3 /= in LEwr. lia. }
  iDestruct "CASE2" as (el3 eVl3 enqid3n γl3n γsl3n vl3n l3n eVenq3n Vl3n)
    "((%Homol3 & %NEQel3 & %eVl3EV') & #HMl3 & #CL@Sgenh3 & #el3✓eVl3 & #enqid3n✓eVenq3n & %EQeVenq3nSYNC & #enqid3n↦el3 & #enqid3n⊒el3 & [_ #Ml3n◯] & l3n↦)".

  iAssert (⌜ el3 = el1 ∧ eVl3 = eVl1 ∧ l3n = l2 ∧ Vl3n = Vl1 ⌝)%I with "[-]" as %(-> & -> & -> & ->).
  { iDestruct (OmoAuth_OmoSnapOmo with "Ml1● OMOl1◯") as %[_ LEwr].
    rewrite Homol1' Homol3 /= in LEwr.
    have Lookup : [0; el1] !! 1 = Some el1 by done.
    eapply prefix_lookup_Some in Lookup; [|exact LEwr].
    inversion Lookup. subst el3.
    iDestruct (OmoEinfo_agree with "el1✓eVl1 el3✓eVl3") as %<-.
    rewrite eVl1EV in eVl3EV'. by inversion eVl3EV'. }

  simplify_meta4 with "HMl3 HMl2".
  iDestruct (OmoEinfo_agree with "enqid2✓eVenq2 enqid3n✓eVenq3n") as %<-.

  (** 3 possible positions to insert a [Deq] event
      1. right after last [Deq] event
      2. right after matching [Enq] event
      3. right after latest [Enq] event that the thread has observed
      Among them, we should choose the latest event *)

  (* Candidate #1 *)
  iDestruct (OmoAuth_OmoCW_l' with "M●3 deqid3↦eh3") as %[eidx3 Heidx3].
  iDestruct (OmoAuth_OmoSnap with "M●3 deqid3↪st3") as %Hst3; [exact Heidx3|].
  set gen1 := gen_of eidx3.

  (* Candidate #2 *)
  iDestruct (OmoAuth_OmoEinfo' with "M●3 enqid3n✓eVenq3n") as %[eidx3n Heidx3n].
  set gen2 := gen_of eidx3n.

  (* Candidate #3 *)
  have [ninfo Hninfo] : is_Some (last CL0) by rewrite last_is_Some.
  destruct ninfo as [[[[enqidL γL] γsL] vL] lL].
  iAssert (∃ eVL, OmoEinfo γg enqidL eVL)%I with "[-]" as (eVL) "#enqidL✓eVL".
  { iDestruct "M_CL0" as "[M_CL0 M_CL0']".
    iDestruct (big_sepL_lookup with "M_CL0") as %INCL; [by rewrite last_lookup in Hninfo|].
    iDestruct (big_sepS_elem_of with "M_CL0'") as (eVL) "[#enqidL✓eVL _]"; [done|]. by iExists eVL. }
  iDestruct (OmoAuth_OmoEinfo' with "M●3 enqidL✓eVL") as %[eidxL HeidxL].
  set gen3 := gen_of eidxL.

  set gen := gen1 `max` gen2 `max` gen3.
  have LEgen1gen : gen1 ≤ gen by lia.
  have LEgen2gen : gen2 ≤ gen by lia.
  have LEgen3gen : gen3 ≤ gen by lia.

  iDestruct "HeadLastMsg3" as (eh3' deqid3' st3' gen1' CLh eVh3' M')
    "(#deqid3'↦eh3' & #deqid3'↪st3' & #eh3'✓eVh3' & #CLh◯ & %LENCLh & #M◯hlast & #M'_CLh & #MAXgen_deqid3' & (%Hgenh3' & %Hgen1' & %HstCL) & #Hst3')".
  have EQ : eh3' = eh3.
  { rewrite last_lookup in Hgenh3'.
    replace (Init.Nat.pred (length (omo_write_op omoh3))) with (length (omo_write_op omoh3) - 1)%nat in Hgenh3'; [|lia].
    rewrite -omo_write_op_length Eqgenh3 in Hgenh3'. by inversion Hgenh3'. } subst eh3'.
  iDestruct (OmoCW_agree_2 with "deqid3↦eh3 deqid3'↦eh3'") as %[_ <-].
  iDestruct (OmoSnap_agree with "deqid3↪st3 deqid3'↪st3'") as %<-.
  iDestruct (OmoEinfo_agree with "eh3✓eVh3 eh3'✓eVh3'") as %<-.
  iClear "deqid3'↦eh3' deqid3'↪st3' eh3'✓eVh3'".
  rewrite eVh3EV /=. iDestruct (OmoAuth_wf with "M●3") as %[OMO_GOOD3 _].
  rewrite -lookup_omo_wr_event in Hgen1'. specialize (lookup_omo_inj _ _ _ _ _ _ OMO_GOOD3 Heidx3 Hgen1') as H%(f_equal gen_of).
  simpl in H. subst gen1'.

  (* Every newer event is Enq v *)
  iAssert ([∗ list] e ∈ drop (gen1 + 1) (omo_write_op omo3), ∃ eV z, OmoEinfo γg e eV ∗ ⌜ eV.(type) = Enq z ⌝)%I with "[-]" as "#AllEnqs".
  { iClear "Hst3'". rewrite big_sepL_forall. iIntros "%g %e %Lookup".
    apply (f_equal ((!!) (length st3 + g)%nat)) in HstCL as HstCL'.
    rewrite lookup_app_r in HstCL'; [|by rewrite !fmap_length; lia].
    rewrite !fmap_length in HstCL'. replace (length st3 + g - length st3) with g in HstCL' by lia.
    rewrite !lookup_drop in HstCL', Lookup. rewrite Lookup in HstCL'. symmetry in HstCL'.
    set ng := length omoh3 + (length st3 + g). clear Hninfo.
    have [ninfo Hninfo] : is_Some (CL3 !! ng).
    { rewrite lookup_lt_is_Some. apply lookup_lt_Some in HstCL'. rewrite !fmap_length in HstCL'. done. }
    destruct ninfo as [[[[e' γl] γsl] v] l].
    rewrite !list_lookup_fmap Hninfo in HstCL'. inversion HstCL'. subst e'.
    iDestruct ("AllNodesClose" with "[Ml1● omol1↦ Hgenh3 Fieldl3']") as "AllNodes3".
    { repeat iExists _. iFrame "∗". iFrame "HMl1". iSplitR; [done|eauto with iFrame]. }

    iDestruct (big_sepL_lookup with "AllNodes3") as "Inner"; [exact Hninfo|].
    iDestruct "Inner" as (?????????) "(%EQ & _ & _ & #enqid✓eVenq & _ & _ & [%z (_ & %EV & _)])".
    inversion EQ. subst e γl0 γsl0 v0 l0.
    iExists eVenq. iFrame "enqid✓eVenq". iExists z. done. }

  (* Since all later events are [Enq], abstract state is monotone increasing *)
  iAssert (∀ g1 g2 st1 st2, ⌜ stlist3 !! g1 = Some st1 → stlist3 !! g2 = Some st2 →
      gen1 ≤ g1 → g1 ≤ g2 → st1 ⊑ st2 ∧ (length st2 = length st1 + (g2 - g1))%nat ⌝)%I with "[M●3]" as %LEst.
  { iIntros "%g1 %g2 %qu1 %qu2 %Lookup1 %Lookup2 %LE1 %LE2".
    iInduction LE2 as [|] "IH" forall (qu2 Lookup2 LE1).
    - rewrite Lookup1 in Lookup2. inversion Lookup2. iPureIntro. split; [done|lia].
    - replace (S m) with (m + 1) in Lookup2; [|lia].
      have [qu2p Hqu2p] : is_Some (stlist3 !! m).
      { rewrite lookup_lt_is_Some. apply lookup_lt_Some in Lookup2. lia. }
      have [e He] : is_Some (omo_write_op omo3 !! (m + 1)).
      { rewrite lookup_lt_is_Some -omo_write_op_length (omo_stlist_length E3 _ stlist3); [|done].
        apply lookup_lt_Some in Lookup2. lia. }
      have [eV HeV] : is_Some (E3 !! e).
      { eapply (lookup_omo_event_valid _ _ _ (wr_event (m + 1))); [done|].
        by rewrite lookup_omo_wr_event. }
      have STEP : step e eV qu2p qu2  by eapply omo_write_op_step.
      iAssert (∃ z, ⌜ eV.(type) = Enq z ⌝)%I with "[-]" as %[z EV].
      { iDestruct (big_sepL_lookup _ _ (m - gen1) with "AllEnqs") as (eV0 z) "[#e✓eV0 %NEQ]".
        { rewrite lookup_drop. replace (gen1 + 1 + (m - gen1)) with (m + 1); [done|lia]. }
        iDestruct (OmoAuth_OmoEinfo with "M●3 e✓eV0") as %HeV0.
        rewrite HeV in HeV0. inversion HeV0. subst eV0. by iExists z. }
      iDestruct ("IH" with "[] [] M●3") as %[LEqu1qu2p LENqu2pqu1]; try done.
      inversion STEP; [|by rewrite EV in DEQ|by rewrite EV in EMPDEQ].
      have ? : qu2p ⊑ qu2p ++ [(e, v, eV.(sync), eV.(eview))] by apply prefix_app_r.
      iPureIntro. split; [solve_lat|]. rewrite app_length LENqu2pqu1 /=. lia. }

  iAssert (∀ gen st', ⌜ gen1 ≤ gen → stlist3 !! gen = Some st' →
    st'.*1.*1.*1 ++ drop (gen + 1) (omo_write_op omo3) = drop (length omoh3) CL3.*1.*1.*1.*1 ⌝)%I with "[M●3]" as %Hstdropdrop.
  { subst gen. iIntros "%gen %st' %LE %Hgen".
    iInduction LE as [|gen'] "IH" forall (st' Hgen).
    - subst gen1. rewrite Hst3 in Hgen. inversion Hgen. subst st'. rewrite omo_write_op_length. done.
    - have [st'' Hgen'] : is_Some (stlist3 !! gen').
      { rewrite lookup_lt_is_Some. apply lookup_lt_Some in Hgen. lia. }
      iDestruct ("IH" with "[] M●3") as %IH; [done|].
      replace (S gen') with (gen' + 1) in Hgen by lia.
      have [e He] : is_Some (lookup_omo omo3 (wr_event (gen' + 1))).
      { rewrite lookup_omo_wr_event lookup_lt_is_Some. apply lookup_lt_Some in Hgen.
        rewrite -(omo_stlist_length _ _ _ OMO_GOOD3) in Hgen. rewrite -omo_write_op_length. done. }
      eapply lookup_omo_event_valid in He as HeV; [|done]. destruct HeV as [eV HeV].
      rewrite lookup_omo_wr_event in He.
      eapply omo_write_op_step in Hgen as STEP; try done.
      iDestruct (big_sepL_lookup _ _ (gen' - gen1) with "AllEnqs") as (eV' z) "[e✓eV' %EV]".
      { rewrite lookup_drop. replace (gen1 + 1 + (gen' - gen1)) with (gen' + 1) by lia. done. }
      iDestruct (OmoAuth_OmoEinfo with "M●3 e✓eV'") as %HeV'. rewrite HeV in HeV'. inversion HeV'. subst eV'.
      inversion STEP; [|by rewrite EV in DEQ|by rewrite EV in EMPDEQ].
      iPureIntro. rewrite (drop_S _ e) in IH; [|done]. rewrite -IH. clear. by simplify_list_eq. }

  set tst := (enqid2, zl2, eVenq2.(sync), eVenq2.(eview)).
  iAssert (∃ st', ⌜ stlist3 !! gen = Some (tst :: st') ⌝)%I with "[-]" as %[st' Hstgen].
  { have [st Hgen] : is_Some (stlist3 !! gen).
    { rewrite lookup_lt_is_Some. apply lookup_omo_lt_Some in Heidx3, Heidx3n, HeidxL.
      rewrite -(omo_stlist_length _ _ _ OMO_GOOD3). lia. }
    have ? : length omoh3 ≠ 0 by destruct omoh3.
    rewrite !(Nat.sub_add 1 (length omoh3)); [|lia].

    destruct st3.
    - simpl in HstCL.
      have Lookup : (drop (gen1 + 1) (omo_write_op omo3)) !! 0 = (drop (length (omo_write_op omoh3)) CL3.*1.*1.*1.*1) !! 0 by rewrite HstCL.
      rewrite !lookup_drop !Nat.add_0_r -omo_write_op_length in Lookup.
      iDestruct (mono_list_auth_idx_lookup with "CL●3 CL@Sgenh3") as %HCL3Sgenh3.
      do 4 rewrite list_lookup_fmap in Lookup. rewrite HCL3Sgenh3 /= in Lookup.

      have [st' Hst'] : is_Some (stlist3 !! (gen1 + 1)).
      { rewrite lookup_lt_is_Some. apply lookup_lt_Some in Lookup. rewrite -omo_write_op_length in Lookup.
        rewrite -(omo_stlist_length _ _ _ OMO_GOOD3). lia. }

      iDestruct (OmoAuth_OmoEinfo with "M●3 enqid3n✓eVenq3n") as %Henqid3n.
      eapply omo_write_op_step in Hst' as STEP; try done.
      inversion STEP; [|by rewrite eVenq2EV in EMPDEQ].
      rewrite app_nil_l in H3. subst st' u uV qu.
      rewrite eVenq2EV in ENQ. inversion ENQ. subst v.
      rewrite -lookup_omo_wr_event in Lookup.
      eapply lookup_omo_inj in OMO_GOOD3 as INJ; [|exact Heidx3n|exact Lookup]. subst eidx3n.
      have LE1 : gen1 ≤ gen1 + 1 by lia.
      have LE2 : gen1 + 1 ≤ gen by simpl in *; lia.
      specialize (LEst _ _ _ _ Hst' Hgen LE1 LE2) as [LEst' _].
      destruct st. { apply prefix_length in LEst'. simpl in *. lia. }
      have EQ : p = tst.
      { have Lookup' : [tst] !! 0 = Some tst by done.
        eapply prefix_lookup_Some in Lookup'; [|done]. by inversion Lookup'. }
      subst p. by iExists st.
    - iDestruct (big_sepL_lookup _ _ 0 with "Hst3'") as (????? eVenq2') "(enqid2✓eVenq2' & CL@Sgenh3' & (%EQ & %eVenq3nEV & %GT0))"; [done|].
      rewrite Nat.add_0_r -omo_write_op_length.
      iDestruct (mono_list_idx_agree with "CL@Sgenh3 CL@Sgenh3'") as %H.
      inversion H. subst enqid' γl' γsl' z' l'. subst p.
      iDestruct (OmoEinfo_agree with "enqid2✓eVenq2 enqid2✓eVenq2'") as %<-.

      have LE1 : gen1 ≤ gen1 by lia.
      specialize (LEst _ _ _ _ Hst3 Hgen LE1 LEgen1gen) as [LEst' _].
      destruct st. { apply prefix_length in LEst'. simpl in *. lia. }
      have EQ : p = tst.
      { have Lookup : (tst :: st3) !! 0 = Some tst by done.
        eapply prefix_lookup_Some in Lookup; [|done]. by inversion Lookup. }
      subst p. by iExists st. }

  iAssert (∀ g st, ⌜ stlist3 !! g = Some st ⌝ -∗ ⌜ gen1 ≤ g ⌝ -∗
              [∗ list] gen'↦state ∈ st,
                ∃ enqid' γl' γsl' (z' : Z) l' (eV' : omo_event qevent),
                OmoEinfo γg enqid' eV' ∗
                ⎡mono_list_idx_own γcl (length (omo_write_op omoh3) + gen') (enqid', γl', γsl', #z', l')⎤ ∗
                ⌜ state = (enqid', z', eV'.(sync), eV'.(eview))
                ∧ eV'.(type) = Enq z' ∧ (z' > 0)%Z ⌝)%I with "[-]" as "#Hst3n".
  { iIntros "%g %st %Hst %LE".
    iDestruct ("AllNodesClose" with "[-M●3 CL●3]") as "AllNodes3".
      { repeat iExists _. iFrame "∗". iFrame "HMl1". iSplitR; [done|eauto with iFrame]. }
    iInduction LE as [|g'] "IH" forall (st Hst).
    - rewrite Hst3 in Hst. inversion Hst. done.
    - clear st' Hstgen.
      have [st' Hst'] : is_Some (stlist3 !! g').
      { rewrite lookup_lt_is_Some. apply lookup_lt_Some in Hst. lia. }
      iDestruct ("IH" $! st' with "[] M●3 CL●3 AllNodes3") as "#IH'"; [done|].
      replace (S g') with (g' + 1) in Hst by lia.
      have [e He] : is_Some (lookup_omo omo3 (wr_event (g' + 1))).
      { rewrite lookup_omo_wr_event lookup_lt_is_Some. apply lookup_lt_Some in Hst.
        rewrite -(omo_stlist_length _ _ _ OMO_GOOD3) in Hst. rewrite -omo_write_op_length. done. }
      eapply lookup_omo_event_valid in He as HeV; [|done]. destruct HeV as [eV HeV].
      eapply omo_write_op_step in Hst as STEP; try done.
      iDestruct (big_sepL_lookup _ _ (g' - gen1) with "AllEnqs") as (eV' z) "[e✓eV' %EV]".
      { rewrite lookup_drop. replace (gen1 + 1 + (g' - gen1)) with (g' + 1) by lia. done. }
      iDestruct (OmoAuth_OmoEinfo with "M●3 e✓eV'") as %HeV'.
      rewrite HeV in HeV'. inversion HeV'. subst eV'.
      inversion STEP; [|by rewrite EV in DEQ|by rewrite EV in EMPDEQ].
      rewrite EV in ENQ. inversion ENQ. subst v.
      rewrite big_sepL_snoc. iFrame "IH'".

      have LE' : gen1 ≤ g' + 1 by lia.
      specialize (Hstdropdrop _ _ LE' Hst).
      apply (f_equal ((!!) (length st'))) in Hstdropdrop.
      rewrite lookup_app_l in Hstdropdrop; last first.
      { subst st. rewrite !fmap_length app_length /=. lia. }
      rewrite -H3 !list_lookup_fmap lookup_app_1_eq lookup_drop /= in Hstdropdrop. symmetry in Hstdropdrop.
      have [ninfo Hlookup] : is_Some (CL3 !! (length omoh3 + length st')).
      { rewrite lookup_lt_is_Some. apply lookup_lt_Some in Hstdropdrop.
        by rewrite !fmap_length in Hstdropdrop. }
      destruct ninfo as [[[[e' γl] γsl] v] l].
      rewrite !list_lookup_fmap Hlookup in Hstdropdrop. inversion Hstdropdrop. subst e'.

      iDestruct (big_sepL_lookup with "AllNodes3") as "Inner"; [exact Hlookup|].
      iDestruct "Inner" as (?????????) "(%EQ & _ & _ & #e✓eVenq & _ & _ & CASE)".
      inversion EQ. subst enqid γl0 γsl0 v0 l0.
      iDestruct (OmoEinfo_agree with "e✓eV' e✓eVenq") as %<-.
      destruct (length omoh3 + length st') eqn:Heq.
      { destruct omoh3; [done|]. rewrite cons_length in Heq. lia. }
      rewrite -Heq in Hlookup.
      iDestruct "CASE" as "(%z' & -> & %EV' & _)".
      rewrite EV in EV'. inversion EV'. subst z'.

      iExists e,γl,γsl,z,l,eV.
      rewrite -omo_write_op_length.
      iDestruct (mono_list_lb_own_get with "CL●3") as "#CL◯3".
      rewrite (@mono_list_idx_own_get _ _ _ γcl CL3 (length omoh3 + length st')); [|done].
      iFrame "#". iPureIntro. split_and!; try done. lia. }

  have LeV0'V2 : V0' ⊑ V2 by solve_lat.
  have LeV0'V3 : V0' ⊑ V3 by solve_lat.
  have LeV0V2 : V0 ⊑ V2 by solve_lat.
  have LeV0V3 : V0 ⊑ V3 by solve_lat.
  have LeVl1V2 : Vl1 ⊑ V2 by clear -LEV1Vl1'V2; solve_lat.
  have LeVl1V3 : Vl1 ⊑ V3 by solve_lat.

  iDestruct (view_at_mono_2 _ V3 with "M◯'") as "#M◯3"; [done|].
  iDestruct (view_at_mono_2 _ V3 with "M◯hlast") as "#M◯hlast'"; [solve_lat|].
  iDestruct (OmoEview_union_obj with "M◯3 M◯hlast'") as "#M◯3'".

  have ? : length omoh3 ≠ 0 by destruct omoh3.
  rewrite (Nat.sub_add 1 (length omoh3)); [|lia].
  iDestruct (mono_list_auth_idx_lookup with "CL●3 CL@Sgenh3") as %HCL3Sgenh3.
  iDestruct (big_sepL_lookup with "EnqSeen3")
    as (CLe eVenq2' M'') "(#CLe◯ & %LENCL' & #enqid2✓eVenq2' & #MAXgen_enqid2 & #M''◯ & #M''_CLe)"; [exact HCL3Sgenh3|].
  simpl. iDestruct (OmoEinfo_agree with "enqid2✓eVenq2 enqid2✓eVenq2'") as %<-.
  rewrite -EQeVenq2SYNC. iDestruct (view_at_mono_2 _ V3 with "M''◯") as "#M'◯V3"; [solve_lat|].
  iDestruct (OmoEview_union_obj with "M◯3' M'◯V3") as "#M◯3''".

  iDestruct (eView_Enq_exact_union with "M_CL0 M'_CLh CL◯0 CLh◯") as (CL0h) "(#MM'_CL0h & #CL0h◯ & %LENCL0h)".
  iDestruct (eView_Enq_exact_union with "MM'_CL0h M''_CLe CL0h◯ CLe◯") as (CL3') "(#M'''_CL3' & #CL3'◯ & %LENCL3')".
  rewrite LENCL0h in LENCL3'.

  iAssert (⌜ (length CL0 - length CLh = gen3 - gen1)%nat ⌝)%I with "[-]" as %Hgen3gen1.
  { destruct (le_lt_dec (length CL0) (length CLh)) as [LE|LT].
    - iDestruct (mono_list_auth_lb_valid with "CL●3 CL◯0") as %[_ SubCL0CL3].
      iDestruct (mono_list_auth_lb_valid with "CL●3 CLh◯") as %[_ SubCLhCL3].
      rewrite last_lookup in Hninfo.
      replace (Init.Nat.pred (length CL0)) with (length CL0 - 1) in Hninfo by lia.
      eapply prefix_lookup_Some in Hninfo as Hlookup; [|exact SubCL0CL3].
      eapply (prefix_lookup_inv CLh) in Hlookup; try done; last first.
      { rewrite lookup_lt_is_Some. apply lookup_lt_Some in Hninfo. lia. }
      iDestruct "M'_CLh" as "[M'_CLh _]".
      iDestruct (big_sepL_lookup with "M'_CLh") as "%enqidLM'"; [exact Hlookup|].
      iDestruct (big_sepS_elem_of _ _ enqidL with "MAXgen_deqid3'") as "enqidL≤deqid3"; [done|].
      iDestruct (OmoLe_Le with "M●3 enqidL≤deqid3") as %LE'; try done.
      subst gen1 gen3. iPureIntro. simpl in LE'. lia.
    - rewrite LENCLh in LT.
      set idx := length CL0 - 1 - length (omo_write_op omoh3).
      apply (f_equal ((!!) idx)) in HstCL.
      rewrite lookup_drop in HstCL. subst idx.
      replace (length (omo_write_op omoh3) + (length CL0 - 1 - length (omo_write_op omoh3))) with (length CL0 - 1) in HstCL by lia.
      iDestruct (mono_list_auth_lb_valid with "CL●3 CL◯0") as %[_ SubCL0CL3].
      have Lookup : CL3 !! (length CL0 - 1) = Some (enqidL, γL, γsL, vL, lL).
      { rewrite last_lookup in Hninfo.
        replace (Init.Nat.pred (length CL0)) with (length CL0 - 1) in Hninfo by lia.
        by eapply prefix_lookup_Some in Hninfo. }
      rewrite !list_lookup_fmap Lookup /= lookup_app_r in HstCL; [|by rewrite !fmap_length omo_write_op_length; lia].
      rewrite !fmap_length lookup_drop -lookup_omo_wr_event in HstCL.
      eapply lookup_omo_inj in HstCL as INJ; [|exact OMO_GOOD3|exact HeidxL].
      subst eidxL gen3 gen1. simpl. iPureIntro. rewrite LENCLh omo_write_op_length. lia. }

  iAssert (⌜ (length CLe - length CLh = gen2 - gen1)%nat ⌝)%I with "[-]" as %Hgen2gen1.
  { destruct (le_lt_dec (length CLe) (length CLh)) as [LE|LT].
    - iDestruct "M''_CLe" as "[M''_CLe _]".
      iDestruct (mono_list_auth_idx_lookup with "CL●3 CL@Sgenh3") as %Hlookup.
      iDestruct (mono_list_auth_lb_valid with "CL●3 CLh◯") as %[_ SubCLhCL3].

      iDestruct "M'_CLh" as "[M'_CLh _]".
      iDestruct (big_sepL_lookup with "M'_CLh") as "%enqid2M'".
      { apply (prefix_lookup_inv CLh) in Hlookup; try done.
        rewrite lookup_lt_is_Some. rewrite LENCL' in LE. lia. }
      iDestruct (big_sepS_elem_of _ _ enqid2 with "MAXgen_deqid3'") as "enqid2≤deqid3"; [done|].
      iDestruct (OmoLe_Le with "M●3 enqid2≤deqid3") as %LE'; try done.
      subst gen1 gen2. iPureIntro. simpl in LE'. lia.
    - rewrite LENCLh LENCL' omo_write_op_length in LT.
      destruct st3; [|simpl in LT; lia].

      simpl in HstCL.
      iDestruct (mono_list_auth_idx_lookup with "CL●3 CL@Sgenh3") as %Hlookup.
      apply (f_equal ((!!) 0)) in HstCL.
      rewrite !lookup_drop !Nat.add_0_r -omo_write_op_length in HstCL.
      do 4 rewrite list_lookup_fmap in HstCL.
      rewrite Hlookup -lookup_omo_wr_event in HstCL.
      eapply lookup_omo_inj in Heidx3n; try done.
      subst eidx3n gen1 gen2.
      rewrite LENCL' LENCLh. iPureIntro. rewrite omo_write_op_length /=. lia. }

  iAssert (⌜ (length CL3' = length omoh3 + length (tst :: st'))%nat ⌝)%I with "[-]" as %HCL3'LEN.
  { rewrite -omo_write_op_length in LENCLh. rewrite LENCLh in LENCL3'. rewrite LENCL3'.
    have LE1 : gen1 ≤ gen_of eidx3 by done.
    have LE2 : gen_of eidx3 ≤ gen by done.
    specialize (LEst _ _ _ _ Hst3 Hstgen LE1 LE2) as [_ EQlenst]. rewrite EQlenst LENCL'.
    replace ((length CL0 `max` (length omoh3 + length st3)) `max` (length omoh3 + 1))
      with ((length omoh3 + length st3) `max` ((length CL0) `max` (length omoh3 + 1))) by lia.
    have MAXeq : ∀ (a b : nat), a `max` b = a + (b - a) by intros; lia.
    rewrite (MAXeq (length omoh3 + length st3)). iPureIntro. lia. }

  set deqId := length E3.
  set Mdeq := {[deqId; enqid2]} ∪ eVenq2.(eview) ∪ M'' ∪ M' ∪ M.
  set egV' := mkOmoEvent (Deq zl2) V3 Mdeq.
  set E3' := E3 ++ [egV'].
  set omo3' := omo_insert_w omo3 (gen + 1) deqId [].
  have SubE3E3' : E3 ⊑ E3' by apply prefix_app_r.

  iAssert (⌜ OmoUBgen omo3 ({[enqid2]} ∪ eVenq2.(eview) ∪ M'') gen ⌝)%I with "[-]" as %MAXgenp1.
  { iDestruct (OmoUB_into_gen with "M●3 MAXgen_enqid2") as %MAXgen; [done|].
    apply (OmoUBgen_mono _ _ (gen_of eidx3n) gen) in MAXgen; [|lia]. done. }

  iAssert (⌜ OmoUBgen omo3 M' gen ⌝)%I with "[-]" as %MAXgenp2.
  { iDestruct (OmoUB_into_gen with "M●3 MAXgen_deqid3'") as %MAXgen; [done|].
    apply (OmoUBgen_mono _ _ (gen_of (wr_event (gen_of eidx3))) gen) in MAXgen; [|simpl;lia]. done. }

  iAssert (⌜ OmoUBgen omo3 M gen ⌝)%I with "[-]" as %MAXgenp3.
  { have [e He] : is_Some (omo_write_op omo3 !! gen).
    { rewrite lookup_lt_is_Some. apply lookup_lt_Some in Hstgen as LT.
      by rewrite -omo_write_op_length (omo_stlist_length _ _ _ OMO_GOOD3). }
    rewrite -lookup_omo_wr_event in He.
    eapply lookup_omo_event_valid in He as HeV; [|done]. destruct HeV as [eV HeV].

    iIntros "%e' %e'M". iDestruct (OmoAuth_wf with "M●3") as %[OMO_GOOD _].
    iDestruct (OmoAuth_OmoEview with "M●3 M◯") as %MIncl.
    apply MIncl in e'M as HeV'. eapply lookup_omo_surjective in HeV' as Heidx'; [|done].
    destruct Heidx' as [eidx' Heidx']. destruct HeV' as [eV' HeV'].
    iDestruct (big_sepL_lookup with "AllEvents3") as "e'Info"; [exact HeV'|].

    iAssert (⌜ (∀ z, eV'.(type) ≠ Enq z) → gen_of eidx' ≤ gen ⌝)%I with "[-]" as %condLE.
    { iIntros "%NEnq". iAssert (∃ e'' eh' eh'', OmoHb γg γh e' eh' ∗ OmoEq γg e' e'' ∗ OmoEq γh eh' eh'' ∗
      OmoCW γg γh e'' eh'' ∗ CWMonoValid γm e'')%I with "[-]" as (???) "(#e'⊒eh' & #e'=e'' & #eh'=eh'' & #e''↦eh'' & #MONO✓e'')".
      { destruct (eV'.(type)); try done. by specialize (NEnq v). }
      iDestruct (OmoHb_HbIncluded with "e'⊒eh' M⊢Mh'") as %eh'Mh'; [done|].
      iDestruct (big_sepS_elem_of with "MAXgen_eh3") as "#eh'≤eh3"; [exact eh'Mh'|].
      rewrite -lookup_omo_wr_event in Eqgenh3.
      iDestruct (CWMono_acc with "MONO3 MONO✓e'' MONO✓deqid3 e''↦eh'' deqid3↦eh3 []") as "#e''≤deqid3".
      { by iApply OmoEq_Le_trans; first iApply OmoEq_sym. }
      iDestruct (OmoEq_Le_trans with "e'=e'' e''≤deqid3") as "e'≤deqid3".
      iDestruct (OmoLe_Le with "M●3 e'≤deqid3") as %LE; try done. iPureIntro. simpl in LE. lia. }

    iExists eidx'. iSplit; [done|].
    destruct (eV'.(type)) eqn:HeV'EV; try (iPureIntro; by apply condLE).
    iDestruct "M_CL0" as "[M_CL0 M_CL0']".
    iDestruct (big_sepS_elem_of with "M_CL0'") as (eV'') "[e'✓eV'' HeV'']"; [exact e'M|].
    iDestruct (OmoAuth_OmoEinfo with "M●3 e'✓eV''") as %HeV''.
    rewrite HeV' in HeV''. inversion HeV''. subst eV''. clear HeV''.
    rewrite HeV'EV. iDestruct "HeV''" as %e'CL0.
    rewrite elem_of_list_lookup in e'CL0. destruct e'CL0 as [idx He'].
    rewrite !list_lookup_fmap in He'.
    destruct (CL0 !! idx) eqn:Hidx; [|done]. destruct p as [[[[enqid γl] γsl] vl] l].
    inversion He'. subst enqid.
    iDestruct (mono_list_auth_lb_valid with "CL●3 CL◯0") as %[_ SubCL0CL3].
    rewrite last_lookup in Hninfo.
    eapply prefix_lookup_Some in Hidx as Hidx', Hninfo; try exact SubCL0CL3.
    iDestruct (gen_le_enq_enq _ _ _ _ _ _ _ _ eidx' eidxL idx (Init.Nat.pred (length CL0)) with "AllPrevLinks3 M●3 CL●3") as %?;
      try done; [apply lookup_lt_Some in Hidx; lia|iPureIntro; lia]. }

  eapply OmoUBgen_union in MAXgenp2 as MAXgenp2'; [|exact MAXgenp1].
  eapply OmoUBgen_union in MAXgenp2' as MAXgen; [|exact MAXgenp3].

  iAssert (∀ len, ∃ stlist3', ⌜ interp_omo E3' ((deqId, []) :: take len (drop (gen + 1) omo3)) (tst :: st') stlist3' ∧ stlist3' !! 0 = Some st' ⌝)%I
    with "[M●3]" as %Hgengood.
  { iIntros "%len". iInduction len as [|] "IH".
    - iPureIntro. exists ([] ++ [st']). split; [|done]. rewrite -(app_nil_l [(deqId, [])]).
      apply (interp_omo_snoc E3' _ _ egV' _ _ ((enqid2, zl2, eVenq2.(sync), eVenq2.(eview)) :: st')). split_and!; try done.
      + subst E3' deqId. by rewrite lookup_app_1_eq.
      + constructor.
      + subst deqId egV' Mdeq. constructor; try done; simpl; [lia|by rewrite -EQeVenq3nSYNC|set_solver-].
    - iDestruct ("IH" with "M●3") as %[stlist3' [IH IHst']].
      destruct (le_lt_dec (length (drop (gen + 1) omo3)) len) as [LE|LT].
      { rewrite take_ge in IH; [|done]. iExists stlist3'. iPureIntro. rewrite take_ge; [|lia]. done. }
      have [ees Hlast] : is_Some ((drop (gen + 1) omo3) !! len) by rewrite lookup_lt_is_Some.
      destruct ees as [e es]. rewrite (take_S_r _ _ (e, es)); [|done]. rewrite lookup_drop in Hlast.
      specialize (omo_gen_info _ _ _ _ _ _ OMO_GOOD3 Hlast) as (eV & eeVs & st & EID_MATCH & EEVS_VALID & E3e & Lookup_stlist3 & Interp & ES).

      have [stp Hstp] : is_Some (stlist3 !! (gen + len)).
      { rewrite lookup_lt_is_Some. apply lookup_lt_Some in Lookup_stlist3. lia. }
      have STEP : step e eV stp st.
      { eapply omo_write_op_step; try done; replace (gen + len + 1) with (gen + 1 + len) by lia; try done.
        rewrite list_lookup_omo_destruct in Hlast. by destruct Hlast as [? _]. }

      inversion STEP.
      + apply interp_omo_length in IH as IHlen.
        have [stl Hstl] : is_Some (last stlist3') by rewrite last_is_Some; destruct stlist3'.
        destruct es as [|e' es']; last first.
        { (* es ≠ []: contradiction *)
          have LE2 : gen ≤ gen + 1 + len by lia.
          rewrite Forall_lookup in ES.
          have Lookup : (e' :: es') !! 0 = Some e' by done.
          specialize (ES _ _ Lookup) as [eV' (E3e' & STEP' & _)].
          inversion STEP'.
          - exfalso. apply (f_equal length) in H8. rewrite app_length /= in H8. lia.
          - exfalso. apply (f_equal length) in H8. rewrite cons_length /= in H8. lia.
          - exfalso. subst. apply (f_equal length) in H7. rewrite app_length /= in H7. lia. }

        iPureIntro. exists (stlist3' ++ [stl ++ [(e, v, eV.(sync), eV.(eview))]]).
        replace ((deqId, []) :: take len (drop (gen + 1) omo3) ++ [(e, [])]) with (((deqId, []) :: take len (drop (gen + 1) omo3)) ++ [(e, [])]); last first.
        { clear. by simplify_list_eq. }
        split; last first. { rewrite lookup_app_l; [done|]. destruct stlist3'; try done. simpl. lia. }

        eapply (interp_omo_snoc _ _ _ eV _ _ stl). split_and!; try done.
        * subst E3'. rewrite lookup_app_l; [done|]. by apply lookup_lt_Some in E3e.
        * by rewrite last_cons Hstl.
        * by apply queue_step_Enq.
      + iDestruct (big_sepL_lookup _ _ (gen + len - gen1) with "AllEnqs") as (eV' z) "[#e✓eV' %EV]".
        { rewrite lookup_drop. replace (gen1 + 1 + (gen + len - gen1)) with (gen + 1 + len) by lia.
          rewrite list_lookup_omo_destruct in Hlast. by destruct Hlast as [? _]. }
        iDestruct (OmoAuth_OmoEinfo with "M●3 e✓eV'") as %HeV'. rewrite /= E3e in HeV'. inversion HeV'. subst eV'.
        by rewrite DEQ in EV.
      + subst. have LE2 : gen ≤ gen + len by lia.
        specialize (LEst _ _ _ _ Hstgen Hstp LEgen1gen LE2) as [LEst' _]. apply prefix_length in LEst'. simpl in LEst'. lia. }

  specialize (Hgengood (length (drop (gen + 1) omo3))) as [stlist3' [Hstlist3' Hhdstlist3']].
  rewrite take_ge in Hstlist3'; [|done].

  iMod "AU" as (?) "[QInv' [_ Commit]]".
  iDestruct "QInv'" as (???) ">M●3'".
  iDestruct (OmoAuth_agree with "M●3 M●3'") as %(<- & <- & <- & <-).
  iCombine "M●3 M●3'" as "M●3".
  iDestruct (OmoSnapStates_get with "M●3") as "#STLIST3◯".
  iMod (OmoAuth_insert with "M●3 M◯3'' WCOMMIT []") as (γs3') "(M●3 & #M◯3''' & #deqId↦ehn3 & #deqId✓egV' & _)".
  { iPureIntro. split_and!; try done; subst egV' Mdeq deqId; simpl; try done; [set_solver-|].
    replace (M ∪ M' ∪ ({[enqid2]} ∪ eVenq2.(eview) ∪ M'')) with (M ∪ ({[enqid2]} ∪ eVenq2.(eview) ∪ M'' ∪ M')) by set_solver-. done. }
  iMod (OmoHb_new_1 with "M●3 deqId✓egV' ehn3✓eVhn3") as "[M●3 #deqId⊒ehn3]"; [rewrite eVhn3SYNC;solve_lat|].
  iDestruct (OmoHbToken_finish with "M●3") as "M●3".

  iDestruct (OmoLt_get _ _ _ _ _ _ eidx3 (wr_event (gen + 1)) with "M●3") as "#deqid3<deqId".
  { have Lookup : lookup_omo (take (gen1 + 1) omo3) eidx3 = Some deqid3 by rewrite lookup_omo_take; [done|lia].
    apply (omo_prefix_lookup_Some _ omo3') in Lookup; [done|].
    apply omo_insert_w_prefix; [apply omo_prefix_take|].
    rewrite take_length Nat.min_l; [lia|].
    apply lookup_omo_lt_Some in Heidx3. subst gen1. lia. }
  { have EQ : length (take (gen + 1) (omo_write_op omo3)) = gen + 1.
    { rewrite take_length -omo_write_op_length.
      apply lookup_lt_Some in Hstgen. rewrite -(omo_stlist_length _ _ _ OMO_GOOD3) in Hstgen. lia. }
    rewrite lookup_omo_wr_event omo_insert_w_write_op lookup_app_r; [|lia].
    rewrite EQ. replace (gen + 1 - (gen + 1)) with 0 by lia. done. } { simpl. lia. }
  iDestruct (OmoLe_get_from_Lt with "deqid3<deqId") as "deqid3≤deqId".
  iMod (@CWMono_insert_last loc_event _ _ _ _ (wr_event (length omoh3 - 1)%nat) _ _ _ _ _ _ omoh3
    with "MONO3 [Mh●3] MONO✓deqid3 deqid3↦eh3 deqId↦ehn3 deqid3≤deqId") as "(MONO3 & #MONO✓deqId & Mh●3)"; [|done|subst omoh3';iFrame|..].
  { rewrite lookup_omo_wr_event -Hgenh3' last_lookup -omo_write_op_length.
    replace (Init.Nat.pred (length omoh3)) with (length omoh3 - 1)%nat by lia. done. }
  iDestruct (OmoSnapHistory_get with "M●3") as "#E◯3".

  iDestruct ("AllNodesClose" with "[Ml1● omol1↦ Hgenh3 Fieldl3']") as "AllNodes3".
  { iExists enqid1,eVenq3,γl1,γsl1,vl1,l1,El3,omol3. iExists mol3. iFrame "∗".
    iFrame "HMl1 enqid3✓eVenq3". iSplit; [done|]. eauto with iFrame. }

  have HdeqId : lookup_omo (omo_insert_w omo3 (gen + 1) (length E3) []) (wr_event (gen + 1)) = Some (length E3).
  { rewrite lookup_omo_wr_event omo_insert_w_write_op.
    have EQ : length (take (gen + 1) (omo_write_op omo3)) = gen + 1.
    { rewrite take_length.
      have ? : gen + 1 ≤ length (omo_write_op omo3); [|lia].
      rewrite -omo_write_op_length. apply lookup_lt_Some in Hstgen. rewrite -(omo_stlist_length _ _ _ OMO_GOOD3) in Hstgen. lia. }
    rewrite lookup_app_r; [|lia].
    rewrite EQ. replace (gen + 1 - (gen + 1)) with 0 by lia. done. }

  iDestruct (OmoSnap_get _ _ _ _ _ _ _ (wr_event (gen + 1)) (gen + 1) with "M●3") as "#deqId↪st'"; try done.
  { have EQ : length (take (gen + 1) stlist3) = gen + 1.
    { rewrite take_length. apply lookup_lt_Some in Hstgen as LT.
      clear -LT. apply PeanoNat.Nat.min_l.
      have COMP : ∀ (a b : nat), a < b → a + 1 ≤ b by lia. by apply COMP. }
    rewrite lookup_app_r; [|lia]. rewrite EQ.
    replace (gen + 1 - (gen + 1)) with 0 by lia. done. }

  iAssert (AllHeadMsg γg γh γs3' γcl γm (omo_write_op omoh3'))%I with "[-]" as "#AllHeadMsg3'".
  { subst omoh3'. rewrite omo_append_w_write_op /AllHeadMsg big_sepL_snoc. iSplit.
    - rewrite (big_sepL_forall (AllHeadMsgInner γg γh γs3' γcl γm)). iIntros "%genh %eh %Lookup".
      iDestruct (big_sepL_lookup with "AllHeadMsg3") as "ehInfo"; [exact Lookup|].
      iDestruct "ehInfo" as (??????????) "(? & deqid↦eh & MONO✓deqid & ? & deqid↪st & ?)".
      iDestruct (OmoLe_get _ _ _ _ _ _ (wr_event genh) (wr_event (length omoh3 - 1)) with "Mh●3") as "#eh≤eh3".
      { rewrite lookup_omo_wr_event omo_append_w_write_op lookup_app_l; [done|]. by apply lookup_lt_Some in Lookup. }
      { rewrite lookup_omo_wr_event omo_append_w_write_op lookup_app_l; [done|]. by apply lookup_lt_Some in Eqgenh3. }
      { simpl. apply lookup_lt_Some in Lookup. rewrite -omo_write_op_length in Lookup. lia. }
      iDestruct (CWMono_acc with "MONO3 MONO✓deqid MONO✓deqid3 deqid↦eh deqid3↦eh3 eh≤eh3") as "#deqid≤deqid3".
      iDestruct (OmoLe_Lt_trans with "deqid≤deqid3 deqid3<deqId") as "deqid<deqId".
      iDestruct (OmoAuth_OmoCW_l' with "M●3 deqid↦eh") as %[eidx Heidx].
      iDestruct (OmoLt_Lt with "M●3 deqid<deqId") as %LT; try done.
      have Heidx' : lookup_omo omo3 eidx = Some deqid.
      { have NEQ : eidx ≠ wr_event (gen + 1) by unfold not; intros; subst; simpl in *; lia.
        have LEgen : gen + 1 ≤ length omo3.
        { apply lookup_lt_Some in Hstgen. rewrite -(omo_stlist_length _ _ _ OMO_GOOD3) in Hstgen. lia. }
        specialize (lookup_omo_before_insert_w _ _ _ _ _ Heidx NEQ LEgen) as [eidx' [Heidx' CASE]].
        rewrite decide_True in CASE; [|done]. by subst eidx'. }
      iDestruct (OmoSnapStates_OmoSnap with "STLIST3◯ deqid↪st") as %Hstlist3; [exact Heidx'|].
      iDestruct (OmoSnap_get _ _ _ _ _ _ _ eidx (gen_of eidx) with "M●3") as "#deqid↪st'"; try done.
      { rewrite lookup_app_l; [by rewrite lookup_take|].
        rewrite take_length. apply lookup_lt_Some in Hstlist3. simpl in *. lia. }
      repeat iExists _. iFrame "#".
    - iAssert (∃ Ml2, OmoAuth γg γs3' 1 (E3 ++ [egV']) omo3' (take (gen + 1) stlist3 ++ stlist3') _ ∗
                      ⎡mono_list_auth_own γcl 1 CL3⎤ ∗ AllNodes γg γcl CL3 ∗ @{V3} OmoEview γl2 Ml2 ∗
                      match st' with
                      | [] => emp
                      | _ => ∃ el omol2, OmoSnapOmo γl2 γsl2 omol2 ∗
                          ⌜ omo_write_op omol2 = [0; el] ∧ Ml2 = {[0; el]} ∧ is_Some (CL3 !! (length (omo_write_op omoh3) + 1)%nat) ⌝
                      end)%I with "[M●3 CL●3 AllNodes3]" as (Ml2 ) "(M●3 & CL●3 & AllNodes3 & #Ml2◯' & Hst')".
      { destruct st'.
        { iExists {[0]}. iDestruct (view_at_mono_2 _ V3 with "Ml3n◯") as "#Ml3n◯'"; [solve_lat|]. iFrame "M●3 CL●3 AllNodes3 Ml3n◯'". }
        specialize (Hstdropdrop _ _ LEgen1gen Hstgen).
        apply (f_equal ((!!) 1)) in Hstdropdrop. rewrite lookup_drop /= in Hstdropdrop. symmetry in Hstdropdrop. clear Hninfo.
        have [ninfo Hninfo] : is_Some (CL3 !! (length omoh3 + 1)).
        { rewrite lookup_lt_is_Some. apply lookup_lt_Some in Hstdropdrop. rewrite !fmap_length in Hstdropdrop. done. }
        iDestruct (big_sepL_lookup with "AllPrevLinks3") as "Info"; [exact Hninfo|].
        replace (length omoh3 + 1) with (S (length omoh3)) by lia.
        iDestruct "Info" as (??????????) "(%& %EQ & CL@Sgenh3' & _ & OMOl'◯ & %LEN)". clear enqid γl γsl v l EQ.

        iDestruct (mono_list_idx_agree with "CL@Sgenh3 CL@Sgenh3'") as %[[[[<- <-]%pair_inj <-]%pair_inj <-]%pair_inj <-]%pair_inj.
        iDestruct (big_sepL_lookup_acc with "AllNodes3") as "[Inner Close]"; [exact HCL3Sgenh3|].
        iDestruct "Inner" as (?????????) "(%EQ & H2 & Ml2● & H4 & H5 & Field & H7)".
        inversion EQ. subst enqid γl γsl v l. clear EQ.
        iDestruct (OmoAuth_OmoSnapOmo with "Ml2● OMOl'◯") as %[_ LEwr].
        iDestruct (NextFieldInfo_dup with "Field") as "[Field Field']".
        iDestruct "Field" as (?) "(_ & _ & [%EQ|CASE2])".
        { apply prefix_length in LEwr. rewrite EQ -omo_write_op_length LEN /= in LEwr. lia. }
        iDestruct "CASE2" as (?????????) "((%Hwr & _ & _) & _ & #CL@SSgenh3 & _ & #enqid'✓eVenq' & -> & _ & _ & [#Ml2◯' _] & _)".

        iDestruct (mono_list_auth_lb_valid with "CL●3 CL3'◯") as %[_ SubCL3'CL3].
        iDestruct (mono_list_auth_idx_lookup with "CL●3 CL@SSgenh3") as %Hlookup'.
        iDestruct "M'''_CL3'" as "[M'''_CL3' _]".
        iDestruct (big_sepL_lookup _ _ (length omoh3 + 1) with "M'''_CL3'") as %INCL.
        { eapply (prefix_lookup_inv CL3') in Hlookup'; try done.
          rewrite lookup_lt_is_Some HCL3'LEN /=. apply lookup_lt_Some in Hlookup'. lia. }
        iDestruct (OmoEinfo_OmoEview_obj with "enqid'✓eVenq' M◯3'''") as %LE; [clear -INCL; set_solver|].
        iDestruct (view_at_mono_2 _ V3 with "Ml2◯'") as "#Ml2◯''"; [done|].
        iDestruct (OmoSnapOmo_get with "Ml2●") as "#OMOl2◯".
        iDestruct ("Close" with "[-M●3 CL●3]") as "AllNodes3". { repeat iExists _. by iFrame. }
        iExists {[el;0]}. iFrame "M●3 CL●3 AllNodes3 Ml2◯''". iExists el,omol0. iFrame "OMOl2◯". iPureIntro. split_and!; try done.
        - set_solver-.
        - rewrite lookup_lt_is_Some -omo_write_op_length. apply lookup_lt_Some in Hlookup'. done. }

      iDestruct (OmoLe_get _ _ _ _ _ _ eidx3n _ enqid2 deqId with "M●3") as "#enqid2≤deqId".
      { have Lookup : lookup_omo (take (gen2 + 1) omo3) eidx3n = Some enqid2 by subst; rewrite lookup_omo_take; [|lia].
        apply (omo_prefix_lookup_Some _ (omo_insert_w omo3 (gen + 1) (length E3) [])) in Lookup; [done|].
        apply omo_insert_w_prefix; [apply omo_prefix_take|].
        rewrite take_length Nat.min_l; [lia|].
        apply lookup_omo_lt_Some in Heidx3n. subst gen2. lia. }
      { done. } { subst gen2. simpl. lia. }
      iExists deqId,eVhn3,enqid2,γl2,γsl2,#zl2,l2,V3. iExists st',Ml2.
      rewrite -omo_write_op_length. iFrame "#". iSplit. { iPureIntro. by rewrite eVhn3EV. }
      destruct st'; [done|].
      iDestruct "Hst'" as (el omol2) "[#OMOl2◯ (%Homol2 & %HMl2 & [%ninfo %Hninfo'])]".
      destruct ninfo as [[[[enqid' γl'] γsl'] v'] l'].
      iDestruct (mono_list_lb_own_get with "CL●3") as "#CL◯3".
      (* TODO: It seems [mono_list_idx_own_get] does not work well in vProp. Need fix *)
      rewrite (@mono_list_idx_own_get _ _ _ γcl CL3 (length omoh3 + 1)); [|done].
      repeat iExists _. iFrame "OMOl2◯ CL◯3". iPureIntro. split_and!; [|done]. subst Ml2. set_solver-. }

  iDestruct (OmoUB_from_gen with "M●3") as "#MAXgen_deqId".
  { done. } { eapply (OmoUBgen_insert_w _ _ gen (gen + 1)) in MAXgen; [done|lia]. } { simpl. lia. }
  iAssert (HeadLastMsg γg γh γs3' γcl (omo_write_op omo3') (omo_write_op omoh3') CL3)%I with "[]" as "HeadLastMsg3".
  { iExists (length Eh3),deqId,st',(gen + 1),CL3',eVhn3,_. rewrite eVhn3EV /=.
    replace (M ∪ ({[enqid2]} ∪ eVenq2.(eview) ∪ M'' ∪ M')) with (M ∪ M' ∪ ({[enqid2]} ∪ eVenq2.(eview) ∪ M'')) by set_solver-.
    iFrame "M◯3'' MAXgen_deqId M'''_CL3' deqId↦ehn3 ehn3✓eVhn3 CL3'◯ deqId↪st'".
    iSplitR; last iSplitR.
    - iPureIntro. subst omoh3'.
      rewrite HCL3'LEN omo_append_w_write_op app_length cons_length omo_write_op_length /=. lia.
    - iPureIntro. split_and!; try done; subst omoh3'.
      + by rewrite omo_append_w_write_op last_app.
      + specialize (Hstdropdrop _ _ LEgen1gen Hstgen). subst omo3'.
        rewrite omo_append_w_write_op omo_insert_w_write_op app_length -omo_write_op_length /=.
        have EQ : take (gen + 1) (omo_write_op omo3) ++ deqId :: drop (gen + 1) (omo_write_op omo3) =
                  (take (gen + 1) (omo_write_op omo3) ++ [deqId]) ++ drop (gen + 1) (omo_write_op omo3) by clear; simplify_list_eq.
        rewrite EQ. clear EQ.
        have EQ : gen + 1 + 1 = length (take (gen + 1) (omo_write_op omo3) ++ [deqId]).
        { rewrite app_length take_length /= Nat.min_l; [done|].
          rewrite -omo_write_op_length. apply lookup_lt_Some in Hstgen.
          rewrite -(omo_stlist_length _ _ _ OMO_GOOD3) in Hstgen. lia. }
        rewrite EQ drop_app. clear EQ.
        have EQ : CL3.*1.*1.*1.*1 !! (length omoh3) = Some enqid2.
        { apply (f_equal ((!!) 0)) in Hstdropdrop. by rewrite lookup_drop Nat.add_0_r /= in Hstdropdrop. }
        rewrite (drop_S CL3.*1.*1.*1.*1 tst.1.1.1) in Hstdropdrop; [|done].
        clear -Hstdropdrop. simplify_list_eq.
        replace (S (length omoh3)) with (length omoh3 + 1) in Hstdropdrop by lia. done.
    - iDestruct ("Hst3n" $! gen (tst :: st') with "[] []") as "Hst3n'"; try done.
      rewrite (big_sepL_forall _ st'). iIntros "%gen' %state %Hstate".
      iDestruct (big_sepL_lookup _ _ (gen' + 1) with "Hst3n'") as (??????) "(H1 & H2 & H3)".
      { replace (gen' + 1) with (S gen') by lia. by rewrite lookup_cons. }
      replace (length (omo_write_op omoh3) + (gen' + 1)) with (length (omo_write_op omoh3') + gen'); last first.
      { subst omoh3'. rewrite omo_append_w_write_op app_length /=. lia. }
      repeat iExists _. iFrame "#". }

  iDestruct "M●3" as "[M●3 M●3']".
  iMod ("Commit" $! zl2 V3 (E3 ++ [egV']) (Deq zl2) Mdeq with "[M●3']") as "HΦ".
  { iFrame "⊒V3". iSplitL; last iSplit.
    - repeat iExists _. iFrame.
    - repeat iExists _.
      iDestruct (eView_Enq_exact_insert_nonenq with "M'''_CL3' deqId✓egV'") as "#M'''_CL3''"; try by subst egV'.
      have EQ : Mdeq = {[length E3]} ∪ (M ∪ M' ∪ ({[enqid2]} ∪ eVenq2.(eview) ∪ M'')) by set_solver-.
      rewrite -!EQ. iFrame "HM QInv M◯3''' M'''_CL3''". iFrame "#". iPureIntro.
      destruct CL3'; [|done]. rewrite cons_length /= in HCL3'LEN. lia.
    - iPureIntro. split_and!; try done.
      rewrite decide_False; [|lia]. split_and!; try done; [set_solver-|].
      rewrite decide_False; [|lia]. split_and!; try done. lia. }

  iMod ("Hclose" with "[-l2↦ HΦ]") as "_".
  { iExists (E3 ++ [egV']). iExists γh,γt,γs3',γsh,γst,γcl,γm,(Eh3 ++ [eVhn3]).
    iExists Et3,(omo_insert_w omo3 (gen + 1) (length E3) []),omoh3',omot3,_,moh3',mot3,CL3. iExists _.
    subst omoh3'. rewrite omo_insert_w_write_op omo_append_w_write_op. iFrame "∗".
    iFrame "HM EnqSeen3 AllHeadMsg3' AllPrevLinks3". iSplitL "omoh↦3"; [eauto with iFrame|].
    iNext. rewrite /AllEvents big_sepL_snoc. iFrame "AllEvents3 HeadLastMsg3". repeat iExists _.
    iFrame "deqId⊒ehn3 deqId↦ehn3 MONO✓deqId". by iSplit; [iApply OmoEq_get_from_Einfo|iApply (@OmoEq_get_from_Einfo loc_event)]. }

  iModIntro. iDestruct "l2↦" as (?) "l2↦".
  iDestruct (view_at_mono_2 _ V3 with "l2↦") as "l2↦"; [solve_lat|].
  iDestruct (view_at_elim with "⊒V3 l2↦") as "l2↦".
  wp_pures. rewrite -[Z.to_nat 1]/(1%nat). wp_read. by iApply "HΦ".
Qed.

Lemma dequeue_spec :
  dequeue_spec' dequeue QueueLocal QueueInv.
Proof.
  intros N DISJ q tid γg E0 M0 V0. iIntros "#⊒V0 #M◯0" (Φ) "AU".
  iLöb as "IH". wp_lam.
  awp_apply (try_deq_spec with "⊒V0 M◯0"); [eauto..|].
  iApply (aacc_aupd with "AU"); [done|].
  iIntros (E1) "QInv".
  iAaccIntro with "QInv"; [eauto with iFrame|].
  iIntros (z V1 E2 deq M1) "(QInv & #⊒V1 & #M◯1 & [%LeV0V1 %CASE]) !>".

  destruct (decide (z = (-1)%Z)) as [->|NEQ].
  - iLeft. destruct CASE as [-> ->]. iFrame "QInv". iIntros "AU !> _".
    wp_let. wp_op. rewrite bool_decide_false; [|lia]. wp_if. by iApply "IH".
  - iRight. destruct CASE as (EQE2E1 & SubM0M1 & CASE).
    iExists z,V1,E2,deq,M1. iFrame "QInv ⊒V1 M◯1". iSplit; [done|].
    iIntros "HΦ !> _". wp_let. wp_op. rewrite bool_decide_true; last first.
    { by destruct (decide (z = 0%Z)) as [->|NEQ']; lia. }
    wp_pures. by iApply "HΦ".
Qed.
End msqueue.

Definition msqueue_impl_history `{!noprolG Σ, !atomicG Σ, !msqueueG Σ}
  : queue_spec Σ := {|
    spec_history.QueueInv_Objective := QueueInv_objective;
    spec_history.QueueInv_Timeless := QueueInv_timeless;
    spec_history.QueueInv_Linearizable := QueueInv_Linearizable_instance;
    spec_history.QueueInv_history_wf := QueueInv_history_wf_instance;
    spec_history.QueueInv_QueueLocal := QueueInv_QueueLocal_instance;
    spec_history.QueueLocal_lookup := QueueLocal_lookup_instance;
    spec_history.QueueLocal_Persistent := QueueLocal_persistent;
    spec_history.new_queue_spec := new_queue_spec;
    spec_history.try_enq_spec := try_enq_spec;
    spec_history.enqueue_spec := enqueue_spec;
    spec_history.try_deq_spec := try_deq_spec;
    spec_history.dequeue_spec := dequeue_spec;
  |}.
