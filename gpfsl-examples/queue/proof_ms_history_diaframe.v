From gpfsl.examples Require Import sflib.

From iris.algebra Require Import auth gset gmap agree.
From iris.algebra Require Import lib.mono_list.
From iris.base_logic Require Import lib.mono_nat.
From iris.proofmode Require Import tactics.

From gpfsl.base_logic Require Import meta_data.
From gpfsl.examples.algebra Require Import mono_list.
From gpfsl.logic Require Import logatom atomics invariants.

From gpfsl.logic Require Import repeat_loop new_delete.
From gpfsl.examples Require Import map_seq loc_helper.
From gpfsl.examples.queue Require Import spec_history code_ms_tailcas.
From gpfsl.examples.omo Require Import omo omo_preds append_only_loc.

From gpfsl.diaframe Require Import vprop_weakestpre spec_notation
 vprop_weakestpre_logatom atom_spec_notation proof_automation omo_specs omo_hints mono_list_hints.

From diaframe Require Import proofmode_base lib.except_zero own_hints steps.verify_tac util_instances max_prefix_list_hints.
From diaframe.symb_exec Require Import weakestpre_logatom.
From Hammer Require Import Tactics.

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
  ∃ eVt ogen gen enqid γl γsl (v : val) (l : loc) V (eVenq : omo_event qevent),
    OmoEinfo γt et eVt ∗
    MatchValue (#l, V) (loc_event_msg eVt.(type)) ∗
    ask_optional ogen gen ∗
    ⎡mono_list_idx_own γcl gen (enqid, γl, γsl, v, l)⎤ ∗
    OmoEinfo γg enqid eVenq ∗
    ⌜ eVenq.(sync) ⊑ V ⌝ ∗
    @{V} OmoEview γl {[0]}.

Definition AllTailMsg γg γt γcl es : vProp :=
  [∗ list] e ∈ es, AllTailMsgInner γg γt γcl e.

Definition AllHeadMsgInnerStCase st γcl γl γsl genh (Ml : eView) : vProp :=
  match st with
    | [] => emp
    | hd :: _ => ∃ enqid' γl' γsl' (v' : val) (l' : loc) el omol',
    OmoSnapOmo γl γsl omol' ∗
    ⎡mono_list_idx_own γcl (genh + 1) (enqid', γl', γsl', v', l')⎤ ∗
    ⌜ Ml = {[el; 0]} ∧ omo_write_op omol' = [0; el] ⌝
  end.

#[local] Instance AllHeadMsgInnerStCase_objective st γcl γl γsl genh Ml : Objective (AllHeadMsgInnerStCase st γcl γl γsl genh Ml).
Proof. destruct st; apply _. Qed.
#[local] Instance AllHeadMsgInnerStCase_persistent st γcl γl γsl genh Ml : Persistent (AllHeadMsgInnerStCase st γcl γl γsl genh Ml).
Proof. destruct st; apply _. Qed.
#[local] Instance AllHeadMsgInnerStCase_timeless st γcl γl γsl genh Ml : Timeless (AllHeadMsgInnerStCase st γcl γl γsl genh Ml).
Proof. destruct st; apply _. Qed.

Definition AllHeadMsgInner γg γh γs γcl γm genh eh : vProp :=
  ∃ deqid eVh enqid γl γsl (v : val) (l : loc) (V : view) st Ml,
    OmoEinfo γh eh eVh ∗
    OmoCW γg γh deqid eh ∗ CWMonoValid γm deqid ∗
    (* omo_gen_map γg γl deqid 0 ∗ initial write event of [next] field of node is associated with [deq] event *)
    ⎡mono_list_idx_own γcl genh (enqid, γl, γsl, v, l)⎤ ∗
    OmoLe γg enqid deqid ∗ (* gen of enq ≤ gen of deq *)
    OmoSnap γg γs deqid st ∗
    MatchValue (#l, V) (loc_event_msg eVh.(type)) ∗
    AllHeadMsgInnerStCase st γcl γl γsl genh Ml ∗
    @{V} OmoEview γl Ml.

Definition AllHeadMsg γg γh γs γcl γm es : vProp :=
  [∗ list] gen↦e ∈ es, AllHeadMsgInner γg γh γs γcl γm gen e.


Definition eView_Enq_exact_left M CL : vProp :=
  ([∗ list] ninfo ∈ CL, ⌜ ninfo.1.1.1.1 ∈ M ⌝).

Definition eView_Enq_exact_right γg M CL : vProp :=
  ([∗ set] e ∈ M,
      ∃ eV,
        OmoEinfo γg e eV ∗
        match eV.(type) with
        | Enq _ => ⌜ e ∈ CL.*1.*1.*1.*1 ⌝
        | _ => True
        end).

#[local] Instance eView_Enq_exact_right_objective γg M CL : Objective (eView_Enq_exact_right γg M CL).
Proof. apply big_sepS_objective => ?. apply exists_objective => eV. destruct (eV.(type)); apply _. Qed.

#[local] Instance eView_Enq_exact_right_timeless γg M CL : Timeless (eView_Enq_exact_right γg M CL).
Proof. apply big_sepS_timeless => ?. apply bi.exist_timeless => eV. destruct (eV.(type)); apply _. Qed.

#[local] Instance eView_Enq_exact_right_persistent γg M CL : Persistent (eView_Enq_exact_right γg M CL).
Proof. apply big_sepS_persistent => ?. apply bi.exist_persistent => eV. destruct (eV.(type)); apply _. Qed.

(* All [Enq] events in [M] are exactly ones in [CL] *)
Definition eView_Enq_exact γg M CL : vProp :=
  eView_Enq_exact_left M CL ∗ eView_Enq_exact_right γg M CL.


Definition HeadLastMsg γg γh γs γcl es esh CL : vProp :=
  ∃ eh deqid st gen CLh (eVh : omo_event loc_event) M',
    MatchValue (Some eh) (last esh) ∗
    OmoEinfo γh eh eVh ∗
    OmoCW γg γh deqid eh ∗
    MatchValue (Some deqid) (es !! gen) ∗
    OmoSnap γg γs deqid st ∗
    ⌜ (length CLh = length esh + length st)%nat ⌝ ∗
    ⎡mono_list_lb_own γcl CLh⎤  ∗
    eView_Enq_exact γg M' CLh ∗
    @{(loc_event_msg eVh.(type)).2} OmoEview γg M' ∗
    OmoUB γg M' deqid ∗
    ⌜ st.*1.*1.*1 ++ drop (gen + 1) es = drop (length esh) CL.*1.*1.*1.*1 ⌝ ∗

    ([∗ list] gen↦state ∈ st,
      ∃ enqid' γl' γsl' (z' : Z) l' eV',
        ⎡mono_list_idx_own γcl (length esh + gen) (enqid', γl', γsl', #z', l')⎤ ∗
        OmoEinfo γg enqid' eV' ∗
        ⌜ state = (enqid', z', eV'.(sync), eV'.(eview))
        ∧ eV'.(type) = Enq z'
        ∧ (z' > 0)%Z ⌝).



Definition NextFieldCase (has_next : bool) γg γl γcl es gen : vProp :=
  (if negb has_next then ⌜es = [0]⌝ else
    (∃ el eVl enqid' γl' γsl' (v' : val) (l' : loc) (eVenq' : omo_event qevent) (V' : view) q,
        ⌜ es = [0; el] ∧ el ≠ 0 ⌝ ∗
        OmoEinfo γl el eVl ∗
        MatchValue (#l', V') (loc_event_msg eVl.(type)) ∗
        meta l' nroot (enqid', γl', γsl', v') ∗
        ⎡mono_list_idx_own γcl (gen + 1) (enqid', γl', γsl', v', l')⎤ ∗
        OmoEinfo γg enqid' eVenq' ∗ ⌜ V' = eVenq'.(sync) ⌝ ∗
        OmoCW γg γl enqid' el ∗
        OmoHb γg γl enqid' el ∗
        @{V'} (OmoEview γl {[el; 0]} ∗ OmoEview γl' {[0]}) ∗
         @{V'} (l' >> data) ↦{q} v'))%I.

#[global] Instance NextFieldCase_objective has_next γg γl γcl es gen :
  Objective (NextFieldCase has_next γg γl γcl es gen).
Proof. destruct has_next; apply _. Qed.

#[global] Instance NextFieldCase_timeless has_next γg γl γcl es gen :
  Timeless (NextFieldCase has_next γg γl γcl es gen).
Proof. destruct has_next; apply _. Qed.

Definition NextFieldInfo γg γl γsl γcl es gen : vProp :=
  ∃ eVl0 V0 has_next,
    OmoEinfo γl 0 eVl0 ∗ MatchValue (#0, V0) (loc_event_msg eVl0.(type)) ∗
    NextFieldCase has_next γg γl γcl es gen.

Definition AllNodesInner γg γcl gen ninfo : vProp :=
  ∃ enqid eVenq γl γsl v l El omol mol Vbl (z : Z),
    ⌜ (enqid, γl, γsl, v, l) = ninfo ⌝ ∗
    ⌜ #z = v ⌝ ∗
    meta l nroot (enqid, γl, γsl, v) ∗
    OmoAuth γl γsl (1/2) El omol mol _ ∗
    OmoEinfo γg enqid eVenq ∗
    ⌜ Enq z = eVenq.(type) ∧ (z > 0)%Z ⌝ ∗
    @{Vbl} append_only_loc (l >> link) γl ∅ cas_only ∗
    NextFieldInfo γg γl γsl γcl (omo_write_op omol) gen.

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
      OmoEinfo γg ninfo.1.1.1.1 eVl ∗
      OmoUB γg ({[ninfo.1.1.1.1]} ∪ eVl.(eview) ∪ M) ninfo.1.1.1.1 ∗
      @{eVl.(sync)} OmoEview γg ({[ninfo.1.1.1.1]} ∪ eVl.(eview) ∪ M) ∗
      eView_Enq_exact γg ({[ninfo.1.1.1.1]} ∪ eVl.(eview) ∪ M) CL' ∗
      ⎡mono_list_lb_own γcl CL'⎤ ∗ ⌜ length CL' = (gen + 1)%nat ⌝.

Definition AllEvents γg γh γcl γm E : vProp :=
  [∗ list] e↦eV ∈ E,
    match eV.(type) with
    | Enq _ => emp
    | _ => ∃ e' eh eh',
      OmoHb γg γh e eh ∗ ask_for eh' ∗ OmoEq γh eh eh' ∗
      OmoCW γg γh e' eh' ∗ OmoEq γg e e' ∗
      CWMonoValid γm e'
    end.

Definition QueueInternalInv γg q E : vProp :=
  ∃ γh γt Vbh Vbt,
    @{Vbh} append_only_loc (q >> head) γh ∅ cas_only ∗
    @{Vbt} append_only_loc (q >> tail) γt ∅ cas_only ∗
  ∃ γsh γst γcl γm omo stlist Eh omoh moh Et omot mot CL γs Mono ,
    meta q nroot (γh,γt,γsh,γst,γcl,γm) ∗

    Peek (OmoAuth γh γsh (1/2) Eh omoh moh _) ∗
    Peek (OmoAuth γt γst (1/2) Et omot mot _) ∗
    Peek (OmoAuth γg γs (1/2) E omo stlist _) ∗
    ⎡mono_list_auth_own γcl 1 CL⎤ ∗


    AllNodes γg γcl CL ∗ AllPrevLinks γg γcl CL ∗
    AllHeadMsg γg γh γs γcl γm (omo_write_op omoh) ∗
    HeadLastMsg γg γh γs γcl (omo_write_op omo) (omo_write_op omoh) CL ∗
    AllTailMsg γg γt γcl (omo_write_op omot) ∗
    CWMono γg γh γm Mono ∗
    EnqSeen γg γcl CL ∗
    AllEvents γg γh γcl γm E ∗
    OmoAuth γh γsh (1/2) Eh omoh moh _ ∗
    OmoAuth γt γst (1/2) Et omot mot _ ∗
    OmoAuth γg γs (1/2) E omo stlist _
    .

Definition QueueInv (γg : gname) (q : loc) (E : history qevent) : vProp :=
  ∃ γs omo stlist, OmoAuth γg γs (1/2) E omo stlist _.

Definition InternalInv_inner γg q : vProp := ∃ E, QueueInternalInv γg q E ∗ emp.
  (* emp is essential here *)
Definition InternInv N γg q := inv (msqN N q) (InternalInv_inner γg q).

Definition QueueLocal (N : namespace) γg q (E : history qevent) M : vProp :=
  ∃ γh γt γsh γst γcl γm Mh Mt CL,
    meta q nroot (γh,γt,γsh,γst,γcl,γm) ∗
    InternInv N γg q ∗

    OmoSnapHistory γg E ∗
    OmoEview γg M ∗
    OmoEview γh Mh ∗
    OmoEview γt Mt ∗
    eView_Enq_exact γg M CL ∗
    ⎡mono_list_lb_own γcl CL⎤ ∗

    ⌜ CL ≠ [] ⌝.


Local Instance PrevLinkInfo_objective γg γcl gen ninfo : Objective (PrevLinkInfo γg γcl gen ninfo).
Proof. destruct gen; apply _. Qed.
Local Instance PrevLinkInfo_persistent γg γcl gen ninfo : Persistent (PrevLinkInfo γg γcl gen ninfo).
Proof. destruct gen; apply _. Qed.
Local Instance PrevLinkInfo_timeless γg γcl gen ninfo : Timeless (PrevLinkInfo γg γcl gen ninfo).
Proof. destruct gen; apply _. Qed.
Local Instance AllHeadMsgInner_persistent γg γh γs γcl γm genh eh : Persistent (AllHeadMsgInner γg γh γs γcl γm genh eh) := _.
Local Instance AllHeadMsgInner_objective γg γh γs γcl γm genh eh : Objective (AllHeadMsgInner γg γh γs γcl γm genh eh) := _.
Local Instance AllHeadMsgInner_timeless γg γh γs γcl γm genh eh : Timeless (AllHeadMsgInner γg γh γs γcl γm genh eh) := _.

Local Instance AllEvents_objective γg γh γcl γm E : Objective (AllEvents γg γh γcl γm E).
Proof. apply big_sepL_objective. intros. destruct (x.(type)); apply _. Qed.

Local Instance AllEvents_persistent γg γh γcl γm E : Persistent (AllEvents γg γh γcl γm E).
Proof. apply big_sepL_persistent. intros. destruct (x.(type)); apply _. Qed.

Local Instance AllEvents_timeless γg γh γcl γm E : Timeless (AllEvents γg γh γcl γm E).
Proof. apply big_sepL_timeless. intros. destruct (x.(type)); apply _. Qed.

Local Instance QueueInternalInv_objective γg q E : Objective (QueueInternalInv γg q E).
Proof. repeat (apply exists_objective; intros). repeat (apply sep_objective; [apply _|]). apply _. Qed.

Local Instance QueueInternalInv_timeless γg q E : Timeless (QueueInternalInv γg q E).
Proof. repeat (apply @bi.exist_timeless; intros). repeat (apply @bi.sep_timeless; [apply _|]). apply _. Qed.

Global Instance QueueInv_objective γg q E : Objective (QueueInv γg q E) := _.
Global Instance QueueInv_timeless γg q E : Timeless (QueueInv γg q E) := _.
Global Instance QueueLocal_persistent N γg q E M : Persistent (QueueLocal N γg q E M) := _.


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
    + rewrite /eView_Enq_exact_left big_sepL_forall. iIntros "%gen %ninfo %Hninfo".
      iDestruct "M2_CL2" as "[M2_CL2 _]". iDestruct (big_sepL_lookup with "M2_CL2") as %M2INCL; [done|]. iPureIntro. set_solver.
    + iApply big_sepS_intro. iIntros "%e %eIncl !>". rewrite elem_of_union in eIncl. destruct eIncl as [eIncl|eIncl].
      * iDestruct "M1_CL1" as "[_ M1_CL1]". iDestruct (big_sepS_elem_of with "M1_CL1") as (eV) "[e✓eV CASE]"; [done|].
        iExists eV. iFrame "e✓eV". destruct (eV.(type)); try done. iDestruct "CASE" as %eInclCL. iPureIntro.
        eapply elem_of_prefix; [done|]. do 4 apply fmap_prefix. done.
      * iDestruct "M2_CL2" as "[_ M2_CL2]". iDestruct (big_sepS_elem_of with "M2_CL2") as "H"; [done|]. iFrame "H".
  - iExists CL1. iFrame "CL1◯". iSplitR; [|by apply prefix_length in LECL2CL1; iPureIntro; lia]. iSplit.
    + rewrite /eView_Enq_exact_left big_sepL_forall. iIntros "%gen %ninfo %Hninfo".
      iDestruct "M1_CL1" as "[M1_CL1 _]". iDestruct (big_sepL_lookup with "M1_CL1") as %M2INCL; [done|]. iPureIntro. set_solver.
    + iApply big_sepS_intro. iIntros "%e %eIncl !>". rewrite elem_of_union in eIncl. destruct eIncl as [eIncl|eIncl].
      * iDestruct "M1_CL1" as "[_ M1_CL1]". iDestruct (big_sepS_elem_of with "M1_CL1") as "H"; [done|]. iFrame "H".
      * iDestruct "M2_CL2" as "[_ M2_CL2]". iDestruct (big_sepS_elem_of with "M2_CL2") as (eV) "[e✓eV CASE]"; [done|].
        iExists eV. iFrame "e✓eV". destruct (eV.(type)); try done. iDestruct "CASE" as %eInclCL. iPureIntro.
        eapply elem_of_prefix; [done|]. do 4 apply fmap_prefix. done.
Qed.



Lemma QueueInv_Linearizable_instance :
  ∀ γg q E, QueueInv γg q E ⊢ ⌜ Linearizability E ⌝.
Proof. intros. iDestruct 1 as (???) "[_ M●]". by iDestruct (OmoAuth_Linearizable with "M●") as %LIN; apply omo_compatible in LIN. Qed.

Lemma QueueInv_history_wf_instance :
  ∀ γg q E, QueueInv γg q E ⊢ ⌜ history_wf E ⌝.
Proof. intros. iDestruct 1 as (???) "[_ M●]". by iDestruct (OmoAuth_wf with "M●") as "[_ %H2]". Qed.

Lemma QueueInv_QueueLocal_instance :
  ∀ N γg q E E' M',
    QueueInv γg q E -∗ QueueLocal N γg q E' M' -∗ ⌜ E' ⊑ E ⌝.
Proof.
  intros. iDestruct 1 as (???) "[_ M●]". iDestruct 1 as (?????????) "(_ & _ & E◯ & _)". by iDestruct (OmoAuth_OmoSnapHistory with "M● E◯") as %?.
Qed.

Lemma QueueLocal_lookup_instance :
  ∀ N γg q E M e V,
    sync <$> E !! e = Some V → e ∈ M →
    QueueLocal N γg q E M -∗ ⊒V.
Proof. intros. iDestruct 1 as (?????????) "(_ & _ & E◯ & M◯ & _)". by iApply (OmoSnapHistory_OmoEview with "E◯ M◯"). Qed.



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
    iDestruct "Inner" as (??????????) "(_ & #deqid'↦eh & _ & #CL@gen1 & #enqid≤deqid' & _ & _)".
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
  - rewrite /eView_Enq_exact_right big_sepS_union; [|set_solver]. iFrame.
    rewrite big_sepS_singleton. iExists eV. iFrame "#". destruct (eV.(type)); try done.
    by specialize (NEQEnq v).
Qed.


#[local] Remove Hints ssrbool.not_false_is_true : core.

Definition do_access_all_nodes_inner (γcl : gname) (gen : nat) (tup : event_id * gname * gname * val * loc) : vProp := emp.

(* Note: This hint is abusing the fact that we are only using one mono_list. *)
#[global] Instance biabd_access_AllNodesInner γcl gen tup :
  HINT ε₀ ✱ [γcl' q CL γg;
    ⎡ mono_list_idx_own γcl gen tup ⎤ ∗
    ⎡ mono_list_auth_own γcl' q CL ⎤ ∗
    ⌜ γcl' = γcl ⌝ ∗  (* we defer proving this equality since we won't know this information before we open the invariant and do a meta agree. *)
    AllNodes γg γcl CL
  ]
  ⊫ [id]
  ; do_access_all_nodes_inner γcl gen tup ✱ [
    AllNodesInner γg γcl gen tup ∗
    ⎡ mono_list_auth_own γcl' q CL ⎤ ∗
    (AllNodesInner γg γcl gen tup -∗ AllNodes γg γcl CL)
  ].
Proof.
  iStep 5 as (q CL γg ??) "CL@gen ? CL● AllNodes". iDestruct (mono_list_auth_idx_lookup with "CL● CL@gen") as %HCLgen.
  iDestruct (big_sepL_lookup_acc with "AllNodes") as "[Inner Close]"; [exact HCLgen|]. iStep. iFrame "Inner Close CL●".
Qed.

#[global] Typeclasses Opaque do_access_all_nodes_inner.
#[global] Opaque do_access_all_nodes_inner.
#[global] Arguments do_access_all_nodes_inner _ _ _ : simpl never.

#[global] Instance biabd_append_only_loc_from_list_idx_own_and_AllNodes' p enqid γcl γsl gen v l γl' :
  HINT  □⟨ p ⟩ ⎡ mono_list_idx_own γcl gen (enqid, γl', γsl, v, l) ⎤ ✱ [V';
    do_access_all_nodes_inner γcl gen (enqid, γl', γsl, v, l) ∗
    @{V'} append_only_loc (l >> 0) γl' ∅ cas_only
  ]
  ⊫ [id]
    γl uf ty V; ▷(@{V} @append_only_loc Σ _ _ _ _ (l >> 0) γl uf ty) ✱ [ ⌜uf = ∅ ∧ ty = cas_only ∧ γl = γl' ∧ V = V'⌝ ].
Proof. iSteps. Qed.


#[global] Instance biabd_NextFieldCase_leak has_next γg γl γcl es gen :
  HINT NextFieldCase has_next γg γl γcl es gen ✱ [-; emp]
  ⊫ [id]
  ; NextFieldCase has_next γg γl γcl es gen ✱ [
    NextFieldCase has_next γg γl γcl es gen
  ] | 0.
Proof using All. destruct has_next; iSteps. Qed.


#[local] Hint Extern 10 (BehindModal (fupd ?El ?Er) (?N ⊆ ?Er)) =>
  unify El Er; unfold BehindModal; pure_solver.trySolvePure : solve_pure_add.


#[global] Instance biabd_omo_gen_le_new γe γs q E omo e e' es stlist Interp :
  HINT OmoAuth γe γs q E (omo_append_w omo e es) stlist Interp ✱ [eV';
    OmoEinfo γe e' eV'
  ]
  ⊫ [id]
  ; OmoLe γe e' e ✱ [ OmoAuth γe γs q E (omo_append_w omo e es) stlist Interp ].
Proof. iSteps as "??? M●". iDestruct (OmoLe_get_append_w with "M● [$]") as "#H". iSteps. Qed.


#[local] Remove Hints biabd_big_sepL_mono : typeclass_instances.


Lemma new_queue_spec :
  new_queue_spec' new_queue QueueLocal QueueInv.
Proof using All.
  intros ???. iStep 50 as (n q) "? HMn n↦ ? HMq _ hd↦ tl↦". rewrite !omo_rewrite_hints.
  iMod (append_only_loc_cas_only_from_na with "n↦") as (γln γsn Vn eVn0) "H"; [done|]. iDecompose "H".
  iMod (append_only_loc_cas_only_from_na_rel _ _ (⊒_) with "[$] tl↦") as (γt γst Vt eVt0) "H"; [done|]. iDecompose "H".
  iMod (append_only_loc_cas_only_from_na_rel _ _ (⊒_) with "[$] hd↦") as (γh γsh Vh eVh0) "H"; [done|]. iDecompose "H".
  iApply (bi.sep_elim_r (do_intro_view_forall)). iStep as (??) "⊒V ???". iAssert (⊒eVh0.(sync))%I as "{⊒V} ?". { iSteps. }
  epose (eVenq := mkOmoEvent (Enq 1) eVt0.(sync) {[0%nat]}).
  iMod (@OmoAuth_alloc _ _ _ _ _ eVenq ([] ++ [(0, _, _, _)]) γln _ queue_interpretable with "[$]") as (γg γs) "H".
  { by eapply queue_step_Enq. } { done. } iDecompose "H" as (??) "? e0↦en0 e0✓eVenq ?? M● _".
  iDestruct (OmoHbToken_finish with "M●") as "M●".

  epose (eVdeq := mkOmoEvent (Deq 1) eVh0.(sync) {[1%nat; 0%nat]}).
  iMod (OmoAuth_insert_last _ γh _ _ _ _ _ _ eVh0.(sync) {[0]} with "M● [] [$] []") as "H"; [iSteps|..].
  { eassert (omo.step 1%nat eVdeq [(0, 1%Z, eVenq.(sync), eVenq.(eview))] []); [|by iPureIntro; split_and!].
    eapply queue_step_Deq; try done; subst eVenq eVdeq; simpl; pure_solver.trySolvePure. }
  iDecompose "H" as (??) "?? e1↦eh0 e1✓eVdeq ?? M● ?".

  iMod (OmoHb_new_1 (eventT2 := loc_event) γg γh _ _ _ _ 1 0 with "M● [$] [$]") as "[M● #e1⊒eh0]"; [solve_lat|].
  iDestruct (OmoHbToken_finish with "M●") as "M●".
  iDestruct (OmoLe_get_append_w with "M● e0✓eVenq") as "#e0≤e1".

  iMod (CWMono_new γg γh) as (γm) "MONO".
  iMod (CWMono_insert_last_last (eventT2 := loc_event) (wr_event 1) _ γh  with "MONO M● [$] e1↦eh0") as "H"; [done|done|]. iDecompose "H".
  set CL := [(0, γln, γsn, #1, n)].
  iMod (mono_list_own_alloc CL) as (γcl) "[CL● #CL◯]".
  iMod (meta_set _ q (γh,γt,γsh,γst,γcl,γm) nroot with "[$]") as "#HM"; [done|].
  iMod (meta_set _ n (0,γln,γsn,#1) nroot with "[$]") as "#HMn"; [done|].
  oSteps. 1: shelve. iExists false. replace [(0, _)] with (omo_append_w [] 0 []); [|done].
  iStep. rewrite H6. simpl. iStep. iExists 1. iStep. iExists CL. iStep. iExists  {[1; 0]}%nat. iStep.
  iAssert (eView_Enq_exact_right γg {[1; 0]} CL) as "#?".
  { iApply big_sepS_intro. iIntros "%e %eIn". destruct (decide (e = 0)) as [->|NEQ]; iModIntro.
    { iSteps. } { have -> : e = 1 by set_solver. iSteps. } }
  iAssert (OmoUB γg {[1; 0]} 1)%I with "[-]" as "#?".
  { rewrite /OmoUB big_sepS_forall.
    iIntros "%e %eIn". destruct (decide (e = 0)) as [->|NEQ]; [done|].
    have EQ : e = 1 by set_solver. subst e. iApply @OmoLe_get_from_Eq. iSteps. }
  iStep. rewrite !H3. iStep. iExists (Some 0). iStep. iExists ∅. have -> : @eq eView ({[0; 0]} ∪ ∅) {[0]} by set_solver-.
  iSplitR. { rewrite /OmoUB big_sepS_singleton. iApply OmoLe_get_from_Eq. iSteps. }
  iStep. iExists [(0, γln, γsn, #1, n)]. iSplitR. { rewrite /eView_Enq_exact_left big_sepL_singleton /=. iPureIntro. set_solver-. }
  iSplitR. { iModIntro. rewrite /eView_Enq_exact_right big_sepS_singleton. iSteps. }
  iDestruct (OmoEq_get_from_Einfo (eventT := loc_event) γh 0 with "[$]") as "H". iDecompose "H". iStep. iExists 0. do 93solveStep. iExists ({[1; 0]}).
  iStep. iExists CL. iSteps. Unshelve. all: try pure_solver.trySolvePure; try iPureIntro.
  1, 4: subst CL; intros ?? [-> <-]%list_lookup_singleton_Some; set_solver-.
  all: try rewrite ?H0 ?H3 ?H6 //=. solve_lat.
Qed.

#[global] Instance try_enq_dspec N V γg q v E1 M :
  SPEC ⟨ ⊤ , ↑N , ↑histN⟩ E, <<
    ⊒V ∗
    QueueLocal N γg q E1 M ∗
    ⌜ N ## histN ⌝ ∗
    ⌜ (0 < v)%Z ⌝
  ¦
    ▷ QueueInv γg q E  > >
      code_ms_tailcas.try_enq [ #q ; #v]
  << (b : bool), RET #b; emp
      ¦
      (if b then (
        ∃ V', ⊒V'  ∗
        ∃ M',
          let E' := E ++ [mkOmoEvent (Enq v) V' M'] in
          ▷ QueueInv γg q E' ∗ @{V'} QueueLocal N γg q E' M' ∗ ⌜ V ⊑ V' ∧ M ⊆ M' ⌝
      )
      else (
        ▷ QueueInv γg q E ∗
        ∃ V', ⊒V' ∗ @{V'} QueueLocal N γg q E M
      ))
    > >.
Proof using All.
  iStep 32 as "????????? AU". iLöb as "IH". iSteps. iExists None. oSteps. iExists None. iSteps. iExists None. iStep 12 as "? Hx75".
  rewrite !omo_rewrite_hints. iStep as "Case1". rewrite !omo_rewrite_hints. iStep 4. destruct x76; last first. (* Read gen *)
  { destruct x49; iDecompose "Case1" as "H"|"?"; [|by rewrite H40 in H36; inversion H36]. rewrite H40 /= in H36. symmetry in H36.
    apply list_lookup_singleton_Some in H36 as [-> ->]. iDecompose "H". rewrite -H42 in H38. inversion H38. subst. oSteps. iExists None. oSteps.
    { iExists None. oSteps. } iExists (Some x120). iSteps. iExists None. iSteps. }

  iAssert (⌜ x75 = 0 ⌝)%I with "[Case1]" as %->; [destruct x49; iDecompose "Case1"; rewrite H40 in H36; by inversion H36|]. iDecompose "Hx75".
  rewrite -H32 in H38. inversion H38. subst. iStep 18. iRename select (_ (x9 ↦ _))%I into "n↦".
  iMod (append_only_loc_cas_only_from_na_rel _ _ (⊒_) with "[] [n↦]") as (γln γsn V2' eVn0) "H"; [|done|iSteps|]; [done|]. iDecompose "H".
  iSteps as "Prev ?????????? ES ????????????????? Mx47 Case2 CL3●". iExists None. iDestruct (mono_list_auth_idx_lookup with "CL3● [$]") as %?.

  iAssert (⌜ if decide (x45 = (length x103 - 1)) then True else x77 = true ⌝ )%I as %Hgen1; [|iStep 15]. {
    destruct (decide _); destruct x77; try done. iExFalso. iDecompose "Case2".
    have [ninfo Hninfo] : is_Some (x103 !! (S x45)) by rewrite lookup_lt_is_Some; apply lookup_lt_Some in H56; lia.
    iDestruct (big_sepL_lookup with "Prev") as "H"; [exact Hninfo|]. iDecompose "H"  as (???????HL2) "H1 Snap".
    iDestruct (OmoAuth_OmoSnapOmo x47 with "Mx47 Snap") as %[_ LE%prefix_length]. rewrite H57 -omo_write_op_length HL2 /= in LE. lia. }
  - do 3 (iStep; try rewrite !omo_rewrite_hints). iApply wp_hist_inv; [done|]. iIntros "!> #HINV". iSteps. rewrite /own_loc_vec //. iStep.
    iDestruct (view_at_elim x75 with "[] [$]") as "n↦"; [iSteps|]. iMod (append_only_loc_to_na with "HINV [$] n↦") as (???) "[n↦ _]"; [solve_ndisj|].
    rewrite !shift_0. oSteps. iDestruct (view_at_elim x12 with "[] [$]") as "AU"; [oSteps|]. iMod "AU" as (?) "[>H [_ Commit]]".
    iDecompose "H". iMod ("Commit" $! false with "[-]") as "?"; iSteps.
  - destruct x77; iDecompose "Case2" as "Hx76"|"?".
    { rewrite omo_write_op_length !H68 /= in H65. inversion H65. subst. iDecompose "Hx76". rewrite -H70 in H66. inversion H66. }
    destruct (decide (x45 = (length x103 - 1))) as [->|_]; last by inversion Hgen1.
    iDestruct (big_sepL_lookup with "ES") as "H"; [done|]. iDecompose "H" as "?????? CL●".
    set M0 := (M ∪ ({[x46]} ∪ eview x52 ∪ x77)). assert (x45 = x103) as ->. { apply prefix_length_eq;[done|lia]. }
    iDestruct (eView_Enq_exact_union γg x5 M _ _ x103 with "[] [] [] []") as "#H"; [iSteps..|]. iDecompose "H".
    assert (x45 = x103) as ->. { apply prefix_length_eq;[done|lia]. }
    iRename select (_ (atomic_update _ _ _ _ _))%I into "AU". iDestruct (view_at_elim with "[] AU") as "AU"; [iSteps|]. iMod "AU" as (E3) "[>H HAUcl]".
    iDecompose "H" as "?? HAUcl". iDestruct (atomic.diaframe_close_right_quant with "HAUcl") as "HAU". iSpecialize ("HAU" $! true).
    iDestruct (OmoAuth_stlist_nonempty γg with "[$]") as %NEQstlist3. have [st Hst] : is_Some (last x96) by rewrite last_is_Some. iStep.
    set M' := {[length x83]} ∪ M0. set egV' := mkOmoEvent (Enq v) x116 M'.
    iMod (OmoAuth_insert_last γg x47 _ _ _ _ _ _ x116 M0 _ egV'  with "[$] [] [$] []") as "H"; [subst M0; iSteps|..].
    { iSteps. iPureIntro. apply queue_step_Enq; [done|lia|set_solver-]. } iDecompose "H".
    iMod (OmoHb_new_2 γg x47 _ _ _ _ _ _ (length x111) {[length x111]} with "[$][][$]") as "[? #?]"; [set_solver-|iSteps|].
    iStep. set (CL3' := x103 ++ [(length x83, γln, γsn, #v, x9)]). iExists CL3'.
    iAssert (⌜ length x111 ≠ 0 ⌝)%I with "[-]" as %x111Neq0; [|iAssert (eView_Enq_exact_left M' CL3') as "H"].
    { destruct x111; [|done]. iDestruct (@OmoAuth_wf loc_event _ _ _ _ x47 with "[$]") as %[OMO_GOOD _]. rewrite !omo_rewrite_hints /omo_append_w /=.
      have EQ1 : lookup_omo (x112 ++ [(0, [])]) (wr_event 0) = Some 0 by rewrite lookup_omo_wr_event omo_append_w_write_op H68.
      have EQ2 : lookup_omo (x112 ++ [(0, [])]) (wr_event 1) = Some 0 by rewrite lookup_omo_wr_event omo_append_w_write_op H68.
      eapply lookup_omo_inj in EQ2 as INJ; [|exact OMO_GOOD|exact EQ1]. inversion INJ. }
    { subst M' CL3'. iPureIntro. intros i ninfo Hi. simpl. destruct (decide (i = length x103)) as [->|NEQ].
      - rewrite lookup_app_1_eq in Hi. inversion Hi. simpl. set_solver-.
      - apply (prefix_lookup_inv x103) in Hi; [specialize (H73 _ _ Hi) as Hprev; set_solver +Hprev|..|by eexists].
        apply lookup_lt_is_Some. apply lookup_lt_Some in Hi. rewrite app_length /= in Hi. lia. } iDecompose "H".
    iAssert (eView_Enq_exact_right γg M' CL3')%I with "[-]" as "#?".
    { subst M' CL3'. iApply big_sepS_intro. iIntros "%e %eIncl". iModIntro. destruct (decide (e = length x83)) as [->|NEQ].
      - iStep. iPureIntro. rewrite !fmap_app /=. set_solver-.
      - have INCL : e ∈ M ∪ {[x46]} ∪ x52.(eview) ∪ x77 by clear -eIncl NEQ; set_solver.
        iDestruct (big_sepS_elem_of _ _ e with "[$]") as (eV) "[e✓eV HeV]"; first (clear -INCL; set_solver).
        iStep. destruct (type eV); try done. iDestruct "HeV" as "%HeV". iPureIntro. rewrite !fmap_app. clear -HeV. set_solver. }

    iMod (mono_list_auth_own_update CL3' with "[$]") as "[H _]". { by eexists. } iDecompose "H".
    iMod (meta_set _ x9 (length x83,γln,γsn,#v) nroot with "[$]") as "#?"; [done|]. iStep 2. rewrite !omo_rewrite_hints. iStep. iExists true. iStep.
    rewrite H68. iStep. rewrite !omo_rewrite_hints. iStep. iExists false. iStep. assert (length x103 = S (length x103 - 1)) as -> by lia. simpl. iStep.
    rewrite !omo_rewrite_hints. repeat iExists _. iSplitR; [by rewrite lookup_app_1_ne; [done|lia]|]. iStep. iExists _. iSplitR.
    { iPureIntro. symmetry. by apply lookup_app_l_Some. } iStep. rewrite !omo_rewrite_hints. iStep. iExists M'.
    replace ({[length x83]} ∪ M' ∪ M') with M' by set_solver-. iSplitR; [|iExists CL3';iSteps;[..|iExists None;oSteps;[iExists None|iExists (Some x145)];oSteps]].
    + iApply big_sepS_subseteq; [|by iApply (@OmoUB_singleton qevent)]; set_solver-.
    + iPureIntro. intros. destruct (decide (k = length x103)) as [->|NEQ].
      { rewrite lookup_app_1_eq in H81. inversion H81. set_solver-. } rewrite lookup_app_1_ne in H81; [|done]. by eapply H78.
    + iPureIntro. rewrite app_length /=. lia.
    + iExists None. iStep. repeat iExists _. iSplitR. { iPureIntro. eapply (prefix_lookup_Some CL3'); [|done]. apply lookup_app_1_eq. } iSteps.
  Unshelve. all : try apply inhabitant; try iPureIntro. 1 : tc_solve. 4 : by rewrite H42 //=.
  * intros. destruct (decide (k = length x103)) as [->|NEQ].
    { rewrite lookup_app_1_eq in H81. inversion H81. set_solver-. } rewrite lookup_app_1_ne in H81; [|done]. by eapply H78.
  * unfold not. intros. apply (f_equal length) in H81. subst CL3'. rewrite app_length /= in H81. lia.
  * rewrite Nat.sub_add; [|lia]. by apply lookup_app_1_eq.
  * rewrite omo_rewrite_hints omo_write_op_length H68 //.
  * assert (x92 < length (omo_write_op x95)). { by eapply lookup_lt_Some. } rewrite drop_app_le; [|lia]. rewrite -4!fmap_drop.
    rewrite drop_app_le; last first. { apply (prefix_length) in H54. lia. } rewrite app_assoc H48 !fmap_app. simplify_list_eq. done.
Qed.

#[local] Remove Hints simplify_neq_nil : typeclass_instances.

#[global] Instance try_deq_dspec N V γg q E0 M :
  SPEC ⟨ ⊤ , ↑N , ↑histN⟩ E, <<
    ⊒V ∗
    QueueLocal N γg q E0 M ∗
    ⌜ N ## histN ⌝
  ¦
    ▷ QueueInv γg q E  > >
      code_ms_tailcas.try_deq [ #q ]
  << (v : Z), RET #v; emp
      ¦
      (∃V', ⊒V' ∗
      (if decide (v = FAIL_RACE) then (
        ▷ QueueInv γg q E ∗
        @{V'} QueueLocal N γg q E M
      )
      else (
        ∃ M' deq,
          ⌜ if decide (v = EMPTY) then deq = EmpDeq
          else (0 < v)%Z ∧ deq = Deq v ⌝ ∗
          let E' := E ++ [mkOmoEvent deq V' M'] in
          ▷ QueueInv γg q E' ∗ @{V'} QueueLocal N γg q E' M' ∗ ⌜ V ⊑ V' ∧ M ⊆ M' ⌝
      )))
    > >.
Proof.
(* Intros preconditions *)
  iStep 3 as (tid φ γh γt γsh γst γcl γm Mh Mt CL0 HneM HneMh HneMt M_CL0_l CL0NEQ DISJ) "? Meta Inv E◯ ⊒M ⊒Mh ⊒Mt M_CL0_r CL◯0 ?".
(* acquire-read the head node. *)
  iStep 8 as (E1 ?? omo1 st1 Eh1 omoh1 moh1 Et1 omot1 mot1 CL1 ??????????????????) "?????? CL◯ ?????????????????????".
  iDestruct (OmoEview_update γg γh _ _ _ _ _ M Mh with "[$] [] []") as (Mh') "{⊒Mh} H"; [iSteps..|]. iDecompose "H" as (??) "?? ⊒Mh' ? M⊢Mh'".
  iExists (Some Mh'). iStep as (V1 ?) "? ⊒M ⊒Mt ⊒Mh' AU ?".
  (* intros read postcondition *)
  iStep 10 as (eh1 genh1 ?? eVh1 ? Eqgenh1 Hvle1 l1 eVh1EV ? HomoPrefix1 ? deqid1 enqid1 γl1 γsl1 vl1 ?? HCL1genh1 ??)
   "eh1✓eVh1 MAXgen_eh1 eh1_gid ehn1_gid ⊒V deqid1↦eh1 ? CL@genh1 ??? ehn1✓eVhn1 ???? RTOKEN' ? Mh●1 ?". iStep as "OMOh◯ ????????".
  do 2(rewrite !omo_rewrite_hints; iStep). iClearAnonymousIntuitionistics. clear st1.
  (* read link of the head node *)
  iStep 8 as (vl1 E2 ?? omo2 stlist2 Eh2 omoh2 moh2 Et2 omot2 mot2 CL2 γs2 Mono2 ? deqid2 st2 genh2 CLh2 ??? Eqgenh2 ?????? HomoPrefix2 eVenq1 El1 omol1 mol1 ??? eVl0 ? has_next2 eVl0EV ??)
    "AllPrevLinks2 AllHeadMsg2 ???????? AllTailMsg2 ? AllEvents2 ?????? CL@genh1 HMl1 OMOl1◯ ? enqid1✓eVenq1 el1✓eVl CL2◯ ? omot↦2 omoh↦2 Mono2 Mh●2 Mt●2 M●2 Ml●2 CASE CL●2 ?".
  iDestruct (big_sepL_lookup with "AllHeadMsg2") as "H". { eapply prefix_lookup_Some; [symmetry; exact Eqgenh1|pure_solver.trySolvePure]. }
  iDecompose "H" as (st1 Ml1 ? LneMl1) "MONO✓deqid1 _ deqid1_gid deqid1↪st1 Hst1 ⊒Ml1".
  iDestruct (OmoEview_update γg γl1 _ _ _ _ _ M Ml1 with "[$] [] []") as (Ml1') "{⊒Ml1} H"; [iSteps..|].
  iDecompose "H" as (??) "?? ⊒Ml1' ? M⊢Ml1'". iExists (Some Ml1'). iStep as (V2 ?) "? ⊒Ml1' ?".
  (* intros read postcondition *)
  iStep 10 as (el1 genl1 vl1' ?? eVl1 ? Hgenl1 ? eVl1EV ???) "el1✓eVl1 el1✓eVl1 OMOl1◯ ? MAXgen_el1 el1_gid el1n_gid ⊒V Ml1● RTOKEN omol1↦". destruct genl1.
  { iAssert (⌜ el1 = 0⌝)%I with "[CASE]" as "#H"; last iDecompose "H" as "? MAXgen_el1". { destruct has_next2; iDecompose "CASE"; rewrite H25 in Hgenl1; by inversion Hgenl1. }
    iAssert (⌜ st1 = [] ∧ vl1' = #0 ⌝)%I with "[-]" as "#H"; last iDecompose "H" as "???? Ml1●".
    { destruct st1; first (iPureIntro; sauto). iExFalso. iDecompose "Hst1" as (el ????? omol1' HCL2Sgenh1 Homol1') "??". iDecompose "Ml1●" as (? LEomol1wr) "?? Ml1●".
      destruct has_next2; last first.
      + iDecompose "CASE" as (Homol1). rewrite omo_insert_r_write_op Homol1 Homol1'  in LEomol1wr. apply prefix_length in LEomol1wr. simpl in *. lia.
      + iDecompose "CASE" as (el0 ??? Homol1 ????) "?????????". rewrite omo_insert_r_write_op Homol1 Homol1' in LEomol1wr.
        apply prefix_length_eq in LEomol1wr; last done. inversion LEomol1wr. subst el0. iDestruct (big_sepS_elem_of _ _ el with "MAXgen_el1") as "#el≤e0"; [set_solver|].
        have Lookup1 : lookup_omo (omo_insert_r omol1 0 (length El1)) (wr_event 0) = Some 0 by rewrite lookup_omo_wr_event omo_insert_r_write_op Homol1.
        have Lookup2 : lookup_omo (omo_insert_r omol1 0 (length El1)) (wr_event 1) = Some el by rewrite lookup_omo_wr_event omo_insert_r_write_op Homol1.
        iDestruct (OmoLe_Le with "Ml1● el≤e0") as %LE; [done..|]. simpl in *. lia. }
    iAssert (OmoUB γg M deqid1)%I with "[-]" as "#MAXgen_deqid1".
    { iApply big_sepS_forall. iIntros "%e %eM". iDestruct (OmoAuth_OmoEview γg _ _ _ _ _ M with "[$] []") as %MIncl; [iSteps|].
      specialize (MIncl _ eM) as [eV He]. iDestruct (big_sepL_lookup with "AllEvents2") as "eInfo"; [exact He|]. destruct (eV.(type)) eqn:HeVev.
      { iAssert (∃ gen γl γsl v l, ⌜ CL0 !! gen = Some (e, γl, γsl, v, l) ⌝)%I with "[-]" as (????) "(% & %HCL0gen)".
        { iDestruct (big_sepS_elem_of with "M_CL0_r") as (eV0) "[e✓eV0 HeV0]"; [exact eM|].
          iDestruct (OmoAuth_OmoEinfo γg with "[$] e✓eV0") as %He'. rewrite He in He'. inversion He'. subst eV0. clear He'. rewrite HeVev.
          iDestruct "HeV0" as %eIn. rewrite elem_of_list_lookup in eIn. destruct eIn as [gen Hgen]. rewrite !list_lookup_fmap in Hgen.
          destruct (CL0 !! gen) eqn:Heq; [|done]. destruct p as [[[[p γl] γsl] v'] l]. inversion Hgen. subst p. iSteps. }
        apply (prefix_lookup_Some _ CL2) in HCL0gen as HCL2gen; [|pure_solver.trySolvePure]. destruct (le_lt_dec gen genh1) as [LE|LT].
        { iApply (gen_le_enq_deq with "AllHeadMsg2 deqid1↦eh1 MONO✓deqid1 Mh●2 Mono2 [$]"); try done.
          eapply prefix_lookup_Some; [symmetry; exact Eqgenh1|]. pure_solver.trySolvePure. }
        have [ninfo Hlookup] : is_Some (CL0  !! (genh1 + 1)). { rewrite lookup_lt_is_Some. apply lookup_lt_Some in HCL0gen. lia. } destruct ninfo as [[[[e' γl'] γsl'] v'] l'].
        iAssert (∃ omol', OmoSnapOmo γl1 γsl1 omol' ∗ ⌜ length omol' = 2 ⌝)%I with "[-]" as (?) "[#OMOl1◯n %LEN]".
        { iDestruct (big_sepL_lookup with "AllPrevLinks2") as "H"; [eapply prefix_lookup_Some; [exact Hlookup|prove_prefix]|].
          replace (genh1 + 1) with (S genh1) by lia. iDecompose "H". iSteps. } iDecompose "Ml1●" as (? LEomol1wr) "?? Ml1●".
        destruct has_next2; last first. { iDecompose "CASE" as (Homol1). rewrite omo_insert_r_write_op Homol1 in LEomol1wr.
          apply prefix_length in LEomol1wr. rewrite -omo_write_op_length LEN /= in LEomol1wr. lia. }
        iDecompose "CASE" as (el eVl enqid' ?????? Homol1 ?? Hlookup' ??) "??????????".
        apply (prefix_lookup_Some _ CL2) in Hlookup as HCL2lookup; [|prove_prefix]. rewrite HCL2lookup in Hlookup'. inversion Hlookup'. subst. clear Hlookup'.
        iAssert (⌜ el ∈ Ml1' ⌝)%I with "[-]" as %elMl1'. { specialize (M_CL0_l _ _ Hlookup) as ?. by iDestruct (OmoHb_HbIncluded with "[$] M⊢Ml1'") as %?. }
        iDestruct (big_sepS_elem_of with "MAXgen_el1") as "#el≤e0"; [exact elMl1'|].
        iDestruct (OmoLe_Le _ _ _ _ _ _ (wr_event 1) (wr_event 0) with "Ml1● el≤e0") as %LE; try by rewrite lookup_omo_wr_event omo_insert_r_write_op Homol1. simpl in LE. lia. }
      all: iDestruct "eInfo" as (???) "(e⊒eh & _ & eh=eh' & e'↦eh' & e=e' & MONO✓e')";
        iDestruct (OmoHb_HbIncluded with "e⊒eh M⊢Mh'") as %ehMh'; [done|]; iDestruct (big_sepS_elem_of with "MAXgen_eh1") as "#eh≤eh1"; [exact ehMh'|];
        iDestruct (OmoEq_Le_trans with "[] eh≤eh1") as "eh'≤eh1"; [by iApply OmoEq_sym|]; iApply OmoEq_Le_trans; [done|]; iApply (CWMono_acc with "[$]"); done. }
    iDestruct (view_at_elim with "[] AU") as "AU"; [iSteps|]. iMod "AU" as (E3) "[>H HAUcl]". iDecompose "H" as "?? HAUcl M●2".
    iDestruct (atomic.diaframe_close_right_quant with "HAUcl") as "HAU". iSpecialize ("HAU" $! EMPTY). iSteps.
    epose (reV := (mkOmoEvent EmpDeq x25 ({[length E2]} ∪ M))).
    iMod (OmoAuth_insert_ro γg γl1 _ _ _ _ x25 M _ _ reV with "M●2 [] RTOKEN [] MAXgen_deqid1 []") as (gen) "H"; [iSteps..| |].
    { iPureIntro. split; [|done]. apply queue_step_EmpDeq; [done|simpl; set_solver-]. } iDecompose "H" as (eidx _ _) "_ _ deqId↦el1n deqId_gid deqId✓egV' _ M●2".
    iMod (OmoHb_new_1 with "M●2 deqId✓egV' ehn1✓eVhn1") as "[M●2 #deqId⊒ehn1]"; [simpl; solve_lat|].
    iDestruct (eView_Enq_exact_insert_nonenq _ M CL0 with "[] deqId✓egV'") as "H"; [done|iSteps|]. iDecompose "H".
    oSteps. iExists eh1. iStep. iClearAnonymousIntuitionistics. iSteps. }
  (* Successfully read nonnull value from next field. Prepare for CAS and close the invariant *)
  iApply (bi.wand_elim_r (AllNodes γg γcl CL2)). iStep. rewrite !omo_rewrite_hints. iStep 2 as "Case2 AllNodes2".
  destruct has_next2; last first. { iDecompose "Case2". exfalso. sauto. }
  iDecompose "Case2" as (el1' eVl1' enqid2 γl2 γsl2 vl2 l2 eVenq2 ? Homol1 ? eVl1EV' HCL2Sgenh1 _ _) "el1'✓eVl1' HMl2 ? enqid2✓eVenq2 enqid2↦el2 enqid2⊒el2 ?? ⊒Ml2 l2↦".
  rewrite Homol1 /= in Hgenl1. destruct genl1; [|done]. iAssert ⌜el1' = el1⌝%I as "H"; [sauto|clear Hgenl1]. iDecompose "H" as "? enqid2⊒el2 enqid2↦el2".
  rewrite -eVl1EV' in eVl1EV. inversion eVl1EV. subst. iDestruct (big_sepL_lookup_acc with "AllNodes2") as "H"; [exact HCL2Sgenh1|].
  iDecompose "H" as (zl2 ????? eVenq2EV ? ? ???) "??????????". do 4 (rewrite !omo_rewrite_hints; iStep). iClearAnonymousIntuitionistics.
  iClear "eh1✓eVh1 MAXgen_eh1 eh1_gid ehn1_gid deqid1↦eh1 ehn1✓eVhn1 AllPrevLinks2 AllHeadMsg2 AllTailMsg2 AllEvents2 MONO✓deqid1 deqid1_gid deqid1↪st1 Hst1 ⊒Ml1' RTOKEN RTOKEN'".
  clear dependent eh1 eVh1 Eh1 omo1 omoh2 deqid1 deqid2.
  (* Do a CAS *)
  iStep 14 as (E3 ?? omo3 stlist3 Eh3 omoh3 moh3 Et3 omot3 mot3 CL3 γs3 Mono3 ? eh3 deqid3 st3 genh3 CLh3 eVh3 M' ????????)
   "AllPrevLinks3 AllHeadMsg3 ????????? AllTailMsg3 ? AllEvents3 ?????? ? omot↦3 AllNodes3 CL●3 Mono3 Mh●3 Mt●3 M●3". iExists None. iStep.
  (* intros cas postcondition *)
  iStep 13 as (b3 eh3' genh3' vh3 Vh3 V3 moh3' omoh3' eVh3' eVhn3 ???).
  iStep as (????????????????????? | l1 ??????? Eqgenh3 enqid3 γl3 γsl3 vl3 Ml3 HCL3genh3 eVh3EV ????)
  "????????????????????" | "MONO✓deqid3 CL@genh3 _ Hst3 ⊒Ml3 ? CL@genh1 MAXgen_eh3 ??? ⊒V WCOMMIT ? Mh●3 omoh↦3".
  { iDestruct (view_at_elim with "[] AU") as "AU"; [iSteps|]. iMod "AU" as (E3') "[>H HAUcl]". iDecompose "H" as "?? HAUcl M●2".
    iDestruct (atomic.diaframe_close_right_quant with "HAUcl") as "HAU". iSpecialize ("HAU" $! FAIL_RACE). oSteps. } rewrite !omo_rewrite_hints.
  iDestruct (big_sepL_lookup_acc with "AllNodes3") as "H"; [exact HCL3genh3|]. iDecompose "H" as (eVenq3 omol3 mol3 ??????? has_next3) "⊒Ml3 Hst3 CL@gen3 ?? Ml1● omol1↦ CASE ?".
  have LEwr : omo_write_op omol1 `prefix_of` omo_write_op omol3 by prove_prefix.
  destruct has_next3; last first. { iDecompose "CASE" as (Homol3). exfalso. apply prefix_length in LEwr. rewrite Homol1 Homol3 /= in LEwr. lia. }
  iDecompose "CASE" as (el3 eVl3 enqid3n γl3n γsl3n vl3n l3n eVenq3n ? Homol3 ? eVl3EV ? _ _) "el3✓eVl3 HMl3 CL@Sgenh3 enqid3n✓eVenq3n enqid3n↦el3 enqid3n⊒el3 ?? ⊒Ml3n ?".
  have ? : length omoh3 ≠ 0 by destruct omoh3. rewrite (Nat.sub_add 1 (length omoh3)); [|lia].
  iAssert ⌜ el3 = el1 ⌝%I as "H"; last iDecompose "H". { rewrite Homol1 Homol3 /= in LEwr. apply prefix_length_eq in LEwr; [sauto|done]. }
  iAssert ⌜ l3n = l2⌝%I as "H"; last iDecompose "H". { rewrite -eVl1EV' in eVl3EV. by inversion eVl3EV. }

 (** 3 possible positions to insert a [Deq] event
      1. right after last [Deq] event
      2. right after matching [Enq] event
      3. right after latest [Enq] event that the thread has observed
      Among them, we should choose the latest event *)

  (* Candidate #1 *)
  iDestruct (OmoAuth_OmoCW_l' with "M●3 [$]") as %[eidx3 Heidx3].
  iDestruct (OmoAuth_OmoSnap with "M●3 []") as %Hst3; [exact Heidx3|iSteps|].
  set gen1 := gen_of eidx3.

  (* Candidate #2 *)
  iDestruct (OmoAuth_OmoEinfo' with "M●3 enqid2✓eVenq2") as %[eidx3n Heidx3n].
  set gen2 := gen_of eidx3n.

  (* Candidate #3 *)
  have [ninfo Hninfo] : is_Some (last CL0) by rewrite last_is_Some.
  destruct ninfo as [[[[enqidL γL] γsL] vL] lL].

  iAssert (∃ eVL, OmoEinfo γg enqidL eVL)%I with "[-]" as (eVL) "#enqidL✓eVL".
  { rewrite last_lookup in Hninfo. specialize (M_CL0_l _ _ Hninfo). iDestruct (big_sepS_elem_of with "M_CL0_r") as (eVL) "[#enqidL✓eVL _]"; [done|]. iSteps. }
  iDestruct (OmoAuth_OmoEinfo' with "M●3 enqidL✓eVL") as %[eidxL HeidxL].
  set gen3 := gen_of eidxL.

  set gen := gen1 `max` gen2 `max` gen3.
  have LEgen1gen : gen1 ≤ gen by lia.
  have LEgen2gen : gen2 ≤ gen by lia.
  have LEgen3gen : gen3 ≤ gen by lia.

  iDestruct (OmoAuth_wf with "M●3") as %[OMO_GOOD3 _].
  rewrite -lookup_omo_wr_event in H10. symmetry in H10. specialize (lookup_omo_inj _ _ _ _ _ _ OMO_GOOD3 Heidx3 H10) as Heidx3_gen1'%(f_equal gen_of).
  simpl in Heidx3_gen1'. subst.

  (* Every newer event is Enq v *)
  iAssert ([∗ list] e ∈ drop (gen1 + 1) (omo_write_op omo3), ∃ eV z, OmoEinfo γg e eV ∗ ⌜ eV.(type) = Enq z ⌝)%I with "[-]" as "#AllEnqs".
  { iEval (rewrite big_sepL_forall). iIntros "%g %e %Lookup".
    apply (f_equal ((!!) (length st3 + g)%nat)) in H29 as HstCL'.
    rewrite lookup_app_r in HstCL'; [|by rewrite !fmap_length; lia].
    rewrite !fmap_length in HstCL'. replace (length st3 + g - length st3) with g in HstCL' by lia.
    rewrite !lookup_drop in HstCL', Lookup. rewrite Lookup in HstCL'. symmetry in HstCL'.
    set ng := length omoh3 + (length st3 + g). clear Hninfo.
    have [ninfo Hninfo] : is_Some (CL3 !! ng). { rewrite lookup_lt_is_Some. apply lookup_lt_Some in HstCL'. rewrite !fmap_length in HstCL'. done. }
    destruct ninfo as [[[[e' γl] γsl] v] l].
    rewrite !list_lookup_fmap Hninfo in HstCL'. inversion HstCL'. subst e'.
    iApply (bi.wand_elim_r (AllNodes γg γcl CL3)). iStep. iExists true. iStep 2 as "_ AllNodes3".
    iDestruct (big_sepL_lookup with "AllNodes3") as "H"; [exact Hninfo|]. iDecompose "H". iSteps. }

  (* Since all later events are [Enq], abstract state is monotone increasing *)
  iAssert (∀ g1 g2 st1 st2, ⌜ stlist3 !! g1 = Some st1 → stlist3 !! g2 = Some st2 →
      gen1 ≤ g1 → g1 ≤ g2 → st1 ⊑ st2 ∧ (length st2 = length st1 + (g2 - g1))%nat ⌝)%I with "[M●3]" as %LEst.
  { iIntros "%g1 %g2 %qu1 %qu2 %Lookup1 %Lookup2 %LE1 %LE2". iInduction LE2 as [|] "IH" forall (qu2 Lookup2 LE1).
    - rewrite Lookup1 in Lookup2. inversion Lookup2. iPureIntro. split; [|lia]. #[local] Typeclasses Transparent sqsubseteq. done.
    - replace (S m) with (m + 1) in Lookup2; [|lia].
      have [qu2p Hqu2p] : is_Some (stlist3 !! m). { rewrite lookup_lt_is_Some. apply lookup_lt_Some in Lookup2. lia. }
      have [e He] : is_Some (omo_write_op omo3 !! (m + 1)).
      { rewrite lookup_lt_is_Some -omo_write_op_length (omo_stlist_length E3 _ stlist3); [|done]. apply lookup_lt_Some in Lookup2. lia. }
      have [eV HeV] : is_Some (E3 !! e). { eapply (lookup_omo_event_valid _ _ _ (wr_event (m + 1))); [done|]. by rewrite lookup_omo_wr_event. }
      have STEP : omo.step e eV qu2p qu2  by eapply omo_write_op_step.
      iAssert (∃ z, ⌜ eV.(type) = Enq z ⌝)%I with "[-]" as %[z EV].
      { iDestruct (big_sepL_lookup _ _ (m - gen1) with "AllEnqs") as (eV0 z) "[#e✓eV0 %NEQ]".
        { rewrite lookup_drop. replace (gen1 + 1 + (m - gen1)) with (m + 1); [done|lia]. }
        iDestruct (OmoAuth_OmoEinfo with "M●3 e✓eV0") as %HeV0. rewrite HeV in HeV0. inversion HeV0. subst eV0. by iExists z. }
      iDestruct ("IH" with "[] [] M●3") as %[LEqu1qu2p LENqu2pqu1]; try done.
      inversion STEP; [|by rewrite EV in DEQ|by rewrite EV in EMPDEQ]. have ? : qu2p ⊑ qu2p ++ [(e, v, eV.(sync), eV.(eview))] by apply prefix_app_r.
      iPureIntro. split; [solve_lat|]. rewrite app_length LENqu2pqu1 /=. lia. }

  iAssert (∀ gen st', ⌜ gen1 ≤ gen → stlist3 !! gen = Some st' →
   st'.*1.*1.*1 ++ drop (gen + 1) (omo_write_op omo3) = drop (length omoh3) CL3.*1.*1.*1.*1 ⌝)%I with "[M●3]" as %Hstdropdrop.
  { subst gen. iIntros "%gen %st' %LE %Hgen". iInduction LE as [|gen'] "IH" forall (st' Hgen).
    - subst gen1. rewrite Hst3 in Hgen. inversion Hgen. subst st'. rewrite omo_write_op_length. done.
    - have [st'' Hgen'] : is_Some (stlist3 !! gen'). { rewrite lookup_lt_is_Some. apply lookup_lt_Some in Hgen. lia. }
      iDestruct ("IH" with "[] M●3") as %IH; [done|]. replace (S gen') with (gen' + 1) in Hgen by lia.
      have [e He] : is_Some (lookup_omo omo3 (wr_event (gen' + 1))).
      { rewrite lookup_omo_wr_event lookup_lt_is_Some. apply lookup_lt_Some in Hgen.
        rewrite -(omo_stlist_length _ _ _ OMO_GOOD3) in Hgen. rewrite -omo_write_op_length. done. }
      eapply lookup_omo_event_valid in He as HeV; [|done]. destruct HeV as [eV HeV].
      rewrite lookup_omo_wr_event in He. eapply omo_write_op_step in Hgen as STEP; try done.
      iDestruct (big_sepL_lookup _ _ (gen' - gen1) with "AllEnqs") as (eV' z) "[e✓eV' %EV]".
      { rewrite lookup_drop. replace (gen1 + 1 + (gen' - gen1)) with (gen' + 1) by lia. done. }
      iDestruct (OmoAuth_OmoEinfo with "M●3 e✓eV'") as %HeV'. rewrite HeV in HeV'. inversion HeV'. subst eV'.
      inversion STEP; [|by rewrite EV in DEQ|by rewrite EV in EMPDEQ].
      iPureIntro. rewrite (drop_S _ e) in IH; [|done]. rewrite -IH. clear. by simplify_list_eq. }

  set tst := (enqid2, zl2, eVenq2.(sync), eVenq2.(eview)).
  iAssert (∃ st', ⌜ stlist3 !! gen = Some (tst :: st') ⌝)%I with "[-]" as %[st' Hstgen].
  { have [st Hgen] : is_Some (stlist3 !! gen).
    { rewrite lookup_lt_is_Some. apply lookup_omo_lt_Some in Heidx3, Heidx3n, HeidxL. rewrite -(omo_stlist_length _ _ _ OMO_GOOD3). lia. }
    destruct st3.
    - simpl in H29. have Lookup : (drop (gen1 + 1) (omo_write_op omo3)) !! 0 = (drop (length (omo_write_op omoh3)) CL3.*1.*1.*1.*1) !! 0 by rewrite H29.
      rewrite !lookup_drop !Nat.add_0_r -omo_write_op_length 4!list_lookup_fmap H49 /= in Lookup.

      have [st' Hst'] : is_Some (stlist3 !! (gen1 + 1)).
      { rewrite lookup_lt_is_Some. apply lookup_lt_Some in Lookup. rewrite -omo_write_op_length in Lookup. rewrite -(omo_stlist_length _ _ _ OMO_GOOD3). lia. }

      iDestruct (OmoAuth_OmoEinfo with "M●3 enqid2✓eVenq2") as "%". eapply omo_write_op_step in Hst' as STEP; try done.
      inversion STEP; [|by rewrite -eVenq2EV in EMPDEQ]. rewrite app_nil_l in H56. subst. rewrite -eVenq2EV in ENQ. inversion ENQ. subst v. clear ENQ.
      rewrite -lookup_omo_wr_event in Lookup. eapply lookup_omo_inj in OMO_GOOD3 as INJ; [|exact Heidx3n|exact Lookup]. subst eidx3n.
      have LE1 : gen1 ≤ gen1 + 1 by lia. have LE2 : gen1 + 1 ≤ gen by simpl in *; lia. specialize (LEst _ _ _ _ Hst' Hgen LE1 LE2) as [LEst' _].
      destruct st. { apply prefix_length in LEst'. simpl in *. lia. }
      have EQ : p = tst. { have Lookup' : [tst] !! 0 = Some tst by done. eapply prefix_lookup_Some in Lookup'; [|done]. by inversion Lookup'. } subst p. by iExists st.
    - iDestruct (big_sepL_lookup _ (p :: st3) 0 with "[$]") as (????? eVenq2') "(? & ? & H3)"; [done|].
      rewrite Nat.add_0_r. iDecompose "H3".
      have LE1 : gen1 ≤ gen1 by lia. specialize (LEst _ _ _ _ Hst3 Hgen LE1 LEgen1gen) as [LEst' _]. destruct st. { apply prefix_length in LEst'. simpl in *. lia. }
      have EQ : p = tst. { have Lookup : (tst :: st3) !! 0 = Some tst by done. eapply prefix_lookup_Some in Lookup; [|done]. by inversion Lookup. } subst p. by iExists st. }

  iAssert (∀ g st, ⌜ stlist3 !! g = Some st ⌝ -∗ ⌜ gen1 ≤ g ⌝ -∗
              [∗ list] gen'↦state ∈ st, ∃ enqid' γl' γsl' (z' : Z) l' (eV' : omo_event qevent),
                ⎡mono_list_idx_own γcl (length (omo_write_op omoh3) + gen') (enqid', γl', γsl', #z', l')⎤ ∗ OmoEinfo γg enqid' eV' ∗
                ⌜ state = (enqid', z', eV'.(sync), eV'.(eview)) ∧ eV'.(type) = Enq z' ∧ (z' > 0)%Z ⌝)%I with "[-]" as "#Hst3n".
  { iIntros "%g %st %Hst %LE".
    iApply (bi.wand_elim_r (AllNodes γg γcl CL3)). iStep. iExists true. iStep 2 as "_ AllNodes3". iAssert (emp)%I with "[-M●3 AllNodes3 CL●3]" as "_"; [done|].
    iInduction LE as [|g'] "IH" forall (st Hst). { rewrite Hst3 in Hst. inversion Hst. rewrite omo_write_op_length. done. }
    clear st' Hstgen. have [st' Hst'] : is_Some (stlist3 !! g'). { rewrite lookup_lt_is_Some. apply lookup_lt_Some in Hst. lia. }
    iDestruct ("IH" $! st' with "[] M●3 AllNodes3 CL●3") as "#IH'"; [done|]. replace (S g') with (g' + 1) in Hst by lia.
    have [e He] : is_Some (lookup_omo omo3 (wr_event (g' + 1))).
    { rewrite lookup_omo_wr_event lookup_lt_is_Some. apply lookup_lt_Some in Hst.
      rewrite -(omo_stlist_length _ _ _ OMO_GOOD3) in Hst. rewrite -omo_write_op_length. done. }
    eapply lookup_omo_event_valid in He as HeV; [|done]. destruct HeV as [eV HeV]. eapply omo_write_op_step in Hst as STEP; try done.
    iDestruct (big_sepL_lookup _ _ (g' - gen1) with "AllEnqs") as (eV' z) "[e✓eV' %EV]".
    { rewrite lookup_drop. replace (gen1 + 1 + (g' - gen1)) with (g' + 1) by lia. done. }
    iDestruct (OmoAuth_OmoEinfo with "M●3 e✓eV'") as %HeV'. rewrite HeV in HeV'. inversion HeV'. subst eV'.
    inversion STEP; [|by rewrite EV in DEQ|by rewrite EV in EMPDEQ]. rewrite EV in ENQ. inversion ENQ. subst v. rewrite big_sepL_snoc. iFrame "IH'".

    have LE' : gen1 ≤ g' + 1 by lia. specialize (Hstdropdrop _ _ LE' Hst).
    apply (f_equal ((!!) (length st'))) in Hstdropdrop.
    rewrite lookup_app_l in Hstdropdrop; last first. { subst st. rewrite !fmap_length app_length /=. lia. }
    rewrite -H55 !list_lookup_fmap lookup_app_1_eq lookup_drop /= in Hstdropdrop. symmetry in Hstdropdrop.
    have [ninfo Hlookup] : is_Some (CL3 !! (length omoh3 + length st')). { rewrite lookup_lt_is_Some. apply lookup_lt_Some in Hstdropdrop. by rewrite !fmap_length in Hstdropdrop. }
    destruct ninfo as [[[[e' γl] γsl] v] l]. rewrite !list_lookup_fmap Hlookup in Hstdropdrop. inversion Hstdropdrop. subst e'.

    iDestruct (big_sepL_lookup with "AllNodes3") as "H"; [exact Hlookup|]. iDecompose "H".

    destruct (length omoh3 + length st') eqn:Heq. { destruct omoh3; [done|]. rewrite cons_length in Heq. lia. }
    rewrite -Heq in Hlookup. iDecompose "CL●3". oSteps. iPureIntro. sauto. }

  iDestruct (big_sepL_lookup _ CL3 with "[$]") as "H"; [exact H49|]. iDecompose "H" as (CLe M'' ????) "???????".

  iDestruct (eView_Enq_exact_union γg γcl M M' CL0 CLh3 with "[][][][]") as "H"; [(iStep;done)..|iSteps|iSteps|]. iDecompose "H" as (CL0_h ?? LENCL0h) "???".
  iDestruct (eView_Enq_exact_union γg γcl (M ∪ M') ({[enqid2]} ∪ eview eVenq2 ∪ M'') CL0_h CLe with "[][][][]") as "H"; [iSteps..|].
  iDecompose "H" as (CL3' ?? LENCL3') "M'''_CL3' ? CL●3". rewrite LENCL0h in LENCL3'.

  iAssert (⌜ (length CL0 - length CLh3 = gen3 - gen1)%nat ⌝)%I with "[-]" as %Hgen3gen1.
  { destruct (le_lt_dec (length CL0) (length CLh3)) as [LE|LT].
    - rewrite last_lookup in Hninfo.
      replace (Init.Nat.pred (length CL0)) with (length CL0 - 1) in Hninfo by lia.
      eapply (prefix_lookup_Some _ CL3) in Hninfo as Hlookup; [|prove_prefix].
      eapply (prefix_lookup_inv CLh3) in Hlookup; try done; last first.
      { rewrite lookup_lt_is_Some. apply lookup_lt_Some in Hninfo. lia. }
      specialize (H17 _ _ Hlookup). iDestruct (big_sepS_elem_of _ M' enqidL with "[$]") as "enqidL≤deqid3"; [done|].
      iDestruct (OmoLe_Le with "M●3 enqidL≤deqid3") as %LE'; try done. subst gen1 gen3. iPureIntro. simpl in LE'. lia.
    - rewrite H12 in LT. set idx := length CL0 - 1 - length (omo_write_op omoh3).
      apply (f_equal ((!!) idx)) in H29. rewrite lookup_drop in H29. subst idx.
      replace (length (omo_write_op omoh3) + (length CL0 - 1 - length (omo_write_op omoh3))) with (length CL0 - 1) in H29 by lia.
      have Lookup : CL3 !! (length CL0 - 1) = Some (enqidL, γL, γsL, vL, lL).
      { rewrite last_lookup in Hninfo. replace (Init.Nat.pred (length CL0)) with (length CL0 - 1) in Hninfo by lia.
        eapply (prefix_lookup_Some _ CL3) in Hninfo; [done|prove_prefix]. }
      rewrite !list_lookup_fmap Lookup /= lookup_app_r in H29; [|by rewrite !fmap_length omo_write_op_length; lia].
      rewrite !fmap_length lookup_drop -lookup_omo_wr_event in H29.
      eapply lookup_omo_inj in H29 as INJ; [|exact OMO_GOOD3|exact HeidxL].
      subst eidxL gen3 gen1. simpl. iPureIntro. rewrite H12 omo_write_op_length. lia. }

  iAssert (⌜ (length CLe - length CLh3 = gen2 - gen1)%nat ⌝)%I with "[-]" as %Hgen2gen1.
  { destruct (le_lt_dec (length CLe) (length CLh3)) as [LE|LT].
    - apply (prefix_lookup_inv CLh3) in H49 as Hlookup; [..|prove_prefix]; last first. { rewrite lookup_lt_is_Some. rewrite H55 in LE. lia. }
      specialize (H17 _ _ Hlookup). simpl in H17.

      iDestruct (big_sepS_elem_of _ M' enqid2 with "[$]") as "enqid2≤deqid3"; [done|].
      iDestruct (OmoLe_Le with "M●3 enqid2≤deqid3") as %LE'; try done.
      subst gen1 gen2. iPureIntro. simpl in LE'. lia.
    - rewrite H12 H55 omo_write_op_length in LT. destruct st3; [|simpl in LT; lia]. simpl in H29.
      apply (f_equal ((!!) 0)) in H29.
      rewrite !lookup_drop !Nat.add_0_r -omo_write_op_length in H29.
      do 4 rewrite list_lookup_fmap in H29. rewrite H49 -lookup_omo_wr_event in H29.
      eapply lookup_omo_inj in Heidx3n; try done. subst eidx3n gen1 gen2.
      rewrite H55 H12. iPureIntro. rewrite omo_write_op_length /=. lia. }

  iAssert (⌜ (length CL3' = length omoh3 + length (tst :: st'))%nat ⌝)%I with "[-]" as %HCL3'LEN.
  { rewrite -omo_write_op_length in H12. rewrite H12 in LENCL3'. rewrite LENCL3'.
    have LE1 : gen1 ≤ gen_of eidx3 by done. have LE2 : gen_of eidx3 ≤ gen by done.
    specialize (LEst _ _ _ _ Hst3 Hstgen LE1 LE2) as [_ EQlenst]. rewrite EQlenst H55.
    replace ((length CL0 `max` (length omoh3 + length st3)) `max` (length omoh3 + 1))
      with ((length omoh3 + length st3) `max` ((length CL0) `max` (length omoh3 + 1))) by (clear; lia).
    have MAXeq : ∀ (a b : nat), a `max` b = a + (b - a) by clear; intros; lia.
    rewrite (MAXeq (length omoh3 + length st3)). iPureIntro. lia. }

  set deqId := length E3.
  set Mdeq := {[deqId; enqid2]} ∪ eVenq2.(eview) ∪ M'' ∪ M' ∪ M.
  epose (E3' := E3 ++ [ mkOmoEvent (Deq zl2) V3 Mdeq]).

  iAssert (⌜ OmoUBgen omo3 ({[enqid2]} ∪ eVenq2.(eview) ∪ M'') gen ⌝)%I with "[-]" as %MAXgenp1.
  { iDestruct (OmoUB_into_gen γg _ _ _ _ _ _ enqid2 with "M●3 [$]") as %MAXgen; [done|].
    apply (OmoUBgen_mono _ _ (gen_of eidx3n) gen) in MAXgen; [|lia]. done. }

  iAssert (⌜ OmoUBgen omo3 M' gen ⌝)%I with "[-]" as %MAXgenp2.
  { iDestruct (OmoUB_into_gen _ _ _ _ _ _ _ deqid3 with "M●3 [$]") as %MAXgen; [done|].
    apply (OmoUBgen_mono _ _ (gen_of (wr_event (gen_of eidx3))) gen) in MAXgen; [|simpl;lia]. done. }

  iAssert (⌜ OmoUBgen omo3 M gen ⌝)%I with "[-]" as %MAXgenp3.
  { have [e He] : is_Some (omo_write_op omo3 !! gen).
    { rewrite lookup_lt_is_Some. apply lookup_lt_Some in Hstgen as LT. by rewrite -omo_write_op_length (omo_stlist_length _ _ _ OMO_GOOD3). }
    rewrite -lookup_omo_wr_event in He. eapply lookup_omo_event_valid in He as HeV; [|done]. destruct HeV as [eV HeV].

    iIntros "%e' %e'M". iDestruct (OmoAuth_wf with "M●3") as %[OMO_GOOD _].
    iDestruct (OmoAuth_OmoEview _ _ _ _ _ _ M with "M●3 []") as %MIncl; [iSteps|].
    apply MIncl in e'M as HeV'. eapply lookup_omo_surjective in HeV' as Heidx'; [|done]. destruct Heidx' as [eidx' Heidx'].
    destruct HeV' as [eV' HeV']. iDestruct (big_sepL_lookup with "AllEvents3") as "e'Info"; [exact HeV'|].

    iAssert (⌜ (∀ z, eV'.(type) ≠ Enq z) → gen_of eidx' ≤ gen ⌝)%I with "[-]" as %condLE.
    { iIntros "%NEnq". iAssert (∃ e'' eh' eh'', OmoHb γg γh e' eh' ∗ ask_for eh'' ∗ OmoEq γh eh' eh'' ∗ OmoCW γg γh e'' eh'' ∗
      OmoEq γg e' e'' ∗ CWMonoValid γm e'')%I with "[-]" as (???) "#(e'⊒eh' & _ & eh'=eh'' & e''↦eh'' & e'=e'' & MONO✓e'')".
      { destruct (eV'.(type)); try done. by specialize (NEnq v). }
      iDestruct (OmoHb_HbIncluded with "e'⊒eh' M⊢Mh'") as %eh'Mh'; [done|].
      iDestruct (big_sepS_elem_of _ Mh' with "[$]") as "#eh'≤eh3"; [exact eh'Mh'|]. rewrite -lookup_omo_wr_event in Eqgenh3.
      iDestruct (CWMono_acc with "[$] MONO✓e'' MONO✓deqid3 e''↦eh'' [$] []") as "#e''≤deqid3". { by iApply OmoEq_Le_trans; first iApply OmoEq_sym. }
      iDestruct (OmoEq_Le_trans with "e'=e'' e''≤deqid3") as "e'≤deqid3".
      iDestruct (OmoLe_Le with "M●3 e'≤deqid3") as %LE; try done. iPureIntro. simpl in LE. lia. }

    iExists eidx'. iSplit; [done|]. destruct (eV'.(type)) eqn:HeV'EV; try (iPureIntro; by apply condLE).
    iDestruct (big_sepS_elem_of with "M_CL0_r") as (eV'') "[e'✓eV'' HeV'']"; [exact e'M|]. iDestruct (OmoAuth_OmoEinfo with "M●3 e'✓eV''") as %HeV''.
    rewrite HeV' in HeV''. inversion HeV''. subst eV''. clear HeV''. rewrite HeV'EV. iDestruct "HeV''" as %e'CL0.
    rewrite elem_of_list_lookup in e'CL0. destruct e'CL0 as [idx He']. rewrite !list_lookup_fmap in He'.
    destruct (CL0 !! idx) eqn:Hidx; [|done]. destruct p as [[[[enqid γl] γsl] vl] l]. inversion He'. subst enqid. rewrite last_lookup in Hninfo.
    eapply (prefix_lookup_Some _ CL3) in Hidx as Hidx', Hninfo; [|prove_prefix..].
    iDestruct (gen_le_enq_enq _ _ _ _ _ _ _ _ eidx' eidxL idx (Init.Nat.pred (length CL0)) with "AllPrevLinks3 M●3 [$]") as %?;
      try done; [apply lookup_lt_Some in Hidx; lia|iPureIntro; lia]. }

  eapply OmoUBgen_union in MAXgenp2 as MAXgenp2'; [|exact MAXgenp1].
  eapply OmoUBgen_union in MAXgenp2' as MAXgen; [|exact MAXgenp3].

  iAssert (∀ len, ∃ stlist3', ⌜ interp_omo E3' ((deqId, []) :: take len (drop (gen + 1) omo3)) (tst :: st') stlist3' ∧ stlist3' !! 0 = Some st' ⌝)%I with "[M●3]" as %Hgengood.
  { iIntros "%len". iInduction len as [|] "IH".
    - iPureIntro. exists ([] ++ [st']). split; [|done]. rewrite -(app_nil_l [(deqId, [])]).
      eapply (interp_omo_snoc E3' _ _ _ _ _ ((enqid2, zl2, eVenq2.(sync), eVenq2.(eview)) :: st')). split_and!; try done.
      { subst E3' deqId. by rewrite lookup_app_1_eq. } { constructor. } { subst deqId Mdeq. constructor; try done; simpl; [lia|weak_lat_solver|set_solver-]. }
    - iDestruct ("IH" with "M●3") as %[stlist3' [IH IHst']]. destruct (le_lt_dec (length (drop (gen + 1) omo3)) len) as [LE|LT].
      { rewrite take_ge in IH; [|done]. iExists stlist3'. iPureIntro. rewrite take_ge; [|lia]. done. }
      have [ees Hlast] : is_Some ((drop (gen + 1) omo3) !! len) by rewrite lookup_lt_is_Some.
      destruct ees as [e es]. rewrite (take_S_r _ _ (e, es)); [|done]. rewrite lookup_drop in Hlast.
      specialize (omo_gen_info _ _ _ _ _ _ OMO_GOOD3 Hlast) as (eV & eeVs & st & EID_MATCH & EEVS_VALID & E3e & Lookup_stlist3 & Interp & ES).

      have [stp Hstp] : is_Some (stlist3 !! (gen + len)). { rewrite lookup_lt_is_Some. apply lookup_lt_Some in Lookup_stlist3. lia. }
      have STEP : omo.step e eV stp st.
      { eapply omo_write_op_step; try done; replace (gen + len + 1) with (gen + 1 + len) by lia; try done. rewrite list_lookup_omo_destruct in Hlast. by destruct Hlast as [? _]. }

      inversion STEP.
      + apply interp_omo_length in IH as IHlen.
        have [stl Hstl] : is_Some (last stlist3') by rewrite last_is_Some; destruct stlist3'.
        destruct es as [|e' es']; last first.
        { have LE2 : gen ≤ gen + 1 + len by lia. rewrite Forall_lookup in ES. have Lookup : (e' :: es') !! 0 = Some e' by done.
          specialize (ES _ _ Lookup) as [eV' (E3e' & STEP' & _)]. inversion STEP'; exfalso.
          1-2: apply (f_equal length) in H67; rewrite ?cons_length ?app_length /= in H67; lia. subst. by eapply nil_snoc. }
        iPureIntro. exists (stlist3' ++ [stl ++ [(e, v, eV.(sync), eV.(eview))]]).
        replace ((deqId, []) :: take len (drop (gen + 1) omo3) ++ [(e, [])]) with (((deqId, []) :: take len (drop (gen + 1) omo3)) ++ [(e, [])]); [|by (clear;simplify_list_eq)].
        split; last first. { rewrite lookup_app_l; [done|]. destruct stlist3'; try done. simpl. lia. }
        eapply (interp_omo_snoc _ _ _ eV _ _ stl). split_and!; try done.
        { subst E3'. rewrite lookup_app_l; [done|]. by apply lookup_lt_Some in E3e. } { by rewrite last_cons Hstl. } { by apply queue_step_Enq. }
      + iDestruct (big_sepL_lookup _ _ (gen + len - gen1) with "AllEnqs") as (eV' z) "[#e✓eV' %EV]".
        { rewrite lookup_drop. replace (gen1 + 1 + (gen + len - gen1)) with (gen + 1 + len) by lia. rewrite list_lookup_omo_destruct in Hlast. by destruct Hlast as [? _]. }
        iDestruct (OmoAuth_OmoEinfo with "M●3 e✓eV'") as %HeV'. rewrite /= E3e in HeV'. inversion HeV'. subst eV'. by rewrite DEQ in EV.
      + subst. have LE2 : gen ≤ gen + len by lia. specialize (LEst _ _ _ _ Hstgen Hstp LEgen1gen LE2) as [LEst' _]. apply prefix_length in LEst'. simpl in LEst'. lia. }

  specialize (Hgengood (length (drop (gen + 1) omo3))) as [stlist3' [Hstlist3' Hhdstlist3']]. rewrite take_ge in Hstlist3'; [|done].
  iDestruct (view_at_elim with "[] AU") as "AU". { iAssert (⊒V3)%I as "?"; [done|iSteps]. } iMod "AU" as (?) "[>H HAUcl]".
  iDestruct (atomic.diaframe_close_right_quant with "HAUcl") as "Commit". iDecompose "H" as "?? Commit M●3". iSpecialize ("Commit" $! zl2).

  iDestruct (OmoSnapStates_get with "M●3") as "#STLIST3◯". rewrite -eVh3EV /=.
  iMod (OmoAuth_insert _ _ _ _ _ _ _ _ V3 (M ∪ M' ∪ ({[enqid2]} ∪ eview eVenq2 ∪ M'')) with "M●3 [] WCOMMIT []")
    as (γs3') "(M●3 & #M◯3''' & #deqId↦ehn3 & #deqId✓egV' & _)"; [iSteps| |].
  { iPureIntro. split_and!; try done; subst Mdeq deqId; simpl; try done; [set_solver-|]. replace (M∪_∪_) with (M∪({[enqid2]}∪eVenq2.(eview)∪M''∪M')) by set_solver-. done. }
  iMod (OmoHb_new_1 (eventT2 := loc_event) _ γh _ _ _ _ _ (length Eh3) with "M●3 deqId✓egV' [$]") as "[M●3 #deqId⊒ehn3]"; [weak_lat_solver|].
  iDestruct (OmoHbToken_finish with "M●3") as "M●3".
  pose (omo3' := omo_insert_w omo3 (gen + 1) deqId []).
  iDestruct (OmoLt_get _ _ _ _ _ _ eidx3 (wr_event (gen + 1)) with "M●3") as "#deqid3<deqId".
  { have Lookup : lookup_omo (take (gen1 + 1) omo3) eidx3 = Some deqid3 by rewrite lookup_omo_take; [done|lia]. apply (omo_prefix_lookup_Some _ omo3') in Lookup; [done|].
    apply omo_insert_w_prefix; [apply omo_prefix_take|]. rewrite take_length Nat.min_l; [lia|]. apply lookup_omo_lt_Some in Heidx3. subst gen1. lia. }
  { have EQ : length (take (gen + 1) (omo_write_op omo3)) = gen + 1.
    { rewrite take_length -omo_write_op_length. apply lookup_lt_Some in Hstgen. rewrite -(omo_stlist_length _ _ _ OMO_GOOD3) in Hstgen. lia. }
    rewrite lookup_omo_wr_event omo_insert_w_write_op lookup_app_r; [|lia]. rewrite EQ. replace (gen + 1 - (gen + 1)) with 0 by lia. done. } { simpl. lia. }
  iDestruct (OmoLe_get_from_Lt with "deqid3<deqId") as "deqid3≤deqId".
  iMod (@CWMono_insert_last loc_event _ _ _ _ (wr_event (length omoh3 - 1)%nat) _ _ _ _ _ _ omoh3
    with "Mono3 [Mh●3] MONO✓deqid3 [$] deqId↦ehn3 deqid3≤deqId") as "(MONO3 & #MONO✓deqId & Mh●3)". 2,3: done.
  { rewrite lookup_omo_wr_event H6 last_lookup -omo_write_op_length. replace (Init.Nat.pred (length omoh3)) with (length omoh3 - 1)%nat by lia. done. }

  iApply (bi.wand_elim_r (AllNodes γg γcl CL3)). iStep. iExists true. iStep 2 as "_ AllNodes3".

  have HdeqId : lookup_omo (omo_insert_w omo3 (gen + 1) (length E3) []) (wr_event (gen + 1)) = Some (length E3).
  { rewrite lookup_omo_wr_event omo_insert_w_write_op.
    have EQ : length (take (gen + 1) (omo_write_op omo3)) = gen + 1.
    { rewrite take_length. have ? : gen + 1 ≤ length (omo_write_op omo3); [|lia].
      rewrite -omo_write_op_length. apply lookup_lt_Some in Hstgen. rewrite -(omo_stlist_length _ _ _ OMO_GOOD3) in Hstgen. lia. }
    rewrite lookup_app_r EQ; [|lia]. replace (gen + 1 - (gen + 1)) with 0 by lia. done. }

  iDestruct (OmoSnap_get _ _ _ _ _ _ _ (wr_event (gen + 1)) (gen + 1) with "M●3") as "#deqId↪st'"; try done.
  { have EQ : length (take (gen + 1) stlist3) = gen + 1.
    { rewrite take_length. apply lookup_lt_Some in Hstgen as LT. clear -LT. apply PeanoNat.Nat.min_l.
      have COMP : ∀ (a b : nat), a < b → a + 1 ≤ b by lia. by apply COMP. }
    rewrite lookup_app_r EQ; [|lia]. replace (gen + 1 - (gen + 1)) with 0 by lia. done. }

  iAssert (AllHeadMsg γg γh γs3' γcl γm (omo_write_op (omo_append_w omoh3 (length Eh3) [])))%I with "[-]" as "#AllHeadMsg3'".
  { rewrite omo_append_w_write_op /AllHeadMsg big_sepL_snoc. iSplit.
    - rewrite (big_sepL_forall (AllHeadMsgInner γg γh γs3' γcl γm)). iIntros "%genh %eh %Lookup".
      iDestruct (big_sepL_lookup with "AllHeadMsg3") as "ehInfo"; [exact Lookup|].
      iDestruct "ehInfo" as (??????????) "(? & deqid↦eh & MONO✓deqid & ? & ? & deqid↪st & ?)".
      iDestruct (OmoLe_get _ _ _ _ _ _ (wr_event genh) (wr_event (length omoh3 - 1)) with "Mh●3") as "#eh≤eh3".
      { rewrite lookup_omo_wr_event omo_append_w_write_op lookup_app_l; [done|]. by apply lookup_lt_Some in Lookup. }
      { rewrite lookup_omo_wr_event omo_append_w_write_op lookup_app_l; [done|]. symmetry in Eqgenh3. by apply lookup_lt_Some in Eqgenh3. }
      { simpl. apply lookup_lt_Some in Lookup. rewrite -omo_write_op_length in Lookup. lia. }
      iDestruct (CWMono_acc with "MONO3 MONO✓deqid MONO✓deqid3 deqid↦eh [$] eh≤eh3") as "#deqid≤deqid3".
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
      { rewrite lookup_app_l; [by rewrite lookup_take|]. rewrite take_length. apply lookup_lt_Some in Hstlist3. simpl in *. lia. } repeat iExists _. iFrame "#".
    - iAssert (∃ Ml2, OmoAuth γg γs3' 1 (E3') omo3' (take (gen + 1) stlist3 ++ stlist3') _ ∗ ⎡mono_list_auth_own γcl 1 CL3⎤ ∗ AllNodes γg γcl CL3 ∗ @{V3} OmoEview γl3n Ml2 ∗
        match st' with | [] => emp
        | _ => ∃ el omol2, OmoSnapOmo γl3n γsl3n omol2 ∗ ⌜ omo_write_op omol2 = [0; el] ∧ Ml2 = {[0; el]} ∧ is_Some (CL3 !! (length (omo_write_op omoh3) + 1)%nat) ⌝
        end)%I with "[M●3 CL●3 AllNodes3]" as (Ml2 ) "(M●3 & CL●3 & AllNodes3 & #Ml2◯' & Hst')".
      { subst E3'. destruct st'. { iSteps. } specialize (Hstdropdrop _ _ LEgen1gen Hstgen).
        apply (f_equal ((!!) 1)) in Hstdropdrop. rewrite lookup_drop /= in Hstdropdrop. symmetry in Hstdropdrop. clear Hninfo.
        have [ninfo Hninfo] : is_Some (CL3 !! (length omoh3 + 1)).
        { rewrite lookup_lt_is_Some. apply lookup_lt_Some in Hstdropdrop. rewrite !fmap_length in Hstdropdrop. done. }
        iDestruct (big_sepL_lookup with "AllPrevLinks3") as "H"; [exact Hninfo|].
        replace (length omoh3 + 1) with (S (length omoh3)) by lia. iDecompose "H" as (enqid γl' γsl' v' l' omol' LEN) "??".

        iDestruct (big_sepL_lookup_acc with "AllNodes3") as "H"; [exact H49|].
        clear LEwr. iDecompose "H" as (????? LEwr ???? has_next ?) "??? Ml2● ? CASE ?".

        destruct has_next; last first. { iDecompose "CASE" as (EQ). apply prefix_length in LEwr. rewrite EQ -omo_write_op_length LEN /= in LEwr. lia. }
        iDecompose "CASE" as (???????????? Hlookup' ??) "?? CL@SSgenh3 enqid'✓eVenq' ??????".
        eapply (prefix_lookup_inv CL3') in Hlookup'; last solve_lat; last first.
        { rewrite lookup_lt_is_Some HCL3'LEN /=. apply lookup_lt_Some in Hlookup'. lia. } specialize (H58 _ _ Hlookup') as INCL.

        iDestruct (OmoEinfo_OmoEview_obj with "enqid'✓eVenq' M◯3'''") as %LE; [clear -INCL; set_solver|].
        iExists {[0; x38]}. iSteps. iExists true. iSteps.
        iPureIntro. rewrite lookup_lt_is_Some -omo_write_op_length. apply lookup_lt_Some in Hlookup'. apply prefix_length in H59. lia. }

      iDestruct (OmoLe_get _ _ _ _ _ _ eidx3n _ enqid2 deqId with "M●3") as "#enqid2≤deqId".
      { have Lookup : lookup_omo (take (gen2 + 1) omo3) eidx3n = Some enqid2 by subst; rewrite lookup_omo_take; [|lia].
        apply (omo_prefix_lookup_Some _ (omo_insert_w omo3 (gen + 1) (length E3) [])) in Lookup; [done|].
        apply omo_insert_w_prefix; [apply omo_prefix_take|]. rewrite take_length Nat.min_l; [lia|].
        apply lookup_omo_lt_Some in Heidx3n. subst gen2. lia. }
      { done. } { subst gen2. simpl. lia. } iDecompose "deqId↪st'". oSteps. iExists Ml2. iSplitL; last done.
      destruct st'; [done|]. iDecompose "Hst'". destruct H62 as [[[[[? ?] ?] ?] ?] ?]. iSteps. iExists x32. iSteps. iPureIntro. set_solver-. }

  iDestruct (OmoUB_from_gen with "M●3") as "#MAXgen_deqId".
  { done. } { eapply (OmoUBgen_insert_w _ _ gen (gen + 1)) in MAXgen; [done|lia]. } { simpl. lia. }
  iAssert (HeadLastMsg γg γh γs3' γcl (omo_write_op omo3') (omo_write_op (omo_append_w omoh3 (length Eh3) [])) CL3)%I with "[]" as "HeadLastMsg3".
  { oSteps. iDecompose "deqId↪st'". iSteps. iExists CL3'. iSteps. { iPureIntro. rewrite HCL3'LEN app_length cons_length omo_write_op_length /=. lia. }
    replace (_ ∪ ({[enqid2]} ∪ eVenq2.(eview) ∪ M'' ∪ M')) with (M ∪ M' ∪ ({[enqid2]} ∪ eVenq2.(eview) ∪ M'')) by set_solver-.
    iStep 2. iDestruct ("Hst3n" $! gen (tst :: st') with "[] []") as "Hst3n'"; try done. rewrite (big_sepL_forall _ st'). iIntros "%gen' %state %Hstate".
    iDestruct (big_sepL_lookup _ _ (gen' + 1) with "Hst3n'") as (??????) "(?&?&?)". { replace (gen' + 1) with (S gen') by lia. by rewrite lookup_cons. }
    replace (length omoh3 + (gen' + 1)) with (length (omo_write_op omoh3 ++ [length Eh3]) + gen'); [|rewrite omo_write_op_length app_length /=; lia].
    repeat iExists _. iFrame "#". Unshelve.
    4: { iPureIntro. specialize (Hstdropdrop _ _ LEgen1gen Hstgen). rewrite omo_insert_w_write_op app_length -omo_write_op_length /=.
      have EQ : take (gen + 1) (omo_write_op omo3) ++ deqId :: drop (gen + 1) (omo_write_op omo3) =
                (take (gen + 1) (omo_write_op omo3) ++ [deqId]) ++ drop (gen + 1) (omo_write_op omo3) by clear; simplify_list_eq.
      rewrite EQ. clear EQ. have EQ : gen + 1 + 1 = length (take (gen + 1) (omo_write_op omo3) ++ [deqId]).
      { rewrite app_length take_length /= Nat.min_l; [done|]. rewrite -omo_write_op_length. apply lookup_lt_Some in Hstgen.
        rewrite -(omo_stlist_length _ _ _ OMO_GOOD3) in Hstgen. lia. }
      rewrite EQ drop_app. clear EQ. have EQ : CL3.*1.*1.*1.*1 !! (length omoh3) = Some enqid2.
      { apply (f_equal ((!!) 0)) in Hstdropdrop. by rewrite lookup_drop Nat.add_0_r /= in Hstdropdrop. }
      rewrite (drop_S CL3.*1.*1.*1.*1 tst.1.1.1) in Hstdropdrop; [|done]. clear -Hstdropdrop. simplify_list_eq.
      replace (S (length omoh3)) with (length omoh3 + 1) in Hstdropdrop by lia. done. } all: shelve. }

  iStep. rewrite decide_False; [|lia]. iStep. iExists _. rewrite decide_False; [|lia].
  iDestruct (eView_Enq_exact_insert_nonenq _ (M ∪ M' ∪ ({[enqid2]} ∪ eview eVenq2 ∪ M'')) with "[] deqId✓egV'") as "#H"; [done|iSteps|].
  do 2 (replace ({[length E3]} ∪ (M ∪ M' ∪ ({[enqid2]} ∪ eview eVenq2 ∪ M''))) with Mdeq; last by subst Mdeq; set_solver-). iDecompose "H".
  Unshelve. 1-4: try apply inhabitant; try pure_solver.trySolvePure; try tc_solve. 2: shelve.
  #[local] Typeclasses Opaque HeadLastMsg AllHeadMsg. oSteps. { exfalso. clear -HCL3'LEN. simpl in *. lia. } iExists (length Eh3).
  do 9solveStep. iSplitR. { by iApply (@OmoEq_get_from_Einfo loc_event). } do 8solveStep. iSplitR. { by iApply OmoEq_get_from_Einfo. }
  iClearAnonymousIntuitionistics. iStep. iModIntro. wp_pures. iSteps.
Qed.

#[local] Opaque QueueLocal QueueInv.

Lemma try_enq_spec :
  try_enq_spec' try_enq QueueLocal QueueInv.
Proof.
  intros ??????????. iStep 11. { iStepsSafest. iRight. iSteps. } iIntros (b). destruct b.
  - iStep. iAssert (⊒x0)%I as "?"; [iSteps|]. iSteps. iExists true. iSteps.
  - iStep. iAssert (⊒x0)%I as "?"; [iSteps|]. iSteps. iExists false. iSteps.
Qed.

Lemma try_deq_spec :
  try_deq_spec' try_deq QueueLocal QueueInv.
Proof.
  intros ????????. iStep 11. { iStepsSafest. iRight. iSteps. }
  iIntros (v). destruct (decide (v = (-1)%Z)) as [->|?]; last destruct (decide (v = 0)) as [->|?].
  - iSteps. iExists (-1)%Z. iSteps. apply inhabitant.
  - iStep. iAssert (⊒x0)%I as "?"; [iSteps|]. iSteps. iExists 0%Z. iSteps.
  - iStep. iAssert (⊒x0)%I as "?"; [iSteps|]. iSteps. iExists v, _. rewrite decide_False; [|lia]. iSteps.
Qed.

Lemma enqueue_spec :
  enqueue_spec' enqueue QueueLocal QueueInv.
Proof using All.
  intros ??????????. iStep 4. iLöb as "IH". iStep 10. { iStepsSafest. iRight. iSteps. }
  iIntros (b). destruct (b).
  - iStep. iAssert (⊒x0)%I as "?"; [iSteps|]. iSteps.
  - iStepsSafest. iRight. iSteps.
Qed.

Lemma dequeue_spec :
  dequeue_spec' dequeue QueueLocal QueueInv.
Proof using All.
  intros ????????. iStep 4 as (Φ) "?? AU". iLöb as "IH". iStep 10. { iStepsSafest. iRight. iSteps. }
  iIntros (v). destruct (decide (v = (-1)%Z)) as [->|?]; last destruct (decide (v = 0)) as [->|?].
  - (* try_pop failed. retry *) iStepsSafest. iRight. iSteps. rewrite bool_decide_false; [|lia]. iSteps.
  - (* Empty pop case *) iStep. iAssert (⊒x)%I as "?"; [iSteps|]. iSteps. iExists 0. iSteps.
    rewrite bool_decide_true; [|done]. iSteps.
  - (* Value pop case *) iStep. rewrite decide_False in H; [|lia]. destruct H as [? ->]. iAssert (⊒x)%I as "?"; [iSteps|]. iSteps.
    iExists v. rewrite decide_False; [|lia]. iSteps. rewrite bool_decide_true;[|lia]. iSteps.
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
