From gpfsl.examples Require Import sflib.

From iris.algebra Require Import auth gset gmap agree.
From iris.algebra Require Import lib.mono_list.
From iris.proofmode Require Import tactics.

From gpfsl.base_logic Require Import meta_data.
From gpfsl.examples.algebra Require Import mono_list_list.
From gpfsl.logic Require Import logatom atomics invariants.

From gpfsl.logic Require Import repeat_loop new_delete.
From gpfsl.examples Require Import map_seq loc_helper.
From gpfsl.examples.stack Require Import spec_treiber_composition code_treiber.
From gpfsl.examples.omo Require Import omo omo_preds append_only_loc.

Require Import iris.prelude.options.

(** Prove that Treiber stack satisfies the compositional linearizability
  specifications *)

#[local] Notation next := 0%nat (only parsing).
#[local] Notation data := 1%nat (only parsing).

#[local] Notation history := (history sevent_hist).
#[local] Notation omo_event := (omo_event sevent_hist).

Implicit Types
  (stk : stack_state) (node : event_id * Z * view * eView)
  (mo : list loc_state)
  (omo omoh : omoT)
  (Eh : omo_history.history loc_event)
  (M : eView)
  (s n: loc) (tid: thread_id) (γg γh γs γm : gname).

(** * The invariant and local assertions *)
Section Interp.
Context `{!noprolG Σ, !atomicG Σ, !omoGeneralG Σ, !omoSpecificG Σ sevent_hist stack_state, !appendOnlyLocG Σ}.

#[local] Notation iProp := (iProp Σ).
#[local] Notation vProp := (vProp Σ).

Local Open Scope nat_scope.

(** Physical resources of the node at loc [n] with a possible next node at [on'] *)
Definition StackNode n (on' : option loc) (v : Z) : vProp :=
  (∃ q, (n >> next) ↦{q} #(oloc_to_lit on')) ∗
  (n >> data) ↦ #v
  (* ∗ ⎡ † n … 2 ⎤ *)
  .

(** [StackNode] for each nodes in having values in [vs]. *)
Fixpoint StackNodes (on : option loc) (vs : list Z) : vProp :=
  match (on, vs) with
  | (None, []) => True
  | (Some n, v :: vs') =>
      ∃ on', StackNode n on' v ∗ StackNodes on' vs'
  | _ => False
  end.

#[global] Instance StackNodes_timeless on vs : Timeless (StackNodes on vs).
Proof. elim: vs on => [|v vs' IH] [n|]; apply _. Qed.

Definition AllLinks_inner γg γh γs γm e' : vProp :=
  ∃ (ont : option loc) e (st : stack_state) eV (V : view),
    ⌜ loc_event_msg eV.(type) = (#(oloc_to_lit ont), V)
    ∧ (ont = None ↔ st = []) ⌝ ∗
    OmoEinfo γh e' eV ∗
    OmoCW γg γh e e' ∗ CWMonoValid γm e ∗
    OmoSnap γg γs e st ∗
    match ont with
    | Some n => ∃ q on', @{V} (n >> next) ↦{q} #(oloc_to_lit on')
    | None => emp
    end.

(** There's a node for each head ptr msgs. Used for [!("h" +ₗ #next)] in pop. *)
Definition AllLinks γg γh γs γm es : vProp :=
  [∗ list] e ∈ es, AllLinks_inner γg γh γs γm e.

Global Instance AllLinks_inner_objective γg γh γs γm e' : Objective (AllLinks_inner γg γh γs γm e').
Proof.
  do 5 (apply exists_objective; intros). repeat (apply sep_objective; [by apply _|]).
  by destruct x; apply _.
Qed.

Global Instance AllLinks_objective γg γh γs γm es : Objective (AllLinks γg γh γs γm es) := _.
Global Instance AllLinks_timeless γg γh γs γm es : Timeless (AllLinks γg γh γs γm es) := _.

Definition seen_event_info γg γh γm s (E : history) : vProp :=
  [∗ list] e↦eV ∈ E,
    ∃ el, OmoHb γg γh e el ∗ OmoCW γg γh e el ∗ CWMonoValid γm e.

Definition last_msg_info γg γh es stlist stk ont Vt : vProp :=
  ∃ el eVl,
    ⌜ last es = Some el ∧ loc_event_msg eVl.(type) = (#(oloc_to_lit ont), Vt)
    ∧ last stlist = Some stk ⌝ ∗
    OmoEinfo γh el eVl ∗
    [∗ list] st ∈ stk,
      ∃ (pseV : omo_event),
        OmoEinfo γg st.1.1.1 pseV ∗
        ⌜ pseV.(type) = Push st.1.1.2 ∧ (0 < st.1.1.2)%Z
        ∧ pseV.(eview) = st.2 ∧ pseV.(sync) = st.1.2 ∧ pseV.(sync) ⊑ Vt ⌝.

(** ** Top-level predicates & invariant *)
Definition StackInv γg γs s E omo stlist : vProp :=
  ∃ (γh γsh γm : gname) stk Eh omoh mo (ont : option loc) Vt Mono,
  meta s nroot (γh,γs,γsh,γm) ∗

  (* Logical states *)
  OmoAuth γg γs 1 E omo stlist _ ∗
  OmoAuth γh γsh (1/2)%Qp Eh omoh mo _ ∗

  (* Physical resources *)
  (* head *)
  (∃ Vb, @{Vb} append_only_loc s γh ∅ cas_only) ∗
  (* physical stack *)
  @{Vt} StackNodes ont stk.*1.*1.*2 ∗
  (* all nodes, including the popped ones *)
  AllLinks γg γh γs γm (omo_write_op omoh) ∗
  seen_event_info γg γh γm s E ∗
  CWMono γg γh γm Mono ∗
  last_msg_info γg γh (omo_write_op omoh) stlist stk ont Vt
  .

Definition StackLocal (_ : namespace) γg s M : vProp :=
  ∃ (γh γs γsh γm : gname) Mh,
  meta s nroot (γh,γs,γsh,γm) ∗

  (* Local snapshot of the history and local observation of events *)
  OmoEview γg M ∗
  OmoEview γh Mh
  .

(** ** Properties of assertions *)
Section assertion_props.
Lemma AllLinks_inner_dup γg γh γs γm e' :
  AllLinks_inner γg γh γs γm e' -∗
  AllLinks_inner γg γh γs γm e' ∗ AllLinks_inner γg γh γs γm e'.
Proof.
  iIntros "(%ont & %e & %st & %eV & %V & [%Eqv %Equiv] & #e✓eV & #e↦e' & #MONO✓e & #e↪st & Hont)". destruct ont.
  - iDestruct "Hont" as "(%q & %on' & [l↦ l↦'])".
    iSplitL "l↦"; iExists (Some l),e,st,eV,V; iSplitR; try done; iFrame "#"; iExists (q/2)%Qp,on'; iFrame.
  - iSplitL; iExists None,e,st,eV,V; iSplit; try done; iFrame "#".
Qed.

Lemma AllLinks_dup γg γh γs γm es :
  AllLinks γg γh γs γm es -∗ AllLinks γg γh γs γm es ∗ AllLinks γg γh γs γm es.
Proof. iIntros "AllLinks". rewrite -big_sepL_sep. by iApply big_sepL_mono; [intros;iApply AllLinks_inner_dup|]. Qed.

Lemma AllLinks_access γg γh γs γm es gen e :
  es !! gen = Some e →
  AllLinks γg γh γs γm es -∗
  AllLinks γg γh γs γm es ∗ AllLinks_inner γg γh γs γm e.
Proof.
  iIntros "%esgen AllLinks". iDestruct (AllLinks_dup with "AllLinks") as "[AllLinks Dup]". iFrame "Dup".
  iDestruct (big_sepL_lookup with "AllLinks") as "INNER"; [done|]. iFrame.
Qed.
End assertion_props.
End Interp.

(** * Proofs *)
Section proof.
Context `{!noprolG Σ, !atomicG Σ, !omoGeneralG Σ, !omoSpecificG Σ sevent_hist stack_state, !appendOnlyLocG Σ}.

#[local] Notation iProp := (iProp Σ).
#[local] Notation vProp := (vProp Σ).

Local Tactic Notation "simplify_meta" "with" constr(Hs) :=
  iDestruct (meta_agree with Hs) as %[[[-> ->]%pair_inj ->]%pair_inj ->]%pair_inj.

Lemma StackInv_Linearizable_instance :
  ∀ γg γs s E omo stlist, StackInv γg γs s E omo stlist ⊢ ⌜ Linearizability_omo E omo stlist ⌝.
Proof.
  intros. iDestruct 1 as (??????????) "(_ & M● & _)".
  by iDestruct (OmoAuth_Linearizable with "M●") as %?.
Qed.

Lemma StackInv_OmoAuth_acc_instance :
  ∀ γg γs s E omo stlist,
    StackInv γg γs s E omo stlist ⊢ OmoAuth γg γs 1 E omo stlist _ ∗ (OmoAuth γg γs 1 E omo stlist _ -∗ StackInv γg γs s E omo stlist).
Proof.
  intros. iDestruct 1 as (??????????) "(H1 & M● & H2)". iFrame "M●". iIntros "M●". repeat iExists _. iFrame.
Qed.

Lemma StackLocal_OmoEview_instance :
  ∀ N γg s M, StackLocal N γg s M ⊢ OmoEview γg M.
Proof. intros. by iDestruct 1 as (?????) "(_ & M◯ & _)". Qed.

Lemma StackLocal_Eview_update_instance :
  ∀ N γg s M1 M2, StackLocal N γg s M1 -∗ OmoEview γg M2 -∗ StackLocal N γg s (M1 ∪ M2).
Proof.
  intros. iDestruct 1 as (?????) "(H1 & ⊒M1 & H2)". iIntros "⊒M2".
  iDestruct (OmoEview_union with "⊒M1 ⊒M2") as "⊒M".
  repeat iExists _. iFrame.
Qed.

Lemma new_stack_spec :
  new_stack_spec' new_tstack StackLocal StackInv.
Proof.
  iIntros (N tid V0 Φ) "#⊒V0 Post".
  (* allocate head *)
  wp_lam. wp_apply wp_new; [done..|]. iIntros (s) "([H†|%] & Hs & Hms & _)"; [|done]. wp_let.
  (* initialize head as null, and create protocol *)
  rewrite own_loc_na_vec_singleton. iApply wp_fupd. wp_write.
  iMod (append_only_loc_cas_only_from_na_rel with "⊒V0 Hs") as (γh γsh V1 eV0)
    "(#⊒V1 & Mh● & [#Mh◯ #⊒V1@V0] & omoh↦ & WCOMMIT & #eh0✓eV0 & [%eV0EV %eV0SYNC])"; [done|].

  iAssert (⌜ V0 ⊑ V1 ⌝)%I with "[]" as %LeV0V1.
  { rewrite !view_at_unfold !monPred_at_in. by iDestruct "⊒V1@V0" as %?. }
  set M := {[0%nat]}.
  set eVinit := mkOmoEvent Init V1 M.

  iMod (@OmoAuth_alloc _ _ _ _ _ eVinit init _ _ stack_interpretable with "WCOMMIT") as (γg γs)
    "(M● & #M◯ & #e0↦eh0 & #e0✓eVinit & #e0↪init & WCOMMIT)". { by apply stack_step_Init. } { done. }
  iMod (OmoHb_new_1 with "M● e0✓eVinit eh0✓eV0") as "[M● #e0⊒eh0]"; [rewrite eV0SYNC; solve_lat|].
  iDestruct (OmoHbToken_finish with "M●") as "M●".
  iMod (CWMono_new γg γh) as (γm) "MONO".
  iMod (CWMono_insert_last_last (wr_event 0) with "MONO M● Mh● e0↦eh0") as "(MONO & #MONO✓e0 & M● & Mh●)"; [done|done|].
  (* set Memp : eView := ∅. have EQ : {[0%nat]} ∪ Memp = {[0%nat]} by set_solver-. rewrite EQ. clear EQ Memp. *)

  iMod (meta_set _ _ (γh,γs,γsh,γm) nroot with "Hms") as "#Hms"; [done|].
  rewrite shift_0. iApply ("Post" $! γg). iModIntro. iFrame "⊒V1 WCOMMIT". iSplitL; last iSplitL.
  - iExists _,_,_,[],_,_,_,None. iExists V1,_. iFrame. iFrame "Hms". iSplitL; repeat iSplitL; try done.
    + iDestruct (view_at_intro with "omoh↦") as (Vb) "[? ?]". by iExists _.
    + iExists None,0%nat,[],eV0,V1. rewrite eV0EV. by iFrame "#".
    + iExists 0%nat. iFrame "#".
    + iExists 0%nat,eV0. rewrite eV0EV. iFrame "#". by iSplit.
  - repeat iExists _. iFrame "#".
  - done.
Qed.

Lemma atom_try_push_internal :
  ∀ N (DISJ: N ## histN) s tid γg M V (v : Z) (Posv: 0 < v) (n : loc),
  (* E1 is a snapshot of the history, locally observed by M *)
  ⊒V -∗ StackLocal N γg s M -∗
  (n >> next) ↦ - -∗ (n >> data) ↦ #v -∗
  (* PUBLIC PRE *)
  <<< ∀ γs E omo stlist, ▷ StackInv γg γs s E omo stlist >>>
    try_push_internal [ #s ; #n] @ tid; ↑N
  <<< ∃ (b: bool) V' E' omo' stlist' M',
      (* PUBLIC POST *)
      ⊒V' ∗ ▷ StackInv γg γs s E' omo' stlist' ∗ @{V'} StackLocal N γg s M' ∗
      if b then (
        (* successful case *)
        ⌜ E' = E ++ [mkOmoEvent (Push v) V' M']
        ∧ omo' = omo_append_w omo (length E) []
        ∧ (∃ st, stlist' = stlist ++ [st])
        ∧ V ⊑ V' ∧ M ⊆ M' ⌝ ∗
        OmoUB γg M (length E) ∗
        OmoTokenW γg (length E)
      ) else (
        (* FAIL_RACE case *)
        ⌜ E' = E ∧ omo' = omo ∧ stlist' = stlist ∧ M' = M ⌝ ∗
        (n >> next) ↦ - ∗ (n >> data) ↦ #v
      ),
      (* RETURN VALUE AT COMMITTING POINT *)
      RET #b, emp >>>
  .
Proof.
  intros. iIntros "#⊒V #StackLocal n↦ d↦" (Φ) "AU".
  iDestruct "StackLocal" as (???? Mh0) "(MS & M◯0 & Mh◯0)".

  wp_lam. wp_bind (!ʳˡˣ _)%E.

  (* Inv access #1 *)
  iMod "AU" as (? E1 omo1 stlist1) "[>StackInv [Abort1 _]]".
  iDestruct "StackInv" as (??? stk1 Eh1 omoh1 mo1 ont1 Vt1 Mono1)
    "(MS' & M●1 & Mh●1 & (%Vb1 & omoh↦1) & StackNodes1 & AllLinks1 & #SeenEs1 & MONO1 & #LASTMSG1)".
  simplify_meta with "MS' MS".
  iDestruct (OmoSnapOmo_get with "Mh●1") as "#OMOh◯1".
  (* read *)
  iDestruct (OmoEview_update with "M●1 M◯0 Mh◯0") as (Mh1) "(M●1 & #Mh◯1 & M⊢Mh1 & %LEMh0Mh1)".
  wp_apply (append_only_loc_relaxed_read with "[$Mh●1 $Mh◯1 $omoh↦1 $⊒V]"); [solve_ndisj|].

  iIntros (eh1 gen1 vh1 Vh1 V1 eVh1 eVhn1) "(Pures & Mh●1 & _ & #MAXgen_eh1 & #eh1✓eVh1 & #ehn1✓eVhn1 & _ & #⊒V1 & _ & #Mh◯1' & omoh↦1)".

  iDestruct "Pures" as %(Eqgen1 & eVh1EV & LeVV1 & eVhn1EV & eVhn1SYNC).
  iDestruct (AllLinks_access with "AllLinks1") as "[AllLinks (%on1 & %e1 & %st1 & %eVh1' & %Vh1' & [%EQ _] & #eh1✓eVh1' & _)]"; [exact Eqgen1|].
  iDestruct (OmoEinfo_agree with "eh1✓eVh1 eh1✓eVh1'") as %<-.
  have EQvh1 : vh1 = #(oloc_to_lit on1) by rewrite eVh1EV in EQ; inversion EQ. subst vh1.

  (* Close Inv #1 *)
  iMod ("Abort1" with "[- n↦ d↦]") as "AU".
  { iExists _,_,_,stk1,(Eh1 ++ [eVhn1]). iExists (omo_insert_r omoh1 _ _). iExists mo1,ont1,Vt1,_. iNext.
    rewrite omo_insert_r_write_op. iFrame "∗#". eauto with iFrame. }
  iClear "eh1✓eVh1'". clear e1 st1 Vh1' EQ.

  (* set n's link to what we read from Head *)
  iModIntro. wp_let. wp_op.
  iDestruct "n↦" as (vn) "n↦". wp_write. clear vn Vb1.

  (* Inv access #2 *)
  iMod "AU" as (? E2 omo2 stlist2) "[>StackInv [_ Commit2]]".
  iDestruct "StackInv" as (??? stk2 Eh2 omoh2 mo2 ont2 Vt2 Mono2)
    "(MS' & M●2 & Mh●2 & (%Vb2 & omoh↦2) & StackNodes2 & AllLinks2 & #SeenEs2 & MONO2 & #LASTMSG2)".
  simplify_meta with "MS' MS".

  iCombine "n↦ d↦" as "n↦d↦". iCombine "n↦d↦ M◯0" as "CHUNK".
  iDestruct (view_at_intro_incl with "CHUNK ⊒V1") as (V1') "(#⊒V1' & %LeV1V1' & [n↦d↦ #M◯2A])".
  iDestruct (view_at_elim with "⊒V1 Mh◯1'") as "Mh◯1''".
  iDestruct (OmoAuth_OmoSnapOmo with "Mh●2 OMOh◯1") as %[_ LEwr1wr2].

  (* CAS with possible pointer comparison *)
  wp_apply (append_only_loc_cas_only_cas _ _ _ _ _ _ _ ∅ _ _ _ (oloc_to_lit on1) n _ ∅
    with "[$Mh●2 $Mh◯1'' $omoh↦2 $⊒V1']"); try done; [by destruct on1|].

  iIntros (b2 eh2 gen2 vr2 Vr2 V2 mo2' omoh2' eVh2 eVhn2) "(Pures & #MAXgen_eh2 & #eh2✓eVh2 & #ehn2✓eVhn2 & Mh●2 & #⊒V2 & #Mh◯2 & omoh↦2 & CASE)".
  iDestruct "Pures" as %(Eqgen2 & eVh2EV & LeV1'V2).

  iDestruct "CASE" as "[(Pures & _) | [Pures sVw2]]".
  { (* fail CAS *)
    iDestruct "Pures" as %(-> & NEq & -> & Homoh2' & eVhn2EV & eVhn2SYNC).
    iDestruct (OmoSnapHistory_get with "M●2") as "#E◯2".

    iMod ("Commit2" $! false V2 E2 _ _ M with "[-]") as "HΦ"; [|by iApply "HΦ"].
    iFrame "⊒V2". iSplitR "n↦d↦"; last iSplitR; last iSplitR; try done.
    - iExists _,_,_,stk2,(Eh2 ++ [eVhn2]). iExists omoh2'. iExists mo2,ont2,Vt2,_. iNext.
      subst omoh2'. rewrite omo_insert_r_write_op. iFrame "∗#". eauto with iFrame.
    - iExists γh. repeat iExists _. by iFrame "#".
    - iDestruct (view_at_elim with "⊒V1' n↦d↦") as "[n↦ $]". by iExists _. }

  (* successful CAS *)
  iDestruct "Pures" as %(-> & -> & ->).
  iDestruct "sVw2" as (Vw2 (Eqmo2'' & Homoh2' & eVhn2EV & eVhn2SYNC & LeVr2Vw2 & NEqVr2Vw & NLeV2Vr2 & NEqV1'V2 & LeV2Vw2))
    "(_ & ⊒Vw2 & WCOMMIT)".

  iDestruct "LASTMSG2" as (ehl2 eVhl2) "((%LAST_MSG & %eVhl2EV & %LASTstk2) & ehl2✓eVhl2 & STK2)".
  rewrite last_lookup -omo_write_op_length in LAST_MSG.
  replace (Init.Nat.pred (length omoh2)) with (length omoh2 - 1)%nat in LAST_MSG; [|lia].
  have EQel2 : ehl2 = eh2 by rewrite Eqgen2 in LAST_MSG; inversion LAST_MSG. subst ehl2. clear LAST_MSG.
  iDestruct (OmoEinfo_agree with "eh2✓eVh2 ehl2✓eVhl2") as %<-.
  have [EQ1 EQ2] : ont2 = on1 ∧ Vt2 = Vr2 by rewrite eVhl2EV in eVh2EV; inversion eVh2EV; destruct ont2, on1; inversion H0. subst ont2 Vt2.
  iDestruct (AllLinks_access with "AllLinks2") as "[AllLinks2 (%ont & %e2 & %st2 & %eV2 & %Vl & _ & _ & #e2↦eh2 & _)]"; [exact Eqgen2|].

  have LeVV2 : V ⊑ V2 by solve_lat.
  set psId := length E2.
  set M' := {[psId]} ∪ M.
  set egV' := mkOmoEvent (Push v) V2 M'.
  set E2' := E2 ++ [egV'].
  set stk2' := (psId, v, V2, M') :: stk2.
  set omo2' := omo_append_w omo2 psId [].

  iDestruct (view_at_mono_2 _ V2 with "M◯2A") as "#M◯2A'"; [done|].
  iMod (OmoAuth_insert_last with "M●2 M◯2A' WCOMMIT []") as "(M●2 & #M◯2A'' & #en2↦ehn2 & #en2✓egV' & #en2↪stk2' & WCOMMIT)".
  { iPureIntro. have ? : step psId egV' stk2 stk2'; last by des.
    apply stack_step_Push; try done. subst egV' M'. simpl. set_solver-. }
  iMod (OmoHb_new_1 with "M●2 en2✓egV' ehn2✓eVhn2") as "[M●2 #en2⊒ehn2]"; [rewrite eVhn2SYNC; solve_lat|].
  iDestruct (OmoHbToken_finish with "M●2") as "M●2".
  iMod (CWMono_insert_last_last (wr_event (length omo2)) _ _ _ _ _ _ _ _ (Eh2 ++ [eVhn2])
    with "MONO2 M●2 [Mh●2] en2↦ehn2") as "(MONO2 & #MONO✓en2 & M●2 & Mh●2)".
  { by rewrite lookup_omo_wr_event omo_append_w_write_op omo_write_op_length lookup_app_1_eq. }
  { by rewrite omo_append_w_length Nat.add_sub. } { subst omoh2'. iFrame "Mh●2". }

  iAssert (AllLinks γg γh γs γm (omo_write_op omoh2') ∗ @{Vw2} StackNodes (Some n) stk2'.*1.*1.*2)%I
    with "[AllLinks2 StackNodes2 n↦d↦]" as "[AllLinks2' StackNodes2']".
  { iDestruct (view_at_mono_2 _ Vw2 with "n↦d↦") as "[[n↦1 n↦2] d↦]"; [solve_lat|]; iSplitL "AllLinks2 n↦1".
    - subst omoh2' mo2'. rewrite /AllLinks omo_append_w_write_op big_sepL_snoc.
      iDestruct (AllLinks_dup with "AllLinks2") as "[AllLinks2 AllLinks2']". iFrame.
      iExists (Some n),(length E2),stk2',eVhn2,Vw2. rewrite eVhn2EV. iFrame "#"; eauto with iFrame.
    - rewrite fmap_cons {2}/StackNodes /= -/StackNodes.
      iExists on1. iSplitL "n↦2 d↦".
      + rewrite /StackNode. iSplitL "n↦2"; first iExists _; iFrame.
      + iApply (view_at_mono_2 _ _ _ LeVr2Vw2 with "StackNodes2"). }

  iDestruct (OmoUB_singleton with "en2✓egV'") as "#MAXen2".
  iDestruct (big_sepS_subseteq _ _ M with "MAXen2") as "#MAXen2'"; [set_solver-|].

  iMod ("Commit2" $! true V2 E2' _ _ M' with "[-]") as "HΦ".
  { iFrame "⊒V2 WCOMMIT MAXen2'". iSplitL; last iSplitL; last iSplitL; try done.
    - iExists _,_,_,stk2',(Eh2 ++ [eVhn2]). iExists omoh2'. iExists mo2',(Some n),Vw2,_.
      subst omoh2'. rewrite omo_append_w_write_op. iFrame "∗#". iNext. iSplitL "omoh↦2"; [by iExists _|]. iSplitL.
      { rewrite big_sepL_singleton. iExists _. rewrite Nat.add_0_r. iFrame "en2⊒ehn2 en2↦ehn2 MONO✓en2". }
      iExists (length Eh2),eVhn2. iFrame "#". iSplit.
      + iPureIntro. rewrite eVhn2EV !last_app. by split_and!.
      + subst stk2'. simpl. iSplit; [by iExists egV'; iFrame "#"|].
        iApply big_sepL_intro. iIntros "%i %st %Lookup !>". iDestruct (big_sepL_lookup with "STK2") as (pseV) "[HeV (%&%&%&%& %LE)]"; [done|].
        iExists pseV. iFrame "HeV". iPureIntro. split_and!; try done. solve_lat.
    - iExists γh. repeat iExists _. by iFrame "#".
    - iPureIntro. subst M'. split_and!; try done; [|set_solver-]. by eexists. }
  by iApply "HΦ".
Qed.

Lemma atom_try_push :
  try_push_spec' try_push StackLocal StackInv.
Proof.
  intros N DISJ s tid γg M V v Posv. iIntros "#⊒V #Es" (Φ) "AU".

  (* allocate node *)
  wp_lam. wp_apply wp_new; [done..|].
  iIntros (n) "([H†|%] & n↦ & Hmn)"; [|done].

  (* initialize n's data as v *)
  rewrite own_loc_na_vec_cons own_loc_na_vec_singleton.
  iDestruct "n↦" as "[n↦ d↦]".
  wp_let. wp_op. wp_write.

  awp_apply (atom_try_push_internal with "⊒V Es [n↦] d↦"); [eauto..|].
  { rewrite shift_0. by iExists _. }

  iApply (aacc_aupd with "AU"); [done|].
  iIntros (γs E omo stlist) "SInv".
  iAaccIntro with "SInv"; first by eauto with iFrame.
  iIntros (b V' E' omo' stlist' M') "(⊒V' & SInv & Local & CASE) !>". iRight.
  iExists b, V', E', omo', stlist', M'. iFrame "SInv ⊒V' Local".
  destruct b.
  - iFrame. iIntros "HΦ !> _". wp_if. by iApply "HΦ".
  - iDestruct "CASE" as "(EQ & n↦ & d↦)". iFrame "EQ". iIntros "HΦ !> _". wp_if.
    (* cleaning up *)
    iDestruct "n↦" as (v') "n↦".
    wp_apply (wp_delete _ tid 2 _ [ v'; #v] with "[H† n↦ d↦]"); [done|done|..].
    { rewrite own_loc_na_vec_cons own_loc_na_vec_singleton.
      rewrite shift_0. iFrame "n↦ d↦". iLeft. by iFrame. }
    iIntros "_". wp_seq. by iApply "HΦ".
Qed.

Lemma atom_push :
  push_spec' push StackLocal StackInv.
Proof.
  intros N DISJ s tid γg M V v Posv. iIntros "#⊒V #Es" (Φ) "AU".
  wp_lam.
  (* allocate node *)
  wp_apply wp_new; [done..|].
  iIntros (n) "([H†|%] & n↦ & Hmn)"; [|done].

  (* initialize n's data as v *)
  rewrite own_loc_na_vec_cons own_loc_na_vec_singleton.
  iDestruct "n↦" as "[n↦ Hd]". iAssert (n ↦ -)%I with "[n↦]" as "n↦"; [by iExists _|].
  wp_let. wp_op. rewrite -[Z.to_nat 1]/(1%nat) -{5}(shift_0 n). wp_write.
  iLöb as "IH". wp_rec. wp_bind (try_push_internal _)%E.

  awp_apply (atom_try_push_internal with "⊒V Es n↦ Hd"); [eauto..|].
  iApply (aacc_aupd with "AU"); [done|].
  iIntros (γs E omo stlist) "SInv".
  iAaccIntro with "SInv"; first by eauto with iFrame.
  iIntros (b V' E' omo' stlist' M') "(⊒V' & SInv & Local & CASE) !>". destruct b.
  - iRight. iDestruct "CASE" as "((%HE' & %Homo' & [%st %Hst] & %LeVV' & %SubMM') & MAX & WCOMMIT)".
    iExists V',st,M'. subst E' omo' stlist'. iFrame. iSplit; [done|]. iIntros "HΦ !> _". wp_pures. by iApply "HΦ".
  - iLeft. iDestruct "CASE" as "((%HE' & %Homo' & %Hstlist' & %HM') & n↦ & d↦)". subst E' omo' stlist' M'. iFrame "SInv".
    iIntros "AU !> _". wp_if. iApply ("IH" with "AU H† d↦ Hmn n↦").
Qed.

Lemma atom_try_pop :
  try_pop_spec' try_pop StackLocal StackInv.
Proof.
  intros N DISJ s tid γg M V. iIntros "#⊒V #StackLocal" (Φ) "AU".
  iDestruct "StackLocal" as (???? Mh0) "(MS & M◯0 & Mh◯0)".

  wp_lam. wp_bind (!ᵃᶜ _)%E.

  (* Inv access #1 *)
  iMod "AU" as (? E1 omo1 stlist1) "[>StackInv Acc1]".
  iDestruct "StackInv" as (??? stk1 Eh1 omoh1 mo1 ont1 Vt1 Mono1)
    "(MS' & M●1 & Mh●1 & (%Vb1 & omoh↦1) & StackNodes1 & AllLinks1 & #SeenEs1 & MONO1 & #LASTMSG1)".
  simplify_meta with "MS' MS".
  iDestruct (OmoSnapOmo_get with "Mh●1") as "#OMOh◯1".

  (* read *)
  iDestruct (view_at_intro_incl with "M◯0 ⊒V") as (V') "(#⊒V' & %LeVV' & #M◯0A)".
  iDestruct (OmoEview_update with "M●1 M◯0 Mh◯0") as (Mh1) "(M●1 & #Mh◯1 & Mh0Mh1 & %Mh0LEMh1)".
  wp_apply (append_only_loc_acquire_read with "[$Mh●1 $Mh◯1 $omoh↦1 $⊒V']"); [solve_ndisj|].

  iIntros (eh1 gen1 vh1 Vh1 V1 eVh1 eVhn1) "(Pures & Mh●1 & RCOMMIT & #MAXgen_eh1 & #eh1✓eVh1 & #ehn1✓eVhn1 & #eh1=ehn1 & #⊒V1 & #Mh◯1' & omoh↦1)".
  iDestruct "Pures" as %(Eqgen1 & eVh1EV & LeVVh1V1 & eVhn1EV & eVhn1SYNC).
  iDestruct (AllLinks_access with "AllLinks1")
    as "[AllLinks1 (%on1 & %e1 & %st1 & %eVh1' & %Vh1' & [%HeVh1' %Equivon1] & #eh1✓eVh1' & #e1↦eh1 & #MONO✓e1 & #e1↪st1 & Hon1)]"; [exact Eqgen1|].
  iDestruct (OmoEinfo_agree with "eh1✓eVh1 eh1✓eVh1'") as %<-.
  have [EQ1 EQ2] : vh1 = #(oloc_to_lit on1) ∧ Vh1 = Vh1'. { rewrite eVh1EV in HeVh1'. by inversion HeVh1'. } subst vh1 Vh1'.
  have [LeV'V1 LeVh1V1] : V' ⊑ V1 ∧ Vh1 ⊑ V1 by solve_lat.

  destruct on1 as [n1|]; last first.
  { (* EMPTY POP. The commit point is the read. *)
    have LeVV1 : V ⊑ V1 by solve_lat.
    set ppId := length E1.
    set M' := {[ppId]} ∪ M.
    set egV' := mkOmoEvent EmpPop V1 M'.
    set E1' := E1 ++ [egV'].
    set stk1' := stk1.

    (* Do read-only commit *)
    iDestruct (view_at_mono_2 _ V1 with "M◯0A") as "#M◯0A'"; [done|].

    iAssert (OmoUB γg M e1)%I with "[M●1 Mh●1 MONO1 Mh0Mh1]" as "#MAXgen_e1".
    { rewrite {2}/OmoUB big_sepS_forall. iIntros "%e %eM".
      iDestruct (OmoAuth_OmoEview with "M●1 M◯0") as %MIncl.
      specialize (MIncl _ eM) as [eV Elookup].
      iDestruct (big_sepL_lookup with "SeenEs1") as (?) "(e⊒el & e↦el & MONO✓e)"; [done|].
      iDestruct (OmoHb_HbIncluded with "e⊒el Mh0Mh1") as %e'Mh1; [done|].
      iApply (CWMono_acc with "MONO1 MONO✓e MONO✓e1 e↦el e1↦eh1").
      by rewrite /OmoUB big_sepS_elem_of. }

    iMod (OmoAuth_insert_ro _ _ _ _ _ _ _ _ _ _ egV' with "M●1 M◯0A' RCOMMIT e1↪st1 MAXgen_e1 []")
      as (gen1') "(M●1 & #M◯0A'' & #en1↦ehn1 & #e1=en1 & #en1✓egV' & RCOMMIT & (%eidx & %Heidx & %EQgen))".
    { iPureIntro. split_and!; try done. have EQst1 : st1 = [] by rewrite -Equivon1.
      subst st1 egV' M' ppId. apply stack_step_EmpPop; try done. set_solver-. }
    iMod (OmoHb_new_1 with "M●1 en1✓egV' ehn1✓eVhn1") as "[M●1 en1⊒ehn1]"; [rewrite eVhn1SYNC;solve_lat|].
    iDestruct (OmoHbToken_finish with "M●1") as "M●1".
    iMod (CWMono_insert_Eq with "MONO1 MONO✓e1 e1↦eh1 en1↦ehn1 e1=en1 eh1=ehn1") as "[MONO1 #MONO✓en1]".
    iDestruct (OmoLe_get_from_Eq with "e1=en1") as "e1≤en1".
    iDestruct (OmoUB_mono with "MAXgen_e1 e1≤en1") as "#MAXgen_en1".

    (* commit *)
    iDestruct "Acc1" as "[_ Commit1]".
    iMod ("Commit1" $! EMPTY V1 E1' _ _ M' with "[-]") as "HΦ"; last first.
    { iModIntro. wp_let. wp_op. wp_if. by iApply "HΦ". }

    iFrame "⊒V1 RCOMMIT MAXgen_en1". iSplitL; last iSplit.
    - iExists _,_,_,stk1',(Eh1 ++ [eVhn1]). iExists (omo_insert_r omoh1 _ _). iExists mo1,ont1,Vt1,_. iNext.
      rewrite omo_insert_r_write_op. iFrame "∗#". iSplitL "omoh↦1"; last iSplit; eauto with iFrame.
      rewrite Nat.add_0_r. eauto with iFrame.
    - iExists γh. repeat iExists _. by iFrame "#".
    - iPureIntro. simpl. split_and!; try done; [set_solver-|]. exists gen1'. split; [done|].
      apply lookup_omo_lt_Some in Heidx. rewrite omo_insert_r_length -EQgen in Heidx. done. }

  (* Possibly non-empty, do not commit yet. *)
  (* Leak a fraction of `n1 >> next` to read after closing the inv. *)
  iDestruct "Hon1" as "(%q & %onn & n1↦)".

  (* Close Inv #1 *)
  iDestruct "Acc1" as "[Abort1 _]".
  iMod ("Abort1" with "[-n1↦ Mh0Mh1]") as "AU".
  { iExists _,_,_,stk1,(Eh1 ++ [eVhn1]). iExists (omo_insert_r omoh1 _ _). iExists mo1,ont1, Vt1,_.
    rewrite omo_insert_r_write_op. iFrame "∗#". eauto with iFrame. }

  iModIntro. simpl. wp_let. wp_op. wp_if. wp_op.

  (* read `n1 >> next` non-atomically *)
  iDestruct (view_at_elim with "[] n1↦") as "n1↦".
  { iApply (monPred_in_mono with "⊒V1"). simpl. solve_lat. }
  wp_read. wp_let. wp_bind (casᵃᶜ(_,_,_))%E.

  (* Inv access #2 *)
  iMod "AU" as (? E2 omo2 stlist2) "[>StackInv [_ Commit2]]".
  iDestruct "StackInv" as (??? stk2 Eh2 omoh2 mo2 ont2 Vt2 Mono2)
    "(MS' & M●2 & Mh●2 & (%Vb2 & omoh↦2) & StackNodes2 & AllLinks2 & #SeenEs2 & MONO2 & #LASTMSG2)".
  simplify_meta with "MS' MS".
  iDestruct (OmoAuth_wf with "M●2") as %[OMO_GOOD2 E2WF].

  iMod (rel_objectively_intro (⊒∅) tid with "[]") as "⊒∅".
  { iApply objective_objectively. iApply monPred_in_bot. }

  iDestruct (view_at_elim with "⊒V1 Mh◯1'") as "Mh◯1''".
  iDestruct (OmoAuth_OmoSnapOmo with "Mh●2 OMOh◯1") as %[_ LEwr1wr2].

  wp_apply (append_only_loc_cas_only_cas_live_loc _ _ _ _ _ _ _ ∅ _ _ _ n1 (oloc_to_lit onn) _ ∅
    with "[$Mh●2 $Mh◯1'' $omoh↦2 $⊒V1 ⊒∅]"); try done; [by destruct onn|].

  iIntros (b2 eh2 gen2 vr2 Vr2 V2 mo2' omoh2' eVh2 eVhn2)
    "(Pures & #MAXgen_eh2 & #eh2✓eVh2 & #ehn2✓eVhn2 & Mh●2 & #⊒V2 & #Mh◯2 & omoh↦2 & CASE)".
  iDestruct "Pures" as %(Eqgen2 & eVh2EV & LeV1'V2).

  have LeVV2 : V ⊑ V2 by solve_lat.

  iDestruct "CASE" as "[(Pures & _) | [Pures sVw2]]".
  { (* FAIL_RACE case *)
    (* COMMIT with no change *)
    iDestruct "Pures" as %(-> & NEq & -> & Homoh2' & eVhn2EV & eVhn2SYNC).
    iDestruct (OmoSnapHistory_get with "M●2") as "#E◯2".
    iMod ("Commit2" $! FAIL_RACE V2 E2 _ _ M with "[-]") as "HΦ".
    { iFrame "⊒V2". iSplitL; last iSplit; [..|done].
      - iExists _,_,_,stk2,(Eh2 ++ [eVhn2]). iExists omoh2'. iExists mo2,ont2,Vt2,_. subst omoh2'.
        rewrite omo_insert_r_write_op. iFrame "∗#". eauto with iFrame.
      - iExists γh. repeat iExists _. iDestruct (view_at_mono_2 _ V2 with "M◯0A") as "M◯0A''"; [solve_lat|by iFrame "∗#"]. }
    iModIntro. wp_if. by iApply "HΦ". }

  iDestruct "Pures" as %(-> & -> & ->).
  iDestruct "sVw2" as (Vw2 (Eqmo2'' & Homoh2' & eVhn2EV & eVhn2SYNC & LeVr2Vw2 & NEqVr2Vw & NLeV2Vr2 & NEqV1'V2 & LeEmpVw2))
    "(_ & %LEVwV2 & WCOMMIT)".

  have LeVr2V2: Vr2 ⊑ V2 by etrans.

  iDestruct "LASTMSG2" as (ehl2 eVhl2) "((%LAST_MSG & %eVhl2EV & %LASTstk2) & ehl2✓eVhl2 & STK2)".
  rewrite last_lookup -omo_write_op_length in LAST_MSG.
  replace (Init.Nat.pred (length omoh2)) with (length omoh2 - 1)%nat in LAST_MSG; [|lia].
  have EQel2 : ehl2 = eh2 by rewrite Eqgen2 in LAST_MSG; inversion LAST_MSG. subst ehl2. clear LAST_MSG.
  iDestruct (OmoEinfo_agree with "eh2✓eVh2 ehl2✓eVhl2") as %<-.
  have [EQ1 EQ2] : ont2 = Some n1 ∧ Vt2 = Vr2 by rewrite eVhl2EV in eVh2EV; inversion eVh2EV; destruct ont2; inversion H0. subst ont2 Vt2.
  iDestruct (AllLinks_access with "AllLinks2") as "[AllLinks2 (%ont & %e2 & %st2 & %eV2 & %Vl & _ & _ & #e2↦eh2 & _)]"; [exact Eqgen2|]. clear eV2 Vl st2.

  iAssert (∃ stk2' node, ⌜ stk2 = node :: stk2'⌝)%I with "[StackNodes2]" as "(%stk2' & %node & ->)".
  { destruct stk2; [by iDestruct "StackNodes2" as %?|by iExists _,_]. }

  (* Get the node to pop. *)
  rewrite !fmap_cons /StackNodes.
  iDestruct "StackNodes2" as (onn') "[Node StackNodes2']". fold StackNodes.
  iDestruct "Node" as "[n↦ d↦]".

  iAssert ⌜stk2' = [] ↔ onn' = None⌝%I with "[StackNodes2']" as %EMPTYING_WRITE.
  { unfold iff. iSplit.
    - iIntros (->). destruct onn'; [|done]. by iDestruct "StackNodes2'" as %?.
    - iIntros (->). case Estk2': (stk2'.*1.*1.*2).
      + do 3 apply fmap_nil_inv in Estk2'. done.
      + by iDestruct "StackNodes2'" as %?. }

  iAssert (⊒Vr2)%I with "[]" as "#⊒Vr2". { by iApply (monPred_in_mono with "⊒V2"). }
  iAssert (⌜onn' = onn⌝)%I with "[n↦ n1↦]" as %->.
  { clear. iDestruct (view_at_elim with "⊒Vr2 n↦") as (?) "n↦".
    by iDestruct (own_loc_na_agree with "n1↦ n↦") as %[=[=->%oloc_to_lit_inj]]. }

  set psId := node.1.1.1.
  set ppId := length E2.
  set M' := M ∪ ({[ppId; psId]} ∪ node.2).
  set v := node.1.1.2.
  set pp := mkOmoEvent (Pop v) V2 M'.
  set E2' := E2 ++ [pp].
  set omo2' := omo_append_w omo2 ppId [].

  iSimpl in "STK2". iDestruct "STK2" as "[(%pseV & #psID✓eV & (%EVps & %NZps & %LVIEWps & %VIEWps & %LepseVVr2)) STK2']".
  have LTpseVV2 : pseV.(sync) ⊑ V2 by solve_lat.

  (* Leak the new head node (if any) *)
  rewrite (_ : ∀ on vs, StackNodes on vs -∗ StackNodes on vs ∗
    if on is Some n
    then ∃ q onn, (n >> next) ↦{q} #(oloc_to_lit onn)
    else emp); last first.
  { clear. iIntros (??) "StackNodes". rewrite {1}/StackNodes.
    case on as [n|]; simpl; last by iFrame.
    case vs as [|v vs']; simpl; first done.
    iDestruct "StackNodes" as (?) "[Node StackNodes']".
    iDestruct "Node" as "[(% & n↦1 & n↦2) d↦]".
    iSplitR "n↦1"; eauto with iFrame. }
  iDestruct "StackNodes2'" as "[StackNodes2' onn↦]".

  (* Sync with matching push event *)
  iDestruct (view_at_mono_2 _ V2 with "M◯0A") as "M◯2A'"; [solve_lat|].
  iDestruct (OmoEview_insert_new_obj with "M◯2A' psID✓eV") as "#M◯2A''"; [done|].

  (* Do write commit *)
  iMod (OmoAuth_insert_last _ _ _ _ _ _ (node :: stk2') stk2' _ _ _ pp with "M●2 M◯2A'' WCOMMIT []")
    as "(M●2 & #M◯2A''' & #en2↦ehn2 & #en2✓pp & #en2↪stk2' & WCOMMIT)".
  { iPureIntro. des. split_and!; [..|by subst pp]; try done; last first.
    { subst pp M' ppId psId. rewrite LVIEWps /=. set_solver-. }
    destruct node as [[[a b] c] d].
    apply stack_step_Pop; try done; subst pp; simpl; try subst M' ppId; [by rewrite VIEWps in LTpseVV2|set_solver]. }
  iMod (OmoHb_new_1 with "M●2 en2✓pp ehn2✓eVhn2") as "[M●2 #en2⊒ehn2]"; [rewrite eVhn2SYNC;solve_lat|].
  iDestruct (OmoHbToken_finish with "M●2") as "M●2".
  iMod (CWMono_insert_last_last (wr_event (length omo2)) _ _ _ _ _ _ _ _ (Eh2 ++ [eVhn2])
    with "MONO2 M●2 [Mh●2] en2↦ehn2") as "(MONO2 & #MONO✓en2 & M●2 & Mh●2)".
  { by rewrite lookup_omo_wr_event omo_append_w_write_op omo_write_op_length lookup_app_1_eq. }
  { by rewrite omo_append_w_length Nat.add_sub. } { subst omoh2'. iFrame "Mh●2". }
  iDestruct (OmoUB_singleton with "en2✓pp") as "#MAXen2".
  iDestruct (big_sepS_subseteq _ _ M with "MAXen2") as "MAXen2'"; [set_solver-|].

  iAssert (AllLinks γg γh γs γm (omo_write_op omoh2'))%I with "[onn↦ AllLinks2]" as "AllLinks2'".
  { subst mo2' omoh2'. rewrite /AllLinks omo_append_w_write_op big_sepL_snoc.
    iDestruct (AllLinks_dup with "AllLinks2") as "[AllLinks2 AllLinks2']". iFrame.
    iExists onn,(length E2),stk2',eVhn2,Vw2. iFrame "#". rewrite eVhn2EV. repeat iSplitR; try done.
    destruct onn; [|done]. iDestruct "onn↦" as (??) "onn↦". iExists _,_. iFrame. }

  iMod ("Commit2" $! v V2 E2' _ _ M' with "[- d↦]") as "HΦ".
  { rewrite decide_False; [|lia]. rewrite decide_False; [|lia]. iFrame "⊒V2 WCOMMIT MAXen2'". iSplitL; last iSplit; last iSplit.
    - iExists _,_,_,stk2',(Eh2 ++ [eVhn2]). iExists omoh2'. iExists mo2',onn,Vw2,_. subst omoh2'.
      rewrite omo_append_w_write_op. iFrame "∗#". iSplitL; [by iExists _|]. iSplit.
      { rewrite big_sepL_singleton Nat.add_0_r. iExists _. iFrame "en2⊒ehn2 en2↦ehn2 MONO✓en2". }
      iNext. iExists (length Eh2),eVhn2. iFrame "ehn2✓eVhn2". iSplit.
      + iPureIntro. rewrite eVhn2EV !last_app. by split_and!.
      + iApply big_sepL_intro. iIntros "%i %st %Lookup !>".
        iDestruct (big_sepL_lookup with "STK2'") as (pseV') "[HpseV (%&%&%&%&%)]"; [done|].
        iExists pseV'. iFrame "HpseV". iPureIntro. split_and!; try done. solve_lat.
    - iExists γh. repeat iExists _. replace M' with ({[length E2]} ∪ ({[node.1.1.1]} ∪ pseV.(eview) ∪ M));
        [by iFrame "∗#"|by subst M' ppId; rewrite -LVIEWps; set_solver].
    - iPureIntro. split_and!; try done. set_solver-.
    - iPureIntro. split_and!; try done. by eexists. }

  (* finish CAS successful case *)
  iIntros "!>". wp_if. wp_op.
  iDestruct (view_at_elim with "⊒Vr2 d↦") as "d↦".
  wp_read. by iApply "HΦ". (* leaking data field *)
Qed.

Lemma atom_pop :
  pop_spec' pop StackLocal StackInv.
Proof.
  intros N DISJ s tid γg M V. iIntros "#⊒V #Es" (Φ) "AU".
  iLöb as "IH" forall "#".

  wp_rec.
  awp_apply (atom_try_pop with "⊒V Es"); [eauto..|].
  iApply (aacc_aupd with "AU"); [done|].
  iIntros (γs E omo stlist) "SInv".
  iAaccIntro with "SInv"; first by eauto with iFrame.
  iIntros (v V' E' omo' stlist' M') "(⊒V' & SInv & Local & CASE)".
  destruct (decide (v = -1)); last destruct (decide (v = 0)).
  - iLeft. iDestruct "CASE" as %(-> & -> & -> & ->).
    iFrame "SInv". iIntros  "!> AU !> _".
    wp_let. wp_op. wp_if. rewrite bool_decide_true; [|done]. iApply ("IH" with "AU ⊒V Es").
  - iRight. iClear "IH". iDestruct "CASE" as "([%LeVV' %SubMM'] & MAX & (%HE' & %Hstlist' & %Homo') & RCOMMIT)".
    subst v. iModIntro. iExists 0,V',E',omo',stlist',M'. iFrame "⊒V' SInv Local MAX RCOMMIT". iSplit; [done|].
    iIntros "HΦ !> _". wp_pures. by iApply "HΦ".
  - iRight. iClear "IH". iDestruct "CASE" as "([%LeVV' %SubMM'] & MAX & (%HE' & %Homo' & %Hst) & WCOMMIT)".
    iModIntro. iExists v,V',E',omo',stlist',M'. rewrite decide_False; [|done]. iFrame "⊒V' SInv Local MAX WCOMMIT". iSplit; [done|].
    iIntros "HΦ !> _". wp_pures. rewrite bool_decide_false; [|done]. wp_pures. by iApply "HΦ".
Qed.
End proof.

Definition treiber_stack_impl `{!noprolG Σ, !atomicG Σ, !omoGeneralG Σ, !omoSpecificG Σ sevent_hist stack_state, !appendOnlyLocG Σ}
  : stack_spec Σ := {|
    spec_treiber_composition.StackInv_Linearizable := StackInv_Linearizable_instance;
    spec_treiber_composition.StackInv_OmoAuth_acc := StackInv_OmoAuth_acc_instance;
    spec_treiber_composition.StackLocal_OmoEview := StackLocal_OmoEview_instance;
    spec_treiber_composition.StackLocal_Eview_update := StackLocal_Eview_update_instance;
    spec_treiber_composition.new_stack_spec := new_stack_spec;
    spec_treiber_composition.try_push_spec := atom_try_push ;
    spec_treiber_composition.push_spec := atom_push ;
    spec_treiber_composition.try_pop_spec := atom_try_pop ;
    spec_treiber_composition.pop_spec := atom_pop ;
  |}.
