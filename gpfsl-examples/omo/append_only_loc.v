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

Require Import iris.prelude.options.

(* Append-only location: an abstraction of shared location with an invariant that new written messages are written at the latest timestamp *)

(** Definition of state transition system of append-only location **)
(* Note that it is very simple; precise semantics for memory accesses are described at the conclusion of each memory access rule *)
Notation loc_state := (event_id * (val * view))%type.
Inductive loc_event := ReadE (msg : (val * view)) | WriteE (msg : (val * view)) | UpdateE (e : event_id) (msg : (val * view)).
Definition loc_event_msg (ev : loc_event) :=
  match ev with
  | ReadE msg => msg
  | WriteE msg => msg
  | UpdateE e msg => msg
  end.
Definition UpdateE_eid (ev : loc_event) :=
  match ev with
  | UpdateE e msg => Some e
  | _ => None
  end.

Global Instance loc_event_Inhabited : Inhabited loc_event := populate (WriteE (#0, ∅)).

Inductive loc_step : ∀ (e : event_id) (eV : omo_event loc_event) (st st' : loc_state), Prop :=
  | loc_step_WriteE e eV msg st
      (WRITE : eV.(type) = WriteE msg)
      (LVIEW : e ∈ eV.(eview))
      : loc_step e eV st (e, msg)
  | loc_step_ReadE e eV st
      (READ : eV.(type) = ReadE st.2)
      (LVIEW : e ∈ eV.(eview))
      : loc_step e eV st st
  | loc_step_UpdateE e eV msg st
      (UPDATE : eV.(type) = UpdateE st.1 msg)
      (LVIEW : e ∈ eV.(eview))
      : loc_step e eV st (e, msg)
  .

Global Instance loc_interpretable : Interpretable loc_event loc_state :=
  {
    init := (0%nat, (#☠, ∅));
    step := loc_step
  }.

(** Ghost construction of append-only-location **)
(* Note that it does not involve `omoGeneralG`. It should be assumed in addition to `appendOnlyLocG` *)
Class appendOnlyLocG Σ := AppendOnlyLocG {
  omo_predsG :> omoSpecificG Σ loc_event loc_state;
  loc_writesG :> mono_listG event_id Σ;
  mono_MLG :> mono_listG (time * val * view) Σ;
}.

Definition appendOnlyLocΣ : gFunctors := #[omoSpecificΣ loc_event loc_state; mono_listΣ event_id; mono_listΣ (time * val * view)].

Global Instance subG_appendOnlyLocΣ {Σ} : subG appendOnlyLocΣ Σ → appendOnlyLocG Σ.
Proof. solve_inG. Qed.

Section append_only_loc.
Context {Σ : gFunctors} `{!noprolG Σ, !atomicG Σ, !omoGeneralG Σ, !appendOnlyLocG Σ}.

Notation history := (history loc_event).
Notation iProp := (iProp Σ).
Notation vProp := (vProp Σ).

Implicit Types
  (γe γx γl γw γm : gname)
  (q : Qp)
  (l : loc)
  (ML : list (time * val * view))
  (ζ : absHist)
  (t : time)
  (eV : omo_event loc_event)
  (mo : list loc_state)
  (es : list event_id)
  (E : history)
  (omo : omoT)
  (M : eView)
  (uf : gset val)
  (eidx : event_idx).

Local Open Scope nat_scope.

(** There are two modes of append-only location:
    1. cas_only: concurrent load, concurrent cas are allowed. store is disallowed.
    2. swriter (single writer): store by a unique thread is additionally allowed.  *)
Inductive append_only_type := cas_only | swriter.
Global Instance append_only_type_inhabited : Inhabited append_only_type := populate cas_only.
Global Instance append_only_type_eq_dec : EqDecision append_only_type.
Proof. solve_decision. Qed.

(* Exclusive permission to perform single-writer store *)
Definition swriter_token_def l γe es : vProp :=
  ∃ γx γl γw γm ML t v V,
    ⌜ γx = encode (γl,γw,γm) ∧ last ML = Some (t, v, V) ⌝ ∗
    OmoGname γe γx ∗
    ⎡mono_list_auth_own γw (1/2 + 1/2/2)%Qp es⎤ ∗
    ⎡mono_list_auth_own γm (1/2 + 1/2/2)%Qp ML⎤ ∗
    l sn⊒{γl} {[t := (v, V)]}.
Definition swriter_token_aux : seal (@swriter_token_def). Proof. by eexists. Qed.
Definition swriter_token := unseal (@swriter_token_aux).
Definition swriter_token_eq : @swriter_token = _ := seal_eq _.

(* ---- Definitions used internally by `append_only_loc` ---- *)
Definition ML_time_mono ML : Prop :=
  ∀ (i1 i2 : nat) (t1 t2 : time),
    ML.*1.*1 !! i1 = Some t1 → ML.*1.*1 !! i2 = Some t2 → (i1 < i2)%nat → (t1 < t2)%positive.

Definition Hist_comparable ζ : Prop :=
  ∀ t v V, ζ !! t = Some (v, V) → ∃ vl : lit, v = #vl ∧ vl ≠ LitPoison.

Definition Hist_ML_valid ζ ML : Prop :=
  ∀ (t : time) (v : val) (V : view), ζ !! t = Some (v, V) ↔ (t, v, V) ∈ ML.

Definition uf_valid ζ uf : Prop :=
  ∀ t v V, ζ !! t = Some (v, V) → ζ !! (t + 1)%positive = None → v ∈ uf ∨ no_earlier_time ζ t.

Definition OMO_ML_valid γe γl γs l omo ML : vProp :=
  [∗ list] ees; minfo ∈ omo; ML,
    ∃ e es eV t v V,
      ⌜ ees = (e, es) ∧ loc_event_msg eV.(type) = (v, V) ∧ minfo = (t, v, V) ⌝ ∗
      OmoEinfo γe e eV ∗ OmoSnap γe γs e (e, (v, V)) ∗
      @{eV.(sync)} l sn⊒{γl} {[t := (v, V)]} ∗
      [∗ list] e' ∈ es,
        ∃ eV',
          ⌜ loc_event_msg eV'.(type) = (v, V) ⌝ ∗
          OmoEinfo γe e' eV' ∗ OmoSnap γe γs e' (e, (v, V)) ∗
          @{eV'.(sync)} l sn⊒{γl} {[t := (v, V)]}.

(* Main definition of `append_only_loc` *)
Definition append_only_loc_def l γe uf (ty : append_only_type) : vProp :=
  ∃ γx γl γw γm γs E omo mo q ML ζ,
    ⌜ γx = encode (γl,γw,γm) ⌝ ∗
    OmoGname γe γx ∗

    OmoAuth γe γs (1/2)%Qp E omo mo _ ∗
    ⎡mono_list_auth_own γw q (omo_write_op omo)⎤ ∗
    ⎡mono_list_auth_own γm q ML⎤ ∗
    l at↦{γl} ζ ∗
    OMO_ML_valid γe γl γs l omo ML ∗

    ⌜ ML_time_mono ML
    ∧ Hist_comparable ζ
    ∧ Hist_ML_valid ζ ML
    ∧ uf_valid ζ uf
    ∧ match ty with
      | cas_only => q = 1%Qp
      | swriter => q = (1/2/2)%Qp
      end ⌝.
Definition append_only_loc_aux : seal (@append_only_loc_def). Proof. by eexists. Qed.
Definition append_only_loc := unseal (@append_only_loc_aux).
Definition append_only_loc_eq : @append_only_loc = _ := seal_eq _.

Global Instance swriter_timeless l γe es : Timeless (swriter_token l γe es).
Proof. rewrite swriter_token_eq. apply _. Qed.
Global Instance append_only_loc_timeless l γe uf ty : Timeless (append_only_loc l γe uf ty).
Proof. rewrite append_only_loc_eq. apply _. Qed.

Lemma swriter_token_exclusive_obj l γe V1 V2 es1 es2 :
  @{V1} swriter_token l γe es1 -∗ @{V2} swriter_token l γe es2 -∗ False.
Proof.
  iIntros "SW1 SW2". rewrite !swriter_token_eq.
  iDestruct "SW1" as (????????) "([%Hγx %LAST] & #Hγx & ES● & _)".
  iDestruct "SW2" as (????????) "([%Hγx' %LAST'] & #Hγx' & ES●' & _)".
  rewrite !view_at_objective_iff.

  iDestruct (OmoGname_agree with "Hγx Hγx'") as %<-. encode_agree Hγx.
  iDestruct (mono_list_auth_own_agree with "ES● ES●'") as %[LE <-].
  replace (1/2 + 1/2/2 + (1/2 + 1/2/2))%Qp with (1 + 1/2)%Qp in LE; [|compute_done].
  exfalso.
  rewrite Qp.le_ngt in LE.
  specialize (Qp.lt_add_r 1 (1/2)%Qp). done.
Qed.

Lemma swriter_token_exclusive l γe es1 es2 :
  swriter_token l γe es1 -∗ swriter_token l γe es2 -∗ False.
Proof.
  iIntros "SW1 SW2".
  iDestruct (view_at_intro with "SW1") as (?) "[_ SW1]".
  iDestruct (view_at_intro with "SW2") as (?) "[_ SW2]".
  iApply (swriter_token_exclusive_obj with "SW1 SW2").
Qed.

Lemma swriter_token_type_obj_1 l γe V1 V2 es uf ty :
  @{V1} swriter_token l γe es -∗ @{V2} append_only_loc l γe uf ty -∗ ⌜ ty = swriter ⌝.
Proof.
  iIntros "SW omo↦". rewrite swriter_token_eq append_only_loc_eq.
  iDestruct "SW" as (????????) "([%Hγx %LASTes] & #Hγx & ES● & ML● & #l⊒)".
  iDestruct "omo↦" as (??????????) "(%& %Hγx' & #Hγx' & M● & ES●' & ML●' & l↦ & #ML✓ & (%ML_t_valid & %ζ_comp & %ζ_ML_valid & %ζ_uf_valid & %Hty))".
  destruct ty; try done. subst q.
  rewrite !view_at_objective_iff.

  iDestruct (OmoGname_agree with "Hγx Hγx'") as %<-. encode_agree Hγx.
  iDestruct (mono_list_auth_own_agree with "ES● ES●'") as %[LE ->].
  rewrite Qp.le_ngt in LE.
  specialize (Qp.lt_add_r 1 (1/2 + 1/2/2)%Qp). done.
Qed.

Lemma swriter_token_type_obj_2 l γe V es uf ty :
  swriter_token l γe es -∗ @{V} append_only_loc l γe uf ty -∗ ⌜ ty = swriter ⌝.
Proof.
  iIntros "SW omo↦". iDestruct (view_at_intro with "SW") as (?) "[_ SW]".
  iApply (swriter_token_type_obj_1 with "SW omo↦").
Qed.

Lemma swriter_token_type l γe es uf ty :
  swriter_token l γe es -∗ append_only_loc l γe uf ty -∗ ⌜ ty = swriter ⌝.
Proof.
  iIntros "SW omo↦".
  iDestruct (view_at_intro with "SW") as (?) "[_ SW]".
  iDestruct (view_at_intro with "omo↦") as (?) "[_ omo↦]".
  iApply (swriter_token_type_obj_1 with "SW omo↦").
Qed.

Lemma OmoAuth_swriter_token_agree_obj_1 l γe γs V1 V2 uf ty q E omo mo es :
  OmoAuth γe γs q E omo mo _ -∗
  @{V1} append_only_loc l γe uf ty -∗
  @{V2} swriter_token l γe es -∗
  ⌜ es = omo_write_op omo ⌝.
Proof.
  iIntros "M● omo↦ SW". rewrite swriter_token_eq append_only_loc_eq.
  iDestruct "SW" as (????????) "([%Hγx %LASTes] & #Hγx & ES● & ML● & #⊒e)".
  iDestruct "omo↦" as (??????????) "(%& %Hγx' & #Hγx' & M●' & ES●' & ML●' & l↦ & #ML✓ & (%ML_t_valid & %ζ_comp & %ζ_ML_valid & %ζ_uf_valid & %Hty))".
  rewrite !view_at_objective_iff.

  iDestruct (OmoGname_agree with "Hγx Hγx'") as %<-. encode_agree Hγx.
  iDestruct (OmoAuth_agree with "M● M●'") as %(<- & <- & <- & <-).
  by iDestruct (mono_list_auth_own_agree with "ES● ES●'") as %[_ ->].
Qed.

Lemma OmoAuth_swriter_token_agree_obj_2 l γe γs V uf ty q E omo mo es :
  OmoAuth γe γs q E omo mo _ -∗
  @{V} append_only_loc l γe uf ty -∗
  swriter_token l γe es -∗
  ⌜ es = omo_write_op omo ⌝.
Proof.
  iIntros "M● omo↦ SW". iDestruct (view_at_intro with "SW") as (?) "[_ SW]".
  iApply (OmoAuth_swriter_token_agree_obj_1 with "M● omo↦ SW").
Qed.

Lemma OmoAuth_swriter_token_agree l γe γs uf ty q E omo mo es :
  OmoAuth γe γs q E omo mo _ -∗
  append_only_loc l γe uf ty -∗
  swriter_token l γe es -∗
  ⌜ es = omo_write_op omo ⌝.
Proof.
  iIntros "M● omo↦ SW".
  iDestruct (view_at_intro with "omo↦") as (?) "[_ omo↦]".
  iDestruct (view_at_intro with "SW") as (?) "[_ SW]".
  iApply (OmoAuth_swriter_token_agree_obj_1 with "M● omo↦ SW").
Qed.

Lemma OmoAuth_append_only_loc_frac_valid_obj γe γs q E omo mo V l uf ty :
  OmoAuth γe γs q E omo mo _ -∗
  @{V} append_only_loc l γe uf ty -∗
  ⌜ (q ≤ 1/2)%Qp ⌝.
Proof.
  iIntros "M● omo↦". rewrite append_only_loc_eq.
  iDestruct "omo↦" as (??????????)
    "(%& %Hγx' & #Hγx' & M●' & ES●' & ML●' & l↦ & #ML✓ & (%ML_t_valid & %ζ_comp & %ζ_ML_valid & %ζ_uf_valid & %Hty))".
  rewrite !view_at_objective_iff.
  iDestruct (OmoAuth_agree with "M● M●'") as %(<- & <- & <- & <-).
  iCombine "M● M●'" as "M●".
  iDestruct (OmoAuth_frac_valid with "M●") as %LE.
  by rewrite -{2}Qp.half_half -Qp.add_le_mono_r in LE.
Qed.

Lemma OmoAuth_append_only_loc_frac_valid γe γs q E omo mo l uf ty :
  OmoAuth γe γs q E omo mo _ -∗
  append_only_loc l γe uf ty -∗
  ⌜ (q ≤ 1/2)%Qp ⌝.
Proof.
  iIntros "M● omo↦".
  iDestruct (view_at_intro with "omo↦") as (?) "[_ omo↦]".
  iApply (OmoAuth_append_only_loc_frac_valid_obj with "M● omo↦").
Qed.

Lemma swriter_to_cas_only_obj_1 l γe V0 V1 es uf :
  @{V0} append_only_loc l γe uf swriter -∗ @{V1} swriter_token l γe es -∗ @{V0} append_only_loc l γe uf cas_only.
Proof.
  iIntros "omo↦ SW". rewrite !append_only_loc_eq swriter_token_eq.
  iDestruct "SW" as (????????) "([%Hγx %LASTes] & #Hγx & ES● & ML● & #⊒e)".
  iDestruct "omo↦" as (??????????) "(%& %Hγx' & #Hγx' & M●' & ES●' & ML●' & l↦ & #ML✓ & (%ML_t_valid & %ζ_comp & %ζ_ML_valid & %ζ_uf_valid & %Hty))".
  rewrite !view_at_objective_iff. subst q.

  iDestruct (OmoGname_agree with "Hγx Hγx'") as %<-. encode_agree Hγx.
  iDestruct (mono_list_auth_own_agree with "ES● ES●'") as %[_ ->].
  iDestruct (mono_list_auth_own_agree with "ML● ML●'") as %[_ <-].
  iCombine "ES● ES●'" as "ES●". iCombine "ML● ML●'" as "ML●".
  replace (1/2 + 1/2/2 + 1/2/2)%Qp with 1%Qp by compute_done.

  iExists γx,γl,γw,γm,γs,E,omo,mo. iExists 1%Qp,ML,ζ. iFrame "∗#%". done.
Qed.

Lemma swriter_to_cas_only_obj_2 l γe V es uf :
  @{V} append_only_loc l γe uf swriter -∗ swriter_token l γe es -∗ @{V} append_only_loc l γe uf cas_only.
Proof.
  iIntros "omo↦ SW". iDestruct (view_at_intro with "SW") as (?) "[_ SW]".
  iApply (swriter_to_cas_only_obj_1 with "omo↦ SW").
Qed.

Lemma swriter_to_cas_only l γe es uf :
  append_only_loc l γe uf swriter -∗ swriter_token l γe es -∗ append_only_loc l γe uf cas_only.
Proof.
  iIntros "omo↦ SW". iCombine "omo↦ SW" as "RES".
  iDestruct (view_at_intro with "RES") as (V) "[#⊒V [omo↦ SW]]".
  iDestruct (swriter_to_cas_only_obj_1 with "omo↦ SW") as "omo↦".
  iDestruct (view_at_elim with "⊒V omo↦") as "omo↦". done.
Qed.

Lemma cas_only_to_swriter_obj l γe γs q mo E omo M e eidx V uf :
  e ∈ M →
  lookup_omo omo eidx = Some e →
  gen_of eidx = (length omo - 1)%nat →
  OmoAuth γe γs q E omo mo _ -∗
  OmoEview γe M -∗
  @{V} append_only_loc l γe uf cas_only -∗
  OmoAuth γe γs q E omo mo _ ∗
  @{V} append_only_loc l γe uf swriter ∗
  swriter_token l γe (omo_write_op omo).
Proof.
  iIntros "%IN %Heidx %EQgen M● #⊒M omo↦".
  iDestruct (OmoAuth_wf with "M●") as %[OMO_GOOD _].
  iDestruct (OmoAuth_omo_nonempty with "M●") as %Nomo.
  have NZomo : length omo ≠ 0 by destruct omo.
  have [[e' es'] Hlast] : is_Some (omo !! (length omo - 1)) by rewrite lookup_lt_is_Some; lia.
  have He' : lookup_omo omo (wr_event (length omo - 1)) = Some e' by rewrite lookup_omo_wr_event /omo_write_op list_lookup_fmap Hlast.

  eapply lookup_omo_event_valid in Heidx as HeV; [|done]. destruct HeV as [eV HeV].
  iDestruct (OmoEinfo_get with "M●") as "#e✓eV"; [done|].
  iDestruct (OmoEq_get with "M●") as "#e=e'".
  { exact Heidx. } { exact He'. } { done. }

  rewrite append_only_loc_eq.
  iDestruct "omo↦" as (??????????) "(%& %Hγx & #Hγx & M●' & ES● & ML● & l↦ & #ML✓ & (%ML_t_valid & %ζ_comp & %ζ_ML_valid & %ζ_uf_valid & %Hty))".
  subst q0. rewrite !view_at_objective_iff.
  iDestruct (OmoAuth_agree with "M● M●'") as %(<- & <- & <- & <-).
  iDestruct "ES●" as "[ES●1 [ES●2 ES●3]]". iCombine "ES●1 ES●3" as "ES●1".
  iDestruct "ML●" as "[ML●1 [ML●2 ML●3]]". iCombine "ML●1 ML●3" as "ML●1".

  iDestruct (big_sepL2_length with "ML✓") as %EQlenML.
  have [minfo Hminfo] : is_Some (ML !! (length omo - 1)) by rewrite lookup_lt_is_Some -EQlenML; lia.
  iDestruct (big_sepL2_lookup with "ML✓") as (?? eV' ?? V') "((%EQ1 & %eV'EV & %EQ2) & e'✓eV' & _ & l⊒@SYNC & BIG)"; [done|done|].
  inversion EQ1. subst e0 es minfo. clear EQ1.

  iAssert (l sn⊒{γl} {[t := (v, V')]})%I with "[-]" as "#l⊒".
  { destruct eidx.
    - simpl in EQgen. subst gen. rewrite lookup_omo_ro_event /omo_read_op list_lookup_fmap Hlast /= in Heidx.
      iDestruct (big_sepL_lookup with "BIG") as (?) "(%eVEV & #e✓eV' & _ & l⊒@SYNC')"; [done|].
      iDestruct (OmoEinfo_agree with "e✓eV e✓eV'") as %<-.
      iDestruct (OmoEinfo_OmoEview with "e✓eV ⊒M") as "#⊒SYNC"; [done|].
      iDestruct (view_at_elim with "⊒SYNC l⊒@SYNC'") as "?". done.
    - simpl in EQgen. subst gen. rewrite lookup_omo_wr_event /omo_write_op list_lookup_fmap Hlast /= in Heidx.
      inversion Heidx. subst e'.
      iDestruct (OmoEinfo_agree with "e✓eV e'✓eV'") as %<-.
      iDestruct (OmoEinfo_OmoEview with "e✓eV ⊒M") as "#⊒SYNC"; [done|].
      iDestruct (view_at_elim with "⊒SYNC l⊒@SYNC") as "?". done. }

  iFrame "M●". iSplitR "ES●1 ML●1".
  - iExists γx,γl,γw,γm,γs,E,omo,mo. iExists (1/2/2)%Qp,ML,ζ. iFrame "∗#%". done.
  - rewrite swriter_token_eq. iExists γx,γl,γw,γm,ML,t,v,V'. iFrame "∗#". iPureIntro. split; try done.
    rewrite last_lookup -EQlenML. replace (Init.Nat.pred (length omo)) with (length omo - 1) by lia. done.
Qed.

Lemma cas_only_to_swriter l γe γs q mo E omo uf :
  OmoAuth γe γs q E omo mo _ -∗
  append_only_loc l γe uf cas_only -∗
  OmoAuth γe γs q E omo mo _ ∗
  append_only_loc l γe uf swriter ∗
  swriter_token l γe (omo_write_op omo).
Proof.
  iIntros "M● omo↦". rewrite append_only_loc_eq.
  iDestruct (OmoAuth_wf with "M●") as %[OMO_GOOD _].
  iDestruct (OmoAuth_omo_nonempty with "M●") as %Nomo.
  have NZomo : length omo ≠ 0 by destruct omo.
  have [[e es] Hlast] : is_Some (omo !! (length omo - 1)) by rewrite lookup_lt_is_Some; lia.
  have He : lookup_omo omo (wr_event (length omo - 1)) = Some e by rewrite lookup_omo_wr_event /omo_write_op list_lookup_fmap Hlast.

  eapply lookup_omo_event_valid in He as HeV; [|done]. destruct HeV as [eV HeV].
  iDestruct (OmoEinfo_get with "M●") as "#e✓eV"; [done|].
  iDestruct (OmoEq_get with "M●") as "#e=e"; try done.

  iDestruct "omo↦" as (??????????) "(%& %Hγx & #Hγx & M●' & ES● & ML● & l↦ & #ML✓ & (%ML_t_valid & %ζ_comp & %ζ_ML_valid & %ζ_uf_valid & %Hty))".
  subst q0.
  iDestruct (OmoAuth_agree with "M● M●'") as %(<- & <- & <- & <-).
  iDestruct "ES●" as "[ES●1 [ES●2 ES●3]]". iCombine "ES●1 ES●3" as "ES●1".
  iDestruct "ML●" as "[ML●1 [ML●2 ML●3]]". iCombine "ML●1 ML●3" as "ML●1".

  iDestruct (AtomicPtsTo_AtomicSync with "l↦") as "#SY".
  iDestruct (AtomicSync_AtomicSeen with "SY") as "l⊒".

  iDestruct (big_sepL2_length with "ML✓") as %EQlenML.
  have [[[t v] V] MLlast] : is_Some (last ML).
  { rewrite last_is_Some. unfold not. intros. subst ML. by destruct omo. }

  iFrame "M●". iSplitR "ES●1 ML●1".
  - iExists γx,γl,γw,γm,γs,E,omo,mo. iExists (1/2/2)%Qp,ML,ζ. iFrame "∗#%". done.
  - rewrite swriter_token_eq. iExists γx,γl,γw,γm,ML,t,v,V. iFrame "∗#". iSplitR; [done|].
    iApply AtomicSeen_mono_lookup_singleton; try done.
    unfold Hist_ML_valid in *. specialize (ζ_ML_valid t v V). rewrite ζ_ML_valid elem_of_list_lookup.
    rewrite last_lookup in MLlast. eexists. done.
Qed.

Lemma append_only_loc_swriter_from_na_rel l (vl : lit) (P : vProp) :
  vl ≠ LitPoison →
  P -∗ l ↦ #vl -∗
  |==> ∃ γe γs V eV (omo := omo_append_w [] 0%nat []),
    ⊒V ∗
    OmoAuth γe γs (1/2)%Qp [eV] omo [(0%nat, (#vl, V))] _ ∗
    @{V} (OmoEview γe {[0%nat]} ∗ P ∗ swriter_token l γe (omo_write_op omo)) ∗
    append_only_loc l γe ∅ swriter ∗
    OmoTokenW γe 0%nat ∗
    OmoEinfo γe 0%nat eV ∗
    ⌜ eV.(type) = WriteE (#vl, V) ∧ eV.(sync) = V ⌝.
Proof.
  iIntros "%NPoison P l↦".
  iMod (AtomicPtsToX_from_na_cofinite_rel_view _ _ ∅ with "P l↦") as (γl t V) "(_ & #⊒V & P@V & lsw & l↦)".
  iAssert (@{V} l sw↦{γl} {[t := (#vl, V)]})%I with "[l↦]" as "l↦".
  { rewrite AtomicPtsTo_eq. iExists t. done. }
  iAssert (@{V} (l at↦{γl} {[t := (#vl, V)]} ∗ l sn⊒{γl} {[t := (#vl, V)]}))%I with "[l↦ lsw]" as "[l↦ #l⊒]".
  { iCombine "l↦ lsw" as "RES". iApply (view_at_mono with "RES"); [done|]. iIntros "[l↦ lsw]".
    iDestruct (AtomicPtsTo_SW_to_CON_1 with "l↦ lsw") as "[l↦ sync]".
    rewrite AtomicSync_AtomicSeen. iFrame. }
  iDestruct (view_at_elim with "⊒V l↦") as "l↦".

  set einit := 0.
  set M := {[einit]}.
  set eVinit := mkOmoEvent (WriteE (#vl, V)) V M.
  set stinit := (einit, (#vl, V)).
  set ML := [(t, #vl, V)].

  iMod (@mono_list_own_alloc event_id _ _ [einit]) as (γw) "[ES● #ES◯]".
  iMod (mono_list_own_alloc ML) as (γm) "[ML● #ML◯]".
  remember (encode (γl,γw,γm)) as γx eqn:Hγx.

  iMod (OmoAuth_alloc_Gname_no_Token eVinit stinit γx) as (γe γs) "(M● & #⊒M & #einit✓eVinit & #einit↪stinit & #Hγx & WCOMMIT)".
  { by apply loc_step_WriteE. } { done. }
  iDestruct (OmoHbToken_finish with "M●") as "[M● M●']".

  iModIntro. iExists γe,γs,V,eVinit. iFrame "⊒V M● P@V ⊒M WCOMMIT einit✓eVinit".
  iDestruct "ES●" as "[ES●1 [ES●2 ES●3]]". iDestruct "ML●" as "[ML●1 [ML●2 ML●3]]".
  iCombine "ES●1 ES●3" as "ES●1". iCombine "ML●1 ML●3" as "ML●1".
  iSplitL "ES●1 ML●1"; last iSplitL; try done.
  - rewrite swriter_token_eq. iExists γx,γl,γw,γm,ML,t,#vl,V. iFrame "∗#%". done.
  - rewrite append_only_loc_eq. iExists γx,γl,γw,γm,γs,_,_,_. iExists _,[(t,#vl,V)],_. iFrame "∗#%". iSplit.
    + rewrite /OMO_ML_valid big_sepL2_singleton. iExists einit,[],eVinit,t,#vl,V. iFrame "#". rewrite big_sepL_nil. done.
    + iPureIntro. split_and!; try done.
      * rewrite /ML_time_mono. intros. rewrite !list_lookup_fmap in H,H0. destruct i1, i2; try done. lia.
      * rewrite /Hist_comparable. intros. rewrite lookup_singleton_Some in H. destruct H as [<- EQ].
        inversion EQ. subst v V0. exists vl. done.
      * rewrite /Hist_ML_valid. intros. split; intros.
        -- rewrite lookup_singleton_Some in H. destruct H as [<- EQ]. inversion EQ. subst v V0.
           rewrite elem_of_list_lookup. exists 0. done.
        -- rewrite elem_of_list_lookup in H. destruct H as [i Hi]. destruct i; try done. inversion Hi. subst t0 v V0.
           rewrite lookup_singleton_Some. done.
      * rewrite /uf_valid. intros. rewrite lookup_singleton_Some in H. destruct H as [<- EQ]. inversion EQ. subst v V0. clear EQ.
        right. rewrite /no_earlier_time. intros. destruct H as [[v' V'] Ht'].
        rewrite lookup_singleton_Some in Ht'. destruct Ht' as [<- EQ]. inversion EQ. subst v' V'. clear EQ. done.
Qed.

Lemma append_only_loc_swriter_from_na l (vl : lit) :
  vl ≠ LitPoison →
  l ↦ #vl -∗
  |==> ∃ γe γs V eV (omo := omo_append_w [] 0%nat []),
    ⊒V ∗
    OmoAuth γe γs (1/2)%Qp [eV] omo [(0%nat, (#vl, V))] _ ∗
    @{V} (OmoEview γe {[0%nat]} ∗ swriter_token l γe (omo_write_op omo)) ∗
    append_only_loc l γe ∅ swriter ∗
    OmoTokenW γe 0%nat ∗
    OmoEinfo γe 0%nat eV ∗
    ⌜ eV.(type) = WriteE (#vl, V) ∧ eV.(sync) = V ⌝.
Proof.
  iIntros "%NPoison l↦".
  iMod (append_only_loc_swriter_from_na_rel _ _ emp with "[] l↦") as (????) "(H1 & H2 & (H3 & _ & H4) & H5)"; try done.
  iModIntro. repeat iExists _. iFrame.
Qed.

Lemma append_only_loc_cas_only_from_na_rel l (vl : lit) (P : vProp) :
  vl ≠ LitPoison →
  P -∗ l ↦ #vl -∗
  |==> ∃ γe γs V eV (omo := omo_append_w [] 0%nat []),
    ⊒V ∗
    OmoAuth γe γs (1/2)%Qp [eV] omo [(0%nat, (#vl, V))] _ ∗
    @{V} (OmoEview γe {[0%nat]} ∗ P) ∗
    append_only_loc l γe ∅ cas_only ∗
    OmoTokenW γe 0%nat ∗
    OmoEinfo γe 0%nat eV ∗
    ⌜ eV.(type) = WriteE (#vl, V) ∧ eV.(sync) = V ⌝.
Proof.
  iIntros "%NPoison P l↦".
  iMod (append_only_loc_swriter_from_na_rel with "P l↦") as (????) "(#⊒V & M● & (#⊒M & P@V & SW) & omo↦ & WCOMMIT & #elem & Pures)"; [done|].
  iDestruct (view_at_elim with "⊒V SW") as "SW".
  iDestruct (swriter_to_cas_only with "omo↦ SW") as "omo↦".

  iModIntro. iExists γe,γs,V,eV. iFrame "∗#%".
Qed.

Lemma append_only_loc_cas_only_from_na l (vl : lit) :
  vl ≠ LitPoison →
  l ↦ #vl -∗
  |==> ∃ γe γs V eV (omo := omo_append_w [] 0%nat []),
    ⊒V ∗
    OmoAuth γe γs (1/2)%Qp [eV] omo [(0%nat, (#vl, V))] _ ∗
    @{V} OmoEview γe {[0%nat]} ∗
    append_only_loc l γe ∅ cas_only ∗
    OmoTokenW γe 0%nat ∗
    OmoEinfo γe 0%nat eV ∗
    ⌜ eV.(type) = WriteE (#vl, V) ∧ eV.(sync) = V ⌝.
Proof.
  iIntros "%NPoison l↦".
  iMod (append_only_loc_cas_only_from_na_rel _ _ emp with "[] l↦") as (????) "(H1 & H2 & [H3 _] & H4)"; try done.
  iModIntro. repeat iExists _. iFrame.
Qed.

Lemma append_only_loc_to_na Ec l γe γs q E omo mo uf ty :
  ↑histN ⊆ Ec →
  ⎡ hist_inv ⎤ -∗ OmoAuth γe γs q E omo mo _ -∗ append_only_loc l γe uf ty ={Ec}=∗
  ∃ v e eV, l ↦ v ∗ OmoAuth γe γs (q + 1/2)%Qp E omo mo _ ∗ OmoEinfo γe e eV ∗
    ⌜ last (omo_write_op omo) = Some e ∧ (loc_event_msg eV.(type)).1 = v ⌝.
Proof.
  iIntros "%INCL #HInv M● omo↦". rewrite append_only_loc_eq.
  iDestruct "omo↦" as (??????????) "(%& %Hγx & #Hγx & M●' & ES● & ML● & l↦ & #ML✓ & (%ML_t_valid & %ζ_comp & %ζ_ML_valid & %ζ_uf_valid & %Hty))".
  iDestruct (OmoAuth_agree with "M● M●'") as %(<- & <- & <- & <-).
  iCombine "M● M●'" as "M●".

  iMod (AtomicPtsTo_to_na with "HInv l↦") as (t v) "[l↦ [%VAL %LATEST]]"; [done|].
  iDestruct (OmoAuth_wf with "M●") as %[OMO_GOOD _].
  iDestruct (OmoAuth_omo_nonempty with "M●") as %Nomo.
  have NZomo : length omo ≠ 0 by destruct omo.
  iDestruct (big_sepL2_length with "ML✓") as %EQlenML.

  have [[[t' v'] V'] Hlast] : is_Some (last ML).
  { rewrite last_is_Some. unfold not. intros. subst ML. done. }
  unfold Hist_ML_valid in *.
  have Ht' : (t', v', V') ∈ ML.
  { rewrite elem_of_list_lookup. rewrite last_lookup in Hlast. eexists. done. }
  rewrite -ζ_ML_valid in Ht'.

  have EQ : t = t'.
  { have CASE : (t < t' ∨ t = t' ∨ t' < t)%positive by lia.
    destruct CASE as [COMP|[COMP|COMP]]; try done.
    - unfold no_earlier_time in *.
      have Ht'' : is_Some (ζ !! t') by done.
      specialize (LATEST t' Ht'').
      have COMP' : (t' ≤ t)%positive by done.
      lia.
    - destruct (ζ !! t) eqn:Heq; try done. destruct p as [v'' V]. inversion VAL. subst v''. clear VAL.
      rewrite ζ_ML_valid elem_of_list_lookup in Heq. destruct Heq as [i Hi].
      rewrite last_lookup in Hlast.
      replace (Init.Nat.pred (length ML)) with (length ML - 1) in Hlast by lia.
      unfold ML_time_mono in *.

      have CONDLT : i < length ML - 1.
      { have LE : i ≤ length ML - 1 by apply lookup_lt_Some in Hi; lia.
        destruct (decide (i = length ML - 1)) as [->|NEQ]; try lia.
        rewrite Hi in Hlast. inversion Hlast. subst t' v' V'. lia. }
      have COND1 : ML.*1.*1 !! i = Some t by rewrite !list_lookup_fmap Hi.
      have COND2 : ML.*1.*1 !! (length ML - 1) = Some t' by rewrite !list_lookup_fmap Hlast.
      specialize (ML_t_valid _ _ _ _ COND1 COND2 CONDLT). lia. }
  subst t'.
  rewrite Ht' in VAL. inversion VAL. subst v'. clear VAL.

  have [[e es] He] : is_Some (last omo) by rewrite last_is_Some.
  rewrite !last_lookup in Hlast,He. rewrite -EQlenML in Hlast.
  iDestruct (big_sepL2_lookup with "ML✓") as (??????) "((%EQ1 & %eVEV & %EQ2) & #e✓eV & _)"; [done|done|].
  inversion EQ1. inversion EQ2. subst e0 es0 t0 v0 V'. clear EQ1 EQ2.

  iModIntro. iExists v,e,eV. iFrame "∗#%". iPureIntro. split.
  - rewrite last_lookup -omo_write_op_length /omo_write_op list_lookup_fmap He. done.
  - rewrite eVEV. done.
Qed.

Lemma append_only_loc_own_loc_prim l γe uf ty :
  append_only_loc l γe uf ty ⊢ ∃ C : cell, l p↦{1} C.
Proof.
  iIntros "omo↦". rewrite append_only_loc_eq.
  iDestruct "omo↦" as (??????????) "(%& %Hγx & #Hγx & M●' & ES● & ML● & l↦ & #ML✓ & (%ML_t_valid & %ζ_comp & %ζ_ML_valid & %ζ_uf_valid & %Hty))".
  rewrite AtomicPtsTo_own_loc_prim. done.
Qed.

Lemma append_only_loc_read l γe γs mo E omo M uf ty o tid V Vb (Ec : coPset) :
  Relaxed ⊑ o → ↑histN ⊆ Ec →
  {{{ OmoAuth γe γs (1/2)%Qp E omo mo _ ∗ OmoEview γe M ∗ @{Vb} append_only_loc l γe uf ty ∗ ⊒V }}}
    Read o #l @ tid; Ec
  {{{ e gen v' V' V'' eV eV', RET v';
      let E' := E ++ [eV'] in
      let e' := length E in
      let omo' := omo_insert_r omo gen e' in
      let M' := {[e']} ∪ M in
      ⌜ omo_write_op omo !! gen = Some e
      ∧ loc_event_msg eV.(type) = (v', V')
      ∧ V ⊑ V''
      ∧ eV'.(type) = ReadE (v', V')
      ∧ eV'.(sync) = V'' ⌝ ∗
      OmoAuth γe γs (1/2)%Qp E' omo' mo _ ∗
      OmoTokenR γe e' ∗ (* use this to commit the event and update [OmoAuth] *)
      OmoUB γe M e ∗
      OmoEinfo γe e eV ∗
      OmoEq γe e e' ∗
      OmoEinfo γe e' eV' ∗
      ⊒V'' ∗
      (if decide (AcqRel ⊑ o) then ⌜V' ⊑ V''⌝ else ▽{tid} ⊒V') ∗
      @{V''} OmoEview γe M' ∗
      @{Vb ⊔ V''} append_only_loc l γe uf ty }}}.
Proof.
  iIntros "%MOMORD %INCL" (Φ) "(M● & #⊒M & omo↦ & #⊒V) Post". rewrite append_only_loc_eq.
  iDestruct "omo↦" as (??????????) "(%& %Hγx & #Hγx & M●' & ES● & ML● & l↦ & #ML✓ & (%ML_t_valid & %ζ_comp & %ζ_ML_valid & %ζ_uf_valid & %Hty))".
  rewrite !view_at_objective_iff.
  iDestruct (OmoAuth_agree with "M● M●'") as %(<- & <- & <- & <-).
  iDestruct (OmoAuth_wf with "M●") as %[OMO_GOOD _].
  iDestruct (OmoEview_nonempty with "⊒M") as %NEmp.
  iDestruct (OmoAuth_OmoEview with "M● ⊒M") as %MIncl.
  iDestruct (big_sepL2_length with "ML✓") as %EQlenML.
  iCombine "M● M●'" as "M●".

  iDestruct (view_at_intro_incl with "⊒M ⊒V") as (V') "(#⊒V' & %LeVV' & #⊒M@V')".

  (* Extract latest observed message *)
  iAssert (∃ e ew eidx tw vw Vw,
    ⌜ e ∈ M ∧ lookup_omo omo eidx = Some e ∧ ML !! (gen_of eidx) = Some (tw, vw, Vw) ∧ OmoUBgen omo M (gen_of eidx) ⌝ ∗
    l sn⊒{γl} {[tw := (vw, Vw)]} ∗ OmoSnap γe γs e (ew, (vw, Vw)))%I
      with "[-]" as "(%&%&%&%&%&%& (%eIn & %Heidx & %MLgen & %MAXgen) & #l⊒ & #e↪st)".
  { iClear "Post ⊒M@V'". iInduction M as [|e M NotIn] "IH" using set_ind_L; [done|].
    destruct (decide (M = ∅)) as [Memp|NEmp'].
    - have EQ : {[e]} ∪ M = {[e]} by set_solver. rewrite !EQ. clear EQ.
      have HeV : e ∈ ({[e]} ∪ M) by set_solver-. apply MIncl in HeV.
      eapply lookup_omo_surjective in HeV as Heidx; [|done]. destruct Heidx as [eidx Heidx]. destruct HeV as [eV HeV].
      have [[e' es'] Hgen] : is_Some (omo !! (gen_of eidx)).
      { rewrite lookup_lt_is_Some. apply lookup_omo_lt_Some in Heidx. done. }
      have [minfo Hminfo] : is_Some (ML !! (gen_of eidx)).
      { rewrite lookup_lt_is_Some -EQlenML. apply lookup_lt_Some in Hgen. done. }
      iDestruct (big_sepL2_lookup with "ML✓") as (?? eV' tw vw Vw) "((%EQ1 & %eV'EV & %EQ2) & #e'✓eV' & #e'↪st' & l⊒@SYNC' & BIG)"; [done|done|].
      inversion EQ1. subst e0 es minfo. clear EQ1.
      destruct eidx.
      + simpl in Hgen. rewrite lookup_omo_ro_event /omo_read_op list_lookup_fmap Hgen /= in Heidx.
        iDestruct (big_sepL_lookup with "BIG") as (?) "(%eVEV & e✓eV & e↪st & l⊒@SYNC)"; [done|].
        iDestruct (OmoEinfo_get with "M●") as "#e✓eV'"; [done|].
        iDestruct (OmoEinfo_agree with "e✓eV e✓eV'") as %->.
        iDestruct (OmoEinfo_OmoEview _ e with "e✓eV ⊒M") as "⊒SYNC"; [set_solver-|].
        iDestruct (view_at_elim with "⊒SYNC l⊒@SYNC") as "l⊒".
        iExists e,e',(ro_event gen i'),tw,vw,Vw. iFrame "l⊒ e↪st". iPureIntro. split_and!; try done.
        * set_solver-.
        * rewrite lookup_omo_ro_event /omo_read_op list_lookup_fmap Hgen. done.
        * rewrite /OmoUBgen. intros.
          have EQ : e0 = e by set_solver. subst e0. exists (ro_event gen i'). split.
          -- rewrite lookup_omo_ro_event /omo_read_op list_lookup_fmap Hgen. done.
          -- done.
      + simpl in Hgen. rewrite lookup_omo_wr_event /omo_write_op list_lookup_fmap Hgen /= in Heidx. inversion Heidx. subst e'. clear Heidx.
        iDestruct (OmoEinfo_get with "M●") as "#e✓eV"; [done|].
        iDestruct (OmoEinfo_agree with "e✓eV e'✓eV'") as %<-.
        iDestruct (OmoEinfo_OmoEview _ e with "e✓eV ⊒M") as "⊒SYNC"; [set_solver-|].
        iDestruct (view_at_elim with "⊒SYNC l⊒@SYNC'") as "l⊒".
        iExists e,e,(wr_event gen),tw,vw,Vw. iFrame "l⊒ e'↪st'". iPureIntro. split_and!; try done.
        * set_solver-.
        * rewrite lookup_omo_wr_event /omo_write_op list_lookup_fmap Hgen. done.
        * rewrite /OmoUBgen. intros.
          have EQ : e0 = e by set_solver. subst e0. exists (wr_event gen). split; [|done].
          rewrite lookup_omo_wr_event /omo_write_op list_lookup_fmap Hgen. done.
    - iDestruct (OmoEview_split with "⊒M") as "[⊒e ⊒M']"; [set_solver-|done|].
      iDestruct ("IH" with "[] [] ⊒M' ES● ML● l↦ M●") as "#H"; [done|..].
      { iPureIntro. intros. apply MIncl. set_solver. }
      iDestruct "H" as (e' ew' eidx' tw' vw' Vw') "((%e'IN & %Heidx' & %MLgen' & %MAXgen) & l⊒' & e'↪st')".
      have HeV : e ∈ ({[e]} ∪ M) by set_solver-. apply MIncl in HeV.
      eapply lookup_omo_surjective in HeV as Heidx; [|done]. destruct Heidx as [eidx Heidx]. destruct HeV as [eV HeV].

      destruct (le_lt_dec (gen_of eidx) (gen_of eidx')) as [LE|LT].
      { (* [e] is non-latest event -> induction hypothesis is the answer *)
        iExists e',ew',eidx',tw',vw',Vw'. iFrame "l⊒' e'↪st'". iPureIntro. split_and!; try done.
        - set_solver.
        - rewrite /OmoUBgen. intros.
          have CASE : e0 = e ∨ e0 ∈ M by set_solver.
          destruct CASE as [->|IN].
          + exists eidx. done.
          + apply MAXgen. done. }

      (* [e] is the latest event *)
      have [[e'' es''] Hgen] : is_Some (omo !! (gen_of eidx)).
      { rewrite lookup_lt_is_Some. apply lookup_omo_lt_Some in Heidx. done. }
      have [minfo Hminfo] : is_Some (ML !! (gen_of eidx)).
      { rewrite lookup_lt_is_Some -EQlenML. apply lookup_lt_Some in Hgen. done. }
      iDestruct (big_sepL2_lookup with "ML✓") as (?? eV'' tw vw Vw) "((%EQ1 & %eV''EV & %EQ2) & e''✓eV'' & e''↪st'' & l⊒@SYNC' & BIG)"; [done|done|].
      inversion EQ1. subst e0 es minfo. clear EQ1. destruct eidx.
      + simpl in Hgen. rewrite lookup_omo_ro_event /omo_read_op list_lookup_fmap Hgen /= in Heidx.
        iDestruct (big_sepL_lookup with "BIG") as (?) "(%eVEV & e✓eV & e↪st & l⊒@SYNC)"; [done|].
        iDestruct (OmoEinfo_get with "M●") as "#e✓eV'"; [done|].
        iDestruct (OmoEinfo_agree with "e✓eV e✓eV'") as %->.
        iDestruct (OmoEinfo_OmoEview _ e with "e✓eV ⊒M") as "⊒SYNC"; [set_solver-|].
        iDestruct (view_at_elim with "⊒SYNC l⊒@SYNC") as "l⊒".
        iExists e,e'',(ro_event gen i'),tw,vw,Vw. iFrame "l⊒ e↪st". iPureIntro. split_and!; try done.
        * set_solver-.
        * rewrite lookup_omo_ro_event /omo_read_op list_lookup_fmap Hgen. done.
        * rewrite /OmoUBgen. intros.
          have CASE : e0 = e ∨ e0 ∈ M by set_solver. destruct CASE as [->|IN].
          -- exists (ro_event gen i'). split; [|done]. rewrite lookup_omo_ro_event /omo_read_op list_lookup_fmap Hgen. done.
          -- unfold OmoUBgen in *. specialize (MAXgen _ IN) as (eidx'' & Heidx'' & LE).
             exists eidx''. split; [done|]. simpl in *. lia.
      + simpl in Hgen. rewrite lookup_omo_wr_event /omo_write_op list_lookup_fmap Hgen /= in Heidx. inversion Heidx. subst e''. clear Heidx.
        iDestruct (OmoEinfo_get with "M●") as "#e✓eV"; [done|].
        iDestruct (OmoEinfo_agree with "e✓eV e''✓eV''") as %<-.
        iDestruct (OmoEinfo_OmoEview _ e with "e✓eV ⊒M") as "⊒SYNC"; [set_solver-|].
        iDestruct (view_at_elim with "⊒SYNC l⊒@SYNC'") as "l⊒".
        iExists e,e,(wr_event gen),tw,vw,Vw. iFrame "l⊒ e''↪st''". iPureIntro. split_and!; try done.
        * set_solver-.
        * rewrite lookup_omo_wr_event /omo_write_op list_lookup_fmap Hgen. done.
        * rewrite /OmoUBgen. intros.
          have CASE : e0 = e ∨ e0 ∈ M by set_solver. destruct CASE as [->|IN].
          -- exists (wr_event gen). split; [|done]. rewrite lookup_omo_wr_event /omo_write_op list_lookup_fmap Hgen. done.
          -- unfold OmoUBgen in *. specialize (MAXgen _ IN) as (eidx'' & Heidx'' & LE).
             exists eidx''. split; [done|]. simpl in *. lia. }

  wp_apply wp_fupd. wp_apply (AtomicSeen_read with "[$l⊒ $l↦ $⊒V']"); [done|done|].
  iIntros (tr vr Vr V'' ζ'') "(Pures & #⊒V'' & H1 & #l⊒@V'' & l↦)".
  iDestruct "Pures" as %([Subζ1 Subζ2] & Htr & MAXtr & LeV'V'').

  iAssert (∃ ir, ⌜ ML !! ir = Some (tr, vr, Vr) ∧ gen_of eidx ≤ ir ⌝)%I with "[-]" as %(ir & MLir & LEir).
  { unfold Hist_ML_valid in *. unfold no_earlier_time in *. unfold ML_time_mono in *.
    have Htr' : ζ !! tr = Some (vr, Vr) by eapply lookup_weaken.
    rewrite ζ_ML_valid elem_of_list_lookup in Htr'. destruct Htr' as [ir MLir].
    have Letwtr : (tw ≤ tr)%positive by apply MAXtr; rewrite lookup_singleton.

    iExists ir. iPureIntro. split; [done|].
    destruct (le_lt_dec (gen_of eidx) ir) as [LE|LT]; try done.
    have COND1 : ML.*1.*1 !! ir = Some tr by rewrite !list_lookup_fmap MLir.
    have COND2 : ML.*1.*1 !! (gen_of eidx) = Some tw by rewrite !list_lookup_fmap MLgen.
    specialize (ML_t_valid _ _ _ _ COND1 COND2 LT). lia. }

  have [[er esr] OMOer] : is_Some (omo !! ir).
  { rewrite lookup_lt_is_Some EQlenML. apply lookup_lt_Some in MLir. done. }
  iDestruct (big_sepL2_lookup with "ML✓") as (?? eVr ???) "((%EQ1 & %eVrEV & %EQ2) & #er✓eVr & #er↪str & _)"; [done|done|].
  inversion EQ1. inversion EQ2. subst e0 es t v V0. clear EQ1 EQ2.
  iDestruct (OmoLe_get _ _ _ _ _ _ eidx (wr_event ir) with "M●") as "#e≤er".
  { done. } { rewrite lookup_omo_wr_event /omo_write_op list_lookup_fmap OMOer. done. } { simpl. done. }

  set en := (length E).
  set M' := {[en]} ∪ M.
  set st := (er, (vr, Vr)).
  set eVn := mkOmoEvent (ReadE (vr, Vr)) V'' M'.

  iDestruct (OmoUB_from_gen with "M●") as "#MAXgen"; [exact Heidx|exact MAXgen|done|].
  iDestruct (OmoUB_mono with "MAXgen e≤er") as "MAXgen'". simpl.
  iDestruct (view_at_mono_2 _ V'' with "⊒M@V'") as "⊒M@V''"; [solve_lat|].
  iMod (OmoAuth_insert_ro_no_Token with "M● ⊒M@V'' er↪str MAXgen' []") as (?) "(M● & #⊒M'@V'' & #er=en & #en✓eVn & RCOMMIT & Pures)".
  { have ? : step en eVn st st.
    { apply loc_step_ReadE; try done. set_solver. }
    iPureIntro. split_and!; try done. }
  iDestruct "Pures" as %(eidx' & Heidx' & EQgen).
  iDestruct (OmoHbToken_finish with "M●") as "[M● M●']".

  apply lookup_omo_lt_Some in Heidx' as LT. rewrite omo_insert_r_length -EQgen in LT.
  have [es Hes] : is_Some (omo_read_op omo !! gen) by rewrite lookup_lt_is_Some -omo_read_op_length.
  erewrite lookup_omo_before_insert_r in Heidx'; [|done].
  destruct (decide (eidx' = ro_event gen (length es))) as [->|NEQ]; last first.
  { eapply lookup_omo_event_valid in Heidx'; [|done]. rewrite lookup_lt_is_Some in Heidx'. lia. }

  set omo' := omo_insert_r omo gen (length E).
  have Heidx'' : lookup_omo omo' (wr_event ir) = Some er.
  { subst omo'. erewrite lookup_omo_before_insert_r; [|done]. rewrite decide_False; [|done].
    rewrite lookup_omo_wr_event /omo_write_op list_lookup_fmap OMOer. done. }
  iDestruct (OmoEq_Eq with "M● er=en") as %EQgen'; [done|done|].
  simpl in EQgen'. clear EQgen. subst ir.

  iDestruct ("Post" $! er gen vr Vr V'' eVr eVn with "[-]") as "HΦ".
  { iFrame "H1 M●' RCOMMIT ⊒V'' en✓eVn er✓eVr er=en MAXgen' ⊒M'@V''". iSplitR.
    - iPureIntro. split_and!; try done; [|solve_lat]. rewrite /omo_write_op list_lookup_fmap OMOer. done.
    - iExists γx,γl,γw,γm,γs. iExists _,omo',mo,q,ML,ζ. subst omo'. rewrite omo_insert_r_write_op. iFrame "l↦ M● ES● ML● Hγx".
      iSplit; [done|]. iSplit; [|done]. rewrite view_at_objective_iff.
      rewrite /OMO_ML_valid /omo_insert_r -{2}(take_drop gen omo) (drop_S _ (er, esr)); [|done].
      rewrite alter_app_r_alt; [|by rewrite take_length; lia].
      replace (gen - length (take gen omo)) with 0; last first.
      { rewrite take_length Nat.min_l; [lia|]. apply lookup_lt_Some in OMOer. lia. }
      simpl. rewrite -{2}(take_drop gen ML) (drop_S _ (tr, vr, Vr)); [|done].

      rewrite -{1}(take_drop gen omo) (drop_S _ (er, esr)); [|done].
      rewrite -{1}(take_drop gen ML) (drop_S _ (tr, vr, Vr)); [|done].
      iDestruct (big_sepL2_app_inv with "ML✓") as "[ML✓1 ML✓2]".
      { left. rewrite !take_length EQlenML. done. }
      rewrite big_sepL2_cons. iDestruct "ML✓2" as "[ML✓2' ML✓3]".

      iApply big_sepL2_app; [done|].
      iApply big_sepL2_cons. iFrame "ML✓3".
      iDestruct "ML✓2'" as (??????) "((%EQ1 & %EQ2 & %EQ3) & H1 & H2 & H3 & H4)".
      inversion EQ1. inversion EQ3. subst e0 es0 t v V0. clear EQ1 EQ3.
      iExists er,(esr ++ [en]),eVr,tr,vr,Vr. rewrite big_sepL_snoc.
      iDestruct (OmoEinfo_agree with "er✓eVr H1") as %<-.
      iFrame "H1 H2 H3 H4". iSplit; [done|]. iExists eVn.
      iDestruct (OmoSnap_get_from_Eq with "er↪str er=en") as "en↪st".
      iFrame "en✓eVn en↪st". iSplit; [done|].
      rewrite (AtomicSeen_mono_lookup_singleton _ _ ζ'' tr vr Vr); [done|].
      eapply lookup_weaken; try done. }

  iModIntro. by iApply "HΦ".
Qed.

Lemma append_only_loc_read_with_swriter_token l γe γs mo E omo es M uf o tid V Vb (Ec : coPset) :
  Relaxed ⊑ o → ↑histN ⊆ Ec →
  {{{ OmoAuth γe γs (1/2)%Qp E omo mo _ ∗ OmoEview γe M ∗
      swriter_token l γe es ∗ @{Vb} append_only_loc l γe uf swriter ∗ ⊒V }}}
    Read o #l @ tid; Ec
  {{{ e v' V' V'' eV eV', RET v';
      let E' := E ++ [eV'] in
      let e' := length E in
      let omo' := omo_insert_r omo (length omo - 1)%nat e' in
      let M' := {[e']} ∪ M in
      ⌜ last (omo_write_op omo) = Some e
      ∧ loc_event_msg eV.(type) = (v', V')
      ∧ V ⊑ V''
      ∧ eV'.(type) = ReadE (v', V')
      ∧ eV'.(sync) = V'' ⌝ ∗
      OmoAuth γe γs (1/2)%Qp E' omo' mo _ ∗
      OmoTokenR γe e' ∗ (* use this to commit the event and update [OmoAuth] *)
      OmoUB γe M e ∗
      OmoEinfo γe e eV ∗
      OmoEinfo γe e' eV' ∗
      OmoEq γe e e' ∗
      ⊒V'' ∗
      (if decide (AcqRel ⊑ o) then ⌜V' ⊑ V''⌝ else ▽{tid} ⊒V') ∗
      @{V''} (swriter_token l γe es ∗ OmoEview γe M') ∗
      @{Vb ⊔ V''} append_only_loc l γe uf swriter }}}.
Proof.
  iIntros "%MOMORD %INCL" (Φ) "(M● & #⊒M & SW & omo↦ & #⊒V) Post". rewrite append_only_loc_eq swriter_token_eq.
  iDestruct "omo↦" as (??????????) "(%& %Hγx & #Hγx & M●' & ES● & ML● & l↦ & #ML✓ & (%ML_t_valid & %ζ_comp & %ζ_ML_valid & %ζ_uf_valid & %Hty))".
  iDestruct "SW" as (????? tw vw Vw) "([%Hγx' %LASTML] & #Hγx' & ES●' & ML●' & #l⊒)".
  rewrite !view_at_objective_iff.
  iDestruct (OmoGname_agree with "Hγx Hγx'") as %<-. encode_agree Hγx.
  iDestruct (OmoAuth_agree with "M● M●'") as %(<- & <- & <- & <-).
  iDestruct (OmoAuth_wf with "M●") as %[OMO_GOOD _].
  iDestruct (OmoEview_nonempty with "⊒M") as %NEmp.
  iDestruct (OmoAuth_OmoEview with "M● ⊒M") as %MIncl.
  iDestruct (big_sepL2_length with "ML✓") as %EQlenML.
  iCombine "M● M●'" as "M●".
  iDestruct (mono_list_auth_own_agree with "ML● ML●'") as %[_ <-].

  iDestruct (view_at_intro_incl with "⊒M ⊒V") as (V') "(#⊒V' & %LeVV' & #⊒M@V')".

  wp_apply wp_fupd. wp_apply (AtomicSeen_read with "[$l⊒ $l↦ $⊒V']"); [done|done|].
  iIntros (tr vr Vr V'' ζ'') "(Pures & #⊒V'' & H1 & #l⊒@V'' & l↦)".
  iDestruct "Pures" as %([Subζ1 Subζ2] & Htr & MAXtr & LeV'V'').

  iAssert (⌜ tw = tr ∧ vw = vr ∧ Vw = Vr ⌝)%I with "[-]" as %(-> & -> & ->).
  { have Htr' : ζ !! tr = Some (vr, Vr) by eapply lookup_weaken.
    rewrite ζ_ML_valid elem_of_list_lookup in Htr'. destruct Htr' as [ir Hir].
    rewrite last_lookup in LASTML. replace (Init.Nat.pred (length ML)) with (length ML - 1) in LASTML by lia.
    have NZML : length ML ≠ 0 by destruct ML.
    apply lookup_lt_Some in Hir as LT.
    destruct (decide (ir = length ML - 1)) as [->|NEQ].
    { rewrite LASTML in Hir. inversion Hir. done. }

    have LT' : ir < length ML - 1 by lia.
    have COND1 : ML.*1.*1 !! ir = Some tr by rewrite !list_lookup_fmap Hir.
    have COND2 : ML.*1.*1 !! (length ML - 1) = Some tw by rewrite !list_lookup_fmap LASTML.
    specialize (ML_t_valid _ _ _ _ COND1 COND2 LT').
    have LE : (tw ≤ tr)%positive.
    { apply MAXtr. rewrite lookup_singleton. done. }
    lia. }

  iDestruct (OmoAuth_omo_nonempty with "M●") as %Nomo.
  have [[er esr] Her] : is_Some (last omo) by rewrite last_is_Some.
  iDestruct (big_sepL2_lookup with "ML✓") as (?? eVr ???) "((%EQ1 & %eVrEV & %EQ2) & er✓eVr & er↪str & _ & BIG)".
  { rewrite last_lookup in Her. done. } { rewrite last_lookup -EQlenML in LASTML. done. }
  inversion EQ1. inversion EQ2. subst e es0 t v V0. clear EQ1 EQ2.

  set en := (length E).
  set M' := {[en]} ∪ M.
  set st := (er, (vr, Vr)).
  set eVn := mkOmoEvent (ReadE (vr, Vr)) V'' M'.

  have MAXgen : OmoUBgen omo M (length omo - 1).
  { rewrite /OmoUBgen. intros.
    apply MIncl in H. eapply lookup_omo_surjective in H as Heidx; [|done]. destruct Heidx as [eidx Heidx].
    exists eidx. split; [done|]. apply lookup_omo_lt_Some in Heidx. lia. }
  iDestruct (OmoUB_from_gen _ _ _ _ _ _ _ _ _ (wr_event (length omo - 1)) with "M●") as "#MAXgen".
  { rewrite lookup_omo_wr_event /omo_write_op list_lookup_fmap.
    rewrite last_lookup in Her. replace (Init.Nat.pred (length omo)) with (length omo - 1) in Her by lia.
    rewrite Her. done. } { done. } { done. }
  iDestruct (view_at_mono_2 _ V'' with "⊒M@V'") as "⊒M@V''"; [solve_lat|].
  iMod (OmoAuth_insert_ro_no_Token with "M● ⊒M@V'' er↪str MAXgen []") as (?) "(M● & #⊒M'@V'' & #er=en & #en✓eVn & RCOMMIT & Pures)".
  { have ? : step en eVn st st.
    { apply loc_step_ReadE; try done. set_solver. }
    iPureIntro. split_and!; try done. }
  iDestruct "Pures" as %(eidx' & Heidx' & EQgen).
  iDestruct (OmoHbToken_finish with "M●") as "[M● M●']".

  apply lookup_omo_lt_Some in Heidx' as LT. rewrite omo_insert_r_length -EQgen in LT.
  have [es' Hes'] : is_Some (omo_read_op omo !! gen) by rewrite lookup_lt_is_Some -omo_read_op_length.
  erewrite lookup_omo_before_insert_r in Heidx'; [|done].
  destruct (decide (eidx' = ro_event gen (length es'))) as [->|NEQ]; last first.
  { eapply lookup_omo_event_valid in Heidx'; [|done]. rewrite lookup_lt_is_Some in Heidx'. lia. }

  set omo' := omo_insert_r omo gen (length E).
  have Heidx'' : lookup_omo omo' (wr_event (length omo - 1)) = Some er.
  { subst omo'. erewrite lookup_omo_before_insert_r; [|done]. rewrite decide_False; [|done].
    rewrite lookup_omo_wr_event /omo_write_op list_lookup_fmap.
    rewrite last_lookup in Her. replace (Init.Nat.pred (length omo)) with (length omo - 1) in Her by lia. rewrite Her. done. }
  iDestruct (OmoEq_Eq with "M● er=en") as %EQgen'; [done|done|].
  simpl in EQgen'. clear EQgen. subst gen.

  iDestruct ("Post" $! er vr Vr V'' eVr eVn with "[-]") as "HΦ".
  { iFrame "H1 M●' RCOMMIT ⊒V'' en✓eVn er✓eVr er=en MAXgen ⊒M'@V''". iSplitR; last iSplitL "ML●' ES●'".
    - iPureIntro. split_and!; try done; [|solve_lat]. rewrite last_lookup -omo_write_op_length /omo_write_op list_lookup_fmap.
      rewrite last_lookup in Her. rewrite Her. done.
    - iExists γx,γl,γw,γm,ML,tr,vr,Vr. iFrame "Hγx ML●' ES●'". iSplitR; [done|].
      rewrite (AtomicSeen_mono_lookup_singleton _ _ ζ'' tr vr Vr); [done|]. done.
    - iExists γx,γl,γw,γm,γs. iExists _,omo',mo,q,ML,ζ. subst omo'. rewrite omo_insert_r_write_op. iFrame "l↦ M● ES● ML● Hγx".
      iSplit; [done|]. iSplit; [|done]. rewrite view_at_objective_iff.
      rewrite /OMO_ML_valid /omo_insert_r -{3}(take_drop (length omo - 1) omo) (drop_S _ (er, esr)); last first.
      { rewrite last_lookup in Her. replace (Init.Nat.pred (length omo)) with (length omo - 1) in Her by lia. done. }
      rewrite alter_app_r_alt; [|by rewrite take_length; lia].
      replace ((length omo - 1) - length (take (length omo - 1) omo)) with 0; last first.
      { rewrite take_length Nat.min_l; [lia|]. lia. }
      simpl. rewrite -{2}(take_drop (length ML - 1) ML) (drop_S _ (tr, vr, Vr)); last first.
      { rewrite last_lookup in LASTML. replace (Init.Nat.pred (length ML)) with (length ML - 1) in LASTML by lia. done. }

      rewrite -{1}(take_drop (length omo - 1) omo) (drop_S _ (er, esr)); last first.
      { rewrite last_lookup in Her. replace (Init.Nat.pred (length omo)) with (length omo - 1) in Her by lia. done. }
      rewrite -{1}(take_drop (length ML - 1) ML) (drop_S _ (tr, vr, Vr)); last first.
      { rewrite last_lookup in LASTML. replace (Init.Nat.pred (length ML)) with (length ML - 1) in LASTML by lia. done. }
      iDestruct (big_sepL2_app_inv with "ML✓") as "[ML✓1 ML✓2]".
      { left. rewrite !take_length EQlenML. done. }
      rewrite big_sepL2_cons. iDestruct "ML✓2" as "[ML✓2' ML✓3]".

      iApply big_sepL2_app; [done|].
      iApply big_sepL2_cons. iFrame "ML✓3".
      iDestruct "ML✓2'" as (??????) "((%EQ1 & %EQ2 & %EQ3) & H1 & H2 & H3 & H4)".
      inversion EQ1. inversion EQ3. subst e es0 t v V0. clear EQ1 EQ3.
      iExists er,(esr ++ [en]),eVr,tr,vr,Vr. rewrite big_sepL_snoc.
      iDestruct (OmoEinfo_agree with "er✓eVr H1") as %<-.
      iFrame "H1 H2 H3 H4". iSplit; [done|]. iExists eVn.
      iDestruct (OmoSnap_get_from_Eq with "er↪str er=en") as "en↪st".
      iFrame "en✓eVn en↪st". iSplit; [done|].
      rewrite (AtomicSeen_mono_lookup_singleton _ _ ζ'' tr vr Vr); [done|].
      eapply lookup_weaken; try done. }

  iModIntro. by iApply "HΦ".
Qed.

Lemma append_only_loc_acquire_read l γe γs mo E omo M uf ty tid V Vb (Ec : coPset) :
  ↑histN ⊆ Ec →
  {{{ OmoAuth γe γs (1/2)%Qp E omo mo _ ∗ OmoEview γe M ∗ @{Vb} append_only_loc l γe uf ty ∗ ⊒V }}}
    !ᵃᶜ#l @ tid; Ec
  {{{ e (gen : nat) v' V' V'' eV eV', RET v';
      let E' := E ++ [eV'] in
      let e' := length E in
      let omo' := omo_insert_r omo gen e' in
      let M' := {[e']} ∪ M in
      ⌜ omo_write_op omo !! gen = Some e
      ∧ loc_event_msg eV.(type) = (v', V')
      ∧ V ⊔ V' ⊑ V''
      ∧ eV'.(type) = ReadE (v', V')
      ∧ eV'.(sync) = V'' ⌝ ∗
      OmoAuth γe γs (1/2)%Qp E' omo' mo _ ∗
      OmoTokenR γe e' ∗ (* use this to commit the event and update [OmoAuth] *)
      OmoUB γe M e ∗
      OmoEinfo γe e eV ∗
      OmoEinfo γe e' eV' ∗
      OmoEq γe e e' ∗
      ⊒V'' ∗
      @{V''} OmoEview γe M' ∗
      @{Vb ⊔ V''} append_only_loc l γe uf ty }}}.
Proof.
  iIntros "%" (Φ) "(M● & #⊒M & omo↦ & #⊒V) Post".
  wp_apply (append_only_loc_read with "[$M● $⊒M $omo↦ $⊒V]"); try done.
  iIntros (???????) "(Pures & M● & RCoMMIT & #MAXgen & #e✓eV & #e=en & #en✓eVn & #⊒V'' & Pure & #⊒M' & omo↦)".
  iDestruct ("Post" $! e gen v' V' V'' eV eV' with "[-]") as "HΦ".
  { iFrame "∗#%". iDestruct "Pures" as %(H1 & H2 & H3 & H4 & H5).
    iDestruct "Pure" as %H6. iPureIntro.
    split_and!; try done. solve_lat. }
  by iApply "HΦ".
Qed.

Lemma append_only_loc_relaxed_read l γe γs mo E omo M uf ty tid V Vb (Ec : coPset) :
  ↑histN ⊆ Ec →
  {{{ OmoAuth γe γs (1/2)%Qp E omo mo _ ∗ OmoEview γe M ∗ @{Vb} append_only_loc l γe uf ty ∗ ⊒V }}}
    !ʳˡˣ#l @ tid; Ec
  {{{ e (gen : nat) v' V' V'' eV eV', RET v';
      let E' := E ++ [eV'] in
      let e' := length E in
      let omo' := omo_insert_r omo gen e' in
      let M' := {[e']} ∪ M in
      ⌜ omo_write_op omo !! gen = Some e
      ∧ loc_event_msg eV.(type) = (v', V')
      ∧ V ⊑ V''
      ∧ eV'.(type) = ReadE (v', V')
      ∧ eV'.(sync) = V'' ⌝ ∗
      OmoAuth γe γs (1/2)%Qp E' omo' mo _ ∗
      OmoTokenR γe e' ∗ (* use this to commit the event and update [OmoAuth] *)
      OmoUB γe M e ∗
      OmoEinfo γe e eV ∗
      OmoEinfo γe e' eV' ∗
      OmoEq γe e e' ∗
      ⊒V'' ∗
      ▽{tid} (⊒V') ∗
      @{V''} OmoEview γe M' ∗
      @{Vb ⊔ V''} append_only_loc l γe uf ty }}}.
Proof.
  iIntros "%" (Φ) "(M● & #⊒M & omo↦ & #⊒V) Post".
  wp_apply (append_only_loc_read with "[$M● $⊒M $omo↦ $⊒V]"); try done.
  iIntros (???????) "(Pures & M● & RCoMMIT & #MAXgen & #e✓eV & #e=en & #en✓eVn & #⊒V'' & H & #⊒M' & omo↦)".
  iDestruct ("Post" $! e gen v' V' V'' eV eV' with "[-]") as "HΦ". { iFrame "∗#%". }
  by iApply "HΦ".
Qed.

Lemma append_only_loc_write_resource l γe γs mo E omo es M uf o tid (Vrel : view) V Vb (v' : lit) (P : vProp) (Ec : coPset) :
  Relaxed ⊑ o → ↑histN ⊆ Ec → v' ≠ LitPoison →
  {{{ OmoAuth γe γs (1/2)%Qp E omo mo _ ∗ OmoEview γe M ∗
      swriter_token l γe es ∗ @{Vb} append_only_loc l γe uf swriter ∗ ⊒V ∗
      (if decide (AcqRel ⊑ o) then P else @{Vrel} P ∗ △{tid} ⊒Vrel) }}}
    Write o #l #v' @ tid; Ec
  {{{ V' V'' eV' e eV, RET #☠;
      let E' := E ++ [eV'] in
      let e' := length E in
      let omo' := omo_append_w omo e' [] in
      let M' := {[e']} ∪ M in
      let uf' := {[(loc_event_msg eV.(type)).1]} ∪ uf in
      ⌜ last (omo_write_op omo) = Some e
      ∧ V ⊑ V'' ∧ V ≠ V'' ∧ (¬ V' ⊑ V)
      ∧ (if decide (AcqRel ⊑ o) then V'' = V' else Vrel ⊑ V' ∧ V' ⊑ V'')
      ∧ eV'.(type) = WriteE (#v', V')
      ∧ eV'.(sync) = V'' ⌝ ∗
      ⊒V'' ∗ @{V'} P ∗
      OmoAuth γe γs (1/2)%Qp E' omo' (mo ++ [(e', (#v', V'))]) _ ∗
      OmoTokenW γe e' ∗
      OmoEinfo γe e eV ∗
      OmoEinfo γe e' eV' ∗
      @{V''} (swriter_token l γe (omo_write_op omo') ∗ OmoEview γe M') ∗
      @{Vb ⊔ V''} append_only_loc l γe uf' swriter }}}.
Proof.
  iIntros "%H1 %H2 %H3" (Φ) "(M● & #⊒M & SW & omo↦ & #⊒V & P) Post".
  set Hrel : vProp := (if decide (AcqRel ⊑ o) then True else △{tid} (⊒Vrel))%I.
  iAssert (Hrel ∗ ∃ V0, ⊒V0 ∧ ⌜V ⊑ V0⌝ ∧
          if decide (AcqRel ⊑ o) then @{V0} P else @{Vrel} P)%I
          with "[P]" as "[sVrel P]".
  { rewrite /Hrel.
    case decide => ?.
    - iSplit; [done|]. by iApply (view_at_intro_incl with "P ⊒V").
    - iDestruct "P" as "[P $]". iExists V. by iFrame "⊒V P". }
  iDestruct "P" as (V0) "(#⊒V0 & %LeV0 & P)".

  rewrite append_only_loc_eq swriter_token_eq.
  iDestruct "omo↦" as (??????????) "(%& %Hγx & #Hγx & M●' & ES● & ML● & l↦ & #ML✓ & (%ML_t_valid & %ζ_comp & %ζ_ML_valid & %ζ_uf_valid & %Hty))".
  iDestruct "SW" as (????? tl vl Vl) "([%Hγx' %LASTML] & #Hγx' & ES●' & ML●' & #l⊒)".
  rewrite !view_at_objective_iff.
  iDestruct (OmoGname_agree with "Hγx Hγx'") as %<-. encode_agree Hγx.
  iDestruct (OmoAuth_agree with "M● M●'") as %(<- & <- & <- & <-).
  iDestruct (OmoAuth_wf with "M●") as %[OMO_GOOD _].
  iDestruct (OmoEview_nonempty with "⊒M") as %NEmp.
  iDestruct (OmoAuth_OmoEview with "M● ⊒M") as %MIncl.
  iDestruct (big_sepL2_length with "ML✓") as %EQlenML.
  iDestruct (OmoAuth_omo_nonempty with "M●") as %Nomo.
  iCombine "M● M●'" as "M●".
  iDestruct (mono_list_auth_own_agree with "ML● ML●'") as %[_ <-].

  iDestruct (view_at_intro_incl with "⊒M ⊒V0") as (V') "(#⊒V' & %LeV0V' & #⊒M@V')".

  wp_apply wp_fupd. wp_apply (AtomicSeen_concurrent_write _ _ _ _ _ _ _ _ _ #v' with "[$l⊒ $l↦ $⊒V' $sVrel]"); [done|done|].
  iIntros (tw Vw V'') "(Pures & #⊒V'' & #l⊒@V'' & l↦)". rename v' into vw.
  iDestruct "Pures" as %(MAXtw & HtwNone & LeV'V'' & NEqV'V'' & NLeVwV' & CASEVIEW).

  have LTtltw : (tl < tw)%positive by apply MAXtw; rewrite lookup_singleton.
  have [[el esl] Hel] : is_Some (last omo) by rewrite last_is_Some.
  iDestruct (big_sepL2_lookup with "ML✓") as (?? eVl ???) "((%EQ1 & %eVlEV & %EQ2) & el✓eVl & el↪stl & _)".
  { rewrite last_lookup in Hel. done. } { rewrite last_lookup -EQlenML in LASTML. done. }
  inversion EQ1. inversion EQ2. subst e es0 t v V1. clear EQ1 EQ2.

  iAssert (⌜ last mo = Some (el, (vl, Vl)) ⌝)%I with "[-]" as %LASTmo.
  { iDestruct (OmoAuth_OmoSnap _ _ _ _ _ _ _ (wr_event (length omo - 1)) with "M● el↪stl") as %Hlookup.
    { rewrite lookup_omo_wr_event /omo_write_op list_lookup_fmap. rewrite last_lookup in Hel.
      replace (Init.Nat.pred (length omo)) with (length omo - 1) in Hel by lia. rewrite Hel. done. }
    iPureIntro. simpl in Hlookup. apply omo_stlist_length in OMO_GOOD. rewrite last_lookup -OMO_GOOD.
    replace (Init.Nat.pred (length omo)) with (length omo - 1) by lia. done. }

  set en := (length E).
  set M' := {[en]} ∪ M.
  set st := (en, (#vw, Vw)).
  set eVn := mkOmoEvent (WriteE (#vw, Vw)) V'' M'.

  iDestruct (view_at_mono_2 _ V'' with "⊒M@V'") as "⊒M@V''"; [done|].
  iMod (OmoAuth_insert_last_no_Token with "M● ⊒M@V'' []") as "(M● & #⊒M'@V'' & #en✓eVn & #en↪stn & WCOMMIT)".
  { have ? : step en eVn (el, (vl, Vl)) st.
    { apply loc_step_WriteE; try done. set_solver-. }
    iPureIntro. split_and!; try done. }
  iDestruct (OmoHbToken_finish with "M●") as "[M● M●']".

  subst q. iDestruct (mono_list_auth_own_agree with "ES● ES●'") as %[_ <-].
  iCombine "ES● ES●'" as "ES●". iCombine "ML● ML●'" as "ML●".
  replace (1/2/2 + (1/2 + 1/2/2))%Qp with 1%Qp by compute_done.

  set omo' := omo_append_w omo en [].
  set ML' := ML ++ [(tw, #vw, Vw)].
  iMod (mono_list_auth_own_update (omo_write_op omo') with "ES●") as "[ES● _]".
  { rewrite omo_append_w_write_op. eapply prefix_app_r. done. }
  iMod (mono_list_auth_own_update ML' with "ML●") as "[ML● _]"; [by eapply prefix_app_r|].

  iDestruct "ES●" as "[ES● [ES●' ES●'']]". iCombine "ES● ES●''" as "ES●".
  iDestruct "ML●" as "[ML● [ML●' ML●'']]". iCombine "ML● ML●''" as "ML●".

  iDestruct ("Post" $! Vw V'' eVn el eVl with "[-]") as "HΦ".
  { iFrame "M●' WCOMMIT ⊒V'' el✓eVl en✓eVn ⊒M'@V''". iSplitR; last iSplitL "P"; last iSplitL "ES● ML●".
    - iPureIntro. split_and!; try done.
      + rewrite last_lookup -omo_write_op_length /omo_write_op list_lookup_fmap. rewrite last_lookup in Hel. rewrite Hel. done.
      + solve_lat.
      + unfold not. intros. subst V''.
        have EQ : V = V'. { clear -LeV0 LeV0V' LeV'V''. solve_lat. } subst V'. done.
      + unfold not. intros.
        have Contra : Vw ⊑ V' by solve_lat. done.
    - destruct (decide (AcqRel ⊑ o)).
      + subst V''. iFrame "P".
      + destruct CASEVIEW as [? _]. iFrame "P".
    - iExists γx,γl,γw,γm,ML',tw,#vw,Vw. iClear "l⊒".
      rewrite (AtomicSeen_mono_lookup_singleton _ _ _ tw); [|by rewrite lookup_insert].
      iFrame "ES● ML● Hγx l⊒@V''". iPureIntro. split; [done|]. subst ML'. rewrite last_app. done.
    - iExists γx,γl,γw,γm,γs. iExists _,_,_,(1/2/2)%Qp,ML',_. iFrame "l↦ M● ES●' ML●' Hγx". iSplit; [done|]. iSplit; [|iPureIntro; split_and!; try done].
      + rewrite view_at_objective_iff /OMO_ML_valid. subst omo' ML'. rewrite /omo_append_w. iApply big_sepL2_app; [done|].
        rewrite big_sepL2_singleton. iExists en,[],eVn,tw,#vw,Vw. rewrite big_sepL_nil. iFrame "en✓eVn en↪stn". iClear "l⊒".
        rewrite (AtomicSeen_mono_lookup_singleton _ _ _ tw); [|by rewrite lookup_insert]. iFrame "l⊒@V''". done.
      + rewrite /ML_time_mono. intros. destruct (le_lt_dec (length ML) i2) as [LE|LT].
        * have EQ : i2 = length ML; [|subst i2].
          { apply lookup_lt_Some in H0. subst ML'. rewrite !fmap_length app_length /= in H0. lia. }
          have LT : i1 < length ML.
          { apply lookup_lt_Some in H. subst ML'. rewrite !fmap_length app_length /= in H. lia. }
          subst ML'. rewrite !list_lookup_fmap lookup_app_1_eq in H0. inversion H0. subst t2. clear H0.
          rewrite !list_lookup_fmap lookup_app_1_ne in H; [|lia]. rewrite -!list_lookup_fmap in H.

          have H' : ML.*1.*1 !! (length ML - 1) = Some tl.
          { rewrite !list_lookup_fmap. rewrite last_lookup in LASTML.
            replace (Init.Nat.pred (length ML)) with (length ML - 1) in LASTML by lia. rewrite LASTML. done. }
          have LEt : (t1 ≤ tl)%positive.
          { destruct (decide (i1 = length ML - 1)) as [->|NEQ].
            - rewrite H in H'. inversion H'. done.
            - have LTt : i1 < length ML - 1 by lia.
              specialize (ML_t_valid _ _ _ _ H H' LTt). lia. }
          lia.
        * rewrite !list_lookup_fmap lookup_app_1_ne in H; [|lia]. rewrite -!list_lookup_fmap in H.
          rewrite !list_lookup_fmap lookup_app_1_ne in H0; [|lia]. rewrite -!list_lookup_fmap in H0.
          eapply ML_t_valid; try done.
      + unfold Hist_comparable in *. intros. destruct (decide (t = tw)) as [->|NEQ].
        * rewrite lookup_insert in H. inversion H. subst v V1. exists vw. done.
        * rewrite lookup_insert_ne in H; [|done]. eapply ζ_comp; try done.
      + unfold Hist_ML_valid in *. intros. destruct (decide (t = tw)) as [->|NEQ].
        * rewrite lookup_insert. split; intros.
          -- inversion H. subst v V1 ML'. rewrite elem_of_list_lookup. exists (length ML). by rewrite lookup_app_1_eq.
          -- rewrite elem_of_list_lookup in H. destruct H as [i Hi]. destruct (decide (i = length ML)) as [->|NEq].
             ++ rewrite lookup_app_1_eq in Hi. inversion Hi. done.
             ++ rewrite lookup_app_1_ne in Hi; [|done]. apply elem_of_list_lookup_2 in Hi.
                rewrite -ζ_ML_valid in Hi. rewrite HtwNone in Hi. done.
        * rewrite lookup_insert_ne; [|done]. split; intros.
          -- rewrite elem_of_app. left. by rewrite -ζ_ML_valid.
          -- rewrite elem_of_list_lookup in H. destruct H as [i Hi].
             destruct (decide (i = length ML)) as [->|NEQ'].
             ++ rewrite lookup_app_1_eq in Hi. inversion Hi. done.
             ++ rewrite lookup_app_1_ne in Hi; [|done]. apply elem_of_list_lookup_2 in Hi. by rewrite ζ_ML_valid.
      + unfold uf_valid in *. intros. destruct (decide (t = tw)) as [->|NEQ].
        * rewrite lookup_insert in H. inversion H. subst v V1. clear H. right.
          unfold no_earlier_time. intros. destruct (decide (t' = tw)) as [->|NEQ']; [done|].
          rewrite lookup_insert_ne in H; [|done].

          destruct H as [[vm Vm] H].
          unfold Hist_ML_valid in *. rewrite ζ_ML_valid elem_of_list_lookup in H.
          destruct H as [i Hi].

          have LE : (t' ≤ tl)%positive.
          { rewrite last_lookup in LASTML. replace (Init.Nat.pred (length ML)) with (length ML - 1) in LASTML by lia.
            destruct (decide (i = length ML - 1)) as [->|NEQ].
            - rewrite Hi in LASTML. inversion LASTML. subst t' vm Vm. done.
            - apply lookup_lt_Some in Hi as LTi.
              have LTi' : i < length ML - 1 by lia.
              have LOOKUP1 : ML.*1.*1 !! i = Some t' by rewrite !list_lookup_fmap Hi.
              have LOOKUP2 : ML.*1.*1 !! (length ML - 1) = Some tl by rewrite !list_lookup_fmap LASTML.
              specialize (ML_t_valid _ _ _ _ LOOKUP1 LOOKUP2 LTi'). lia. }
          have ? : (t' ≤ tw)%positive by lia. done.
        * rewrite lookup_insert_ne in H; [|done].
          destruct (decide (tw = t + 1)%positive) as [->|NEQ']; [by rewrite lookup_insert in H0|].
          rewrite lookup_insert_ne in H0; [|done].
          apply ζ_uf_valid in H as CASE; [|done]. destruct CASE as [IN|MAXgen].
          -- left. clear -IN. set_solver.
          -- have LE1 : (tl ≤ t)%positive.
             { apply MAXgen. rewrite last_lookup in LASTML. apply elem_of_list_lookup_2 in LASTML.
               rewrite -ζ_ML_valid in LASTML. rewrite LASTML. done. }
             have LE2 : (t ≤ tl)%positive.
             { rewrite ζ_ML_valid elem_of_list_lookup in H. destruct H as [i Hi].
               rewrite last_lookup in LASTML. replace (Init.Nat.pred (length ML)) with (length ML - 1) in LASTML by lia.
               destruct (decide (i = length ML - 1)) as [->|NEQ''].
               - rewrite LASTML in Hi. inversion Hi. done.
               - apply lookup_lt_Some in Hi as LT.
                have LT' : i < length ML - 1 by lia.
                have LOOKUP1 : ML.*1.*1 !! i = Some t by rewrite !list_lookup_fmap Hi.
                have LOOKUP2 : ML.*1.*1 !! (length ML - 1) = Some tl by rewrite !list_lookup_fmap LASTML.
                specialize (ML_t_valid _ _ _ _ LOOKUP1 LOOKUP2 LT'). lia. }
             have EQ : t = tl by lia. subst t. clear LE1 LE2.
             rewrite last_lookup in LASTML. apply elem_of_list_lookup_2 in LASTML. rewrite -ζ_ML_valid in LASTML.
             rewrite LASTML in H. inversion H. subst v V1.
             left. rewrite eVlEV. set_solver-. }

  iModIntro. by iApply "HΦ".
Qed.

Lemma append_only_loc_write l γe γs mo E omo es M uf o tid (Vrel : view) V Vb (v' : lit) (Ec : coPset) :
  Relaxed ⊑ o → ↑histN ⊆ Ec → v' ≠ LitPoison →
  {{{ OmoAuth γe γs (1/2)%Qp E omo mo _ ∗ OmoEview γe M ∗
      swriter_token l γe es ∗ @{Vb} append_only_loc l γe uf swriter ∗ ⊒V ∗
      (if decide (AcqRel ⊑ o) then True else △{tid} ⊒Vrel) }}}
    Write o #l #v' @ tid; Ec
  {{{ V' V'' eV' e eV, RET #☠;
      let E' := E ++ [eV'] in
      let e' := length E in
      let omo' := omo_append_w omo e' [] in
      let M' := {[e']} ∪ M in
      let uf' := {[(loc_event_msg eV.(type)).1]} ∪ uf in
      ⌜ last (omo_write_op omo) = Some e
      ∧ V ⊑ V'' ∧ V ≠ V'' ∧ (¬ V' ⊑ V)
      ∧ (if decide (AcqRel ⊑ o) then V'' = V' else Vrel ⊑ V' ∧ V' ⊑ V'')
      ∧ eV'.(type) = WriteE (#v', V')
      ∧ eV'.(sync) = V'' ⌝ ∗
      ⊒V'' ∗
      OmoAuth γe γs (1/2)%Qp E' omo' (mo ++ [(e', (#v', V'))]) _ ∗
      OmoTokenW γe e' ∗
      OmoEinfo γe e eV ∗
      OmoEinfo γe e' eV' ∗
      @{V''} (swriter_token l γe (omo_write_op omo') ∗ OmoEview γe M') ∗
      @{Vb ⊔ V''} append_only_loc l γe uf' swriter }}}.
Proof.
  iIntros "%H1 %H2 %H3" (Φ) "(M● & #⊒M & SW & omo↦ & #⊒V & F) Post".
  wp_apply (append_only_loc_write_resource _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ True with "[$M● $SW $omo↦ F $⊒M $⊒V]"); try done.
  { destruct (decide (AcqRel ⊑ o)); try done. iFrame "F". done. }

  iIntros (?????) "(Pures & #⊒V'' & _ & M● & WCOMMIT & #e✓eV & #en✓eVn & RES & omo↦)".
  iDestruct ("Post" $! V' V'' eV' e eV with "[-]") as "HΦ"; [iFrame "∗#%"|].
  by iApply "HΦ".
Qed.

Lemma append_only_loc_release_write l γe γs mo E omo es M uf tid V Vb (v' : lit) (P : vProp) (Ec : coPset) :
  ↑histN ⊆ Ec → v' ≠ LitPoison →
  {{{ OmoAuth γe γs (1/2)%Qp E omo mo _ ∗ OmoEview γe M ∗
      swriter_token l γe es ∗ @{Vb} append_only_loc l γe uf swriter ∗ P ∗ ⊒V }}}
    #l <-ʳᵉˡ #v' @ tid; Ec
  {{{ V' eV' e eV, RET #☠;
      let E' := E ++ [eV'] in
      let e' := length E in
      let omo' := omo_append_w omo e' [] in
      let M' := {[e']} ∪ M in
      let uf' := {[(loc_event_msg eV.(type)).1]} ∪ uf in
      ⌜ last (omo_write_op omo) = Some e
      ∧ V ⊑ V' ∧ V ≠ V'
      ∧ eV'.(type) = WriteE (#v', V')
      ∧ eV'.(sync) = V' ⌝ ∗
      ⊒V' ∗
      OmoAuth γe γs (1/2)%Qp E' omo' (mo ++ [(e', (#v', V'))]) _ ∗
      OmoTokenW γe e' ∗
      OmoEinfo γe e eV ∗
      OmoEinfo γe e' eV' ∗
      @{V'} (swriter_token l γe (omo_write_op omo') ∗ OmoEview γe M' ∗ P) ∗
      @{Vb ⊔ V'} append_only_loc l γe uf' swriter }}}.
Proof.
  iIntros "%H1 %H2" (Φ) "(M● & #⊒M & SW & omo↦ & P & #⊒V) Post".
  wp_apply (append_only_loc_write_resource _ _ _ _ _ _ _ _ _ _ _ ∅ _ _ _ P with "[$M● $SW $omo↦ P $⊒M $⊒V]"); [done|done|done|iFrame "P"|].

  iIntros (?????) "(Pures & #⊒V'' & P & M● & WCOMMIT & #e✓eV & #en✓eVn & RES & omo↦)".
  iDestruct "Pures" as %(H3 & H4 & H5 & H6 & H7 & H8 & H9). subst V''.
  iDestruct ("Post" $! V' eV' e eV with "[-]") as "HΦ".
  { iFrame "∗#%". iFrame "RES". iPureIntro. split_and!; try done. }
  by iFrame "HΦ".
Qed.

Lemma append_only_loc_release_write_cur l γe γs mo E omo es M uf tid (v' : lit) (P : vProp) (Ec : coPset) :
  ↑histN ⊆ Ec → v' ≠ LitPoison →
  {{{ OmoAuth γe γs (1/2)%Qp E omo mo _ ∗ OmoEview γe M ∗
      swriter_token l γe es ∗ append_only_loc l γe uf swriter ∗ P }}}
    #l <-ʳᵉˡ #v' @ tid; Ec
  {{{ V' eV' e eV, RET #☠;
      let E' := E ++ [eV'] in
      let e' := length E in
      let omo' := omo_append_w omo e' [] in
      let M' := {[e']} ∪ M in
      let uf' := {[(loc_event_msg eV.(type)).1]} ∪ uf in
      ⌜ last (omo_write_op omo) = Some e
      ∧ eV'.(type) = WriteE (#v', V')
      ∧ eV'.(sync) = V' ⌝ ∗
      ⊒V' ∗
      OmoAuth γe γs (1/2)%Qp E' omo' (mo ++ [(e', (#v', V'))]) _ ∗
      OmoTokenW γe e' ∗
      OmoEinfo γe e eV ∗
      OmoEinfo γe e' eV' ∗
      @{V'} P ∗
      swriter_token l γe (omo_write_op omo') ∗ OmoEview γe M' ∗
      append_only_loc l γe uf' swriter }}}.
Proof.
  iIntros "%H1 %H2" (Φ) "(M● & #⊒M & SW & omo↦ & P) Post".
  iDestruct (view_at_intro with "omo↦") as (V) "[#⊒V omo↦]".
  wp_apply (append_only_loc_release_write _ _ _ _ _ _ _ _ _ _ _ _ _ P with "[$M● $⊒M $SW $omo↦ $P $⊒V]"); [done|done|].
  iIntros (????) "(Pures & #⊒V' & M● & WCOMMIT & #e✓eV & #en✓eVn & (SW & #⊒M' & P) & omo↦)".
  iDestruct "Pures" as %(H3 & H4 & H5 & H6 & H7).
  iCombine "⊒V ⊒V'" as "⊒V''". rewrite monPred_in_view_op.
  iDestruct (view_at_elim with "⊒V'' omo↦") as "omo↦".
  iDestruct (view_at_elim with "⊒V' SW") as "SW".
  iDestruct (view_at_elim with "⊒V' ⊒M'") as "⊒M''".

  iDestruct ("Post" $! V' eV' e eV with "[-]") as "HΦ"; [by iFrame "∗#%"|].
  by iApply "HΦ".
Qed.

Lemma append_only_loc_relaxed_write l γe γs mo E omo es M uf tid (Vrel : view) V Vb (v' : lit) (P : vProp) (Ec : coPset) :
  ↑histN ⊆ Ec → v' ≠ LitPoison →
  {{{ OmoAuth γe γs (1/2)%Qp E omo mo _ ∗ OmoEview γe M ∗
      swriter_token l γe es ∗ @{Vb} append_only_loc l γe uf swriter ∗ ⊒V ∗ @{Vrel} P ∗ △{tid} ⊒Vrel }}}
    #l <-ʳˡˣ #v' @ tid; Ec
  {{{ V' V'' eV' e eV, RET #☠;
      let E' := E ++ [eV'] in
      let e' := length E in
      let omo' := omo_append_w omo e' [] in
      let M' := {[e']} ∪ M in
      let uf' := {[(loc_event_msg eV.(type)).1]} ∪ uf in
      ⌜ last (omo_write_op omo) = Some e
      ∧ V ⊑ V'' ∧ V ≠ V'' ∧ (¬ V' ⊑ V)
      ∧ Vrel ⊑ V' ∧ V' ⊑ V''
      ∧ eV'.(type) = WriteE (#v', V')
      ∧ eV'.(sync) = V'' ⌝ ∗
      ⊒V'' ∗ @{V'} P ∗
      OmoAuth γe γs (1/2)%Qp E' omo' (mo ++ [(e', (#v', V'))]) _ ∗
      OmoTokenW γe e' ∗
      OmoEinfo γe e eV ∗
      OmoEinfo γe e' eV' ∗
      @{V''} (swriter_token l γe (omo_write_op omo') ∗ OmoEview γe M') ∗
      @{Vb ⊔ V''} append_only_loc l γe uf' swriter }}}.
Proof.
  iIntros "%H1 %H2" (Φ) "(M● & #⊒M & SW & omo↦ & #⊒V & P & #Vrel) Post".
  wp_apply (append_only_loc_write_resource _ _ _ _ _ _ _ _ _ _ _ Vrel _ _ _ P with "[$M● $SW $omo↦ P $⊒M $⊒V]");
    [done|done|done|iFrame "P Vrel"|].

  iIntros (?????) "(Pures & #⊒V'' & P & M● & WCOMMIT & #e✓eV & #en✓eVn & RES & omo↦)".
  iDestruct "Pures" as %(H3 & H4 & H5 & H6 & [H7 H7'] & H8 & H9).
  iDestruct ("Post" $! V' V'' eV' e eV with "[-]") as "HΦ"; [by iFrame "∗#%"|].
  by iApply "HΦ".
Qed.

(** Latest message written in location is different to [vr].
    This is necessary in must-fail CAS operation *)
Definition append_only_loc_cas_latest_neq γe omo (vr : lit) : vProp :=
  ∃ e eV,
    OmoEinfo γe e eV ∗
    ⌜ last (omo_write_op omo) = Some e
    ∧ (loc_event_msg eV.(type)).1 ≠ #vr ⌝.

Lemma append_only_loc_cas_general l γe γs mo E omo M uf ty orf or ow (vr : lit) (vw : lit) tid (Vrel : view) V Vb (Ec : coPset) :
  Relaxed ⊑ orf → Relaxed ⊑ or → Relaxed ⊑ ow →
  ↑histN ⊆ Ec → #vr ∉ uf → vr ≠ ☠%V → vw ≠ ☠%V →
  {{{ OmoAuth γe γs (1/2)%Qp E omo mo _ ∗ OmoEview γe M ∗
      @{Vb} append_only_loc l γe uf ty ∗ ⊒V ∗
      (if decide (AcqRel ⊑ ow) then True else △{tid} ⊒Vrel) }}}
    CAS #l #vr #vw orf or ow @ tid; Ec
{{{ b e (gen : nat) (v' : lit) Vr V'' mo' omo' eV eV', RET #b;
      let E' := E ++ [eV'] in
      let e' := length E in
      let M' := {[e']} ∪ M in
      ⌜ (* read message *) omo_write_op omo !! gen = Some e ∧ loc_event_msg eV.(type) = (#v', Vr)
      ∧ (* pre-view ⊑ post-view *) V ⊑ V'' ⌝ ∗
      OmoUB γe M e ∗
      OmoEinfo γe e eV ∗
      OmoEinfo γe e' eV' ∗
      OmoAuth γe γs (1/2)%Qp E' omo' mo' _ ∗
      ⊒V'' ∗ @{V''} OmoEview γe M' ∗
      ( (⌜b = false ∧ lit_neq vr v' ∧ mo' = mo
        ∧ omo' = omo_insert_r omo gen e'
        ∧ eV'.(type) = ReadE (#v', Vr)
        ∧ eV'.(sync) = V''⌝
        ∧ (if decide (AcqRel ⊑ orf) then ⌜Vr ⊑ V''⌝ else ▽{tid} ⊒Vr)
        ∗ @{Vb ⊔ V''} append_only_loc l γe uf ty
        ∗ OmoEq γe e e'
        ∗ OmoTokenR γe e')
      ∨ (⌜b = true ∧ v' = vr ∧ gen = (length omo - 1)%nat⌝
        ∧ ∃ Vw,
            ⌜ mo' = mo ++ [(e', (#vw, Vw))]
            ∧ omo' = omo_append_w omo e' []
            ∧ eV'.(type) = UpdateE e (#vw, Vw)
            ∧ eV'.(sync) = V''
            (* release sequence: Vwrite includes Vread *)
            ∧ Vr ⊑ Vw ∧ Vr ≠ Vw
            ∧ (¬ V'' ⊑ Vr)
            ∧ V ≠ V''
            ∧ ( if decide (AcqRel ⊑ ow) then
                  ( if decide (AcqRel ⊑ or) then
                      (* release-acquire CAS *) Vw = V''
                    else (* release CAS *) V'' ⊑ Vw )
                else (* relaxed write CAS *) Vrel ⊑ Vw ) ⌝
            ∧ (if decide (AcqRel ⊑ ow) then @{Vw} OmoEview γe M' else emp)
            (* If current type is swriter, then we need exclusive permission to perform write *)
            ∗ (match ty with
              | cas_only => @{Vb ⊔ V''} append_only_loc l γe uf ty
              | swriter => ∀ es Vs, @{Vs} swriter_token l γe es ==∗ @{Vs ⊔ V''} swriter_token l γe (omo_write_op omo') ∗ @{Vb ⊔ V''} append_only_loc l γe uf ty
              end)
            ∗ (if decide (AcqRel ⊑ or) then ⌜Vw ⊑ V''⌝ else ▽{tid} ⊒Vw)
            ∗ OmoTokenW γe e')) }}}.
Proof.
  iIntros "%ORD1 %ORD2 %ORD3 %INCL1 %INCL2 %NEqvr %NEqvw" (Φ) "(M● & #⊒M & omo↦ & #⊒V & F) Post". rewrite append_only_loc_eq.
  iDestruct "omo↦" as (??????????) "(%& %Hγx & #Hγx & M●' & ES● & ML● & l↦ & #ML✓ & (%ML_t_valid & %ζ_comp & %ζ_ML_valid & %ζ_uf_valid & %Hty))".
  rewrite !view_at_objective_iff.
  iDestruct (OmoAuth_agree with "M● M●'") as %(<- & <- & <- & <-).
  iDestruct (OmoAuth_wf with "M●") as %[OMO_GOOD _].
  iDestruct (OmoEview_nonempty with "⊒M") as %NEmp.
  iDestruct (OmoAuth_OmoEview with "M● ⊒M") as %MIncl.
  iDestruct (big_sepL2_length with "ML✓") as %EQlenML.
  iCombine "M● M●'" as "M●".

  iDestruct (view_at_intro_incl with "⊒M ⊒V") as (V') "(#⊒V' & %LeVV' & #⊒M@V')".

  (* Extract latest observed message *)
  iAssert (∃ e em eidx tm vm Vm,
    ⌜ e ∈ M ∧ lookup_omo omo eidx = Some e ∧ ML !! (gen_of eidx) = Some (tm, vm, Vm) ∧ OmoUBgen omo M (gen_of eidx) ⌝ ∗
    l sn⊒{γl} {[tm := (vm, Vm)]} ∗ OmoSnap γe γs e (em, (vm, Vm)))%I
      with "[-]" as "(%&%&%&%&%&%& (%eIn & %Heidx & %MLgen & %MAXgen) & #l⊒ & #e↪st)".
  { iClear "Post ⊒M@V'". iInduction M as [|e M NotIn] "IH" using set_ind_L; [done|].
    destruct (decide (M = ∅)) as [Memp|NEmp'].
    - have EQ : {[e]} ∪ M = {[e]} by set_solver. rewrite !EQ. clear EQ.
      have HeV : e ∈ ({[e]} ∪ M) by set_solver-. apply MIncl in HeV.
      eapply lookup_omo_surjective in HeV as Heidx; [|done]. destruct Heidx as [eidx Heidx]. destruct HeV as [eV HeV].
      have [[e' es'] Hgen] : is_Some (omo !! (gen_of eidx)).
      { rewrite lookup_lt_is_Some. apply lookup_omo_lt_Some in Heidx. done. }
      have [minfo Hminfo] : is_Some (ML !! (gen_of eidx)).
      { rewrite lookup_lt_is_Some -EQlenML. apply lookup_lt_Some in Hgen. done. }
      iDestruct (big_sepL2_lookup with "ML✓") as (?? eV' tm vm Vm) "((%EQ1 & %eV'EV & %EQ2) & #e'✓eV' & #e'↪st' & l⊒@SYNC' & BIG)"; [done|done|].
      inversion EQ1. subst e0 es minfo. clear EQ1.
      destruct eidx.
      + simpl in Hgen. rewrite lookup_omo_ro_event /omo_read_op list_lookup_fmap Hgen /= in Heidx.
        iDestruct (big_sepL_lookup with "BIG") as (?) "(%eVEV & e✓eV & e↪st & l⊒@SYNC)"; [done|].
        iDestruct (OmoEinfo_get with "M●") as "#e✓eV'"; [done|].
        iDestruct (OmoEinfo_agree with "e✓eV e✓eV'") as %->.
        iDestruct (OmoEinfo_OmoEview _ e with "e✓eV ⊒M") as "⊒SYNC"; [set_solver-|].
        iDestruct (view_at_elim with "⊒SYNC l⊒@SYNC") as "l⊒".
        iExists e,e',(ro_event gen i'),tm,vm,Vm. iFrame "l⊒ e↪st". iPureIntro. split_and!; try done.
        * set_solver-.
        * rewrite lookup_omo_ro_event /omo_read_op list_lookup_fmap Hgen. done.
        * rewrite /OmoUBgen. intros.
          have EQ : e0 = e by set_solver. subst e0. exists (ro_event gen i'). split.
          -- rewrite lookup_omo_ro_event /omo_read_op list_lookup_fmap Hgen. done.
          -- done.
      + simpl in Hgen. rewrite lookup_omo_wr_event /omo_write_op list_lookup_fmap Hgen /= in Heidx. inversion Heidx. subst e'. clear Heidx.
        iDestruct (OmoEinfo_get with "M●") as "#e✓eV"; [done|].
        iDestruct (OmoEinfo_agree with "e✓eV e'✓eV'") as %<-.
        iDestruct (OmoEinfo_OmoEview _ e with "e✓eV ⊒M") as "⊒SYNC"; [set_solver-|].
        iDestruct (view_at_elim with "⊒SYNC l⊒@SYNC'") as "l⊒".
        iExists e,e,(wr_event gen),tm,vm,Vm. iFrame "l⊒ e'↪st'". iPureIntro. split_and!; try done.
        * set_solver-.
        * rewrite lookup_omo_wr_event /omo_write_op list_lookup_fmap Hgen. done.
        * rewrite /OmoUBgen. intros.
          have EQ : e0 = e by set_solver. subst e0. exists (wr_event gen). split; [|done].
          rewrite lookup_omo_wr_event /omo_write_op list_lookup_fmap Hgen. done.
    - iDestruct (OmoEview_split with "⊒M") as "[⊒e ⊒M']"; [set_solver-|done|].
      iDestruct ("IH" with "[] [] ⊒M' ES● ML● l↦ F M●") as "#H"; [done|..].
      { iPureIntro. intros. apply MIncl. set_solver. }
      iDestruct "H" as (e' ew' eidx' tm' vm' Vm') "((%e'IN & %Heidx' & %MLgen' & %MAXgen) & l⊒' & e'↪st')".
      have HeV : e ∈ ({[e]} ∪ M) by set_solver-. apply MIncl in HeV.
      eapply lookup_omo_surjective in HeV as Heidx; [|done]. destruct Heidx as [eidx Heidx]. destruct HeV as [eV HeV].

      destruct (le_lt_dec (gen_of eidx) (gen_of eidx')) as [LE|LT].
      { (* [e] is non-latest event -> induction hypothesis is the answer *)
        iExists e',ew',eidx',tm',vm',Vm'. iFrame "l⊒' e'↪st'". iPureIntro. split_and!; try done.
        - set_solver.
        - rewrite /OmoUBgen. intros.
          have CASE : e0 = e ∨ e0 ∈ M by set_solver.
          destruct CASE as [->|IN].
          + exists eidx. done.
          + apply MAXgen. done. }

      (* [e] is the latest event *)
      have [[e'' es''] Hgen] : is_Some (omo !! (gen_of eidx)).
      { rewrite lookup_lt_is_Some. apply lookup_omo_lt_Some in Heidx. done. }
      have [minfo Hminfo] : is_Some (ML !! (gen_of eidx)).
      { rewrite lookup_lt_is_Some -EQlenML. apply lookup_lt_Some in Hgen. done. }
      iDestruct (big_sepL2_lookup with "ML✓") as (?? eV'' tm vm Vm) "((%EQ1 & %eV''EV & %EQ2) & e''✓eV'' & e''↪st'' & l⊒@SYNC' & BIG)"; [done|done|].
      inversion EQ1. subst e0 es minfo. clear EQ1. destruct eidx.
      + simpl in Hgen. rewrite lookup_omo_ro_event /omo_read_op list_lookup_fmap Hgen /= in Heidx.
        iDestruct (big_sepL_lookup with "BIG") as (?) "(%eVEV & e✓eV & e↪st & l⊒@SYNC)"; [done|].
        iDestruct (OmoEinfo_get with "M●") as "#e✓eV'"; [done|].
        iDestruct (OmoEinfo_agree with "e✓eV e✓eV'") as %->.
        iDestruct (OmoEinfo_OmoEview _ e with "e✓eV ⊒M") as "⊒SYNC"; [set_solver-|].
        iDestruct (view_at_elim with "⊒SYNC l⊒@SYNC") as "l⊒".
        iExists e,e'',(ro_event gen i'),tm,vm,Vm. iFrame "l⊒ e↪st". iPureIntro. split_and!; try done.
        * set_solver-.
        * rewrite lookup_omo_ro_event /omo_read_op list_lookup_fmap Hgen. done.
        * rewrite /OmoUBgen. intros.
          have CASE : e0 = e ∨ e0 ∈ M by set_solver. destruct CASE as [->|IN].
          -- exists (ro_event gen i'). split; [|done]. rewrite lookup_omo_ro_event /omo_read_op list_lookup_fmap Hgen. done.
          -- unfold OmoUBgen in *. specialize (MAXgen _ IN) as (eidx'' & Heidx'' & LE).
             exists eidx''. split; [done|]. simpl in *. lia.
      + simpl in Hgen. rewrite lookup_omo_wr_event /omo_write_op list_lookup_fmap Hgen /= in Heidx. inversion Heidx. subst e''. clear Heidx.
        iDestruct (OmoEinfo_get with "M●") as "#e✓eV"; [done|].
        iDestruct (OmoEinfo_agree with "e✓eV e''✓eV''") as %<-.
        iDestruct (OmoEinfo_OmoEview _ e with "e✓eV ⊒M") as "⊒SYNC"; [set_solver-|].
        iDestruct (view_at_elim with "⊒SYNC l⊒@SYNC'") as "l⊒".
        iExists e,e,(wr_event gen),tm,vm,Vm. iFrame "l⊒ e''↪st''". iPureIntro. split_and!; try done.
        * set_solver-.
        * rewrite lookup_omo_wr_event /omo_write_op list_lookup_fmap Hgen. done.
        * rewrite /OmoUBgen. intros.
          have CASE : e0 = e ∨ e0 ∈ M by set_solver. destruct CASE as [->|IN].
          -- exists (wr_event gen). split; [|done]. rewrite lookup_omo_wr_event /omo_write_op list_lookup_fmap Hgen. done.
          -- unfold OmoUBgen in *. specialize (MAXgen _ IN) as (eidx'' & Heidx'' & LE).
             exists eidx''. split; [done|]. simpl in *. lia. }

  wp_apply wp_fupd. wp_apply (AtomicSeen_CON_CAS _ _ _ _ _ _ _ _ #vw with "[$l⊒ $l↦ $⊒V' $F]"); [done|done|done|done|..].
  { intros. unfold Hist_comparable in *.
    destruct (ζ !! t) eqn:Heq; try done. destruct p as [? ?]. inversion H0. subst v0. clear H0.
    apply ζ_comp in Heq. destruct Heq as (vl & EQ & NEQ). subst v. exists vl. split; [done|]. destruct vr, vl; try done; try constructor. }

  iIntros (???????) "(Pures & #⊒V'' & #l⊒ζ''@V'' & l↦ & CASE)".
  iDestruct "Pures" as %([Subζζ'' Subζ''ζn] & Hζ''t' & MAXt' & LeV'V'').
  iDestruct "CASE" as "[[(%&%&%) F]|[[%%] CASE]]".
  - (* CAS failed *)
    subst b ζn.

    iAssert (∃ ir, ⌜ ML !! ir = Some (t', #v', Vr) ∧ gen_of eidx ≤ ir ⌝)%I with "[-]" as %(ir & MLir & LEir).
    { unfold Hist_ML_valid in *. unfold no_earlier_time in *. unfold ML_time_mono in *.
      have Htr' : ζ !! t' = Some (#v', Vr) by eapply lookup_weaken.
      rewrite ζ_ML_valid elem_of_list_lookup in Htr'. destruct Htr' as [ir MLir].
      have Letwtr : (tm ≤ t')%positive by apply MAXt'; rewrite lookup_singleton.

      iExists ir. iPureIntro. split; [done|].
      destruct (le_lt_dec (gen_of eidx) ir) as [LE|LT]; try done.
      have COND1 : ML.*1.*1 !! ir = Some t' by rewrite !list_lookup_fmap MLir.
      have COND2 : ML.*1.*1 !! (gen_of eidx) = Some tm by rewrite !list_lookup_fmap MLgen.
      specialize (ML_t_valid _ _ _ _ COND1 COND2 LT). lia. }

    have [[er esr] OMOer] : is_Some (omo !! ir).
    { rewrite lookup_lt_is_Some EQlenML. apply lookup_lt_Some in MLir. done. }
    iDestruct (big_sepL2_lookup with "ML✓") as (?? eVr ???) "((%EQ1 & %eVrEV & %EQ2) & #er✓eVr & #er↪str & _)"; [done|done|].
    inversion EQ1. inversion EQ2. subst e0 es t v V0. clear EQ1 EQ2.
    iDestruct (OmoLe_get _ _ _ _ _ _ eidx (wr_event ir) with "M●") as "#e≤er".
    { done. } { rewrite lookup_omo_wr_event /omo_write_op list_lookup_fmap OMOer. done. } { simpl. done. }

    set en := (length E).
    set M' := {[en]} ∪ M.
    set st := (er, (#v', Vr)).
    set eVn := mkOmoEvent (ReadE (#v', Vr)) V'' M'.

    iDestruct (OmoUB_from_gen with "M●") as "#MAXgen"; [exact Heidx|exact MAXgen|done|].
    iDestruct (OmoUB_mono with "MAXgen e≤er") as "MAXgen'". simpl.
    iDestruct (view_at_mono_2 _ V'' with "⊒M@V'") as "⊒M@V''"; [solve_lat|].
    iMod (OmoAuth_insert_ro_no_Token with "M● ⊒M@V'' er↪str MAXgen' []") as (?) "(M● & #⊒M'@V'' & #er=en & #en✓eVn & RCOMMIT & Pures)".
    { have ? : step en eVn st st.
      { apply loc_step_ReadE; try done. set_solver. }
      iPureIntro. split_and!; try done. }
    iDestruct "Pures" as %(eidx' & Heidx' & EQgen).
    iDestruct (OmoHbToken_finish with "M●") as "[M● M●']".

    apply lookup_omo_lt_Some in Heidx' as LT. rewrite omo_insert_r_length -EQgen in LT.
    have [es Hes] : is_Some (omo_read_op omo !! gen) by rewrite lookup_lt_is_Some -omo_read_op_length.
    erewrite lookup_omo_before_insert_r in Heidx'; [|done].
    destruct (decide (eidx' = ro_event gen (length es))) as [->|NEQ]; last first.
    { eapply lookup_omo_event_valid in Heidx'; [|done]. rewrite lookup_lt_is_Some in Heidx'. lia. }

    set omo' := omo_insert_r omo gen (length E).
    have Heidx'' : lookup_omo omo' (wr_event ir) = Some er.
    { subst omo'. erewrite lookup_omo_before_insert_r; [|done]. rewrite decide_False; [|done].
      rewrite lookup_omo_wr_event /omo_write_op list_lookup_fmap OMOer. done. }
    iDestruct (OmoEq_Eq with "M● er=en") as %EQgen'; [done|done|].
    simpl in EQgen'. clear EQgen. subst ir.

    iDestruct ("Post" $! false er gen v' Vr V'' mo omo' eVr eVn with "[-]") as "HΦ".
    { iFrame "M●' ⊒M'@V'' MAXgen' er✓eVr en✓eVn ⊒V''". iSplitR.
      { iPureIntro. split_and!; try done; [|solve_lat]. rewrite /omo_write_op list_lookup_fmap OMOer. done. }
      iLeft. iFrame "er=en RCOMMIT F". iSplitR.
      - done.
      - iExists γx,γl,γw,γm,γs. iExists _,omo',mo,_,ML,ζ. rewrite omo_insert_r_write_op. iFrame "M● ES● ML● Hγx l↦".
        iSplit; [done|]. iSplit; [|done]. rewrite view_at_objective_iff /OMO_ML_valid. subst omo'. rewrite /omo_insert_r.

        rewrite -{2}(take_drop gen omo) (drop_S _ (er, esr)); [|done].
        rewrite alter_app_r_alt; [|by rewrite take_length; lia].
        replace (gen - length (take gen omo)) with 0; last first.
        { rewrite take_length Nat.min_l; [lia|]. apply lookup_lt_Some in OMOer. lia. }
        rewrite -{2}(take_drop gen ML) (drop_S _ (t',#v',Vr)) /=; [|done].
        rewrite -{1}(take_drop gen omo) (drop_S _ (er, esr)); [|done].
        rewrite -{1}(take_drop gen ML) (drop_S _ (t',#v',Vr)) /=; [|done].
        iDestruct (big_sepL2_app_inv with "ML✓") as "[ML✓1 ML✓2]".
        { left. rewrite !take_length EQlenML. done. }
        rewrite big_sepL2_cons. iDestruct "ML✓2" as "[ML✓2' ML✓3]".

        iApply big_sepL2_app; [done|].
        iApply big_sepL2_cons. iFrame "ML✓3".
        iDestruct "ML✓2'" as (??????) "((%EQ1 & %eVrEV' & %EQ2) & er✓eVr' & er↪str' & l⊒' & BIG)".
        inversion EQ1. inversion EQ2. subst e0 es0 t v V0. clear EQ1 EQ2.
        iDestruct (OmoEinfo_agree with "er✓eVr er✓eVr'") as %<-.
        iDestruct (OmoSnap_get_from_Eq with "er↪str er=en") as "en↪st".

        iExists er,(esr ++ [en]),eVr,t',#v',Vr. iFrame "er✓eVr er↪str l⊒'". iSplit; [done|]. rewrite big_sepL_snoc. iFrame "BIG".
        iExists eVn. iFrame "en✓eVn en↪st". iClear "l⊒".
        rewrite (AtomicSeen_mono_lookup_singleton _ _ _ t'); [|done].
        iFrame "l⊒ζ''@V''". done. }

    iModIntro. by iApply "HΦ".
  - (* CAS success *)
    subst b v'.
    iDestruct "CASE" as (Vw) "(Pures & l⊒CASE & F)".
    iDestruct "Pures" as %(ζSt' & EQζn & ζ''St' & LeVrVw & NeVrVw & NLeV''Vr & NeV'V'' & CASE).

    have ζt' : ζ !! t' = Some (#vr, Vr).
    { subst ζn. eapply lookup_weaken in Hζ''t'; [|exact Subζ''ζn]. rewrite lookup_insert_ne in Hζ''t'; [|lia]. done. }

    have LASTML : last ML = Some (t', #vr, Vr).
    { unfold uf_valid in *. eapply ζ_uf_valid in ζSt' as CASE'; [|done]. destruct CASE' as [?|MAXt'2]; [done|].
      rewrite ζ_ML_valid elem_of_list_lookup in ζt'. destruct ζt' as [i MLi].
      have [[[tl vl] Vl] LASTML] : is_Some (last ML).
      { rewrite last_is_Some. unfold not. intros. subst ML. done. }
      rewrite last_lookup in LASTML. replace (Init.Nat.pred (length ML)) with (length ML - 1) in LASTML by lia.

      destruct (decide (i = length ML - 1)) as [->|NEQ].
      - rewrite MLi in LASTML. inversion LASTML. rewrite last_lookup. subst tl vl Vl.
        replace (Init.Nat.pred (length ML)) with (length ML - 1) by lia. done.
      - apply lookup_lt_Some in MLi as LT.
        have LT' : i < length ML - 1 by lia.
        have LOOKUP1 : ML.*1.*1 !! i = Some t' by rewrite !list_lookup_fmap MLi.
        have LOOKUP2 : ML.*1.*1 !! (length ML - 1) = Some tl by rewrite !list_lookup_fmap LASTML.
        specialize (ML_t_valid _ _ _ _ LOOKUP1 LOOKUP2 LT').
        unfold no_earlier_time in *. apply elem_of_list_lookup_2 in LASTML. rewrite -ζ_ML_valid in LASTML.
        have LE : (tl ≤ t')%positive.
        { apply MAXt'2. rewrite LASTML. done. }
        lia. }

    iDestruct (OmoAuth_omo_nonempty with "M●") as %Nomo.
    have [[el esl] LASTomo] : is_Some (last omo) by rewrite last_is_Some.
    iDestruct (big_sepL2_lookup with "ML✓") as (?? eVl ???) "((%EQ1 & %eVlEV & %EQ2) & #el✓eVl & #el↪stl & _)".
    { rewrite last_lookup in LASTomo. done. } { rewrite last_lookup -EQlenML in LASTML. done. }
    inversion EQ1. inversion EQ2. subst e0 es t v V0. clear EQ1 EQ2.

    iDestruct (OmoUB_from_gen with "M●") as "#MAXgen"; [exact Heidx|exact MAXgen|done|].
    iDestruct (OmoLe_get _ _ _ _ _ _ eidx (wr_event (length omo - 1)) with "M●") as "#e≤el"; [done|..].
    { rewrite lookup_omo_wr_event /omo_write_op list_lookup_fmap.
      rewrite last_lookup in LASTomo. replace (Init.Nat.pred (length omo)) with (length omo - 1) in LASTomo by lia.
      rewrite LASTomo. done. } { apply lookup_omo_lt_Some in Heidx. simpl. lia. }
    iDestruct (OmoUB_mono with "MAXgen e≤el") as "MAXgen'".

    set en := (length E).
    set M' := {[en]} ∪ M.
    set st := (en, (#vw, Vw)).
    set eVn := mkOmoEvent (UpdateE el (#vw, Vw)) V'' M'.

    iDestruct (view_at_mono_2 _ V'' with "⊒M@V'") as "⊒M@V''"; [done|].
    iDestruct (OmoAuth_OmoSnap _ _ _ _ _ _ _ (wr_event (length omo - 1)) with "M● el↪stl") as %LASTmo.
    { rewrite lookup_omo_wr_event /omo_write_op list_lookup_fmap.
      rewrite last_lookup in LASTomo. replace (Init.Nat.pred (length omo)) with (length omo - 1) in LASTomo by lia.
      rewrite LASTomo. done. }
    apply omo_stlist_length in OMO_GOOD as EQlenmo. rewrite EQlenmo /= in LASTmo.
    replace (length mo - 1) with (Init.Nat.pred (length mo)) in LASTmo by lia. rewrite -last_lookup in LASTmo.
    iMod (OmoAuth_insert_last_no_Token with "M● ⊒M@V'' []") as "(M● & #⊒M'@V'' & #en✓eVn & #en↪stn & WCOMMIT)".
    { have ? : step en eVn (el, (#vr, Vr)) st.
      { apply loc_step_UpdateE; try done. set_solver-. }
      iPureIntro. split_and!; try done. }
    iDestruct (OmoHbToken_finish with "M●") as "[M● M●']".

    set omo' := omo_append_w omo (length E) [].
    set ML' := ML ++ [((t' + 1)%positive, #vw, Vw)].
    iAssert (|==> match ty with
      | cas_only => ⎡mono_list_auth_own γw q (omo_write_op omo')⎤ ∗ ⎡mono_list_auth_own γm q ML'⎤
      | swriter => ⎡mono_list_auth_own γw q (omo_write_op omo)⎤ ∗ ⎡mono_list_auth_own γm q ML⎤
    end)%I with "[ES● ML●]" as ">Hty".
    { destruct ty.
      - subst q.
        iMod (mono_list_auth_own_update ML' with "ML●") as "[ML● _]"; [by eapply prefix_app_r|].
        iMod (mono_list_auth_own_update (omo_write_op omo') with "ES●") as "[ES● _]".
        { rewrite omo_append_w_write_op. by eapply prefix_app_r. }
        iModIntro. iFrame "ML● ES●".
      - iModIntro. iFrame "ML● ES●". }

    iAssert (OMO_ML_valid γe γl γs l omo' ML')%I with "[-]" as "#ML'✓".
    { unfold OMO_ML_valid. subst omo' ML'. rewrite /omo_append_w. iApply big_sepL2_snoc. iFrame "ML✓".
      iExists en,[],eVn,(t'+1)%positive,#vw,Vw. rewrite big_sepL_nil. iFrame "en✓eVn en↪stn". iSplit; [done|]. iSplit; [|done].
      iApply (view_at_mono with "l⊒ζ''@V''"); [done|]. iApply AtomicSeen_mono_lookup_singleton. done. }

    have ML'_t_valid : ML_time_mono ML'.
    { rewrite /ML_time_mono. intros. destruct (le_lt_dec (length ML) i2) as [LE|LT].
      - have EQ : i2 = length ML; [|subst i2].
        { apply lookup_lt_Some in H0. subst ML'. rewrite !fmap_length app_length /= in H0. lia. }
        have LT : i1 < length ML.
        { apply lookup_lt_Some in H. subst ML'. rewrite !fmap_length app_length /= in H. lia. }
        subst ML'. rewrite !list_lookup_fmap lookup_app_1_eq in H0. inversion H0. subst t2. clear H0.
        rewrite !list_lookup_fmap lookup_app_1_ne in H; [|lia]. rewrite -!list_lookup_fmap in H.

        have H' : ML.*1.*1 !! (length ML - 1) = Some t'.
        { rewrite !list_lookup_fmap. rewrite last_lookup in LASTML.
          replace (Init.Nat.pred (length ML)) with (length ML - 1) in LASTML by lia. rewrite LASTML. done. }
        have LEt : (t1 ≤ t')%positive.
        { destruct (decide (i1 = length ML - 1)) as [->|NEQ].
          - rewrite H in H'. inversion H'. done.
          - have LTt : i1 < length ML - 1 by lia.
            specialize (ML_t_valid _ _ _ _ H H' LTt). lia. }
        lia.
      - rewrite !list_lookup_fmap lookup_app_1_ne in H; [|lia]. rewrite -!list_lookup_fmap in H.
        rewrite !list_lookup_fmap lookup_app_1_ne in H0; [|lia]. rewrite -!list_lookup_fmap in H0.
        eapply ML_t_valid; try done. }

    have ζn_comp : Hist_comparable ζn.
    { subst ζn. unfold Hist_comparable in *. intros. destruct (decide (t = (t'+1)%positive)) as [->|NEQ].
      - rewrite lookup_insert in H. inversion H. subst v V0. exists vw. done.
      - rewrite lookup_insert_ne in H; [|done]. eapply ζ_comp; try done. }

    have ζn_ML'_valid : Hist_ML_valid ζn ML'.
    { subst ζn. unfold Hist_ML_valid in *. intros. destruct (decide (t = (t'+1)%positive)) as [->|NEQ].
      - rewrite lookup_insert. split; intros.
        + inversion H. subst v V0 ML'. rewrite elem_of_list_lookup. exists (length ML). by rewrite lookup_app_1_eq.
        + rewrite elem_of_list_lookup in H. destruct H as [i Hi]. destruct (decide (i = length ML)) as [->|NEq].
          * rewrite lookup_app_1_eq in Hi. inversion Hi. done.
          * rewrite lookup_app_1_ne in Hi; [|done]. apply elem_of_list_lookup_2 in Hi.
            rewrite -ζ_ML_valid in Hi. rewrite ζSt' in Hi. done.
      - rewrite lookup_insert_ne; [|done]. split; intros.
        + rewrite elem_of_app. left. by rewrite -ζ_ML_valid.
        + rewrite elem_of_list_lookup in H. destruct H as [i Hi].
          destruct (decide (i = length ML)) as [->|NEQ'].
          * rewrite lookup_app_1_eq in Hi. inversion Hi. done.
          * rewrite lookup_app_1_ne in Hi; [|done]. apply elem_of_list_lookup_2 in Hi. by rewrite ζ_ML_valid. }

    have ζn_uf_valid : uf_valid ζn uf.
    { subst ζn. unfold uf_valid in *. intros. destruct (decide (t = (t'+1)%positive)) as [->|NEQ].
      - rewrite lookup_insert in H. inversion H. subst v V0. clear H. right.
        unfold no_earlier_time. intros. destruct (decide (t'0 = (t'+1)%positive)) as [->|NEQ']; [done|].
        rewrite lookup_insert_ne in H; [|done].

        destruct H as [[vm' Vm'] H].
        unfold Hist_ML_valid in *. rewrite ζ_ML_valid elem_of_list_lookup in H.
        destruct H as [i Hi].

        have LE : (t'0 ≤ t')%positive.
        { rewrite last_lookup in LASTML. replace (Init.Nat.pred (length ML)) with (length ML - 1) in LASTML by lia.
          destruct (decide (i = length ML - 1)) as [->|NEQ].
          - rewrite Hi in LASTML. inversion LASTML. subst t'0 vm' Vm'. done.
          - apply lookup_lt_Some in Hi as LTi.
            have LTi' : i < length ML - 1 by lia.
            have LOOKUP1 : ML.*1.*1 !! i = Some t'0 by rewrite !list_lookup_fmap Hi.
            have LOOKUP2 : ML.*1.*1 !! (length ML - 1) = Some t' by rewrite !list_lookup_fmap LASTML.
            specialize (ML_t_valid _ _ _ _ LOOKUP1 LOOKUP2 LTi'). lia. }
        have ? : (t'0 ≤ (t'+1))%positive by lia. done.
      - rewrite lookup_insert_ne in H; [|done].
        destruct (decide (t' = t)%positive) as [->|NEQ']; [by rewrite lookup_insert in H0|].
        rewrite lookup_insert_ne in H0; [|lia].
        apply ζ_uf_valid in H as CASE'; [|done]. destruct CASE' as [IN|MAXgen'].
        + left. clear -IN. set_solver.
        + have LE1 : (t' ≤ t)%positive.
          { apply MAXgen'. rewrite last_lookup in LASTML. apply elem_of_list_lookup_2 in LASTML.
            rewrite -ζ_ML_valid in LASTML. rewrite LASTML. done. }
          have LE2 : (t ≤ t')%positive.
          { rewrite ζ_ML_valid elem_of_list_lookup in H. destruct H as [i Hi].
            rewrite last_lookup in LASTML. replace (Init.Nat.pred (length ML)) with (length ML - 1) in LASTML by lia.
            destruct (decide (i = length ML - 1)) as [->|NEQ''].
            - rewrite LASTML in Hi. inversion Hi. done.
            - apply lookup_lt_Some in Hi as LT.
              have LT' : i < length ML - 1 by lia.
              have LOOKUP1 : ML.*1.*1 !! i = Some t by rewrite !list_lookup_fmap Hi.
              have LOOKUP2 : ML.*1.*1 !! (length ML - 1) = Some t' by rewrite !list_lookup_fmap LASTML.
              specialize (ML_t_valid _ _ _ _ LOOKUP1 LOOKUP2 LT'). lia. }
          have EQ : t = t' by lia. subst t. clear LE1 LE2. done. }

    iDestruct ("Post" $! true el (length omo - 1) vr Vr V'' (mo ++ [st]) omo' eVl eVn with "[-]") as "HΦ".
    { iFrame "M●' MAXgen' el✓eVl en✓eVn ⊒V'' ⊒M'@V''". iSplitR.
      { iPureIntro. split_and!; try done; [|solve_lat]. rewrite /omo_write_op list_lookup_fmap.
        rewrite last_lookup in LASTomo. replace (Init.Nat.pred (length omo)) with (length omo - 1) in LASTomo by lia.
        by rewrite LASTomo. }

      iRight. iFrame "WCOMMIT". iSplit; [done|]. iExists Vw. iFrame "F". iSplit.
      { iPureIntro. split_and!; try done. unfold not. intros. subst V''.
        have ? : V = V' by solve_lat. done. }

      iSplitR.
      { destruct (decide (AcqRel ⊑ ow)).
        - destruct (decide (AcqRel ⊑ or)).
          + subst Vw. iFrame "⊒M'@V''".
          + iFrame "⊒M'@V''".
        - done. }

      destruct ty.
      - iDestruct "Hty" as "[ES● ML●]".
        iExists γx,γl,γw,γm,γs. iExists _,omo',_,_,ML',ζn. iFrame "M● ML● ES● l↦ Hγx ML'✓". rewrite view_at_objective_iff. done.
      - iIntros (??) "SW". rewrite swriter_token_eq.
        iDestruct "SW" as (????? tl vl Vl) "([%Hγx' %LASTML'] & #Hγx' & ES●' & ML●' & #l⊒SW)".
        rewrite !view_at_objective_iff.
        iDestruct (OmoGname_agree with "Hγx Hγx'") as %<-. encode_agree Hγx.
        iDestruct "Hty" as "[ES● ML●]".
        iDestruct (mono_list_auth_own_agree with "ES● ES●'") as %[_ <-].
        iDestruct (mono_list_auth_own_agree with "ML● ML●'") as %[_ <-].
        iCombine "ML● ML●'" as "ML●". iCombine "ES● ES●'" as "ES●". subst q.
        replace (1/2/2 + (1/2 + 1/2/2))%Qp with 1%Qp by compute_done.

        iMod (mono_list_auth_own_update ML' with "ML●") as "[ML● _]"; [by eapply prefix_app_r|].
        iMod (mono_list_auth_own_update (omo_write_op omo') with "ES●") as "[ES● _]".
        { rewrite omo_append_w_write_op. by eapply prefix_app_r. }
        iDestruct "ML●" as "[ML● [ML●' ML●'']]". iCombine "ML● ML●''" as "ML●".
        iDestruct "ES●" as "[ES● [ES●' ES●'']]". iCombine "ES● ES●''" as "ES●".

        iModIntro. iSplitL "ML● ES●".
        + iExists γx,γl,γw,γm,ML',(t'+1)%positive,#vw,Vw. iFrame "Hγx ML● ES●". iSplit.
          { iPureIntro. split; [done|]. rewrite last_app. done. }
          iApply (view_at_mono with "l⊒ζ''@V''"); [solve_lat|].
          iApply AtomicSeen_mono_lookup_singleton. done.
        + iExists γx,γl,γw,γm,γs. iExists _,omo',_,_,ML',ζn. iFrame "M● ML●' ES●' l↦ Hγx ML'✓". done. }

    iModIntro. by iApply "HΦ".
Qed.

Lemma append_only_loc_cas_only_cas l γe γs mo E omo M uf orf or ow (vr : lit) (vw : lit) tid (Vrel : view) V Vb (Ec : coPset) :
  Relaxed ⊑ orf → Relaxed ⊑ or → Relaxed ⊑ ow →
  ↑histN ⊆ Ec → #vr ∉ uf → vr ≠ ☠%V → vw ≠ ☠%V →
  {{{ OmoAuth γe γs (1/2)%Qp E omo mo _ ∗ OmoEview γe M ∗ @{Vb} append_only_loc l γe uf cas_only ∗ ⊒V ∗
      (if decide (AcqRel ⊑ ow) then True else △{tid} ⊒Vrel) }}}
    CAS #l #vr #vw orf or ow @ tid; Ec
  {{{ b e (gen : nat) (v' : lit) Vr V'' mo' omo' eV eV', RET #b;
      let E' := E ++ [eV'] in
      let e' := length E in
      let M' := {[e']} ∪ M in
      ⌜ (* read message *) omo_write_op omo !! gen = Some e ∧ loc_event_msg eV.(type) = (#v', Vr)
      ∧ (* pre-view ⊑ post-view *) V ⊑ V'' ⌝ ∗
      OmoUB γe M e ∗
      OmoEinfo γe e eV ∗
      OmoEinfo γe e' eV' ∗
      OmoAuth γe γs (1/2)%Qp E' omo' mo' _ ∗
      ⊒V'' ∗ @{V''} OmoEview γe M' ∗ @{Vb ⊔ V''} append_only_loc l γe uf cas_only ∗
      ( (⌜b = false ∧ lit_neq vr v' ∧ mo' = mo
        ∧ omo' = omo_insert_r omo gen e'
        ∧ eV'.(type) = ReadE (#v', Vr)
        ∧ eV'.(sync) = V''⌝
        ∧ (if decide (AcqRel ⊑ orf) then ⌜Vr ⊑ V''⌝ else ▽{tid} ⊒Vr)
        ∗ OmoEq γe e e'
        ∗ OmoTokenR γe e')
      ∨ (⌜b = true ∧ v' = vr ∧ gen = (length omo - 1)%nat⌝
        ∧ ∃ Vw,
            ⌜ mo' = mo ++ [(e', (#vw, Vw))]
            ∧ omo' = omo_append_w omo e' []
            ∧ eV'.(type) = UpdateE e (#vw, Vw)
            ∧ eV'.(sync) = V''
            (* release sequence: Vwrite includes Vread *)
            ∧ Vr ⊑ Vw ∧ Vr ≠ Vw
            ∧ (¬ V'' ⊑ Vr)
            ∧ V ≠ V''
            ∧ ( if decide (AcqRel ⊑ ow) then
                  ( if decide (AcqRel ⊑ or) then
                      (* release-acquire CAS *) Vw = V''
                    else (* release CAS *) V'' ⊑ Vw )
                else (* relaxed write CAS *) Vrel ⊑ Vw ) ⌝
            ∧ (if decide (AcqRel ⊑ ow) then @{Vw} OmoEview γe M' else emp)
            ∗ (if decide (AcqRel ⊑ or) then ⌜Vw ⊑ V''⌝ else ▽{tid} ⊒Vw)
            ∗ OmoTokenW γe e')) }}}.
Proof.
  iIntros "%ORD1 %ORD2 %ORD3 %INCL1 %INCL2 %NEqvr %NEqvw" (Φ) "(M● & #⊒M & omo↦ & #⊒V & F) Post".
  wp_apply (append_only_loc_cas_general with "[$M● $⊒M $omo↦ $⊒V $F]"); try done.
  iIntros (??????????) "(Pures & #MAXgen & #e✓eV & #en✓eVn & M● & #⊒V'' & #⊒M'@V'' & CASE)".
  iDestruct "Pures" as %(Hgen & eVEV & LeVV'').
  iDestruct "CASE" as "[(Pures & F & omo↦ & #e=en & RCOMMIT) | [Pures sVw2]]".
  - iDestruct "Pures" as %(-> & NEq & -> & Homo' & eV'EV & eV'SYNC).
    iDestruct ("Post" $! false e gen v' Vr V'' mo omo' eV eV' with "[-]") as "HΦ".
    { iFrame "MAXgen e✓eV en✓eVn M● ⊒V'' ⊒M'@V'' omo↦". iSplit; [done|]. iLeft. iFrame "e=en RCOMMIT F". done. }
    by iApply "HΦ".
  - iDestruct "Pures" as %(-> & -> & ->).
    iDestruct "sVw2" as (Vw (Eqmo' & Homo' & eV'EV & eV'SYNC & LeVrVw & NEqVrVw & NLeV''Vr & NEqVV'' & CASE)) "(CASE & omo↦ & F & WCOMMIT)".
    iDestruct ("Post" $! true e (length omo - 1) vr Vr V'' mo' omo' eV eV' with "[-]") as "HΦ".
    { iFrame "MAXgen e✓eV en✓eVn M● ⊒V'' ⊒M'@V'' omo↦". iSplit; [done|]. iRight. iSplit; [done|]. iExists Vw. iFrame "WCOMMIT CASE F". done. }
    by iApply "HΦ".
Qed.

Lemma append_only_loc_swriter_cas l γe γs mo E omo es M uf orf or ow (vr : lit) (vw : lit) tid (Vrel : view) V Vb Vc (Ec : coPset) :
  Relaxed ⊑ orf → Relaxed ⊑ or → Relaxed ⊑ ow →
  ↑histN ⊆ Ec → #vr ∉ uf → vr ≠ ☠%V → vw ≠ ☠%V →
  {{{ OmoAuth γe γs (1/2)%Qp E omo mo _ ∗ OmoEview γe M ∗
      @{Vb} append_only_loc l γe uf swriter ∗ @{Vc} swriter_token l γe es ∗ ⊒V ∗
      (if decide (AcqRel ⊑ ow) then True else △{tid} ⊒Vrel) }}}
    CAS #l #vr #vw orf or ow @ tid; Ec
  {{{ b e (gen : nat) (v' : lit) Vr V'' mo' es' omo' eV eV', RET #b;
      let E' := E ++ [eV'] in
      let e' := length E in
      let M' := {[e']} ∪ M in
      ⌜ (* read message *) omo_write_op omo !! gen = Some e ∧ loc_event_msg eV.(type) = (#v', Vr)
      ∧ (* pre-view ⊑ post-view *) V ⊑ V'' ⌝ ∗
      OmoUB γe M e ∗
      OmoEinfo γe e eV ∗
      OmoEinfo γe e' eV' ∗
      OmoAuth γe γs (1/2)%Qp E' omo' mo' _ ∗
      ⊒V'' ∗ @{V''} OmoEview γe M' ∗
      @{Vb ⊔ V''} append_only_loc l γe uf swriter ∗
      ( (⌜b = false ∧ lit_neq vr v' ∧ mo' = mo ∧ es' = es
        ∧ omo' = omo_insert_r omo gen e'
        ∧ eV'.(type) = ReadE (#v', Vr)
        ∧ eV'.(sync) = V''⌝
        ∧ (if decide (AcqRel ⊑ orf) then ⌜Vr ⊑ V''⌝ else ▽{tid} ⊒Vr)
        ∗ @{Vc} swriter_token l γe es'
        ∗ OmoEq γe e e'
        ∗ OmoTokenR γe e')
      ∨ (⌜b = true ∧ v' = vr ∧ gen = (length omo - 1)%nat⌝
          ∧ ∃ Vw,
              ⌜ mo' = mo ++ [(e', (#vw, Vw))] ∧ es' = es ++ [e']
              ∧ omo' = omo_append_w omo e' []
              ∧ eV'.(type) = UpdateE e (#vw, Vw)
              ∧ eV'.(sync) = V''
              (* release sequence: Vwrite includes Vread *)
              ∧ Vr ⊑ Vw ∧ Vr ≠ Vw
              ∧ (¬ V'' ⊑ Vr)
              ∧ V ≠ V''
              ∧ ( if decide (AcqRel ⊑ ow) then
                    ( if decide (AcqRel ⊑ or) then
                        (* release-acquire CAS *) Vw = V''
                      else (* release CAS *) V'' ⊑ Vw )
                  else (* relaxed write CAS *) Vrel ⊑ Vw )⌝
              ∧ (if decide (AcqRel ⊑ ow) then @{Vw} OmoEview γe M' else emp)
              ∗ (if decide (AcqRel ⊑ or) then ⌜Vw ⊑ V''⌝ else ▽{tid} ⊒Vw)
              ∗ @{Vc ⊔ V''} swriter_token l γe es'
              ∗ OmoTokenW γe e')) }}}.
Proof.
  iIntros "%ORD1 %ORD2 %ORD3 %INCL1 %INCL2 %NEqvr %NEqvw" (Φ) "(M● & #⊒M & omo↦ & SW & #⊒V & F) Post".
  iDestruct (OmoAuth_swriter_token_agree_obj_1 with "M● omo↦ SW") as %EQes.
  wp_apply wp_fupd. wp_apply (append_only_loc_cas_general with "[$M● $⊒M $omo↦ $⊒V $F]"); try done.
  iIntros (??????????) "(Pures & #MAXgen & #e✓eV & #en✓eVn & M● & #⊒V'' & #⊒M'@V'' & CASE)".
  iDestruct "Pures" as %(Hgen & eVEV & LeVV'').
  iDestruct "CASE" as "[(Pures & F & omo↦ & #e=en & RCOMMIT) | [Pures sVw2]]".
  - iDestruct "Pures" as %(-> & NEq & -> & Homo' & eV'EV & eV'SYNC).
    iDestruct ("Post" $! false e gen v' Vr V'' mo es omo' eV eV' with "[-]") as "HΦ".
    { iFrame "MAXgen e✓eV en✓eVn M● ⊒V'' ⊒M'@V'' omo↦ SW". iSplit; [done|]. iLeft. iFrame "e=en RCOMMIT F". done. }
    by iApply "HΦ".
  - iDestruct "Pures" as %(-> & -> & ->).
    iDestruct "sVw2" as (Vw (Eqmo' & Homo' & eV'EV & eV'SYNC & LeVrVw & NEqVrVw & NLeV''Vr & NEqVV'' & CASE)) "(CASE & omo↦ & F & WCOMMIT)".
    iMod ("omo↦" with "SW") as "[SW omo↦]".
    iDestruct ("Post" $! true e (length omo - 1) vr Vr V'' mo' (omo_write_op omo') omo' eV eV' with "[-]") as "HΦ".
    { iFrame "MAXgen e✓eV en✓eVn M● ⊒V'' ⊒M'@V'' omo↦". iSplit; [done|]. iRight. iSplit; [done|]. iExists Vw. iFrame "WCOMMIT CASE F SW".
      iPureIntro. split_and!; try done. subst omo'. rewrite omo_append_w_write_op EQes. done. }
    by iApply "HΦ".
Qed.

Lemma append_only_loc_cas_fail l γe γs mo E omo M uf ty orf or ow (vr : lit) (vw : val) tid (Vrel : view) V Vb (Ec : coPset) :
  Relaxed ⊑ orf → Relaxed ⊑ or → Relaxed ⊑ ow →
  ↑histN ⊆ Ec → #vr ∉ uf → vr ≠ ☠%V →
  {{{ OmoAuth γe γs (1/2)%Qp E omo mo _ ∗ OmoEview γe M ∗
      @{Vb} append_only_loc l γe uf ty ∗ ⊒V ∗
      (if decide (AcqRel ⊑ ow) then True else △{tid} ⊒Vrel) ∗
      append_only_loc_cas_latest_neq γe omo vr }}}
    CAS #l #vr vw orf or ow @ tid; Ec
  {{{ e (gen : nat) (v' : lit) Vr V'' omo' eV eV', RET #false;
      let E' := E ++ [eV'] in
      let e' := length E in
      let M' := {[e']} ∪ M in
      ⌜ (* read message *) omo_write_op omo !! gen = Some e ∧ loc_event_msg eV.(type) = (#v', Vr)
      ∧ (* pre-view ⊑ post-view *) V ⊑ V'' ⌝ ∗
      OmoUB γe M e ∗
      OmoEinfo γe e eV ∗
      OmoEinfo γe e' eV' ∗
      OmoEq γe e e' ∗
      OmoAuth γe γs (1/2)%Qp E' omo' mo _ ∗
      OmoTokenR γe e' ∗
      ⊒V'' ∗ @{V''} OmoEview γe M' ∗
      @{Vb ⊔ V''} (append_only_loc l γe uf ty) ∗
      (if decide (AcqRel ⊑ orf) then ⌜Vr ⊑ V''⌝ else ▽{tid} ⊒Vr) ∗
      ⌜ lit_neq vr v'
      ∧ omo' = omo_insert_r omo gen e'
      ∧ eV'.(type) = ReadE (#v', Vr)
      ∧ eV'.(sync) = V''⌝ }}}.
Proof.
  iIntros "%ORD1 %ORD2 %ORD3 %INCL1 %INCL2 %NEqvr" (Φ) "(M● & #⊒M & omo↦ & #⊒V & F & #FAIL) Post". rewrite append_only_loc_eq.
  iDestruct "omo↦" as (??????????) "(%& %Hγx & #Hγx & M●' & ES● & ML● & l↦ & #ML✓ & (%ML_t_valid & %ζ_comp & %ζ_ML_valid & %ζ_uf_valid & %Hty))".
  rewrite !view_at_objective_iff.
  iDestruct (OmoAuth_agree with "M● M●'") as %(<- & <- & <- & <-).
  iDestruct (OmoAuth_wf with "M●") as %[OMO_GOOD _].
  iDestruct (OmoEview_nonempty with "⊒M") as %NEmp.
  iDestruct (OmoAuth_OmoEview with "M● ⊒M") as %MIncl.
  iDestruct (big_sepL2_length with "ML✓") as %EQlenML.
  iCombine "M● M●'" as "M●".

  iDestruct (view_at_intro_incl with "⊒M ⊒V") as (V') "(#⊒V' & %LeVV' & #⊒M@V')".

  (* Extract latest observed message *)
  iAssert (∃ e em eidx tm vm Vm,
    ⌜ e ∈ M ∧ lookup_omo omo eidx = Some e ∧ ML !! (gen_of eidx) = Some (tm, vm, Vm) ∧ OmoUBgen omo M (gen_of eidx) ⌝ ∗
    l sn⊒{γl} {[tm := (vm, Vm)]} ∗ OmoSnap γe γs e (em, (vm, Vm)))%I
      with "[-]" as "(%&%&%&%&%&%& (%eIn & %Heidx & %MLgen & %MAXgen) & #l⊒ & #e↪st)".
  { iClear "Post ⊒M@V'". iInduction M as [|e M NotIn] "IH" using set_ind_L; [done|].
    destruct (decide (M = ∅)) as [Memp|NEmp'].
    - have EQ : {[e]} ∪ M = {[e]} by set_solver. rewrite !EQ. clear EQ.
      have HeV : e ∈ ({[e]} ∪ M) by set_solver-. apply MIncl in HeV.
      eapply lookup_omo_surjective in HeV as Heidx; [|done]. destruct Heidx as [eidx Heidx]. destruct HeV as [eV HeV].
      have [[e' es'] Hgen] : is_Some (omo !! (gen_of eidx)).
      { rewrite lookup_lt_is_Some. apply lookup_omo_lt_Some in Heidx. done. }
      have [minfo Hminfo] : is_Some (ML !! (gen_of eidx)).
      { rewrite lookup_lt_is_Some -EQlenML. apply lookup_lt_Some in Hgen. done. }
      iDestruct (big_sepL2_lookup with "ML✓") as (?? eV' tm vm Vm) "((%EQ1 & %eV'EV & %EQ2) & #e'✓eV' & #e'↪st' & l⊒@SYNC' & BIG)"; [done|done|].
      inversion EQ1. subst e0 es minfo. clear EQ1.
      destruct eidx.
      + simpl in Hgen. rewrite lookup_omo_ro_event /omo_read_op list_lookup_fmap Hgen /= in Heidx.
        iDestruct (big_sepL_lookup with "BIG") as (?) "(%eVEV & e✓eV & e↪st & l⊒@SYNC)"; [done|].
        iDestruct (OmoEinfo_get with "M●") as "#e✓eV'"; [done|].
        iDestruct (OmoEinfo_agree with "e✓eV e✓eV'") as %->.
        iDestruct (OmoEinfo_OmoEview _ e with "e✓eV ⊒M") as "⊒SYNC"; [set_solver-|].
        iDestruct (view_at_elim with "⊒SYNC l⊒@SYNC") as "l⊒".
        iExists e,e',(ro_event gen i'),tm,vm,Vm. iFrame "l⊒ e↪st". iPureIntro. split_and!; try done.
        * set_solver-.
        * rewrite lookup_omo_ro_event /omo_read_op list_lookup_fmap Hgen. done.
        * rewrite /OmoUBgen. intros.
          have EQ : e0 = e by set_solver. subst e0. exists (ro_event gen i'). split.
          -- rewrite lookup_omo_ro_event /omo_read_op list_lookup_fmap Hgen. done.
          -- done.
      + simpl in Hgen. rewrite lookup_omo_wr_event /omo_write_op list_lookup_fmap Hgen /= in Heidx. inversion Heidx. subst e'. clear Heidx.
        iDestruct (OmoEinfo_get with "M●") as "#e✓eV"; [done|].
        iDestruct (OmoEinfo_agree with "e✓eV e'✓eV'") as %<-.
        iDestruct (OmoEinfo_OmoEview _ e with "e✓eV ⊒M") as "⊒SYNC"; [set_solver-|].
        iDestruct (view_at_elim with "⊒SYNC l⊒@SYNC'") as "l⊒".
        iExists e,e,(wr_event gen),tm,vm,Vm. iFrame "l⊒ e'↪st'". iPureIntro. split_and!; try done.
        * set_solver-.
        * rewrite lookup_omo_wr_event /omo_write_op list_lookup_fmap Hgen. done.
        * rewrite /OmoUBgen. intros.
          have EQ : e0 = e by set_solver. subst e0. exists (wr_event gen). split; [|done].
          rewrite lookup_omo_wr_event /omo_write_op list_lookup_fmap Hgen. done.
    - iDestruct (OmoEview_split with "⊒M") as "[⊒e ⊒M']"; [set_solver-|done|].
      iDestruct ("IH" with "[] [] ⊒M' ES● ML● l↦ F M●") as "#H"; [done|..].
      { iPureIntro. intros. apply MIncl. set_solver. }
      iDestruct "H" as (e' ew' eidx' tm' vm' Vm') "((%e'IN & %Heidx' & %MLgen' & %MAXgen) & l⊒' & e'↪st')".
      have HeV : e ∈ ({[e]} ∪ M) by set_solver-. apply MIncl in HeV.
      eapply lookup_omo_surjective in HeV as Heidx; [|done]. destruct Heidx as [eidx Heidx]. destruct HeV as [eV HeV].

      destruct (le_lt_dec (gen_of eidx) (gen_of eidx')) as [LE|LT].
      { (* [e] is non-latest event -> induction hypothesis is the answer *)
        iExists e',ew',eidx',tm',vm',Vm'. iFrame "l⊒' e'↪st'". iPureIntro. split_and!; try done.
        - set_solver.
        - rewrite /OmoUBgen. intros.
          have CASE : e0 = e ∨ e0 ∈ M by set_solver.
          destruct CASE as [->|IN].
          + exists eidx. done.
          + apply MAXgen. done. }

      (* [e] is the latest event *)
      have [[e'' es''] Hgen] : is_Some (omo !! (gen_of eidx)).
      { rewrite lookup_lt_is_Some. apply lookup_omo_lt_Some in Heidx. done. }
      have [minfo Hminfo] : is_Some (ML !! (gen_of eidx)).
      { rewrite lookup_lt_is_Some -EQlenML. apply lookup_lt_Some in Hgen. done. }
      iDestruct (big_sepL2_lookup with "ML✓") as (?? eV'' tm vm Vm) "((%EQ1 & %eV''EV & %EQ2) & e''✓eV'' & e''↪st'' & l⊒@SYNC' & BIG)"; [done|done|].
      inversion EQ1. subst e0 es minfo. clear EQ1. destruct eidx.
      + simpl in Hgen. rewrite lookup_omo_ro_event /omo_read_op list_lookup_fmap Hgen /= in Heidx.
        iDestruct (big_sepL_lookup with "BIG") as (?) "(%eVEV & e✓eV & e↪st & l⊒@SYNC)"; [done|].
        iDestruct (OmoEinfo_get with "M●") as "#e✓eV'"; [done|].
        iDestruct (OmoEinfo_agree with "e✓eV e✓eV'") as %->.
        iDestruct (OmoEinfo_OmoEview _ e with "e✓eV ⊒M") as "⊒SYNC"; [set_solver-|].
        iDestruct (view_at_elim with "⊒SYNC l⊒@SYNC") as "l⊒".
        iExists e,e'',(ro_event gen i'),tm,vm,Vm. iFrame "l⊒ e↪st". iPureIntro. split_and!; try done.
        * set_solver-.
        * rewrite lookup_omo_ro_event /omo_read_op list_lookup_fmap Hgen. done.
        * rewrite /OmoUBgen. intros.
          have CASE : e0 = e ∨ e0 ∈ M by set_solver. destruct CASE as [->|IN].
          -- exists (ro_event gen i'). split; [|done]. rewrite lookup_omo_ro_event /omo_read_op list_lookup_fmap Hgen. done.
          -- unfold OmoUBgen in *. specialize (MAXgen _ IN) as (eidx'' & Heidx'' & LE).
             exists eidx''. split; [done|]. simpl in *. lia.
      + simpl in Hgen. rewrite lookup_omo_wr_event /omo_write_op list_lookup_fmap Hgen /= in Heidx. inversion Heidx. subst e''. clear Heidx.
        iDestruct (OmoEinfo_get with "M●") as "#e✓eV"; [done|].
        iDestruct (OmoEinfo_agree with "e✓eV e''✓eV''") as %<-.
        iDestruct (OmoEinfo_OmoEview _ e with "e✓eV ⊒M") as "⊒SYNC"; [set_solver-|].
        iDestruct (view_at_elim with "⊒SYNC l⊒@SYNC'") as "l⊒".
        iExists e,e,(wr_event gen),tm,vm,Vm. iFrame "l⊒ e''↪st''". iPureIntro. split_and!; try done.
        * set_solver-.
        * rewrite lookup_omo_wr_event /omo_write_op list_lookup_fmap Hgen. done.
        * rewrite /OmoUBgen. intros.
          have CASE : e0 = e ∨ e0 ∈ M by set_solver. destruct CASE as [->|IN].
          -- exists (wr_event gen). split; [|done]. rewrite lookup_omo_wr_event /omo_write_op list_lookup_fmap Hgen. done.
          -- unfold OmoUBgen in *. specialize (MAXgen _ IN) as (eidx'' & Heidx'' & LE).
             exists eidx''. split; [done|]. simpl in *. lia. }

  wp_apply wp_fupd. wp_apply (AtomicSeen_CON_CAS _ _ _ _ _ _ _ _ vw with "[$l⊒ $l↦ $⊒V' $F]"); [done|done|done|done|..].
  { intros. unfold Hist_comparable in *.
    destruct (ζ !! t) eqn:Heq; try done. destruct p as [? ?]. inversion H0. subst v0. clear H0.
    apply ζ_comp in Heq. destruct Heq as (vl & EQ & NEQ). subst v. exists vl. split; [done|]. destruct vr, vl; try done; try constructor. }

  iIntros (???????) "(Pures & #⊒V'' & #l⊒ζ''@V'' & l↦ & CASE)".
  iDestruct "Pures" as %([Subζζ'' Subζ''ζn] & Hζ''t' & MAXt' & LeV'V'').
  iDestruct "CASE" as "[[(%&%&%) F]|[[%%] CASE]]".
  - (* CAS failed *)
    subst b ζn.

    iAssert (∃ ir, ⌜ ML !! ir = Some (t', #v', Vr) ∧ gen_of eidx ≤ ir ⌝)%I with "[-]" as %(ir & MLir & LEir).
    { unfold Hist_ML_valid in *. unfold no_earlier_time in *. unfold ML_time_mono in *.
      have Htr' : ζ !! t' = Some (#v', Vr) by eapply lookup_weaken.
      rewrite ζ_ML_valid elem_of_list_lookup in Htr'. destruct Htr' as [ir MLir].
      have Letwtr : (tm ≤ t')%positive by apply MAXt'; rewrite lookup_singleton.

      iExists ir. iPureIntro. split; [done|].
      destruct (le_lt_dec (gen_of eidx) ir) as [LE|LT]; try done.
      have COND1 : ML.*1.*1 !! ir = Some t' by rewrite !list_lookup_fmap MLir.
      have COND2 : ML.*1.*1 !! (gen_of eidx) = Some tm by rewrite !list_lookup_fmap MLgen.
      specialize (ML_t_valid _ _ _ _ COND1 COND2 LT). lia. }

    have [[er esr] OMOer] : is_Some (omo !! ir).
    { rewrite lookup_lt_is_Some EQlenML. apply lookup_lt_Some in MLir. done. }
    iDestruct (big_sepL2_lookup with "ML✓") as (?? eVr ???) "((%EQ1 & %eVrEV & %EQ2) & #er✓eVr & #er↪str & _)"; [done|done|].
    inversion EQ1. inversion EQ2. subst e0 es t v V0. clear EQ1 EQ2.
    iDestruct (OmoLe_get _ _ _ _ _ _ eidx (wr_event ir) with "M●") as "#e≤er".
    { done. } { rewrite lookup_omo_wr_event /omo_write_op list_lookup_fmap OMOer. done. } { simpl. done. }

    set en := (length E).
    set M' := {[en]} ∪ M.
    set st := (er, (#v', Vr)).
    set eVn := mkOmoEvent (ReadE (#v', Vr)) V'' M'.

    iDestruct (OmoUB_from_gen with "M●") as "#MAXgen"; [exact Heidx|exact MAXgen|done|].
    iDestruct (OmoUB_mono with "MAXgen e≤er") as "MAXgen'". simpl.
    iDestruct (view_at_mono_2 _ V'' with "⊒M@V'") as "⊒M@V''"; [solve_lat|].
    iMod (OmoAuth_insert_ro_no_Token with "M● ⊒M@V'' er↪str MAXgen' []") as (?) "(M● & #⊒M'@V'' & #er=en & #en✓eVn & RCOMMIT & Pures)".
    { have ? : step en eVn st st.
      { apply loc_step_ReadE; try done. set_solver. }
      iPureIntro. split_and!; try done. }
    iDestruct "Pures" as %(eidx' & Heidx' & EQgen).
    iDestruct (OmoHbToken_finish with "M●") as "[M● M●']".

    apply lookup_omo_lt_Some in Heidx' as LT. rewrite omo_insert_r_length -EQgen in LT.
    have [es Hes] : is_Some (omo_read_op omo !! gen) by rewrite lookup_lt_is_Some -omo_read_op_length.
    erewrite lookup_omo_before_insert_r in Heidx'; [|done].
    destruct (decide (eidx' = ro_event gen (length es))) as [->|NEQ]; last first.
    { eapply lookup_omo_event_valid in Heidx'; [|done]. rewrite lookup_lt_is_Some in Heidx'. lia. }

    set omo' := omo_insert_r omo gen (length E).
    have Heidx'' : lookup_omo omo' (wr_event ir) = Some er.
    { subst omo'. erewrite lookup_omo_before_insert_r; [|done]. rewrite decide_False; [|done].
      rewrite lookup_omo_wr_event /omo_write_op list_lookup_fmap OMOer. done. }
    iDestruct (OmoEq_Eq with "M● er=en") as %EQgen'; [done|done|].
    simpl in EQgen'. clear EQgen. subst ir.

    iDestruct ("Post" $! er gen v' Vr V'' omo' eVr eVn with "[-]") as "HΦ".
    { iFrame "M●' ⊒M'@V'' MAXgen' er✓eVr en✓eVn ⊒V'' er=en RCOMMIT F". iSplitR; last iSplitL.
      - iPureIntro. split_and!; try done; [|solve_lat]. rewrite /omo_write_op list_lookup_fmap OMOer. done.
      - iExists γx,γl,γw,γm,γs. iExists _,omo',mo,_,ML,ζ. rewrite omo_insert_r_write_op. iFrame "M● ES● ML● Hγx l↦".
        iSplit; [done|]. iSplit; [|done]. rewrite view_at_objective_iff /OMO_ML_valid. subst omo'. rewrite /omo_insert_r.

        rewrite -{3}(take_drop gen omo) (drop_S _ (er, esr)); [|done].
        rewrite alter_app_r_alt; [|by rewrite take_length; lia].
        replace (gen - length (take gen omo)) with 0; last first.
        { rewrite take_length Nat.min_l; [lia|]. apply lookup_lt_Some in OMOer. lia. }
        rewrite -{2}(take_drop gen ML) (drop_S _ (t',#v',Vr)) /=; [|done].
        rewrite -{2}(take_drop gen omo) (drop_S _ (er, esr)); [|done].
        rewrite -{1}(take_drop gen ML) (drop_S _ (t',#v',Vr)) /=; [|done].
        iDestruct (big_sepL2_app_inv with "ML✓") as "[ML✓1 ML✓2]".
        { left. rewrite !take_length EQlenML. done. }
        rewrite big_sepL2_cons. iDestruct "ML✓2" as "[ML✓2' ML✓3]".

        iApply big_sepL2_app; [done|].
        iApply big_sepL2_cons. iFrame "ML✓3".
        iDestruct "ML✓2'" as (??????) "((%EQ1 & %eVrEV' & %EQ2) & er✓eVr' & er↪str' & l⊒' & BIG)".
        inversion EQ1. inversion EQ2. subst e0 es0 t v V0. clear EQ1 EQ2.
        iDestruct (OmoEinfo_agree with "er✓eVr er✓eVr'") as %<-.
        iDestruct (OmoSnap_get_from_Eq with "er↪str er=en") as "en↪st".

        iExists er,(esr ++ [en]),eVr,t',#v',Vr. iFrame "er✓eVr er↪str l⊒'". iSplit; [done|]. rewrite big_sepL_snoc. iFrame "BIG".
        iExists eVn. iFrame "en✓eVn en↪st". iClear "l⊒".
        rewrite (AtomicSeen_mono_lookup_singleton _ _ _ t'); [|done].
        iFrame "l⊒ζ''@V''". done.
      - iPureIntro. split_and!; try done. }

    iModIntro. by iApply "HΦ".
  - (* CAS success: impossible *)
    subst b v'.
    iDestruct "CASE" as (Vw) "(Pures & l⊒CASE & F)".
    iDestruct "Pures" as %(ζSt' & EQζn & ζ''St' & LeVrVw & NeVrVw & NLeV''Vr & NeV'V'' & CASE).

    have ζt' : ζ !! t' = Some (#vr, Vr).
    { subst ζn. eapply lookup_weaken in Hζ''t'; [|exact Subζ''ζn]. rewrite lookup_insert_ne in Hζ''t'; [|lia]. done. }

    have LASTML : last ML = Some (t', #vr, Vr).
    { unfold uf_valid in *. eapply ζ_uf_valid in ζSt' as CASE'; [|done]. destruct CASE' as [?|MAXt'2]; [done|].
      rewrite ζ_ML_valid elem_of_list_lookup in ζt'. destruct ζt' as [i MLi].
      have [[[tl vl] Vl] LASTML] : is_Some (last ML).
      { rewrite last_is_Some. unfold not. intros. subst ML. done. }
      rewrite last_lookup in LASTML. replace (Init.Nat.pred (length ML)) with (length ML - 1) in LASTML by lia.

      destruct (decide (i = length ML - 1)) as [->|NEQ].
      - rewrite MLi in LASTML. inversion LASTML. rewrite last_lookup. subst tl vl Vl.
        replace (Init.Nat.pred (length ML)) with (length ML - 1) by lia. done.
      - apply lookup_lt_Some in MLi as LT.
        have LT' : i < length ML - 1 by lia.
        have LOOKUP1 : ML.*1.*1 !! i = Some t' by rewrite !list_lookup_fmap MLi.
        have LOOKUP2 : ML.*1.*1 !! (length ML - 1) = Some tl by rewrite !list_lookup_fmap LASTML.
        specialize (ML_t_valid _ _ _ _ LOOKUP1 LOOKUP2 LT').
        unfold no_earlier_time in *. apply elem_of_list_lookup_2 in LASTML. rewrite -ζ_ML_valid in LASTML.
        have LE : (tl ≤ t')%positive.
        { apply MAXt'2. rewrite LASTML. done. }
        lia. }

    iDestruct (OmoAuth_omo_nonempty with "M●") as %Nomo.
    have [[el esl] LASTomo] : is_Some (last omo) by rewrite last_is_Some.
    iDestruct (big_sepL2_lookup with "ML✓") as (?? eVl ???) "((%EQ1 & %eVlEV & %EQ2) & #el✓eVl & #el↪stl & _)".
    { rewrite last_lookup in LASTomo. done. } { rewrite last_lookup -EQlenML in LASTML. done. }
    inversion EQ1. inversion EQ2. subst e0 es t v V0. clear EQ1 EQ2.

    iDestruct "FAIL" as (??) "[#el✓eVl' [%LAST %eVlEV']]".
    rewrite last_lookup in LASTomo.
    rewrite last_lookup -omo_write_op_length /omo_write_op list_lookup_fmap LASTomo in LAST. inversion LAST. subst e0. clear LAST.
    iDestruct (OmoEinfo_agree with "el✓eVl el✓eVl'") as %<-.
    rewrite eVlEV in eVlEV'. done.
Qed.

(* CAS on locs values *)
Lemma append_only_loc_cas_live_loc_general l γe γs mo E omo M uf ty orf or ow (lr : loc) (vw : lit) tid (Vrel : view) V Vb (Ec : coPset) :
  Relaxed ⊑ orf → Relaxed ⊑ or → Relaxed ⊑ ow →
  ↑histN ⊆ Ec → #lr ∉ uf → vw ≠ ☠%V →
  {{{ OmoAuth γe γs (1/2)%Qp E omo mo _ ∗ OmoEview γe M ∗
      @{Vb} append_only_loc l γe uf ty ∗ ⊒V ∗
      (if decide (AcqRel ⊑ ow) then True else △{tid} ⊒Vrel) }}}
    CAS #l #lr #vw orf or ow @ tid; Ec
  {{{ b e (gen : nat) (v' : lit) Vr V'' mo' omo' eV eV', RET #b;
      let E' := E ++ [eV'] in
      let e' := length E in
      let M' := {[e']} ∪ M in
      ⌜ (* read message *) omo_write_op omo !! gen = Some e ∧ loc_event_msg eV.(type) = (#v', Vr)
      ∧ (* pre-view ⊑ post-view *) V ⊑ V'' ⌝ ∗
      OmoUB γe M e ∗
      OmoEinfo γe e eV ∗
      OmoEinfo γe e' eV' ∗
      OmoAuth γe γs (1/2)%Qp E' omo' mo' _ ∗
      ⊒V'' ∗ @{V''} OmoEview γe M' ∗
      ( (⌜b = false ∧ lit_neq lr v' ∧ mo' = mo
        ∧ omo' = omo_insert_r omo gen e'
        ∧ eV'.(type) = ReadE (#v', Vr)
        ∧ eV'.(sync) = V'' ⌝
        ∧ (if decide (AcqRel ⊑ orf) then ⌜Vr ⊑ V''⌝ else ▽{tid} ⊒Vr)
        ∗ @{Vb ⊔ V''} append_only_loc l γe uf ty
        ∗ OmoEq γe e e'
        ∗ OmoTokenR γe e')
      ∨ (⌜b = true ∧ v' = lr ∧ gen = (length omo - 1)%nat⌝
          ∧ ∃ Vw,
              ⌜ mo' = mo ++ [(e', (#vw, Vw))]
              ∧ omo' = omo_append_w omo e' []
              ∧ eV'.(type) = UpdateE e (#vw, Vw)
              ∧ eV'.(sync) = V''
              (* release sequence: Vwrite includes Vread *)
              ∧ Vr ⊑ Vw ∧ Vr ≠ Vw
              ∧ (¬ V'' ⊑ Vr)
              ∧ V ≠ V''
              ∧ ( if decide (AcqRel ⊑ ow) then
                    ( if decide (AcqRel ⊑ or) then
                        (* release-acquire CAS *) Vw = V''
                      else (* release CAS *) V'' ⊑ Vw )
                  else (* relaxed write CAS *) Vrel ⊑ Vw )⌝
              ∧ (if decide (AcqRel ⊑ ow) then @{Vw} OmoEview γe M' else emp)
              (* If current type is swriter, then we need exclusive permission to perform write *)
              ∗ (match ty with
                | cas_only => @{Vb ⊔ V''} append_only_loc l γe uf ty
                | swriter => ∀ es Vs, @{Vs} swriter_token l γe es ==∗ @{Vs ⊔ V''} swriter_token l γe (omo_write_op omo') ∗ @{Vb ⊔ V''} append_only_loc l γe uf ty
                end)
              ∗ (if decide (AcqRel ⊑ or) then ⌜Vw ⊑ V''⌝ else ▽{tid} ⊒Vw)
              ∗ OmoTokenW γe e')) }}}.
Proof.
  iIntros "%ORD1 %ORD2 %ORD3 %INCL1 %INCL2 %NEqvw" (Φ) "(M● & #⊒M & omo↦ & #⊒V & F) Post".
  wp_apply (append_only_loc_cas_general with "[$M● $⊒M $omo↦ $⊒V $F]"); try done.
Qed.

Lemma append_only_loc_cas_only_cas_live_loc l γe γs mo E omo M uf orf or ow (lr : loc) (vw : lit) tid (Vrel : view) V Vb (Ec : coPset) :
  Relaxed ⊑ orf → Relaxed ⊑ or → Relaxed ⊑ ow →
  ↑histN ⊆ Ec → #lr ∉ uf → vw ≠ ☠%V →
  {{{ OmoAuth γe γs (1/2)%Qp E omo mo _ ∗ OmoEview γe M ∗
      @{Vb} append_only_loc l γe uf cas_only ∗ ⊒V ∗
      (if decide (AcqRel ⊑ ow) then True else △{tid} ⊒Vrel) }}}
    CAS #l #lr #vw orf or ow @ tid; Ec
  {{{ b e (gen : nat) (v' : lit) Vr V'' mo' omo' eV eV', RET #b;
      let E' := E ++ [eV'] in
      let e' := length E in
      let M' := {[e']} ∪ M in
      ⌜ (* read message *) omo_write_op omo !! gen = Some e ∧ loc_event_msg eV.(type) = (#v', Vr)
      ∧ (* pre-view ⊑ post-view *) V ⊑ V'' ⌝ ∗
      OmoUB γe M e ∗
      OmoEinfo γe e eV ∗
      OmoEinfo γe e' eV' ∗
      OmoAuth γe γs (1/2)%Qp E' omo' mo' _ ∗
      ⊒V'' ∗ @{V''} OmoEview γe M' ∗ @{Vb ⊔ V''} append_only_loc l γe uf cas_only ∗
      ( (⌜b = false ∧ lit_neq lr v' ∧ mo' = mo
        ∧ omo' = omo_insert_r omo gen e'
        ∧ eV'.(type) = ReadE (#v', Vr)
        ∧ eV'.(sync) = V'' ⌝
        ∧ (if decide (AcqRel ⊑ orf) then ⌜Vr ⊑ V''⌝ else ▽{tid} ⊒Vr)
        ∗ OmoEq γe e e'
        ∗ OmoTokenR γe e')
      ∨ (⌜b = true ∧ v' = lr ∧ gen = (length omo - 1)%nat⌝
          ∧ ∃ Vw,
              ⌜ mo' = mo ++ [(e', (#vw, Vw))]
              ∧ omo' = omo_append_w omo e' []
              ∧ eV'.(type) = UpdateE e (#vw, Vw)
              ∧ eV'.(sync) = V''
              (* release sequence: Vwrite includes Vread *)
              ∧ Vr ⊑ Vw ∧ Vr ≠ Vw
              ∧ (¬ V'' ⊑ Vr)
              ∧ V ≠ V''
              ∧ ( if decide (AcqRel ⊑ ow) then
                    ( if decide (AcqRel ⊑ or) then
                        (* release-acquire CAS *) Vw = V''
                      else (* release CAS *) V'' ⊑ Vw )
                  else (* relaxed write CAS *) Vrel ⊑ Vw )⌝
              ∧ (if decide (AcqRel ⊑ ow) then @{Vw} OmoEview γe M' else emp)
              ∗ (if decide (AcqRel ⊑ or) then ⌜Vw ⊑ V''⌝ else ▽{tid} ⊒Vw)
              ∗ OmoTokenW γe e')) }}}.
Proof.
  iIntros "%ORD1 %ORD2 %ORD3 %INCL1 %INCL2 %NEqvw" (Φ) "(M● & #⊒M & omo↦ & #⊒V & F) Post".
  wp_apply (append_only_loc_cas_only_cas with "[$M● $⊒M $omo↦ $⊒V $F]"); try done.
Qed.

Lemma append_only_loc_swriter_cas_live_loc l γe γs mo E omo es M uf orf or ow (lr : loc) (vw : lit) tid (Vrel : view) V Vb Vc (Ec : coPset) :
  Relaxed ⊑ orf → Relaxed ⊑ or → Relaxed ⊑ ow →
  ↑histN ⊆ Ec → #lr ∉ uf → vw ≠ ☠%V →
  {{{ OmoAuth γe γs (1/2)%Qp E omo mo _ ∗ OmoEview γe M ∗
      @{Vb} append_only_loc l γe uf swriter ∗ @{Vc} swriter_token l γe es ∗ ⊒V ∗
      (if decide (AcqRel ⊑ ow) then True else △{tid} ⊒Vrel) }}}
    CAS #l #lr #vw orf or ow @ tid; Ec
  {{{ b e (gen : nat) (v' : lit) Vr V'' mo' es' omo' eV eV', RET #b;
      let E' := E ++ [eV'] in
      let e' := length E in
      let M' := {[e']} ∪ M in
      ⌜ (* read message *) omo_write_op omo !! gen = Some e ∧ loc_event_msg eV.(type) = (#v', Vr)
      ∧ (* pre-view ⊑ post-view *) V ⊑ V'' ⌝ ∗
      OmoUB γe M e ∗
      OmoEinfo γe e eV ∗
      OmoEinfo γe e' eV' ∗
      OmoAuth γe γs (1/2)%Qp E' omo' mo' _ ∗
      ⊒V'' ∗ @{V''} OmoEview γe M' ∗
      @{Vb ⊔ V''} append_only_loc l γe uf swriter ∗
      ( (⌜b = false ∧ lit_neq lr v' ∧ mo' = mo ∧ es' = es
        ∧ omo' = omo_insert_r omo gen e'
        ∧ eV'.(type) = ReadE (#v', Vr)
        ∧ eV'.(sync) = V''⌝
        ∧ (if decide (AcqRel ⊑ orf) then ⌜Vr ⊑ V''⌝ else ▽{tid} ⊒Vr)
        ∗ @{Vc} swriter_token l γe es'
        ∗ OmoEq γe e e'
        ∗ OmoTokenR γe e')
      ∨ (⌜b = true ∧ v' = lr ∧ gen = (length omo - 1)%nat⌝
          ∧ ∃ Vw,
              ⌜ mo' = mo ++ [(e', (#vw, Vw))] ∧ es' = es ++ [e']
              ∧ omo' = omo_append_w omo e' []
              ∧ eV'.(type) = UpdateE e (#vw, Vw)
              ∧ eV'.(sync) = V''
              (* release sequence: Vwrite includes Vread *)
              ∧ Vr ⊑ Vw ∧ Vr ≠ Vw
              ∧ (¬ V'' ⊑ Vr)
              ∧ V ≠ V''
              ∧ ( if decide (AcqRel ⊑ ow) then
                    ( if decide (AcqRel ⊑ or) then
                        (* release-acquire CAS *) Vw = V''
                      else (* release CAS *) V'' ⊑ Vw )
                  else (* relaxed write CAS *) Vrel ⊑ Vw )⌝
              ∧ (if decide (AcqRel ⊑ ow) then @{Vw} OmoEview γe M' else emp)
              ∗ (if decide (AcqRel ⊑ or) then ⌜Vw ⊑ V''⌝ else ▽{tid} ⊒Vw)
              ∗ @{Vc ⊔ V''} swriter_token l γe es'
              ∗ OmoTokenW γe e')) }}}.
Proof.
  iIntros "%ORD1 %ORD2 %ORD3 %INCL1 %INCL2 %NEqvw" (Φ) "(M● & #⊒M & omo↦ & SW & #⊒V & F) Post".
  wp_apply (append_only_loc_swriter_cas with "[$M● $⊒M $omo↦ $⊒V $SW $F]"); try done.
Qed.

Lemma append_only_loc_cas_live_loc_fail l γe γs mo E omo M uf ty orf or ow (lr : loc) (vw : val) tid (Vrel : view) V Vb (Ec : coPset) :
  Relaxed ⊑ orf → Relaxed ⊑ or → Relaxed ⊑ ow →
  ↑histN ⊆ Ec → #lr ∉ uf →
  {{{ OmoAuth γe γs (1/2)%Qp E omo mo _ ∗ OmoEview γe M ∗
      @{Vb} append_only_loc l γe uf ty ∗ ⊒V ∗
      (if decide (AcqRel ⊑ ow) then True else △{tid} ⊒Vrel) ∗
      append_only_loc_cas_latest_neq γe omo lr }}}
    CAS #l #lr vw orf or ow @ tid; Ec
  {{{ e (gen : nat) (v' : lit) Vr V'' omo' eV eV', RET #false;
      let E' := E ++ [eV'] in
      let e' := length E in
      let M' := {[e']} ∪ M in
      ⌜ (* read message *) omo_write_op omo !! gen = Some e ∧ loc_event_msg eV.(type) = (#v', Vr)
      ∧ (* pre-view ⊑ post-view *) V ⊑ V'' ⌝ ∗
      OmoUB γe M e ∗
      OmoEinfo γe e eV ∗
      OmoEinfo γe e' eV' ∗
      OmoEq γe e e' ∗
      OmoAuth γe γs (1/2)%Qp E' omo' mo _ ∗
      OmoTokenR γe e' ∗
      ⊒V'' ∗ @{V''} OmoEview γe M' ∗
      @{Vb ⊔ V''} (append_only_loc l γe uf ty) ∗
      (if decide (AcqRel ⊑ orf) then ⌜Vr ⊑ V''⌝ else ▽{tid} ⊒Vr) ∗
      ⌜ lit_neq lr v'
      ∧ omo' = omo_insert_r omo gen e'
      ∧ eV'.(type) = ReadE (#v', Vr)
      ∧ eV'.(sync) = V''⌝ }}}.
Proof.
  iIntros "%ORD1 %ORD2 %ORD3 %INCL1 %INCL2" (Φ) "(M● & #⊒M & omo↦ & #⊒V & F) Post".
  wp_apply (append_only_loc_cas_fail with "[$M● $⊒M $omo↦ $⊒V $F]"); try done.
Qed.

End append_only_loc.
