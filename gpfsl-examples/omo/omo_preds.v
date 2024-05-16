From gpfsl.examples Require Import sflib.

From iris.algebra Require Import auth gset gmap agree.
From iris.algebra Require Import lib.mono_list.
From iris.proofmode Require Import tactics.
From iris.bi Require Import fractional.
From iris.base_logic.lib Require Import ghost_var ghost_map.

From gpfsl.base_logic Require Import meta_data.
From gpfsl.examples.algebra Require Import mono_list.
From gpfsl.logic Require Import logatom atomics invariants.

From gpfsl.logic Require Import repeat_loop new_delete.
From gpfsl.examples Require Import map_seq loc_helper.

From stdpp Require Import namespaces.
From gpfsl.logic Require Import logatom.
From gpfsl.examples.omo Require Import omo omo_event omo_history.

Require Import iris.prelude.options.

Ltac encode_agree Hγ :=
  match type of Hγ with
  | ?γ = ?e =>
      match goal with
      | H1 : ?γ = ?e, H2 : ?γ = _ |- _ =>
          rewrite H1 in H2; apply (inj encode) in H2;
          first [ injection H2 as [= <- <- <- <- <- <- <- <- <- <- <-]
                | injection H2 as [= <- <- <- <- <- <- <- <- <- <-]
                | injection H2 as [= <- <- <- <- <- <- <- <- <-]
                | injection H2 as [= <- <- <- <- <- <- <- <-]
                | injection H2 as [= <- <- <- <- <- <- <-]
                | injection H2 as [= <- <- <- <- <- <-]
                | injection H2 as [= <- <- <- <- <-]
                | injection H2 as [= <- <- <- <-]
                | injection H2 as [= <- <- <-]
                | injection H2 as [= <- <-] ]
      end
  end.

(** Ghost construction for OMO.
    `omoGeneralG` is for library-unspecific predicates,
    and `omoSpecificG` is for library-specific predicates.

    Usage: In order to prove a library L by composing several libraries L1, L2, ..., Ln,
           assume the following in the proof context:
           1. single `omoGeneralG`
           2. multiple `omoSpecificG`'s, each of which corresponds to L, L1, L2, ..., Ln. *)
Class omoGeneralG Σ := OmoGeneralG {
  mono_ELG :> mono_listG (gname * option gname * view * eView * Qp * gname) Σ;
  mono_WLG :> mono_listG (event_id * gname * Qp) Σ;
  mono_RLG :> mono_listG event_id Σ;
  mono_GLG :> mono_listG (gname * event_id) Σ;
  tok_typeG :> inG Σ (agreeR boolO);
  mono_gmapG :> ghost_mapG Σ event_id nat;
  gen_gmapG :> ghost_mapG Σ Qp nat;
  agree_gnameG :> inG Σ (agreeR gnameO);
}.

Class omoSpecificG Σ (eventT absStateT : Type) := OmoSpecificG {
  mono_TLG :> mono_listG eventT Σ;
  mono_SLG :> mono_listG absStateT Σ;
  mono_EG :> mono_listG (omo_event eventT) Σ;
  agree_gvarG :> ghost_varG Σ (gname * history eventT * omoT * list absStateT);
}.

Definition omoGeneralΣ : gFunctors :=
  #[mono_listΣ (gname * option gname * view * eView * Qp * gname);
    mono_listΣ (event_id * gname * Qp);
    mono_listΣ event_id;
    mono_listΣ (gname * event_id);
    GFunctor (agreeR boolO);
    ghost_mapΣ event_id nat;
    ghost_mapΣ Qp nat;
    GFunctor (agreeR gnameO)].

Definition omoSpecificΣ (eventT absStateT : Type) : gFunctors :=
  #[mono_listΣ eventT;
    mono_listΣ absStateT;
    mono_listΣ (omo_event eventT);
    ghost_varΣ (gname * history eventT * omoT * list absStateT)].

Global Instance subG_omoGeneralΣ {Σ} : subG omoGeneralΣ Σ → omoGeneralG Σ.
Proof. solve_inG. Qed.

Global Instance subG_omoSpecificΣ {Σ} eventT absStateT : subG (omoSpecificΣ eventT absStateT) Σ → omoSpecificG Σ eventT absStateT.
Proof. solve_inG. Qed.

(** Definitions of library-unspecific predicates **)
Section omo_general_def.
Context {Σ : gFunctors} `{!omoGeneralG Σ}.

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

Local Open Scope nat_scope.

(* Persistent assertion that gen of `e1` < gen of `e2`. *)
Definition OmoLt_def (γe : gname) (e1 e2 : event_id) : vProp :=
  ∃ γtl γel γh γg γn einfo1 einfo2,
    ⌜ γe = encode (γtl,γel,γh,γg,γn) ∧ (einfo1.1.2 < einfo2.1.2)%Qp ⌝ ∗

    ⎡mono_list_idx_own γel e1 einfo1⎤ ∗
    ⎡mono_list_idx_own γel e2 einfo2⎤.
Definition OmoLt_aux : seal (@OmoLt_def). Proof. by eexists. Qed.
Definition OmoLt := unseal (@OmoLt_aux).
Definition OmoLt_eq : @OmoLt = _ := seal_eq _.

(* Persistent assertion that gen of `e1` ≤ gen of `e2` *)
Definition OmoLe_def (γe : gname) (e1 e2 : event_id) : vProp :=
  ∃ γtl γel γh γg γn einfo1 einfo2,
    ⌜ γe = encode (γtl,γel,γh,γg,γn) ∧ (einfo1.1.2 ≤ einfo2.1.2)%Qp ⌝ ∗

    ⎡mono_list_idx_own γel e1 einfo1⎤ ∗
    ⎡mono_list_idx_own γel e2 einfo2⎤.
Definition OmoLe_aux : seal (@OmoLe_def). Proof. by eexists. Qed.
Definition OmoLe := unseal (@OmoLe_aux).
Definition OmoLe_eq : @OmoLe = _ := seal_eq _.

(* Persistent assertion that gen of `e1` = gen of `e2` *)
Definition OmoEq_def (γe : gname) (e1 e2 : event_id) : vProp :=
  ∃ γtl γel γh γg γn einfo1 einfo2,
    ⌜ γe = encode (γtl,γel,γh,γg,γn) ∧ (einfo1.1.2 = einfo2.1.2)%Qp ⌝ ∗

    ⎡mono_list_idx_own γel e1 einfo1⎤ ∗
    ⎡mono_list_idx_own γel e2 einfo2⎤.
Definition OmoEq_aux : seal (@OmoEq_def). Proof. by eexists. Qed.
Definition OmoEq := unseal (@OmoEq_aux).
Definition OmoEq_eq : @OmoEq = _ := seal_eq _.

(* Persistent assertion that `e'` happens-before `e` *)
Definition OmoHb_def (γe γe' : gname) (e e' : event_id) : vProp :=
  ∃ γtl γel γh γg γn γtl' γel' γh' γg' γn' einfo einfo' GL,
    ⌜ γe = encode (γtl,γel,γh,γg,γn) ∧ γe' = encode (γtl',γel',γh',γg',γn') ∧ (γe', e') ∈ GL ∧ einfo'.1.1.1.2 ⊑ einfo.1.1.1.2 ⌝ ∗

    ⎡mono_list_idx_own γel e einfo⎤ ∗ ⎡mono_list_idx_own γel' e' einfo'⎤ ∗
    ⎡mono_list_lb_own einfo.2 GL⎤.
Definition OmoHb_aux : seal (@OmoHb_def). Proof. by eexists. Qed.
Definition OmoHb := unseal (@OmoHb_aux).
Definition OmoHb_eq : @OmoHb = _ := seal_eq _.

(* `OmoHb` for set of events *)
Definition OmoHbs_def (γe γe' : gname) (e : event_id) (M : eView) : vProp :=
  [∗ set] e' ∈ M, OmoHb γe γe' e e'.
Definition OmoHbs_aux : seal (@OmoHbs_def). Proof. by eexists. Qed.
Definition OmoHbs := unseal (@OmoHbs_aux).
Definition OmoHbs_eq : @OmoHbs = _ := seal_eq _.

(* `gen` is an upper bound of generation of each element in `M` *)
Definition OmoUBgen (omo : omoT) M gen : Prop :=
  ∀ e, e ∈ M → ∃ eidx, lookup_omo omo eidx = Some e ∧ (gen_of eidx ≤ gen)%nat.

(* generation of `e` is an upper bound of generation of each element in `M` *)
Definition OmoUB γe M e : vProp :=
  [∗ set] e' ∈ M, OmoLe γe e' e.

(* Commit-with relation from `e` to `e'` *)
Definition OmoCW_def (γe γe' : gname) (e e' : event_id) : vProp :=
  ∃ γtl γel γh γg γn γtl' γel' γh' γg' γn' einfo einfo' γgl γb,
    ⌜ γe = encode (γtl,γel,γh,γg,γn) ∧ γe' = encode (γtl',γel',γh',γg',γn') ⌝ ∗

    ⎡mono_list_idx_own γel e einfo⎤ ∗
    ⎡mono_list_idx_own γel' e' einfo'⎤ ∗
    ⎡mono_list_idx_own γgl 0 (γe',e') ⎤ ∗
    ⎡mono_list_idx_own γgl 1 (γe,e) ⎤ ∗

    ⌜ einfo.1.1.1.1.2 = Some γgl ∧ einfo'.1.1.1.1.1 = encode (γgl,γb) ⌝.
Definition OmoCW_aux : seal (@OmoCW_def). Proof. by eexists. Qed.
Definition OmoCW := unseal (@OmoCW_aux).
Definition OmoCW_eq : @OmoCW = _ := seal_eq _.

(* Monotonicity of commit-with relations for all relations with starting event e ∈ M *)
Definition CWMono_def (γe γe' γm : gname) M : vProp :=
  ⎡ghost_map_auth γm 1 (gset_to_gmap 0%nat M)⎤ ∗
  ([∗ set] e ∈ M, ∃ e', ⎡e ↪[γm]□ 0%nat⎤ ∗ OmoCW γe γe' e e') ∗
  □ (∀ e1 e2 e1' e2', ⌜ e1 ∈ M ∧ e2 ∈ M ⌝ -∗
    OmoCW γe γe' e1 e1' -∗ OmoCW γe γe' e2 e2' -∗ OmoLe γe' e1' e2' -∗ OmoLe γe e1 e2).
Definition CWMono_aux : seal (@CWMono_def). Proof. by eexists. Qed.
Definition CWMono := unseal (@CWMono_aux).
Definition CWMono_eq : @CWMono = _ := seal_eq _.

(* Persistent snapshot of e ∈ M where M is the one in CWMono *)
Definition CWMonoValid_def γm (e : event_id) : vProp :=
  ⎡e ↪[γm]□ 0%nat⎤.
Definition CWMonoValid_aux : seal (@CWMonoValid_def). Proof. by eexists. Qed.
Definition CWMonoValid := unseal (@CWMonoValid_aux).
Definition CWMonoValid_eq : @CWMonoValid = _ := seal_eq _.

(* Persistent assertion that ∀ e e' ∈ M, OmoHb e e' -∗ ⌜ e' ∈ M ⌝ *)
Definition HbIncluded_def (γe γe' : gname) (M M' : eView) : vProp :=
  ∃ γtl γel γh γg γn,
    ⌜ γe = encode (γtl,γel,γh,γg,γn) ⌝ ∗
    [∗ set] e ∈ M,
      ∃ einfo q GL,
        ⎡mono_list_idx_own γel e einfo⎤ ∗
        ⎡mono_list_auth_own einfo.2 q GL⎤ ∗
        ⌜ (∀ e', (γe', e') ∈ GL → e' ∈ M') ⌝.
Definition HbIncluded_aux : seal (@HbIncluded_def). Proof. by eexists. Qed.
Definition HbIncluded := unseal (@HbIncluded_aux).
Definition HbIncluded_eq : @HbIncluded = _ := seal_eq _.

(* Local observation of events, not objective *)
Definition OmoEview_def (γe : gname) (M : eView) : vProp :=
  ∃ γtl γel γh γg γn,
    ⌜ γe = encode (γtl,γel,γh,γg,γn) ∧ M ≠ ∅ ⌝ ∗
    [∗ set] e ∈ M,
      ∃ einfo,
        ⎡mono_list_idx_own γel e einfo⎤ ∗
        ⊒(einfo.1.1.1.2).
Definition OmoEview_aux : seal (@OmoEview_def). Proof. by eexists. Qed.
Definition OmoEview := unseal (@OmoEview_aux).
Definition OmoEview_eq : @OmoEview = _ := seal_eq _.

(* Persistent snapshot of `omo` *)
Definition OmoSnapOmo_def (γe γs : gname) (omo : omoT) : vProp :=
  ∃ γtl γel γh γg γn γwl γsl γq WL,
    ⌜ γe = encode (γtl,γel,γh,γg,γn) ∧ γs = encode (γwl,γsl,γq) ⌝ ∗
    ⎡mono_list_lb_own γwl WL⎤ ∗
    ([∗ list] ees; winfo ∈ omo; WL,
      ∃ e es γrl einfo,
        ⌜ ees = (e, es) ∧ winfo = (e, γrl, einfo.1.2) ⌝ ∗
        ⎡mono_list_lb_own γrl es⎤ ∗
        ⎡mono_list_idx_own γel e einfo⎤ ∗
        [∗ list] e' ∈ es,
          ∃ einfo',
          ⎡mono_list_idx_own γel e' einfo'⎤ ∗
          ⌜ einfo'.1.2 = einfo.1.2 ⌝) ∗
    [∗ list] i↦winfo ∈ WL, ⎡winfo.2 ↪[γq]□ i⎤.
Definition OmoSnapOmo_aux : seal (@OmoSnapOmo_def). Proof. by eexists. Qed.
Definition OmoSnapOmo := unseal (@OmoSnapOmo_aux).
Definition OmoSnapOmo_eq : @OmoSnapOmo = _ := seal_eq _.

(* Token for producing read-only events *)
Definition OmoTokenR_def (γe : gname) (e : event_id) : vProp :=
  ∃ γtl γel γh γg γn einfo γgl γb,
    ⌜ γe = encode (γtl,γel,γh,γg,γn) ∧ einfo.1.1.1.1.1 = encode (γgl, γb) ⌝ ∗
    ⎡mono_list_idx_own γel e einfo⎤ ∗
    ⎡mono_list_auth_own γgl 1 [(γe, e)]⎤ ∗
    ⎡own γb (to_agree false)⎤.
Definition OmoTokenR_aux : seal (@OmoTokenR_def). Proof. by eexists. Qed.
Definition OmoTokenR := unseal (@OmoTokenR_aux).
Definition OmoTokenR_eq : @OmoTokenR = _ := seal_eq _.

(* Token for producing write events *)
Definition OmoTokenW_def (γe : gname) (e : event_id) : vProp :=
  ∃ γtl γel γh γg γn einfo γgl γb,
    ⌜ γe = encode (γtl,γel,γh,γg,γn) ∧ einfo.1.1.1.1.1 = encode (γgl, γb) ⌝ ∗
    ⎡mono_list_idx_own γel e einfo⎤ ∗
    ⎡mono_list_auth_own γgl 1 [(γe,e)]⎤ ∗
    ⎡own γb (to_agree true)⎤.
Definition OmoTokenW_aux : seal (@OmoTokenW_def). Proof. by eexists. Qed.
Definition OmoTokenW := unseal (@OmoTokenW_aux).
Definition OmoTokenW_eq : @OmoTokenW = _ := seal_eq _.

(* Auxilliary predicate for persistently remembering `γx` for `γe` *)
Definition OmoGname_def (γe γx : gname) : vProp :=
  ∃ γtl γel γh γg γn,
    ⌜ γe = encode (γtl,γel,γh,γg,γn) ⌝ ∗ ⎡own γn (to_agree γx)⎤.
Definition OmoGname_aux : seal (@OmoGname_def). Proof. by eexists. Qed.
Definition OmoGname := unseal (@OmoGname_aux).
Definition OmoGname_eq : @OmoGname = _ := seal_eq _.

Global Instance OmoLt_persistent γe e1 e2 : Persistent (OmoLt γe e1 e2).
Proof. rewrite OmoLt_eq. apply _. Qed.
Global Instance OmoLt_timeless γe e1 e2 : Timeless (OmoLt γe e1 e2).
Proof. rewrite OmoLt_eq. apply _. Qed.
Global Instance OmoLt_objective γe e1 e2 : Objective (OmoLt γe e1 e2).
Proof. rewrite OmoLt_eq. apply _. Qed.
Global Instance OmoLe_persistent γe e1 e2 : Persistent (OmoLe γe e1 e2).
Proof. rewrite OmoLe_eq. apply _. Qed.
Global Instance OmoLe_timeless γe e1 e2 : Timeless (OmoLe γe e1 e2).
Proof. rewrite OmoLe_eq. apply _. Qed.
Global Instance OmoLe_objective γe e1 e2 : Objective (OmoLe γe e1 e2).
Proof. rewrite OmoLe_eq. apply _. Qed.
Global Instance OmoEq_persistent γe e1 e2 : Persistent (OmoEq γe e1 e2).
Proof. rewrite OmoEq_eq. apply _. Qed.
Global Instance OmoEq_timeless γe e1 e2 : Timeless (OmoEq γe e1 e2).
Proof. rewrite OmoEq_eq. apply _. Qed.
Global Instance OmoEq_objective γe e1 e2 : Objective (OmoEq γe e1 e2).
Proof. rewrite OmoEq_eq. apply _. Qed.
Global Instance OmoHb_persistent γe γe' e e' : Persistent (OmoHb γe γe' e e').
Proof. rewrite OmoHb_eq. apply _. Qed.
Global Instance OmoHb_timeless γe γe' e e' : Timeless (OmoHb γe γe' e e').
Proof. rewrite OmoHb_eq. apply _. Qed.
Global Instance OmoHb_objective γe γe' e e' : Objective (OmoHb γe γe' e e').
Proof. rewrite OmoHb_eq. apply _. Qed.
Global Instance OmoHbs_persistent γe γe' e M : Persistent (OmoHbs γe γe' e M).
Proof. rewrite OmoHbs_eq. apply _. Qed.
Global Instance OmoHbs_timeless γe γe' e M : Timeless (OmoHbs γe γe' e M).
Proof. rewrite OmoHbs_eq. apply _. Qed.
Global Instance OmoHbs_objective γe γe' e M : Objective (OmoHbs γe γe' e M).
Proof. rewrite OmoHbs_eq. apply _. Qed.
Global Instance OmoUB_persistent γe M e : Persistent (OmoUB γe M e) := _.
Global Instance OmoUB_timeless γe M e : Timeless (OmoUB γe M e) := _.
Global Instance OmoUB_objective γe M e : Objective (OmoUB γe M e) := _.
Global Instance OmoCW_persistent γe γe' e e' : Persistent (OmoCW γe γe' e e').
Proof. rewrite OmoCW_eq. apply _. Qed.
Global Instance OmoCW_timeless γe γe' e e' : Timeless (OmoCW γe γe' e e').
Proof. rewrite OmoCW_eq. apply _. Qed.
Global Instance OmoCW_objective γe γe' e e' : Objective (OmoCW γe γe' e e').
Proof. rewrite OmoCW_eq. apply _. Qed.
Global Instance CWMono_timeless γe γe' γm M : Timeless (CWMono γe γe' γm M).
Proof. rewrite CWMono_eq. apply _. Qed.
Global Instance CWMono_objective γe γe' γm M : Objective (CWMono γe γe' γm M).
Proof. rewrite CWMono_eq. apply _. Qed.
Global Instance CWMonoValid_persistent γm e : Persistent (CWMonoValid γm e).
Proof. rewrite CWMonoValid_eq. apply _. Qed.
Global Instance CWMonoValid_timeless γm e : Timeless (CWMonoValid γm e).
Proof. rewrite CWMonoValid_eq. apply _. Qed.
Global Instance CWMonoValid_objective γm e : Objective (CWMonoValid γm e).
Proof. rewrite CWMonoValid_eq. apply _. Qed.
Global Instance HbIncluded_timeless γe γe' M M' : Timeless (HbIncluded γe γe' M M').
Proof. rewrite HbIncluded_eq. apply _. Qed.
Global Instance HbIncluded_objective γe γe' M M' : Objective (HbIncluded γe γe' M M').
Proof. rewrite HbIncluded_eq. apply _. Qed.
Global Instance OmoEview_persistent γe M : Persistent (OmoEview γe M).
Proof. rewrite OmoEview_eq. apply _. Qed.
Global Instance OmoEview_timeless γe M : Timeless (OmoEview γe M).
Proof. rewrite OmoEview_eq. apply _. Qed.
Global Instance OmoSnapOmo_persistent γe γs omo : Persistent (OmoSnapOmo γe γs omo ).
Proof. rewrite OmoSnapOmo_eq. apply _. Qed.
Global Instance OmoSnapOmo_timeless γe γs omo : Timeless (OmoSnapOmo γe γs omo).
Proof. rewrite OmoSnapOmo_eq. apply _. Qed.
Global Instance OmoSnapOmo_objective γe γs omo : Objective (OmoSnapOmo γe γs omo).
Proof. rewrite OmoSnapOmo_eq. apply _. Qed.
Global Instance OmoTokenR_objective γe e : Objective (OmoTokenR γe e).
Proof. rewrite OmoTokenR_eq. apply _. Qed.
Global Instance OmoTokenR_timeless γe e : Timeless (OmoTokenR γe e).
Proof. rewrite OmoTokenR_eq. apply _. Qed.
Global Instance OmoTokenW_objective γe e : Objective (OmoTokenW γe e).
Proof. rewrite OmoTokenW_eq. apply _. Qed.
Global Instance OmoTokenW_timeless γe e : Timeless (OmoTokenW γe e).
Proof. rewrite OmoTokenW_eq. apply _. Qed.
Global Instance OmoGname_persistent γe γx : Persistent (OmoGname γe γx).
Proof. rewrite OmoGname_eq. apply _. Qed.
Global Instance OmoGname_timeless γe γx : Timeless (OmoGname γe γx).
Proof. rewrite OmoGname_eq. apply _. Qed.
Global Instance OmoGname_objective γe γx : Objective (OmoGname γe γx).
Proof. rewrite OmoGname_eq. apply _. Qed.

End omo_general_def.

(** Definitions of library-specific predicates **)
Section omo_specific_def.
Context {eventT absStateT : Type}.
Context {Σ : gFunctors} `{!omoGeneralG Σ, !omoSpecificG Σ eventT absStateT}.

Notation history := (history eventT).
Notation iProp := (iProp Σ).
Notation vProp := (vProp Σ).

Implicit Types
  (γe γs γtl γel γh γg γwl γrl γgl γsl γq γb γm γn : gname)
  (q qg : Qp)
  (E : history)
  (M : eView)
  (st : absStateT)
  (ty : eventT)
  (einfo : (gname * option gname * view * eView * Qp * gname))
  (TL : list eventT) (* mono_list for type of events *)
  (EL : list (gname * option gname * view * eView * Qp * gname)) (* mono_list for all event info excluding event type *)
  (WL : list (event_id * gname * Qp)) (* mono_list for γs *)
  (RL : list event_id) (* mono_list for each generation *)
  (GL : list (gname * event_id)) (* mono_list for commit-with relation or seen_event *)
  (SL : list absStateT)
  (QM : gmap Qp nat)
  (eidx : event_idx).

Local Open Scope nat_scope.

(** Persistent assertion that the resulting abstract state is `st`
    when we do interpretation until the occurrence of `e` in linearization order *)
(** Note that this assertion is indeed persistent.
    This is possible since `γs` part in `OmoAuth` will be changed when we perform `OmoAuth_insert`.
    This behavior models invalidation of old interpretation when we insert a new write event in the middle of the generation. *)
Definition OmoSnap_def (γe γs : gname) (e : event_id) (st : absStateT) : vProp :=
  ∃ γtl γel γh γg γn γwl γsl γq i einfo,
    ⌜ γe = encode (γtl,γel,γh,γg,γn) ∧ γs = encode (γwl,γsl,γq) ⌝ ∗

    ⎡mono_list_idx_own γel e einfo⎤ ∗
    ⎡einfo.1.2 ↪[γq]□ i⎤ ∗
    ⎡mono_list_idx_own γsl i st⎤.
Definition OmoSnap_aux : seal (@OmoSnap_def). Proof. by eexists. Qed.
Definition OmoSnap := unseal (@OmoSnap_aux).
Definition OmoSnap_eq : @OmoSnap = _ := seal_eq _.

(* Persistent knowledge of omo event `eV` corresponding to event id `e` *)
Definition OmoEinfo_def (γe : gname) (e : event_id) (eV : omo_event eventT) : vProp :=
  ∃ γtl γel γh γg γn ty einfo,
    ⌜ γe = encode (γtl,γel,γh,γg,γn) ∧ eV.(type) = ty ∧ eV.(sync) = einfo.1.1.1.2 ∧ eV.(eview) = einfo.1.1.2 ⌝ ∗

    ⎡mono_list_idx_own γtl e ty⎤ ∗
    ⎡mono_list_idx_own γel e einfo⎤ ∗
    ⎡mono_list_idx_own γh e eV⎤ ∗
    OmoUB γe ({[e]} ∪ eV.(eview)) e ∗
    @{eV.(sync)} OmoEview γe ({[e]} ∪ eV.(eview)).
Definition OmoEinfo_aux : seal (@OmoEinfo_def). Proof. by eexists. Qed.
Definition OmoEinfo := unseal (@OmoEinfo_aux).
Definition OmoEinfo_eq : @OmoEinfo = _ := seal_eq _.

(* ---- Definitions used internally by `OmoAuth` ---- *)
Definition OmoAuth_E_TL_valid E TL : Prop :=
  ∀ e eV ty,
    E !! e = Some eV →
    TL !! e = Some ty →
    eV.(type) = ty.

Definition OmoAuth_E_EL_valid E EL : Prop :=
  ∀ e eV einfo,
    E !! e = Some eV →
    EL !! e = Some einfo →
    eV.(sync) = einfo.1.1.1.2 ∧ eV.(eview) = einfo.1.1.2.

Definition OmoAuth_EL_seen_event_valid EL : vProp :=
  [∗ list] einfo ∈ EL,
    ∃ q GL,
      ⎡mono_list_auth_own einfo.2 q GL⎤ ∗
      [∗ list] geinfo ∈ GL,
        ∃ γe e γtl γel γh γg γn einfo',
          ⌜ geinfo = (γe, e) ∧ γe = encode(γtl,γel,γh,γg,γn) ∧ einfo'.1.1.1.2 ⊑ einfo.1.1.1.2 ⌝ ∗
          ⎡mono_list_idx_own γel e einfo'⎤.

Definition OmoAuth_WL_valid γs γel q omo WL : vProp :=
  [∗ list] ees; winfo ∈ omo; WL,
    ∃ e es γrl einfo,
      ⌜ ees = (e, es) ∧ winfo = (e, γrl, einfo.1.2) ⌝ ∗
      ⎡mono_list_auth_own γrl q es⎤ ∗
      ⎡mono_list_idx_own γel e einfo⎤ ∗
      [∗ list] e' ∈ es,
        ∃ einfo',
          ⎡mono_list_idx_own γel e' einfo'⎤ ∗
          ⌜ einfo'.1.2 = einfo.1.2 ⌝.

Definition OmoAuth_qg_mono WL : Prop :=
  ∀ n1 n2 winfo1 winfo2,
    WL !! n1 = Some winfo1 →
    WL !! n2 = Some winfo2 →
    (n1 < n2)%nat →
    (winfo1.2 < winfo2.2)%Qp.

Definition OmoAuth_all_elem γe (E : history) : vProp :=
  [∗ list] e↦eV ∈ E, OmoEinfo γe e eV.

Definition OmoAuth_QM_valid WL QM : Prop :=
  ∀ qg i, WL.*2 !! i = Some qg ↔ QM !! qg = Some i.

Definition OmoAuth_qg_keys γq QM : vProp :=
  [∗ map] q↦i ∈ QM, ⎡q ↪[γq]□ i⎤.

(* Main definition of `OmoAuth` predicate *)
Definition OmoAuth_def (γe γs : gname) (q : Qp) (E : history) (omo : omoT) (stlist : list absStateT) `{Interpretable eventT absStateT} : vProp :=
  ∃ γtl γel γh γg γn γwl γsl γq TL EL WL QM,
    ⌜ γe = encode (γtl,γel,γh,γg,γn) ∧ γs = encode (γwl,γsl,γq) ⌝ ∗

    ⎡mono_list_auth_own γtl q TL⎤ ∗
    ⎡mono_list_auth_own γel q EL⎤ ∗
    ⎡mono_list_auth_own γwl q WL⎤ ∗
    ⎡mono_list_auth_own γsl q stlist⎤ ∗
    ⎡ghost_map_auth γq q QM⎤ ∗
    ⎡mono_list_auth_own γh q E⎤ ∗
    ⎡ghost_var γg q (γs,E,omo,stlist)⎤∗

    OmoAuth_EL_seen_event_valid EL ∗
    OmoAuth_WL_valid γs γel q omo WL ∗
    OmoAuth_all_elem γe E ∗
    OmoAuth_qg_keys γq QM ∗

    ⌜ (length E = length TL)%nat
    ∧ (length E = length EL)%nat
    ∧ OmoAuth_E_TL_valid E TL
    ∧ OmoAuth_E_EL_valid E EL
    ∧ OmoAuth_qg_mono WL
    ∧ OmoAuth_QM_valid WL QM
    ∧ omo ≠ [] ∧ E ≠ []
    ∧ history_wf E
    ∧ lhb E (seq 0 (length E))
    ∧ Linearizability_omo E omo stlist ⌝.
Definition OmoAuth_aux : seal (@OmoAuth_def). Proof. by eexists. Qed.
Definition OmoAuth := unseal (@OmoAuth_aux).
Definition OmoAuth_eq : @OmoAuth = _ := seal_eq _.

(* Snapshot of history of all events ever committed *)
Definition OmoSnapHistory_def (γe : gname) (E : history) : vProp :=
  ∃ γtl γel γh γg γn TL EL,
    ⌜ γe = encode (γtl,γel,γh,γg,γn) ⌝ ∗

    ⎡mono_list_lb_own γtl TL⎤ ∗
    ⎡mono_list_lb_own γel EL⎤ ∗
    ⎡mono_list_lb_own γh E⎤ ∗

    ⌜ (length E = length TL)%nat
    ∧ (length E = length EL)%nat
    ∧ OmoAuth_E_TL_valid E TL
    ∧ OmoAuth_E_EL_valid E EL ⌝.
Definition OmoSnapHistory_aux : seal (@OmoSnapHistory_def). Proof. by eexists. Qed.
Definition OmoSnapHistory := unseal (@OmoSnapHistory_aux).
Definition OmoSnapHistory_eq : @OmoSnapHistory = _ := seal_eq _.

(* Snapshot of list of abstract state *)
Definition OmoSnapStates_def (γe γs : gname) (omo : omoT) (stlist : list absStateT) : vProp :=
  ∃ γwl γsl γq,
    ⌜ γs = encode (γwl,γsl,γq) ∧ length omo = length stlist ⌝ ∗
    ⎡mono_list_lb_own γsl stlist⎤ ∗
    OmoSnapOmo γe γs omo.
Definition OmoSnapStates_aux : seal (@OmoSnapStates_def). Proof. by eexists. Qed.
Definition OmoSnapStates := unseal (@OmoSnapStates_aux).
Definition OmoSnapStates_eq : @OmoSnapStates = _ := seal_eq _.

(** This is a special form of `OmoAuth` that allows us to register `OmoHb` relation.
    Whenever `OmoAuth` is updated or initialized, it turns into `OmoHbToken`.
    When registration of `OmoHb` relation is finished, use `OmoHbToken_finish` to return it to `OmoAuth`. *)
(** Detailed explanation for `OmoHbToken` and `OmoAuth`:

    < When initializing an invariant and creating `OmoAuth` resource >
    1. Create `OmoHbToken` resource by allocation rule of `OmoAuth`.
    2. Create any number of `OmoHb` relations (if needed).
    3. Turn `OmoHbToken` into `OmoAuth` by a rule `OmoHbToken_finish`.

    < When inserting a new event into `OmoAuth` and re-establish the invariant >
    1. Using a `OmoAuth` resource, perform an insertion rule (e.g. `OmoAuth_insert_ro`, `OmoAuth_insert_last`, `OmoAuth_insert`).
    2. Then, take `OmoHbToken` resource.
    3. Create any number of `OmoHb` relations (if needed).
    4. Turn `OmoHbToken` into `OmoAuth` by the rule `OmoHbToken_finish`.
*)
Definition OmoHbToken_def (γe γs : gname) (E : history) (omo : omoT) (stlist : list absStateT) (e : event_id)
  `{Interpretable eventT absStateT} : vProp :=
 ∃ γtl γel γh γg γn γwl γsl γq TL EL WL QM elast GL,
    ⌜ γe = encode (γtl,γel,γh,γg,γn) ∧ γs = encode (γwl,γsl,γq) ⌝ ∗

    ⎡mono_list_auth_own γtl 1 TL⎤ ∗
    ⎡mono_list_auth_own γel 1 EL⎤ ∗
    ⎡mono_list_auth_own γwl 1 WL⎤ ∗
    ⎡mono_list_auth_own γsl 1 stlist⎤ ∗
    ⎡ghost_map_auth γq 1 QM⎤ ∗
    ⎡mono_list_auth_own elast.2 1 GL⎤ ∗
    ⎡mono_list_auth_own γh 1 E⎤ ∗
    ⎡ghost_var γg 1 (γs,E,omo,stlist)⎤ ∗

    OmoAuth_EL_seen_event_valid (take (length EL - 1)%nat EL) ∗
    OmoAuth_WL_valid γs γel 1 omo WL ∗
    OmoAuth_all_elem γe E ∗
    OmoAuth_qg_keys γq QM ∗
    ([∗ list] geinfo ∈ GL,
        ∃ γe' e' γtl' γel' γh' γg' γn' einfo',
          ⌜ geinfo = (γe', e') ∧ γe' = encode (γtl',γel',γh',γg',γn') ∧ einfo'.1.1.1.2 ⊑ elast.1.1.1.2 ⌝ ∗
          ⎡mono_list_idx_own γel' e' einfo'⎤) ∗

    ⌜ (length E = length TL)%nat
    ∧ (length E = length EL)%nat
    ∧ (e = length EL - 1)%nat
    ∧ last EL = Some elast
    ∧ OmoAuth_E_TL_valid E TL
    ∧ OmoAuth_E_EL_valid E EL
    ∧ OmoAuth_qg_mono WL
    ∧ OmoAuth_QM_valid WL QM
    ∧ E ≠ [] ∧ omo ≠ []
    ∧ history_wf E
    ∧ hb_ord E (seq 0 (length E))
    ∧ Linearizability_omo E omo stlist ⌝.
Definition OmoHbToken_aux : seal (@OmoHbToken_def). Proof. by eexists. Qed.
Definition OmoHbToken := unseal (@OmoHbToken_aux).
Definition OmoHbToken_eq : @OmoHbToken = _ := seal_eq _.

Global Instance OmoSnap_persistent γe γs e st : Persistent (OmoSnap γe γs e st).
Proof. rewrite OmoSnap_eq. apply _. Qed.
Global Instance OmoSnap_timeless γe γs e st : Timeless (OmoSnap γe γs e st).
Proof. rewrite OmoSnap_eq. apply _. Qed.
Global Instance OmoSnap_objective γe γs e st : Objective (OmoSnap γe γs e st).
Proof. rewrite OmoSnap_eq. apply _. Qed.
Global Instance OmoEinfo_persistent γe e eV : Persistent (OmoEinfo γe e eV).
Proof. rewrite OmoEinfo_eq. apply _. Qed.
Global Instance OmoEinfo_timeless γe e eV : Timeless (OmoEinfo γe e eV).
Proof. rewrite OmoEinfo_eq. apply _. Qed.
Global Instance OmoEinfo_objective γe e eV : Objective (OmoEinfo γe e eV).
Proof. rewrite OmoEinfo_eq. apply _. Qed.
Global Instance OmoAuth_timeless γe γs q E omo stlist `{Interpretable eventT absStateT} :
  Timeless (OmoAuth γe γs q E omo stlist _).
Proof. rewrite OmoAuth_eq. apply _. Qed.
Global Instance OmoAuth_objective γe γs q E omo stlist `{Interpretable eventT absStateT} :
  Objective (OmoAuth γe γs q E omo stlist _).
Proof. rewrite OmoAuth_eq. apply _. Qed.
Global Instance OmoAuth_fractional γe γs E omo stlist `{Interpretable eventT absStateT} :
  Fractional (λ q, OmoAuth γe γs q E omo stlist _).
Proof.
  intros ??. rewrite OmoAuth_eq. iSplit.
  - iIntros "M●". iDestruct "M●" as (??????????)
      "(%&%& [%Hγe %Hγs] & [TL● TL●'] & [EL● EL●'] & [WL● WL●'] & [SL● SL●'] & [Hγq Hγq'] & [HL● HL●'] & [Hγg Hγg'] & EL✓ & WL✓ & #ELEMS & #KEYS & Pures)".
    iDestruct "Pures" as %(EQlenTL & EQlenEL & E_TL_VALID & E_EL_VALID & MONOqg & QM_VALID & Nomo & NE & HWF & LHB & OMO_GOOD).

    iAssert (OmoAuth_EL_seen_event_valid EL ∗ OmoAuth_EL_seen_event_valid EL)%I with "[EL✓]" as "[EL✓ EL✓']".
    { rewrite !/OmoAuth_EL_seen_event_valid. rewrite -big_sepL_sep. iApply (big_sepL_impl with "EL✓"). iModIntro.
      iIntros "%i %einfo %Heinfo H". iDestruct "H" as (??) "[[GL● GL●'] #BIG]".
      iSplitL "GL●"; repeat iExists _; iFrame "∗#". }

    iAssert (OmoAuth_WL_valid γs γel p omo WL ∗ OmoAuth_WL_valid γs γel q omo WL)%I with "[WL✓]" as "[WL✓ WL✓']".
    { rewrite !/OmoAuth_WL_valid. rewrite -big_sepL2_sep. iApply (big_sepL2_impl with "WL✓"). iModIntro.
      iIntros "%i %ees %winfo %Hi %Hwinfo H". destruct ees as [e es].
      iDestruct "H" as (????) "(%EQ & [RL● RL●'] & #EL & #BIG)". iSplitL "RL●"; repeat iExists _; iFrame "∗#%". }

    iSplitL "TL● EL● WL● SL● Hγq HL● Hγg EL✓ WL✓"; repeat iExists _; iFrame "∗#%"; done.
  - iIntros "[M● M●']". iDestruct "M●" as (??????????)
      "(%&%& [%Hγe %Hγs] & TL● & EL● & WL● & SL● & Hγq & HL● & Hγg & EL✓ & WL✓ & #ELEMS & #KEYS & Pures)".
    iDestruct "Pures" as %(EQlenTL & EQlenEL & E_TL_VALID & E_EL_VALID & MONOqg & QM_VALID & Nomo & NE & HWF & LHB & OMO_GOOD).
    iDestruct "M●'" as (??????????)
      "(%&%& [%Hγe' %Hγs'] & TL●' & EL●' & WL●' & SL●' & Hγq' & HL●' & Hγg' & EL✓' & WL✓' & #ELEMS' & #KEYS' & Pures)".
    iDestruct "Pures" as %(EQlenTL' & EQlenEL' & E_TL_VALID' & E_EL_VALID' & MONOqg' & QM_VALID' & Nomo' & NE' & HWF' & LHB' & OMO_GOOD').
    encode_agree Hγe. encode_agree Hγs.
    iDestruct (mono_list_auth_own_agree with "TL● TL●'") as %[_ <-].
    iCombine "TL● TL●'" as "TL●".
    iDestruct (mono_list_auth_own_agree with "EL● EL●'") as %[_ <-].
    iCombine "EL● EL●'" as "EL●".
    iDestruct (mono_list_auth_own_agree with "WL● WL●'") as %[_ <-].
    iCombine "WL● WL●'" as "WL●".
    iCombine "SL● SL●'" as "SL●".
    iDestruct (ghost_map_auth_agree with "Hγq Hγq'") as %<-.
    iCombine "Hγq Hγq'" as "Hγq".
    iCombine "HL● HL●'" as "HL●".
    iCombine "Hγg Hγg'" as "Hγg".

    iAssert (OmoAuth_WL_valid γs γel (p + q)%Qp omo WL)%I with "[WL✓ WL✓']" as "WL✓".
    { iCombine "WL✓ WL✓'" as "WL✓". rewrite !/OmoAuth_WL_valid -big_sepL2_sep.
      iApply (big_sepL2_impl with "WL✓"). iModIntro. iIntros "%i %ees %winfo %Hi %Hwinfo [H1 H2]". destruct ees as [e es].
      iDestruct "H1" as (????) "([%EQ1 %EQ2] & RL● & #EL@e & BIG)".
      iDestruct "H2" as (????) "([%EQ1' %EQ2'] & RL●' & #EL@e' & BIG')".
      inversion EQ1. subst e0 es0 winfo. inversion EQ1'. inversion EQ2'. subst e1 es1 γrl0.
      iExists e,es,γrl,einfo. iCombine "RL● RL●'" as "RL●".
      iDestruct (mono_list_idx_agree with "EL@e EL@e'") as %<-. clear EQ1 EQ2' EQ1' H3 H5.
      iFrame "∗#%". done. }

    repeat iExists _. iFrame "∗#%". done.
Qed.
Global Instance OmoAuth_asfractional γe γs q E omo stlist `{Interpretable eventT absStateT} :
  AsFractional (OmoAuth γe γs q E omo stlist _) (λ q, OmoAuth γe γs q E omo stlist _) q.
Proof. constructor; [done|apply _]. Qed.
Global Instance OmoSnapHistory_persistent γe E : Persistent (OmoSnapHistory γe E).
Proof. rewrite OmoSnapHistory_eq. apply _. Qed.
Global Instance OmoSnapHistory_timeless γe E : Timeless (OmoSnapHistory γe E).
Proof. rewrite OmoSnapHistory_eq. apply _. Qed.
Global Instance OmoSnapHistory_objective γe E : Objective (OmoSnapHistory γe E).
Proof. rewrite OmoSnapHistory_eq. apply _. Qed.
Global Instance OmoSnapStates_persistent γe γs omo stlist : Persistent (OmoSnapStates γe γs omo stlist).
Proof. rewrite OmoSnapStates_eq. apply _. Qed.
Global Instance OmoSnapStates_timeless γe γs omo stlist : Timeless (OmoSnapStates γe γs omo stlist).
Proof. rewrite OmoSnapStates_eq. apply _. Qed.
Global Instance OmoSnapStates_objective γe γs omo stlist : Objective (OmoSnapStates γe γs omo stlist).
Proof. rewrite OmoSnapStates_eq. apply _. Qed.
Global Instance OmoHbToken_timeless γe γs E omo stlist e `{Interpretable eventT absStateT} :
  Timeless (OmoHbToken γe γs E omo stlist e _).
Proof. rewrite OmoHbToken_eq. apply _. Qed.
Global Instance OmoHbToken_objective γe γs E omo stlist e `{Interpretable eventT absStateT} :
  Objective (OmoHbToken γe γs E omo stlist e _).
Proof. rewrite OmoHbToken_eq. apply _. Qed.

End omo_specific_def.

(* Lemmas that involve only omoGeneralG *)
Section omo_general_lemma.
Context {Σ : gFunctors} `{!omoGeneralG Σ}.

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

Local Open Scope nat_scope.

Lemma OmoGname_agree γe γx γx' :
  OmoGname γe γx -∗ OmoGname γe γx' -∗ ⌜ γx = γx' ⌝.
Proof.
  iIntros "#Hγx #Hγx'". rewrite !OmoGname_eq.
  iDestruct "Hγx" as (?????) "[%Hγe Hγx]".
  iDestruct "Hγx'" as (?????) "[%Hγe' Hγx']".
  encode_agree Hγe.
  iDestruct (own_valid_2 with "Hγx Hγx'") as %?%to_agree_op_inv_L. done.
Qed.

Lemma OmoTokenW_contra γe γe' e e' :
  OmoTokenW γe' e' -∗ OmoCW γe γe' e e' -∗ False.
Proof.
  iIntros "WCOMMIT #e↦e'".
  rewrite OmoCW_eq OmoTokenW_eq.
  iDestruct "e↦e'" as (??????????) "(%&%&%&%& [%Hγe %Hγe'] & EL@e & EL'@e' & GL@0 & GL@1 & [%Heinfo %Heinfo'])".
  iDestruct "WCOMMIT" as (????????) "([%Hγe2 %Heinfo'2] & #EL'@e'2 & GL● & _)".
  encode_agree Hγe'. iDestruct (mono_list_idx_agree with "EL'@e' EL'@e'2") as %<-.
  encode_agree Heinfo'.
  iDestruct (mono_list_auth_idx_lookup with "GL● GL@1") as %?. done.
Qed.

Lemma OmoTokenW_excl γe e :
  OmoTokenW γe e -∗ OmoTokenW γe e -∗ False.
Proof.
  iIntros "WCOMMIT WCOMMIT'". rewrite OmoTokenW_eq.
  iDestruct "WCOMMIT" as (????????) "([%Hγe %Heinfo] & #EL@e & GL● & _)".
  iDestruct "WCOMMIT'" as (????????) "([%Hγe' %Heinfo'] & #EL@e' & GL●' & _)".
  encode_agree Hγe. iDestruct (mono_list_idx_agree with "EL@e EL@e'") as %<-.
  encode_agree Heinfo. iDestruct (mono_list_auth_own_agree with "GL● GL●'") as %[? _]. done.
Qed.

Lemma OmoTokenR_contra γe γe' e e' :
  OmoTokenR γe' e' -∗ OmoCW γe γe' e e' -∗ False.
Proof.
  iIntros "RCOMMIT #e↦e'".
  rewrite OmoCW_eq OmoTokenR_eq.
  iDestruct "e↦e'" as (??????????) "(%&%&%&%& [%Hγe %Hγe'] & EL@e & EL'@e' & GL@0 & GL@1 & [%Heinfo %Heinfo'])".
  iDestruct "RCOMMIT" as (????????) "([%Hγe2 %Heinfo'2] & #EL'@e'2 & GL● & _)".
  encode_agree Hγe'. iDestruct (mono_list_idx_agree with "EL'@e' EL'@e'2") as %<-.
  encode_agree Heinfo'.
  iDestruct (mono_list_auth_idx_lookup with "GL● GL@1") as %?. done.
Qed.

Lemma OmoTokenR_excl γe e :
  OmoTokenR γe e -∗ OmoTokenR γe e -∗ False.
Proof.
  iIntros "RCOMMIT RCOMMIT'". rewrite OmoTokenR_eq.
  iDestruct "RCOMMIT" as (????????) "([%Hγe %Heinfo] & #EL@e & GL● & _)".
  iDestruct "RCOMMIT'" as (????????) "([%Hγe' %Heinfo'] & #EL@e' & GL●' & _)".
  encode_agree Hγe. iDestruct (mono_list_idx_agree with "EL@e EL@e'") as %<-.
  encode_agree Heinfo. iDestruct (mono_list_auth_own_agree with "GL● GL●'") as %[? _]. done.
Qed.

Lemma OmoTokenWR_excl γe e :
  OmoTokenW γe e -∗ OmoTokenR γe e -∗ False.
Proof.
  iIntros "WCOMMIT RCOMMIT". rewrite OmoTokenW_eq OmoTokenR_eq.
  iDestruct "WCOMMIT" as (????????) "([%Hγe %Heinfo] & #EL@e & GL● & #Hγb)".
  iDestruct "RCOMMIT" as (????????) "([%Hγe' %Heinfo'] & #EL@e' & GL●' & #Hγb')".
  encode_agree Hγe. iDestruct (mono_list_idx_agree with "EL@e EL@e'") as %<-.
  encode_agree Heinfo.
  iDestruct (own_valid_2 with "Hγb Hγb'") as %?%to_agree_op_inv_L. done.
Qed.

Lemma OmoEview_nonempty γe M :
  OmoEview γe M -∗ ⌜ M ≠ ∅ ⌝.
Proof.
  iIntros "#⊒M". rewrite OmoEview_eq.
  by iDestruct "⊒M" as (?????) "[[%Hγe %NEmp] BIG]".
Qed.

Lemma OmoEview_nonempty_obj γe M V :
  @{V} OmoEview γe M -∗ ⌜ M ≠ ∅ ⌝.
Proof.
  iIntros "#⊒M". rewrite OmoEview_eq.
  by iDestruct "⊒M" as (?????) "[[%Hγe %NEmp] BIG]".
Qed.

Lemma OmoEview_split γe M1 M2 :
  M1 ≠ ∅ → M2 ≠ ∅ →
  OmoEview γe M1 ∗ OmoEview γe M2 ⊣⊢ OmoEview γe (M1 ∪ M2).
Proof.
  iIntros "%NEmp1 %NEmp2". rewrite OmoEview_eq. iSplit.
  - iIntros "[#⊒M1 #⊒M2]".
    iDestruct "⊒M1" as (?????) "[[%Hγe _] BIG1]".
    iDestruct "⊒M2" as (?????) "[[%Hγe' _] BIG2]". encode_agree Hγe.
    iExists γtl,γel,γh,γg,γn. iSplit.
    { iPureIntro. split; [done|]. set_solver. }
    iApply big_sepS_forall. iIntros "%e %IN".
    have CASE : e ∈ M1 ∨ e ∈ M2 by set_solver.
    destruct CASE as [IN'|IN'].
    + by iDestruct (big_sepS_elem_of with "BIG1") as "?".
    + by iDestruct (big_sepS_elem_of with "BIG2") as "?".
  - iIntros "#⊒M". iDestruct "⊒M" as (?????) "[[%Hγe _] BIG]". iSplit.
    + iExists γtl,γel,γh,γg,γn. iSplit; [done|]. iApply big_sepS_forall. iIntros "%e %IN".
      by iDestruct (big_sepS_elem_of _ _ e with "BIG") as "?"; [set_solver|].
    + iExists γtl,γel,γh,γg,γn. iSplit; [done|]. iApply big_sepS_forall. iIntros "%e %IN".
      by iDestruct (big_sepS_elem_of _ _ e with "BIG") as "?"; [set_solver|].
Qed.

Lemma OmoEview_union γe M1 M2 :
  OmoEview γe M1 -∗ OmoEview γe M2 -∗
  OmoEview γe (M1 ∪ M2).
Proof.
  iIntros "#⊒M1 #⊒M2". rewrite OmoEview_eq.
  iDestruct "⊒M1" as (?????) "[[%Hγe %NEmp1] BIG1]".
  iDestruct "⊒M2" as (?????) "[[%Hγe' %NEmp2] BIG2]". encode_agree Hγe.
  iExists γtl,γel,γh,γg,γn. iSplitR.
  { iPureIntro. split; [done|]. set_solver. }
  iApply big_sepS_forall. iIntros "%e %IN".
  have CASE : e ∈ M1 ∨ e ∈ M2 by set_solver.
  destruct CASE as [IN'|IN'].
  - by iDestruct (big_sepS_elem_of with "BIG1") as "H".
  - by iDestruct (big_sepS_elem_of with "BIG2") as "H".
Qed.

Lemma OmoEview_union_obj γe M1 M2 V :
  @{V} OmoEview γe M1 -∗ @{V} OmoEview γe M2 -∗
  @{V} OmoEview γe (M1 ∪ M2).
Proof.
  iIntros "#⊒M1@V #⊒M2@V". iCombine "⊒M1@V ⊒M2@V" as "RES".
  iApply (view_at_mono with "RES"); [done|].
  iIntros "[#⊒M1 #⊒M2]". by iApply OmoEview_union.
Qed.

Lemma OmoEview_mono γe M1 M2 :
  M2 ⊆ M1 → M2 ≠ ∅ →
  OmoEview γe M1 -∗
  OmoEview γe M2.
Proof.
  iIntros "%SubM2M1 %NEmp #⊒M". rewrite OmoEview_eq.
  iDestruct "⊒M" as (?????) "[[%Hγe _] BIG]".
  iExists γtl,γel,γh,γg,γn. iSplit; [done|]. iApply big_sepS_forall. iIntros "%e %IN".
  iDestruct (big_sepS_elem_of _ _ e with "BIG") as "H"; [set_solver|]. done.
Qed.

Lemma OmoEview_mono_obj γe M1 M2 V :
  M2 ⊆ M1 → M2 ≠ ∅ →
  @{V} OmoEview γe M1 -∗
  @{V} OmoEview γe M2.
Proof.
  iIntros "%SubM2M1 %NEmp #⊒M@V". iApply (view_at_mono with "⊒M@V"); [done|].
  iIntros "#⊒M". by iApply OmoEview_mono.
Qed.

Lemma OmoEview_latest_elem_obj γe M V :
  @{V} OmoEview γe M -∗
  ∃ e, OmoUB γe M e ∗ ⌜ e ∈ M ⌝.
Proof.
  iIntros "#⊒M". rewrite OmoEview_eq.
  iDestruct "⊒M" as (?????) "[[%Hγe %NEmp] BIG]".
  iInduction M as [|e M NotIn] "IH" using set_ind_L; [done|].
  destruct (decide (M = ∅)) as [EQM|Nemp].
  { iExists e. iSplit; [|iPureIntro;set_solver].
    have EQ : {[e]} ∪ M = {[e]} by set_solver. rewrite EQ. subst M. clear EQ.
    rewrite /OmoUB !big_sepS_singleton OmoLe_eq.
    iDestruct "BIG" as (?) "[EL◯ _]". rewrite view_at_objective_iff.
    iExists γtl,γel,γh,γg,γn,einfo,einfo. iFrame "EL◯". done. }

  rewrite big_sepS_union; [|set_solver]. iDestruct "BIG" as "[BIG1 BIG2]".
  iDestruct ("IH" with "[] BIG2") as (e') "[MAX %e'IN]"; [done|].
  rewrite big_sepS_singleton. iDestruct "BIG1" as (einfo) "[EL◯ _]".

  iAssert (∃ einfo', @{V} ⎡mono_list_idx_own γel e' einfo'⎤)%I with "[]" as (?) "#EL◯'".
  { rewrite -view_at_exist. iApply (view_at_mono with "BIG2"); [done|]. iIntros "BIG".
    iDestruct (big_sepS_elem_of with "BIG") as (einfo') "[H _]"; [done|]. iExists einfo'. done. }
  rewrite !view_at_objective_iff.

  destruct (decide (einfo.1.2 ≤ einfo'.1.2)%Qp) as [LE|LT].
  { iExists e'. iSplit; [|iPureIntro;set_solver]. rewrite /OmoUB big_sepS_union; [|set_solver]. iFrame "MAX".
    rewrite big_sepS_singleton OmoLe_eq. iExists γtl,γel,γh,γg,γn,einfo,einfo'. iFrame "EL◯ EL◯'".
    iPureIntro. split; [done|]. done. }

  rewrite -Qp.lt_nge in LT.
  iExists e. iSplit; [|iPureIntro;set_solver]. rewrite /OmoUB big_sepS_union; [|set_solver]. iSplit.
  - rewrite big_sepS_singleton OmoLe_eq. iExists γtl,γel,γh,γg,γn,einfo,einfo. iFrame "EL◯". done.
  - iApply big_sepS_forall. iIntros "%x %IN". iDestruct (big_sepS_elem_of with "MAX") as "LE"; [exact IN|].
    rewrite OmoLe_eq. iDestruct "LE" as (???????) "([%Hγe' %LE] & #EL◯x & #EL◯'')".
    encode_agree Hγe. iDestruct (mono_list_idx_agree with "EL◯' EL◯''") as %<-.
    iExists γtl,γel,γh,γg,γn,einfo1,einfo. iFrame "EL◯x EL◯". iPureIntro. split; [done|].
    apply Qp.lt_le_incl. eapply Qp.le_lt_trans; try done.
Qed.

Lemma OmoEview_latest_elem γe M :
  OmoEview γe M -∗
  ∃ e, OmoUB γe M e ∗ ⌜ e ∈ M ⌝.
Proof.
  iIntros "#⊒M". iDestruct (view_at_intro with "⊒M") as (V) "[_ ⊒M@V]".
  by iApply OmoEview_latest_elem_obj.
Qed.

(* Irreflexitivity of `OmoLt` *)
Lemma OmoLt_irrefl γe e :
  OmoLt γe e e -∗ False.
Proof.
  iIntros "#e<e". rewrite OmoLt_eq.
  iDestruct "e<e" as (???????) "([%Hγe %LT] & #EL@e & #EL@e')".
  iDestruct (mono_list_idx_agree with "EL@e EL@e'") as %<-.
  have LE : (einfo1.1.2 ≤ einfo1.1.2)%Qp by done.
  apply Qp.lt_nge in LT. done.
Qed.

Lemma OmoLt_trans γe e1 e2 e3 :
  OmoLt γe e1 e2 -∗
  OmoLt γe e2 e3 -∗
  OmoLt γe e1 e3.
Proof.
  iIntros "#e1<e2 #e2<e3". rewrite OmoLt_eq.
  iDestruct "e1<e2" as (???????) "([%Hγe %LT1] & #EL@e1 & #EL@e2)".
  iDestruct "e2<e3" as (???????) "([%Hγe' %LT2] & #EL@e2' & #EL@e3)". encode_agree Hγe.
  iDestruct (mono_list_idx_agree with "EL@e2 EL@e2'") as %<-.
  iExists γtl,γel,γh,γg,γn,einfo1,einfo3. iFrame "#". iPureIntro. split; [done|].
  transitivity einfo2.1.2; try done.
Qed.

Lemma OmoLe_get_from_Lt γe e1 e2 :
  OmoLt γe e1 e2 -∗ OmoLe γe e1 e2.
Proof.
  iIntros "#e1<e2". rewrite OmoLe_eq OmoLt_eq.
  iDestruct "e1<e2" as (???????) "([%Hγe %LE] & #EL@e1 & #EL@e2)".
  iExists γtl,γel,γh,γg,γn,einfo1,einfo2. iFrame "#". iPureIntro. split; [done|].
  by apply Qp.lt_le_incl.
Qed.

Lemma OmoLe_get_from_Eq γe e1 e2 :
  OmoEq γe e1 e2 -∗ OmoLe γe e1 e2.
Proof.
  iIntros "#e1=e2". rewrite OmoLe_eq OmoEq_eq.
  iDestruct "e1=e2" as (???????) "([%Hγe %EQ] & #EL@e1 & #EL@e2)".
  iExists γtl,γel,γh,γg,γn,einfo1,einfo2. iFrame "#". iPureIntro. rewrite EQ. done.
Qed.

Lemma OmoEq_Le_trans γe e1 e1' e2 :
  OmoEq γe e1 e1' -∗
  OmoLe γe e1' e2 -∗
  OmoLe γe e1 e2.
Proof.
  iIntros "#e1=e1' #e1'≤e2". rewrite OmoEq_eq OmoLe_eq.
  iDestruct "e1=e1'" as (???????) "([%Hγe %EQ] & #EL@e1 & #EL@e1')".
  iDestruct "e1'≤e2" as (???????) "([%Hγe' %LE] & #EL@e1'' & #EL@e2)". encode_agree Hγe.
  iDestruct (mono_list_idx_agree with "EL@e1' EL@e1''") as %<-.
  iExists γtl,γel,γh,γg,γn,einfo1,einfo3. iFrame "#". iPureIntro. rewrite -EQ in LE. done.
Qed.

Lemma OmoLe_Eq_trans γe e1 e2 e2' :
  OmoLe γe e1 e2 -∗
  OmoEq γe e2 e2' -∗
  OmoLe γe e1 e2'.
Proof.
  iIntros "#e1≤e2 #e2=e2'". rewrite OmoEq_eq OmoLe_eq.
  iDestruct "e1≤e2" as (???????) "([%Hγe %LE] & #EL@e1 & #EL@e2)".
  iDestruct "e2=e2'" as (???????) "([%Hγe' %EQ] & #EL@e2a & #EL@e2')". encode_agree Hγe.
  iDestruct (mono_list_idx_agree with "EL@e2 EL@e2a") as %<-.
  iExists γtl,γel,γh,γg,γn,einfo1,einfo3. iFrame "#". iPureIntro. rewrite EQ in LE. done.
Qed.

Lemma OmoLe_trans γe e1 e2 e3 :
  OmoLe γe e1 e2 -∗
  OmoLe γe e2 e3 -∗
  OmoLe γe e1 e3.
Proof.
  iIntros "#e1≤e2 #e2≤e3". rewrite OmoLe_eq.
  iDestruct "e1≤e2" as (???????) "([%Hγe %LE1] & #EL@e1 & #EL@e2)".
  iDestruct "e2≤e3" as (???????) "([%Hγe' %LE2] & #EL@e2' & #EL@e3)". encode_agree Hγe.
  iDestruct (mono_list_idx_agree with "EL@e2 EL@e2'") as %<-.
  iExists γtl,γel,γh,γg,γn,einfo1,einfo3. iFrame "#". iPureIntro. split; [done|]. transitivity einfo2.1.2; done.
Qed.

Lemma OmoLe_Lt_trans γe e1 e2 e3 :
  OmoLe γe e1 e2 -∗
  OmoLt γe e2 e3 -∗
  OmoLt γe e1 e3.
Proof.
  iIntros "#e1≤e2 #e2<e3". rewrite OmoLe_eq OmoLt_eq.
  iDestruct "e1≤e2" as (???????) "([%Hγe %LE] & #EL@e1 & #EL@e2)".
  iDestruct "e2<e3" as (???????) "([%Hγe' %LT] & #EL@e2' & #EL@e3)". encode_agree Hγe.
  iDestruct (mono_list_idx_agree with "EL@e2 EL@e2'") as %<-.
  iExists γtl,γel,γh,γg,γn,einfo1,einfo3. iFrame "#". iPureIntro. split; [done|].
  by eapply Qp.le_lt_trans.
Qed.

Lemma OmoLt_Le_trans γe e1 e2 e3 :
  OmoLt γe e1 e2 -∗
  OmoLe γe e2 e3 -∗
  OmoLt γe e1 e3.
Proof.
  iIntros "#e1<e2 #e2≤e3". rewrite OmoLe_eq OmoLt_eq.
  iDestruct "e1<e2" as (???????) "([%Hγe %LT] & #EL@e1 & #EL@e2)".
  iDestruct "e2≤e3" as (???????) "([%Hγe' %LE] & #EL@e2' & #EL@e3)". encode_agree Hγe.
  iDestruct (mono_list_idx_agree with "EL@e2 EL@e2'") as %<-.
  iExists γtl,γel,γh,γg,γn,einfo1,einfo3. iFrame "#". iPureIntro. split; [done|].
  by eapply Qp.lt_le_trans.
Qed.

Lemma OmoLe_Lt_contra γe e1 e2 :
  OmoLe γe e1 e2 -∗ OmoLt γe e2 e1 -∗ False.
Proof.
  iIntros "#e1≤e2 #e2<e1". rewrite OmoLe_eq OmoLt_eq.
  iDestruct "e1≤e2" as (???????) "([%Hγe %LE] & #EL@e1 & #EL@e2)".
  iDestruct "e2<e1" as (???????) "([%Hγe' %LT] & #EL@e2' & #EL@e1')". encode_agree Hγe.
  iDestruct (mono_list_idx_agree with "EL@e1 EL@e1'") as %<-.
  iDestruct (mono_list_idx_agree with "EL@e2 EL@e2'") as %<-.
  apply Qp.lt_nge in LT. done.
Qed.

Lemma OmoLt_Le_contra γe e1 e2 :
  OmoLt γe e1 e2 -∗ OmoLe γe e2 e1 -∗ False.
Proof.
  iIntros "#e1<e2 #e2≤e1". by iApply OmoLe_Lt_contra.
Qed.

Lemma OmoEq_get_from_CW γe γe' e e' :
  OmoCW γe γe' e e' -∗
  OmoEq γe e e ∗ OmoEq γe' e' e'.
Proof.
  iIntros "#e↦e'". rewrite OmoCW_eq OmoEq_eq.
  iDestruct "e↦e'" as (??????????) "(%&%&%&%& [%Hγe %Hγe'] & EL@e & EL'@e' & _)".
  iSplit.
  - iExists γtl,γel,γh,γg,γn,einfo,einfo. iFrame "#". done.
  - iExists γtl',γel',γh',γg',γn',einfo',einfo'. iFrame "#". done.
Qed.

Lemma OmoEq_sym γe e1 e2 :
  OmoEq γe e1 e2 -∗ OmoEq γe e2 e1.
Proof.
  iIntros "#e1=e2". rewrite OmoEq_eq.
  iDestruct "e1=e2" as (???????) "([%Hγe %EQ] & EL@e1 & EL@e2)".
  iExists γtl,γel,γh,γg,γn,einfo2,einfo1. iFrame "#". done.
Qed.

Lemma OmoEq_trans γe e1 e2 e3 :
  OmoEq γe e1 e2 -∗
  OmoEq γe e2 e3 -∗
  OmoEq γe e1 e3.
Proof.
  iIntros "#e1=e2 #e2=e3". rewrite OmoEq_eq.
  iDestruct "e1=e2" as (???????) "([%Hγe %EQ1] & EL@e1 & EL@e2)".
  iDestruct "e2=e3" as (???????) "([%Hγe' %EQ2] & EL@e2' & EL@e3)". encode_agree Hγe.
  iDestruct (mono_list_idx_agree with "EL@e2 EL@e2'") as %<-.
  iExists γtl,γel,γh,γg,γn,einfo1,einfo3. iFrame "#". rewrite EQ1 -EQ2. done.
Qed.

Lemma OmoCW_agree_1 γe γe' γe'' e e' e'' :
  OmoCW γe γe' e e' -∗
  OmoCW γe γe'' e e'' -∗
  ⌜ γe' = γe'' ∧ e' = e'' ⌝.
Proof.
  iIntros "#e↦e' #e↦e''". rewrite OmoCW_eq.
  iDestruct "e↦e'" as (??????????) "(%&%&%&%& [%Hγe %Hγe'] & EL@e & EL'@e' & GL@0 & GL@1 & [%EQ1 %EQ2])".
  iDestruct "e↦e''" as (??????????) "(%&%&%&%& [%Hγen %Hγen'] & EL@e' & EL'@e'' & GL@0' & GL@1' & [%EQ1' %EQ2'])".
  encode_agree Hγe.
  iDestruct (mono_list_idx_agree with "EL@e EL@e'") as %<-.
  rewrite EQ1 in EQ1'. inversion EQ1'. subst γgl0.
  iDestruct (mono_list_idx_agree with "GL@0 GL@0'") as %[<- <-]%pair_inj. done.
Qed.

Lemma OmoCW_agree_2 γe1 γe1' γe2 e1 e1' e2 :
  OmoCW γe1 γe2 e1 e2 -∗
  OmoCW γe1' γe2 e1' e2 -∗
  ⌜ γe1 = γe1' ∧ e1 = e1' ⌝.
Proof.
  iIntros "#e↦e' #e↦e''". rewrite OmoCW_eq.
  iDestruct "e↦e'" as (??????????) "(%&%&%&%& [%Hγe %Hγe'] & EL@e & EL'@e' & GL@0 & GL@1 & [%EQ1 %EQ2])".
  iDestruct "e↦e''" as (??????????) "(%&%&%&%& [%Hγen %Hγen'] & EL@e' & EL'@e'' & GL@0' & GL@1' & [%EQ1' %EQ2'])".
  encode_agree Hγe'.
  iDestruct (mono_list_idx_agree with "EL'@e' EL'@e''") as %<-.
  rewrite EQ2 in EQ2'. apply (inj encode) in EQ2'. inversion EQ2'. subst γgl0.
  iDestruct (mono_list_idx_agree with "GL@1 GL@1'") as %[<- <-]%pair_inj. done.
Qed.

Lemma OmoUBgen_empty omo gen :
  OmoUBgen omo ∅ gen.
Proof. done. Qed.

Lemma OmoUBgen_append_w omo M gen e es :
  OmoUBgen omo M gen → OmoUBgen (omo_append_w omo e es) M gen.
Proof.
  intros. unfold OmoUBgen in *. intros. specialize (H _ H0) as (eidx & LOOKUP & LE).
  exists eidx. split; [|done]. destruct eidx.
  - rewrite lookup_omo_ro_event in LOOKUP. destruct (omo_read_op omo !! gen0) eqn:Heq; [|done].
    rewrite lookup_omo_ro_event omo_append_w_read_op lookup_app_l; [|by apply lookup_lt_Some in Heq].
    rewrite Heq. done.
  - rewrite lookup_omo_wr_event in LOOKUP.
    rewrite lookup_omo_wr_event omo_append_w_write_op lookup_app_l; [|by apply lookup_lt_Some in LOOKUP]. done.
Qed.

Lemma OmoUBgen_insert_w omo M gen gen' e es :
  (gen < gen')%nat →
  OmoUBgen omo M gen → OmoUBgen (omo_insert_w omo gen' e es) M gen.
Proof.
  intros. unfold OmoUBgen in *. intros. specialize (H0 _ H1) as (eidx & LOOKUP & LE).
  exists eidx. split; [|done]. destruct eidx.
  - rewrite lookup_omo_ro_event in LOOKUP. destruct (omo_read_op omo !! gen0) eqn:Heq; [|done].
    rewrite lookup_omo_ro_event omo_insert_w_read_op lookup_app_l; last first.
    { rewrite take_length. apply lookup_lt_Some in Heq. simpl in LE. lia. }
    rewrite lookup_take; [|simpl in *;lia]. rewrite Heq. done.
  - rewrite lookup_omo_wr_event in LOOKUP.
    rewrite lookup_omo_wr_event omo_insert_w_write_op lookup_app_l; last first.
    { rewrite take_length. apply lookup_lt_Some in LOOKUP. simpl in LE. lia. }
    rewrite lookup_take; [|simpl in *;lia]. done.
Qed.

Lemma OmoUBgen_insert_r omo M gen gen' e :
  OmoUBgen omo M gen → OmoUBgen (omo_insert_r omo gen' e) M gen.
Proof.
  intros. destruct (le_lt_dec (length omo) gen') as [LE|LT].
  { rewrite /omo_insert_r. replace omo with (omo ++ []); [|by simplify_list_eq]. rewrite alter_app_r_alt; [|done].
    rewrite /alter /list_alter. simplify_list_eq. done. }
  unfold OmoUBgen in *. intros. specialize (H _ H0) as (eidx & LOOKUP & LE).
  have [[e' es] Hgen'] : is_Some (omo !! gen') by rewrite lookup_lt_is_Some.
  exists eidx. split; [|done]. erewrite lookup_omo_before_insert_r; last first.
  { rewrite /omo_read_op list_lookup_fmap Hgen'. done. }
  simpl. rewrite decide_False; [done|]. unfold not. intros. subst eidx.
  rewrite lookup_omo_ro_event /omo_read_op list_lookup_fmap Hgen' /= in LOOKUP.
  apply lookup_lt_Some in LOOKUP. lia.
Qed.

Lemma OmoUBgen_mono omo M (gen1 gen2 : nat) :
  gen1 ≤ gen2 → OmoUBgen omo M gen1 → OmoUBgen omo M gen2.
Proof.
  intros. unfold OmoUBgen in *. intros.
  specialize (H0 _ H1) as (eidx & Heidx & LE).
  exists eidx. split; [done|]. lia.
Qed.

Lemma OmoUBgen_union omo M1 M2 gen :
  OmoUBgen omo M1 gen → OmoUBgen omo M2 gen → OmoUBgen omo (M1 ∪ M2) gen.
Proof.
  intros. unfold OmoUBgen in *. intros.
  have CASE : e ∈ M1 ∨ e ∈ M2 by set_solver.
  destruct CASE as [IN|IN].
  - specialize (H _ IN) as (eidx & Heidx & LE). exists eidx. done.
  - specialize (H0 _ IN) as (eidx & Heidx & LE). exists eidx. done.
Qed.

Lemma OmoUB_empty γe e :
  ⊢ OmoUB γe ∅ e.
Proof. unfold OmoUB. rewrite big_sepS_empty. done. Qed.

Lemma OmoUB_mono γe M e e' :
  OmoUB γe M e -∗
  OmoLe γe e e' -∗
  OmoUB γe M e'.
Proof.
  iIntros "#MAXgen_e #e≤e'". rewrite {2}/OmoUB big_sepS_forall. iIntros "%e'' %IN".
  iDestruct (big_sepS_elem_of with "MAXgen_e") as "#e''≤e"; [done|].
  iApply OmoLe_trans; try done.
Qed.

Lemma OmoUB_union γe M1 M2 e :
  OmoUB γe M1 e -∗ OmoUB γe M2 e -∗ OmoUB γe (M1 ∪ M2) e.
Proof.
  iIntros "#MAXgen #MAXgen'". rewrite {3}/OmoUB big_sepS_forall. iIntros "%e' %IN".
  have CASE : e' ∈ M1 ∨ e' ∈ M2 by set_solver.
  destruct CASE as [IN'|IN'].
  - by iDestruct (big_sepS_elem_of with "MAXgen") as "#e'≤e".
  - by iDestruct (big_sepS_elem_of with "MAXgen'") as "#e'≤e".
Qed.

Lemma CWMono_new γe γe' :
  ⊢ |==> ∃ γm, CWMono γe γe' γm ∅.
Proof.
  rewrite CWMono_eq.
  iMod (@ghost_map_alloc_empty _ event_id nat) as (γm) "Hγm".
  iModIntro. iExists γm. unfold CWMono_def.
  rewrite gset_to_gmap_empty big_sepS_empty. iFrame. iSplit; [done|].
  iModIntro. iIntros "%%%% [%IN _]". done.
Qed.

Lemma CWMonoValid_new γe γe' γm M e :
  e ∈ M →
  CWMono γe γe' γm M -∗
  CWMonoValid γm e.
Proof.
  iIntros "%IN MONO". rewrite CWMono_eq CWMonoValid_eq.
  iDestruct "MONO" as "(_ & BIG & _)".
  iDestruct (big_sepS_elem_of with "BIG") as (?) "[? _]"; [done|]. done.
Qed.

Lemma CWMono_acc γe γe' γm M  e1 e2 e1' e2' :
  CWMono γe γe' γm M -∗
  CWMonoValid γm e1 -∗
  CWMonoValid γm e2 -∗
  OmoCW γe γe' e1 e1' -∗
  OmoCW γe γe' e2 e2' -∗
  OmoLe γe' e1' e2' -∗
  OmoLe γe e1 e2.
Proof.
  iIntros "MONO #MONO✓e1 #MONO✓e2 #e1↦e1' #e2↦e2' #e1'≤e2'".
  rewrite CWMonoValid_eq CWMono_eq.
  iDestruct "MONO" as "(Hγm & #BIG & #COND)".
  iDestruct (ghost_map_lookup with "Hγm MONO✓e1") as %IN1.
  iDestruct (ghost_map_lookup with "Hγm MONO✓e2") as %IN2.
  rewrite !lookup_gset_to_gmap_Some in IN1,IN2.
  destruct IN1 as [IN1 _]. destruct IN2 as [IN2 _].
  iApply "COND"; try done.
Qed.

Lemma CWMono_acc' γe γe' γm M  e1 e2 e1' e2' :
  e1 ∈ M → e2 ∈ M →
  CWMono γe γe' γm M -∗
  OmoCW γe γe' e1 e1' -∗
  OmoCW γe γe' e2 e2' -∗
  OmoLe γe' e1' e2' -∗
  OmoLe γe e1 e2.
Proof.
  iIntros "%IN1 %IN2 MONO #e1↦e1' #e2↦e2' #e1'≤e2'".
  iDestruct (CWMonoValid_new with "MONO") as "#MONO✓e1"; [exact IN1|].
  iDestruct (CWMonoValid_new with "MONO") as "#MONO✓e2"; [exact IN2|].
  iApply (CWMono_acc with "MONO"); try done.
Qed.

(* General rule for inserting a new event into [CWMono] *)
Lemma CWMono_insert γe γe' γm M e1 e1' :
  CWMono γe γe' γm M -∗
  OmoCW γe γe' e1 e1' -∗
  □ ([∗ set] e2 ∈ M, ∀ e2', OmoCW γe γe' e2 e2' -∗ OmoLe γe' e1' e2' -∗ OmoLe γe e1 e2) -∗
  □ ([∗ set] e2 ∈ M, ∀ e2', OmoCW γe γe' e2 e2' -∗ OmoLe γe' e2' e1' -∗ OmoLe γe e2 e1)
  ==∗
  CWMono γe γe' γm ({[e1]} ∪ M) ∗ CWMonoValid γm e1.
Proof.
  iIntros "MONO #e1↦e1' #BIG1 #BIG2".
  destruct (decide (e1 ∈ M)) as [IN|NOTIN].
  { replace ({[e1]} ∪ M) with M by set_solver. iModIntro.
    iDestruct (CWMonoValid_new with "MONO") as "#MONO✓e1"; [done|].
    iFrame "∗#". }

  rewrite CWMono_eq CWMonoValid_eq.
  iDestruct "MONO" as "(Hγm & #BIG & #COND)".
  iMod (ghost_map_insert_persist e1 0 with "Hγm") as "[Hγm #KEYe1]".
  { rewrite lookup_gset_to_gmap_None. done. }
  rewrite -gset_to_gmap_union_singleton.
  iModIntro. iFrame "KEYe1". iFrame "Hγm". iSplitL.
  - iApply big_sepS_union; [set_solver|]. rewrite big_sepS_singleton. iFrame "#". iExists e1'. done.
  - iModIntro. iIntros "%e2 %e3 %e2' %e3' [%IN2 %IN3] #e2↦e2' #e3↦e3' #e2'≤e3'".
    destruct (decide (e2 = e1)) as [->|NE2]; destruct (decide (e3 = e1)) as [->|NE3].
    + iDestruct (OmoEq_get_from_CW with "e1↦e1'") as "[e1=e1 _]".
      iApply OmoLe_get_from_Eq. done.
    + have IN3' : e3 ∈ M by set_solver.
      iDestruct (big_sepS_elem_of with "BIG1") as "COND'"; [done|].
      iDestruct (OmoCW_agree_1 with "e1↦e1' e2↦e2'") as %[_ <-].
      iApply "COND'"; try done.
    + have IN2' : e2 ∈ M by set_solver.
      iDestruct (big_sepS_elem_of with "BIG2") as "COND'"; [done|].
      iDestruct (OmoCW_agree_1 with "e1↦e1' e3↦e3'") as %[_ <-].
      iApply "COND'"; try done.
    + have IN2' : e2 ∈ M by set_solver.
      have IN3' : e3 ∈ M by set_solver.
      iApply "COND"; try done.
Qed.

(* Insert a new event into [CWMono] if there is another event map with same generation *)
Lemma CWMono_insert_Eq γe γe' γm M e1 e2 e1' e2' :
  CWMono γe γe' γm M -∗
  CWMonoValid γm e1 -∗
  OmoCW γe γe' e1 e1' -∗
  OmoCW γe γe' e2 e2' -∗
  OmoEq γe e1 e2 -∗
  OmoEq γe' e1' e2'
  ==∗
  CWMono γe γe' γm ({[e2]} ∪ M) ∗ CWMonoValid γm e2.
Proof.
  iIntros "MONO #MONO✓e1 #e1↦e1' #e2↦e2' #e1=e2 #e1'=e2'".
  destruct (decide (e2 ∈ M)) as [IN|NOTIN].
  { replace ({[e2]} ∪ M) with M by set_solver. iModIntro.
    iDestruct (CWMonoValid_new with "MONO") as "#MONO✓e2"; [done|].
    iFrame "∗#". }

  rewrite CWMono_eq CWMonoValid_eq.
  iDestruct "MONO" as "(Hγm & #BIG & #COND)".
  iDestruct (ghost_map_lookup with "Hγm MONO✓e1") as %IN1.
  rewrite lookup_gset_to_gmap_Some in IN1. destruct IN1 as [IN1 _].
  iMod (ghost_map_insert_persist e2 0 with "Hγm") as "[Hγm #KEYe2]".
  { rewrite lookup_gset_to_gmap_None. done. }
  rewrite -gset_to_gmap_union_singleton.
  iModIntro. iFrame "Hγm KEYe2". iSplit.
  - iApply big_sepS_union; [set_solver|]. rewrite big_sepS_singleton. iFrame "#". iExists e2'. done.
  - iModIntro. iIntros "%e3 %e4 %e3' %e4' [%IN3 %IN4] #e3↦e3' #e4↦e4' #e3'≤e4'".
    destruct (decide (e3 = e2)) as [->|NE3]; destruct (decide (e4 = e2)) as [->|NE4].
    + iDestruct (OmoEq_get_from_CW with "e2↦e2'") as "[#e2=e2 _]".
      by iApply OmoLe_get_from_Eq.
    + have IN4' : e4 ∈ M by set_solver.
      iDestruct (OmoEq_sym with "e1=e2") as "e2=e1". iApply OmoEq_Le_trans; try done.
      iApply "COND"; try done.
      iDestruct (OmoCW_agree_1 with "e2↦e2' e3↦e3'") as %[_ <-].
      iApply OmoEq_Le_trans; try done.
    + have IN3' : e3 ∈ M by set_solver.
      iDestruct (OmoEq_sym with "e1=e2") as "e2=e1". iApply OmoLe_Eq_trans; try done.
      iApply "COND"; try done.
      iDestruct (OmoCW_agree_1 with "e2↦e2' e4↦e4'") as %[_ <-].
      iDestruct (OmoEq_sym with "e1'=e2'") as "e2'=e1'". iApply OmoLe_Eq_trans; try done.
    + have IN3' : e3 ∈ M by set_solver.
      have IN4' : e4 ∈ M by set_solver.
      iApply "COND"; try done.
Qed.

Lemma OmoHbs_split γe γe' e M1 M2 :
  OmoHbs γe γe' e M1 ∗ OmoHbs γe γe' e M2 ⊣⊢ OmoHbs γe γe' e (M1 ∪ M2).
Proof.
  iSplit.
  - iIntros "[#e⊒M1 #e⊒M2]". rewrite !OmoHbs_eq. iApply big_sepS_forall.
    iIntros "%e' %IN".
    have CASE : e' ∈ M1 ∨ e' ∈ M2 by set_solver.
    destruct CASE as [IN'|IN'].
    + iDestruct (big_sepS_elem_of with "e⊒M1") as "?"; try done.
    + iDestruct (big_sepS_elem_of with "e⊒M2") as "?"; try done.
  - iIntros "#e⊒M". rewrite !OmoHbs_eq. iSplit.
    + iApply big_sepS_forall. iIntros "%e' %IN".
      iDestruct (big_sepS_elem_of with "e⊒M") as "?"; try done. set_solver.
    + iApply big_sepS_forall. iIntros "%e' %IN".
      iDestruct (big_sepS_elem_of with "e⊒M") as "?"; try done. set_solver.
Qed.

Lemma OmoHb_from_Hbs γe γe' M e e' :
  e' ∈ M →
  OmoHbs γe γe' e M -∗
  OmoHb γe γe' e e'.
Proof.
  iIntros "%IN #e⊒M". rewrite OmoHbs_eq.
  iDestruct (big_sepS_elem_of with "e⊒M") as "e⊒e'"; [done|]. done.
Qed.

Lemma OmoHb_HbIncluded γe γe' M M' e e' :
  e ∈ M →
  OmoHb γe γe' e e' -∗
  HbIncluded γe γe' M M' -∗
  ⌜ e' ∈ M' ⌝.
Proof.
  iIntros "%IN #e⊒e' M⊢M'". rewrite OmoHb_eq HbIncluded_eq.
  iDestruct "M⊢M'" as (?????) "[%Hγe BIG]".
  iDestruct "e⊒e'" as (??????????) "(%&%&%& (%Hγe2 & %Hγe' & %INGL & %INCL') & EL@e & EL'@e' & GL◯)". encode_agree Hγe.
  iDestruct (big_sepS_elem_of with "BIG") as (???) "(#EL@e' & GL● & %INCL)"; [done|].
  iDestruct (mono_list_idx_agree with "EL@e EL@e'") as %<-.
  iDestruct (mono_list_auth_lb_valid with "GL● GL◯") as %[_ LEGL].
  iPureIntro. apply INCL.
  eapply elem_of_prefix; try done.
Qed.

Lemma OmoHbs_HbIncluded γe γe' M M' M'' e :
  e ∈ M →
  OmoHbs γe γe' e M' -∗
  HbIncluded γe γe' M M'' -∗
  ⌜ M' ⊆ M'' ⌝.
Proof.
  iIntros "%IN #e⊒M' M⊢M''".
  iInduction M' as [|e' M' NotIn] "IH" using set_ind_L.
  - set_solver.
  - iDestruct (OmoHb_from_Hbs _ _ _ _ e' with "e⊒M'") as "e⊒e'"; [set_solver|].
    iDestruct (OmoHb_HbIncluded with "e⊒e' M⊢M''") as %INCL; [done|].
    rewrite -OmoHbs_split. iDestruct "e⊒M'" as "[e⊒e's e⊒M']".
    iDestruct ("IH" with "e⊒M' M⊢M''") as %INCL'.
    iPureIntro. set_solver.
Qed.

End omo_general_lemma.

(* Lemmas that involve single `omoGeneralG` and `omoSpecificG` *)
Section omo_specific_1_lemma.
Context {eventT absStateT : Type}.
Context {Σ : gFunctors} `{!omoGeneralG Σ, !omoSpecificG Σ eventT absStateT}.

Notation history := (history eventT).
Notation iProp := (iProp Σ).
Notation vProp := (vProp Σ).

Implicit Types
  (γe γs γtl γel γh γg γwl γrl γgl γsl γq γb γm γn γx : gname)
  (q qg : Qp)
  (E : history)
  (M : eView)
  (st : absStateT)
  (ty : eventT)
  (einfo : (gname * option gname * view * eView * Qp * gname))
  (TL : list eventT) (* mono_list for type of events *)
  (EL : list (gname * option gname * view * eView * Qp * gname)) (* mono_list for all event info excluding event type *)
  (WL : list (event_id * gname * Qp)) (* mono_list for γs *)
  (RL : list event_id) (* mono_list for each generation *)
  (GL : list (gname * event_id)) (* mono_list for commit-with relation or seen_event *)
  (SL : list absStateT)
  (QM : gmap Qp nat)
  (eidx : event_idx).

Local Open Scope nat_scope.

Lemma OmoAuth_agree γe γs γs' q q' E E' omo omo' stlist stlist' `{Interpretable eventT absStateT} :
  OmoAuth γe γs q E omo stlist _ -∗ OmoAuth γe γs' q' E' omo' stlist' _ -∗
  ⌜ γs = γs' ∧ E = E' ∧ omo = omo' ∧ stlist = stlist' ⌝.
Proof.
  iIntros "M● M●'". rewrite OmoAuth_eq.
  iDestruct "M●" as (??????????) "(%&%& [%Hγe %Hγs] & _ & _ & _ & _ & _ & _ & Hγg & _)".
  iDestruct "M●'" as (??????????) "(%&%& [%Hγe' %Hγs'] & _ & _ & _ & _ & _ & _ & Hγg' & _)".
  encode_agree Hγe. iDestruct (ghost_var_agree with "Hγg Hγg'") as %[[[<- <-]%pair_inj <-]%pair_inj <-]%pair_inj.
  done.
Qed.

Lemma OmoAuth_wf γe γs q E omo stlist `{Interpretable eventT absStateT} :
  OmoAuth γe γs q E omo stlist _ -∗ ⌜ Linearizability_omo E omo stlist ∧ history_wf E ⌝.
Proof.
  iIntros "M●". rewrite OmoAuth_eq.
  iDestruct "M●" as (??????????)
    "(%&%& [%Hγe %Hγs] & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & %H')".
  des. done.
Qed.

Lemma OmoHbToken_wf γe γs E omo stlist e `{Interpretable eventT absStateT} :
  OmoHbToken γe γs E omo stlist e _ -∗ ⌜ Linearizability_omo E omo stlist ∧ history_wf E ⌝.
Proof.
  iIntros "M●". rewrite OmoHbToken_eq.
  iDestruct "M●" as (??????????)
    "(%&%&%&%& [%Hγe %Hγs] & TL● & EL● & WL● & SL● & Hγq & GL● & HL● & Hγg & EL✓ & WL✓ & #ELEMS & #KEYS & #BIG & %Pures)".
  des. done.
Qed.

Lemma OmoAuth_Linearizable γe γs q E omo stlist `{Interpretable eventT absStateT} :
  OmoAuth γe γs q E omo stlist _ -∗ ⌜ Linearizability_omo E omo stlist ⌝.
Proof.
  iIntros "M●". rewrite OmoAuth_eq.
  iDestruct "M●" as (??????????)
    "(%&%& [%Hγe %Hγs] & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & %H')".
  des. done.
Qed.

Lemma OmoHbToken_Linearizable γe γs E omo stlist e `{Interpretable eventT absStateT} :
  OmoHbToken γe γs E omo stlist e _ -∗ ⌜ Linearizability_omo E omo stlist ⌝.
Proof.
  iIntros "M●". rewrite OmoHbToken_eq.
  iDestruct "M●" as (??????????)
    "(%&%&%&%& [%Hγe %Hγs] & TL● & EL● & WL● & SL● & Hγq & GL● & HL● & Hγg & EL✓ & WL✓ & #ELEMS & #KEYS & #BIG & %Pures)".
  des. done.
Qed.

Lemma OmoAuth_hb_ord γe γs q E omo stlist `{Interpretable eventT absStateT} :
  OmoAuth γe γs q E omo stlist _ -∗ ⌜hb_ord E (seq 0 (length E))⌝.
Proof.
  iIntros "M●". rewrite OmoAuth_eq.
  iDestruct "M●" as (??????????)
    "(%&%& [%Hγe %Hγs] & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & %H')".
  des. done.
Qed.

Lemma OmoAuth_omo_nonempty γe γs q E omo stlist `{Interpretable eventT absStateT} :
  OmoAuth γe γs q E omo stlist _ -∗ ⌜ omo ≠ [] ⌝.
Proof.
  iIntros "M●". rewrite OmoAuth_eq.
  iDestruct "M●" as (??????????)
    "(%&%& [%Hγe %Hγs] & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & %H')".
  des. iPureIntro. done.
Qed.

Lemma OmoHbToken_omo_nonempty γe γs E omo stlist e `{Interpretable eventT absStateT} :
  OmoHbToken γe γs E omo stlist e _ -∗ ⌜ omo ≠ [] ⌝.
Proof.
  iIntros "M●". rewrite OmoHbToken_eq.
  iDestruct "M●" as (??????????)
    "(%&%&%&%& [%Hγe %Hγs] & TL● & EL● & WL● & SL● & Hγq & GL● & HL● & Hγg & EL✓ & WL✓ & #ELEMS & #KEYS & #BIG & Pures)".
  iDestruct "Pures" as %(EQlenTL & EQlenEL & EQe & LASTEL & E_TL_VALID & E_EL_VALID & MONOqg & QM_VALID & Nomo & NE & HWF & LHB & OMO_GOOD).
  done.
Qed.

Lemma OmoAuth_stlist_nonempty γe γs q E omo stlist `{Interpretable eventT absStateT} :
  OmoAuth γe γs q E omo stlist _ -∗ ⌜ stlist ≠ [] ⌝.
Proof.
  iIntros "M●". rewrite OmoAuth_eq.
  iDestruct "M●" as (??????????)
    "(%&%& [%Hγe %Hγs] & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & %H')".
  des. iPureIntro.
  eapply omo_stlist_length in H'9. unfold not. intros. subst stlist. destruct omo; try done.
Qed.

Lemma OmoAuth_frac_valid γe γs q E omo stlist `{Interpretable eventT absStateT} :
  OmoAuth γe γs q E omo stlist _ -∗ ⌜ (q ≤ 1)%Qp ⌝.
Proof.
  iIntros "M●". rewrite OmoAuth_eq.
  iDestruct "M●" as (??????????) "(%&%& [%Hγe %Hγs] & H & _)".
  iDestruct (mono_list_lb_own_get with "H") as "#H◯".
  iDestruct (mono_list_auth_lb_valid with "H H◯") as %[? _]. done.
Qed.

Lemma OmoAuth_OmoSnapHistory γe γs q E1 E2 omo stlist `{Interpretable eventT absStateT} :
  OmoAuth γe γs q E1 omo stlist _ -∗
  OmoSnapHistory γe E2 -∗
  ⌜ E2 ⊑ E1 ⌝.
Proof.
  iIntros "M● #E◯". rewrite OmoAuth_eq OmoSnapHistory_eq.
  iDestruct "M●" as (??????????)
    "(%&%& [%Hγe %Hγs] & TL● & EL● & WL● & SL● & Hγq & H● & Hγg & EL✓ & WL✓ & #ELEMS & #KEYS & Pures)".
  iDestruct "E◯" as (????? TL2 EL2) "(%Hγe' & TL◯ & EL◯ & H◯ & (%EQlenTL2 & %EQlenEL2 & %E2_TL2_VALID & %E2_EL2_VALID))".
  encode_agree Hγe.
  by iDestruct (mono_list_auth_lb_valid with "H● H◯") as %[_ ?].
Qed.

Lemma OmoAuth_OmoEview_obj γe γs V q E omo stlist M `{Interpretable eventT absStateT} :
  OmoAuth γe γs q E omo stlist _ -∗
  @{V} OmoEview γe M -∗
  ⌜ (∀ e, e ∈ M → is_Some (E !! e)) ⌝.
Proof.
  iIntros "M● #⊒M". rewrite OmoAuth_eq OmoEview_eq.
  iDestruct "M●" as (??????????)
    "(%&%& [%Hγe %Hγs] & TL● & EL● & WL● & SL● & Hγq & H● & Hγg & EL✓ & WL✓ & #ELEMS & #KEYS & Pures)".
  iDestruct "Pures" as %(EQlenTL & EQlenEL & E_TL_VALID & E_EL_VALID & MONOqg & QM_VALID & Nomo & NE & HWF & LHB & OMO_GOOD).
  iDestruct "⊒M" as (?????) "[[%Hγe' %NEmp] BIG]". encode_agree Hγe.
  iIntros "%e %IN". rewrite big_sepS_elem_of; [|done]. iDestruct "BIG" as (einfo) "[EL@e _]".
  rewrite view_at_objective_iff.
  iDestruct (mono_list_auth_idx_lookup with "EL● EL@e") as %ELe.
  iPureIntro. apply lookup_lt_Some in ELe. rewrite lookup_lt_is_Some. lia.
Qed.

Lemma OmoAuth_OmoEview γe γs q E omo stlist M `{Interpretable eventT absStateT} :
  OmoAuth γe γs q E omo stlist _ -∗
  OmoEview γe M -∗
  ⌜ (∀ e, e ∈ M → is_Some (E !! e)) ⌝.
Proof.
  iIntros "M● #⊒M". iDestruct (view_at_intro with "⊒M") as (?) "[_ ⊒M@V]".
  iApply (OmoAuth_OmoEview_obj with "M● ⊒M@V").
Qed.

Lemma OmoSnapHistory_OmoEview γe E M e V :
  sync <$> E !! e = Some V → e ∈ M →
  OmoSnapHistory γe E -∗
  OmoEview γe M -∗ ⊒V.
Proof.
  iIntros "%Ee %IN #E◯ #⊒M".
  destruct (E !! e) as [eV|] eqn:Heq; [|done]. inversion Ee. subst V.
  rewrite OmoSnapHistory_eq OmoEview_eq.
  iDestruct "E◯" as (???????) "(%Hγe & TL◯ & EL◯ & H◯ & (%EQlenTL & %EQlenEL & %E_TL_VALID & %E_EL_VALID))".
  iDestruct "⊒M" as (?????) "[[%Hγe' %NEmp] BIG]". encode_agree Hγe.
  iDestruct (big_sepS_elem_of with "BIG") as (einfo) "[EL@e ⊒OUT]"; [done|].
  have [einfo' Heinfo'] : is_Some (EL !! e).
  { rewrite lookup_lt_is_Some -EQlenEL. apply lookup_lt_Some in Heq. done. }
  iDestruct (@mono_list_idx_own_get _ _ _ _ _ e with "EL◯") as "EL@e'"; [done|].
  iDestruct (mono_list_idx_agree with "EL@e EL@e'") as %<-.
  unfold OmoAuth_E_EL_valid in *.
  specialize (E_EL_VALID _ _ _ Heq Heinfo') as [EQ _]. rewrite -EQ. done.
Qed.

Lemma OmoSnapHistory_OmoEview_obj γe E M e V' V :
  sync <$> E !! e = Some V' → e ∈ M →
  OmoSnapHistory γe E -∗
  @{V} OmoEview γe M -∗ ⌜ V' ⊑ V ⌝.
Proof.
  iIntros "%Ee %IN #E◯ #⊒M".
  destruct (E !! e) as [eV|] eqn:Heq; [|done]. inversion Ee. subst V'.
  rewrite OmoSnapHistory_eq OmoEview_eq.
  iDestruct "E◯" as (???????) "(%Hγe & TL◯ & EL◯ & H◯ & (%EQlenTL & %EQlenEL & %E_TL_VALID & %E_EL_VALID))".
  iDestruct "⊒M" as (?????) "[[%Hγe' %NEmp] BIG]". encode_agree Hγe.
  rewrite big_sepS_elem_of; [|done]. iDestruct "BIG" as (einfo) "[EL@e ⊒OUT]".
  rewrite view_at_objective_iff.
  have [einfo' Heinfo'] : is_Some (EL !! e).
  { rewrite lookup_lt_is_Some -EQlenEL. apply lookup_lt_Some in Heq. done. }
  iDestruct (@mono_list_idx_own_get _ _ _ _ _ e with "EL◯") as "EL@e'"; [done|].
  iDestruct (mono_list_idx_agree with "EL@e EL@e'") as %<-.
  unfold OmoAuth_E_EL_valid in *.
  specialize (E_EL_VALID _ _ _ Heq Heinfo') as [EQ _]. rewrite -EQ !view_at_unfold !monPred_at_in.
  iDestruct "⊒OUT" as %?. done.
Qed.

Lemma OmoEinfo_OmoEview γe e eV M :
  e ∈ M →
  OmoEinfo γe e eV -∗
  OmoEview γe M -∗
  ⊒(eV.(sync)).
Proof.
  iIntros "%IN #e✓eV #⊒M".
  rewrite OmoEinfo_eq OmoEview_eq.
  iDestruct "e✓eV" as (???????) "((%Hγe & %Hty & %Hdv & %Hlv) & TL@e & EL@e & HL@e & MAXgen & _)".
  iDestruct "⊒M" as (?????) "[[%Hγe' %NEmp] BIG]". encode_agree Hγe.
  iDestruct (big_sepS_elem_of with "BIG") as (einfo') "[EL@e' ⊒OUT]"; [done|].
  iDestruct (mono_list_idx_agree with "EL@e EL@e'") as %<-.
  rewrite -Hdv. done.
Qed.

Lemma OmoAuth_OmoSnapOmo γe γs q E omo1 omo2 stlist `{Interpretable eventT absStateT} :
  OmoAuth γe γs q E omo1 stlist _ -∗
  OmoSnapOmo γe γs omo2 -∗
  ⌜ omo_prefix omo2 omo1 ⌝.
Proof.
  iIntros "M● #M◯". rewrite OmoAuth_eq OmoSnapOmo_eq.
  iDestruct "M●" as (??????????)
    "(%&%& [%Hγe %Hγs] & TL● & EL● & WL● & SL● & Hγq & H● & Hγg & EL✓ & WL✓ & #ELEMS & #KEYS & Pures)".
  iDestruct "Pures" as %(EQlenTL & EQlenEL & E_TL_VALID & E_EL_VALID & MONOqg & QM_VALID & Nomo & NE & HWF & LHB & OMO_GOOD).
  iDestruct "M◯" as (?????????) "([%Hγe' %Hγs'] & WL◯ & BIG1 & BIG2)". encode_agree Hγe. encode_agree Hγs.
  iDestruct (mono_list_auth_lb_valid with "WL● WL◯") as %[_ PREFIX].
  iDestruct (big_sepL2_length with "BIG1") as %EQlenWL0.
  iDestruct (big_sepL2_length with "WL✓") as %EQlenWL.
  iSplit.
  - rewrite /mono_list_list.prefixes /map_included /map_relation. iIntros "%i". destruct (omo2 !! i) eqn:Heq; last first.
    { rewrite /omo_read_op list_lookup_fmap Heq /=. by destruct (omo1.*2 !! i). }
    destruct p as [e es]. rewrite /omo_read_op list_lookup_fmap Heq /=.
    have [winfo Hwinfo] : is_Some (WL0 !! i).
    { rewrite lookup_lt_is_Some -EQlenWL0. apply lookup_lt_Some in Heq. done. }
    iDestruct (big_sepL2_lookup with "BIG1") as (????) "([%Hees %Hwinfo'] & RL◯ & EL@e' & _)"; [done|done|].
    inversion Hees. subst e0 es0 winfo. clear Hees.
    iDestruct (@mono_list_idx_own_get _ _ _ _ _ i with "WL◯") as "WL@i"; [done|].
    iDestruct (mono_list_auth_idx_lookup with "WL● WL@i") as %WLi.
    have [[e' es'] Hi] : is_Some (omo1 !! i).
    { rewrite lookup_lt_is_Some EQlenWL. apply lookup_lt_Some in WLi. done. }
    iDestruct (big_sepL2_lookup with "WL✓") as (????) "([%EQ1 %EQ2] & RL● & #EL@e & BIG')"; [done|done|].
    inversion EQ1. inversion EQ2. subst e'. subst e0 es0 γrl0.
    iDestruct (mono_list_auth_lb_valid with "RL● RL◯") as %[_ PREFIX'].
    rewrite list_lookup_fmap Hi /=. done.
  - iAssert (⌜ WL0.*1.*1 = omo_write_op omo2 ⌝)%I with "[]" as %EQ1.
    { clear PREFIX. iClear "WL◯ BIG2". iInduction omo2 as [|[e es] omo2] "IH" forall (WL0 EQlenWL0).
      - by destruct WL0.
      - destruct WL0; try done. rewrite big_sepL2_cons. iDestruct "BIG1" as "[H BIG]".
        iDestruct "H" as (????) "[[%EQ1 %EQ2] RL◯]". inversion EQ1. subst e0 es0 p. clear EQ1.
        rewrite /omo_write_op !fmap_cons /=.
        iDestruct ("IH" with "[] BIG") as %EQ.
        { simpl in EQlenWL0. iPureIntro. lia. }
        rewrite EQ. done. }
    iAssert (⌜ WL.*1.*1 = omo_write_op omo1 ⌝)%I with "[WL✓]" as %EQ2.
    { clear MONOqg PREFIX OMO_GOOD Nomo QM_VALID. iClear "WL◯ BIG1 BIG2". iInduction omo1 as [|[e es] omo1] "IH" forall (WL EQlenWL).
      - by destruct WL.
      - destruct WL; try done. rewrite /OmoAuth_WL_valid big_sepL2_cons. iDestruct "WL✓" as "[H WL✓]".
        iDestruct "H" as (????) "[[%EQ1' %EQ2] _]". inversion EQ1'. subst e0 es0 p. clear EQ1'.
        rewrite /omo_write_op !fmap_cons /=.
        iDestruct ("IH" with "[] WL✓") as %EQ.
        { simpl in EQlenWL. iPureIntro. lia. }
        rewrite EQ. done. }
    rewrite -EQ1 -EQ2. iPureIntro. do 2 apply fmap_prefix. done.
Qed.

Lemma OmoEinfo_OmoEview_obj γe e eV M V :
  e ∈ M →
  OmoEinfo γe e eV -∗
  @{V} OmoEview γe M -∗
  ⌜ eV.(sync) ⊑ V ⌝.
Proof.
  iIntros "%IN #e✓eV #⊒M".
  rewrite OmoEinfo_eq OmoEview_eq.
  iDestruct "e✓eV" as (???????) "((%Hγe & %Hty & %Hdv & %Hlv) & TL@e & EL@e & HL@e & MAXgen & _)".
  iDestruct "⊒M" as (?????) "[[%Hγe' %NEmp] BIG]". encode_agree Hγe.
  rewrite big_sepS_elem_of; [|done]. iDestruct "BIG" as (einfo') "[EL@e' ⊒OUT]". rewrite view_at_objective_iff.
  iDestruct (mono_list_idx_agree with "EL@e EL@e'") as %<-.
  rewrite -Hdv !view_at_unfold !monPred_at_in. by iDestruct "⊒OUT" as %?.
Qed.

Lemma OmoSnapOmo_get γe γs q E omo stlist `{Interpretable eventT absStateT} :
  OmoAuth γe γs q E omo stlist _ -∗
  OmoSnapOmo γe γs omo.
Proof.
  rewrite OmoAuth_eq OmoSnapOmo_eq.
  iDestruct 1 as (??????????)
    "(%&%& [%Hγe %Hγs] & TL● & EL● & WL● & SL● & Hγq & H● & Hγg & EL✓ & WL✓ & #ELEMS & #KEYS & Pures)".
  iDestruct "Pures" as %(EQlenTL & EQlenEL & E_TL_VALID & E_EL_VALID & MONOqg & QM_VALID & Nomo & NE & HWF & LHB & OMO_GOOD).
  iExists γtl,γel,γh,γg,γn,γwl,γsl,γq. iExists WL.
  iDestruct (mono_list_lb_own_get with "WL●") as "#WL◯". iFrame "WL◯". iSplitR; [done|]. iSplit.
  - iApply (big_sepL2_impl with "WL✓ []").
    iIntros "%i %x1 %x2 %OMOi %WLi !> H". destruct x1 as [e es]. destruct x2 as [[e' γrl] qg].
    iDestruct "H" as (????) "([%EQ1 %EQ2] & RL● & #EL@e & BIG)".
    inversion EQ1. inversion EQ2. subst e'. subst e0 es0 γrl0 qg.
    iDestruct (mono_list_lb_own_get with "RL●") as "#RL◯".
    iExists e,es,γrl,einfo. iFrame "#". iFrame "BIG". done.
  - iApply big_sepL_forall. iIntros "%i %winfo %Hwinfo".
    unfold OmoAuth_QM_valid in *. specialize (QM_VALID winfo.2 i).
    have Hwinfo' : WL.*2 !! i = Some winfo.2 by rewrite list_lookup_fmap Hwinfo.
    rewrite QM_VALID in Hwinfo'.
    iDestruct (big_sepM_lookup with "KEYS") as "KEY"; [done|]. done.
Qed.

Lemma OmoSnapOmo_get_from_SnapStates γe γs omo stlist :
  OmoSnapStates γe γs omo stlist -∗
  OmoSnapOmo γe γs omo.
Proof.
  iIntros "#ST◯". rewrite OmoSnapStates_eq. rewrite /OmoSnapStates_def.
  iDestruct "ST◯" as (???) "(%Hγs & _ & H)". done.
Qed.

Lemma OmoSnapHistory_get γe γs q E omo stlist `{Interpretable eventT absStateT} :
  OmoAuth γe γs q E omo stlist _ -∗
  OmoSnapHistory γe E.
Proof.
  rewrite OmoAuth_eq OmoSnapHistory_eq.
  iDestruct 1 as (??????????)
    "(%&%& [%Hγe %Hγs] & TL● & EL● & WL● & SL● & Hγq & HL● & Hγg & EL✓ & WL✓ & #ELEMS & #KEYS & Pures)".
  iDestruct "Pures" as %(EQlenTL & EQlenEL & E_TL_VALID & E_EL_VALID & MONOqg & QM_VALID & Nomo & NE & HWF & LHB & OMO_GOOD).
  iDestruct (mono_list_lb_own_get with "TL●") as "#TL◯".
  iDestruct (mono_list_lb_own_get with "HL●") as "#HL◯".
  iDestruct (mono_list_lb_own_get with "EL●") as "#EL◯".
  iExists γtl,γel,γh,γg,γn,TL,EL. iFrame "#". iPureIntro. done.
Qed.

Lemma OmoEview_get_from_Einfo γe e eV :
  OmoEinfo γe e eV -∗
  @{eV.(sync)} OmoEview γe ({[e]} ∪ eV.(eview)).
Proof.
  iIntros "#e✓eV". rewrite OmoEinfo_eq.
  by iDestruct "e✓eV" as (???????) "((%Hγe & %Hty & %Hdv & %Hlv) & TL@e & EL@e & HL@e & MAXgen & EVIEW)".
Qed.

Lemma OmoEview_insert_new γe M e eV :
  OmoEview γe M -∗
  OmoEinfo γe e eV -∗
  ⊒eV.(sync) -∗
  OmoEview γe ({[e]} ∪ eV.(eview) ∪ M).
Proof.
  iIntros "#⊒M #e✓eV #⊒OUT".
  iDestruct (OmoEview_get_from_Einfo with "e✓eV") as "EVIEW@SYNC".
  iDestruct (view_at_elim with "⊒OUT EVIEW@SYNC") as "EVIEW".
  by iApply OmoEview_union.
Qed.

Lemma OmoEview_insert_new_obj Vb γe M e eV :
  eV.(sync) ⊑ Vb →
  @{Vb} OmoEview γe M -∗
  OmoEinfo γe e eV -∗
  @{Vb} OmoEview γe ({[e]} ∪ eV.(eview) ∪ M).
Proof.
  iIntros "%LeOUTVb #⊒M@Vb #e✓eV".
  iDestruct (view_at_objective_iff _ Vb with "e✓eV") as "e✓eV@Vb".
  iAssert (@{Vb} (⊒eV.(sync)))%I with "[]" as "#⊒OUT@Vb"; [done|].
  iCombine "⊒M@Vb e✓eV@Vb ⊒OUT@Vb" as "RES".
  iApply (view_at_mono with "RES"); [done|].
  iIntros "(#⊒M & #e✓eV & ⊒OUt)".
  by iApply OmoEview_insert_new.
Qed.

Lemma OmoEinfo_get γe γs q E omo stlist e eV `{Interpretable eventT absStateT} :
  E !! e = Some eV →
  OmoAuth γe γs q E omo stlist _ -∗
  OmoEinfo γe e eV.
Proof.
  iIntros "%Ee M●". rewrite OmoAuth_eq.
  iDestruct "M●" as (??????????)
    "(%&%& [%Hγe %Hγs] & TL● & EL● & WL● & SL● & Hγq & HL● & Hγg & EL✓ & WL✓ & #ELEMS & #KEYS & Pures)".
  iDestruct "Pures" as %(EQlenTL & EQlenEL & E_TL_VALID & E_EL_VALID & MONOqg & QM_VALID & Nomo & NE & HWF & LHB & OMO_GOOD).
  by iDestruct (big_sepL_lookup with "ELEMS") as "e✓eV".
Qed.

Lemma OmoEinfo_get_from_HbToken γe γs E omo stlist e eV e' `{Interpretable eventT absStateT} :
  E !! e = Some eV →
  OmoHbToken γe γs E omo stlist e' _ -∗
  OmoEinfo γe e eV.
Proof.
  iIntros "%Ee M●". rewrite OmoHbToken_eq.
  iDestruct "M●" as (??????????)
    "(%&%&%&%& [%Hγe %Hγs] & TL● & EL● & WL● & SL● & Hγq & GL● & HL● & Hγg & EL✓ & WL✓ & #ELEMS & #KEYS & #BIG & Pures)".
  iDestruct "Pures" as %(EQlenTL & EQlenEL & E_TL_VALID & E_EL_VALID & MONOqg & QM_VALID & Nomo & NE & HWF & LHB & OMO_GOOD).
  by iDestruct (big_sepL_lookup with "ELEMS") as "e✓eV".
Qed.

Lemma OmoEinfo_get' γe γs q E omo stlist e `{Interpretable eventT absStateT} :
  is_Some (E !! e) →
  OmoAuth γe γs q E omo stlist _ -∗
  ∃ eV, OmoEinfo γe e eV.
Proof.
  iIntros "%Ee M●". destruct Ee as [eV He].
  iDestruct (OmoEinfo_get with "M●") as "#e✓eV"; [done|].
  iExists eV. done.
Qed.

Lemma OmoAuth_OmoEinfo γe γs q E omo stlist e eV `{Interpretable eventT absStateT} :
  OmoAuth γe γs q E omo stlist _ -∗
  OmoEinfo γe e eV -∗
  ⌜ E !! e = Some eV ⌝.
Proof.
  iIntros "M● #e✓eV". rewrite OmoAuth_eq OmoEinfo_eq.
  iDestruct "M●" as (??????????)
    "(%&%& [%Hγe %Hγs] & TL● & EL● & WL● & SL● & Hγq & HL● & Hγg & EL✓ & WL✓ & #ELEMS & #KEYS & Pures)".
  iDestruct "Pures" as %(EQlenTL & EQlenEL & E_TL_VALID & E_EL_VALID & MONOqg & QM_VALID & Nomo & NE & HWF & LHB & OMO_GOOD).
  iDestruct "e✓eV" as (???????) "((%Hγe' & %Hty & %Hdv & %Hlv) & TL@e & EL@e & HL@e & MAXgen & EVIEW)".
  encode_agree Hγe.
  iDestruct (mono_list_auth_idx_lookup with "HL● HL@e") as %LOOKUP. done.
Qed.

Lemma OmoHbToken_OmoEinfo γe γs E omo stlist e eV e' `{Interpretable eventT absStateT} :
  OmoHbToken γe γs E omo stlist e' _ -∗
  OmoEinfo γe e eV -∗
  ⌜ E !! e = Some eV ⌝.
Proof.
  iIntros "M● #e✓eV". rewrite OmoHbToken_eq OmoEinfo_eq.
  iDestruct "M●" as (??????????)
    "(%&%&%&%& [%Hγe %Hγs] & TL● & EL● & WL● & SL● & Hγq & GL● & HL● & Hγg & EL✓ & WL✓ & #ELEMS & #KEYS & #BIG & Pures)".
  iDestruct "Pures" as %(EQlenTL & EQlenEL & E_TL_VALID & E_EL_VALID & MONOqg & QM_VALID & Nomo & NE & HWF & LHB & OMO_GOOD).
  iDestruct "e✓eV" as (???????) "((%Hγe' & %Hty & %Hdv & %Hlv) & TL@e & EL@e & HL@e & MAXgen & EVIEW)".
  encode_agree Hγe.
  iDestruct (mono_list_auth_idx_lookup with "HL● HL@e") as %LOOKUP. done.
Qed.

Lemma OmoAuth_OmoEinfo' γe γs q E omo stlist e eV `{Interpretable eventT absStateT} :
  OmoAuth γe γs q E omo stlist _ -∗
  OmoEinfo γe e eV -∗
  ∃ eidx, ⌜ lookup_omo omo eidx = Some e ⌝.
Proof.
  iIntros "M● #e✓eV". iDestruct (OmoAuth_OmoEinfo with "M● e✓eV") as %He.
  iDestruct (OmoAuth_wf with "M●") as %[OMO_GOOD _].
  eapply lookup_omo_surjective in OMO_GOOD; [|done]. done.
Qed.

Lemma OmoHbToken_OmoEinfo' γe γs E omo stlist e eV e' `{Interpretable eventT absStateT} :
  OmoHbToken γe γs E omo stlist e' _ -∗
  OmoEinfo γe e eV -∗
  ∃ eidx, ⌜ lookup_omo omo eidx = Some e ⌝.
Proof.
  iIntros "M● #e✓eV". iDestruct (OmoHbToken_OmoEinfo with "M● e✓eV") as %He.
  iDestruct (OmoHbToken_wf with "M●") as %[OMO_GOOD _].
  eapply lookup_omo_surjective in OMO_GOOD; [|done]. done.
Qed.

Lemma OmoEinfo_agree γe e eV eV' :
  OmoEinfo γe e eV -∗
  OmoEinfo γe e eV' -∗
  ⌜ eV = eV' ⌝.
Proof.
  iIntros "#e✓eV #e✓eV'". rewrite OmoEinfo_eq.
  iDestruct "e✓eV" as (???????) "((%Hγe & %Hty & %Hdv & %Hlv) & TL@e & EL@e & HL@e & MAXgen & EVIEW)".
  iDestruct "e✓eV'" as (???????) "((%Hγe' & %Hty' & %Hdv' & %Hlv') & TL@e' & EL@e' & HL@e' & MAXgen' & EVIEW')".
  encode_agree Hγe.
  iDestruct (mono_list_idx_agree with "HL@e HL@e'") as %<-. done.
Qed.

Lemma OmoLt_get γe γs q E omo stlist eidx1 eidx2 e1 e2 `{Interpretable eventT absStateT} :
  lookup_omo omo eidx1 = Some e1 →
  lookup_omo omo eidx2 = Some e2 →
  (gen_of eidx1 < gen_of eidx2)%nat →
  OmoAuth γe γs q E omo stlist _ -∗
  OmoLt γe e1 e2.
Proof.
  iIntros "%Heidx1 %Heidx2 %LT M●". rewrite OmoAuth_eq OmoLt_eq.
  iDestruct "M●" as (??????????)
    "(%&%& [%Hγe %Hγs] & TL● & EL● & WL● & SL● & Hγq & HL● & Hγg & EL✓ & WL✓ & #ELEMS & #KEYS & Pures)".
  iDestruct "Pures" as %(EQlenTL & EQlenEL & E_TL_VALID & E_EL_VALID & MONOqg & QM_VALID & Nomo & NE & HWF & LHB & OMO_GOOD).
  eapply lookup_omo_event_valid in Heidx1 as He1; [|done]. rewrite lookup_lt_is_Some in He1.
  eapply lookup_omo_event_valid in Heidx2 as He2; [|done]. rewrite lookup_lt_is_Some in He2.
  have [einfo1 Heinfo1] : is_Some (EL !! e1) by rewrite lookup_lt_is_Some -EQlenEL.
  have [einfo2 Heinfo2] : is_Some (EL !! e2) by rewrite lookup_lt_is_Some -EQlenEL.
  iDestruct (mono_list_lb_own_get with "EL●") as "#EL◯".
  iDestruct (@mono_list_idx_own_get _ _ _ _ _ e1 with "EL◯") as "#EL@e1"; [done|].
  iDestruct (@mono_list_idx_own_get _ _ _ _ _ e2 with "EL◯") as "#EL@e2"; [done|].
  iDestruct (big_sepL2_length with "WL✓") as %EQlenWL.

  set gen1 := gen_of eidx1.
  set gen2 := gen_of eidx2.
  have [winfo1 Hwinfo1] : is_Some (WL !! gen1).
  { rewrite lookup_lt_is_Some -EQlenWL. apply lookup_omo_lt_Some in Heidx1. done. }
  have [winfo2 Hwinfo2] : is_Some (WL !! gen2).
  { rewrite lookup_lt_is_Some -EQlenWL. apply lookup_omo_lt_Some in Heidx2. done. }
  iAssert (⌜ winfo1.2 = einfo1.1.2 ⌝)%I with "[-]" as %EQgen1.
  { destruct (omo !! gen1) as [[e es]|] eqn:Heq; last first.
    { apply lookup_ge_None_1 in Heq. apply lookup_omo_lt_Some in Heidx1. lia. }
    iDestruct (big_sepL2_lookup with "WL✓") as (????) "([%EQ1 %EQ2] & RL● & #EL@e & BIG)"; [done|done|].
    inversion EQ1. subst e0 es0 winfo1. clear EQ1. simpl.
    destruct (decide (e1 = e)) as [->|NEQ].
    - iDestruct (mono_list_idx_agree with "EL@e1 EL@e") as %<-. done.
    - destruct eidx1; last first.
      { rewrite lookup_omo_wr_event /omo_write_op list_lookup_fmap Heq /= in Heidx1. inversion Heidx1. done. }
      rewrite lookup_omo_ro_event /omo_read_op list_lookup_fmap Heq /= in Heidx1.
      iDestruct (big_sepL_lookup with "BIG") as (?) "[#EL@e1' %EQ]"; [done|].
      iDestruct (mono_list_idx_agree with "EL@e1 EL@e1'") as %<-. rewrite EQ. done. }
  iAssert (⌜ winfo2.2 = einfo2.1.2 ⌝)%I with "[-]" as %EQgen2.
  { destruct (omo !! gen2) as [[e es]|] eqn:Heq; last first.
    { apply lookup_ge_None_1 in Heq. apply lookup_omo_lt_Some in Heidx2. lia. }
    iDestruct (big_sepL2_lookup with "WL✓") as (????) "([%EQ1 %EQ2] & RL● & #EL@e & BIG)"; [done|done|].
    inversion EQ1. subst e0 es0 winfo2. clear EQ1. simpl.
    destruct (decide (e2 = e)) as [->|NEQ].
    - iDestruct (mono_list_idx_agree with "EL@e2 EL@e") as %<-. done.
    - destruct eidx2; last first.
      { rewrite lookup_omo_wr_event /omo_write_op list_lookup_fmap Heq /= in Heidx2. inversion Heidx2. done. }
      rewrite lookup_omo_ro_event /omo_read_op list_lookup_fmap Heq /= in Heidx2.
      iDestruct (big_sepL_lookup with "BIG") as (?) "[#EL@e2' %EQ]"; [done|].
      iDestruct (mono_list_idx_agree with "EL@e2 EL@e2'") as %<-. rewrite EQ. done. }
  unfold OmoAuth_qg_mono in *.
  have CONDLT : gen1 < gen2 by lia.
  specialize (MONOqg _ _ _ _ Hwinfo1 Hwinfo2 CONDLT).

  iExists γtl,γel,γh,γg,γn,einfo1,einfo2. iFrame "#". iPureIntro. rewrite -EQgen1 -EQgen2. done.
Qed.

Lemma OmoLt_get_from_HbToken γe γs E omo stlist eidx1 eidx2 e1 e2 e3 `{Interpretable eventT absStateT} :
  lookup_omo omo eidx1 = Some e1 →
  lookup_omo omo eidx2 = Some e2 →
  (gen_of eidx1 < gen_of eidx2)%nat →
  OmoHbToken γe γs E omo stlist e3 _ -∗
  OmoLt γe e1 e2.
Proof.
  iIntros "%Heidx1 %Heidx2 %LT M●". rewrite OmoHbToken_eq OmoLt_eq.
  iDestruct "M●" as (??????????)
    "(%&%&%&%& [%Hγe %Hγs] & TL● & EL● & WL● & SL● & Hγq & GL● & HL● & Hγg & EL✓ & WL✓ & #ELEMS & #KEYS & #BIG & Pures)".
  iDestruct "Pures" as %(EQlenTL & EQlenEL & EQe & LASTEL & E_TL_VALID & E_EL_VALID & MONOqg & QM_VALID & Nomo & NE & HWF & LHB & OMO_GOOD).
  eapply lookup_omo_event_valid in Heidx1 as He1; [|done]. rewrite lookup_lt_is_Some in He1.
  eapply lookup_omo_event_valid in Heidx2 as He2; [|done]. rewrite lookup_lt_is_Some in He2.
  have [einfo1 Heinfo1] : is_Some (EL !! e1) by rewrite lookup_lt_is_Some -EQlenEL.
  have [einfo2 Heinfo2] : is_Some (EL !! e2) by rewrite lookup_lt_is_Some -EQlenEL.
  iDestruct (mono_list_lb_own_get with "EL●") as "#EL◯".
  iDestruct (@mono_list_idx_own_get _ _ _ _ _ e1 with "EL◯") as "#EL@e1"; [done|].
  iDestruct (@mono_list_idx_own_get _ _ _ _ _ e2 with "EL◯") as "#EL@e2"; [done|].
  iDestruct (big_sepL2_length with "WL✓") as %EQlenWL.

  set gen1 := gen_of eidx1.
  set gen2 := gen_of eidx2.
  have [winfo1 Hwinfo1] : is_Some (WL !! gen1).
  { rewrite lookup_lt_is_Some -EQlenWL. apply lookup_omo_lt_Some in Heidx1. done. }
  have [winfo2 Hwinfo2] : is_Some (WL !! gen2).
  { rewrite lookup_lt_is_Some -EQlenWL. apply lookup_omo_lt_Some in Heidx2. done. }
  iAssert (⌜ winfo1.2 = einfo1.1.2 ⌝)%I with "[-]" as %EQgen1.
  { destruct (omo !! gen1) as [[e es]|] eqn:Heq; last first.
    { apply lookup_ge_None_1 in Heq. apply lookup_omo_lt_Some in Heidx1. lia. }
    iDestruct (big_sepL2_lookup with "WL✓") as (????) "([%EQ1 %EQ2] & RL● & #EL@e & BIG')"; [done|done|].
    inversion EQ1. subst e0 es0 winfo1. clear EQ1. simpl.
    destruct (decide (e1 = e)) as [->|NEQ].
    - iDestruct (mono_list_idx_agree with "EL@e1 EL@e") as %<-. done.
    - destruct eidx1; last first.
      { rewrite lookup_omo_wr_event /omo_write_op list_lookup_fmap Heq /= in Heidx1. inversion Heidx1. done. }
      rewrite lookup_omo_ro_event /omo_read_op list_lookup_fmap Heq /= in Heidx1.
      iDestruct (big_sepL_lookup with "BIG'") as (?) "[#EL@e1' %EQ]"; [done|].
      iDestruct (mono_list_idx_agree with "EL@e1 EL@e1'") as %<-. rewrite EQ. done. }
  iAssert (⌜ winfo2.2 = einfo2.1.2 ⌝)%I with "[-]" as %EQgen2.
  { destruct (omo !! gen2) as [[e es]|] eqn:Heq; last first.
    { apply lookup_ge_None_1 in Heq. apply lookup_omo_lt_Some in Heidx2. lia. }
    iDestruct (big_sepL2_lookup with "WL✓") as (????) "([%EQ1 %EQ2] & RL● & #EL@e & BIG')"; [done|done|].
    inversion EQ1. subst e0 es0 winfo2. clear EQ1. simpl.
    destruct (decide (e2 = e)) as [->|NEQ].
    - iDestruct (mono_list_idx_agree with "EL@e2 EL@e") as %<-. done.
    - destruct eidx2; last first.
      { rewrite lookup_omo_wr_event /omo_write_op list_lookup_fmap Heq /= in Heidx2. inversion Heidx2. done. }
      rewrite lookup_omo_ro_event /omo_read_op list_lookup_fmap Heq /= in Heidx2.
      iDestruct (big_sepL_lookup with "BIG'") as (?) "[#EL@e2' %EQ]"; [done|].
      iDestruct (mono_list_idx_agree with "EL@e2 EL@e2'") as %<-. rewrite EQ. done. }
  unfold OmoAuth_qg_mono in *.
  have CONDLT : gen1 < gen2 by lia.
  specialize (MONOqg _ _ _ _ Hwinfo1 Hwinfo2 CONDLT).

  iExists γtl,γel,γh,γg,γn,einfo1,einfo2. iFrame "#". iPureIntro. rewrite -EQgen1 -EQgen2. done.
Qed.

Lemma OmoLt_get_append_w γe γs q E omo stlist e e' eV' `{Interpretable eventT absStateT} :
  e ≠ e' →
  OmoAuth γe γs q E (omo_append_w omo e []) stlist _ -∗
  OmoEinfo γe e' eV' -∗
  OmoLt γe e' e.
Proof.
  iIntros "%NE M● #e'✓eV'".
  iDestruct (OmoAuth_OmoEinfo' with "M● e'✓eV'") as %[eidx' Heidx'].

  set eidx := wr_event (length omo).
  set omo' := omo_append_w omo e [].
  have Heidx : lookup_omo omo' eidx = Some e.
  { subst omo' eidx. rewrite lookup_omo_wr_event omo_append_w_write_op omo_write_op_length lookup_app_1_eq. done. }
  iApply (OmoLt_get with "M●"); try done.
  subst eidx. simpl.
  rewrite lookup_omo_before_append_w in Heidx'. destruct (decide (eidx' = wr_event (length omo))) as [->|NEQ].
  { rewrite Heidx in Heidx'. inversion Heidx'. done. }
  by apply lookup_omo_lt_Some in Heidx'.
Qed.

Lemma OmoLt_get_append_w_from_HbToken γe γs E omo stlist e e' e'' eV' `{Interpretable eventT absStateT} :
  e ≠ e' →
  OmoHbToken γe γs E (omo_append_w omo e []) stlist e'' _ -∗
  OmoEinfo γe e' eV' -∗
  OmoLt γe e' e.
Proof.
  iIntros "%NE M● #e'✓eV'".
  iDestruct (OmoHbToken_OmoEinfo' with "M● e'✓eV'") as %[eidx' Heidx'].

  set eidx := wr_event (length omo).
  set omo' := omo_append_w omo e [].
  have Heidx : lookup_omo omo' eidx = Some e.
  { subst omo' eidx. rewrite lookup_omo_wr_event omo_append_w_write_op omo_write_op_length lookup_app_1_eq. done. }
  iApply (OmoLt_get_from_HbToken with "M●"); try done.
  subst eidx. simpl.
  rewrite lookup_omo_before_append_w in Heidx'. destruct (decide (eidx' = wr_event (length omo))) as [->|NEQ].
  { rewrite Heidx in Heidx'. inversion Heidx'. done. }
  by apply lookup_omo_lt_Some in Heidx'.
Qed.

Lemma OmoAuth_OmoLt γe γs q E omo stlist e1 e2 `{Interpretable eventT absStateT} :
  OmoAuth γe γs q E omo stlist _ -∗
  OmoLt γe e1 e2 -∗
  ⌜ is_Some (E !! e1) ∧ is_Some (E !! e2) ⌝.
Proof.
  iIntros "M● #e1<e2". rewrite OmoAuth_eq OmoLt_eq.
  iDestruct "M●" as (??????????)
    "(%&%& [%Hγe %Hγs] & TL● & EL● & WL● & SL● & Hγq & HL● & Hγg & EL✓ & WL✓ & #ELEMS & #KEYS & Pures)".
  iDestruct "Pures" as %(EQlenTL & EQlenEL & E_TL_VALID & E_EL_VALID & MONOqg & QM_VALID & Nomo & NE & HWF & LHB & OMO_GOOD).
  iDestruct "e1<e2" as (???????) "([%Hγe' %LT] & #EL@e1 & #EL@e2)". encode_agree Hγe.
  iDestruct (mono_list_auth_idx_lookup with "EL● EL@e1") as %He1%lookup_lt_Some.
  iDestruct (mono_list_auth_idx_lookup with "EL● EL@e2") as %He2%lookup_lt_Some.
  iPureIntro. rewrite !lookup_lt_is_Some !EQlenEL. done.
Qed.

Lemma OmoAuth_OmoLt_l γe γs q E omo stlist e1 e2 `{Interpretable eventT absStateT} :
  OmoAuth γe γs q E omo stlist _ -∗
  OmoLt γe e1 e2 -∗
  ∃ eidx, ⌜ lookup_omo omo eidx = Some e1 ⌝.
Proof.
  iIntros "M● #e1<e2". iDestruct (OmoAuth_OmoLt with "M● e1<e2") as %[He1 _].
  iDestruct (OmoAuth_wf with "M●") as %[OMO_GOOD _].
  eapply lookup_omo_surjective in He1; [|done]. done.
Qed.

Lemma OmoAuth_OmoLt_r γe γs q E omo stlist e1 e2 `{Interpretable eventT absStateT} :
  OmoAuth γe γs q E omo stlist _ -∗
  OmoLt γe e1 e2 -∗
  ∃ eidx, ⌜ lookup_omo omo eidx = Some e2 ⌝.
Proof.
  iIntros "M● #e1<e2". iDestruct (OmoAuth_OmoLt with "M● e1<e2") as %[_ He2].
  iDestruct (OmoAuth_wf with "M●") as %[OMO_GOOD _].
  eapply lookup_omo_surjective in He2; [|done]. done.
Qed.

Lemma OmoLt_Lt γe γs q E omo stlist eidx1 eidx2 e1 e2 `{Interpretable eventT absStateT} :
  lookup_omo omo eidx1 = Some e1 →
  lookup_omo omo eidx2 = Some e2 →
  OmoAuth γe γs q E omo stlist _ -∗
  OmoLt γe e1 e2 -∗
  ⌜ (gen_of eidx1 < gen_of eidx2)%nat ⌝.
Proof.
  iIntros "%Heidx1 %Heidx2 M● #e1<e2". rewrite OmoAuth_eq OmoLt_eq.
  iDestruct "M●" as (??????????)
    "(%&%& [%Hγe %Hγs] & TL● & EL● & WL● & SL● & Hγq & HL● & Hγg & EL✓ & WL✓ & #ELEMS & #KEYS & Pures)".
  iDestruct "Pures" as %(EQlenTL & EQlenEL & E_TL_VALID & E_EL_VALID & MONOqg & QM_VALID & Nomo & NE & HWF & LHB & OMO_GOOD).
  iDestruct "e1<e2" as (???????) "([%Hγe' %LT] & #EL@e1 & #EL@e2)". encode_agree Hγe.
  iDestruct (big_sepL2_length with "WL✓") as %EQlenWL.

  set gen1 := gen_of eidx1.
  set gen2 := gen_of eidx2.
  have [winfo1 Hwinfo1] : is_Some (WL !! gen1).
  { rewrite lookup_lt_is_Some -EQlenWL. apply lookup_omo_lt_Some in Heidx1. done. }
  have [winfo2 Hwinfo2] : is_Some (WL !! gen2).
  { rewrite lookup_lt_is_Some -EQlenWL. apply lookup_omo_lt_Some in Heidx2. done. }
  iAssert (⌜ winfo1.2 = einfo1.1.2 ⌝)%I with "[-]" as %EQgen1.
  { destruct (omo !! gen1) as [[e es]|] eqn:Heq; last first.
    { apply lookup_ge_None_1 in Heq. apply lookup_omo_lt_Some in Heidx1. lia. }
    iDestruct (big_sepL2_lookup with "WL✓") as (????) "([%EQ1 %EQ2] & RL● & #EL@e & BIG)"; [done|done|].
    inversion EQ1. subst e0 es0 winfo1. clear EQ1. simpl.
    destruct (decide (e1 = e)) as [->|NEQ].
    - iDestruct (mono_list_idx_agree with "EL@e1 EL@e") as %<-. done.
    - destruct eidx1; last first.
      { rewrite lookup_omo_wr_event /omo_write_op list_lookup_fmap Heq /= in Heidx1. inversion Heidx1. done. }
      rewrite lookup_omo_ro_event /omo_read_op list_lookup_fmap Heq /= in Heidx1.
      iDestruct (big_sepL_lookup with "BIG") as (?) "[#EL@e1' %EQ]"; [done|].
      iDestruct (mono_list_idx_agree with "EL@e1 EL@e1'") as %<-. rewrite EQ. done. }
  iAssert (⌜ winfo2.2 = einfo2.1.2 ⌝)%I with "[-]" as %EQgen2.
  { destruct (omo !! gen2) as [[e es]|] eqn:Heq; last first.
    { apply lookup_ge_None_1 in Heq. apply lookup_omo_lt_Some in Heidx2. lia. }
    iDestruct (big_sepL2_lookup with "WL✓") as (????) "([%EQ1 %EQ2] & RL● & #EL@e & BIG)"; [done|done|].
    inversion EQ1. subst e0 es0 winfo2. clear EQ1. simpl.
    destruct (decide (e2 = e)) as [->|NEQ].
    - iDestruct (mono_list_idx_agree with "EL@e2 EL@e") as %<-. done.
    - destruct eidx2; last first.
      { rewrite lookup_omo_wr_event /omo_write_op list_lookup_fmap Heq /= in Heidx2. inversion Heidx2. done. }
      rewrite lookup_omo_ro_event /omo_read_op list_lookup_fmap Heq /= in Heidx2.
      iDestruct (big_sepL_lookup with "BIG") as (?) "[#EL@e2' %EQ]"; [done|].
      iDestruct (mono_list_idx_agree with "EL@e2 EL@e2'") as %<-. rewrite EQ. done. }

  unfold OmoAuth_qg_mono in *.
  have CASE : gen1 < gen2 ∨ gen1 = gen2 ∨ gen2 < gen1 by lia.
  destruct CASE as [COMP|[EQ|COMP]]; [done|..].
  - rewrite -EQ Hwinfo1 in Hwinfo2. inversion Hwinfo2. subst winfo2. clear Hwinfo2.
    rewrite -EQgen1 -EQgen2 in LT. by apply Qp.lt_strict in LT.
  - specialize (MONOqg _ _ _ _ Hwinfo2 Hwinfo1 COMP). rewrite EQgen1 EQgen2 in MONOqg.
    apply Qp.lt_nge in MONOqg. apply Qp.lt_le_incl in LT. done.
Qed.

Lemma OmoLe_get γe γs q E omo stlist eidx1 eidx2 e1 e2 `{Interpretable eventT absStateT} :
  lookup_omo omo eidx1 = Some e1 →
  lookup_omo omo eidx2 = Some e2 →
  (gen_of eidx1 ≤ gen_of eidx2)%nat →
  OmoAuth γe γs q E omo stlist _ -∗
  OmoLe γe e1 e2.
Proof.
  iIntros "%Heidx1 %Heidx2 %LT M●". rewrite OmoAuth_eq OmoLe_eq.
  iDestruct "M●" as (??????????)
    "(%&%& [%Hγe %Hγs] & TL● & EL● & WL● & SL● & Hγq & HL● & Hγg & EL✓ & WL✓ & #ELEMS & #KEYS & Pures)".
  iDestruct "Pures" as %(EQlenTL & EQlenEL & E_TL_VALID & E_EL_VALID & MONOqg & QM_VALID & Nomo & NE & HWF & LHB & OMO_GOOD).
  eapply lookup_omo_event_valid in Heidx1 as He1; [|done]. rewrite lookup_lt_is_Some in He1.
  eapply lookup_omo_event_valid in Heidx2 as He2; [|done]. rewrite lookup_lt_is_Some in He2.
  have [einfo1 Heinfo1] : is_Some (EL !! e1) by rewrite lookup_lt_is_Some -EQlenEL.
  have [einfo2 Heinfo2] : is_Some (EL !! e2) by rewrite lookup_lt_is_Some -EQlenEL.
  iDestruct (mono_list_lb_own_get with "EL●") as "#EL◯".
  iDestruct (@mono_list_idx_own_get _ _ _ _ _ e1 with "EL◯") as "#EL@e1"; [done|].
  iDestruct (@mono_list_idx_own_get _ _ _ _ _ e2 with "EL◯") as "#EL@e2"; [done|].
  iDestruct (big_sepL2_length with "WL✓") as %EQlenWL.

  set gen1 := gen_of eidx1.
  set gen2 := gen_of eidx2.
  have [winfo1 Hwinfo1] : is_Some (WL !! gen1).
  { rewrite lookup_lt_is_Some -EQlenWL. apply lookup_omo_lt_Some in Heidx1. done. }
  have [winfo2 Hwinfo2] : is_Some (WL !! gen2).
  { rewrite lookup_lt_is_Some -EQlenWL. apply lookup_omo_lt_Some in Heidx2. done. }
  iAssert (⌜ winfo1.2 = einfo1.1.2 ⌝)%I with "[-]" as %EQgen1.
  { destruct (omo !! gen1) as [[e es]|] eqn:Heq; last first.
    { apply lookup_ge_None_1 in Heq. apply lookup_omo_lt_Some in Heidx1. lia. }
    iDestruct (big_sepL2_lookup with "WL✓") as (????) "([%EQ1 %EQ2] & RL● & #EL@e & BIG)"; [done|done|].
    inversion EQ1. subst e0 es0 winfo1. clear EQ1. simpl.
    destruct (decide (e1 = e)) as [->|NEQ].
    - iDestruct (mono_list_idx_agree with "EL@e1 EL@e") as %<-. done.
    - destruct eidx1; last first.
      { rewrite lookup_omo_wr_event /omo_write_op list_lookup_fmap Heq /= in Heidx1. inversion Heidx1. done. }
      rewrite lookup_omo_ro_event /omo_read_op list_lookup_fmap Heq /= in Heidx1.
      iDestruct (big_sepL_lookup with "BIG") as (?) "[#EL@e1' %EQ]"; [done|].
      iDestruct (mono_list_idx_agree with "EL@e1 EL@e1'") as %<-. rewrite EQ. done. }
  iAssert (⌜ winfo2.2 = einfo2.1.2 ⌝)%I with "[-]" as %EQgen2.
  { destruct (omo !! gen2) as [[e es]|] eqn:Heq; last first.
    { apply lookup_ge_None_1 in Heq. apply lookup_omo_lt_Some in Heidx2. lia. }
    iDestruct (big_sepL2_lookup with "WL✓") as (????) "([%EQ1 %EQ2] & RL● & #EL@e & BIG)"; [done|done|].
    inversion EQ1. subst e0 es0 winfo2. clear EQ1. simpl.
    destruct (decide (e2 = e)) as [->|NEQ].
    - iDestruct (mono_list_idx_agree with "EL@e2 EL@e") as %<-. done.
    - destruct eidx2; last first.
      { rewrite lookup_omo_wr_event /omo_write_op list_lookup_fmap Heq /= in Heidx2. inversion Heidx2. done. }
      rewrite lookup_omo_ro_event /omo_read_op list_lookup_fmap Heq /= in Heidx2.
      iDestruct (big_sepL_lookup with "BIG") as (?) "[#EL@e2' %EQ]"; [done|].
      iDestruct (mono_list_idx_agree with "EL@e2 EL@e2'") as %<-. rewrite EQ. done. }

  have LE : (einfo1.1.2 ≤ einfo2.1.2)%Qp.
  { destruct (decide (gen1 = gen2)) as [EQ|NEQ].
    - rewrite -EQ Hwinfo1 in Hwinfo2. inversion Hwinfo2. subst winfo2. rewrite -EQgen1 -EQgen2. done.
    - unfold OmoAuth_qg_mono in *.
      have CONDLT : gen1 < gen2 by lia.
      specialize (MONOqg _ _ _ _ Hwinfo1 Hwinfo2 CONDLT). rewrite -EQgen1 -EQgen2. apply Qp.lt_le_incl. done. }

  iExists γtl,γel,γh,γg,γn,einfo1,einfo2. iFrame "#". iPureIntro. done.
Qed.

Lemma OmoLe_get_from_HbToken γe γs E omo stlist eidx1 eidx2 e1 e2 e3 `{Interpretable eventT absStateT} :
  lookup_omo omo eidx1 = Some e1 →
  lookup_omo omo eidx2 = Some e2 →
  (gen_of eidx1 ≤ gen_of eidx2)%nat →
  OmoHbToken γe γs E omo stlist e3 _ -∗
  OmoLe γe e1 e2.
Proof.
  iIntros "%Heidx1 %Heidx2 %LT M●". rewrite OmoHbToken_eq OmoLe_eq.
  iDestruct "M●" as (??????????)
    "(%&%&%&%& [%Hγe %Hγs] & TL● & EL● & WL● & SL● & Hγq & GL● & HL● & Hγg & EL✓ & WL✓ & #ELEMS & #KEYS & #BIG' & Pures)".
  iDestruct "Pures" as %(EQlenTL & EQlenEL & EQe & LASTEL & E_TL_VALID & E_EL_VALID & MONOqg & QM_VALID & Nomo & NE & HWF & LHB & OMO_GOOD).
  eapply lookup_omo_event_valid in Heidx1 as He1; [|done]. rewrite lookup_lt_is_Some in He1.
  eapply lookup_omo_event_valid in Heidx2 as He2; [|done]. rewrite lookup_lt_is_Some in He2.
  have [einfo1 Heinfo1] : is_Some (EL !! e1) by rewrite lookup_lt_is_Some -EQlenEL.
  have [einfo2 Heinfo2] : is_Some (EL !! e2) by rewrite lookup_lt_is_Some -EQlenEL.
  iDestruct (mono_list_lb_own_get with "EL●") as "#EL◯".
  iDestruct (@mono_list_idx_own_get _ _ _ _ _ e1 with "EL◯") as "#EL@e1"; [done|].
  iDestruct (@mono_list_idx_own_get _ _ _ _ _ e2 with "EL◯") as "#EL@e2"; [done|].
  iDestruct (big_sepL2_length with "WL✓") as %EQlenWL.

  set gen1 := gen_of eidx1.
  set gen2 := gen_of eidx2.
  have [winfo1 Hwinfo1] : is_Some (WL !! gen1).
  { rewrite lookup_lt_is_Some -EQlenWL. apply lookup_omo_lt_Some in Heidx1. done. }
  have [winfo2 Hwinfo2] : is_Some (WL !! gen2).
  { rewrite lookup_lt_is_Some -EQlenWL. apply lookup_omo_lt_Some in Heidx2. done. }
  iAssert (⌜ winfo1.2 = einfo1.1.2 ⌝)%I with "[-]" as %EQgen1.
  { destruct (omo !! gen1) as [[e es]|] eqn:Heq; last first.
    { apply lookup_ge_None_1 in Heq. apply lookup_omo_lt_Some in Heidx1. lia. }
    iDestruct (big_sepL2_lookup with "WL✓") as (????) "([%EQ1 %EQ2] & RL● & #EL@e & BIG)"; [done|done|].
    inversion EQ1. subst e0 es0 winfo1. clear EQ1. simpl.
    destruct (decide (e1 = e)) as [->|NEQ].
    - iDestruct (mono_list_idx_agree with "EL@e1 EL@e") as %<-. done.
    - destruct eidx1; last first.
      { rewrite lookup_omo_wr_event /omo_write_op list_lookup_fmap Heq /= in Heidx1. inversion Heidx1. done. }
      rewrite lookup_omo_ro_event /omo_read_op list_lookup_fmap Heq /= in Heidx1.
      iDestruct (big_sepL_lookup with "BIG") as (?) "[#EL@e1' %EQ]"; [done|].
      iDestruct (mono_list_idx_agree with "EL@e1 EL@e1'") as %<-. rewrite EQ. done. }
  iAssert (⌜ winfo2.2 = einfo2.1.2 ⌝)%I with "[-]" as %EQgen2.
  { destruct (omo !! gen2) as [[e es]|] eqn:Heq; last first.
    { apply lookup_ge_None_1 in Heq. apply lookup_omo_lt_Some in Heidx2. lia. }
    iDestruct (big_sepL2_lookup with "WL✓") as (????) "([%EQ1 %EQ2] & RL● & #EL@e & BIG)"; [done|done|].
    inversion EQ1. subst e0 es0 winfo2. clear EQ1. simpl.
    destruct (decide (e2 = e)) as [->|NEQ].
    - iDestruct (mono_list_idx_agree with "EL@e2 EL@e") as %<-. done.
    - destruct eidx2; last first.
      { rewrite lookup_omo_wr_event /omo_write_op list_lookup_fmap Heq /= in Heidx2. inversion Heidx2. done. }
      rewrite lookup_omo_ro_event /omo_read_op list_lookup_fmap Heq /= in Heidx2.
      iDestruct (big_sepL_lookup with "BIG") as (?) "[#EL@e2' %EQ]"; [done|].
      iDestruct (mono_list_idx_agree with "EL@e2 EL@e2'") as %<-. rewrite EQ. done. }

  have LE : (einfo1.1.2 ≤ einfo2.1.2)%Qp.
  { destruct (decide (gen1 = gen2)) as [EQ|NEQ].
    - rewrite -EQ Hwinfo1 in Hwinfo2. inversion Hwinfo2. subst winfo2. rewrite -EQgen1 -EQgen2. done.
    - unfold OmoAuth_qg_mono in *.
      have CONDLT : gen1 < gen2 by lia.
      specialize (MONOqg _ _ _ _ Hwinfo1 Hwinfo2 CONDLT). rewrite -EQgen1 -EQgen2. apply Qp.lt_le_incl. done. }

  iExists γtl,γel,γh,γg,γn,einfo1,einfo2. iFrame "#". iPureIntro. done.
Qed.

Lemma OmoAuth_OmoLe γe γs q E omo stlist e1 e2 `{Interpretable eventT absStateT} :
  OmoAuth γe γs q E omo stlist _ -∗
  OmoLe γe e1 e2 -∗
  ⌜ is_Some (E !! e1) ∧ is_Some (E !! e2) ⌝.
Proof.
  iIntros "M● #e1≤e2". rewrite OmoAuth_eq OmoLe_eq.
  iDestruct "M●" as (??????????)
    "(%&%& [%Hγe %Hγs] & TL● & EL● & WL● & SL● & Hγq & HL● & Hγg & EL✓ & WL✓ & #ELEMS & #KEYS & Pures)".
  iDestruct "Pures" as %(EQlenTL & EQlenEL & E_TL_VALID & E_EL_VALID & MONOqg & QM_VALID & Nomo & NE & HWF & LHB & OMO_GOOD).
  iDestruct "e1≤e2" as (???????) "([%Hγe' %LE] & #EL@e1 & #EL@e2)". encode_agree Hγe.
  iDestruct (mono_list_auth_idx_lookup with "EL● EL@e1") as %He1%lookup_lt_Some.
  iDestruct (mono_list_auth_idx_lookup with "EL● EL@e2") as %He2%lookup_lt_Some.
  iPureIntro. rewrite !lookup_lt_is_Some !EQlenEL. done.
Qed.

Lemma OmoAuth_OmoLe_l γe γs q E omo stlist e1 e2 `{Interpretable eventT absStateT} :
  OmoAuth γe γs q E omo stlist _ -∗
  OmoLe γe e1 e2 -∗
  ∃ eidx, ⌜ lookup_omo omo eidx = Some e1 ⌝.
Proof.
  iIntros "M● #e1≤e2". iDestruct (OmoAuth_OmoLe with "M● e1≤e2") as %[He1 _].
  iDestruct (OmoAuth_wf with "M●") as %[OMO_GOOD _].
  eapply lookup_omo_surjective in He1; [|done]. done.
Qed.

Lemma OmoAuth_OmoLe_r γe γs q E omo stlist e1 e2 `{Interpretable eventT absStateT} :
  OmoAuth γe γs q E omo stlist _ -∗
  OmoLe γe e1 e2 -∗
  ∃ eidx, ⌜ lookup_omo omo eidx = Some e2 ⌝.
Proof.
  iIntros "M● #e1≤e2". iDestruct (OmoAuth_OmoLe with "M● e1≤e2") as %[_ He2].
  iDestruct (OmoAuth_wf with "M●") as %[OMO_GOOD _].
  eapply lookup_omo_surjective in He2; [|done]. done.
Qed.

Lemma OmoLe_Le γe γs q E omo stlist eidx1 eidx2 e1 e2 `{Interpretable eventT absStateT} :
  lookup_omo omo eidx1 = Some e1 →
  lookup_omo omo eidx2 = Some e2 →
  OmoAuth γe γs q E omo stlist _ -∗
  OmoLe γe e1 e2 -∗
  ⌜ (gen_of eidx1 ≤ gen_of eidx2)%nat ⌝.
Proof.
  iIntros "%Heidx1 %Heidx2 M● #e1≤e2". rewrite OmoAuth_eq OmoLe_eq.
  iDestruct "M●" as (??????????)
    "(%&%& [%Hγe %Hγs] & TL● & EL● & WL● & SL● & Hγq & HL● & Hγg & EL✓ & WL✓ & #ELEMS & #KEYS & Pures)".
  iDestruct "Pures" as %(EQlenTL & EQlenEL & E_TL_VALID & E_EL_VALID & MONOqg & QM_VALID & Nomo & NE & HWF & LHB & OMO_GOOD).
  iDestruct "e1≤e2" as (???????) "([%Hγe' %LE] & #EL@e1 & #EL@e2)". encode_agree Hγe.
  iDestruct (big_sepL2_length with "WL✓") as %EQlenWL.

  set gen1 := gen_of eidx1.
  set gen2 := gen_of eidx2.
  have [winfo1 Hwinfo1] : is_Some (WL !! gen1).
  { rewrite lookup_lt_is_Some -EQlenWL. apply lookup_omo_lt_Some in Heidx1. done. }
  have [winfo2 Hwinfo2] : is_Some (WL !! gen2).
  { rewrite lookup_lt_is_Some -EQlenWL. apply lookup_omo_lt_Some in Heidx2. done. }
  iAssert (⌜ winfo1.2 = einfo1.1.2 ⌝)%I with "[-]" as %EQgen1.
  { destruct (omo !! gen1) as [[e es]|] eqn:Heq; last first.
    { apply lookup_ge_None_1 in Heq. apply lookup_omo_lt_Some in Heidx1. lia. }
    iDestruct (big_sepL2_lookup with "WL✓") as (????) "([%EQ1 %EQ2] & RL● & #EL@e & BIG)"; [done|done|].
    inversion EQ1. subst e0 es0 winfo1. clear EQ1. simpl.
    destruct (decide (e1 = e)) as [->|NEQ].
    - iDestruct (mono_list_idx_agree with "EL@e1 EL@e") as %<-. done.
    - destruct eidx1; last first.
      { rewrite lookup_omo_wr_event /omo_write_op list_lookup_fmap Heq /= in Heidx1. inversion Heidx1. done. }
      rewrite lookup_omo_ro_event /omo_read_op list_lookup_fmap Heq /= in Heidx1.
      iDestruct (big_sepL_lookup with "BIG") as (?) "[#EL@e1' %EQ]"; [done|].
      iDestruct (mono_list_idx_agree with "EL@e1 EL@e1'") as %<-. rewrite EQ. done. }
  iAssert (⌜ winfo2.2 = einfo2.1.2 ⌝)%I with "[-]" as %EQgen2.
  { destruct (omo !! gen2) as [[e es]|] eqn:Heq; last first.
    { apply lookup_ge_None_1 in Heq. apply lookup_omo_lt_Some in Heidx2. lia. }
    iDestruct (big_sepL2_lookup with "WL✓") as (????) "([%EQ1 %EQ2] & RL● & #EL@e & BIG)"; [done|done|].
    inversion EQ1. subst e0 es0 winfo2. clear EQ1. simpl.
    destruct (decide (e2 = e)) as [->|NEQ].
    - iDestruct (mono_list_idx_agree with "EL@e2 EL@e") as %<-. done.
    - destruct eidx2; last first.
      { rewrite lookup_omo_wr_event /omo_write_op list_lookup_fmap Heq /= in Heidx2. inversion Heidx2. done. }
      rewrite lookup_omo_ro_event /omo_read_op list_lookup_fmap Heq /= in Heidx2.
      iDestruct (big_sepL_lookup with "BIG") as (?) "[#EL@e2' %EQ]"; [done|].
      iDestruct (mono_list_idx_agree with "EL@e2 EL@e2'") as %<-. rewrite EQ. done. }

  unfold OmoAuth_qg_mono in *. destruct (le_lt_dec gen1 gen2) as [COMP|COMP]; [done|].
  specialize (MONOqg _ _ _ _ Hwinfo2 Hwinfo1 COMP).
  rewrite EQgen1 EQgen2 in MONOqg. apply Qp.lt_nge in MONOqg. done.
Qed.

Lemma OmoLe_get_append_w γe γs q E omo stlist e e' es eV' `{Interpretable eventT absStateT} :
  OmoAuth γe γs q E (omo_append_w omo e es) stlist _ -∗
  OmoEinfo γe e' eV' -∗
  OmoLe γe e' e.
Proof.
  iIntros "M● #e'✓eV'".
  iDestruct (OmoAuth_OmoEinfo' with "M● e'✓eV'") as %[eidx' Heidx'].

  set eidx := wr_event (length omo).
  set omo' := omo_append_w omo e es.
  have Heidx : lookup_omo omo' eidx = Some e.
  { subst omo' eidx. rewrite lookup_omo_wr_event omo_append_w_write_op omo_write_op_length lookup_app_1_eq. done. }
  iApply (OmoLe_get with "M●"); try done.
  subst eidx. simpl. apply lookup_omo_lt_Some in Heidx'. rewrite omo_append_w_length in Heidx'. lia.
Qed.

Lemma OmoEq_get γe γs q E omo stlist eidx1 eidx2 e1 e2 `{Interpretable eventT absStateT} :
  lookup_omo omo eidx1 = Some e1 →
  lookup_omo omo eidx2 = Some e2 →
  gen_of eidx1 = gen_of eidx2 →
  OmoAuth γe γs q E omo stlist _ -∗
  OmoEq γe e1 e2.
Proof.
  iIntros "%Heidx1 %Heidx2 %EQ M●". rewrite OmoAuth_eq OmoEq_eq.
  iDestruct "M●" as (??????????)
    "(%&%& [%Hγe %Hγs] & TL● & EL● & WL● & SL● & Hγq & HL● & Hγg & EL✓ & WL✓ & #ELEMS & #KEYS & Pures)".
  iDestruct "Pures" as %(EQlenTL & EQlenEL & E_TL_VALID & E_EL_VALID & MONOqg & QM_VALID & Nomo & NE & HWF & LHB & OMO_GOOD).
  eapply lookup_omo_event_valid in Heidx1 as He1; [|done]. rewrite lookup_lt_is_Some in He1.
  eapply lookup_omo_event_valid in Heidx2 as He2; [|done]. rewrite lookup_lt_is_Some in He2.
  have [einfo1 Heinfo1] : is_Some (EL !! e1) by rewrite lookup_lt_is_Some -EQlenEL.
  have [einfo2 Heinfo2] : is_Some (EL !! e2) by rewrite lookup_lt_is_Some -EQlenEL.
  iDestruct (mono_list_lb_own_get with "EL●") as "#EL◯".
  iDestruct (@mono_list_idx_own_get _ _ _ _ _ e1 with "EL◯") as "#EL@e1"; [done|].
  iDestruct (@mono_list_idx_own_get _ _ _ _ _ e2 with "EL◯") as "#EL@e2"; [done|].
  iDestruct (big_sepL2_length with "WL✓") as %EQlenWL.

  set gen1 := gen_of eidx1.
  set gen2 := gen_of eidx2.
  have [winfo1 Hwinfo1] : is_Some (WL !! gen1).
  { rewrite lookup_lt_is_Some -EQlenWL. apply lookup_omo_lt_Some in Heidx1. done. }
  have [winfo2 Hwinfo2] : is_Some (WL !! gen2).
  { rewrite lookup_lt_is_Some -EQlenWL. apply lookup_omo_lt_Some in Heidx2. done. }
  iAssert (⌜ winfo1.2 = einfo1.1.2 ⌝)%I with "[-]" as %EQgen1.
  { destruct (omo !! gen1) as [[e es]|] eqn:Heq; last first.
    { apply lookup_ge_None_1 in Heq. apply lookup_omo_lt_Some in Heidx1. lia. }
    iDestruct (big_sepL2_lookup with "WL✓") as (????) "([%EQ1 %EQ2] & RL● & #EL@e & BIG)"; [done|done|].
    inversion EQ1. subst e0 es0 winfo1. clear EQ1. simpl.
    destruct (decide (e1 = e)) as [->|NEQ].
    - iDestruct (mono_list_idx_agree with "EL@e1 EL@e") as %<-. done.
    - destruct eidx1; last first.
      { rewrite lookup_omo_wr_event /omo_write_op list_lookup_fmap Heq /= in Heidx1. inversion Heidx1. done. }
      rewrite lookup_omo_ro_event /omo_read_op list_lookup_fmap Heq /= in Heidx1.
      iDestruct (big_sepL_lookup with "BIG") as (?) "[#EL@e1' %EQ']"; [done|].
      iDestruct (mono_list_idx_agree with "EL@e1 EL@e1'") as %<-. rewrite EQ'. done. }
  iAssert (⌜ winfo2.2 = einfo2.1.2 ⌝)%I with "[-]" as %EQgen2.
  { destruct (omo !! gen2) as [[e es]|] eqn:Heq; last first.
    { apply lookup_ge_None_1 in Heq. apply lookup_omo_lt_Some in Heidx2. lia. }
    iDestruct (big_sepL2_lookup with "WL✓") as (????) "([%EQ1 %EQ2] & RL● & #EL@e & BIG)"; [done|done|].
    inversion EQ1. subst e0 es0 winfo2. clear EQ1. simpl.
    destruct (decide (e2 = e)) as [->|NEQ].
    - iDestruct (mono_list_idx_agree with "EL@e2 EL@e") as %<-. done.
    - destruct eidx2; last first.
      { rewrite lookup_omo_wr_event /omo_write_op list_lookup_fmap Heq /= in Heidx2. inversion Heidx2. done. }
      rewrite lookup_omo_ro_event /omo_read_op list_lookup_fmap Heq /= in Heidx2.
      iDestruct (big_sepL_lookup with "BIG") as (?) "[#EL@e2' %EQ']"; [done|].
      iDestruct (mono_list_idx_agree with "EL@e2 EL@e2'") as %<-. rewrite EQ'. done. }

  iExists γtl,γel,γh,γg,γn,einfo1,einfo2. iFrame "#". iPureIntro. split; [done|].
  subst gen1 gen2. rewrite -EQ Hwinfo1 in Hwinfo2. inversion Hwinfo2. subst winfo2. rewrite -EQgen1 -EQgen2. done.
Qed.

Lemma OmoAuth_OmoEq γe γs q E omo stlist e1 e2 `{Interpretable eventT absStateT} :
  OmoAuth γe γs q E omo stlist _ -∗
  OmoEq γe e1 e2 -∗
  ⌜ is_Some (E !! e1) ∧ is_Some (E !! e2) ⌝.
Proof.
  iIntros "M● #e1=e2".
  iDestruct (OmoLe_get_from_Eq with "e1=e2") as "e1≤e2".
  by iApply (OmoAuth_OmoLe with "M● e1≤e2").
Qed.

Lemma OmoAuth_OmoEq_l γe γs q E omo stlist e1 e2 `{Interpretable eventT absStateT} :
  OmoAuth γe γs q E omo stlist _ -∗
  OmoEq γe e1 e2 -∗
  ∃ eidx, ⌜ lookup_omo omo eidx = Some e1 ⌝.
Proof.
  iIntros "M● #e1=e2".
  iDestruct (OmoLe_get_from_Eq with "e1=e2") as "e1≤e2".
  by iApply (OmoAuth_OmoLe_l with "M● e1≤e2").
Qed.

Lemma OmoAuth_OmoEq_r γe γs q E omo stlist e1 e2 `{Interpretable eventT absStateT} :
  OmoAuth γe γs q E omo stlist _ -∗
  OmoEq γe e1 e2 -∗
  ∃ eidx, ⌜ lookup_omo omo eidx = Some e2 ⌝.
Proof.
  iIntros "M● #e1=e2".
  iDestruct (OmoLe_get_from_Eq with "e1=e2") as "e1≤e2".
  by iApply (OmoAuth_OmoLe_r with "M● e1≤e2").
Qed.

Lemma OmoEq_get_from_Einfo γe e eV :
  OmoEinfo γe e eV -∗
  OmoEq γe e e.
Proof.
  iIntros "#e✓eV". rewrite OmoEinfo_eq OmoEq_eq.
  iDestruct "e✓eV" as (???????) "((%Hγe & %Hty & %Hdv & %Hlv) & TL@e & EL@e & HL@e & MAXgen & EVIEW)".
  iExists γtl,γel,γh,γg,γn,einfo,einfo. iFrame "#". done.
Qed.

Lemma OmoEq_same γe γs q E omo stlist e `{Interpretable eventT absStateT} :
  is_Some (E !! e) →
  OmoAuth γe γs q E omo stlist _ -∗
  OmoEq γe e e.
Proof.
  iIntros "%He M●". iDestruct (OmoEinfo_get' with "M●") as (eV) "#e✓eV"; [done|].
  by iApply (OmoEq_get_from_Einfo with "e✓eV").
Qed.

Lemma OmoEq_Eq γe γs q E omo stlist eidx1 eidx2 e1 e2 `{Interpretable eventT absStateT} :
  lookup_omo omo eidx1 = Some e1 →
  lookup_omo omo eidx2 = Some e2 →
  OmoAuth γe γs q E omo stlist _ -∗
  OmoEq γe e1 e2 -∗
  ⌜ (gen_of eidx1 = gen_of eidx2)%nat ⌝.
Proof.
  iIntros "%Heidx1 %Heidx2 M● #e1=e2". rewrite OmoAuth_eq OmoEq_eq.
  iDestruct "M●" as (??????????)
    "(%&%& [%Hγe %Hγs] & TL● & EL● & WL● & SL● & Hγq & HL● & Hγg & EL✓ & WL✓ & #ELEMS & #KEYS & Pures)".
  iDestruct "Pures" as %(EQlenTL & EQlenEL & E_TL_VALID & E_EL_VALID & MONOqg & QM_VALID & Nomo & NE & HWF & LHB & OMO_GOOD).
  iDestruct "e1=e2" as (???????) "([%Hγe' %EQ] & #EL@e1 & #EL@e2)". encode_agree Hγe.
  iDestruct (big_sepL2_length with "WL✓") as %EQlenWL.

  set gen1 := gen_of eidx1.
  set gen2 := gen_of eidx2.
  have [winfo1 Hwinfo1] : is_Some (WL !! gen1).
  { rewrite lookup_lt_is_Some -EQlenWL. apply lookup_omo_lt_Some in Heidx1. done. }
  have [winfo2 Hwinfo2] : is_Some (WL !! gen2).
  { rewrite lookup_lt_is_Some -EQlenWL. apply lookup_omo_lt_Some in Heidx2. done. }
  iAssert (⌜ winfo1.2 = einfo1.1.2 ⌝)%I with "[-]" as %EQgen1.
  { destruct (omo !! gen1) as [[e es]|] eqn:Heq; last first.
    { apply lookup_ge_None_1 in Heq. apply lookup_omo_lt_Some in Heidx1. lia. }
    iDestruct (big_sepL2_lookup with "WL✓") as (????) "([%EQ1 %EQ2] & RL● & #EL@e & BIG)"; [done|done|].
    inversion EQ1. subst e0 es0 winfo1. clear EQ1. simpl.
    destruct (decide (e1 = e)) as [->|NEQ].
    - iDestruct (mono_list_idx_agree with "EL@e1 EL@e") as %<-. done.
    - destruct eidx1; last first.
      { rewrite lookup_omo_wr_event /omo_write_op list_lookup_fmap Heq /= in Heidx1. inversion Heidx1. done. }
      rewrite lookup_omo_ro_event /omo_read_op list_lookup_fmap Heq /= in Heidx1.
      iDestruct (big_sepL_lookup with "BIG") as (?) "[#EL@e1' %EQ']"; [done|].
      iDestruct (mono_list_idx_agree with "EL@e1 EL@e1'") as %<-. rewrite EQ'. done. }
  iAssert (⌜ winfo2.2 = einfo2.1.2 ⌝)%I with "[-]" as %EQgen2.
  { destruct (omo !! gen2) as [[e es]|] eqn:Heq; last first.
    { apply lookup_ge_None_1 in Heq. apply lookup_omo_lt_Some in Heidx2. lia. }
    iDestruct (big_sepL2_lookup with "WL✓") as (????) "([%EQ1 %EQ2] & RL● & #EL@e & BIG)"; [done|done|].
    inversion EQ1. subst e0 es0 winfo2. clear EQ1. simpl.
    destruct (decide (e2 = e)) as [->|NEQ].
    - iDestruct (mono_list_idx_agree with "EL@e2 EL@e") as %<-. done.
    - destruct eidx2; last first.
      { rewrite lookup_omo_wr_event /omo_write_op list_lookup_fmap Heq /= in Heidx2. inversion Heidx2. done. }
      rewrite lookup_omo_ro_event /omo_read_op list_lookup_fmap Heq /= in Heidx2.
      iDestruct (big_sepL_lookup with "BIG") as (?) "[#EL@e2' %EQ']"; [done|].
      iDestruct (mono_list_idx_agree with "EL@e2 EL@e2'") as %<-. rewrite EQ'. done. }

  unfold OmoAuth_qg_mono in *.
  have CASE : gen1 < gen2 ∨ gen1 = gen2 ∨ gen2 < gen1 by lia.
  destruct CASE as [COMP|[COMP|COMP]]; try done.
  - specialize (MONOqg _ _ _ _ Hwinfo1 Hwinfo2 COMP). rewrite EQgen1 EQgen2 EQ in MONOqg. by apply Qp.lt_strict in MONOqg.
  - specialize (MONOqg _ _ _ _ Hwinfo2 Hwinfo1 COMP). rewrite EQgen1 EQgen2 EQ in MONOqg. by apply Qp.lt_strict in MONOqg.
Qed.

Lemma OmoSnap_get γe γs q E omo stlist e eidx gen st `{Interpretable eventT absStateT} :
  stlist !! gen = Some st →
  lookup_omo omo eidx = Some e →
  gen_of eidx = gen →
  OmoAuth γe γs q E omo stlist _ -∗
  OmoSnap γe γs e st.
Proof.
  iIntros "%Hst %Heidx %Hgen M●". rewrite OmoAuth_eq OmoSnap_eq.
  iDestruct "M●" as (??????????)
    "(%&%& [%Hγe %Hγs] & TL● & EL● & WL● & SL● & Hγq & HL● & Hγg & EL✓ & WL✓ & #ELEMS & #KEYS & Pures)".
  iDestruct "Pures" as %(EQlenTL & EQlenEL & E_TL_VALID & E_EL_VALID & MONOqg & QM_VALID & Nomo & NE & HWF & LHB & OMO_GOOD).
  iDestruct (big_sepL2_length with "WL✓") as %EQlenWL.
  apply omo_stlist_length in OMO_GOOD as EQlenst.
  eapply lookup_omo_event_valid in Heidx as He; [|done]. destruct He as [eV HeV].

  have [einfo Heinfo] : is_Some (EL !! e).
  { rewrite lookup_lt_is_Some -EQlenEL. apply lookup_lt_Some in HeV. done. }
  have [winfo Hwinfo] : is_Some (WL !! gen).
  { rewrite lookup_lt_is_Some -EQlenWL -Hgen. apply lookup_omo_lt_Some in Heidx. done. }

  iDestruct (mono_list_lb_own_get with "EL●") as "#EL◯".
  iDestruct (mono_list_lb_own_get with "WL●") as "#WL◯".
  iDestruct (mono_list_lb_own_get with "SL●") as "#SL◯".
  iDestruct (@mono_list_idx_own_get _ _ _ _ _ e with "EL◯") as "EL@e"; [done|].
  iDestruct (@mono_list_idx_own_get _ _ _ _ _ gen with "WL◯") as "WL@gen"; [done|].
  iDestruct (@mono_list_idx_own_get _ _ _ _ _ gen with "SL◯") as "SL@gen"; [done|].

  iAssert (⌜ winfo.2 = einfo.1.2 ⌝)%I with "[-]" as %EQgen.
  { destruct (omo !! gen) as [[e' es']|] eqn:Heq; last first.
    { apply lookup_ge_None_1 in Heq. apply lookup_omo_lt_Some in Heidx. rewrite Hgen in Heidx. lia. }
    iDestruct (big_sepL2_lookup with "WL✓") as (??? einfo') "([%EQ1 %EQ2] & RL● & #EL@e' & BIG)"; [done|done|].
    inversion EQ1. subst e0 es winfo. clear EQ1. simpl. destruct (decide (e = e')) as [<-|NEQ].
    - iDestruct (mono_list_idx_agree with "EL@e EL@e'") as %<-. done.
    - destruct eidx; last first.
      { simpl in Hgen. rewrite lookup_omo_wr_event /omo_write_op list_lookup_fmap Hgen Heq /= in Heidx. inversion Heidx. done. }
      simpl in Hgen. rewrite lookup_omo_ro_event /omo_read_op list_lookup_fmap Hgen Heq /= in Heidx.
      iDestruct (big_sepL_lookup with "BIG") as (?) "[#EL@ea %EQ]"; [done|].
      iDestruct (mono_list_idx_agree with "EL@e EL@ea") as %<-. done. }

  unfold OmoAuth_QM_valid in *.
  have LOOKUP : WL.*2 !! gen = Some winfo.2 by rewrite list_lookup_fmap Hwinfo.
  specialize (QM_VALID winfo.2 gen). rewrite QM_VALID in LOOKUP.
  iDestruct (big_sepM_lookup with "KEYS") as "KEY"; [done|].
  rewrite EQgen.

  iExists γtl,γel,γh,γg,γn,γwl,γsl,γq. iExists gen,einfo. iFrame "#". done.
Qed.

Lemma OmoSnap_get_from_Eq γe γs e1 e2 st :
  OmoSnap γe γs e1 st -∗
  OmoEq γe e1 e2 -∗
  OmoSnap γe γs e2 st.
Proof.
  iIntros "#e1↪st #e1=e2". rewrite OmoSnap_eq OmoEq_eq.
  iDestruct "e1↪st" as (??????????) "([%Hγe %Hγs] & #EL@e1 & #KEY & #SL@i)".
  iDestruct "e1=e2" as (???????) "([%Hγe' %EQ] & #EL@e1' & #EL@e2)". encode_agree Hγe.
  iDestruct (mono_list_idx_agree with "EL@e1 EL@e1'") as %<-.
  iExists γtl,γel,γh,γg,γn,γwl,γsl,γq. iExists i,einfo2. rewrite -EQ. iFrame "#". done.
Qed.

Lemma OmoSnap_agree γe γs e st st' :
  OmoSnap γe γs e st -∗
  OmoSnap γe γs e st' -∗
  ⌜ st = st' ⌝.
Proof.
  iIntros "#e↪st #e↪st'". rewrite OmoSnap_eq.
  iDestruct "e↪st" as (??????????) "([%Hγe %Hγs] & #EL@e & #KEY & #SL@i)".
  iDestruct "e↪st'" as (??????????) "([%Hγe' %Hγs'] & #EL@e' & #KEY' & #SL@i')".
  encode_agree Hγe. encode_agree Hγs.
  iDestruct (mono_list_idx_agree with "EL@e EL@e'") as %<-.
  iDestruct (ghost_map_elem_agree with "KEY KEY'") as %<-.
  iDestruct (mono_list_idx_agree with "SL@i SL@i'") as %<-. done.
Qed.

Lemma OmoSnap_agree' γe γs e1 e2 st st' :
  OmoSnap γe γs e1 st -∗
  OmoSnap γe γs e2 st' -∗
  OmoEq γe e1 e2 -∗
  ⌜ st = st' ⌝.
Proof.
  iIntros "#e1↪st #e2↪st' #e1=e2". rewrite OmoSnap_eq OmoEq_eq.
  iDestruct "e1↪st" as (??????????) "([%Hγe %Hγs] & #EL@e1 & #KEY & #SL@i)".
  iDestruct "e2↪st'" as (??????????) "([%Hγe' %Hγs'] & #EL@e2 & #KEY' & #SL@i')".
  encode_agree Hγe. encode_agree Hγs.
  iDestruct "e1=e2" as (???????) "([%Hγe' %EQ] & #EL@e1' & #EL@e2')". encode_agree Hγe.
  iDestruct (mono_list_idx_agree with "EL@e1 EL@e1'") as %->.
  iDestruct (mono_list_idx_agree with "EL@e2 EL@e2'") as %->. rewrite -EQ.
  iDestruct (ghost_map_elem_agree with "KEY KEY'") as %<-.
  iDestruct (mono_list_idx_agree with "SL@i SL@i'") as %<-. done.
Qed.

Lemma OmoAuth_OmoSnap γe γs q E omo stlist e eidx st `{Interpretable eventT absStateT} :
  lookup_omo omo eidx = Some e →
  OmoAuth γe γs q E omo stlist _ -∗
  OmoSnap γe γs e st -∗
  ⌜ stlist !! (gen_of eidx) = Some st ⌝.
Proof.
  iIntros "%Heidx M● #e↪st". rewrite OmoAuth_eq OmoSnap_eq.
  iDestruct "M●" as (??????????)
    "(%&%& [%Hγe %Hγs] & TL● & EL● & WL● & SL● & Hγq & HL● & Hγg & EL✓ & WL✓ & #ELEMS & #KEYS & Pures)".
  iDestruct "Pures" as %(EQlenTL & EQlenEL & E_TL_VALID & E_EL_VALID & MONOqg & QM_VALID & Nomo & NE & HWF & LHB & OMO_GOOD).
  iDestruct "e↪st" as (??????????) "([%Hγe' %Hγs'] & #EL@e & #KEY & #SL@i)".
  encode_agree Hγe. encode_agree Hγs.
  iDestruct (big_sepL2_length with "WL✓") as %EQlenWL.

  iDestruct (ghost_map_lookup with "Hγq KEY") as %LOOKUP.
  unfold OmoAuth_QM_valid in *.
  specialize (QM_VALID einfo.1.2 i).
  rewrite -QM_VALID in LOOKUP.
  apply list_lookup_fmap_inv in LOOKUP as [winfo [EQqg Hwinfo]].

  iDestruct (mono_list_auth_idx_lookup with "SL● SL@i") as %LOOKUP.
  iAssert (⌜ i = gen_of eidx ⌝)%I with "[-]" as %->; [|done].

  unfold OmoAuth_qg_mono in *.
  destruct (omo !! (gen_of eidx)) as [[e' es']|] eqn:Heq; last first.
  { apply lookup_ge_None_1 in Heq. apply lookup_omo_lt_Some in Heidx. lia. }
  have [winfo' Hwinfo'] : is_Some (WL !! (gen_of eidx)).
  { rewrite lookup_lt_is_Some -EQlenWL. apply lookup_lt_Some in Heq. done. }
  iDestruct (big_sepL2_lookup with "WL✓") as (??? einfo') "([%EQ1 %EQ2] & RL● & #EL@e' & BIG)"; [done|done|].
  inversion EQ1. subst e0 es winfo'. clear EQ1.
  iDestruct (mono_list_auth_idx_lookup with "EL● EL@e") as %Heinfo.

  iAssert (⌜ einfo.1.2 = einfo'.1.2 ⌝)%I with "[-]" as %EQqg'.
  { destruct eidx.
    - rewrite lookup_omo_ro_event /omo_read_op list_lookup_fmap Heq /= in Heidx.
      iDestruct (big_sepL_lookup with "BIG") as (?) "[#EL@ea %]"; [done|].
      iDestruct (mono_list_idx_agree with "EL@e EL@ea") as %<-. done.
    - rewrite lookup_omo_wr_event /omo_write_op list_lookup_fmap Heq /= in Heidx. inversion Heidx. subst e'.
      iDestruct (mono_list_idx_agree with "EL@e EL@e'") as %<-. done. }

  have CASE : i < gen_of eidx ∨ i = gen_of eidx ∨ gen_of eidx < i by lia.
  destruct CASE as [COMP|[COMP|COMP]]; try done.
  - specialize (MONOqg _ _ _ _ Hwinfo Hwinfo' COMP). rewrite -EQqg -EQqg' /= in MONOqg. by apply Qp.lt_strict in MONOqg.
  - specialize (MONOqg _ _ _ _ Hwinfo' Hwinfo COMP). rewrite -EQqg -EQqg' /= in MONOqg. by apply Qp.lt_strict in MONOqg.
Qed.

Lemma OmoAuth_OmoSnap' γe γs γs' q E omo stlist e st `{Interpretable eventT absStateT} :
  OmoAuth γe γs q E omo stlist _ -∗
  OmoSnap γe γs' e st -∗
  ⌜ is_Some (E !! e) ⌝.
Proof.
  iIntros "M● #e↪st". rewrite OmoAuth_eq OmoSnap_eq.
  iDestruct "M●" as (??????????)
    "(%&%& [%Hγe %Hγs] & TL● & EL● & WL● & SL● & Hγq & HL● & Hγg & EL✓ & WL✓ & #ELEMS & #KEYS & Pures)".
  iDestruct "Pures" as %(EQlenTL & EQlenEL & E_TL_VALID & E_EL_VALID & MONOqg & QM_VALID & Nomo & NE & HWF & LHB & OMO_GOOD).
  iDestruct "e↪st" as (??????????) "([%Hγe' %Hγs'] & #EL@e & #KEY & #SL@i)". encode_agree Hγe.

  iDestruct (mono_list_auth_idx_lookup with "EL● EL@e") as %He.
  apply lookup_lt_Some in He. iPureIntro. rewrite lookup_lt_is_Some EQlenEL. done.
Qed.

Lemma OmoAuth_OmoSnap'' γe γs γs' q E omo stlist e st `{Interpretable eventT absStateT} :
  OmoAuth γe γs q E omo stlist _ -∗
  OmoSnap γe γs' e st -∗
  ∃ eidx, ⌜ lookup_omo omo eidx = Some e ⌝.
Proof.
  iIntros "M● #e↪st".
  iDestruct (OmoAuth_wf with "M●") as %[OMO_GOOD _].
  iDestruct (OmoAuth_OmoSnap' with "M● e↪st") as %He.
  eapply lookup_omo_surjective in He; [|done]. done.
Qed.

Lemma OmoSnapStates_OmoSnap γe γs omo stlist e eidx st :
  lookup_omo omo eidx = Some e →
  OmoSnapStates γe γs omo stlist -∗
  OmoSnap γe γs e st -∗
  ⌜ stlist !! (gen_of eidx) = Some st ⌝.
Proof.
  iIntros "%Heidx #ST◯ #e↪st". rewrite OmoSnapStates_eq OmoSnap_eq.
  iDestruct "ST◯" as (???) "([%Hγs %EQlenST] & ST◯ & M◯)".
  iDestruct "e↪st" as (??????????) "([%Hγe %Hγs'] & #EL@e & #KEY & #SL@i)". encode_agree Hγs.
  rewrite OmoSnapOmo_eq.
  iDestruct "M◯" as (?????????) "([%Hγe' %Hγs'] & WL◯ & BIG1 & BIG2)". encode_agree Hγe. encode_agree Hγs.

  set gen := gen_of eidx.
  have [[e' es'] Hgen] : is_Some (omo !! gen).
  { rewrite lookup_lt_is_Some. apply lookup_omo_lt_Some in Heidx. done. }
  iDestruct (big_sepL2_length with "BIG1") as %EQlenWL.
  have [winfo Hwinfo] : is_Some (WL !! gen).
  { rewrite lookup_lt_is_Some -EQlenWL. by apply lookup_lt_Some in Hgen. }
  iDestruct (big_sepL2_lookup with "BIG1") as (????) "([%EQ1 %EQ2] & RL◯ & EL@e' & BIGES)"; [done|done|].
  inversion EQ1. subst e0 es winfo. clear EQ1.

  iAssert (⌜ einfo.1.2 = einfo0.1.2 ⌝)%I with "[-]" as %EQqg.
  { destruct eidx.
    - rewrite lookup_omo_ro_event /omo_read_op list_lookup_fmap Hgen /= in Heidx.
      iDestruct (big_sepL_lookup with "BIGES") as (?) "[#EL@ea %EQqg']"; [done|].
      iDestruct (mono_list_idx_agree with "EL@e EL@ea") as %<-. done.
    - rewrite lookup_omo_wr_event /omo_write_op list_lookup_fmap Hgen /= in Heidx. inversion Heidx. subst e'.
      iDestruct (mono_list_idx_agree with "EL@e EL@e'") as %<-. done. }

  rewrite -EQqg in Hwinfo. iDestruct (big_sepL_lookup with "BIG2") as "#KEY'"; [done|]. simpl.
  iDestruct (ghost_map_elem_agree with "KEY KEY'") as %->.
  have [st' Hst'] : is_Some (stlist !! gen).
  { rewrite lookup_lt_is_Some -EQlenST. apply lookup_omo_lt_Some in Heidx. done. }
  iDestruct (@mono_list_idx_own_get _ _ _ _ _ gen with "ST◯") as "SL@gen"; [done|].
  iDestruct (mono_list_idx_agree with "SL@i SL@gen") as %<-. done.
Qed.

Lemma OmoSnapStates_get γe γs q E omo stlist `{Interpretable eventT absStateT} :
  OmoAuth γe γs q E omo stlist _ -∗
  OmoSnapStates γe γs omo stlist.
Proof.
  iIntros "M●".
  iDestruct (OmoSnapOmo_get with "M●") as "#M◯".
  rewrite OmoAuth_eq OmoSnapStates_eq.
  iDestruct "M●" as (??????????)
    "(%&%& [%Hγe %Hγs] & TL● & EL● & WL● & SL● & Hγq & HL● & Hγg & EL✓ & WL✓ & #ELEMS & #KEYS & Pures)".
  iDestruct "Pures" as %(EQlenTL & EQlenEL & E_TL_VALID & E_EL_VALID & MONOqg & QM_VALID & Nomo & NE & HWF & LHB & OMO_GOOD).
  iDestruct (mono_list_lb_own_get with "SL●") as "#SL◯".
  iExists γwl,γsl,γq. iFrame "#". apply omo_stlist_length in OMO_GOOD. done.
Qed.

Lemma OmoAuth_OmoTokenR γe γs q E omo stlist e `{Interpretable eventT absStateT} :
  OmoAuth γe γs q E omo stlist _ -∗
  OmoTokenR γe e -∗
  ⌜ is_Some (E !! e) ⌝.
Proof.
  iIntros "M● RCOMMIT". rewrite OmoAuth_eq OmoTokenR_eq.
  iDestruct "M●" as (??????????)
    "(%&%& [%Hγe %Hγs] & TL● & EL● & WL● & SL● & Hγq & HL● & Hγg & EL✓ & WL✓ & #ELEMS & #KEYS & Pures)".
  iDestruct "Pures" as %(EQlenTL & EQlenEL & E_TL_VALID & E_EL_VALID & MONOqg & QM_VALID & Nomo & NE & HWF & LHB & OMO_GOOD).
  iDestruct "RCOMMIT" as (????????) "([%Hγe' Hγ] & #EL@e & GL● & #Hγb)". encode_agree Hγe.
  iDestruct (mono_list_auth_idx_lookup with "EL● EL@e") as %LOOKUP%lookup_lt_Some.
  iPureIntro. rewrite lookup_lt_is_Some EQlenEL. done.
Qed.

Lemma OmoAuth_OmoTokenW γe γs q E omo stlist e `{Interpretable eventT absStateT} :
  OmoAuth γe γs q E omo stlist _ -∗
  OmoTokenW γe e -∗
  ⌜ is_Some (E !! e) ⌝.
Proof.
  iIntros "M● WCOMMIT". rewrite OmoAuth_eq OmoTokenW_eq.
  iDestruct "M●" as (??????????)
    "(%&%& [%Hγe %Hγs] & TL● & EL● & WL● & SL● & Hγq & HL● & Hγg & EL✓ & WL✓ & #ELEMS & #KEYS & Pures)".
  iDestruct "Pures" as %(EQlenTL & EQlenEL & E_TL_VALID & E_EL_VALID & MONOqg & QM_VALID & Nomo & NE & HWF & LHB & OMO_GOOD).
  iDestruct "WCOMMIT" as (????????) "([%Hγe' Hγ] & #EL@e & GL● & #Hγb)". encode_agree Hγe.
  iDestruct (mono_list_auth_idx_lookup with "EL● EL@e") as %LOOKUP%lookup_lt_Some.
  iPureIntro. rewrite lookup_lt_is_Some EQlenEL. done.
Qed.

Lemma OmoEview_update γe γe' γs q E omo stlist M M' `{Interpretable eventT absStateT} :
  OmoAuth γe γs q E omo stlist _ -∗
  OmoEview γe M -∗
  OmoEview γe' M' -∗
  ∃ M'',
    OmoAuth γe γs q E omo stlist _ ∗
    OmoEview γe' M'' ∗
    HbIncluded γe γe' M M'' ∗
    ⌜ M' ⊆ M'' ⌝.
Proof.
  iIntros "M● #⊒M #⊒M'". rewrite OmoAuth_eq HbIncluded_eq.
  iDestruct "M●" as (??????????)
    "(%&%& [%Hγe %Hγs] & TL● & EL● & WL● & SL● & Hγq & HL● & Hγg & EL✓ & WL✓ & #ELEMS & #KEYS & Pures)".
  iDestruct "Pures" as %(EQlenTL & EQlenEL & E_TL_VALID & E_EL_VALID & MONOqg & QM_VALID & Nomo & NE & HWF & LHB & OMO_GOOD).
  iDestruct (OmoEview_nonempty with "⊒M") as %NEmp.
  iInduction M as [|e M NotIn] "IH" using set_ind_L; [done|].

  destruct (decide (M = ∅)) as [EQ|NEmp'].
  { rewrite {4}OmoEview_eq.
    have EQ' : {[e]} ∪ M = {[e]} by set_solver. rewrite EQ'. subst M. clear EQ'.
    iDestruct "⊒M" as (?????) "[[%Hγe' _] BIG]". encode_agree Hγe.
    rewrite big_sepS_singleton. iDestruct "BIG" as (einfo) "[EL@e ⊒OUT]".

    iDestruct (mono_list_auth_idx_lookup with "EL● EL@e") as %ELe.
    iDestruct (big_sepL_lookup_acc with "EL✓") as "[(%&%& GL● & #BIG) CLOSE]"; [done|].
    iDestruct "GL●" as "[GL● GL●']".
    iDestruct ("CLOSE" with "[GL●']") as "EL✓".
    { iExists _,GL. iFrame. iFrame "BIG". }

    iAssert (∃ M'', OmoEview γe' M'' ∗ ⌜ ∀ e', (γe', e') ∈ GL → e' ∈ M'' ⌝)%I with "[-]" as (M''') "[#⊒M''' %HM''']".
    { iClear "IH GL● EL✓". iInduction GL as [] "IH".
      - iExists M'. iFrame "#". iPureIntro. intros. set_solver.
      - rewrite big_sepL_cons. iDestruct "BIG" as "[H BIG]".
        iDestruct "H" as (γe'' e' γtl'' γel'' γh'' γg'' γn'' einfo') "[(%EQ1 & %Hγe' & %LEout) #EL@e'']".
        subst a. iDestruct ("IH" with "BIG TL● EL● WL● SL● Hγq HL● Hγg WL✓") as (M'') "[#⊒M'' %HM'']".
        destruct (decide (γe'' = γe')) as [->|NEQ].
        + iExists ({[e']} ∪ M''). iDestruct (OmoEview_nonempty with "⊒M''") as %NEmp''.
          rewrite -!OmoEview_split; try done; try set_solver-. iFrame "⊒M''". iSplit.
          * rewrite OmoEview_eq. iExists γtl'',γel'',γh'',γg'',γn''. iSplit.
            { iPureIntro. split; [done|]. set_solver-. }
            rewrite big_sepS_singleton.
            iExists einfo'. iFrame "#". iApply monPred_in_mono; try done.
          * iPureIntro. intros. destruct (decide (e'0 = e')) as [->|NEQ]; [set_solver|].
            have IN : (γe', e'0) ∈ GL by set_solver. specialize (HM'' _ IN). set_solver.
        + iExists M''. iFrame "⊒M''". iPureIntro. intros. apply HM''. set_solver. }

    iDestruct (OmoEview_union with "⊒M' ⊒M'''") as "⊒Mn".
    iExists (M' ∪ M'''). iFrame "⊒Mn". iSplitR "GL●".
    { repeat iExists _. iFrame "∗". iFrame "ELEMS KEYS". iPureIntro. split_and!; try done. }
    iSplit; [|iPureIntro;set_solver].
    iExists γtl,γel,γh,γg,γn. iSplit; [done|]. rewrite big_sepS_singleton.
    repeat iExists _. iFrame "∗#". iPureIntro. intros.
    specialize (HM''' _ H0). set_solver. }

  iDestruct (OmoEview_split with "⊒M") as "[⊒e ⊒Ma]"; [set_solver|set_solver|].
  rewrite {5}OmoEview_eq. iDestruct "⊒e" as (?????) "[[%Hγe' _] BIG]". encode_agree Hγe.
  rewrite big_sepS_singleton. iDestruct "BIG" as (einfo) "[EL@e ⊒OUT]".

  iDestruct (mono_list_auth_idx_lookup with "EL● EL@e") as %ELe.
  iDestruct (big_sepL_lookup_acc with "EL✓") as "[(%&%& GL● & #BIG) CLOSE]"; [done|].
  iDestruct "GL●" as "[GL● GL●']".
  iDestruct ("CLOSE" with "[GL●']") as "EL✓".
  { iExists _,GL. iFrame. iFrame "BIG". }

  iAssert (∃ M'', OmoEview γe' M'' ∗ ⌜ ∀ e', (γe', e') ∈ GL → e' ∈ M'' ⌝)%I with "[-]" as (M''') "[#⊒M''' %HM''']".
  { iClear "IH GL● EL✓". iInduction GL as [] "IH".
    - iExists M'. iFrame "#". iPureIntro. intros. set_solver.
    - rewrite big_sepL_cons. iDestruct "BIG" as "[H BIG]".
      iDestruct "H" as (γe'' e' γtl'' γel'' γh'' γg'' γn'' einfo') "[(%EQ1 & %Hγe' & %LEout) #EL@e'']".
      subst a. iDestruct ("IH" with "BIG TL● EL● WL● SL● Hγq HL● Hγg WL✓") as (M'') "[#⊒M'' %HM'']".
      destruct (decide (γe'' = γe')) as [->|NEQ].
      + iExists ({[e']} ∪ M''). iDestruct (OmoEview_nonempty with "⊒M''") as %NEmp''.
        rewrite -!OmoEview_split; try done; try set_solver-. iFrame "⊒M''". iSplit.
        * rewrite OmoEview_eq. iExists γtl'',γel'',γh'',γg'',γn''. iSplit.
          { iPureIntro. split; [done|]. set_solver-. }
          rewrite big_sepS_singleton.
          iExists einfo'. iFrame "#". iApply monPred_in_mono; try done.
        * iPureIntro. intros. destruct (decide (e'0 = e')) as [->|NEQ]; [set_solver|].
          have IN : (γe', e'0) ∈ GL by set_solver. specialize (HM'' _ IN). set_solver.
      + iExists M''. iFrame "⊒M''". iPureIntro. intros. apply HM''. set_solver. }

  iDestruct ("IH" with "[] ⊒Ma TL● EL● WL● SL● Hγq HL● Hγg EL✓ WL✓") as (M'') "(M● & ⊒M'' & M⊢M'' & %SubM'M'')"; [done|].
  iDestruct (OmoEview_union with "⊒M'' ⊒M'''") as "⊒Mn".
  iExists (M'' ∪ M'''). iFrame "M● ⊒Mn". iSplit; [|iPureIntro;set_solver].
  iExists γtl,γel,γh,γg,γn. iSplit; [done|]. iApply big_sepS_union; [set_solver|]. iSplitL "GL●".
  - rewrite big_sepS_singleton. repeat iExists _. iFrame "GL● EL@e".
    iPureIntro. intros. specialize (HM''' _ H0). set_solver.
  - iDestruct "M⊢M''" as (?????) "[%Hγe' H]". encode_agree Hγe.
    iApply (big_sepS_impl with "H"). iIntros "%e' %IN !> H".
    iDestruct "H" as (???) "(H1 & H2 & %Hin)". repeat iExists _. iFrame "H1 H2".
    iPureIntro. intros. specialize (Hin _ H0). set_solver.
Qed.

Lemma OmoEview_update_obj V1 V2 γe γe' γs q E omo stlist M M' `{Interpretable eventT absStateT} :
  V1 ⊑ V2 →
  OmoAuth γe γs q E omo stlist _ -∗
  @{V1} OmoEview γe M -∗
  @{V2} OmoEview γe' M' -∗
  ∃ M'',
    OmoAuth γe γs q E omo stlist _ ∗
    @{V2} (OmoEview γe' M'' ∗ HbIncluded γe γe' M M'') ∗
    ⌜ M' ⊆ M'' ⌝.
Proof.
  iIntros "%LeV1V2 M● ⊒M@V1 ⊒M'@V2".
  iAssert (@{V2} (∃ M'', OmoAuth γe γs q E omo stlist _ ∗ OmoEview γe' M'' ∗ HbIncluded γe γe' M M'' ∗ ⌜ M' ⊆ M'' ⌝))%I
    with "[-]" as (M'') "(M● & #H1 & H2 & %Sub)".
  { iDestruct (view_at_mono_2 _ V2 with "⊒M@V1") as "⊒M@V2"; [done|].
    iDestruct (view_at_objective_iff _ V2 with "M●") as "M●".
    iCombine "⊒M@V2 ⊒M'@V2 M●" as "RES". iApply (view_at_mono with "RES"); [done|].
    iIntros "(#⊒M & #⊒M' & M●)". by iApply (OmoEview_update with "M●"). }
  iExists M''. rewrite view_at_objective_iff. iFrame "∗#". done.
Qed.

Lemma OmoAuth_OmoCW_l γe γe' γs q E omo stlist e e' `{Interpretable eventT absStateT} :
  OmoAuth γe γs q E omo stlist _ -∗
  OmoCW γe γe' e e' -∗
  ⌜ is_Some (E !! e) ⌝.
Proof.
  iIntros "M● #e↦e'". rewrite OmoAuth_eq OmoCW_eq.
  iDestruct "M●" as (??????????)
    "(%&%& [%Hγe %Hγs] & TL● & EL● & WL● & SL● & Hγq & HL● & Hγg & EL✓ & WL✓ & #ELEMS & #KEYS & Pures)".
  iDestruct "Pures" as %(EQlenTL & EQlenEL & E_TL_VALID & E_EL_VALID & MONOqg & QM_VALID & Nomo & NE & HWF & LHB & OMO_GOOD).
  iDestruct "e↦e'" as (??????????) "(%&%&%&%& [%Hγen %Hγe'] & EL@e & EL'@e' & GL@0 & GL@1 & [%EQ1 %EQ2])".
  encode_agree Hγe.
  iDestruct (mono_list_auth_idx_lookup with "EL● EL@e") as %ELe.
  iPureIntro. rewrite lookup_lt_is_Some EQlenEL. by apply lookup_lt_Some in ELe.
Qed.

Lemma OmoHbToken_OmoCW_l γe γe' γs E omo stlist e e' e'' `{Interpretable eventT absStateT} :
  OmoHbToken γe γs E omo stlist e'' _ -∗
  OmoCW γe γe' e e' -∗
  ⌜ is_Some (E !! e) ⌝.
Proof.
  iIntros "M● #e↦e'". rewrite OmoHbToken_eq OmoCW_eq.
  iDestruct "M●" as (??????????)
    "(%&%&%&%& [%Hγe %Hγs] & TL● & EL● & WL● & SL● & Hγq & GL● & HL● & Hγg & EL✓ & WL✓ & #ELEMS & #KEYS & #BIG & Pures)".
  iDestruct "Pures" as %(EQlenTL & EQlenEL & EQe & LASTEL & E_TL_VALID & E_EL_VALID & MONOqg & QM_VALID & Nomo & NE & HWF & LHB & OMO_GOOD).
  iDestruct "e↦e'" as (??????????) "(%&%&%&%& [%Hγen %Hγe'] & EL@e & EL'@e' & GL@0 & GL@1 & [%EQ1 %EQ2])".
  encode_agree Hγe.
  iDestruct (mono_list_auth_idx_lookup with "EL● EL@e") as %ELe.
  iPureIntro. rewrite lookup_lt_is_Some EQlenEL. by apply lookup_lt_Some in ELe.
Qed.

Lemma OmoAuth_OmoCW_l' γe γe' γs q E omo stlist e e' `{Interpretable eventT absStateT} :
  OmoAuth γe γs q E omo stlist _ -∗
  OmoCW γe γe' e e' -∗
  ∃ eidx, ⌜ lookup_omo omo eidx = Some e ⌝.
Proof.
  iIntros "M● #e↦e'".
  iDestruct (OmoAuth_wf with "M●") as %[OMO_GOOD _].
  iDestruct (OmoAuth_OmoCW_l with "M● e↦e'") as %He.
  eapply lookup_omo_surjective in He; [|done]. done.
Qed.

Lemma OmoHbToken_OmoCW_l' γe γe' γs E omo stlist e e' e'' `{Interpretable eventT absStateT} :
  OmoHbToken γe γs E omo stlist e'' _ -∗
  OmoCW γe γe' e e' -∗
  ∃ eidx, ⌜ lookup_omo omo eidx = Some e ⌝.
Proof.
  iIntros "M● #e↦e'".
  iDestruct (OmoHbToken_wf with "M●") as %[OMO_GOOD _].
  iDestruct (OmoHbToken_OmoCW_l with "M● e↦e'") as %He.
  eapply lookup_omo_surjective in He; [|done]. done.
Qed.

Lemma OmoAuth_OmoCW_r γe γe' γs q E omo stlist e e' `{Interpretable eventT absStateT} :
  OmoAuth γe' γs q E omo stlist _ -∗
  OmoCW γe γe' e e' -∗
  ⌜ is_Some (E !! e') ⌝.
Proof.
  iIntros "M● #e↦e'". rewrite OmoAuth_eq OmoCW_eq.
  iDestruct "M●" as (??????????)
    "(%&%& [%Hγe %Hγs] & TL● & EL● & WL● & SL● & Hγq & HL● & Hγg & EL✓ & WL✓ & #ELEMS & #KEYS & Pures)".
  iDestruct "Pures" as %(EQlenTL & EQlenEL & E_TL_VALID & E_EL_VALID & MONOqg & QM_VALID & Nomo & NE & HWF & LHB & OMO_GOOD).
  iDestruct "e↦e'" as (??????????) "(%&%&%&%& [%Hγen %Hγe'] & EL@e & EL'@e' & GL@0 & GL@1 & [%EQ1 %EQ2])".
  encode_agree Hγe'.
  iDestruct (mono_list_auth_idx_lookup with "EL● EL'@e'") as %ELe.
  iPureIntro. rewrite lookup_lt_is_Some EQlenEL. by apply lookup_lt_Some in ELe.
Qed.

Lemma OmoHbToken_OmoCW_r γe γe' γs E omo stlist e e' e'' `{Interpretable eventT absStateT} :
  OmoHbToken γe' γs E omo stlist e'' _ -∗
  OmoCW γe γe' e e' -∗
  ⌜ is_Some (E !! e') ⌝.
Proof.
  iIntros "M● #e↦e'". rewrite OmoHbToken_eq OmoCW_eq.
  iDestruct "M●" as (??????????)
    "(%&%&%&%& [%Hγe %Hγs] & TL● & EL● & WL● & SL● & Hγq & GL● & HL● & Hγg & EL✓ & WL✓ & #ELEMS & #KEYS & #BIG & Pures)".
  iDestruct "Pures" as %(EQlenTL & EQlenEL & E_TL_VALID & E_EL_VALID & MONOqg & QM_VALID & Nomo & NE & HWF & LHB & OMO_GOOD).
  iDestruct "e↦e'" as (??????????) "(%&%&%&%& [%Hγen %Hγe'] & EL@e & EL'@e' & GL@0 & GL@1 & [%EQ1 %EQ2])".
  encode_agree Hγe'.
  iDestruct (mono_list_auth_idx_lookup with "EL● EL'@e'") as %ELe.
  iPureIntro. rewrite lookup_lt_is_Some EQlenEL. by apply lookup_lt_Some in ELe.
Qed.

Lemma OmoAuth_OmoCW_r' γe γe' γs q E omo stlist e e' `{Interpretable eventT absStateT} :
  OmoAuth γe' γs q E omo stlist _ -∗
  OmoCW γe γe' e e' -∗
  ∃ eidx, ⌜ lookup_omo omo eidx = Some e' ⌝.
Proof.
  iIntros "M● #e↦e'".
  iDestruct (OmoAuth_wf with "M●") as %[OMO_GOOD _].
  iDestruct (OmoAuth_OmoCW_r with "M● e↦e'") as %He.
  eapply lookup_omo_surjective in He; [|done]. done.
Qed.

Lemma OmoHbToken_OmoCW_r' γe γe' γs E omo stlist e e' e'' `{Interpretable eventT absStateT} :
  OmoHbToken γe' γs E omo stlist e'' _ -∗
  OmoCW γe γe' e e' -∗
  ∃ eidx, ⌜ lookup_omo omo eidx = Some e' ⌝.
Proof.
  iIntros "M● #e↦e'".
  iDestruct (OmoHbToken_wf with "M●") as %[OMO_GOOD _].
  iDestruct (OmoHbToken_OmoCW_r with "M● e↦e'") as %He.
  eapply lookup_omo_surjective in He; [|done]. done.
Qed.

Lemma OmoUBgen_add (omo : omoT) M gen e eidx eV γe γs q E stlist `{Interpretable eventT absStateT} :
  E !! e = Some eV →
  lookup_omo omo eidx = Some e →
  (gen_of eidx ≤ gen)%nat →
  OmoUBgen omo M gen →
  OmoAuth γe γs q E omo stlist _ -∗
  ⌜ OmoUBgen omo ({[e]} ∪ eV.(eview) ∪ M) gen ⌝.
Proof.
  iIntros "%He %Heidx %LE %MAXgen M●".
  iDestruct (OmoAuth_wf with "M●") as %[OMO_GOOD HWF]. iPureIntro.
  inversion OMO_GOOD. unfold lhb_omo in *.
  unfold OmoUBgen in *. intros.
  have CASE : e0 = e ∨ e0 ∈ eV.(eview) ∨ e0 ∈ M by set_solver.
  destruct CASE as [->|[IN|IN]].
  - exists eidx. done.
  - destruct HWF. specialize (hwf_logview_closed _ _ He _ IN). simpl in hwf_logview_closed.
    eapply lookup_omo_surjective in hwf_logview_closed as [eidx' Heidx']; [|done].
    specialize (LHB_OMO _ _ _ _ _ Heidx' Heidx He IN).
    exists eidx'. split; [done|]. inversion LHB_OMO; subst eidx eidx'; simpl in *; try lia.
  - specialize (MAXgen _ IN). done.
Qed.

Lemma OmoUB_from_gen γe γs q E omo stlist M gen e eidx `{Interpretable eventT absStateT} :
  lookup_omo omo eidx = Some e →
  OmoUBgen omo M gen →
  (gen ≤ gen_of eidx)%nat →
  OmoAuth γe γs q E omo stlist _ -∗
  OmoUB γe M e.
Proof.
  iIntros "%Heidx %MAXgen %LE M●". rewrite /OmoUB big_sepS_forall. iIntros "%e' %IN".
  unfold OmoUBgen in *. specialize (MAXgen _ IN) as (eidx' & Heidx' & LE').
  iApply OmoLe_get; try done. lia.
Qed.

Lemma OmoUB_into_gen γe γs q E omo stlist M e eidx `{Interpretable eventT absStateT} :
  lookup_omo omo eidx = Some e →
  OmoAuth γe γs q E omo stlist _ -∗
  OmoUB γe M e -∗
  ⌜ OmoUBgen omo M (gen_of eidx) ⌝.
Proof.
  iIntros "%Heidx M● #MAXgen %e' %IN".
  iDestruct (OmoAuth_wf with "M●") as %[OMO_GOOD _].
  iDestruct (big_sepS_elem_of with "MAXgen") as "#e'≤e"; [done|].
  iDestruct (OmoAuth_OmoLe_l with "M● e'≤e") as %[eidx' Heidx'].
  iDestruct (OmoLe_Le with "M● e'≤e") as %LE; [done|done|].
  iPureIntro. exists eidx'. done.
Qed.

Lemma OmoUB_singleton γe e eV :
  OmoEinfo γe e eV -∗ OmoUB γe ({[e]} ∪ eV.(eview)) e.
Proof.
  iIntros "#e✓eV". rewrite OmoEinfo_eq.
  by iDestruct "e✓eV" as (???????) "(H1 & H2 & H3 & H4 & H5 & H6)".
Qed.

(** Allocation of `OmoAuth`.
    Note that it gives `OmoHbToken` to allow registration of `HbToken` for initial event,
    which can be later turned into `OmoAuth` by the lemma `OmoHbToken_finish` *)
Lemma OmoAuth_alloc_Gname eV st γe' γx e' (e := 0%nat) (omo := omo_append_w [] e []) `{Interpretable eventT absStateT} :
  step e eV init st → eV.(eview) = {[e]} →
  OmoTokenW γe' e'
  ==∗
  ∃ γe γs,
    OmoHbToken γe γs [eV] omo [st] e _ ∗
    @{eV.(sync)} OmoEview γe {[e]} ∗
    OmoCW γe γe' e e' ∗
    OmoEinfo γe e eV ∗
    OmoSnap γe γs e st ∗
    OmoGname γe γx ∗
    OmoTokenW γe e.
Proof.
  iIntros "%STEP %EVIEW WCOMMIT". rewrite OmoTokenW_eq.
  iDestruct "WCOMMIT" as (γtl' γel' γh' γg' γn' einfo' γgl' γb') "([%Hγe' %Heinfo'] & #EL'@e' & GL'● & #Hγb')".

  have OMO_GOOD : Linearizability_omo [eV] omo [st].
  { subst omo. replace [eV] with ([] ++ [eV]); [|by simplify_list_eq]. replace [st] with ([] ++ [st]); [|by simplify_list_eq].
    eapply Linearizability_omo_append_w; try done. apply Linearizability_omo_empty. }

  iMod (@mono_list_own_alloc (gname * event_id) _ _ []) as (γgl) "[GL● _]".
  iMod (@mono_list_own_alloc (gname * event_id) _ _ []) as (γgls) "[GLs● #GLs◯]".
  iMod (@mono_list_own_alloc event_id _ _ []) as (γrl) "[RL● #RL◯]".
  iMod (own_alloc (to_agree true)) as (γb) "#Hγb"; [done|].

  set TL := [eV.(type)].
  set elast : (gname * option gname * view * eView * Qp * gname) := (encode (γgl,γb), Some γgl', eV.(sync), eV.(eview), 1%Qp, γgls).
  set EL : list (gname * option gname * view * eView * Qp * gname) := [elast].
  set WL : list (event_id * gname * Qp) := [(0, γrl, 1%Qp)].
  iMod (mono_list_own_alloc TL) as (γtl) "[TL● #TL◯]".
  iMod (mono_list_own_alloc EL) as (γel) "[EL● #EL◯]".
  iMod (mono_list_own_alloc WL) as (γwl) "[WL● #WL◯]".
  iMod (mono_list_own_alloc [st]) as (γsl) "[SL● #SL◯]".
  iMod (mono_list_own_alloc [eV]) as (γh) "[HL● #HL◯]".
  iMod (@ghost_map_alloc_empty _ Qp nat) as (γq) "Hγq".
  iMod (ghost_map_insert_persist 1%Qp 0 with "Hγq") as "[Hγq #KEY]"; [done|].
  remember (encode (γwl,γsl,γq)) as γs eqn:Hγs.
  iMod (ghost_var_alloc (γs,[eV],omo,[st])) as (γg) "Hγg".
  iMod (own_alloc (to_agree γx)) as (γn) "#Hγx"; [done|].
  remember (encode (γtl,γel,γh,γg,γn)) as γe eqn:Hγe.

  iDestruct (@mono_list_idx_own_get _ _ _ _ _ 0 with "TL◯") as "#TL@e"; [done|].
  iDestruct (@mono_list_idx_own_get _ _ _ _ _ 0 with "EL◯") as "#EL@e"; [done|].
  iDestruct (@mono_list_idx_own_get _ _ _ _ _ 0 with "WL◯") as "#WL@0"; [done|].
  iDestruct (@mono_list_idx_own_get _ _ _ _ _ 0 with "SL◯") as "#SL@0"; [done|].
  iDestruct (@mono_list_idx_own_get _ _ _ _ _ 0 with "HL◯") as "#HL@e"; [done|].

  iAssert (OmoAuth_EL_seen_event_valid (take (length EL - 1)%nat EL))%I with "[]" as "EL✓".
  { rewrite /OmoAuth_EL_seen_event_valid. subst EL. simplify_list_eq. done. }

  iAssert (OmoAuth_WL_valid γs γel 1 omo WL)%I with "[RL●]" as "WL✓".
  { rewrite /OmoAuth_WL_valid. subst omo WL. simplify_list_eq. iSplitL; [|done].
    iExists e,[],γrl,elast. subst e elast. simpl. iSplitR; [done|]. iFrame "RL●". iSplit; [|done].
    iDestruct (@mono_list_idx_own_get _ _ _ _ _ 0 with "EL◯") as "EL@0"; [done|]. done. }

  iAssert (|==> OmoCW γe γe' e e' ∗ OmoTokenW_def γe e)%I with "[GL● GL'●]" as ">[#e↦e' WCOMMIT]".
  { iMod (mono_list_auth_own_update [(γe',e');(γe,e)] with "GL'●") as "[GL'● #GL'◯]".
    { replace [(γe',e');(γe,e)] with ([(γe',e')] ++ [(γe,e)]); [|by simplify_list_eq]. by eapply prefix_app_r. }
    iMod (mono_list_auth_own_update [(γe,e)] with "GL●") as "[GL● #GL◯]".
    { replace [(γe,e)] with ([] ++ [(γe,e)]); [|by simplify_list_eq]. by eapply prefix_app_r. }
    iModIntro. iSplitR.
    - rewrite OmoCW_eq /OmoCW_def. iExists γtl,γel,γh,γg,γn. iExists γtl',γel',γh',γg',γn'. iExists elast,einfo'. iExists γgl',γb'.
      iDestruct (@mono_list_idx_own_get _ _ _ _ _ 0 with "GL'◯") as "#GL'@0"; [done|].
      iDestruct (@mono_list_idx_own_get _ _ _ _ _ 1 with "GL'◯") as "#GL'@1"; [done|].
      iFrame "EL@e GL'@0 GL'@1 EL'@e'". iPureIntro. split_and!; try done.
    - iExists γtl,γel,γh,γg,γn,elast,γgl,γb. iFrame "GL● Hγb EL@e". iPureIntro. split_and!; try done. }

  iAssert (OmoEinfo γe e eV)%I with "[-]" as "#e✓eV".
  { rewrite OmoEinfo_eq /OmoEinfo_def. iExists γtl,γel,γh,γg,γn,eV.(type),elast. iFrame "TL@e EL@e HL@e".
    iSplit; [iPureIntro; split_and!; try done|]. iSplit.
    + rewrite EVIEW /OmoUB big_sepS_forall. iIntros "%e'' %IN".
      have EQ : e'' = e by set_solver. subst e''. rewrite OmoLe_eq. iExists γtl,γel,γh,γg,γn,elast,elast. iFrame "#". done.
    + rewrite EVIEW OmoEview_eq. iExists γtl,γel,γh,γg,γn. iSplit; [done|].
      iAssert (@{eV.(sync)} (⊒eV.(sync)))%I with "[]" as "#⊒OUT@SYNC"; [done|].
      iDestruct (view_at_objective_iff _ (eV.(sync)) with "EL@e") as "EL@e@SYNC".
      iCombine "⊒OUT@SYNC EL@e@SYNC" as "RES". iApply (view_at_mono with "RES"); [done|]. iIntros "[#⊒OUT #EL@e]".
      iApply big_sepS_forall. iIntros "%e'' %IN".
      have EQ : e'' = e by set_solver. subst e''. iExists elast. subst elast. simpl. iFrame "#". }

  iAssert (OmoAuth_all_elem γe [eV])%I with "[]" as "#ELEMS".
  { rewrite /OmoAuth_all_elem big_sepL_singleton. done. }

  iAssert (OmoAuth_qg_keys γq (<[1%Qp:=0]> ∅))%I with "[]" as "#KEYS".
  { iApply big_sepM_insert; [done|]. iFrame "#". done. }

  iAssert (OmoGname γe γx)%I with "[]" as "#Hγx'".
  { rewrite OmoGname_eq. iExists γtl,γel,γh,γg,γn. iFrame "#". done. }

  iModIntro. iExists γe,γs. iFrame "WCOMMIT e↦e' Hγx'". iSplitL; last iSplit; last iSplit.
  - rewrite OmoHbToken_eq /OmoHbToken_def.
    iExists γtl,γel,γh,γg,γn,γwl,γsl,γq. iExists TL,EL,WL,_,elast,[]. iFrame. iFrame "EL✓ ELEMS KEYS".
    rewrite big_sepL_nil. iPureIntro. split_and!; try done.
    + rewrite /OmoAuth_E_TL_valid. intros. destruct e0; try done. inversion H0. subst eV0. inversion H1. done.
    + rewrite /OmoAuth_E_EL_valid. intros. destruct e0; try done. inversion H0. inversion H1. subst eV0 einfo. done.
    + rewrite /OmoAuth_qg_mono. intros. apply lookup_lt_Some in H0,H1. subst WL. simpl in *. lia.
    + rewrite /OmoAuth_QM_valid. subst WL. intros. split; intros.
      * rewrite list_lookup_fmap in H0. destruct i; [|done]. inversion H0. subst qg. done.
      * destruct (decide (qg = 1%Qp)) as [->|NEQ].
        -- rewrite lookup_insert in H0. inversion H0. subst i. rewrite list_lookup_fmap /=. done.
        -- rewrite lookup_insert_ne in H0; [|done]. done.
    + constructor; intros; destruct e0; try done; inversion H0; subst eV0.
      * set_solver.
      * rewrite EVIEW. rewrite set_Forall_singleton. done.
    + rewrite /hb_ord. intros. apply lookup_lt_Some in ORD_i1,ORD_i2. simpl in *. lia.
  - rewrite OmoEview_eq /OmoEview_def. iExists γtl,γel,γh,γg,γn. iSplit; [done|].
    rewrite big_sepS_singleton. iExists elast. iFrame "EL@e". done.
  - iFrame "e✓eV".
  - rewrite OmoSnap_eq /OmoSnap_def. iExists γtl,γel,γh,γg,γn,γwl,γsl,γq. iExists 0,elast. iFrame "EL@e KEY SL@0". iPureIntro. split_and!; try done.
Qed.

(* Finishes registering `HbToken` and return to `OmoAuth` *)
Lemma OmoHbToken_finish γe γs E omo stlist e `{Interpretable eventT absStateT} :
  OmoHbToken γe γs E omo stlist e _ -∗
  OmoAuth γe γs 1 E omo stlist _.
Proof.
  iIntros "M●". rewrite OmoHbToken_eq OmoAuth_eq.
  iDestruct "M●" as (??????????)
    "(%&%&%&%& [%Hγe %Hγs] & TL● & EL● & WL● & SL● & Hγq & GL● & HL● & Hγg & EL✓ & WL✓ & #ELEMS & #KEYS & #BIG & Pures)".
  iDestruct "Pures" as %(EQlenTL & EQlenEL & EQe & LASTEL & E_TL_VALID & E_EL_VALID & MONOqg & QM_VALID & Nomo & NE & HWF & LHB & OMO_GOOD).

  iAssert (OmoAuth_EL_seen_event_valid EL)%I with "[EL✓ GL●]" as "EL✓".
  { rewrite -{3}(take_drop (length EL) EL) drop_ge; [|done]. simplify_list_eq.
    have EQ : length EL = S (length EL - 1) by destruct EL; try done; simpl; lia.
    rewrite {2}EQ. clear EQ.
    rewrite last_lookup in LASTEL. replace (Init.Nat.pred (length EL)) with (length EL - 1) in LASTEL by lia.
    rewrite (take_S_r _ _ elast); [|done].
    rewrite /OmoAuth_EL_seen_event_valid big_sepL_snoc. iFrame "EL✓". repeat iExists _. iFrame "GL●". done. }

  repeat iExists _. iFrame "EL●". iFrame "∗#". iPureIntro. split_and!; try done.
Qed.

(* special version of `OmoAuth_alloc` that does not involve `OmoGname` *)
Lemma OmoAuth_alloc eV st γe' e' (e := 0%nat) (omo := omo_append_w [] e []) `{Interpretable eventT absStateT} :
  step e eV init st → eV.(eview) = {[e]} →
  OmoTokenW γe' e'
  ==∗
  ∃ γe γs,
    OmoHbToken γe γs [eV] omo [st] e _ ∗
    @{eV.(sync)} OmoEview γe {[e]} ∗
    OmoCW γe γe' e e' ∗
    OmoEinfo γe e eV ∗
    OmoSnap γe γs e st ∗
    OmoTokenW γe e.
Proof.
  iIntros "%STEP %EVIEW WCOMMIT".
  iMod (OmoAuth_alloc_Gname _ _ _ γe' with "WCOMMIT") as (??) "(H1 & H2 & H3 & H4 & H5 & H6 & H7)"; try done.
  iModIntro. iExists γe,γs. iFrame.
Qed.

Lemma OmoAuth_insert_ro γe γe' γs E omo stlist Vb M e e' eV st (en := length E) `{Interpretable eventT absStateT} :
  OmoAuth γe γs 1 E omo stlist _ -∗
  @{Vb} OmoEview γe M -∗
  OmoTokenR γe' e' -∗
  OmoSnap γe γs e st -∗
  OmoUB γe M e -∗
  ⌜ step en eV st st
  ∧ eV.(sync) = Vb
  ∧ eV.(eview) = {[en]} ∪ M ⌝
  ==∗
  ∃ gen,
    OmoHbToken γe γs (E ++ [eV]) (omo_insert_r omo gen en) stlist en _ ∗
    @{Vb} OmoEview γe ({[en]} ∪ M) ∗
    OmoCW γe γe' en e' ∗
    OmoEq γe e en ∗
    OmoEinfo γe en eV ∗
    OmoTokenR γe en ∗
    (∃ eidx, ⌜ lookup_omo (omo_insert_r omo gen en) eidx = Some en ∧ gen = gen_of eidx ⌝).
Proof.
  iIntros "M● #⊒M RCOMMIT #e↪st #MAXgen_e (%STEP & %eVOUT & %eVEVIEW)".
  iDestruct (OmoAuth_OmoSnap'' with "M● e↪st") as %[eidx Heidx].
  iDestruct (OmoAuth_OmoSnap with "M● e↪st") as %Hst; [done|].
  iDestruct (OmoUB_into_gen with "M● MAXgen_e") as %MAXgen; [done|].
  iDestruct (OmoAuth_OmoEview_obj with "M● ⊒M") as %Mvalid.
  iDestruct (OmoEview_nonempty_obj with "⊒M") as %NEmp.
  rewrite OmoAuth_eq. iDestruct "M●" as (??????????)
    "(%&%& [%Hγe %Hγs] & TL● & EL● & WL● & SL● & Hγq & HL● & Hγg & EL✓ & WL✓ & #ELEMS & #KEYS & Pures)".
  iDestruct "Pures" as %(EQlenTL & EQlenEL & E_TL_VALID & E_EL_VALID & MONOqg & QM_VALID & Nomo & NE & HWF & LHB & OMO_GOOD).

  set E' := E ++ [eV].
  set gen := gen_of eidx.
  set omo' := omo_insert_r omo gen en.
  have OMO_GOOD' : Linearizability_omo E' omo' stlist.
  { eapply Linearizability_omo_insert_r; try done. intros. unfold OmoUBgen in *.
    specialize (MAXgen _ H0) as (eidx' & Heidx' & LE).
    eapply lookup_omo_inj in Heidx'; [|done|exact H1]. subst eidx'. done. }
  iMod (ghost_var_update (γs,E',omo',stlist) with "Hγg") as "Hγg".
  iMod (mono_list_auth_own_update E' with "HL●") as "[HL● #HL◯]"; [by eapply prefix_app_r|].
  iDestruct (@mono_list_idx_own_get _ _ _ _ _ en with "HL◯") as "HL@en"; [by rewrite lookup_app_1_eq|].

  rewrite OmoSnap_eq.
  iDestruct "e↪st" as (??????????) "([%Hγe2 %Hγs2] & #EL@e & #KEYi & SL@i)".
  encode_agree Hγe. encode_agree Hγs.

  rewrite OmoTokenR_eq.
  iDestruct "RCOMMIT" as (γtl' γel' γh' γg' γn' einfo' γgl' γb') "([%Hγe' %Heinfo'] & #EL'@e' & GL'● & #Hγb')".
  iMod (@mono_list_own_alloc (gname * event_id) _ _ [(γe,en)]) as (γgl) "[GL● #GL◯]".
  iMod (@mono_list_own_alloc (gname * event_id) _ _ []) as (γgls) "[GLs● #GLs◯]".
  iMod (own_alloc (to_agree false)) as (γb) "#Hγb"; [done|].
  set neinfo := (encode (γgl,γb), Some γgl', eV.(sync), eV.(eview), einfo.1.2, γgls).
  set EL' := EL ++ [neinfo].
  iMod (mono_list_auth_own_update EL' with "EL●") as "[EL● #EL◯]"; [by eapply prefix_app_r|].
  iDestruct (@mono_list_idx_own_get _ _ _ _ _ en with "EL◯") as "#EL@en".
  { subst EL' en. rewrite EQlenEL. by rewrite lookup_app_1_eq. }

  set TL' := TL ++ [eV.(type)].
  iMod (mono_list_auth_own_update TL' with "TL●") as "[TL● #TL◯]"; [by eapply prefix_app_r|].
  iDestruct (@mono_list_idx_own_get _ _ _ _ _ en with "TL◯") as "#TL@en".
  { subst TL' en. rewrite EQlenTL. by rewrite lookup_app_1_eq. }

  iAssert (|==> OmoTokenR_def γe en ∗ OmoCW γe γe' en e')%I with "[GL● GL'●]" as ">[RCOMMIT #en↦e']".
  { iMod (mono_list_auth_own_update [(γe',e');(γe,en)] with "GL'●") as "[GL'● #GL'◯]".
    { replace [(γe',e');(γe,en)] with ([(γe',e')] ++ [(γe,en)]); [|by simplify_list_eq]. by eapply prefix_app_r. }
    iDestruct (@mono_list_idx_own_get _ _ _ _ _ 0 with "GL'◯") as "GL'@0"; [done|].
    iDestruct (@mono_list_idx_own_get _ _ _ _ _ 1 with "GL'◯") as "GL'@1"; [done|].
    iModIntro. iSplitL.
    - iExists γtl,γel,γh,γg,γn,neinfo,γgl,γb. iFrame "GL● EL@en Hγb". iPureIntro. split_and!; done.
    - rewrite OmoCW_eq. iExists γtl,γel,γh,γg,γn. iExists γtl',γel',γh',γg',γn'. iExists neinfo,einfo',γgl',γb'. iFrame "EL'@e' EL@en GL'@0 GL'@1".
      iPureIntro. split_and!; try done. }

  iAssert (|==> OmoAuth_WL_valid γs γel 1 omo' WL)%I with "[WL✓]" as ">WL✓".
  { rewrite /OmoAuth_WL_valid. subst omo'. rewrite /omo_insert_r -{2}(take_drop gen omo).
    iDestruct (big_sepL2_length with "WL✓") as %EQlen.
    have [[e'' es''] Hgen] : is_Some (omo !! gen).
    { rewrite lookup_lt_is_Some. apply lookup_omo_lt_Some in Heidx. done. }
    have LE1 : (gen < length omo)%nat by apply lookup_lt_Some in Hgen.
    have LE2 : (gen < length WL)%nat by rewrite -EQlen.
    rewrite (drop_S _ (e'',es'')); [|done]. simplify_list_eq. rewrite alter_app_r_alt; last first.
    { rewrite take_length. lia. }
    replace (gen - length (take gen omo)) with 0%nat; last first.
    { rewrite take_length Nat.min_l; lia. }
    simplify_list_eq.
    rewrite -{2}(take_drop gen WL).
    have [winfo' Hgen'] : is_Some (WL !! gen) by rewrite lookup_lt_is_Some; lia.
    rewrite (drop_S _ winfo'); [|done].
    rewrite -{1}(take_drop gen omo) (drop_S _ (e'',es'')); [|done].
    rewrite -{1}(take_drop gen WL) (drop_S _ winfo'); [|done].
    iDestruct (big_sepL2_app_inv with "WL✓") as "[WL✓ WL✓']".
    { left. have H1 : ∀ (a b : nat), (a < b)%nat → (a ≤ b)%nat by lia.
      rewrite !take_length Nat.min_l; [|by apply H1]. (* direct [lia] does not work *)
      rewrite Nat.min_l; [done|by apply H1]. }
    iDestruct (big_sepL2_cons with "WL✓'") as "[WL✓' WL✓'']".
    iApply (big_sepL2_app with "WL✓"). iApply big_sepL2_cons. iFrame "WL✓''".
    iDestruct "WL✓'" as (????) "([%EQ %EQwinfo'] & RL● & #EL@e'' & BIGes)".
    inversion EQ. subst e0 es winfo'. clear EQ.
    iAssert (⌜ einfo0.1.2 = einfo.1.2 ⌝)%I with "[-]" as %EQqg.
    { destruct (decide (e = e'')) as [<-|NEQ].
      - iDestruct (mono_list_idx_agree with "EL@e EL@e''") as %<-. done.
      - destruct eidx; last first.
        { rewrite lookup_omo_wr_event /omo_write_op list_lookup_fmap Hgen in Heidx. inversion Heidx. done. }
        rewrite lookup_omo_ro_event /omo_read_op list_lookup_fmap Hgen /= in Heidx.
        iDestruct (big_sepL_lookup with "BIGes") as (?) "[#EL@e2 %EQ]"; [exact Heidx|].
        iDestruct (mono_list_idx_agree with "EL@e EL@e2") as %<-. done. }
    iMod (mono_list_auth_own_update (es'' ++ [en]) with "RL●") as "[RL● #RL◯]"; [by eapply prefix_app_r|].
    iExists e'',(es''++[en]),γrl,einfo0. iFrame "RL● EL@e''". iModIntro. iSplitR; [done|].
    iApply big_sepL_app. iFrame "BIGes". rewrite big_sepL_singleton. iExists neinfo. iFrame "EL@en". rewrite EQqg. done. }

  iAssert (OmoEq γe e en)%I with "[-]" as "#e=en".
  { rewrite OmoEq_eq. iExists γtl,γel,γh,γg,γn,einfo,neinfo. iSplit; [done|]. iFrame "#". }

  iAssert (OmoEinfo γe en eV)%I with "[-]" as "#en✓eV".
  { rewrite OmoEinfo_eq. iExists γtl,γel,γh,γg,γn,eV.(type),neinfo. iFrame "#". iSplit; [done|repeat iSplit].
    - rewrite eVEVIEW. replace ({[en]} ∪ ({[en]} ∪ M)) with ({[en]} ∪ M); [|set_solver].
      iApply big_sepS_forall. iIntros "%e'' %IN".
      have CASE : e'' = en ∨ e'' ∈ M by set_solver.
      destruct CASE as [->|IN'].
      + rewrite OmoLe_eq. iExists γtl,γel,γh,γg,γn,neinfo,neinfo. iFrame "#". done.
      + iDestruct (big_sepS_elem_of with "MAXgen_e") as "#e''≤e"; [done|]. by iApply OmoLe_Eq_trans.
    - rewrite eVEVIEW eVOUT. replace ({[en]} ∪ ({[en]} ∪ M)) with ({[en]} ∪ M); [|set_solver].
      rewrite -OmoEview_split; [|set_solver-|set_solver]. iFrame "⊒M". rewrite OmoEview_eq.
      iExists γtl,γel,γh,γg,γn. iSplit.
      { iPureIntro. split; [done|]. set_solver-. }
      rewrite big_sepS_singleton. iExists neinfo. iFrame "#". subst neinfo. simpl. rewrite eVOUT. done. }
  iAssert (OmoAuth_all_elem γe E')%I with "[-]" as "#ELEMS'".
  { iApply big_sepL_snoc. iFrame "ELEMS en✓eV". }

  iModIntro. iExists gen. iFrame "en↦e' RCOMMIT en✓eV e=en". iSplitL; [|repeat iSplit].
  - rewrite OmoHbToken_eq. iExists γtl,γel,γh,γg,γn,γwl,γsl,γq. iExists TL',EL',WL,QM. iExists neinfo,[].
    iFrame. rewrite big_sepL_nil. replace (take (length EL' - 1) EL') with EL; last first.
    { subst EL'. rewrite app_length /= Nat.add_sub take_app. done. }
    iFrame "EL✓ ELEMS' KEYS". iPureIntro. subst EL' TL' E'. rewrite !app_length /=. split_and!; try done.
    + rewrite EQlenTL. done.
    + rewrite EQlenEL. done.
    + lia.
    + rewrite last_app. done.
    + rewrite /OmoAuth_E_TL_valid. intros. destruct (decide (e0 = length E)) as [->|NEQ].
      * rewrite lookup_app_1_eq in H0. inversion H0. subst eV0.
        rewrite EQlenTL lookup_app_1_eq in H1. inversion H1. done.
      * rewrite lookup_app_1_ne in H0; [|done]. rewrite lookup_app_1_ne in H1; [|rewrite -EQlenTL;done].
        unfold OmoAuth_E_TL_valid in E_TL_VALID. eapply E_TL_VALID; try done.
    + rewrite /OmoAuth_E_EL_valid. intros. destruct (decide (e0 = length E)) as [->|NEQ].
      * rewrite lookup_app_1_eq in H0. inversion H0. subst eV0.
        rewrite EQlenEL lookup_app_1_eq in H1. inversion H1. done.
      * rewrite lookup_app_1_ne in H0; [|done]. rewrite lookup_app_1_ne in H1; [|rewrite -EQlenEL;done].
        unfold OmoAuth_E_EL_valid in E_EL_VALID. eapply E_EL_VALID; try done.
    + unfold not. intros. apply (f_equal length) in H0. rewrite app_length /= in H0. lia.
    + unfold not. intros. apply (f_equal length) in H0. rewrite omo_insert_r_length /= in H0. by destruct omo.
    + eapply history_wf_add; try done.
    + replace (length E + 1) with (length (E ++ [eV])); [|rewrite app_length /=;done].
      eapply hb_xo_add; try done.
  - rewrite OmoEview_eq. iDestruct "⊒M" as (?????) "[[%Hγe2 %NEmp'] BIGM]". encode_agree Hγe.
    iExists γtl,γel,γh,γg,γn. iSplit.
    { iPureIntro. split; [done|]. set_solver. }
    rewrite big_sepS_union; last first.
    { rewrite disjoint_singleton_l. unfold not. intros. specialize (Mvalid _ H0). rewrite lookup_lt_is_Some in Mvalid. lia. }
    iFrame "BIGM". rewrite big_sepS_singleton. iExists neinfo. iFrame "EL@en". subst neinfo. simpl. rewrite eVOUT. done.
  - have [[e'' es''] Hgen] : is_Some (omo !! gen).
    { rewrite lookup_lt_is_Some. apply lookup_omo_lt_Some in Heidx. done. }
    iExists (ro_event gen (length es'')). iPureIntro. split; [|done].
    rewrite lookup_omo_ro_event omo_insert_r_read_op list_lookup_alter /omo_read_op list_lookup_fmap Hgen /= lookup_app_1_eq. done.
Qed.

Lemma OmoAuth_insert_ro_gen γe γe' γs E omo stlist Vb M e' eV (gen : nat) st (e := length E) `{Interpretable eventT absStateT} :
  OmoAuth γe γs 1 E omo stlist _ -∗
  @{Vb} OmoEview γe M -∗
  OmoTokenR γe' e' -∗
  ⌜ stlist !! gen = Some st
  ∧ step e eV st st
  ∧ OmoUBgen omo M gen
  ∧ eV.(sync) = Vb
  ∧ eV.(eview) = {[e]} ∪ M ⌝
  ==∗
  OmoHbToken γe γs (E ++ [eV]) (omo_insert_r omo gen e) stlist e _ ∗
  @{Vb} OmoEview γe ({[e]} ∪ M) ∗
  OmoCW γe γe' e e' ∗
  OmoSnap γe γs e st ∗
  OmoEinfo γe e eV ∗
  OmoTokenR γe e.
Proof.
  iIntros "M● #⊒M RCOMMIT (%Hgenst & %STEP & %MAXgen & %eVOUT & %eVEVIEW)".
  iDestruct (OmoAuth_wf with "M●") as %[OMO_GOOD _].
  apply omo_stlist_length in OMO_GOOD as EQlenST.

  have [[ew es] Hgen] : is_Some (omo !! gen).
  { rewrite lookup_lt_is_Some EQlenST. apply lookup_lt_Some in Hgenst. done. }
  have Hew : lookup_omo omo (wr_event gen) = Some ew by rewrite lookup_omo_wr_event /omo_write_op list_lookup_fmap Hgen.
  eapply lookup_omo_event_valid in Hew as VAL; [|done].
  iDestruct (OmoSnap_get _ _ _ _ _ _ _ (wr_event gen) with "M●") as "#ew↪st"; [done..|].
  iDestruct (OmoUB_from_gen _ _ _ _ _ _ _ _ _ (wr_event gen) with "M●") as "#MAXew"; [done..|].
  iMod (OmoAuth_insert_ro with "M● ⊒M RCOMMIT ew↪st MAXew []") as (gen')
    "(M● & #⊒M' & #e↦e' & #ew=e & #e✓eV & RCOMMIT & (%eidx & %Heidx & %EQgen))"; [done|].

  set omo' := omo_insert_r omo gen' (length E).
  have Hew' : lookup_omo omo' (wr_event gen) = Some ew.
  { rewrite lookup_omo_wr_event omo_insert_r_write_op -lookup_omo_wr_event. done. }

  iAssert (⌜ gen = gen' ⌝)%I with "[-]" as %<-.
  { iDestruct (OmoHbToken_finish with "M●") as "M●".
    iDestruct (OmoEq_Eq with "M● ew=e") as %EQ; [done..|]. simpl in *. rewrite EQ EQgen. done. }
  iDestruct (OmoSnap_get_from_Eq with "ew↪st ew=e") as "e↪st".

  iModIntro. iFrame "∗#%".
Qed.

Lemma OmoAuth_insert_last γe γe' γs E omo stlist (st st' : absStateT) Vb M e' eV (e := length E) `{Interpretable eventT absStateT} :
  OmoAuth γe γs 1 E omo stlist _ -∗
  @{Vb} OmoEview γe M -∗
  OmoTokenW γe' e' -∗
  ⌜ last stlist = Some st ∧ step e eV st st' ∧ eV.(eview) = {[e]} ∪ M ∧ eV.(sync) = Vb ⌝
  ==∗
  OmoHbToken γe γs (E ++ [eV]) (omo_append_w omo e []) (stlist ++ [st']) e _ ∗
  @{Vb} OmoEview γe ({[e]} ∪ M) ∗
  OmoCW γe γe' e e' ∗
  OmoEinfo γe e eV ∗
  OmoSnap γe γs e st' ∗
  OmoTokenW γe e.
Proof.
  iIntros "M● #⊒M WCOMMIT (%LASTst & %STEP & %EVIEW & %eVOUT)".
  iDestruct (OmoAuth_OmoEview_obj with "M● ⊒M") as %Mvalid.
  iDestruct (OmoEview_nonempty_obj with "⊒M") as %NEmp.
  rewrite OmoAuth_eq. iDestruct "M●" as (??????????)
    "(%&%& [%Hγe %Hγs] & TL● & EL● & WL● & SL● & Hγq & HL● & Hγg & EL✓ & WL✓ & #ELEMS & #KEYS & Pures)".
  iDestruct "Pures" as %(EQlenTL & EQlenEL & E_TL_VALID & E_EL_VALID & MONOqg & QM_VALID & Nomo & NE & HWF & LHB & OMO_GOOD).

  iAssert (⌜ (length WL = length omo ∧ length stlist = length omo)%nat ⌝)%I with "[-]" as %[EQlenWL EQlenST].
  { rewrite /OmoAuth_WL_valid. iDestruct (big_sepL2_length with "WL✓") as %?.
    apply omo_stlist_length in OMO_GOOD. by rewrite -OMO_GOOD H0. }

  set E' := E ++ [eV].
  set omo' := omo_append_w omo e [].
  set gen := length omo.
  set stlist' := stlist ++ [st'].
  have OMO_GOOD' : Linearizability_omo E' omo' stlist'.
  { eapply Linearizability_omo_append_w; try done. by rewrite last_cons LASTst. }
  iMod (ghost_var_update (γs,E',omo',stlist') with "Hγg") as "Hγg".
  iMod (mono_list_auth_own_update E' with "HL●") as "[HL● #HL◯]"; [by eapply prefix_app_r|].
  iDestruct (@mono_list_idx_own_get _ _ _ _ _ e with "HL◯") as "#HL@e"; [by rewrite lookup_app_1_eq|].

  rewrite OmoTokenW_eq.
  iDestruct "WCOMMIT" as (γtl' γel' γh' γg' γn' einfo' γgl' γb') "([%Hγe' %Heinfo'] & #EL'@e' & GL'● & #Hγb')".
  iMod (@mono_list_own_alloc (gname * event_id) _ _ [(γe,e)]) as (γgl) "[GL● #GL◯]".
  iMod (@mono_list_own_alloc (gname * event_id) _ _ []) as (γgls) "[GLs● #GLs◯]".
  iMod (own_alloc (to_agree true)) as (γb) "#Hγb"; [done|].
  have [winfol Hwinfol] : is_Some (last WL).
  { rewrite last_is_Some. unfold not. intros. subst WL. by destruct omo. }
  set einfo := (encode (γgl,γb), Some γgl', eV.(sync), eV.(eview), (winfol.2 + 1)%Qp, γgls).
  set EL' := EL ++ [einfo].
  iMod (mono_list_auth_own_update EL' with "EL●") as "[EL● #EL◯]"; [by eapply prefix_app_r|].
  iDestruct (@mono_list_idx_own_get _ _ _ _ _ e with "EL◯") as "#EL@e".
  { subst EL' e. rewrite EQlenEL. by rewrite lookup_app_1_eq. }

  set TL' := TL ++ [eV.(type)].
  iMod (mono_list_auth_own_update TL' with "TL●") as "[TL● #TL◯]"; [by eapply prefix_app_r|].
  iDestruct (@mono_list_idx_own_get _ _ _ _ _ e with "TL◯") as "#TL@e".
  { subst TL' e. rewrite EQlenTL. by rewrite lookup_app_1_eq. }

  iMod (mono_list_auth_own_update stlist' with "SL●") as "[SL● #SL◯]"; [by eapply prefix_app_r|].
  iDestruct (@mono_list_idx_own_get _ _ _ _ _ gen with "SL◯") as "#SL@gen".
  { subst stlist' gen. rewrite -EQlenST lookup_app_1_eq. done. }

  iMod (@mono_list_own_alloc event_id _ _ []) as (γrl) "[RL● #RL◯]".
  set WL' := WL ++ [(e, γrl, einfo.1.2)].
  iMod (mono_list_auth_own_update WL' with "WL●") as "[WL● #WL◯]"; [by eapply prefix_app_r|].
  iDestruct (@mono_list_idx_own_get _ _ _ _ _ gen with "WL◯") as "#WL@gen".
  { subst WL' gen. rewrite -EQlenWL lookup_app_1_eq. done. }
  have MONOqg' : OmoAuth_qg_mono WL'.
  { unfold OmoAuth_qg_mono in *. intros. destruct (decide (n2 = length WL)) as [->|NEQ].
    - rewrite lookup_app_1_eq in H1. inversion H1. subst winfo2. clear H1. simpl.
      have LT : (winfol.2 < winfol.2 + 1)%Qp by apply Qp.lt_add_l.
      eapply Qp.le_lt_trans; [|exact LT]. clear LT.
      destruct (decide (n1 = length WL - 1)) as [->|NEQ'].
      + rewrite last_lookup in Hwinfol. replace (Init.Nat.pred (length WL)) with (length WL - 1) in Hwinfol by lia.
        rewrite lookup_app_l in H0; [|lia]. rewrite Hwinfol in H0. inversion H0. subst winfo1. clear H0. done.
      + rewrite last_lookup in Hwinfol. replace (Init.Nat.pred (length WL)) with (length WL - 1) in Hwinfol by lia.
        rewrite lookup_app_l in H0; [|lia].
        have CONDLT : n1 < length WL - 1 by lia.
        specialize (MONOqg _ _ _ _ H0 Hwinfol CONDLT). by apply Qp.lt_le_incl.
    - have LT : n2 < length WL.
      { apply lookup_lt_Some in H1. rewrite app_length /= in H1. lia. }
      rewrite lookup_app_l in H0; [|lia]. rewrite lookup_app_l in H1; [|lia].
      eapply MONOqg; done. }

  have NInclQM : QM !! einfo.1.2 = None.
  { destruct (QM !! einfo.1.2) as [i|] eqn:Heq; [|done].
    unfold OmoAuth_QM_valid in *. specialize (QM_VALID einfo.1.2 i). rewrite -QM_VALID in Heq.
    apply list_lookup_fmap_inv in Heq as [winfo [EQ Hwinfo]].
    rewrite last_lookup EQlenWL in Hwinfol. replace (Init.Nat.pred (length omo)) with (length omo - 1) in Hwinfol by lia.
    destruct (decide (i = (length omo - 1))) as [->|NEQ].
    - rewrite Hwinfo in Hwinfol. inversion Hwinfol. subst winfo. subst einfo. simpl in EQ. by apply Qp.add_id_free in EQ.
    - have LT : i < length omo - 1.
      { apply lookup_lt_Some in Hwinfo. rewrite EQlenWL in Hwinfo. lia. }
      unfold OmoAuth_qg_mono in *. specialize (MONOqg _ _ _ _ Hwinfo Hwinfol LT). rewrite -EQ in MONOqg. subst einfo.
      simpl in MONOqg. apply Qp.lt_nge in MONOqg. exfalso. apply MONOqg. apply Qp.le_add_l. }
  iMod (ghost_map_insert_persist einfo.1.2 gen with "Hγq") as "[Hγq #KEY@gen]"; [done|].
  set QM' := <[einfo.1.2:=gen]> QM.
  iAssert (OmoAuth_qg_keys γq QM')%I with "[-]" as "#KEYS'".
  { iApply big_sepM_insert; [done|]. iFrame "#". }

  iAssert (|==> OmoTokenW_def γe e ∗ OmoCW γe γe' e e')%I with "[GL● GL'●]" as ">[WCOMMIT #e↦e']".
  { iMod (mono_list_auth_own_update [(γe',e');(γe,e)] with "GL'●") as "[GL'● #GL'◯]".
    { replace [(γe',e');(γe,e)] with ([(γe',e')] ++ [(γe,e)]); [|by simplify_list_eq]. by eapply prefix_app_r. }
    iDestruct (@mono_list_idx_own_get _ _ _ _ _ 0 with "GL'◯") as "GL'@0"; [done|].
    iDestruct (@mono_list_idx_own_get _ _ _ _ _ 1 with "GL'◯") as "GL'@1"; [done|].
    iModIntro. iSplitL.
    - iExists γtl,γel,γh,γg,γn,einfo,γgl,γb. iFrame "GL● EL@e Hγb". iPureIntro. split_and!; done.
    - rewrite OmoCW_eq. iExists γtl,γel,γh,γg,γn. iExists γtl',γel',γh',γg',γn'. iExists einfo,einfo',γgl',γb'. iFrame "EL'@e' EL@e GL'@0 GL'@1".
      iPureIntro. split_and!; try done. }

  iAssert (OmoAuth_WL_valid γs γel 1 omo' WL')%I with "[WL✓ RL●]" as "WL✓".
  { rewrite /OmoAuth_WL_valid. subst omo' WL'. rewrite /omo_append_w.
    iApply (big_sepL2_app with "WL✓"). rewrite big_sepL2_singleton. iExists e,[],γrl,einfo. iFrame "RL● EL@e".
    rewrite big_sepL_nil. iPureIntro. split_and!; try done. }

  iAssert (OmoEinfo γe e eV)%I with "[-]" as "#e✓eV".
  { rewrite OmoEinfo_eq. iExists γtl,γel,γh,γg,γn,eV.(type),einfo. iFrame "#". iSplit; [done|repeat iSplit].
    - rewrite EVIEW. replace ({[e]} ∪ ({[e]} ∪ M)) with ({[e]} ∪ M); [|set_solver].
      iApply big_sepS_forall. iIntros "%e'' %IN".
      have CASE : e'' = e ∨ e'' ∈ M by set_solver.
      destruct CASE as [->|IN'].
      + rewrite OmoLe_eq. iExists γtl,γel,γh,γg,γn,einfo,einfo. iFrame "#". done.
      + rewrite OmoEview_eq OmoLe_eq.
        iDestruct "⊒M" as (?????) "[[%Hγe'' %NEmp'] BIG]". encode_agree Hγe.
        rewrite big_sepS_elem_of; [|exact IN']. iDestruct "BIG" as (einfo'') "[EL@e'' _]".
        rewrite view_at_objective_iff.
        iExists γtl,γel,γh,γg,γn,einfo'',einfo. iFrame "#". iSplit; [done|].

        iAssert (∃ i winfo, ⌜ WL' !! i = Some winfo ∧ winfo.2 = einfo''.1.2 ⌝)%I with "[-]" as %(i & winfo & Hwinfo & EQ).
        { iDestruct (mono_list_auth_idx_lookup with "EL● EL@e''") as %LOOKUP.
          apply lookup_lt_Some in LOOKUP as LT. replace (length EL') with (length E') in LT; last first.
          { subst E' EL'. rewrite !app_length /=. lia. }
          rewrite -lookup_lt_is_Some in LT. eapply lookup_omo_surjective in LT as [eidx Heidx]; [|done].
          have [[e''' es'''] Hgen] : is_Some (omo' !! (gen_of eidx)).
          { rewrite lookup_lt_is_Some. apply lookup_omo_lt_Some in Heidx. done. }
          have [winfo Hwinfo] : is_Some (WL' !! (gen_of eidx)).
          { rewrite lookup_lt_is_Some. apply lookup_lt_Some in Hgen. subst WL' omo'. rewrite app_length /=. rewrite omo_append_w_length in Hgen. lia. }
          iDestruct (big_sepL2_lookup with "WL✓") as (????) "([%EQ1 %EQ2] & RL● & #EL@e''' & BIG)"; [done|done|].
          inversion EQ1. subst e0 es winfo. clear EQ1.
          iExists (gen_of eidx),(e''',γrl0,einfo0.1.2). iSplit; [done|].
          destruct eidx.
          - rewrite lookup_omo_ro_event /omo_read_op list_lookup_fmap Hgen /= in Heidx.
            iDestruct (big_sepL_lookup with "BIG") as (?) "[#EL@e''a %EQ]"; [done|].
            iDestruct (mono_list_idx_agree with "EL@e'' EL@e''a") as %<-. done.
          - rewrite lookup_omo_wr_event /omo_write_op list_lookup_fmap Hgen /= in Heidx. inversion Heidx. subst e'''.
            iDestruct (mono_list_idx_agree with "EL@e'' EL@e'''") as %<-. done. }
        have Hwinfo' : WL' !! (length WL) = Some (e, γrl, einfo.1.2) by rewrite lookup_app_1_eq.
        destruct (decide (i = length WL)) as [->|NEQ].
        * rewrite Hwinfo in Hwinfo'. inversion Hwinfo'. subst winfo. simpl in EQ. rewrite -EQ. subst einfo. simpl. done.
        * have CONDLT : i < length WL.
          { apply lookup_lt_Some in Hwinfo. subst WL'. rewrite app_length /= in Hwinfo. lia. }
          specialize (MONOqg' _ _ _ _ Hwinfo Hwinfo' CONDLT). rewrite EQ /= in MONOqg'. subst einfo. simpl. iPureIntro. by apply Qp.lt_le_incl.
    - rewrite EVIEW eVOUT. replace ({[e]} ∪ ({[e]} ∪ M)) with ({[e]} ∪ M); [|set_solver].
      rewrite -OmoEview_split; [|set_solver-|set_solver]. iFrame "⊒M". rewrite OmoEview_eq.
      iExists γtl,γel,γh,γg,γn. iSplit.
      { iPureIntro. split; [done|]. set_solver-. }
      rewrite big_sepS_singleton. iExists einfo. iFrame "#". subst einfo. simpl. rewrite eVOUT. done. }
  iAssert (OmoAuth_all_elem γe E')%I with "[-]" as "#ELEMS'".
  { iApply big_sepL_snoc. iFrame "ELEMS e✓eV". }

  iModIntro. iFrame "WCOMMIT e↦e' e✓eV". iSplitL; [|repeat iSplit].
  - rewrite OmoHbToken_eq. iExists γtl,γel,γh,γg,γn,γwl,γsl,γq. iExists TL',EL',WL',QM',einfo,[].
    iFrame. replace (take (length EL' - 1) EL') with EL; last first.
    { subst EL'. rewrite app_length /= Nat.add_sub take_app. done. }
    iFrame "EL✓ ELEMS' KEYS'". rewrite big_sepL_nil. iPureIntro. split_and!; try done.
    + subst E' TL'. rewrite !app_length EQlenTL /=. done.
    + subst E' EL'. rewrite !app_length /=. lia.
    + subst EL'. rewrite app_length /= Nat.add_sub. done.
    + subst EL'. rewrite last_app. done.
    + subst E' TL'. rewrite /OmoAuth_E_TL_valid. intros. destruct (decide (e0 = length E)) as [->|NEQ].
      * rewrite lookup_app_1_eq in H0. rewrite EQlenTL lookup_app_1_eq in H1. inversion H0. inversion H1. subst eV0 ty. done.
      * rewrite lookup_app_1_ne in H0; [|done]. rewrite lookup_app_1_ne in H1; [|rewrite -EQlenTL;done].
        rewrite /OmoAuth_E_TL_valid in E_TL_VALID. eapply E_TL_VALID; try done.
    + subst E' EL'. rewrite /OmoAuth_E_EL_valid. intros. destruct (decide (e0 = length E)) as [->|NEQ].
      * rewrite lookup_app_1_eq in H0. rewrite EQlenEL lookup_app_1_eq in H1. inversion H0. inversion H1. subst eV0 einfo0. done.
      * rewrite lookup_app_1_ne in H0; [|done]. rewrite lookup_app_1_ne in H1; [|rewrite -EQlenEL;done].
        rewrite /OmoAuth_E_EL_valid in E_EL_VALID. eapply E_EL_VALID; try done.
    + unfold OmoAuth_QM_valid in *. intros. destruct (decide (i = length WL)) as [->|NEQ].
      * rewrite list_lookup_fmap lookup_app_1_eq /=. split; intros.
        -- inversion H0. subst qg QM' einfo. simpl. rewrite lookup_insert. subst gen. rewrite EQlenWL. done.
        -- subst QM'. destruct (decide (qg = einfo.1.2)) as [->|NEQ]; [done|].
           rewrite lookup_insert_ne in H0; [|done]. specialize (QM_VALID qg (length WL)). rewrite -QM_VALID in H0.
           apply lookup_lt_Some in H0. rewrite fmap_length in H0. lia.
      * rewrite list_lookup_fmap lookup_app_1_ne /=; [|done]. split; intros.
        -- destruct (decide (qg = einfo.1.2)) as [->|NEQ'].
           ++ specialize (QM_VALID einfo.1.2 i). rewrite list_lookup_fmap in QM_VALID. rewrite QM_VALID in H0. rewrite H0 in NInclQM. done.
           ++ rewrite lookup_insert_ne; [|done]. specialize (QM_VALID qg i). rewrite list_lookup_fmap in QM_VALID. rewrite QM_VALID in H0. done.
        -- destruct (decide (qg = einfo.1.2)) as [->|NEQ'].
           ++ rewrite lookup_insert in H0. inversion H0. subst i.
              specialize (QM_VALID einfo.1.2 gen). rewrite list_lookup_fmap in QM_VALID. rewrite QM_VALID. done.
           ++ rewrite lookup_insert_ne in H0; [|done]. specialize (QM_VALID qg i). rewrite -QM_VALID list_lookup_fmap in H0. done.
    + unfold not. intros. subst E'. apply (f_equal length) in H0. rewrite app_length /= in H0. lia.
    + unfold not. intros. subst omo'. apply (f_equal length) in H0. rewrite omo_append_w_length /= in H0. lia.
    + subst E'. eapply history_wf_add; try done.
    + subst E'. apply hb_xo_add; try done.
  - rewrite OmoEview_eq. iDestruct "⊒M" as (?????) "[[%Hγe2 %NEmp'] BIGM]". encode_agree Hγe.
    iExists γtl,γel,γh,γg,γn. iSplit.
    { iPureIntro. split; [done|]. set_solver-. }
    rewrite big_sepS_union; last first.
    { rewrite disjoint_singleton_l. unfold not. intros. specialize (Mvalid _ H0). rewrite lookup_lt_is_Some in Mvalid. lia. }
    iFrame "BIGM". rewrite big_sepS_singleton. iExists einfo. iFrame "EL@e". subst einfo. simpl. rewrite eVOUT. done.
  - rewrite OmoSnap_eq. iExists γtl,γel,γh,γg,γn,γwl,γsl,γq. iExists gen,einfo. iFrame "#". iPureIntro. split_and!; try done.
Qed.

Lemma OmoAuth_insert γe γe' γs E omo (stlist stnew : list absStateT) (st : absStateT) Vb M gen e' eV
  (e := length E) `{Interpretable eventT absStateT} :
  OmoAuth γe γs 1 E omo stlist _ -∗
  @{Vb} OmoEview γe M -∗
  OmoTokenW γe' e' -∗
  ⌜ eV.(sync) = Vb
  ∧ eV.(eview) = {[e]} ∪ M
  ∧ stlist !! gen = Some st
  ∧ OmoUBgen omo M gen
  ∧ interp_omo (E ++ [eV]) ((e, []) :: (drop (gen + 1)%nat omo)) st stnew ⌝
  ==∗
  ∃ γs',
    OmoHbToken γe γs' (E ++ [eV]) (omo_insert_w omo (gen + 1) e []) (take (gen + 1)%nat stlist ++ stnew) e _ ∗
    @{Vb} OmoEview γe ({[e]} ∪ M) ∗
    OmoCW γe γe' e e' ∗
    OmoEinfo γe e eV ∗
    OmoTokenW γe e.
Proof.
  iIntros "M● #⊒M WCOMMIT (%eVOUT & %EVIEW & %STgen & %MAXgen & %GEN_GOOD)".
  destruct (decide (gen = length omo - 1)) as [->|NEgen].
  { iDestruct (OmoAuth_wf with "M●") as %[OMO_GOOD _]. apply omo_stlist_length in OMO_GOOD.
    iDestruct (OmoAuth_omo_nonempty with "M●") as %Nomo.
    have [st' [COND1 [COND2 COND3]]] : ∃ st', last stlist = Some st ∧ step (length E) eV st st' ∧ stnew = [st'].
    { rewrite Nat.sub_add in GEN_GOOD; [|by destruct omo; try done; simpl; lia].
      rewrite drop_ge in GEN_GOOD; [|done]. apply interp_omo_length in GEN_GOOD as EQlenst. simpl in EQlenst.
      inversion GEN_GOOD.
      have EQ : omo0 ++ [(e0, es)] = [] ++ [(e, [])] by simplify_list_eq.
      apply app_inj_2 in EQ as [-> EQ]; [|done]. inversion EQ. subst st1 stnew e0 es E0. clear H0 EQ.
      destruct H2 as (H1 & H2 & H3 & H4 & H5).
      subst e. rewrite lookup_app_1_eq in H1. inversion H1. subst eV0. clear H1.
      rewrite app_length /= in EQlenst. destruct stlist0; [|by simpl in *; lia].
      inversion H3. subst st2. exists st3. split_and!.
      - rewrite last_lookup. replace (Init.Nat.pred (length stlist)) with (length stlist - 1) by lia.
        rewrite -OMO_GOOD. done.
      - done.
      - by simplify_list_eq. }
    iMod (OmoAuth_insert_last with "M● ⊒M WCOMMIT []") as "(M● & #⊒M' & #e↦e' & #e✓eV & #e↪st' & WCOMMIT)"; [by iPureIntro; split_and!|].
    iModIntro. iExists γs. rewrite Nat.sub_add; [|by destruct omo; try done; simpl; lia].
    rewrite omo_insert_w_append_w; [|done]. rewrite take_ge; [|by rewrite OMO_GOOD]. subst stnew. iFrame. iFrame "⊒M' e↦e' e✓eV". }

  iDestruct (OmoAuth_OmoEview_obj with "M● ⊒M") as %Mvalid.
  iDestruct (OmoEview_nonempty_obj with "⊒M") as %NEmp.
  rewrite OmoAuth_eq. iDestruct "M●" as (??????????)
    "(%&%& [%Hγe %Hγs] & TL● & EL● & WL● & SL● & Hγq & HL● & Hγg & EL✓ & WL✓ & #ELEMS & #KEYS & Pures)".
  iDestruct "Pures" as %(EQlenTL & EQlenEL & E_TL_VALID & E_EL_VALID & MONOqg & QM_VALID & Nomo & NE & HWF & LHB & OMO_GOOD).

  iAssert (⌜ (length WL = length omo ∧ length stlist = length omo)%nat ⌝)%I with "[-]" as %[EQlenWL EQlenST].
  { rewrite /OmoAuth_WL_valid. iDestruct (big_sepL2_length with "WL✓") as %?.
    apply omo_stlist_length in OMO_GOOD. by rewrite -OMO_GOOD H0. }

  set E' := E ++ [eV].
  set omo' := omo_insert_w omo (gen + 1) e [].
  set stlist' := take (gen + 1) stlist ++ stnew.
  have OMO_GOOD' : Linearizability_omo E' omo' stlist'.
  { eapply Linearizability_omo_insert_w; try done.
    - rewrite last_cons. replace (gen + 1) with (S gen) by lia. rewrite (take_S_r _ _ st); [|done].
      rewrite last_app. done.
    - intros. rewrite /OmoUBgen in MAXgen. specialize (MAXgen _ H0) as (eidx' & Heidx' & LE).
      eapply lookup_omo_inj in Heidx'; [|done|exact H1]. subst eidx'. lia. }
  iMod (mono_list_auth_own_update E' with "HL●") as "[HL● #HL◯]"; [by eapply prefix_app_r|].
  iDestruct (@mono_list_idx_own_get _ _ _ _ _ e with "HL◯") as "#HL@e"; [by rewrite lookup_app_1_eq|].

  rewrite OmoTokenW_eq.
  iDestruct "WCOMMIT" as (γtl' γel' γh' γg' γn' einfo' γgl' γb') "([%Hγe' %Heinfo'] & #EL'@e' & GL'● & #Hγb')".
  iMod (@mono_list_own_alloc (gname * event_id) _ _ [(γe,e)]) as (γgl) "[GL● #GL◯]".
  iMod (@mono_list_own_alloc (gname * event_id) _ _ []) as (γgls) "[GLs● #GLs◯]".
  iMod (own_alloc (to_agree true)) as (γb) "#Hγb"; [done|].
  have NZomo : length omo ≠ 0 by destruct omo.
  have [winfol Hwinfol] : is_Some (WL !! gen).
  { rewrite lookup_lt_is_Some EQlenWL -EQlenST. apply lookup_lt_Some in STgen. done. }
  have [winfor Hwinfor] : is_Some (WL !! (S gen)).
  { rewrite lookup_lt_is_Some EQlenWL. apply lookup_lt_Some in Hwinfol. rewrite EQlenWL in Hwinfol. lia. }

  set einfo := (encode (γgl,γb), Some γgl', eV.(sync), eV.(eview), ((winfol.2 + winfor.2) / 2)%Qp, γgls).
  set EL' := EL ++ [einfo].
  iMod (mono_list_auth_own_update EL' with "EL●") as "[EL● #EL◯]"; [by eapply prefix_app_r|].
  iDestruct (@mono_list_idx_own_get _ _ _ _ _ e with "EL◯") as "#EL@e".
  { subst EL' e. rewrite EQlenEL. by rewrite lookup_app_1_eq. }

  set TL' := TL ++ [eV.(type)].
  iMod (mono_list_auth_own_update TL' with "TL●") as "[TL● #TL◯]"; [by eapply prefix_app_r|].
  iDestruct (@mono_list_idx_own_get _ _ _ _ _ e with "TL◯") as "#TL@e".
  { subst TL' e. rewrite EQlenTL. by rewrite lookup_app_1_eq. }

  iMod (@mono_list_own_alloc event_id _ _ []) as (γrl) "[RL● #RL◯]".
  set WL' := take (gen + 1) WL ++ [(e, γrl, einfo.1.2)] ++ drop (gen + 1) WL.
  iMod (mono_list_own_alloc WL') as (γwl') "[WL'● #WL'◯]".
  iMod (mono_list_own_alloc stlist') as (γsl') "[SL'● #SL'◯]".

  have MONOqg' : OmoAuth_qg_mono WL'.
  { unfold OmoAuth_qg_mono in *. intros. subst WL'.
    destruct (decide (n1 = (gen + 1))) as [->|NE1]; destruct (decide (n2 = (gen + 1))) as [->|NE2].
    - lia.
    - have GENeq : length (take (gen + 1) WL) = gen + 1.
      { rewrite take_length Nat.min_l; [done|].
        apply lookup_lt_Some in Hwinfol. lia. }
      rewrite lookup_app_r in H0; [|rewrite GENeq;lia].
      rewrite GENeq in H0. replace (gen + 1 - (gen + 1)) with 0 in H0 by lia.
      simpl in H0. inversion H0. subst winfo1. simpl. clear H0.
      rewrite lookup_app_r in H1; [|rewrite GENeq;lia].
      rewrite GENeq lookup_app_r in H1; [|simpl;lia]. simpl in H1.
      have LE : (winfor.2 ≤ winfo2.2)%Qp.
      { destruct (decide (n2 = gen + 2)) as [->|NEQ].
        - replace (gen + 2 - (gen + 1) - 1) with 0 in H1 by lia.
          rewrite lookup_drop Nat.add_0_r in H1.
          replace (gen + 1) with (S gen) in H1 by lia.
          rewrite Hwinfor in H1. inversion H1. subst winfo2. done.
        - rewrite lookup_drop in H1.
          have CONDLT : S gen < gen + 1 + (n2 - (gen + 1) - 1) by lia.
          specialize (MONOqg _ _ _ _ Hwinfor H1 CONDLT).
          apply Qp.lt_le_incl. done. }
      have LELR : (winfol.2 < winfor.2)%Qp.
      { have CONDLT : gen < S gen by lia. specialize (MONOqg _ _ _ _ Hwinfol Hwinfor CONDLT). done. }
      eapply Qp.lt_le_trans; try done.
      have EQ : (winfor.2 = (winfor.2 + winfor.2) / 2)%Qp.
      { rewrite Qp.add_diag Qp.mul_comm. unfold Qp.div. rewrite -Qp.mul_assoc.
        replace (2 * /2)%Qp with (2 / 2)%Qp; [|by unfold Qp.div].
        rewrite Qp.div_diag Qp.mul_1_r. done. }
      rewrite {2}EQ -Qp.div_lt_mono_r -Qp.add_lt_mono_r. done.
    - have GENeq : length (take (gen + 1) WL) = gen + 1.
      { rewrite take_length Nat.min_l; [done|].
        apply lookup_lt_Some in Hwinfol. lia. }
      rewrite lookup_app_r in H1; [|by rewrite GENeq;lia].
      replace (gen + 1 - length (take (gen + 1) WL)) with 0 in H1 by lia. simpl in H1. inversion H1. subst winfo2. clear H1. simpl.
      rewrite lookup_app_l in H0; [|lia].
      rewrite lookup_take in H0; [|lia].
      have LE : (winfo1.2 ≤ winfol.2)%Qp.
      { destruct (decide (n1 = gen)) as [->|NEQ].
        - rewrite Hwinfol in H0. inversion H0. done.
        - have CONDLT : n1 < gen by lia.
          specialize (MONOqg _ _ _ _ H0 Hwinfol CONDLT). apply Qp.lt_le_incl. done. }
      eapply Qp.le_lt_trans; try done.
      have LELR : (winfol.2 < winfor.2)%Qp.
      { have CONDLT : gen < S gen by lia. specialize (MONOqg _ _ _ _ Hwinfol Hwinfor CONDLT). done. }
      have EQ : (winfol.2 = (winfol.2 + winfol.2) / 2)%Qp.
      { rewrite Qp.add_diag Qp.mul_comm. unfold Qp.div. rewrite -Qp.mul_assoc.
        replace (2 * /2)%Qp with (2 / 2)%Qp; [|by unfold Qp.div].
        rewrite Qp.div_diag Qp.mul_1_r. done. }
      rewrite {1}EQ -Qp.div_lt_mono_r -Qp.add_lt_mono_l. done.
    - have [n1' [n2' [LOOKUP1 [LOOKUP2 LT]]]] : ∃ n1' n2', WL !! n1' = Some winfo1 ∧ WL !! n2' = Some winfo2 ∧ n1' < n2'.
      { have GENeq : length (take (gen + 1) WL) = gen + 1.
        { rewrite take_length Nat.min_l; [done|].
          apply lookup_lt_Some in Hwinfol. lia. }
        have CASE : n2 < gen + 1 ∨ (n1 < gen + 1 ∧ gen + 1 < n2) ∨ (gen + 1 < n1) by lia.
        destruct CASE as [COMP2|[[COMP1 COMP2]|COMP1]].
        - rewrite lookup_app_l in H0; [|by rewrite GENeq;lia].
          rewrite lookup_take in H0; [|lia].
          rewrite lookup_app_l in H1; [|by rewrite GENeq;lia].
          rewrite lookup_take in H1; [|lia].
          exists n1,n2. split_and!; try done.
        - rewrite lookup_app_l in H0; [|by rewrite GENeq;lia].
          rewrite lookup_take in H0; [|lia].
          rewrite lookup_app_r in H1; [|by rewrite GENeq;lia]. rewrite GENeq in H1.
          rewrite lookup_app_r in H1; [|simpl;lia].
          rewrite lookup_drop /= in H1. replace (gen + 1 + (n2 - (gen + 1) - 1)) with (n2 - 1) in H1 by lia.
          exists n1,(n2 - 1). split_and!; try done. lia.
        - rewrite lookup_app_r in H0; [|by rewrite GENeq;lia]. rewrite GENeq in H0.
          rewrite lookup_app_r in H0; [|simpl;lia].
          rewrite lookup_drop /= in H0. replace (gen + 1 + (n1 - (gen + 1) - 1)) with (n1 - 1) in H0 by lia.
          rewrite lookup_app_r in H1; [|by rewrite GENeq;lia]. rewrite GENeq in H1.
          rewrite lookup_app_r in H1; [|simpl;lia].
          rewrite lookup_drop /= in H1. replace (gen + 1 + (n2 - (gen + 1) - 1)) with (n2 - 1) in H1 by lia.
          exists (n1 - 1),(n2 - 1). split_and!; try done. lia. }
      specialize (MONOqg _ _ _ _ LOOKUP1 LOOKUP2 LT). done. }

  iMod (@ghost_map_alloc_empty _ Qp nat) as (γq') "Hγq'".
  iAssert (|==> ∃ QM', ⎡ghost_map_auth γq' 1 QM'⎤ ∗ OmoAuth_qg_keys γq' QM' ∗ ⌜ OmoAuth_QM_valid WL' QM' ⌝)%I
    with "[Hγq']" as ">(%QM' & Hγq' & #KEYS' & %QM_VALID')".
  { iClear "⊒M ELEMS KEYS HL◯ HL@e EL'@e' Hγb' GL◯ GLs◯ Hγb EL◯ EL@e TL◯ TL@e RL◯ WL'◯ SL'◯".
    have [i Hi] : ∃ i, WL' = take i WL' by exists (length WL'); rewrite take_ge.
    rewrite Hi. clear Hi. iInduction i as [] "IH".
    - iModIntro. iExists ∅. iFrame. iSplit.
      + by rewrite /OmoAuth_qg_keys big_sepM_empty.
      + iPureIntro. rewrite take_0. unfold OmoAuth_QM_valid. intros. done.
    - iMod ("IH" with "Hγq'") as (QM') "(Hγq' & #KEYS & %QM_VALID')".
      destruct (le_lt_dec (length WL') i) as [LE|LT].
      { repeat (rewrite take_ge; [|lia]). rewrite take_ge in QM_VALID'; [|lia].
        iModIntro. iExists QM'. iFrame "∗#%". }
      rewrite -lookup_lt_is_Some in LT. destruct LT as [winfo Hwinfo].
      have NInclQM : QM' !! winfo.2 = None.
      { destruct (QM' !! winfo.2) as [i'|] eqn:Heq; [|done].
        unfold OmoAuth_QM_valid in *. specialize (QM_VALID' winfo.2 i'). rewrite -QM_VALID' in Heq.
        apply list_lookup_fmap_inv in Heq as [winfo' [EQ' Hwinfo']].
        rewrite lookup_take_Some in Hwinfo'. destruct Hwinfo' as [Hwinfo' LT].
        specialize (MONOqg' _ _ _ _ Hwinfo' Hwinfo LT). rewrite EQ' in MONOqg'. by apply Qp.lt_strict in MONOqg'. }
      iMod (ghost_map_insert_persist winfo.2 i with "Hγq'") as "[Hγq' #KEYi]"; [done|].
      iModIntro. iExists (<[winfo.2:=i]> QM'). iFrame "Hγq'". iSplitL.
      + iApply big_sepM_insert; [done|]. iFrame "#".
      + iPureIntro. unfold OmoAuth_QM_valid. intros. split; intros.
        * destruct (decide (i0 = i)) as [->|NEQ].
          -- rewrite list_lookup_fmap lookup_take in H0; [|lia]. rewrite Hwinfo in H0. inversion H0. subst qg.
             rewrite lookup_insert. done.
          -- apply list_lookup_fmap_inv in H0 as [winfo' [EQ Hwinfo']]. subst qg.
             rewrite lookup_take_Some in Hwinfo'. destruct Hwinfo' as [Hwinfo' LT].
             have CONDLT : i0 < i by lia.
             specialize (MONOqg' _ _ _ _ Hwinfo' Hwinfo CONDLT).
             unfold OmoAuth_QM_valid in *.
             specialize (QM_VALID' winfo'.2 i0).
             rewrite lookup_insert_ne; last first.
             { unfold not. intros. rewrite H0 in MONOqg'. by apply Qp.lt_strict in MONOqg'. }
             rewrite -QM_VALID'. rewrite list_lookup_fmap lookup_take; [|lia]. rewrite Hwinfo'. done.
        * destruct (decide (qg = winfo.2)) as [->|NEQ].
          -- rewrite lookup_insert in H0. inversion H0. subst i0.
             rewrite list_lookup_fmap lookup_take; [|lia]. rewrite Hwinfo. done.
          -- rewrite lookup_insert_ne in H0; [|done]. specialize (QM_VALID' qg i0). rewrite -QM_VALID' in H0.
             apply list_lookup_fmap_inv in H0 as [winfo' [EQ Hwinfo']]. subst qg.
             rewrite lookup_take_Some in Hwinfo'. destruct Hwinfo' as [Hwinfo' LT].
             rewrite list_lookup_fmap lookup_take; [|lia]. rewrite Hwinfo'. done. }
  remember (encode (γwl',γsl',γq')) as γs' eqn:Hγs'.
  iMod (ghost_var_update (γs',E',omo',stlist') with "Hγg") as "Hγg".

  iAssert (|==> OmoTokenW_def γe e ∗ OmoCW γe γe' e e')%I with "[GL● GL'●]" as ">[WCOMMIT #e↦e']".
  { iMod (mono_list_auth_own_update [(γe',e');(γe,e)] with "GL'●") as "[GL'● #GL'◯]".
    { replace [(γe',e');(γe,e)] with ([(γe',e')] ++ [(γe,e)]); [|by simplify_list_eq]. by eapply prefix_app_r. }
    iDestruct (@mono_list_idx_own_get _ _ _ _ _ 0 with "GL'◯") as "GL'@0"; [done|].
    iDestruct (@mono_list_idx_own_get _ _ _ _ _ 1 with "GL'◯") as "GL'@1"; [done|].
    iModIntro. iSplitL.
    - iExists γtl,γel,γh,γg,γn,einfo,γgl,γb. iFrame "GL● EL@e Hγb". iPureIntro. split_and!; done.
    - rewrite OmoCW_eq. iExists γtl,γel,γh,γg,γn. iExists γtl',γel',γh',γg',γn'. iExists einfo,einfo',γgl',γb'. iFrame "EL'@e' EL@e GL'@0 GL'@1".
      iPureIntro. split_and!; try done. }

  iAssert (OmoAuth_WL_valid γs γel 1 omo' WL')%I with "[WL✓ RL●]" as "WL✓".
  { rewrite /OmoAuth_WL_valid. subst omo' WL'. rewrite /omo_insert_w.
    rewrite -{1}(take_drop (gen + 1) omo). rewrite -{3}(take_drop (gen + 1) WL).
    iDestruct (big_sepL2_app_inv with "WL✓") as "[WL✓ WL✓']".
    { left. have H1 : ∀ (a b : nat), (a < b)%nat → (a ≤ b)%nat by lia.
      rewrite !take_length Nat.min_l; last first.
      { apply lookup_lt_Some in Hwinfor. rewrite EQlenWL in Hwinfor. replace (gen + 1) with (S gen) by lia.
        apply H1. done. }
      rewrite Nat.min_l; [done|]. apply H1. apply lookup_lt_Some in Hwinfor. replace (gen + 1) with (S gen) by lia. done. }
    iApply (big_sepL2_app with "WL✓").
    have EQ : (e, []) :: drop (gen + 1) omo = [(e, [])] ++ drop (gen + 1) omo by simplify_list_eq.
    rewrite EQ. clear EQ. iApply (big_sepL2_app with "[RL●]"); [|done].
    rewrite big_sepL2_singleton. iExists e,[],γrl,einfo. iFrame "RL● EL@e". rewrite big_sepL_nil. iPureIntro. split_and!; try done. }

  iAssert (OmoEinfo γe e eV)%I with "[-]" as "#e✓eV".
  { rewrite OmoEinfo_eq. iExists γtl,γel,γh,γg,γn,eV.(type),einfo. iFrame "#". iSplit; [done|repeat iSplit].
    - rewrite EVIEW. replace ({[e]} ∪ ({[e]} ∪ M)) with ({[e]} ∪ M); [|set_solver].
      iApply big_sepS_forall. iIntros "%e'' %IN".
      destruct (decide (e'' = e)) as [->|NEe''].
      + rewrite OmoLe_eq. iExists γtl,γel,γh,γg,γn,einfo,einfo. iFrame "#". done.
      + have IN' : e'' ∈ M by set_solver.
        rewrite OmoEview_eq OmoLe_eq.
        iDestruct "⊒M" as (?????) "[[%Hγe'' %NEmp'] BIG]". encode_agree Hγe.
        rewrite big_sepS_elem_of; [|exact IN']. iDestruct "BIG" as (einfo'') "[EL@e'' _]".
        rewrite view_at_objective_iff.
        iExists γtl,γel,γh,γg,γn,einfo'',einfo. iFrame "#". iSplit; [done|].

        have EQlen : length (take (gen + 1) WL) = gen + 1.
          { rewrite take_length Nat.min_l; [done|]. apply lookup_lt_Some in Hwinfor. lia. }

        iAssert (∃ i winfo, ⌜ WL' !! i = Some winfo ∧ winfo.2 = einfo''.1.2 ∧ i ≤ gen + 1⌝)%I with "[-]" as %(i & winfo & Hwinfo & EQ & LE).
        { iDestruct (mono_list_auth_idx_lookup with "EL● EL@e''") as %LOOKUP.
          apply lookup_lt_Some in LOOKUP as LT. replace (length EL') with (length E') in LT; last first.
          { subst E' EL'. rewrite !app_length /=. lia. }
          rewrite -lookup_lt_is_Some in LT. eapply lookup_omo_surjective in LT as [eidx Heidx]; [|done].
          have [[e''' es'''] Hgen] : is_Some (omo' !! (gen_of eidx)).
          { rewrite lookup_lt_is_Some. apply lookup_omo_lt_Some in Heidx. done. }
          have [winfo Hwinfo] : is_Some (WL' !! (gen_of eidx)).
          { rewrite lookup_lt_is_Some. apply lookup_lt_Some in Hgen. subst WL' omo'. rewrite !app_length /= EQlen drop_length.
            apply lookup_lt_Some in Hwinfor. rewrite omo_insert_w_length -EQlenWL in Hgen. lia. }
          iDestruct (big_sepL2_lookup with "WL✓") as (????) "([%EQ1 %EQ2] & RL● & #EL@e''' & BIG)"; [done|done|].
          inversion EQ1. subst e0 es winfo. clear EQ1.
          iExists (gen_of eidx),(e''',γrl0,einfo0.1.2). iSplit; [done|]. iSplit.
          - destruct eidx.
            + rewrite lookup_omo_ro_event /omo_read_op list_lookup_fmap Hgen /= in Heidx.
              iDestruct (big_sepL_lookup with "BIG") as (?) "[#EL@e''a %EQ]"; [done|].
              iDestruct (mono_list_idx_agree with "EL@e'' EL@e''a") as %<-. done.
            + rewrite lookup_omo_wr_event /omo_write_op list_lookup_fmap Hgen /= in Heidx. inversion Heidx. subst e'''.
              iDestruct (mono_list_idx_agree with "EL@e'' EL@e'''") as %<-. done.
          - specialize (MAXgen _ IN') as (eidx' & Heidx' & LE).
            subst omo'. destruct (decide (eidx = wr_event (gen + 1))) as [->|NEQeidx].
            { have EQlen' : length (take (gen + 1) omo) = gen + 1.
              { rewrite take_length -EQlenWL Nat.min_l; [done|]. apply lookup_lt_Some in Hwinfor. lia. }
              rewrite /omo_insert_w /= lookup_app_r in Hgen; [|by rewrite EQlen'].
              rewrite EQlen' in Hgen. replace (gen + 1 - (gen + 1)) with 0 in Hgen by lia. simpl in Hgen. inversion Hgen. subst e''' es'''. done. }
            eapply lookup_omo_before_insert_w in Heidx as Heidx''; try done; last first.
            { apply lookup_lt_Some in Hwinfor. rewrite -EQlenWL. lia. }
            destruct Heidx'' as (eidx'' & Heidx'' & CASE).
            specialize (lookup_omo_inj _ _ _ _ _ _ OMO_GOOD Heidx' Heidx'') as EQ. subst eidx''.
            destruct (decide (gen_of eidx < gen + 1)).
            + subst eidx'. iPureIntro. lia.
            + destruct CASE as (H1 & H2 & H3). rewrite H2. lia. }
        have Hwinfo' : WL' !! (gen + 1) = Some (e, γrl, einfo.1.2).
        { rewrite lookup_app_r; [|by rewrite EQlen]. rewrite EQlen. replace (gen + 1 - (gen + 1)) with 0 by lia. simpl. done. }
        destruct (decide (i = gen + 1)) as [->|NEQ].
        * rewrite Hwinfo in Hwinfo'. inversion Hwinfo'. subst winfo. simpl in *. rewrite -EQ. done.
        * have CONDLT : i < gen + 1 by lia.
          specialize (MONOqg' _ _ _ _ Hwinfo Hwinfo' CONDLT). rewrite EQ /= in MONOqg'. subst einfo. simpl. iPureIntro. by apply Qp.lt_le_incl.
    - rewrite EVIEW eVOUT. replace ({[e]} ∪ ({[e]} ∪ M)) with ({[e]} ∪ M); [|set_solver].
      rewrite -OmoEview_split; [|set_solver-|set_solver]. iFrame "⊒M". rewrite OmoEview_eq.
      iExists γtl,γel,γh,γg,γn. iSplit.
      { iPureIntro. split; [done|]. set_solver-. }
      rewrite big_sepS_singleton. iExists einfo. iFrame "#". subst einfo. simpl. rewrite eVOUT. done. }
  iAssert (OmoAuth_all_elem γe E')%I with "[-]" as "#ELEMS'".
  { iApply big_sepL_snoc. iFrame "ELEMS e✓eV". }

  iModIntro. iExists γs'. iFrame "e↦e' WCOMMIT e✓eV". iSplitL.
  - rewrite OmoHbToken_eq. iExists γtl,γel,γh,γg,γn,γwl',γsl',γq'. iExists TL',EL',WL',QM',einfo,[].
    replace (take (length EL' - 1) EL') with EL; last first.
    { subst EL'. rewrite app_length /= Nat.add_sub take_app. done. }
    iFrame. iFrame "ELEMS' KEYS'". rewrite big_sepL_nil. iPureIntro. split_and!; try done.
    + subst E' TL'. rewrite !app_length /=. lia.
    + subst E' EL'. rewrite !app_length /=. lia.
    + subst EL'. rewrite app_length /= Nat.add_sub. done.
    + subst EL'. rewrite last_app. done.
    + subst E' TL'. rewrite /OmoAuth_E_TL_valid. intros. destruct (decide (e0 = length E)) as [->|NEQ].
      * rewrite lookup_app_1_eq in H0. rewrite EQlenTL lookup_app_1_eq in H1. inversion H0. inversion H1. subst eV0 ty. done.
      * rewrite lookup_app_1_ne in H0; [|done]. rewrite lookup_app_1_ne in H1; [|rewrite -EQlenTL;done].
        rewrite /OmoAuth_E_TL_valid in E_TL_VALID. eapply E_TL_VALID; try done.
    + subst E' EL'. rewrite /OmoAuth_E_EL_valid. intros. destruct (decide (e0 = length E)) as [->|NEQ].
      * rewrite lookup_app_1_eq in H0. rewrite EQlenEL lookup_app_1_eq in H1. inversion H0. inversion H1. subst eV0 einfo0. done.
      * rewrite lookup_app_1_ne in H0; [|done]. rewrite lookup_app_1_ne in H1; [|rewrite -EQlenEL;done].
        rewrite /OmoAuth_E_EL_valid in E_EL_VALID. eapply E_EL_VALID; try done.
    + unfold not. intros. subst E'. apply (f_equal length) in H0. rewrite app_length /= in H0. lia.
    + unfold not. intros. subst omo'. apply (f_equal length) in H0. rewrite omo_insert_w_length /= in H0. lia.
    + eapply history_wf_add; try done.
    + apply hb_xo_add; try done.
  - rewrite OmoEview_eq. iDestruct "⊒M" as (?????) "[[%Hγe2 %Nemp'] BIGM]". encode_agree Hγe.
    iExists γtl,γel,γh,γg,γn. iSplit.
    { iPureIntro. split; [done|]. set_solver-. }
    rewrite big_sepS_union; last first.
    { rewrite disjoint_singleton_l. unfold not. intros. specialize (Mvalid _ H0). rewrite lookup_lt_is_Some in Mvalid. lia. }
    iFrame "BIGM". rewrite big_sepS_singleton. iExists einfo. iFrame "EL@e". subst einfo. simpl. rewrite eVOUT. done.
Qed.

(* special version of `OmoAuth_alloc_Gname` that does not require prior Token. This is used by append-only-location *)
Lemma OmoAuth_alloc_Gname_no_Token eV st γx (e := 0%nat) (omo := omo_append_w [] e []) `{Interpretable eventT absStateT} :
  step e eV init st → eV.(eview) = {[e]} →
  ⊢ |==>
  ∃ γe γs,
    OmoHbToken γe γs [eV] omo [st] e _ ∗
    @{eV.(sync)} OmoEview γe {[e]} ∗
    OmoEinfo γe e eV ∗
    OmoSnap γe γs e st ∗
    OmoGname γe γx ∗
    OmoTokenW γe e.
Proof.
  iIntros "%STEP %EVIEW".

  have OMO_GOOD : Linearizability_omo [eV] omo [st].
  { subst omo. replace [eV] with ([] ++ [eV]); [|by simplify_list_eq]. replace [st] with ([] ++ [st]); [|by simplify_list_eq].
    eapply Linearizability_omo_append_w; try done. apply Linearizability_omo_empty. }

  iMod (@mono_list_own_alloc (gname * event_id) _ _ []) as (γgl) "[GL● _]".
  iMod (@mono_list_own_alloc (gname * event_id) _ _ []) as (γgls) "[GLs● #GLs◯]".
  iMod (@mono_list_own_alloc event_id _ _ []) as (γrl) "[RL● #RL◯]".
  iMod (own_alloc (to_agree true)) as (γb) "#Hγb"; [done|].

  set TL := [eV.(type)].
  set elast : (gname * option gname * view * eView * Qp * gname) := (encode (γgl,γb), None, eV.(sync), eV.(eview), 1%Qp, γgls).
  set EL : list (gname * option gname * view * eView * Qp * gname) := [elast].
  set WL : list (event_id * gname * Qp) := [(0, γrl, 1%Qp)].
  iMod (mono_list_own_alloc TL) as (γtl) "[TL● #TL◯]".
  iMod (mono_list_own_alloc EL) as (γel) "[EL● #EL◯]".
  iMod (mono_list_own_alloc WL) as (γwl) "[WL● #WL◯]".
  iMod (mono_list_own_alloc [st]) as (γsl) "[SL● #SL◯]".
  iMod (mono_list_own_alloc [eV]) as (γh) "[HL● #HL◯]".
  iMod (@ghost_map_alloc_empty _ Qp nat) as (γq) "Hγq".
  iMod (ghost_map_insert_persist 1%Qp 0 with "Hγq") as "[Hγq #KEY]"; [done|].
  remember (encode (γwl,γsl,γq)) as γs eqn:Hγs.
  iMod (ghost_var_alloc (γs,[eV],omo,[st])) as (γg) "Hγg".
  iMod (own_alloc (to_agree γx)) as (γn) "#Hγx"; [done|].
  remember (encode (γtl,γel,γh,γg,γn)) as γe eqn:Hγe.

  iDestruct (@mono_list_idx_own_get _ _ _ _ _ 0 with "TL◯") as "#TL@e"; [done|].
  iDestruct (@mono_list_idx_own_get _ _ _ _ _ 0 with "EL◯") as "#EL@e"; [done|].
  iDestruct (@mono_list_idx_own_get _ _ _ _ _ 0 with "WL◯") as "#WL@0"; [done|].
  iDestruct (@mono_list_idx_own_get _ _ _ _ _ 0 with "SL◯") as "#SL@0"; [done|].
  iDestruct (@mono_list_idx_own_get _ _ _ _ _ 0 with "HL◯") as "#HL@e"; [done|].

  iAssert (OmoAuth_EL_seen_event_valid (take (length EL - 1)%nat EL))%I with "[]" as "EL✓".
  { rewrite /OmoAuth_EL_seen_event_valid. subst EL. simplify_list_eq. done. }

  iAssert (OmoAuth_WL_valid γs γel 1 omo WL)%I with "[RL●]" as "WL✓".
  { rewrite /OmoAuth_WL_valid. subst omo WL. simplify_list_eq. iSplitL; [|done].
    iExists e,[],γrl,elast. subst e elast. simpl. iSplitR; [done|]. iFrame "RL●". iSplit; [|done].
    iDestruct (@mono_list_idx_own_get _ _ _ _ _ 0 with "EL◯") as "EL@0"; [done|]. done. }

  iAssert (|==> OmoTokenW γe e)%I with "[GL●]" as ">WCOMMIT".
  { iMod (mono_list_auth_own_update [(γe,e)] with "GL●") as "[GL● #GL◯]".
    { replace [(γe,e)] with ([] ++ [(γe,e)]); [|by simplify_list_eq]. by eapply prefix_app_r. }
    iModIntro. rewrite OmoTokenW_eq.
    iExists γtl,γel,γh,γg,γn,elast,γgl,γb. iFrame "GL● Hγb EL@e". done. }

  iAssert (OmoEinfo γe e eV)%I with "[-]" as "#e✓eV".
  { rewrite OmoEinfo_eq /OmoEinfo_def. iExists γtl,γel,γh,γg,γn,eV.(type),elast. iFrame "TL@e EL@e HL@e".
    iSplit; [iPureIntro; split_and!; try done|]. iSplit.
    + rewrite EVIEW /OmoUB big_sepS_forall. iIntros "%e'' %IN".
      have EQ : e'' = e by set_solver. subst e''. rewrite OmoLe_eq. iExists γtl,γel,γh,γg,γn,elast,elast. iFrame "#". done.
    + rewrite EVIEW OmoEview_eq. iExists γtl,γel,γh,γg,γn. iSplit; [done|].
      iAssert (@{eV.(sync)} (⊒eV.(sync)))%I with "[]" as "#⊒OUT@SYNC"; [done|].
      iDestruct (view_at_objective_iff _ (eV.(sync)) with "EL@e") as "EL@e@SYNC".
      iCombine "⊒OUT@SYNC EL@e@SYNC" as "RES". iApply (view_at_mono with "RES"); [done|]. iIntros "[#⊒OUT #EL@e]".
      iApply big_sepS_forall. iIntros "%e'' %IN".
      have EQ : e'' = e by set_solver. subst e''. iExists elast. subst elast. simpl. iFrame "#". }

  iAssert (OmoAuth_all_elem γe [eV])%I with "[]" as "#ELEMS".
  { rewrite /OmoAuth_all_elem big_sepL_singleton. done. }

  iAssert (OmoAuth_qg_keys γq (<[1%Qp:=0]> ∅))%I with "[]" as "#KEYS".
  { iApply big_sepM_insert; [done|]. iFrame "#". done. }

  iAssert (OmoGname γe γx)%I with "[]" as "#Hγx'".
  { rewrite OmoGname_eq. iExists γtl,γel,γh,γg,γn. iFrame "#". done. }

  iModIntro. iExists γe,γs. iFrame "WCOMMIT Hγx'". iSplitL; last iSplit; last iSplit.
  - rewrite OmoHbToken_eq /OmoHbToken_def.
    iExists γtl,γel,γh,γg,γn,γwl,γsl,γq. iExists TL,EL,WL,_,elast,[]. iFrame. iFrame "EL✓ ELEMS KEYS".
    rewrite big_sepL_nil. iPureIntro. split_and!; try done.
    + rewrite /OmoAuth_E_TL_valid. intros. destruct e0; try done. inversion H0. subst eV0. inversion H1. done.
    + rewrite /OmoAuth_E_EL_valid. intros. destruct e0; try done. inversion H0. inversion H1. subst eV0 einfo. done.
    + rewrite /OmoAuth_qg_mono. intros. apply lookup_lt_Some in H0,H1. subst WL. simpl in *. lia.
    + rewrite /OmoAuth_QM_valid. subst WL. intros. split; intros.
      * rewrite list_lookup_fmap in H0. destruct i; [|done]. inversion H0. subst qg. done.
      * destruct (decide (qg = 1%Qp)) as [->|NEQ].
        -- rewrite lookup_insert in H0. inversion H0. subst i. rewrite list_lookup_fmap /=. done.
        -- rewrite lookup_insert_ne in H0; [|done]. done.
    + constructor; intros; destruct e0; try done; inversion H0; subst eV0.
      * set_solver.
      * rewrite EVIEW. rewrite set_Forall_singleton. done.
    + rewrite /hb_ord. intros. apply lookup_lt_Some in ORD_i1,ORD_i2. simpl in *. lia.
  - rewrite OmoEview_eq /OmoEview_def. iExists γtl,γel,γh,γg,γn. iSplit; [done|].
    rewrite big_sepS_singleton. iExists elast. iFrame "EL@e". done.
  - iFrame "e✓eV".
  - rewrite OmoSnap_eq /OmoSnap_def. iExists γtl,γel,γh,γg,γn,γwl,γsl,γq. iExists 0,elast. iFrame "EL@e KEY SL@0". iPureIntro. split_and!; try done.
Qed.

(* special version of `OmoAuth_alloc` that does not require Token, used by append-only-location *)
Lemma OmoAuth_alloc_no_Token eV st (e := 0%nat) (omo := omo_append_w [] e []) `{Interpretable eventT absStateT} :
  step e eV init st → eV.(eview) = {[e]} →
  ⊢ |==>
  ∃ γe γs,
    OmoHbToken γe γs [eV] omo [st] e _ ∗
    @{eV.(sync)} OmoEview γe {[e]} ∗
    OmoEinfo γe e eV ∗
    OmoSnap γe γs e st ∗
    OmoTokenW γe e.
Proof.
  iIntros "%STEP %EVIEW".

  (* allocate dummy [own] to get dummy gname *)
  iMod (own_alloc (to_agree false)) as (γx) "#Hγx"; [done|].
  iMod (OmoAuth_alloc_Gname_no_Token _ _ γx) as (??) "(H1 & H2 & H3 & H4 & H5 & H6)"; [done|done|].
  iModIntro. iExists γe,γs. iFrame.
Qed.

(* no Token version of `OmoAuth_insert_ro` *)
Lemma OmoAuth_insert_ro_no_Token γe γs E omo stlist Vb M e eV st (en := length E) `{Interpretable eventT absStateT} :
  OmoAuth γe γs 1 E omo stlist _ -∗
  @{Vb} OmoEview γe M -∗
  OmoSnap γe γs e st -∗
  OmoUB γe M e -∗
  ⌜ step en eV st st
  ∧ eV.(sync) = Vb
  ∧ eV.(eview) = {[en]} ∪ M ⌝
  ==∗
  ∃ gen,
    OmoHbToken γe γs (E ++ [eV]) (omo_insert_r omo gen en) stlist en _ ∗
    @{Vb} OmoEview γe ({[en]} ∪ M) ∗
    OmoEq γe e en ∗
    OmoEinfo γe en eV ∗
    OmoTokenR γe en ∗
    (∃ eidx, ⌜ lookup_omo (omo_insert_r omo gen en) eidx = Some en ∧ gen = gen_of eidx ⌝).
Proof.
  iIntros "M● #⊒M #e↪st #MAXgen_e (%STEP & %eVOUT & %eVEVIEW)".
  iDestruct (OmoAuth_OmoSnap'' with "M● e↪st") as %[eidx Heidx].
  iDestruct (OmoAuth_OmoSnap with "M● e↪st") as %Hst; [done|].
  iDestruct (OmoUB_into_gen with "M● MAXgen_e") as %MAXgen; [done|].
  iDestruct (OmoAuth_OmoEview_obj with "M● ⊒M") as %Mvalid.
  iDestruct (OmoEview_nonempty_obj with "⊒M") as %NEmp.
  rewrite OmoAuth_eq. iDestruct "M●" as (??????????)
    "(%&%& [%Hγe %Hγs] & TL● & EL● & WL● & SL● & Hγq & HL● & Hγg & EL✓ & WL✓ & #ELEMS & #KEYS & Pures)".
  iDestruct "Pures" as %(EQlenTL & EQlenEL & E_TL_VALID & E_EL_VALID & MONOqg & QM_VALID & Nomo & NE & HWF & LHB & OMO_GOOD).

  set E' := E ++ [eV].
  set gen := gen_of eidx.
  set omo' := omo_insert_r omo gen en.
  have OMO_GOOD' : Linearizability_omo E' omo' stlist.
  { eapply Linearizability_omo_insert_r; try done. intros. unfold OmoUBgen in *.
    specialize (MAXgen _ H0) as (eidx' & Heidx' & LE).
    eapply lookup_omo_inj in Heidx'; [|done|exact H1]. subst eidx'. done. }
  iMod (ghost_var_update (γs,E',omo',stlist) with "Hγg") as "Hγg".
  iMod (mono_list_auth_own_update E' with "HL●") as "[HL● #HL◯]"; [by eapply prefix_app_r|].
  iDestruct (@mono_list_idx_own_get _ _ _ _ _ en with "HL◯") as "HL@en"; [by rewrite lookup_app_1_eq|].

  rewrite OmoSnap_eq.
  iDestruct "e↪st" as (??????????) "([%Hγe2 %Hγs2] & #EL@e & #KEYi & SL@i)".
  encode_agree Hγe. encode_agree Hγs.

  iMod (@mono_list_own_alloc (gname * event_id) _ _ [(γe,en)]) as (γgl) "[GL● #GL◯]".
  iMod (@mono_list_own_alloc (gname * event_id) _ _ []) as (γgls) "[GLs● #GLs◯]".
  iMod (own_alloc (to_agree false)) as (γb) "#Hγb"; [done|].
  set neinfo : gname * option gname * view * eView * Qp * gname := (encode (γgl,γb), None, eV.(sync), eV.(eview), einfo.1.2, γgls).
  set EL' := EL ++ [neinfo].
  iMod (mono_list_auth_own_update EL' with "EL●") as "[EL● #EL◯]"; [by eapply prefix_app_r|].
  iDestruct (@mono_list_idx_own_get _ _ _ _ _ en with "EL◯") as "#EL@en".
  { subst EL' en. rewrite EQlenEL. by rewrite lookup_app_1_eq. }

  set TL' := TL ++ [eV.(type)].
  iMod (mono_list_auth_own_update TL' with "TL●") as "[TL● #TL◯]"; [by eapply prefix_app_r|].
  iDestruct (@mono_list_idx_own_get _ _ _ _ _ en with "TL◯") as "#TL@en".
  { subst TL' en. rewrite EQlenTL. by rewrite lookup_app_1_eq. }

  iAssert (OmoTokenR γe en)%I with "[GL●]" as "RCOMMIT".
  { rewrite OmoTokenR_eq. iExists γtl,γel,γh,γg,γn,neinfo,γgl,γb. iFrame "GL● EL@en Hγb". done. }

  iAssert (|==> OmoAuth_WL_valid γs γel 1 omo' WL)%I with "[WL✓]" as ">WL✓".
  { rewrite /OmoAuth_WL_valid. subst omo'. rewrite /omo_insert_r -{2}(take_drop gen omo).
    iDestruct (big_sepL2_length with "WL✓") as %EQlen.
    have [[e'' es''] Hgen] : is_Some (omo !! gen).
    { rewrite lookup_lt_is_Some. apply lookup_omo_lt_Some in Heidx. done. }
    have LE1 : (gen < length omo)%nat by apply lookup_lt_Some in Hgen.
    have LE2 : (gen < length WL)%nat by rewrite -EQlen.
    rewrite (drop_S _ (e'',es'')); [|done]. simplify_list_eq. rewrite alter_app_r_alt; last first.
    { rewrite take_length. lia. }
    replace (gen - length (take gen omo)) with 0%nat; last first.
    { rewrite take_length Nat.min_l; lia. }
    simplify_list_eq.
    rewrite -{2}(take_drop gen WL).
    have [winfo' Hgen'] : is_Some (WL !! gen) by rewrite lookup_lt_is_Some; lia.
    rewrite (drop_S _ winfo'); [|done].
    rewrite -{1}(take_drop gen omo) (drop_S _ (e'',es'')); [|done].
    rewrite -{1}(take_drop gen WL) (drop_S _ winfo'); [|done].
    iDestruct (big_sepL2_app_inv with "WL✓") as "[WL✓ WL✓']".
    { left. have H1 : ∀ (a b : nat), (a < b)%nat → (a ≤ b)%nat by lia.
      rewrite !take_length Nat.min_l; [|by apply H1]. (* direct [lia] does not work *)
      rewrite Nat.min_l; [done|by apply H1]. }
    iDestruct (big_sepL2_cons with "WL✓'") as "[WL✓' WL✓'']".
    iApply (big_sepL2_app with "WL✓"). iApply big_sepL2_cons. iFrame "WL✓''".
    iDestruct "WL✓'" as (????) "([%EQ %EQwinfo'] & RL● & #EL@e'' & BIGes)".
    inversion EQ. subst e0 es winfo'. clear EQ.
    iAssert (⌜ einfo0.1.2 = einfo.1.2 ⌝)%I with "[-]" as %EQqg.
    { destruct (decide (e = e'')) as [<-|NEQ].
      - iDestruct (mono_list_idx_agree with "EL@e EL@e''") as %<-. done.
      - destruct eidx; last first.
        { rewrite lookup_omo_wr_event /omo_write_op list_lookup_fmap Hgen in Heidx. inversion Heidx. done. }
        rewrite lookup_omo_ro_event /omo_read_op list_lookup_fmap Hgen /= in Heidx.
        iDestruct (big_sepL_lookup with "BIGes") as (?) "[#EL@e2 %EQ]"; [exact Heidx|].
        iDestruct (mono_list_idx_agree with "EL@e EL@e2") as %<-. done. }
    iMod (mono_list_auth_own_update (es'' ++ [en]) with "RL●") as "[RL● #RL◯]"; [by eapply prefix_app_r|].
    iExists e'',(es''++[en]),γrl,einfo0. iFrame "RL● EL@e''". iModIntro. iSplitR; [done|].
    iApply big_sepL_app. iFrame "BIGes". rewrite big_sepL_singleton. iExists neinfo. iFrame "EL@en". rewrite EQqg. done. }

  iAssert (OmoEq γe e en)%I with "[-]" as "#e=en".
  { rewrite OmoEq_eq. iExists γtl,γel,γh,γg,γn,einfo,neinfo. iSplit; [done|]. iFrame "#". }

  iAssert (OmoEinfo γe en eV)%I with "[-]" as "#en✓eV".
  { rewrite OmoEinfo_eq. iExists γtl,γel,γh,γg,γn,eV.(type),neinfo. iFrame "#". iSplit; [done|repeat iSplit].
    - rewrite eVEVIEW. replace ({[en]} ∪ ({[en]} ∪ M)) with ({[en]} ∪ M); [|set_solver].
      iApply big_sepS_forall. iIntros "%e'' %IN".
      have CASE : e'' = en ∨ e'' ∈ M by set_solver.
      destruct CASE as [->|IN'].
      + rewrite OmoLe_eq. iExists γtl,γel,γh,γg,γn,neinfo,neinfo. iFrame "#". done.
      + iDestruct (big_sepS_elem_of with "MAXgen_e") as "#e''≤e"; [done|]. by iApply OmoLe_Eq_trans.
    - rewrite eVEVIEW eVOUT. replace ({[en]} ∪ ({[en]} ∪ M)) with ({[en]} ∪ M); [|set_solver].
      rewrite -OmoEview_split; [|set_solver-|set_solver]. iFrame "⊒M". rewrite OmoEview_eq.
      iExists γtl,γel,γh,γg,γn. iSplit.
      { iPureIntro. split; [done|]. set_solver-. }
      rewrite big_sepS_singleton. iExists neinfo. iFrame "#". subst neinfo. simpl. rewrite eVOUT. done. }
  iAssert (OmoAuth_all_elem γe E')%I with "[-]" as "#ELEMS'".
  { iApply big_sepL_snoc. iFrame "ELEMS en✓eV". }

  iModIntro. iExists gen. iFrame "RCOMMIT en✓eV e=en". iSplitL; [|repeat iSplit].
  - rewrite OmoHbToken_eq. iExists γtl,γel,γh,γg,γn,γwl,γsl,γq. iExists TL',EL',WL,QM. iExists neinfo,[].
    iFrame. rewrite big_sepL_nil. replace (take (length EL' - 1) EL') with EL; last first.
    { subst EL'. rewrite app_length /= Nat.add_sub take_app. done. }
    iFrame "EL✓ ELEMS' KEYS". iPureIntro. subst EL' TL' E'. rewrite !app_length /=. split_and!; try done.
    + rewrite EQlenTL. done.
    + rewrite EQlenEL. done.
    + lia.
    + rewrite last_app. done.
    + rewrite /OmoAuth_E_TL_valid. intros. destruct (decide (e0 = length E)) as [->|NEQ].
      * rewrite lookup_app_1_eq in H0. inversion H0. subst eV0.
        rewrite EQlenTL lookup_app_1_eq in H1. inversion H1. done.
      * rewrite lookup_app_1_ne in H0; [|done]. rewrite lookup_app_1_ne in H1; [|rewrite -EQlenTL;done].
        unfold OmoAuth_E_TL_valid in E_TL_VALID. eapply E_TL_VALID; try done.
    + rewrite /OmoAuth_E_EL_valid. intros. destruct (decide (e0 = length E)) as [->|NEQ].
      * rewrite lookup_app_1_eq in H0. inversion H0. subst eV0.
        rewrite EQlenEL lookup_app_1_eq in H1. inversion H1. done.
      * rewrite lookup_app_1_ne in H0; [|done]. rewrite lookup_app_1_ne in H1; [|rewrite -EQlenEL;done].
        unfold OmoAuth_E_EL_valid in E_EL_VALID. eapply E_EL_VALID; try done.
    + unfold not. intros. apply (f_equal length) in H0. rewrite app_length /= in H0. lia.
    + unfold not. intros. apply (f_equal length) in H0. rewrite omo_insert_r_length /= in H0. by destruct omo.
    + eapply history_wf_add; try done.
    + replace (length E + 1) with (length (E ++ [eV])); [|rewrite app_length /=;done].
      eapply hb_xo_add; try done.
  - rewrite OmoEview_eq. iDestruct "⊒M" as (?????) "[[%Hγe2 %NEmp'] BIGM]". encode_agree Hγe.
    iExists γtl,γel,γh,γg,γn. iSplit.
    { iPureIntro. split; [done|]. set_solver-. }
    rewrite big_sepS_union; last first.
    { rewrite disjoint_singleton_l. unfold not. intros. specialize (Mvalid _ H0). rewrite lookup_lt_is_Some in Mvalid. lia. }
    iFrame "BIGM". rewrite big_sepS_singleton. iExists neinfo. iFrame "EL@en". subst neinfo. simpl. rewrite eVOUT. done.
  - have [[e'' es''] Hgen] : is_Some (omo !! gen).
    { rewrite lookup_lt_is_Some. apply lookup_omo_lt_Some in Heidx. done. }
    iExists (ro_event gen (length es'')). iPureIntro. split; [|done].
    rewrite lookup_omo_ro_event omo_insert_r_read_op list_lookup_alter /omo_read_op list_lookup_fmap Hgen /= lookup_app_1_eq. done.
Qed.

(* no Token version of `OmoAuth_insert_ro_gen` *)
Lemma OmoAuth_insert_ro_gen_no_Token γe γe' γs E omo stlist Vb M eV (gen : nat) st (e := length E) `{Interpretable eventT absStateT} :
  OmoAuth γe γs 1 E omo stlist _ -∗
  @{Vb} OmoEview γe M -∗
  ⌜ stlist !! gen = Some st
  ∧ step e eV st st
  ∧ OmoUBgen omo M gen
  ∧ eV.(sync) = Vb
  ∧ eV.(eview) = {[e]} ∪ M ⌝
  ==∗
  OmoHbToken γe γs (E ++ [eV]) (omo_insert_r omo gen e) stlist e _ ∗
  @{Vb} OmoEview γe ({[e]} ∪ M) ∗
  OmoSnap γe γs e st ∗
  OmoEinfo γe e eV ∗
  OmoTokenR γe e.
Proof.
  iIntros "M● #⊒M (%Hgenst & %STEP & %MAXgen & %eVOUT & %eVEVIEW)".
  iDestruct (OmoAuth_wf with "M●") as %[OMO_GOOD _].
  apply omo_stlist_length in OMO_GOOD as EQlenST.

  have [[ew es] Hgen] : is_Some (omo !! gen).
  { rewrite lookup_lt_is_Some EQlenST. apply lookup_lt_Some in Hgenst. done. }
  have Hew : lookup_omo omo (wr_event gen) = Some ew by rewrite lookup_omo_wr_event /omo_write_op list_lookup_fmap Hgen.
  eapply lookup_omo_event_valid in Hew as VAL; [|done].
  iDestruct (OmoSnap_get _ _ _ _ _ _ _ (wr_event gen) with "M●") as "#ew↪st"; [done..|].
  iDestruct (OmoUB_from_gen _ _ _ _ _ _ _ _ _ (wr_event gen) with "M●") as "#MAXew"; [done..|].
  iMod (OmoAuth_insert_ro_no_Token with "M● ⊒M ew↪st MAXew []") as (gen')
    "(M● & #⊒M' & #ew=e & #e✓eV & RCOMMIT & (%eidx & %Heidx & %EQgen))"; [done|].

  set omo' := omo_insert_r omo gen' (length E).
  have Hew' : lookup_omo omo' (wr_event gen) = Some ew.
  { rewrite lookup_omo_wr_event omo_insert_r_write_op -lookup_omo_wr_event. done. }

  iAssert (⌜ gen = gen' ⌝)%I with "[-]" as %<-.
  { iDestruct (OmoHbToken_finish with "M●") as "M●".
    iDestruct (OmoEq_Eq with "M● ew=e") as %EQ; [done..|]. simpl in *. rewrite EQ EQgen. done. }
  iDestruct (OmoSnap_get_from_Eq with "ew↪st ew=e") as "e↪st".

  iModIntro. iFrame "∗#%".
Qed.

(* no Token version of `OmoAuth_insert_last` *)
Lemma OmoAuth_insert_last_no_Token γe γs E omo stlist (st st' : absStateT) Vb M eV (e := length E) `{Interpretable eventT absStateT} :
  OmoAuth γe γs 1 E omo stlist _ -∗
  @{Vb} OmoEview γe M -∗
  ⌜ last stlist = Some st ∧ step e eV st st' ∧ eV.(eview) = {[e]} ∪ M ∧ eV.(sync) = Vb ⌝
  ==∗
  OmoHbToken γe γs (E ++ [eV]) (omo_append_w omo e []) (stlist ++ [st']) e _ ∗
  @{Vb} OmoEview γe ({[e]} ∪ M) ∗
  OmoEinfo γe e eV ∗
  OmoSnap γe γs e st' ∗
  OmoTokenW γe e.
Proof.
  iIntros "M● #⊒M (%LASTst & %STEP & %EVIEW & %eVOUT)".
  iDestruct (OmoAuth_OmoEview_obj with "M● ⊒M") as %Mvalid.
  iDestruct (OmoEview_nonempty_obj with "⊒M") as %NEmp.
  rewrite OmoAuth_eq. iDestruct "M●" as (??????????)
    "(%&%& [%Hγe %Hγs] & TL● & EL● & WL● & SL● & Hγq & HL● & Hγg & EL✓ & WL✓ & #ELEMS & #KEYS & Pures)".
  iDestruct "Pures" as %(EQlenTL & EQlenEL & E_TL_VALID & E_EL_VALID & MONOqg & QM_VALID & Nomo & NE & HWF & LHB & OMO_GOOD).

  iAssert (⌜ (length WL = length omo ∧ length stlist = length omo)%nat ⌝)%I with "[-]" as %[EQlenWL EQlenST].
  { rewrite /OmoAuth_WL_valid. iDestruct (big_sepL2_length with "WL✓") as %?.
    apply omo_stlist_length in OMO_GOOD. by rewrite -OMO_GOOD H0. }

  set E' := E ++ [eV].
  set omo' := omo_append_w omo e [].
  set gen := length omo.
  set stlist' := stlist ++ [st'].
  have OMO_GOOD' : Linearizability_omo E' omo' stlist'.
  { eapply Linearizability_omo_append_w; try done. by rewrite last_cons LASTst. }
  iMod (ghost_var_update (γs,E',omo',stlist') with "Hγg") as "Hγg".
  iMod (mono_list_auth_own_update E' with "HL●") as "[HL● #HL◯]"; [by eapply prefix_app_r|].
  iDestruct (@mono_list_idx_own_get _ _ _ _ _ e with "HL◯") as "#HL@e"; [by rewrite lookup_app_1_eq|].

  iMod (@mono_list_own_alloc (gname * event_id) _ _ [(γe,e)]) as (γgl) "[GL● #GL◯]".
  iMod (@mono_list_own_alloc (gname * event_id) _ _ []) as (γgls) "[GLs● #GLs◯]".
  iMod (own_alloc (to_agree true)) as (γb) "#Hγb"; [done|].
  have [winfol Hwinfol] : is_Some (last WL).
  { rewrite last_is_Some. unfold not. intros. subst WL. by destruct omo. }
  set einfo : gname * option gname * view * eView * Qp * gname := (encode (γgl,γb), None, eV.(sync), eV.(eview), (winfol.2 + 1)%Qp, γgls).
  set EL' := EL ++ [einfo].
  iMod (mono_list_auth_own_update EL' with "EL●") as "[EL● #EL◯]"; [by eapply prefix_app_r|].
  iDestruct (@mono_list_idx_own_get _ _ _ _ _ e with "EL◯") as "#EL@e".
  { subst EL' e. rewrite EQlenEL. by rewrite lookup_app_1_eq. }

  set TL' := TL ++ [eV.(type)].
  iMod (mono_list_auth_own_update TL' with "TL●") as "[TL● #TL◯]"; [by eapply prefix_app_r|].
  iDestruct (@mono_list_idx_own_get _ _ _ _ _ e with "TL◯") as "#TL@e".
  { subst TL' e. rewrite EQlenTL. by rewrite lookup_app_1_eq. }

  iMod (mono_list_auth_own_update stlist' with "SL●") as "[SL● #SL◯]"; [by eapply prefix_app_r|].
  iDestruct (@mono_list_idx_own_get _ _ _ _ _ gen with "SL◯") as "#SL@gen".
  { subst stlist' gen. rewrite -EQlenST lookup_app_1_eq. done. }

  iMod (@mono_list_own_alloc event_id _ _ []) as (γrl) "[RL● #RL◯]".
  set WL' := WL ++ [(e, γrl, einfo.1.2)].
  iMod (mono_list_auth_own_update WL' with "WL●") as "[WL● #WL◯]"; [by eapply prefix_app_r|].
  iDestruct (@mono_list_idx_own_get _ _ _ _ _ gen with "WL◯") as "#WL@gen".
  { subst WL' gen. rewrite -EQlenWL lookup_app_1_eq. done. }
  have MONOqg' : OmoAuth_qg_mono WL'.
  { unfold OmoAuth_qg_mono in *. intros. destruct (decide (n2 = length WL)) as [->|NEQ].
    - rewrite lookup_app_1_eq in H1. inversion H1. subst winfo2. clear H1. simpl.
      have LT : (winfol.2 < winfol.2 + 1)%Qp by apply Qp.lt_add_l.
      eapply Qp.le_lt_trans; [|exact LT]. clear LT.
      destruct (decide (n1 = length WL - 1)) as [->|NEQ'].
      + rewrite last_lookup in Hwinfol. replace (Init.Nat.pred (length WL)) with (length WL - 1) in Hwinfol by lia.
        rewrite lookup_app_l in H0; [|lia]. rewrite Hwinfol in H0. inversion H0. subst winfo1. clear H0. done.
      + rewrite last_lookup in Hwinfol. replace (Init.Nat.pred (length WL)) with (length WL - 1) in Hwinfol by lia.
        rewrite lookup_app_l in H0; [|lia].
        have CONDLT : n1 < length WL - 1 by lia.
        specialize (MONOqg _ _ _ _ H0 Hwinfol CONDLT). by apply Qp.lt_le_incl.
    - have LT : n2 < length WL.
      { apply lookup_lt_Some in H1. rewrite app_length /= in H1. lia. }
      rewrite lookup_app_l in H0; [|lia]. rewrite lookup_app_l in H1; [|lia].
      eapply MONOqg; done. }

  have NInclQM : QM !! einfo.1.2 = None.
  { destruct (QM !! einfo.1.2) as [i|] eqn:Heq; [|done].
    unfold OmoAuth_QM_valid in *. specialize (QM_VALID einfo.1.2 i). rewrite -QM_VALID in Heq.
    apply list_lookup_fmap_inv in Heq as [winfo [EQ Hwinfo]].
    rewrite last_lookup EQlenWL in Hwinfol. replace (Init.Nat.pred (length omo)) with (length omo - 1) in Hwinfol by lia.
    destruct (decide (i = (length omo - 1))) as [->|NEQ].
    - rewrite Hwinfo in Hwinfol. inversion Hwinfol. subst winfo. subst einfo. simpl in EQ. by apply Qp.add_id_free in EQ.
    - have LT : i < length omo - 1.
      { apply lookup_lt_Some in Hwinfo. rewrite EQlenWL in Hwinfo. lia. }
      unfold OmoAuth_qg_mono in *. specialize (MONOqg _ _ _ _ Hwinfo Hwinfol LT). rewrite -EQ in MONOqg. subst einfo.
      simpl in MONOqg. apply Qp.lt_nge in MONOqg. exfalso. apply MONOqg. apply Qp.le_add_l. }
  iMod (ghost_map_insert_persist einfo.1.2 gen with "Hγq") as "[Hγq #KEY@gen]"; [done|].
  set QM' := <[einfo.1.2:=gen]> QM.
  iAssert (OmoAuth_qg_keys γq QM')%I with "[-]" as "#KEYS'".
  { iApply big_sepM_insert; [done|]. iFrame "#". }

  iAssert (OmoTokenW γe e)%I with "[GL●]" as "WCOMMIT".
  { rewrite OmoTokenW_eq. iExists γtl,γel,γh,γg,γn,einfo,γgl,γb. iFrame "GL● EL@e Hγb". done. }

  iAssert (OmoAuth_WL_valid γs γel 1 omo' WL')%I with "[WL✓ RL●]" as "WL✓".
  { rewrite /OmoAuth_WL_valid. subst omo' WL'. rewrite /omo_append_w.
    iApply (big_sepL2_app with "WL✓"). rewrite big_sepL2_singleton. iExists e,[],γrl,einfo. iFrame "RL● EL@e".
    rewrite big_sepL_nil. iPureIntro. split_and!; try done. }

  iAssert (OmoEinfo γe e eV)%I with "[-]" as "#e✓eV".
  { rewrite OmoEinfo_eq. iExists γtl,γel,γh,γg,γn,eV.(type),einfo. iFrame "#". iSplit; [done|repeat iSplit].
    - rewrite EVIEW. replace ({[e]} ∪ ({[e]} ∪ M)) with ({[e]} ∪ M); [|set_solver].
      iApply big_sepS_forall. iIntros "%e'' %IN".
      have CASE : e'' = e ∨ e'' ∈ M by set_solver.
      destruct CASE as [->|IN'].
      + rewrite OmoLe_eq. iExists γtl,γel,γh,γg,γn,einfo,einfo. iFrame "#". done.
      + rewrite OmoEview_eq OmoLe_eq.
        iDestruct "⊒M" as (?????) "[[%Hγe'' %NEmp'] BIG]". encode_agree Hγe.
        rewrite big_sepS_elem_of; [|exact IN']. iDestruct "BIG" as (einfo'') "[EL@e'' _]".
        rewrite view_at_objective_iff.
        iExists γtl,γel,γh,γg,γn,einfo'',einfo. iFrame "#". iSplit; [done|].

        iAssert (∃ i winfo, ⌜ WL' !! i = Some winfo ∧ winfo.2 = einfo''.1.2 ⌝)%I with "[-]" as %(i & winfo & Hwinfo & EQ).
        { iDestruct (mono_list_auth_idx_lookup with "EL● EL@e''") as %LOOKUP.
          apply lookup_lt_Some in LOOKUP as LT. replace (length EL') with (length E') in LT; last first.
          { subst E' EL'. rewrite !app_length /=. lia. }
          rewrite -lookup_lt_is_Some in LT. eapply lookup_omo_surjective in LT as [eidx Heidx]; [|done].
          have [[e''' es'''] Hgen] : is_Some (omo' !! (gen_of eidx)).
          { rewrite lookup_lt_is_Some. apply lookup_omo_lt_Some in Heidx. done. }
          have [winfo Hwinfo] : is_Some (WL' !! (gen_of eidx)).
          { rewrite lookup_lt_is_Some. apply lookup_lt_Some in Hgen. subst WL' omo'. rewrite app_length /=. rewrite omo_append_w_length in Hgen. lia. }
          iDestruct (big_sepL2_lookup with "WL✓") as (????) "([%EQ1 %EQ2] & RL● & #EL@e''' & BIG)"; [done|done|].
          inversion EQ1. subst e0 es winfo. clear EQ1.
          iExists (gen_of eidx),(e''',γrl0,einfo0.1.2). iSplit; [done|].
          destruct eidx.
          - rewrite lookup_omo_ro_event /omo_read_op list_lookup_fmap Hgen /= in Heidx.
            iDestruct (big_sepL_lookup with "BIG") as (?) "[#EL@e''a %EQ]"; [done|].
            iDestruct (mono_list_idx_agree with "EL@e'' EL@e''a") as %<-. done.
          - rewrite lookup_omo_wr_event /omo_write_op list_lookup_fmap Hgen /= in Heidx. inversion Heidx. subst e'''.
            iDestruct (mono_list_idx_agree with "EL@e'' EL@e'''") as %<-. done. }
        have Hwinfo' : WL' !! (length WL) = Some (e, γrl, einfo.1.2) by rewrite lookup_app_1_eq.
        destruct (decide (i = length WL)) as [->|NEQ].
        * rewrite Hwinfo in Hwinfo'. inversion Hwinfo'. subst winfo. simpl in EQ. rewrite -EQ. subst einfo. simpl. done.
        * have CONDLT : i < length WL.
          { apply lookup_lt_Some in Hwinfo. subst WL'. rewrite app_length /= in Hwinfo. lia. }
          specialize (MONOqg' _ _ _ _ Hwinfo Hwinfo' CONDLT). rewrite EQ /= in MONOqg'. subst einfo. simpl. iPureIntro. by apply Qp.lt_le_incl.
    - rewrite EVIEW eVOUT. replace ({[e]} ∪ ({[e]} ∪ M)) with ({[e]} ∪ M); [|set_solver].
      rewrite -OmoEview_split; [|set_solver-|set_solver]. iFrame "⊒M". rewrite OmoEview_eq.
      iExists γtl,γel,γh,γg,γn. iSplit.
      { iPureIntro. split; [done|]. set_solver-. }
      rewrite big_sepS_singleton. iExists einfo. iFrame "#". subst einfo. simpl. rewrite eVOUT. done. }
  iAssert (OmoAuth_all_elem γe E')%I with "[-]" as "#ELEMS'".
  { iApply big_sepL_snoc. iFrame "ELEMS e✓eV". }

  iModIntro. iFrame "WCOMMIT e✓eV". iSplitL; [|repeat iSplit].
  - rewrite OmoHbToken_eq. iExists γtl,γel,γh,γg,γn,γwl,γsl,γq. iExists TL',EL',WL',QM',einfo,[].
    iFrame. replace (take (length EL' - 1) EL') with EL; last first.
    { subst EL'. rewrite app_length /= Nat.add_sub take_app. done. }
    iFrame "EL✓ ELEMS' KEYS'". rewrite big_sepL_nil. iPureIntro. split_and!; try done.
    + subst E' TL'. rewrite !app_length EQlenTL /=. done.
    + subst E' EL'. rewrite !app_length /=. lia.
    + subst EL'. rewrite app_length /= Nat.add_sub. done.
    + subst EL'. rewrite last_app. done.
    + subst E' TL'. rewrite /OmoAuth_E_TL_valid. intros. destruct (decide (e0 = length E)) as [->|NEQ].
      * rewrite lookup_app_1_eq in H0. rewrite EQlenTL lookup_app_1_eq in H1. inversion H0. inversion H1. subst eV0 ty. done.
      * rewrite lookup_app_1_ne in H0; [|done]. rewrite lookup_app_1_ne in H1; [|rewrite -EQlenTL;done].
        rewrite /OmoAuth_E_TL_valid in E_TL_VALID. eapply E_TL_VALID; try done.
    + subst E' EL'. rewrite /OmoAuth_E_EL_valid. intros. destruct (decide (e0 = length E)) as [->|NEQ].
      * rewrite lookup_app_1_eq in H0. rewrite EQlenEL lookup_app_1_eq in H1. inversion H0. inversion H1. subst eV0 einfo0. done.
      * rewrite lookup_app_1_ne in H0; [|done]. rewrite lookup_app_1_ne in H1; [|rewrite -EQlenEL;done].
        rewrite /OmoAuth_E_EL_valid in E_EL_VALID. eapply E_EL_VALID; try done.
    + unfold OmoAuth_QM_valid in *. intros. destruct (decide (i = length WL)) as [->|NEQ].
      * rewrite list_lookup_fmap lookup_app_1_eq /=. split; intros.
        -- inversion H0. subst qg QM' einfo. simpl. rewrite lookup_insert. subst gen. rewrite EQlenWL. done.
        -- subst QM'. destruct (decide (qg = einfo.1.2)) as [->|NEQ]; [done|].
           rewrite lookup_insert_ne in H0; [|done]. specialize (QM_VALID qg (length WL)). rewrite -QM_VALID in H0.
           apply lookup_lt_Some in H0. rewrite fmap_length in H0. lia.
      * rewrite list_lookup_fmap lookup_app_1_ne /=; [|done]. split; intros.
        -- destruct (decide (qg = einfo.1.2)) as [->|NEQ'].
           ++ specialize (QM_VALID einfo.1.2 i). rewrite list_lookup_fmap in QM_VALID. rewrite QM_VALID in H0. rewrite H0 in NInclQM. done.
           ++ rewrite lookup_insert_ne; [|done]. specialize (QM_VALID qg i). rewrite list_lookup_fmap in QM_VALID. rewrite QM_VALID in H0. done.
        -- destruct (decide (qg = einfo.1.2)) as [->|NEQ'].
           ++ rewrite lookup_insert in H0. inversion H0. subst i.
              specialize (QM_VALID einfo.1.2 gen). rewrite list_lookup_fmap in QM_VALID. rewrite QM_VALID. done.
           ++ rewrite lookup_insert_ne in H0; [|done]. specialize (QM_VALID qg i). rewrite -QM_VALID list_lookup_fmap in H0. done.
    + unfold not. intros. subst E'. apply (f_equal length) in H0. rewrite app_length /= in H0. lia.
    + unfold not. intros. subst omo'. apply (f_equal length) in H0. rewrite omo_append_w_length /= in H0. lia.
    + subst E'. eapply history_wf_add; try done.
    + subst E'. apply hb_xo_add; try done.
  - rewrite OmoEview_eq. iDestruct "⊒M" as (?????) "[[%Hγe2 %NEmp'] BIGM]". encode_agree Hγe.
    iExists γtl,γel,γh,γg,γn. iSplit.
    { iPureIntro. split; [done|]. set_solver-. }
    rewrite big_sepS_union; last first.
    { rewrite disjoint_singleton_l. unfold not. intros. specialize (Mvalid _ H0). rewrite lookup_lt_is_Some in Mvalid. lia. }
    iFrame "BIGM". rewrite big_sepS_singleton. iExists einfo. iFrame "EL@e". subst einfo. simpl. rewrite eVOUT. done.
  - rewrite OmoSnap_eq. iExists γtl,γel,γh,γg,γn,γwl,γsl,γq. iExists gen,einfo. iFrame "#". iPureIntro. split_and!; try done.
Qed.

(* no Token version of `OmoAuth_insert` *)
Lemma OmoAuth_insert_no_Token γe γs E omo (stlist stnew : list absStateT) (st : absStateT) Vb M gen eV
  (e := length E) `{Interpretable eventT absStateT} :
  OmoAuth γe γs 1 E omo stlist _ -∗
  @{Vb} OmoEview γe M -∗
  ⌜ eV.(sync) = Vb
  ∧ eV.(eview) = {[e]} ∪ M
  ∧ stlist !! gen = Some st
  ∧ OmoUBgen omo M gen
  ∧ interp_omo (E ++ [eV]) ((e, []) :: (drop (gen + 1)%nat omo)) st stnew ⌝
  ==∗
  ∃ γs',
    OmoHbToken γe γs' (E ++ [eV]) (omo_insert_w omo (gen + 1) e []) (take (gen + 1)%nat stlist ++ stnew) e _ ∗
    @{Vb} OmoEview γe ({[e]} ∪ M) ∗
    OmoEinfo γe e eV ∗
    OmoTokenW γe e.
Proof.
  iIntros "M● #⊒M (%eVOUT & %EVIEW & %STgen & %MAXgen & %GEN_GOOD)".
  destruct (decide (gen = length omo - 1)) as [->|NEgen].
  { iDestruct (OmoAuth_wf with "M●") as %[OMO_GOOD _]. apply omo_stlist_length in OMO_GOOD.
    iDestruct (OmoAuth_omo_nonempty with "M●") as %Nomo.
    have [st' [COND1 [COND2 COND3]]] : ∃ st', last stlist = Some st ∧ step (length E) eV st st' ∧ stnew = [st'].
    { rewrite Nat.sub_add in GEN_GOOD; [|by destruct omo; try done; simpl; lia].
      rewrite drop_ge in GEN_GOOD; [|done]. apply interp_omo_length in GEN_GOOD as EQlenst. simpl in EQlenst.
      inversion GEN_GOOD.
      have EQ : omo0 ++ [(e0, es)] = [] ++ [(e, [])] by simplify_list_eq.
      apply app_inj_2 in EQ as [-> EQ]; [|done]. inversion EQ. subst st1 stnew e0 es E0. clear H0 EQ.
      destruct H2 as (H1 & H2 & H3 & H4 & H5).
      subst e. rewrite lookup_app_1_eq in H1. inversion H1. subst eV0. clear H1.
      rewrite app_length /= in EQlenst. destruct stlist0; [|by simpl in *; lia].
      inversion H3. subst st2. exists st3. split_and!.
      - rewrite last_lookup. replace (Init.Nat.pred (length stlist)) with (length stlist - 1) by lia.
        rewrite -OMO_GOOD. done.
      - done.
      - by simplify_list_eq. }
    iMod (OmoAuth_insert_last_no_Token with "M● ⊒M []") as "(M● & #⊒M' & #e✓eV & #e↪st' & WCOMMIT)"; [by iPureIntro; split_and!|].
    iModIntro. iExists γs. rewrite Nat.sub_add; [|by destruct omo; try done; simpl; lia].
    rewrite omo_insert_w_append_w; [|done]. rewrite take_ge; [|by rewrite OMO_GOOD]. subst stnew. iFrame. iFrame "⊒M' e✓eV". }

  iDestruct (OmoAuth_OmoEview_obj with "M● ⊒M") as %Mvalid.
  iDestruct (OmoEview_nonempty_obj with "⊒M") as %NEmp.
  rewrite OmoAuth_eq. iDestruct "M●" as (??????????)
    "(%&%& [%Hγe %Hγs] & TL● & EL● & WL● & SL● & Hγq & HL● & Hγg & EL✓ & WL✓ & #ELEMS & #KEYS & Pures)".
  iDestruct "Pures" as %(EQlenTL & EQlenEL & E_TL_VALID & E_EL_VALID & MONOqg & QM_VALID & Nomo & NE & HWF & LHB & OMO_GOOD).

  iAssert (⌜ (length WL = length omo ∧ length stlist = length omo)%nat ⌝)%I with "[-]" as %[EQlenWL EQlenST].
  { rewrite /OmoAuth_WL_valid. iDestruct (big_sepL2_length with "WL✓") as %?.
    apply omo_stlist_length in OMO_GOOD. by rewrite -OMO_GOOD H0. }

  set E' := E ++ [eV].
  set omo' := omo_insert_w omo (gen + 1) e [].
  set stlist' := take (gen + 1) stlist ++ stnew.
  have OMO_GOOD' : Linearizability_omo E' omo' stlist'.
  { eapply Linearizability_omo_insert_w; try done.
    - rewrite last_cons. replace (gen + 1) with (S gen) by lia. rewrite (take_S_r _ _ st); [|done].
      rewrite last_app. done.
    - intros. rewrite /OmoUBgen in MAXgen. specialize (MAXgen _ H0) as (eidx' & Heidx' & LE).
      eapply lookup_omo_inj in Heidx'; [|done|exact H1]. subst eidx'. lia. }
  iMod (mono_list_auth_own_update E' with "HL●") as "[HL● #HL◯]"; [by eapply prefix_app_r|].
  iDestruct (@mono_list_idx_own_get _ _ _ _ _ e with "HL◯") as "#HL@e"; [by rewrite lookup_app_1_eq|].

  iMod (@mono_list_own_alloc (gname * event_id) _ _ [(γe,e)]) as (γgl) "[GL● #GL◯]".
  iMod (@mono_list_own_alloc (gname * event_id) _ _ []) as (γgls) "[GLs● #GLs◯]".
  iMod (own_alloc (to_agree true)) as (γb) "#Hγb"; [done|].
  have NZomo : length omo ≠ 0 by destruct omo.
  have [winfol Hwinfol] : is_Some (WL !! gen).
  { rewrite lookup_lt_is_Some EQlenWL -EQlenST. apply lookup_lt_Some in STgen. done. }
  have [winfor Hwinfor] : is_Some (WL !! (S gen)).
  { rewrite lookup_lt_is_Some EQlenWL. apply lookup_lt_Some in Hwinfol. rewrite EQlenWL in Hwinfol. lia. }

  set einfo : gname * option gname * view * eView * Qp * gname := (encode (γgl,γb), None, eV.(sync), eV.(eview), ((winfol.2 + winfor.2) / 2)%Qp, γgls).
  set EL' := EL ++ [einfo].
  iMod (mono_list_auth_own_update EL' with "EL●") as "[EL● #EL◯]"; [by eapply prefix_app_r|].
  iDestruct (@mono_list_idx_own_get _ _ _ _ _ e with "EL◯") as "#EL@e".
  { subst EL' e. rewrite EQlenEL. by rewrite lookup_app_1_eq. }

  set TL' := TL ++ [eV.(type)].
  iMod (mono_list_auth_own_update TL' with "TL●") as "[TL● #TL◯]"; [by eapply prefix_app_r|].
  iDestruct (@mono_list_idx_own_get _ _ _ _ _ e with "TL◯") as "#TL@e".
  { subst TL' e. rewrite EQlenTL. by rewrite lookup_app_1_eq. }

  iMod (@mono_list_own_alloc event_id _ _ []) as (γrl) "[RL● #RL◯]".
  set WL' := take (gen + 1) WL ++ [(e, γrl, einfo.1.2)] ++ drop (gen + 1) WL.
  iMod (mono_list_own_alloc WL') as (γwl') "[WL'● #WL'◯]".
  iMod (mono_list_own_alloc stlist') as (γsl') "[SL'● #SL'◯]".

  have MONOqg' : OmoAuth_qg_mono WL'.
  { unfold OmoAuth_qg_mono in *. intros. subst WL'.
    destruct (decide (n1 = (gen + 1))) as [->|NE1]; destruct (decide (n2 = (gen + 1))) as [->|NE2].
    - lia.
    - have GENeq : length (take (gen + 1) WL) = gen + 1.
      { rewrite take_length Nat.min_l; [done|].
        apply lookup_lt_Some in Hwinfol. lia. }
      rewrite lookup_app_r in H0; [|rewrite GENeq;lia].
      rewrite GENeq in H0. replace (gen + 1 - (gen + 1)) with 0 in H0 by lia.
      simpl in H0. inversion H0. subst winfo1. simpl. clear H0.
      rewrite lookup_app_r in H1; [|rewrite GENeq;lia].
      rewrite GENeq lookup_app_r in H1; [|simpl;lia]. simpl in H1.
      have LE : (winfor.2 ≤ winfo2.2)%Qp.
      { destruct (decide (n2 = gen + 2)) as [->|NEQ].
        - replace (gen + 2 - (gen + 1) - 1) with 0 in H1 by lia.
          rewrite lookup_drop Nat.add_0_r in H1.
          replace (gen + 1) with (S gen) in H1 by lia.
          rewrite Hwinfor in H1. inversion H1. subst winfo2. done.
        - rewrite lookup_drop in H1.
          have CONDLT : S gen < gen + 1 + (n2 - (gen + 1) - 1) by lia.
          specialize (MONOqg _ _ _ _ Hwinfor H1 CONDLT).
          apply Qp.lt_le_incl. done. }
      have LELR : (winfol.2 < winfor.2)%Qp.
      { have CONDLT : gen < S gen by lia. specialize (MONOqg _ _ _ _ Hwinfol Hwinfor CONDLT). done. }
      eapply Qp.lt_le_trans; try done.
      have EQ : (winfor.2 = (winfor.2 + winfor.2) / 2)%Qp.
      { rewrite Qp.add_diag Qp.mul_comm. unfold Qp.div. rewrite -Qp.mul_assoc.
        replace (2 * /2)%Qp with (2 / 2)%Qp; [|by unfold Qp.div].
        rewrite Qp.div_diag Qp.mul_1_r. done. }
      rewrite {2}EQ -Qp.div_lt_mono_r -Qp.add_lt_mono_r. done.
    - have GENeq : length (take (gen + 1) WL) = gen + 1.
      { rewrite take_length Nat.min_l; [done|].
        apply lookup_lt_Some in Hwinfol. lia. }
      rewrite lookup_app_r in H1; [|by rewrite GENeq;lia].
      replace (gen + 1 - length (take (gen + 1) WL)) with 0 in H1 by lia. simpl in H1. inversion H1. subst winfo2. clear H1. simpl.
      rewrite lookup_app_l in H0; [|lia].
      rewrite lookup_take in H0; [|lia].
      have LE : (winfo1.2 ≤ winfol.2)%Qp.
      { destruct (decide (n1 = gen)) as [->|NEQ].
        - rewrite Hwinfol in H0. inversion H0. done.
        - have CONDLT : n1 < gen by lia.
          specialize (MONOqg _ _ _ _ H0 Hwinfol CONDLT). apply Qp.lt_le_incl. done. }
      eapply Qp.le_lt_trans; try done.
      have LELR : (winfol.2 < winfor.2)%Qp.
      { have CONDLT : gen < S gen by lia. specialize (MONOqg _ _ _ _ Hwinfol Hwinfor CONDLT). done. }
      have EQ : (winfol.2 = (winfol.2 + winfol.2) / 2)%Qp.
      { rewrite Qp.add_diag Qp.mul_comm. unfold Qp.div. rewrite -Qp.mul_assoc.
        replace (2 * /2)%Qp with (2 / 2)%Qp; [|by unfold Qp.div].
        rewrite Qp.div_diag Qp.mul_1_r. done. }
      rewrite {1}EQ -Qp.div_lt_mono_r -Qp.add_lt_mono_l. done.
    - have [n1' [n2' [LOOKUP1 [LOOKUP2 LT]]]] : ∃ n1' n2', WL !! n1' = Some winfo1 ∧ WL !! n2' = Some winfo2 ∧ n1' < n2'.
      { have GENeq : length (take (gen + 1) WL) = gen + 1.
        { rewrite take_length Nat.min_l; [done|].
          apply lookup_lt_Some in Hwinfol. lia. }
        have CASE : n2 < gen + 1 ∨ (n1 < gen + 1 ∧ gen + 1 < n2) ∨ (gen + 1 < n1) by lia.
        destruct CASE as [COMP2|[[COMP1 COMP2]|COMP1]].
        - rewrite lookup_app_l in H0; [|by rewrite GENeq;lia].
          rewrite lookup_take in H0; [|lia].
          rewrite lookup_app_l in H1; [|by rewrite GENeq;lia].
          rewrite lookup_take in H1; [|lia].
          exists n1,n2. split_and!; try done.
        - rewrite lookup_app_l in H0; [|by rewrite GENeq;lia].
          rewrite lookup_take in H0; [|lia].
          rewrite lookup_app_r in H1; [|by rewrite GENeq;lia]. rewrite GENeq in H1.
          rewrite lookup_app_r in H1; [|simpl;lia].
          rewrite lookup_drop /= in H1. replace (gen + 1 + (n2 - (gen + 1) - 1)) with (n2 - 1) in H1 by lia.
          exists n1,(n2 - 1). split_and!; try done. lia.
        - rewrite lookup_app_r in H0; [|by rewrite GENeq;lia]. rewrite GENeq in H0.
          rewrite lookup_app_r in H0; [|simpl;lia].
          rewrite lookup_drop /= in H0. replace (gen + 1 + (n1 - (gen + 1) - 1)) with (n1 - 1) in H0 by lia.
          rewrite lookup_app_r in H1; [|by rewrite GENeq;lia]. rewrite GENeq in H1.
          rewrite lookup_app_r in H1; [|simpl;lia].
          rewrite lookup_drop /= in H1. replace (gen + 1 + (n2 - (gen + 1) - 1)) with (n2 - 1) in H1 by lia.
          exists (n1 - 1),(n2 - 1). split_and!; try done. lia. }
      specialize (MONOqg _ _ _ _ LOOKUP1 LOOKUP2 LT). done. }

  iMod (@ghost_map_alloc_empty _ Qp nat) as (γq') "Hγq'".
  iAssert (|==> ∃ QM', ⎡ghost_map_auth γq' 1 QM'⎤ ∗ OmoAuth_qg_keys γq' QM' ∗ ⌜ OmoAuth_QM_valid WL' QM' ⌝)%I
    with "[Hγq']" as ">(%QM' & Hγq' & #KEYS' & %QM_VALID')".
  { iClear "⊒M ELEMS KEYS HL◯ HL@e GL◯ GLs◯ Hγb EL◯ EL@e TL◯ TL@e RL◯ WL'◯ SL'◯".
    have [i Hi] : ∃ i, WL' = take i WL' by exists (length WL'); rewrite take_ge.
    rewrite Hi. clear Hi. iInduction i as [] "IH".
    - iModIntro. iExists ∅. iFrame. iSplit.
      + by rewrite /OmoAuth_qg_keys big_sepM_empty.
      + iPureIntro. rewrite take_0. unfold OmoAuth_QM_valid. intros. done.
    - iMod ("IH" with "Hγq'") as (QM') "(Hγq' & #KEYS & %QM_VALID')".
      destruct (le_lt_dec (length WL') i) as [LE|LT].
      { repeat (rewrite take_ge; [|lia]). rewrite take_ge in QM_VALID'; [|lia].
        iModIntro. iExists QM'. iFrame "∗#%". }
      rewrite -lookup_lt_is_Some in LT. destruct LT as [winfo Hwinfo].
      have NInclQM : QM' !! winfo.2 = None.
      { destruct (QM' !! winfo.2) as [i'|] eqn:Heq; [|done].
        unfold OmoAuth_QM_valid in *. specialize (QM_VALID' winfo.2 i'). rewrite -QM_VALID' in Heq.
        apply list_lookup_fmap_inv in Heq as [winfo' [EQ' Hwinfo']].
        rewrite lookup_take_Some in Hwinfo'. destruct Hwinfo' as [Hwinfo' LT].
        specialize (MONOqg' _ _ _ _ Hwinfo' Hwinfo LT). rewrite EQ' in MONOqg'. by apply Qp.lt_strict in MONOqg'. }
      iMod (ghost_map_insert_persist winfo.2 i with "Hγq'") as "[Hγq' #KEYi]"; [done|].
      iModIntro. iExists (<[winfo.2:=i]> QM'). iFrame "Hγq'". iSplitL.
      + iApply big_sepM_insert; [done|]. iFrame "#".
      + iPureIntro. unfold OmoAuth_QM_valid. intros. split; intros.
        * destruct (decide (i0 = i)) as [->|NEQ].
          -- rewrite list_lookup_fmap lookup_take in H0; [|lia]. rewrite Hwinfo in H0. inversion H0. subst qg.
             rewrite lookup_insert. done.
          -- apply list_lookup_fmap_inv in H0 as [winfo' [EQ Hwinfo']]. subst qg.
             rewrite lookup_take_Some in Hwinfo'. destruct Hwinfo' as [Hwinfo' LT].
             have CONDLT : i0 < i by lia.
             specialize (MONOqg' _ _ _ _ Hwinfo' Hwinfo CONDLT).
             unfold OmoAuth_QM_valid in *.
             specialize (QM_VALID' winfo'.2 i0).
             rewrite lookup_insert_ne; last first.
             { unfold not. intros. rewrite H0 in MONOqg'. by apply Qp.lt_strict in MONOqg'. }
             rewrite -QM_VALID'. rewrite list_lookup_fmap lookup_take; [|lia]. rewrite Hwinfo'. done.
        * destruct (decide (qg = winfo.2)) as [->|NEQ].
          -- rewrite lookup_insert in H0. inversion H0. subst i0.
             rewrite list_lookup_fmap lookup_take; [|lia]. rewrite Hwinfo. done.
          -- rewrite lookup_insert_ne in H0; [|done]. specialize (QM_VALID' qg i0). rewrite -QM_VALID' in H0.
             apply list_lookup_fmap_inv in H0 as [winfo' [EQ Hwinfo']]. subst qg.
             rewrite lookup_take_Some in Hwinfo'. destruct Hwinfo' as [Hwinfo' LT].
             rewrite list_lookup_fmap lookup_take; [|lia]. rewrite Hwinfo'. done. }
  remember (encode (γwl',γsl',γq')) as γs' eqn:Hγs'.
  iMod (ghost_var_update (γs',E',omo',stlist') with "Hγg") as "Hγg".

  iAssert (OmoTokenW γe e)%I with "[GL●]" as "WCOMMIT".
  { rewrite OmoTokenW_eq. iExists γtl,γel,γh,γg,γn,einfo,γgl,γb. iFrame "GL● EL@e Hγb". done. }

  iAssert (OmoAuth_WL_valid γs γel 1 omo' WL')%I with "[WL✓ RL●]" as "WL✓".
  { rewrite /OmoAuth_WL_valid. subst omo' WL'. rewrite /omo_insert_w.
    rewrite -{1}(take_drop (gen + 1) omo). rewrite -{3}(take_drop (gen + 1) WL).
    iDestruct (big_sepL2_app_inv with "WL✓") as "[WL✓ WL✓']".
    { left. have H1 : ∀ (a b : nat), (a < b)%nat → (a ≤ b)%nat by lia.
      rewrite !take_length Nat.min_l; last first.
      { apply lookup_lt_Some in Hwinfor. rewrite EQlenWL in Hwinfor. replace (gen + 1) with (S gen) by lia.
        apply H1. done. }
      rewrite Nat.min_l; [done|]. apply H1. apply lookup_lt_Some in Hwinfor. replace (gen + 1) with (S gen) by lia. done. }
    iApply (big_sepL2_app with "WL✓").
    have EQ : (e, []) :: drop (gen + 1) omo = [(e, [])] ++ drop (gen + 1) omo by simplify_list_eq.
    rewrite EQ. clear EQ. iApply (big_sepL2_app with "[RL●]"); [|done].
    rewrite big_sepL2_singleton. iExists e,[],γrl,einfo. iFrame "RL● EL@e". rewrite big_sepL_nil. iPureIntro. split_and!; try done. }

  iAssert (OmoEinfo γe e eV)%I with "[-]" as "#e✓eV".
  { rewrite OmoEinfo_eq. iExists γtl,γel,γh,γg,γn,eV.(type),einfo. iFrame "#". iSplit; [done|repeat iSplit].
    - rewrite EVIEW. replace ({[e]} ∪ ({[e]} ∪ M)) with ({[e]} ∪ M); [|set_solver].
      iApply big_sepS_forall. iIntros "%e'' %IN".
      destruct (decide (e'' = e)) as [->|NEe''].
      + rewrite OmoLe_eq. iExists γtl,γel,γh,γg,γn,einfo,einfo. iFrame "#". done.
      + have IN' : e'' ∈ M by set_solver.
        rewrite OmoEview_eq OmoLe_eq.
        iDestruct "⊒M" as (?????) "[[%Hγe'' %NEmp'] BIG]". encode_agree Hγe.
        rewrite big_sepS_elem_of; [|exact IN']. iDestruct "BIG" as (einfo'') "[EL@e'' _]".
        rewrite view_at_objective_iff.
        iExists γtl,γel,γh,γg,γn,einfo'',einfo. iFrame "#". iSplit; [done|].

        have EQlen : length (take (gen + 1) WL) = gen + 1.
          { rewrite take_length Nat.min_l; [done|]. apply lookup_lt_Some in Hwinfor. lia. }

        iAssert (∃ i winfo, ⌜ WL' !! i = Some winfo ∧ winfo.2 = einfo''.1.2 ∧ i ≤ gen + 1⌝)%I with "[-]" as %(i & winfo & Hwinfo & EQ & LE).
        { iDestruct (mono_list_auth_idx_lookup with "EL● EL@e''") as %LOOKUP.
          apply lookup_lt_Some in LOOKUP as LT. replace (length EL') with (length E') in LT; last first.
          { subst E' EL'. rewrite !app_length /=. lia. }
          rewrite -lookup_lt_is_Some in LT. eapply lookup_omo_surjective in LT as [eidx Heidx]; [|done].
          have [[e''' es'''] Hgen] : is_Some (omo' !! (gen_of eidx)).
          { rewrite lookup_lt_is_Some. apply lookup_omo_lt_Some in Heidx. done. }
          have [winfo Hwinfo] : is_Some (WL' !! (gen_of eidx)).
          { rewrite lookup_lt_is_Some. apply lookup_lt_Some in Hgen. subst WL' omo'. rewrite !app_length /= EQlen drop_length.
            apply lookup_lt_Some in Hwinfor. rewrite omo_insert_w_length -EQlenWL in Hgen. lia. }
          iDestruct (big_sepL2_lookup with "WL✓") as (????) "([%EQ1 %EQ2] & RL● & #EL@e''' & BIG)"; [done|done|].
          inversion EQ1. subst e0 es winfo. clear EQ1.
          iExists (gen_of eidx),(e''',γrl0,einfo0.1.2). iSplit; [done|]. iSplit.
          - destruct eidx.
            + rewrite lookup_omo_ro_event /omo_read_op list_lookup_fmap Hgen /= in Heidx.
              iDestruct (big_sepL_lookup with "BIG") as (?) "[#EL@e''a %EQ]"; [done|].
              iDestruct (mono_list_idx_agree with "EL@e'' EL@e''a") as %<-. done.
            + rewrite lookup_omo_wr_event /omo_write_op list_lookup_fmap Hgen /= in Heidx. inversion Heidx. subst e'''.
              iDestruct (mono_list_idx_agree with "EL@e'' EL@e'''") as %<-. done.
          - specialize (MAXgen _ IN') as (eidx' & Heidx' & LE).
            subst omo'. destruct (decide (eidx = wr_event (gen + 1))) as [->|NEQeidx].
            { have EQlen' : length (take (gen + 1) omo) = gen + 1.
              { rewrite take_length -EQlenWL Nat.min_l; [done|]. apply lookup_lt_Some in Hwinfor. lia. }
              rewrite /omo_insert_w /= lookup_app_r in Hgen; [|by rewrite EQlen'].
              rewrite EQlen' in Hgen. replace (gen + 1 - (gen + 1)) with 0 in Hgen by lia. simpl in Hgen. inversion Hgen. subst e''' es'''. done. }
            eapply lookup_omo_before_insert_w in Heidx as Heidx''; try done; last first.
            { apply lookup_lt_Some in Hwinfor. rewrite -EQlenWL. lia. }
            destruct Heidx'' as (eidx'' & Heidx'' & CASE).
            specialize (lookup_omo_inj _ _ _ _ _ _ OMO_GOOD Heidx' Heidx'') as EQ. subst eidx''.
            destruct (decide (gen_of eidx < gen + 1)).
            + subst eidx'. iPureIntro. lia.
            + destruct CASE as (H1 & H2 & H3). rewrite H2. lia. }
        have Hwinfo' : WL' !! (gen + 1) = Some (e, γrl, einfo.1.2).
        { rewrite lookup_app_r; [|by rewrite EQlen]. rewrite EQlen. replace (gen + 1 - (gen + 1)) with 0 by lia. simpl. done. }
        destruct (decide (i = gen + 1)) as [->|NEQ].
        * rewrite Hwinfo in Hwinfo'. inversion Hwinfo'. subst winfo. simpl in *. rewrite -EQ. done.
        * have CONDLT : i < gen + 1 by lia.
          specialize (MONOqg' _ _ _ _ Hwinfo Hwinfo' CONDLT). rewrite EQ /= in MONOqg'. subst einfo. simpl. iPureIntro. by apply Qp.lt_le_incl.
    - rewrite EVIEW eVOUT. replace ({[e]} ∪ ({[e]} ∪ M)) with ({[e]} ∪ M); [|set_solver].
      rewrite -OmoEview_split; [|set_solver-|set_solver]. iFrame "⊒M". rewrite OmoEview_eq.
      iExists γtl,γel,γh,γg,γn. iSplit.
      { iPureIntro. split; [done|]. set_solver-. }
      rewrite big_sepS_singleton. iExists einfo. iFrame "#". subst einfo. simpl. rewrite eVOUT. done. }
  iAssert (OmoAuth_all_elem γe E')%I with "[-]" as "#ELEMS'".
  { iApply big_sepL_snoc. iFrame "ELEMS e✓eV". }

  iModIntro. iExists γs'. iFrame "WCOMMIT e✓eV". iSplitL.
  - rewrite OmoHbToken_eq. iExists γtl,γel,γh,γg,γn,γwl',γsl',γq'. iExists TL',EL',WL',QM',einfo,[].
    replace (take (length EL' - 1) EL') with EL; last first.
    { subst EL'. rewrite app_length /= Nat.add_sub take_app. done. }
    iFrame. iFrame "ELEMS' KEYS'". rewrite big_sepL_nil. iPureIntro. split_and!; try done.
    + subst E' TL'. rewrite !app_length /=. lia.
    + subst E' EL'. rewrite !app_length /=. lia.
    + subst EL'. rewrite app_length /= Nat.add_sub. done.
    + subst EL'. rewrite last_app. done.
    + subst E' TL'. rewrite /OmoAuth_E_TL_valid. intros. destruct (decide (e0 = length E)) as [->|NEQ].
      * rewrite lookup_app_1_eq in H0. rewrite EQlenTL lookup_app_1_eq in H1. inversion H0. inversion H1. subst eV0 ty. done.
      * rewrite lookup_app_1_ne in H0; [|done]. rewrite lookup_app_1_ne in H1; [|rewrite -EQlenTL;done].
        rewrite /OmoAuth_E_TL_valid in E_TL_VALID. eapply E_TL_VALID; try done.
    + subst E' EL'. rewrite /OmoAuth_E_EL_valid. intros. destruct (decide (e0 = length E)) as [->|NEQ].
      * rewrite lookup_app_1_eq in H0. rewrite EQlenEL lookup_app_1_eq in H1. inversion H0. inversion H1. subst eV0 einfo0. done.
      * rewrite lookup_app_1_ne in H0; [|done]. rewrite lookup_app_1_ne in H1; [|rewrite -EQlenEL;done].
        rewrite /OmoAuth_E_EL_valid in E_EL_VALID. eapply E_EL_VALID; try done.
    + unfold not. intros. subst E'. apply (f_equal length) in H0. rewrite app_length /= in H0. lia.
    + unfold not. intros. subst omo'. apply (f_equal length) in H0. rewrite omo_insert_w_length /= in H0. lia.
    + eapply history_wf_add; try done.
    + apply hb_xo_add; try done.
  - rewrite OmoEview_eq. iDestruct "⊒M" as (?????) "[[%Hγe2 %NEmp'] BIGM]". encode_agree Hγe.
    iExists γtl,γel,γh,γg,γn. iSplit.
    { iPureIntro. split; [done|]. set_solver-. }
    rewrite big_sepS_union; last first.
    { rewrite disjoint_singleton_l. unfold not. intros. specialize (Mvalid _ H0). rewrite lookup_lt_is_Some in Mvalid. lia. }
    iFrame "BIGM". rewrite big_sepS_singleton. iExists einfo. iFrame "EL@e". subst einfo. simpl. rewrite eVOUT. done.
Qed.

Lemma OmoAuth_OmoHb_l γe γe' γs q E omo stlist e e' `{Interpretable eventT absStateT} :
  OmoAuth γe γs q E omo stlist _ -∗
  OmoHb γe γe' e e' -∗
  ⌜ is_Some (E !! e) ⌝.
Proof.
  iIntros "M● #e⊒e'". rewrite OmoAuth_eq OmoHb_eq.
  iDestruct "M●" as (??????????)
    "(%&%& [%Hγe %Hγs] & TL● & EL● & WL● & SL● & Hγq & HL● & Hγg & EL✓ & WL✓ & #ELEMS & #KEYS & Pures)".
  iDestruct "Pures" as %(EQlenTL & EQlenEL & E_TL_VALID & E_EL_VALID & MONOqg & QM_VALID & Nomo & NE & HWF & LHB & OMO_GOOD).
  iDestruct "e⊒e'" as (??????????) "(%&%&%& (%Hγe2 & %Hγe' & %INGL & %INCL1) & EL@e & #EL'@e' & GL0◯)".
  encode_agree Hγe.
  iDestruct (mono_list_auth_idx_lookup with "EL● EL@e") as %ELe.
  iPureIntro. rewrite lookup_lt_is_Some. apply lookup_lt_Some in ELe. lia.
Qed.

Lemma OmoAuth_OmoHb_l' γe γe' γs q E omo stlist e e' `{Interpretable eventT absStateT} :
  OmoAuth γe γs q E omo stlist _ -∗
  OmoHb γe γe' e e' -∗
  ∃ eidx, ⌜ lookup_omo omo eidx = Some e ⌝.
Proof.
  iIntros "M● #e⊒e'".
  iDestruct (OmoAuth_wf with "M●") as %[OMO_GOOD _].
  iDestruct (OmoAuth_OmoHb_l with "M● e⊒e'") as %VALe.
  eapply lookup_omo_surjective in OMO_GOOD as [eidx Heidx]; try done. iExists eidx. done.
Qed.

Lemma OmoAuth_OmoHb_r γe γe' γs' q' E' omo' stlist' e e' `{Interpretable eventT absStateT} :
  OmoAuth γe' γs' q' E' omo' stlist' _ -∗
  OmoHb γe γe' e e' -∗
  ⌜ is_Some (E' !! e') ⌝.
Proof.
  iIntros "M● #e⊒e'". rewrite OmoAuth_eq OmoHb_eq.
  iDestruct "M●" as (??????????)
    "(%&%& [%Hγe %Hγs] & TL● & EL● & WL● & SL● & Hγq & HL● & Hγg & EL✓ & WL✓ & #ELEMS & #KEYS & Pures)".
  iDestruct "Pures" as %(EQlenTL & EQlenEL & E_TL_VALID & E_EL_VALID & MONOqg & QM_VALID & Nomo & NE & HWF & LHB & OMO_GOOD).
  iDestruct "e⊒e'" as (??????????) "(%&%&%& (%Hγe2 & %Hγe' & %INGL & %INCL1) & EL@e & #EL'@e' & GL0◯)".
  encode_agree Hγe.
  iDestruct (mono_list_auth_idx_lookup with "EL● EL'@e'") as %ELe.
  iPureIntro. rewrite lookup_lt_is_Some. apply lookup_lt_Some in ELe. lia.
Qed.

Lemma OmoAuth_OmoHb_r' γe γe' γs' q' E' omo' stlist' e e' `{Interpretable eventT absStateT} :
  OmoAuth γe' γs' q' E' omo' stlist' _ -∗
  OmoHb γe γe' e e' -∗
  ∃ eidx', ⌜ lookup_omo omo' eidx' = Some e' ⌝.
Proof.
  iIntros "M● #e⊒e'".
  iDestruct (OmoAuth_wf with "M●") as %[OMO_GOOD _].
  iDestruct (OmoAuth_OmoHb_r with "M● e⊒e'") as %VALe.
  eapply lookup_omo_surjective in OMO_GOOD as [eidx Heidx]; try done. iExists eidx. done.
Qed.

Lemma OmoHb_new_2 γe γe' γs E omo stlist e eV e' M `{Interpretable eventT absStateT} :
  e' ∈ M →
  OmoHbToken γe γs E omo stlist e _ -∗
  @{eV.(sync)} OmoEview γe' M -∗
  OmoEinfo γe e eV ==∗
  OmoHbToken γe γs E omo stlist e _ ∗
  OmoHb γe γe' e e'.
Proof.
  iIntros "%IN M● #⊒M #e✓eV".
  rewrite OmoHbToken_eq OmoEinfo_eq OmoEview_eq OmoHb_eq.
  iDestruct "M●" as (??????????)
    "(%&%&%&%& [%Hγe %Hγs] & TL● & EL● & WL● & SL● & Hγq & GL● & HL● & Hγg & EL✓ & WL✓ & #ELEMS & #KEYS & #BIG & Pures)".
  iDestruct "Pures" as %(EQlenTL & EQlenEL & EQe & LASTEL & E_TL_VALID & E_EL_VALID & MONOqg & QM_VALID & Nomo & NE & HWF & LHB & OMO_GOOD).
  iDestruct "e✓eV" as (???????) "((%Hγe' & %Hty & %Hdv & %Hlv) & TL@e & EL@e & HL@e & _)". encode_agree Hγe.
  iDestruct "⊒M" as (γtl' γel' γh' γg' γn' Hγe') "BIG'". destruct Hγe' as [Hγe' NEmp].
  rewrite big_sepS_elem_of; [|done]. iDestruct "BIG'" as (einfo') "[#EL'@e' ⊒OUT]".
  rewrite view_at_objective_iff.

  set GL' := GL ++ [(γe',e')].
  iMod (mono_list_auth_own_update GL' with "GL●") as "[GL● #GL◯]"; [by eapply prefix_app_r|].
  iDestruct (mono_list_auth_idx_lookup with "EL● EL@e") as %LOOKUP.
  have EQ : elast = einfo.
  { subst e. rewrite last_lookup in LASTEL. replace (Init.Nat.pred (length EL)) with (length EL - 1) in LASTEL by lia.
    rewrite LASTEL in LOOKUP. inversion LOOKUP. done. }
  subst einfo. iModIntro. iSplitL.
  - repeat iExists _. iFrame "∗#". rewrite big_sepL_singleton. iSplitL; [done|]. iSplitL; [|done].
    iExists γe',e',γtl',γel',γh',γg',γn',einfo'. iFrame "#". rewrite -Hdv.
    rewrite !view_at_unfold !monPred_at_in. iDestruct "⊒OUT" as %?. done.
  - iExists γtl,γel,γh,γg,γn. iExists γtl',γel',γh',γg',γn'. iExists elast,einfo',GL'. iFrame "#".
    rewrite !view_at_unfold !monPred_at_in. iDestruct "⊒OUT" as %H'. rewrite Hdv in H'. iPureIntro. split_and!; try done.
    apply elem_of_list_lookup. exists (length GL). by rewrite lookup_app_1_eq.
Qed.

Lemma OmoHb_new_3 γe γe' γe'' γs E omo stlist e e' e'' `{Interpretable eventT absStateT} :
  OmoHbToken γe γs E omo stlist e _ -∗
  OmoHb γe γe' e e' -∗ OmoHb γe' γe'' e' e'' ==∗
  OmoHbToken γe γs E omo stlist e _ ∗ OmoHb γe γe'' e e''.
Proof.
  iIntros "M● #e⊒e' #e'⊒e''".
  rewrite OmoHbToken_eq OmoHb_eq.
  iDestruct "M●" as (??????????)
    "(%&%&%&%& [%Hγe %Hγs] & TL● & EL● & WL● & SL● & Hγq & GL● & HL● & Hγg & EL✓ & WL✓ & #ELEMS & #KEYS & #BIG & Pures)".
  iDestruct "Pures" as %(EQlenTL & EQlenEL & EQe & LASTEL & E_TL_VALID & E_EL_VALID & MONOqg & QM_VALID & Nomo & NE & HWF & LHB & OMO_GOOD).
  iDestruct "e⊒e'" as (??????????) "(%&%&%& (%Hγe2 & %Hγe' & %INGL & %INCL1) & EL@e & #EL'@e' & GL0◯)".
  iDestruct "e'⊒e''" as (????? γtl'' γel'' γh'' γg'' γn'') "(%& %einfo'' & %GL0' & (%Hγe'2 & %Hγe'' & %INGL' & %INCL2) & EL'@e'2 & #EL''@e'' & GL◯')".
  encode_agree Hγe. encode_agree Hγe'.
  iDestruct (mono_list_idx_agree with "EL'@e' EL'@e'2") as %<-.

  set GL' := GL ++ [(γe'',e'')].
  iMod (mono_list_auth_own_update GL' with "GL●") as "[GL● #GL◯]"; [by eapply prefix_app_r|].
  iDestruct (mono_list_auth_idx_lookup with "EL● EL@e") as %LOOKUP.
  have EQ : elast = einfo.
  { subst e. rewrite last_lookup in LASTEL. replace (Init.Nat.pred (length EL)) with (length EL - 1) in LASTEL by lia.
    rewrite LASTEL in LOOKUP. inversion LOOKUP. done. }
  subst einfo. iModIntro. iSplitL.
  - repeat iExists _. iFrame "∗#". rewrite big_sepL_singleton. iSplitL; [done|]. iSplitL; [|done].
    iExists γe'',e'',γtl'',γel'',γh'',γg'',γn'',einfo''. iFrame "#". iPureIntro. split_and!; try done. solve_lat.
  - iExists γtl,γel,γh,γg,γn. iExists γtl'',γel'',γh'',γg'',γn''. iExists elast,einfo'',GL'. iFrame "#". iPureIntro. split_and!; try done; [|solve_lat].
    apply elem_of_list_lookup. exists (length GL). by rewrite lookup_app_1_eq.
Qed.

Lemma OmoHbs_new γe γe' γs E omo stlist e eV M `{Interpretable eventT absStateT} :
  OmoHbToken γe γs E omo stlist e _ -∗
  @{eV.(sync)} OmoEview γe' M -∗
  OmoEinfo γe e eV ==∗
  OmoHbToken γe γs E omo stlist e _ ∗
  OmoHbs γe γe' e M.
Proof.
  iIntros "M● #⊒M #e✓eV". iDestruct (OmoEview_nonempty_obj with "⊒M") as %NEmp.
  iInduction M as [|e' M NotIn] "IH" using set_ind_L.
  - iModIntro. iFrame. rewrite OmoHbs_eq. rewrite /OmoHbs_def big_sepS_empty. done.
  - destruct (decide (M = ∅)) as [EQ|NEmp'].
    { have EQ' : {[e']} ∪ M = {[e']} by set_solver. rewrite EQ'. subst M. clear EQ'.
      iMod (OmoHb_new_2 _ _ _ _ _ _ _ _ e' with "M● ⊒M e✓eV") as "[M● #e⊒e']"; [set_solver|].
      iModIntro. iFrame. rewrite OmoHbs_eq /OmoHbs_def big_sepS_singleton. done. }
    rewrite -OmoEview_split; [|set_solver-|set_solver]. iDestruct "⊒M" as "[⊒e' ⊒M]".
    iMod ("IH" with "[] ⊒M M●") as "[M● #e⊒M]"; [done|].
    iMod (OmoHb_new_2 _ _ _ _ _ _ _ _ e' with "M● ⊒e' e✓eV") as "[M● #e⊒e']"; [set_solver|].
    iModIntro. iFrame. rewrite !OmoHbs_eq. iApply big_sepS_union; [set_solver|].
    iFrame "#". rewrite big_sepS_singleton. iFrame "#".
Qed.

Lemma OmoHb_new_2' γe γe' γs E omo stlist e eV e' M `{Interpretable eventT absStateT} :
  E !! e = Some eV →
  e' ∈ M →
  OmoHbToken γe γs E omo stlist e _ -∗
  @{eV.(sync)} OmoEview γe' M ==∗
  OmoHbToken γe γs E omo stlist e _ ∗
  OmoHb γe γe' e e'.
Proof.
  iIntros "%HeV %IN M● #⊒M".
  iAssert (OmoEinfo γe e eV)%I with "[-]" as "#e✓eV".
  { iDestruct (OmoHbToken_finish with "M●") as "M●".
    iDestruct (OmoEinfo_get with "M●") as "?"; try done. }
  iApply (OmoHb_new_2 with "M●"); try done.
Qed.

Lemma OmoHbs_new' γe γe' γs E omo stlist e eV M `{Interpretable eventT absStateT} :
  E !! e = Some eV →
  OmoHbToken γe γs E omo stlist e _ -∗
  @{eV.(sync)} OmoEview γe' M ==∗
  OmoHbToken γe γs E omo stlist e _ ∗
  OmoHbs γe γe' e M.
Proof.
  iIntros "%HeV M● #⊒M".
  iAssert (OmoEinfo γe e eV)%I with "[-]" as "#e✓eV".
  { iDestruct (OmoHbToken_finish with "M●") as "M●".
    iDestruct (OmoEinfo_get with "M●") as "?"; try done. }
  iApply (OmoHbs_new with "M●"); try done.
Qed.

(* Insert a new event into `CWMono` if e2' is the latest write event *)
Lemma CWMono_insert_last eidx γe γe' γm γs q E omo stlist M e1 e2 e1' e2' `{Interpretable eventT absStateT} :
  lookup_omo omo eidx = Some e1' → (gen_of eidx = length omo - 1)%nat →
  CWMono γe γe' γm M -∗
  OmoAuth γe' γs q E (omo_append_w omo e2' []) stlist _ -∗
  CWMonoValid γm e1 -∗
  OmoCW γe γe' e1 e1' -∗
  OmoCW γe γe' e2 e2' -∗
  OmoLe γe e1 e2
  ==∗
  CWMono γe γe' γm ({[e2]} ∪ M) ∗ CWMonoValid γm e2 ∗ OmoAuth γe' γs q E (omo_append_w omo e2' []) stlist _.
Proof.
  iIntros "%Heidx %EQgen MONO M● #MONO✓e1 #e1↦e1' #e2↦e2' #e1≤e2".
  destruct (decide (e2 ∈ M)) as [IN|NOTIN].
  { replace ({[e2]} ∪ M) with M by set_solver.
    iDestruct (CWMonoValid_new with "MONO") as "#MONO✓e2"; [done|].
    iModIntro. iFrame "∗#". }

  rewrite CWMono_eq CWMonoValid_eq.
  iDestruct (OmoAuth_OmoCW_r with "M● e1↦e1'") as %[eV1' HeV1'].
  iDestruct (OmoEinfo_get with "M●") as "#e1'✓eV1'"; [done|].
  iDestruct (OmoAuth_wf with "M●") as %[OMO_GOOD _].
  have Nomo : omo ≠ [].
  { unfold not. intros. subst omo. apply lookup_omo_lt_Some in Heidx. simpl in *. lia. }
  have NZomo : length omo ≠ 0 by destruct omo.

  iDestruct "MONO" as "(Hγm & #BIG & #COND)".
  iDestruct (ghost_map_lookup with "Hγm MONO✓e1") as %INe1.
  apply lookup_gset_to_gmap_Some in INe1. destruct INe1 as [INe1 _].
  iDestruct (OmoLt_get_append_w with "M● e1'✓eV1'") as "#e1'<e2'".
  { unfold not. intros. subst e2'.
    have Heidx' : lookup_omo (omo_append_w omo e1' []) (wr_event (length omo)) = Some e1'.
    { rewrite lookup_omo_wr_event omo_append_w_write_op omo_write_op_length lookup_app_1_eq. done. }
    have Heidx'' : lookup_omo (omo_append_w omo e1' []) eidx = Some e1'.
    { rewrite lookup_omo_before_append_w decide_False; [done|]. unfold not. intros. subst eidx. simpl in EQgen. lia. }
    specialize (lookup_omo_inj _ _ _ _ _ _ OMO_GOOD Heidx' Heidx'') as EQ. subst eidx. simpl in EQgen. lia. }

  iAssert (∀ e, ⌜ e ∈ M ∧ e ≠ e2 ⌝ -∗ ∃ e', OmoCW γe γe' e e' ∗ OmoLe γe' e' e1')%I with "[-]" as "#MAXgen".
  { iIntros "%e [%IN %NE]". iDestruct (big_sepS_elem_of with "BIG") as (e') "[_ e↦e']"; [done|].
    iExists e'. iFrame "#". set omo' := (omo_append_w omo e2' []).
    have Heidxn : lookup_omo omo' eidx = Some e1'.
    { rewrite lookup_omo_before_append_w decide_False; [done|]. unfold not. intros. subst eidx.
      apply lookup_omo_lt_Some in Heidx. simpl in Heidx. lia. }
    iDestruct (OmoAuth_OmoCW_r' with "M● e↦e'") as %[eidx' Heidx'].
    iAssert (⌜ e' ≠ e2' ⌝)%I with "[-]" as %NE'.
    { unfold not. iIntros "%EQ". subst e'.
      iDestruct (OmoCW_agree_2 with "e2↦e2' e↦e'") as %[_ ->]. done. }
    iApply (OmoLe_get with "M●"); try done. rewrite EQgen.

    have Heidx'' : lookup_omo omo' eidx' = Some e' by done.
    rewrite lookup_omo_before_append_w decide_False in Heidx'; last first.
    { unfold not. intros. subst eidx'.
      rewrite lookup_omo_wr_event omo_append_w_write_op omo_write_op_length lookup_app_1_eq in Heidx''.
      inversion Heidx''. subst e'. done. }
    apply lookup_omo_lt_Some in Heidx'. lia. }

  iMod (ghost_map_insert_persist e2 0 with "Hγm") as "[Hγm #KEYe2]".
  { rewrite lookup_gset_to_gmap_None. done. }
  rewrite -gset_to_gmap_union_singleton.
  iModIntro. iFrame "∗#". iSplit.
  - iApply big_sepS_union; [set_solver|]. rewrite big_sepS_singleton. iFrame "#". iExists e2'. done.
  - iModIntro. iIntros "%e3 %e4 %e3' %e4' [%IN3 %IN4] #e3↦e3' #e4↦e4' #e3'≤e4'".
    destruct (decide (e3 = e2)) as [->|NE3]; destruct (decide (e4 = e2)) as [->|NE4].
    + iDestruct (OmoEq_get_from_CW with "e2↦e2'") as "[#e2=e2 _]".
      by iApply OmoLe_get_from_Eq.
    + have IN4' : e4 ∈ M by set_solver.
      iDestruct (OmoCW_agree_1 with "e2↦e2' e3↦e3'") as %[_ <-].
      iDestruct (OmoLt_Le_trans with "e1'<e2' e3'≤e4'") as "e1'<e4'".
      iDestruct ("MAXgen" $! e4 with "[]") as (?) "[e4↦e4'' e4'≤e1']"; [done|].
      iDestruct (OmoCW_agree_1 with "e4↦e4' e4↦e4''") as %[_ <-].
      by iDestruct (OmoLe_Lt_contra with "e4'≤e1' e1'<e4'") as "?".
    + have IN3' : e3 ∈ M by set_solver.
      iDestruct (OmoCW_agree_1 with "e2↦e2' e4↦e4'") as %[_ <-].
      iDestruct ("MAXgen" $! e3 with "[]") as (?) "[e3↦e3'' e3'≤e1']"; [done|].
      iDestruct (OmoCW_agree_1 with "e3↦e3' e3↦e3''") as %[_ <-].
      iDestruct ("COND" with "[] e3↦e3' e1↦e1' e3'≤e1'") as "e3≤e1"; [done|].
      iApply OmoLe_trans; try done.
    + have IN3' : e3 ∈ M by set_solver.
      have IN4' : e4 ∈ M by set_solver.
      by iApply "COND".
Qed.

Lemma CWMono_insert_last_from_HbToken eidx γe γe' γm γs E omo stlist M e1 e2 e1' e2' e3' `{Interpretable eventT absStateT} :
  lookup_omo omo eidx = Some e1' → (gen_of eidx = length omo - 1)%nat →
  CWMono γe γe' γm M -∗
  OmoHbToken γe' γs E (omo_append_w omo e2' []) stlist e3' _ -∗
  CWMonoValid γm e1 -∗
  OmoCW γe γe' e1 e1' -∗
  OmoCW γe γe' e2 e2' -∗
  OmoLe γe e1 e2
  ==∗
  CWMono γe γe' γm ({[e2]} ∪ M) ∗ CWMonoValid γm e2 ∗ OmoHbToken γe' γs E (omo_append_w omo e2' []) stlist e3' _.
Proof.
  iIntros "%Heidx %EQgen MONO M● #MONO✓e1 #e1↦e1' #e2↦e2' #e1≤e2".
  destruct (decide (e2 ∈ M)) as [IN|NOTIN].
  { replace ({[e2]} ∪ M) with M by set_solver.
    iDestruct (CWMonoValid_new with "MONO") as "#MONO✓e2"; [done|].
    iModIntro. iFrame "∗#". }

  rewrite CWMono_eq CWMonoValid_eq.
  iDestruct (OmoHbToken_OmoCW_r with "M● e1↦e1'") as %[eV1' HeV1'].
  iDestruct (OmoEinfo_get_from_HbToken with "M●") as "#e1'✓eV1'"; [done|].
  iDestruct (OmoHbToken_wf with "M●") as %[OMO_GOOD _].
  have Nomo : omo ≠ [].
  { unfold not. intros. subst omo. apply lookup_omo_lt_Some in Heidx. simpl in *. lia. }
  have NZomo : length omo ≠ 0 by destruct omo.

  iDestruct "MONO" as "(Hγm & #BIG & #COND)".
  iDestruct (ghost_map_lookup with "Hγm MONO✓e1") as %INe1.
  apply lookup_gset_to_gmap_Some in INe1. destruct INe1 as [INe1 _].
  iDestruct (OmoLt_get_append_w_from_HbToken with "M● e1'✓eV1'") as "#e1'<e2'".
  { unfold not. intros. subst e2'.
    have Heidx' : lookup_omo (omo_append_w omo e1' []) (wr_event (length omo)) = Some e1'.
    { rewrite lookup_omo_wr_event omo_append_w_write_op omo_write_op_length lookup_app_1_eq. done. }
    have Heidx'' : lookup_omo (omo_append_w omo e1' []) eidx = Some e1'.
    { rewrite lookup_omo_before_append_w decide_False; [done|]. unfold not. intros. subst eidx. simpl in EQgen. lia. }
    specialize (lookup_omo_inj _ _ _ _ _ _ OMO_GOOD Heidx' Heidx'') as EQ. subst eidx. simpl in EQgen. lia. }

  iAssert (∀ e, ⌜ e ∈ M ∧ e ≠ e2 ⌝ -∗ ∃ e', OmoCW γe γe' e e' ∗ OmoLe γe' e' e1')%I with "[-]" as "#MAXgen".
  { iIntros "%e [%IN %NE]". iDestruct (big_sepS_elem_of with "BIG") as (e') "[_ e↦e']"; [done|].
    iExists e'. iFrame "#". set omo' := (omo_append_w omo e2' []).
    have Heidxn : lookup_omo omo' eidx = Some e1'.
    { rewrite lookup_omo_before_append_w decide_False; [done|]. unfold not. intros. subst eidx.
      apply lookup_omo_lt_Some in Heidx. simpl in Heidx. lia. }
    iDestruct (OmoHbToken_OmoCW_r' with "M● e↦e'") as %[eidx' Heidx'].
    iAssert (⌜ e' ≠ e2' ⌝)%I with "[-]" as %NE'.
    { unfold not. iIntros "%EQ". subst e'.
      iDestruct (OmoCW_agree_2 with "e2↦e2' e↦e'") as %[_ ->]. done. }
    iApply (OmoLe_get_from_HbToken with "M●"); try done. rewrite EQgen.

    have Heidx'' : lookup_omo omo' eidx' = Some e' by done.
    rewrite lookup_omo_before_append_w decide_False in Heidx'; last first.
    { unfold not. intros. subst eidx'.
      rewrite lookup_omo_wr_event omo_append_w_write_op omo_write_op_length lookup_app_1_eq in Heidx''.
      inversion Heidx''. subst e'. done. }
    apply lookup_omo_lt_Some in Heidx'. lia. }

  iMod (ghost_map_insert_persist e2 0 with "Hγm") as "[Hγm #KEYe2]".
  { rewrite lookup_gset_to_gmap_None. done. }
  rewrite -gset_to_gmap_union_singleton.
  iModIntro. iFrame "∗#". iSplit.
  - iApply big_sepS_union; [set_solver|]. rewrite big_sepS_singleton. iFrame "#". iExists e2'. done.
  - iModIntro. iIntros "%e3 %e4 %e3'' %e4' [%IN3 %IN4] #e3↦e3' #e4↦e4' #e3'≤e4'".
    destruct (decide (e3 = e2)) as [->|NE3]; destruct (decide (e4 = e2)) as [->|NE4].
    + iDestruct (OmoEq_get_from_CW with "e2↦e2'") as "[#e2=e2 _]".
      by iApply OmoLe_get_from_Eq.
    + have IN4' : e4 ∈ M by set_solver.
      iDestruct (OmoCW_agree_1 with "e2↦e2' e3↦e3'") as %[_ <-].
      iDestruct (OmoLt_Le_trans with "e1'<e2' e3'≤e4'") as "e1'<e4'".
      iDestruct ("MAXgen" $! e4 with "[]") as (?) "[e4↦e4'' e4'≤e1']"; [done|].
      iDestruct (OmoCW_agree_1 with "e4↦e4' e4↦e4''") as %[_ <-].
      by iDestruct (OmoLe_Lt_contra with "e4'≤e1' e1'<e4'") as "?".
    + have IN3' : e3 ∈ M by set_solver.
      iDestruct (OmoCW_agree_1 with "e2↦e2' e4↦e4'") as %[_ <-].
      iDestruct ("MAXgen" $! e3 with "[]") as (?) "[e3↦e3'' e3'≤e1']"; [done|].
      iDestruct (OmoCW_agree_1 with "e3↦e3' e3↦e3''") as %[_ <-].
      iDestruct ("COND" with "[] e3↦e3' e1↦e1' e3'≤e1'") as "e3≤e1"; [done|].
      iApply OmoLe_trans; try done.
    + have IN3' : e3 ∈ M by set_solver.
      have IN4' : e4 ∈ M by set_solver.
      by iApply "COND".
Qed.

End omo_specific_1_lemma.

(* Lemmas that involve single `omoGeneralG` and two `omoSpecificG`'s *)
Section omo_specific_2_lemma.
Context {eventT1 eventT2 absStateT1 absStateT2 : Type}.
Context {Σ : gFunctors} `{!omoGeneralG Σ, !omoSpecificG Σ eventT1 absStateT1, !omoSpecificG Σ eventT2 absStateT2}.

Notation vProp := (vProp Σ).
Notation historyT1 := (history eventT1).
Notation historyT2 := (history eventT2).

Implicit Types
  (γe γs γtl γel γh γg γwl γrl γgl γsl γq γb γm : gname)
  (q qg : Qp)
  (M : eView)
  (einfo : (gname * option gname * view * eView * Qp * gname))
  (EL : list (gname * option gname * view * eView * Qp * gname)) (* mono_list for all event info excluding event type *)
  (WL : list (event_id * gname * Qp)) (* mono_list for γs *)
  (RL : list event_id) (* mono_list for each generation *)
  (GL : list (gname * event_id)) (* mono_list for commit-with relation or seen_event *)
  (QM : gmap Qp nat)
  (eidx : event_idx).

Local Open Scope nat_scope.

Lemma OmoHb_new_1 γe γe' γs (E1 : historyT1) omo1 (stlist : list absStateT1) e e' (eV : omo_event eventT1) (eV' : omo_event eventT2) `{Interpretable eventT1 absStateT1} :
  eV'.(sync) ⊑ eV.(sync) →
  OmoHbToken γe γs E1 omo1 stlist e _ -∗
  OmoEinfo γe e eV -∗
  OmoEinfo γe' e' eV'
  ==∗
  OmoHbToken γe γs E1 omo1 stlist e _ ∗
  OmoHb γe γe' e e'.
Proof.
  iIntros "%LE M● #e✓eV #e'✓eV'". rewrite OmoHbToken_eq !OmoEinfo_eq OmoHb_eq.
  iDestruct "M●" as (??????????)
    "(%&%&%&%& [%Hγe %Hγs] & TL● & EL● & WL● & SL● & Hγq & GL● & HL● & Hγg & EL✓ & WL✓ & #ELEMS & #KEYS & #BIG & Pures)".
  iDestruct "Pures" as %(EQlenTL & EQlenEL & EQe & LASTEL & E_TL_VALID & E_EL_VALID & MONOqg & QM_VALID & Nomo & NE & HWF & LHB & OMO_GOOD).
  iDestruct "e✓eV" as (???????) "((%Hγe' & %Hty & %Hdv & %Hlv) & TL@e & EL@e & HL@e & _)". encode_agree Hγe.
  iDestruct "e'✓eV'" as (???????) "((%Hγe' & %Hty' & %Hdv' & %Hlv') & TL'@e' & EL'@e' & HL'@e' & _)".

  set GL' := GL ++ [(γe',e')].
  iMod (mono_list_auth_own_update GL' with "GL●") as "[GL● #GL◯]"; [by eapply prefix_app_r|].
  iDestruct (mono_list_auth_idx_lookup with "EL● EL@e") as %LOOKUP.
  have EQ : elast = einfo.
  { subst e. rewrite last_lookup in LASTEL. replace (Init.Nat.pred (length EL)) with (length EL - 1) in LASTEL by lia.
    rewrite LASTEL in LOOKUP. inversion LOOKUP. done. }
  subst einfo. iModIntro. iSplitL.
  - repeat iExists _. iFrame "∗#". rewrite big_sepL_singleton. iSplitL; [done|]. iSplitL; [|done].
    iExists γe',e',γtl0,γel0,γh0,γg0,γn0,einfo0. iFrame "#". rewrite -Hdv -Hdv'. done.
  - iExists γtl,γel,γh,γg,γn. iExists γtl0,γel0,γh0,γg0,γn0. iExists elast,einfo0,GL'. iFrame "#". rewrite -Hdv -Hdv'. iPureIntro. split_and!; try done.
    apply elem_of_list_lookup. exists (length GL). by rewrite lookup_app_1_eq.
Qed.

(* Special case of `CWMono_insert_last` where e2 is also the latest event *)
Lemma CWMono_insert_last_last eidx γe γe' γm γs γs' q q' (E : historyT1) (E' : historyT2) omo omo' stlist stlist' M e e' `{Interpretable eventT1 absStateT1} `{Interpretable eventT2 absStateT2} :
  lookup_omo omo eidx = Some e → (gen_of eidx = length omo - 1)%nat →
  CWMono γe γe' γm M -∗
  OmoAuth γe γs q E omo stlist _ -∗
  OmoAuth γe' γs' q' E' (omo_append_w omo' e' []) stlist' _ -∗
  OmoCW γe γe' e e'
  ==∗
  CWMono γe γe' γm ({[e]} ∪ M) ∗ CWMonoValid γm e ∗
  OmoAuth γe γs q E omo stlist _ ∗ OmoAuth γe' γs' q' E' (omo_append_w omo' e' []) stlist' _.
Proof.
  iIntros "%Heidx %EQgen MONO M● M'● #e↦e'".
  destruct (decide (e ∈ M)) as [IN|NOTIN].
  { replace ({[e]} ∪ M) with M by set_solver.
    iDestruct (CWMonoValid_new with "MONO") as "#MONO✓e"; [done|].
    iModIntro. iFrame "∗#". }

  rewrite CWMono_eq CWMonoValid_eq.
  iDestruct "MONO" as "(Hγm & #BIG & #COND)".
  iMod (ghost_map_insert_persist e 0 with "Hγm") as "[Hγm #KEYe]".
  { rewrite lookup_gset_to_gmap_None. done. }
  rewrite -gset_to_gmap_union_singleton.

  iAssert (∀ en, ⌜ en ∈ M ⌝ -∗ ∃ en', OmoCW γe γe' en en' ∗ OmoLe γe en e ∗ OmoLt γe' en' e')%I with "[-]" as "#COND'".
  { iIntros "%en %IN". iDestruct (big_sepS_elem_of with "BIG") as (en') "[_ en↦en']"; [done|].
    iExists en'. iFrame "#". iSplitL "M●".
    - iDestruct (OmoAuth_OmoCW_l' with "M● en↦en'") as %[eidx' Heidx']. iDestruct (OmoAuth_omo_nonempty with "M●") as %Nomo.
      iApply (OmoLe_get with "M●"); try done.
      apply lookup_omo_lt_Some in Heidx'. lia.
    - have NEQ : e ≠ en by set_solver.
      set omo'' := (omo_append_w omo' e' []).
      have Heidxn : lookup_omo omo'' (wr_event (length omo')) = Some e'.
      { rewrite lookup_omo_wr_event omo_append_w_write_op omo_write_op_length lookup_app_1_eq. done. }
      iDestruct (OmoAuth_OmoCW_r' with "M'● en↦en'") as %[eidx' Heidx'].
      have Heidx'' : lookup_omo omo'' eidx' = Some en' by done.
      rewrite lookup_omo_before_append_w in Heidx'. destruct (decide (eidx' = wr_event (length omo'))) as [->|NEQ'].
      { rewrite Heidxn in Heidx'. inversion Heidx'. subst en'.
        iDestruct (OmoCW_agree_2 with "e↦e' en↦en'") as %[_ <-]. done. }
      iApply (OmoLt_get with "M'●"); try done. simpl. apply lookup_omo_lt_Some in Heidx'. done. }

  iModIntro. iFrame "∗#". rewrite big_sepS_union; [|set_solver]. rewrite big_sepS_singleton. iFrame "#". iSplit.
  - iExists e'. iFrame "#".
  - iModIntro. iIntros "%e1 %e2 %e1' %e2' [%IN1 %IN2] #e1↦e1' #e2↦e2' #e1'≤e2'".
    destruct (decide (e1 = e)) as [->|NE1]; destruct (decide (e2 = e)) as [->|NE2].
    + iDestruct (OmoEq_get_from_CW with "e↦e'") as "[e=e _]". by iApply OmoLe_get_from_Eq.
    + have IN2' : e2 ∈ M by set_solver.
      iDestruct (OmoCW_agree_1 with "e↦e' e1↦e1'") as %[_ <-].
      iDestruct ("COND'" $! e2 with "[]") as (?) "(e2↦e2'' & e2≤e & e2'<e')"; [done|].
      iDestruct (OmoCW_agree_1 with "e2↦e2' e2↦e2''") as %[_ <-].
      by iDestruct (OmoLe_Lt_contra with "e1'≤e2' e2'<e'") as "?".
    + have IN1' : e1 ∈ M by set_solver.
      iDestruct (OmoCW_agree_1 with "e↦e' e2↦e2'") as %[_ <-].
      iDestruct ("COND'" $! e1 with "[]") as (?) "(e1↦e1'' & e1≤e & e1'≤e')"; [done|].
      iDestruct (OmoCW_agree_1 with "e1↦e1' e1↦e1''") as %[_ <-]. done.
    + have IN1' : e1 ∈ M by set_solver.
      have IN2' : e2 ∈ M by set_solver.
      iDestruct ("COND" with "[] e1↦e1' e2↦e2' e1'≤e2'") as "?"; done.
Qed.

Lemma CWMono_insert_last_last_from_HbToken_1 eidx γe γe' γm γs γs' q' (E : historyT1) (E' : historyT2) omo omo' stlist stlist' M e e' e'' `{Interpretable eventT1 absStateT1} `{Interpretable eventT2 absStateT2} :
  lookup_omo omo eidx = Some e → (gen_of eidx = length omo - 1)%nat →
  CWMono γe γe' γm M -∗
  OmoHbToken γe γs E omo stlist e'' _ -∗
  OmoAuth γe' γs' q' E' (omo_append_w omo' e' []) stlist' _ -∗
  OmoCW γe γe' e e'
  ==∗
  CWMono γe γe' γm ({[e]} ∪ M) ∗ CWMonoValid γm e ∗
  OmoHbToken γe γs E omo stlist e'' _ ∗ OmoAuth γe' γs' q' E' (omo_append_w omo' e' []) stlist' _.
Proof.
  iIntros "%Heidx %EQgen MONO M● M'● #e↦e'".
  destruct (decide (e ∈ M)) as [IN|NOTIN].
  { replace ({[e]} ∪ M) with M by set_solver.
    iDestruct (CWMonoValid_new with "MONO") as "#MONO✓e"; [done|].
    iModIntro. iFrame "∗#". }

  rewrite CWMono_eq CWMonoValid_eq.
  iDestruct "MONO" as "(Hγm & #BIG & #COND)".
  iMod (ghost_map_insert_persist e 0 with "Hγm") as "[Hγm #KEYe]".
  { rewrite lookup_gset_to_gmap_None. done. }
  rewrite -gset_to_gmap_union_singleton.

  iAssert (∀ en, ⌜ en ∈ M ⌝ -∗ ∃ en', OmoCW γe γe' en en' ∗ OmoLe γe en e ∗ OmoLt γe' en' e')%I with "[-]" as "#COND'".
  { iIntros "%en %IN". iDestruct (big_sepS_elem_of with "BIG") as (en') "[_ en↦en']"; [done|].
    iExists en'. iFrame "#". iSplitL "M●".
    - iDestruct (OmoHbToken_OmoCW_l' with "M● en↦en'") as %[eidx' Heidx']. iDestruct (OmoHbToken_omo_nonempty with "M●") as %Nomo.
      iApply (OmoLe_get_from_HbToken with "M●"); try done.
      apply lookup_omo_lt_Some in Heidx'. lia.
    - have NEQ : e ≠ en by set_solver.
      set omo'' := (omo_append_w omo' e' []).
      have Heidxn : lookup_omo omo'' (wr_event (length omo')) = Some e'.
      { rewrite lookup_omo_wr_event omo_append_w_write_op omo_write_op_length lookup_app_1_eq. done. }
      iDestruct (OmoAuth_OmoCW_r' with "M'● en↦en'") as %[eidx' Heidx'].
      have Heidx'' : lookup_omo omo'' eidx' = Some en' by done.
      rewrite lookup_omo_before_append_w in Heidx'. destruct (decide (eidx' = wr_event (length omo'))) as [->|NEQ'].
      { rewrite Heidxn in Heidx'. inversion Heidx'. subst en'.
        iDestruct (OmoCW_agree_2 with "e↦e' en↦en'") as %[_ <-]. done. }
      iApply (OmoLt_get with "M'●"); try done. simpl. apply lookup_omo_lt_Some in Heidx'. done. }

  iModIntro. iFrame "∗#". rewrite big_sepS_union; [|set_solver]. rewrite big_sepS_singleton. iFrame "#". iSplit.
  - iExists e'. iFrame "#".
  - iModIntro. iIntros "%e1 %e2 %e1' %e2' [%IN1 %IN2] #e1↦e1' #e2↦e2' #e1'≤e2'".
    destruct (decide (e1 = e)) as [->|NE1]; destruct (decide (e2 = e)) as [->|NE2].
    + iDestruct (OmoEq_get_from_CW with "e↦e'") as "[e=e _]". by iApply OmoLe_get_from_Eq.
    + have IN2' : e2 ∈ M by set_solver.
      iDestruct (OmoCW_agree_1 with "e↦e' e1↦e1'") as %[_ <-].
      iDestruct ("COND'" $! e2 with "[]") as (?) "(e2↦e2'' & e2≤e & e2'<e')"; [done|].
      iDestruct (OmoCW_agree_1 with "e2↦e2' e2↦e2''") as %[_ <-].
      by iDestruct (OmoLe_Lt_contra with "e1'≤e2' e2'<e'") as "?".
    + have IN1' : e1 ∈ M by set_solver.
      iDestruct (OmoCW_agree_1 with "e↦e' e2↦e2'") as %[_ <-].
      iDestruct ("COND'" $! e1 with "[]") as (?) "(e1↦e1'' & e1≤e & e1'≤e')"; [done|].
      iDestruct (OmoCW_agree_1 with "e1↦e1' e1↦e1''") as %[_ <-]. done.
    + have IN1' : e1 ∈ M by set_solver.
      have IN2' : e2 ∈ M by set_solver.
      iDestruct ("COND" with "[] e1↦e1' e2↦e2' e1'≤e2'") as "?"; done.
Qed.

Lemma CWMono_insert_last_last_from_HbToken_2 eidx γe γe' γm γs γs' q (E : historyT1) (E' : historyT2) omo omo' stlist stlist' M e e' e'' `{Interpretable eventT1 absStateT1} `{Interpretable eventT2 absStateT2} :
  lookup_omo omo eidx = Some e → (gen_of eidx = length omo - 1)%nat →
  CWMono γe γe' γm M -∗
  OmoAuth γe γs q E omo stlist _ -∗
  OmoHbToken γe' γs' E' (omo_append_w omo' e' []) stlist' e'' _ -∗
  OmoCW γe γe' e e'
  ==∗
  CWMono γe γe' γm ({[e]} ∪ M) ∗ CWMonoValid γm e ∗
  OmoAuth γe γs q E omo stlist _ ∗ OmoHbToken γe' γs' E' (omo_append_w omo' e' []) stlist' e'' _.
Proof.
  iIntros "%Heidx %EQgen MONO M● M'● #e↦e'".
  destruct (decide (e ∈ M)) as [IN|NOTIN].
  { replace ({[e]} ∪ M) with M by set_solver.
    iDestruct (CWMonoValid_new with "MONO") as "#MONO✓e"; [done|].
    iModIntro. iFrame "∗#". }

  rewrite CWMono_eq CWMonoValid_eq.
  iDestruct "MONO" as "(Hγm & #BIG & #COND)".
  iMod (ghost_map_insert_persist e 0 with "Hγm") as "[Hγm #KEYe]".
  { rewrite lookup_gset_to_gmap_None. done. }
  rewrite -gset_to_gmap_union_singleton.

  iAssert (∀ en, ⌜ en ∈ M ⌝ -∗ ∃ en', OmoCW γe γe' en en' ∗ OmoLe γe en e ∗ OmoLt γe' en' e')%I with "[-]" as "#COND'".
  { iIntros "%en %IN". iDestruct (big_sepS_elem_of with "BIG") as (en') "[_ en↦en']"; [done|].
    iExists en'. iFrame "#". iSplitL "M●".
    - iDestruct (OmoAuth_OmoCW_l' with "M● en↦en'") as %[eidx' Heidx']. iDestruct (OmoAuth_omo_nonempty with "M●") as %Nomo.
      iApply (OmoLe_get with "M●"); try done.
      apply lookup_omo_lt_Some in Heidx'. lia.
    - have NEQ : e ≠ en by set_solver.
      set omo'' := (omo_append_w omo' e' []).
      have Heidxn : lookup_omo omo'' (wr_event (length omo')) = Some e'.
      { rewrite lookup_omo_wr_event omo_append_w_write_op omo_write_op_length lookup_app_1_eq. done. }
      iDestruct (OmoHbToken_OmoCW_r' with "M'● en↦en'") as %[eidx' Heidx'].
      have Heidx'' : lookup_omo omo'' eidx' = Some en' by done.
      rewrite lookup_omo_before_append_w in Heidx'. destruct (decide (eidx' = wr_event (length omo'))) as [->|NEQ'].
      { rewrite Heidxn in Heidx'. inversion Heidx'. subst en'.
        iDestruct (OmoCW_agree_2 with "e↦e' en↦en'") as %[_ <-]. done. }
      iApply (OmoLt_get_from_HbToken with "M'●"); try done. simpl. apply lookup_omo_lt_Some in Heidx'. done. }

  iModIntro. iFrame "∗#". rewrite big_sepS_union; [|set_solver]. rewrite big_sepS_singleton. iFrame "#". iSplit.
  - iExists e'. iFrame "#".
  - iModIntro. iIntros "%e1 %e2 %e1' %e2' [%IN1 %IN2] #e1↦e1' #e2↦e2' #e1'≤e2'".
    destruct (decide (e1 = e)) as [->|NE1]; destruct (decide (e2 = e)) as [->|NE2].
    + iDestruct (OmoEq_get_from_CW with "e↦e'") as "[e=e _]". by iApply OmoLe_get_from_Eq.
    + have IN2' : e2 ∈ M by set_solver.
      iDestruct (OmoCW_agree_1 with "e↦e' e1↦e1'") as %[_ <-].
      iDestruct ("COND'" $! e2 with "[]") as (?) "(e2↦e2'' & e2≤e & e2'<e')"; [done|].
      iDestruct (OmoCW_agree_1 with "e2↦e2' e2↦e2''") as %[_ <-].
      by iDestruct (OmoLe_Lt_contra with "e1'≤e2' e2'<e'") as "?".
    + have IN1' : e1 ∈ M by set_solver.
      iDestruct (OmoCW_agree_1 with "e↦e' e2↦e2'") as %[_ <-].
      iDestruct ("COND'" $! e1 with "[]") as (?) "(e1↦e1'' & e1≤e & e1'≤e')"; [done|].
      iDestruct (OmoCW_agree_1 with "e1↦e1' e1↦e1''") as %[_ <-]. done.
    + have IN1' : e1 ∈ M by set_solver.
      have IN2' : e2 ∈ M by set_solver.
      iDestruct ("COND" with "[] e1↦e1' e2↦e2' e1'≤e2'") as "?"; done.
Qed.

Lemma CWMono_insert_last_last_from_HbToken_3 eidx γe γe' γm γs γs' (E : historyT1) (E' : historyT2) omo omo' stlist stlist' M e e' e'' e''' `{Interpretable eventT1 absStateT1} `{Interpretable eventT2 absStateT2} :
  lookup_omo omo eidx = Some e → (gen_of eidx = length omo - 1)%nat →
  CWMono γe γe' γm M -∗
  OmoHbToken γe γs E omo stlist e'' _ -∗
  OmoHbToken γe' γs' E' (omo_append_w omo' e' []) stlist' e''' _ -∗
  OmoCW γe γe' e e'
  ==∗
  CWMono γe γe' γm ({[e]} ∪ M) ∗ CWMonoValid γm e ∗
  OmoHbToken γe γs E omo stlist e'' _ ∗ OmoHbToken γe' γs' E' (omo_append_w omo' e' []) stlist' e''' _.
Proof.
  iIntros "%Heidx %EQgen MONO M● M'● #e↦e'".
  destruct (decide (e ∈ M)) as [IN|NOTIN].
  { replace ({[e]} ∪ M) with M by set_solver.
    iDestruct (CWMonoValid_new with "MONO") as "#MONO✓e"; [done|].
    iModIntro. iFrame "∗#". }

  rewrite CWMono_eq CWMonoValid_eq.
  iDestruct "MONO" as "(Hγm & #BIG & #COND)".
  iMod (ghost_map_insert_persist e 0 with "Hγm") as "[Hγm #KEYe]".
  { rewrite lookup_gset_to_gmap_None. done. }
  rewrite -gset_to_gmap_union_singleton.

  iAssert (∀ en, ⌜ en ∈ M ⌝ -∗ ∃ en', OmoCW γe γe' en en' ∗ OmoLe γe en e ∗ OmoLt γe' en' e')%I with "[-]" as "#COND'".
  { iIntros "%en %IN". iDestruct (big_sepS_elem_of with "BIG") as (en') "[_ en↦en']"; [done|].
    iExists en'. iFrame "#". iSplitL "M●".
    - iDestruct (OmoHbToken_OmoCW_l' with "M● en↦en'") as %[eidx' Heidx']. iDestruct (OmoHbToken_omo_nonempty with "M●") as %Nomo.
      iApply (OmoLe_get_from_HbToken with "M●"); try done.
      apply lookup_omo_lt_Some in Heidx'. lia.
    - have NEQ : e ≠ en by set_solver.
      set omo'' := (omo_append_w omo' e' []).
      have Heidxn : lookup_omo omo'' (wr_event (length omo')) = Some e'.
      { rewrite lookup_omo_wr_event omo_append_w_write_op omo_write_op_length lookup_app_1_eq. done. }
      iDestruct (OmoHbToken_OmoCW_r' with "M'● en↦en'") as %[eidx' Heidx'].
      have Heidx'' : lookup_omo omo'' eidx' = Some en' by done.
      rewrite lookup_omo_before_append_w in Heidx'. destruct (decide (eidx' = wr_event (length omo'))) as [->|NEQ'].
      { rewrite Heidxn in Heidx'. inversion Heidx'. subst en'.
        iDestruct (OmoCW_agree_2 with "e↦e' en↦en'") as %[_ <-]. done. }
      iApply (OmoLt_get_from_HbToken with "M'●"); try done. simpl. apply lookup_omo_lt_Some in Heidx'. done. }

  iModIntro. iFrame "∗#". rewrite big_sepS_union; [|set_solver]. rewrite big_sepS_singleton. iFrame "#". iSplit.
  - iExists e'. iFrame "#".
  - iModIntro. iIntros "%e1 %e2 %e1' %e2' [%IN1 %IN2] #e1↦e1' #e2↦e2' #e1'≤e2'".
    destruct (decide (e1 = e)) as [->|NE1]; destruct (decide (e2 = e)) as [->|NE2].
    + iDestruct (OmoEq_get_from_CW with "e↦e'") as "[e=e _]". by iApply OmoLe_get_from_Eq.
    + have IN2' : e2 ∈ M by set_solver.
      iDestruct (OmoCW_agree_1 with "e↦e' e1↦e1'") as %[_ <-].
      iDestruct ("COND'" $! e2 with "[]") as (?) "(e2↦e2'' & e2≤e & e2'<e')"; [done|].
      iDestruct (OmoCW_agree_1 with "e2↦e2' e2↦e2''") as %[_ <-].
      by iDestruct (OmoLe_Lt_contra with "e1'≤e2' e2'<e'") as "?".
    + have IN1' : e1 ∈ M by set_solver.
      iDestruct (OmoCW_agree_1 with "e↦e' e2↦e2'") as %[_ <-].
      iDestruct ("COND'" $! e1 with "[]") as (?) "(e1↦e1'' & e1≤e & e1'≤e')"; [done|].
      iDestruct (OmoCW_agree_1 with "e1↦e1' e1↦e1''") as %[_ <-]. done.
    + have IN1' : e1 ∈ M by set_solver.
      have IN2' : e2 ∈ M by set_solver.
      iDestruct ("COND" with "[] e1↦e1' e2↦e2' e1'≤e2'") as "?"; done.
Qed.

End omo_specific_2_lemma.
