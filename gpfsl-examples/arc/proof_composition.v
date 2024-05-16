From gpfsl.examples Require Import sflib.

From iris.algebra Require Import auth gset gmap agree.
From iris.algebra Require Import lib.mono_list.
From iris.proofmode Require Import tactics.
From iris.base_logic.lib Require Import ghost_var ghost_map.
From iris.bi Require Import fractional.

From gpfsl.base_logic Require Import meta_data.
From gpfsl.examples.algebra Require Import mono_list_list saved_vprop.
From gpfsl.logic Require Import logatom atomics invariants.

From gpfsl.logic Require Import repeat_loop new_delete.
From gpfsl.examples Require Import uniq_token map_seq loc_helper algebra.mono_list.
From gpfsl.examples.omo Require Import omo omo_preds append_only_loc.
From gpfsl.examples.arc Require Import code spec_composition.

Require Import iris.prelude.options.

Local Notation ainfo_type := (Qp * view * (gset event_id) * (gset event_id) * append_only_type)%type.

Class arcG Σ := ArcG {
  arc_omoGeneralG :> omoGeneralG Σ;
  arc_arcG :> omoSpecificG Σ arc_event arc_state;
  arc_aolG :> appendOnlyLocG Σ;
  (** Qp:               fraction of strong/weak/fake arc
      view:             lower bound of observation of strong/weak/fake arc
      gset event_id:    lower bound of eView of strong/weak/fake arc
      gset event_id:    lower bound of set of observed message of weak counter
      append_only_type: current state of append_only_loc of weak counter (meaningful only in [sarc]) *)
  arc_ainfoG :> ghost_mapG Σ event_id ainfo_type;
  arc_aliveG :> ghost_varG Σ bool;
  arc_events :> ghost_varG Σ (gset event_id);
  arc_gname :> mono_listG gname Σ;
}.

Definition arcΣ : gFunctors :=
  #[omoGeneralΣ;
    omoSpecificΣ arc_event arc_state;
    appendOnlyLocΣ;
    ghost_mapΣ event_id ainfo_type;
    ghost_varΣ bool;
    ghost_varΣ (gset event_id);
    mono_listΣ gname].

Global Instance subG_arcΣ {Σ} : subG arcΣ Σ → arcG Σ.
Proof. solve_inG. Qed.

Section Arc.
Context `{!noprolG Σ, !atomicG Σ, !arcG Σ}.

Local Notation iProp := (iProp Σ).
Local Notation vProp := (vProp Σ).
Local Open Scope nat_scope.

Implicit Types
  (γg γn γnl γs γsa γwa γb γm γes γss γew γsw γu γd γl γul : gname) (qs qw qsa qwa : Qp) (alive : bool)
  (omo omos omow : omoT) (l : loc) (mos mow : list loc_state)
  (stlist : list arc_state) (st stf : arc_state)
  (eV : omo_event arc_event) (eVl eVs : omo_event loc_event)
  (E : history arc_event) (Es Ew : history loc_event)
  (arcs sarc warc : gmap event_id ainfo_type)
  (ainfo : ainfo_type)
  (sdom wdom adom upds dgds lcks ulcks : gset event_id)
  .

Definition arcN (N : namespace) := N .@ "arc".

(* Used by [map_fold] in computing summation of Qp field of [sarc] or [warc] *)
Definition frac_sum := λ (e : event_id) (val : ainfo_type) (q : Qp), (val.1.1.1.1 + q)%Qp.
(* Used by [map_fold] in computing summation of view field of [sarc] or [warc] *)
Definition view_join_total := λ (e : event_id) (val : ainfo_type) (V : view), val.1.1.1.2 ⊔ V.

(* Inexistence of [WeakDrop _ true] or [Unique] that destroys Arc *)
Definition ArcAlive E : Prop :=
  Forall (λ eV, match eV.(type) with | WeakDrop _ true | Unique _ => False | _ => True end) E.

(* Every StrongArc object should observe [Clone] event that it has involved in *)
Definition SeenClone E sarc : Prop :=
  ∀ e e' ainfo eV,
    sarc !! e = Some ainfo →
      E !! e' = Some eV →
        eV.(type) = Clone e →
          e' ∈ ainfo.1.1.2.

(* Every WeakArc/FakeArc object should observe [WeakClone] event that it has involved in *)
(* Note: in fact, FakeArc cannot perform WeakClone event, but we can still state this invariant *)
Definition SeenWeakClone E warc : Prop :=
  ∀ e e' ainfo eV,
    warc !! e = Some ainfo →
      E !! e' = Some eV →
        eV.(type) = WeakClone e →
          e' ∈ ainfo.1.1.2.

(* Every [Upgrade] event should be observed by some WeakArc *)
(* Note: [upds] records observation of [Upgrade] event by destroyed WeakArc *)
Definition SeenUpgrade E warc upds : Prop :=
  ∀ e eV,
    E !! e = Some eV →
      match eV.(type) with
      | Upgrade => e ∈ upds ∨ (∃ e' ainfo, warc !! e' = Some ainfo ∧ e ∈ ainfo.1.1.2)
      | _ => True
      end.

(* Every [Downgrade] event should be observed by some StrongArc *)
(* Note: [dgds] records observation of [Downgrade] event by destroyed StrongArc *)
Definition SeenDowngrade E sarc dgds : Prop :=
  ∀ e eV,
    E !! e = Some eV →
      match eV.(type) with
      | Downgrade => e ∈ dgds ∨ (∃ e' ainfo, sarc !! e' = Some ainfo ∧ e ∈ ainfo.1.1.2)
      | _ => True
      end.

(* Every unlocking message is observed by some StrongArc *)
Definition SeenUnlock sarc lcks ulcks : Prop :=
  ∀ e, e ∈ ulcks → (e ∈ lcks ∨ (∃ e' ainfo, sarc !! e' = Some ainfo ∧ e ∈ ainfo.1.2)).

Definition ArcsValid E adom : Prop :=
  ∀ e, e ∈ adom → e < length E.

(* Dropped element should not be contained in [sarc] and [warc] *)
Definition ArcsValid2 E sdom wdom : Prop :=
  ∀ e eV,
    E !! e = Some eV →
      match eV.(type) with
      | StrongDrop e' _ => e' ∉ sdom
      | WeakDrop e' _ => e' ∉ wdom
      | _ => True
      end.

Definition EventIdValid E : Prop :=
  ∀ e eV,
    E !! e = Some eV →
      match eV.(type) with
      | Clone e' | WeakClone e' | WeakDrop e' _ | StrongDrop e' _ | UnwrapFail e' => e' < length E
      | _ => True
      end.

Definition ArcsSeen arcs Vp : Prop :=
  ∀ e ainfo, arcs !! e = Some ainfo → Vp ⊑ ainfo.1.1.1.2.

(* Whenever FakeArc is absent, StrongArc is also absent *)
Definition StlistValid stlist : Prop :=
  Forall (λ st, 0 ∉ st.2.1.1 → st.1.1.1 = ∅) stlist.

Definition AllLockMessageInner γew sarc lcks ew : vProp :=
  ∃ eVw (z : Z),
    OmoEinfo γew ew eVw ∗
    ⌜ (loc_event_msg eVw.(type)).1 = #z
    ∧ (z = (-1)%Z → (ew ∈ lcks ∨ (∃ e ainfo, sarc !! e = Some ainfo ∧ ew ∈ ainfo.1.2))) ⌝.

Definition AllLockMessage γew esw sarc lcks : vProp :=
  [∗ list] ew ∈ esw, AllLockMessageInner γew sarc lcks ew.

(* Every weak event or strong read-only event observes nearest previous strong write event *)
Definition SeenPrevStrong γg γes ess e : vProp :=
    (* Case 1: [e] is located later than last strong event *)
    (∃ ef esf esfeq, OmoLe γg ef e ∗ OmoEq γes esf esfeq ∗
      OmoCW γg γes ef esf ∗ OmoHb γg γes e esfeq ∗ ⌜ last ess = Some esf ⌝)
    (* Case 2: [e] is located between two consecutive strong events [el] and [er] *)
  ∨ (∃ el er esl esleq esr gen,
      OmoLe γg el e ∗ OmoLt γg e er ∗ OmoEq γes esl esleq ∗
      OmoCW γg γes el esl ∗ OmoCW γg γes er esr ∗ OmoHb γg γes e esleq ∗
      ⌜ ess !! gen = Some esl ∧ ess !! (gen + 1)%nat = Some esr ⌝).

Definition AllEvents γg γes γm E ess : vProp :=
  [∗ list] e↦eV ∈ E,
    match eV.(type) with
    | StrongInit | WeakInit | Clone _ | Upgrade | StrongDrop _ _ =>
      ∃ es, OmoCW γg γes e es ∗ OmoHb γg γes e es ∗ CWMonoValid γm e
    | _ => SeenPrevStrong γg γes ess e
    end.

Definition AllStrongsInner γg γes γs γss γm gen es : vProp :=
  ∃ e st eVs,
    OmoCW γg γes e es ∗ OmoHb γg γes e es ∗ OmoSnap γg γs e st ∗ OmoEinfo γes es eVs ∗ CWMonoValid γm e ∗
    (* every strong counter value matches with set size of abstract state *)
    ⌜ (loc_event_msg eVs.(type)).1 = #(size st.1.1.1) ⌝ ∗
    match gen with
    | 0 => emp
    | S _ => (* Invariant with previous message *)
      ∃ omos e' es' eV eVs' st',
        OmoSnapOmo γes γss omos ∗ OmoCW γg γes e' es' ∗ OmoEinfo γg e eV ∗ OmoEinfo γes es' eVs' ∗ OmoSnap γg γs e' st' ∗ OmoLt γg e' e ∗
        ⌜ omo_write_op omos !! (gen - 1) = Some es' ∧ (loc_event_msg eVs'.(type)).1 = #(size st'.1.1.1) ∧ size st'.1.1.1 ≠ 0
        ∧ ( ( (* Case 1: strong count increases by 1 *)
              size st.1.1.1 = ((size st'.1.1.1) + 1)%nat ∧ ((∃ e'', eV.(type) = Clone e'' ∧ e'' ∈ st'.1.1.1) ∨ eV.(type) = Upgrade))
          ∨ ( (* Case 2: strong count decreases by 1 *)
              size st.1.1.1 = ((size st'.1.1.1) - 1)%nat ∧ (∃ e'' b, eV.(type) = StrongDrop e'' b))) ⌝
    end.

Definition AllStrongs γg γes γs γss γm ess : vProp :=
  [∗ list] gen↦es ∈ ess, AllStrongsInner γg γes γs γss γm gen es.

Definition AllWeaksInner γg γew γsw wdom ulcks gen ew : vProp :=
  ∃ eVw (v : Z),
    OmoEinfo γew ew eVw ∗
    ⌜ (loc_event_msg eVw.(type)).1 = #v ∧ (-1 ≤ v)%Z ⌝ ∗
    match gen with
    | 0 => emp
    | S _ => (* Invariant with previous message *)
      ∃ omow ew' eVw' (v' : Z),
        OmoSnapOmo γew γsw omow ∗ OmoEinfo γew ew' eVw' ∗
        ⌜ omo_write_op omow !! (gen - 1) = Some ew' ∧ (loc_event_msg eVw'.(type)).1 = #v' ⌝ ∗
        ( ( (* Case 1: weak count increases by 1 *)
            ∃ e eV, OmoCW γg γew e ew ∗ OmoEinfo γg e eV ∗ OmoHb γg γew e ew ∗
              ⌜ (1 ≤ v')%Z ∧ (v = v' + 1)%Z
                (** Corresponding event should be either [Downgrade] or [WeakClone].
                    Here, if weak counter increases from 1 to 2 and if we know that 0 is alive currently,
                    then we know it should be cloned from WeakArc with id 0 *)
              ∧ (eV.(type) = Downgrade ∨ (∃ e', eV.(type) = WeakClone e' ∧ ((v' = 1%Z ∧ 0 ∈ wdom) → e' = 0))) ⌝)
        ∨ ( (* Case 2: weak counter decreases by 1 *)
            ⌜ (1 ≤ v')%Z ∧ (v = v' - 1)%Z ⌝)
        ∨ ( (* Case 3: weak counter gets locked (i.e., 1 -> -1) *)
            ⌜ v' = 1%Z ∧ v = (-1)%Z ⌝)
        ∨ ( (* Case 4: weak counter gets unlocked (i.e., -1 -> 1) *)
            ⌜ v' = (-1)%Z ∧ v = 1%Z ∧ ew ∈ ulcks ⌝))
    end.

Definition AllWeaks γg γew γsw wdom ulcks esw : vProp :=
  [∗ list] gen↦ew ∈ esw, AllWeaksInner γg γew γsw wdom ulcks gen ew.

Definition ArcInternalInvAlive l γg γs γes γss γew γsw γsa γwa γb γm γu γd γl γul E omo ess esw sarc warc qsa qwa stlist (P1 : Qp → vProp) (P2 : vProp) : vProp :=
  ∃ Vbs Vbw ty uf stf esf ewf eVsf eVwf (nsf : nat) (zwf : Z) Vsf Vwf Vp q1 q2 qu qd upds dgds lcks ulcks,
    AllEvents γg γes γm E ess ∗
    AllStrongs γg γes γs γss γm ess ∗
    AllWeaks γg γew γsw (dom warc) ulcks esw ∗

    @{Vbs} append_only_loc l γes ∅ cas_only ∗
    @{Vbw} append_only_loc (l >> 1) γew uf ty ∗

    (** [upds]: set of [Upgrade] event observed by destroyed WeakArc
        [dgds]: set of [Downgrade] event observed by destroyed StrongArc
        [lcks]: set of locking/unlocking message of weak counter observed by destroyed StrongArc
        [ulcks]: set of entire unlocking message of weak counter *)
    ⎡ghost_var γu qu upds⎤ ∗
    ⎡ghost_var γd qd dgds⎤ ∗
    ⎡ghost_var γl qd lcks⎤ ∗
    ⎡ghost_var γul qwa ulcks⎤ ∗
    AllLockMessage γew esw sarc lcks ∗
    @{Vwf} (OmoEview γg upds ∗ OmoEview γew ulcks) ∗
    (* @{Vsf} (OmoEview γg dgds ∗ OmoEview γew lcks) ∗ *)

    OmoEinfo γes esf eVsf ∗
    OmoEinfo γew ewf eVwf ∗

    (* P1 is stored in this invariant whenever strong arc counter is nonzero *)
    match nsf with
    | 0 => emp
    | S _ =>
      @{Vp} (P1 q1) ∗ @{Vsf} (P1 q2 ∗ OmoEview γg dgds ∗ OmoEview γew lcks) ∗ (∃ eV0, OmoEinfo γg 0 eV0 ∗ ⌜ eV0.(type) = StrongInit ⌝) ∗
      ⎡0 ↪[γwa] ((1/2)%Qp, Vp, ∅, ∅, cas_only)⎤ ∗ ⎡ghost_var γb (1/2/2)%Qp true⎤ ∗ ⎡ghost_var γul (1/2)%Qp ulcks⎤ ∗
      ⌜ qd = 1%Qp ⌝ (* New [Downgrade] event can be inserted only if there exists a strong arc *)
    end ∗

    (** P2 is stored in this invariant
        whenever [fake_arc] has been returned or the Arc has been initialized by [create_weak] *)
    match warc !! 0 with
    | None => @{Vwf} P2
    | _ => emp
    end ∗

    (* Weak arc counter can be in [swriter] mode iff it is currently locked *)
    match ty with
    | cas_only =>
      ( (∃ e, OmoHb γg γew e ewf) ∨ (∃ e ainfo, ⌜ sarc !! e = Some ainfo ∧ ewf ∈ ainfo.1.2 ⌝) ∨ ⌜ nsf = 0 ⌝) ∗
      ⌜ zwf = Z.of_nat (size stf.2.1.1) ∧ qu = 1%Qp ⌝ (* New [Upgrade] event can only be inserted if current weak counter is unlocked *)
    | swriter =>
      ⌜ zwf = (-1)%Z ∧ size stf.2.1.1 = 1
      ∧ (∃ e ainfo, e ∈ stf.1.1.1 ∧ sarc !! e = Some ainfo ∧ ainfo.2 = swriter)
      ∧ qu = (1/2)%Qp ⌝
    end ∗

    (* Reading last message of strong/weak counter guarantees observing event view in corresponding abstract state *)
    @{Vsf} OmoEview γg (stf.1.2) ∗
    @{Vwf} OmoEview γg (stf.2.2) ∗

    ⌜ uf ⊆ {[#(-1)]} ∧ last ess = Some esf ∧ last esw = Some ewf
    ∧ loc_event_msg eVsf.(type) = (#nsf, Vsf)
    ∧ loc_event_msg eVwf.(type) = (#zwf, Vwf)
    ∧ map_fold frac_sum qsa sarc = 1%Qp
    ∧ map_fold frac_sum qwa warc = 1%Qp
    ∧ ArcsValid E (dom sarc) ∧ ArcsValid E (dom warc) ∧ ArcsValid2 E (dom sarc) (dom warc)
    ∧ SeenClone E sarc ∧ SeenWeakClone E warc
    ∧ omo_write_op omo !! 0 = Some 0
    (* [sarc] and [warc] should contain exactly strong/weak arc objects that are alive *)
    ∧ last stlist = Some stf ∧ dom sarc = stf.1.1.1 ∧ dom warc = stf.2.1.1
    ∧ qsa = (q1 + q2)%Qp
    ∧ ArcAlive E ∧ EventIdValid E
    (* Collecting all thread views and message view guarantees observing all events *)
    ∧ Vbs ⊔ Vbw ⊑ (map_fold view_join_total Vp sarc) ⊔ (map_fold view_join_total Vp warc) ⊔ Vsf ⊔ Vwf
    (* Reading last message of strong/weak counter guarantees observing physical view in abstract state *)
    ∧ stf.1.1.2 ⊑ Vsf ∧ stf.2.1.2 ⊑ Vwf
    (* Observation of [Upgrade], [Downgrade], and unlocking message *)
    ∧ SeenUpgrade E warc upds ∧ SeenDowngrade E sarc dgds ∧ SeenUnlock sarc lcks ulcks
    (* Vp is observed by all arcs *)
    ∧ ArcsSeen sarc Vp ∧ ArcsSeen warc Vp
    (* Whenever FakeArc is absent, StrongArc is also absent *)
    ∧ StlistValid stlist
    (* If there is no strong arc, all events regarding strong arcs are recorded in weak arcs *)
    ∧ (if (decide (nsf = 0)) then Vsf ⊑ (map_fold view_join_total Vp warc) ⊔ Vwf else True)
    ∧ nsf = size stf.1.1.1 ⌝.

Definition ArcGname γg γsa γwa γb γm γes γss γew γsw γu γd γl γul : vProp :=
  ∃ γnl γn, OmoGname γg γnl ∗ ⎡mono_list_idx_own γnl 0 γn⎤ ∗
    ⌜ γn = encode (γsa,γwa,γb,γm,γes,γss,γew,γsw,γu,γd,γl,γul) ⌝.

Definition ArcInternalInv γg l (P1 : Qp → vProp) (P2 : vProp) : vProp :=
  ∃ γsa γwa γs γb γm γes γss γew γsw γu γd γl γul sarc warc qsa qwa alive E Es Ew omo omos omow stlist mos mow Mono,
    ArcGname γg γsa γwa γb γm γes γss γew γsw γu γd γl γul ∗

    OmoAuth γg γs (1/2)%Qp E omo stlist _ ∗
    OmoAuth γes γss (1/2)%Qp Es omos mos _ ∗
    OmoAuth γew γsw (1/2)%Qp Ew omow mow _ ∗

    ⎡ghost_map_auth γsa 1 sarc⎤ ∗
    ⎡ghost_map_auth γwa 1 warc⎤ ∗
    ⎡ghost_var γb (qsa/2 + qwa/2)%Qp alive⎤ ∗
    CWMono γg γes γm Mono ∗

    (if alive then
      ArcInternalInvAlive l γg γs γes γss γew γsw γsa γwa γb γm γu γd γl γul E omo (omo_write_op omos) (omo_write_op omow) sarc warc qsa qwa stlist P1 P2
    else emp).

Definition ArcInv γg γs (l : loc) E omo stlist : vProp := OmoAuth γg γs (1/2)%Qp E omo stlist _.
Definition InternInv N γg l P1 P2 : vProp := inv (arcN N) (ArcInternalInv γg l P1 P2).

Definition StrongArc N γg l q P1 P2 M e : vProp :=
  ∃ γsa γwa γb γm γes γss γew γsw γu γd γl γul Ms Mw eV ainfo,
    ArcGname γg γsa γwa γb γm γes γss γew γsw γu γd γl γul ∗
    InternInv N γg l P1 P2 ∗

    OmoEview γg M ∗
    OmoEview γes Ms ∗
    OmoEview γew Mw ∗
    OmoEinfo γg e eV ∗
    ⊒ainfo.1.1.1.2 ∗

    ⎡ghost_var γb (ainfo.1.1.1.1/2)%Qp true⎤ ∗ (* Arc is alive *)
    ⎡e ↪[γsa] ainfo⎤ ∗

    ⌜ q = ainfo.1.1.1.1 ∧ ainfo.2 = cas_only ∧ e ∈ M ∧ (eV.(type) = StrongInit ∨ (∃ e', eV.(type) = Clone e') ∨ eV.(type) = Upgrade)
    ∧ ainfo.1.1.2 ⊆ M ∧ ainfo.1.2 ⊆ Mw ⌝
    .

Definition WeakArc N γg l P1 P2 M e : vProp :=
  ∃ γsa γwa γb γm γes γss γew γsw γu γd γl γul Ms Mw eV ainfo ulcks,
    ArcGname γg γsa γwa γb γm γes γss γew γsw γu γd γl γul ∗
    InternInv N γg l P1 P2 ∗

    OmoEview γg M ∗
    OmoEview γes Ms ∗
    OmoEview γew Mw ∗
    OmoEinfo γg e eV ∗
    ⊒ainfo.1.1.1.2 ∗

    ⎡ghost_var γb (ainfo.1.1.1.1/2)%Qp true⎤ ∗ (* Arc is alive *)
    ⎡e ↪[γwa] ainfo⎤ ∗
    ⎡ghost_var γul ainfo.1.1.1.1 ulcks⎤ ∗

    (if (decide (e = 0)) then P2 ∗ ⌜ eV.(type) = WeakInit ⌝ else emp) ∗

    ⌜ ainfo.2 = cas_only ∧ e ∈ M ∧ (eV.(type) = StrongInit ∨ eV.(type) = WeakInit ∨ (∃ e', eV.(type) = WeakClone e') ∨ eV.(type) = Downgrade)
    ∧ ainfo.1.1.2 ⊆ M ∧ ainfo.1.2 ∪ ulcks ⊆ Mw ⌝
    .

Definition FakeArc N γg l P1 P2 M : vProp :=
  ∃ γsa γwa γb γm γes γss γew γsw γu γd γl γul Ms Mw e eV0 eV ainfo dgds ulcks qd,
    ArcGname γg γsa γwa γb γm γes γss γew γsw γu γd γl γul ∗
    InternInv N γg l P1 P2 ∗

    OmoEview γg M ∗
    OmoEview γes Ms ∗
    OmoEview γew Mw ∗
    OmoEinfo γg 0 eV0 ∗
    OmoEinfo γg e eV ∗
    ⊒ainfo.1.1.1.2 ∗

    ⎡ghost_var γb (ainfo.1.1.1.1/2)%Qp true⎤ ∗ (* Arc is alive *)
    ⎡0 ↪[γwa] ainfo⎤ ∗
    ⎡ghost_var γul ainfo.1.1.1.1 ulcks⎤ ∗
    ⎡ghost_var γd qd dgds⎤ ∗

    ⌜ ainfo.2 = cas_only ∧ e ∈ M ∧ eV0.(type) = StrongInit ∧ (∃ e', eV.(type) = StrongDrop e' true)
    ∧ ainfo.1.1.2 ∪ dgds ⊆ M ∧ ainfo.1.2 ∪ ulcks ⊆ Mw ⌝
    .

Local Instance AllEvents_timeless γg γes γm E ess : Timeless (AllEvents γg γes γm E ess).
Proof. apply big_sepL_timeless. intros. destruct (x.(type)); apply _. Qed.
Local Instance AllEvents_persistent γg γes γm E ess : Persistent (AllEvents γg γes γm E ess).
Proof. apply big_sepL_persistent. intros. destruct (x.(type)); apply _. Qed.
Local Instance AllEvents_objective γg γes γm E ess : Objective (AllEvents γg γes γm E ess).
Proof. apply big_sepL_objective. intros. destruct (x.(type)); apply _. Qed.
Local Instance AllStrongsInner_timeless γg γes γs γss γm gen es : Timeless (AllStrongsInner γg γes γs γss γm gen es).
Proof. repeat (apply @bi.exist_timeless; intros). destruct gen; apply _. Qed.
Local Instance AllStrongsInner_persistent γg γes γs γss γm gen es : Persistent (AllStrongsInner γg γes γs γss γm gen es).
Proof. repeat (apply @bi.exist_persistent; intros). destruct gen; apply _. Qed.
Local Instance AllStrongsInner_objective γg γes γs γss γm gen es : Objective (AllStrongsInner γg γes γs γss γm gen es).
Proof. repeat (apply exists_objective; intros). destruct gen; apply _. Qed.
Local Instance AllWeaksInner_timeless γg γew γsw wdom ulcks gen ew : Timeless (AllWeaksInner γg γew γsw wdom ulcks gen ew).
Proof. repeat (apply @bi.exist_timeless; intros). destruct gen; apply _. Qed.
Local Instance AllWeaksInner_persistent γg γew γsw wdom ulcks gen ew : Persistent (AllWeaksInner γg γew γsw wdom ulcks gen ew).
Proof. repeat (apply @bi.exist_persistent; intros). destruct gen; apply _. Qed.
Local Instance AllWeaksInner_objective γg γew γsw wdom ulcks gen ew : Objective (AllWeaksInner γg γew γsw wdom ulcks gen ew).
Proof. repeat (apply exists_objective; intros). destruct gen; apply _. Qed.
Local Instance ArcInternalInvAlive_objective l γg γs γes γss γew γsw γsa γwa γb γm γu γd γl γul E omo ess esw sarc warc qsa qwa stlist P1 P2 :
  Objective (ArcInternalInvAlive l γg γs γes γss γew γsw γsa γwa γb γm γu γd γl γul E omo ess esw sarc warc qsa qwa stlist P1 P2).
Proof.
  repeat (apply exists_objective; intros). repeat (apply sep_objective; try apply _);
    [destruct x8; apply _|destruct (warc !! 0); apply _|destruct x1; apply _].
Qed.
Local Instance ArcInternalInv_objective γg l P1 P2 : Objective (ArcInternalInv γg l P1 P2).
Proof. repeat (apply exists_objective; intros). repeat (apply sep_objective; try apply _). destruct x16; apply _. Qed.

Lemma ArcGname_agree γg γsa γsa' γwa γwa' γb γb' γm γm' γes γes' γss γss' γew γew' γsw γsw' γu γu' γd γd' γl γl' γul γul' :
  ArcGname γg γsa γwa γb γm γes γss γew γsw γu γd γl γul -∗
  ArcGname γg γsa' γwa' γb' γm' γes' γss' γew' γsw' γu' γd' γl' γul' -∗
  ⌜ γsa = γsa' ∧ γwa = γwa' ∧ γb = γb' ∧ γm = γm' ∧ γes = γes' ∧ γss = γss' ∧ γew = γew' ∧ γsw = γsw' ∧ γu = γu' ∧ γd = γd' ∧ γl = γl' ∧ γul = γul' ⌝.
Proof.
  iDestruct 1 as (γnl γn) "(#Hγnl & #Hγn & %Hγn)". iDestruct 1 as (γnl' γn') "(#Hγnl' & #Hγn' & %Hγn')".
  iDestruct (OmoGname_agree with "Hγnl Hγnl'") as %<-. iDestruct (mono_list_idx_agree with "Hγn Hγn'") as %<-.
  encode_agree Hγn. subst γul'. done.
Qed.

Local Tactic Notation "gname_agree" "with" constr(Hs) :=
  iDestruct (ArcGname_agree with Hs) as %(<- & <- & <- & <- & <- & <- & <- & <- & <- & <- & <- & <-).

Lemma dom_same arcs e ainfo ainfo' (arcs' := <[ e := ainfo' ]> (delete e arcs))
    (He : arcs !! e = Some ainfo) :
  dom arcs = dom arcs'.
Proof.
  subst arcs'. rewrite dom_insert_L dom_delete_L. apply elem_of_dom_2 in He. apply set_eq. intros.
  split; intros; try set_solver. destruct (decide (x = e)) as [->|NEQ]; try set_solver.
Qed.

Lemma frac_sum_wf arcs :
  ∀ (j1 j2 : event_id) (z1 z2 : Qp * view * gset event_id * gset event_id * append_only_type) (y : Qp),
  j1 ≠ j2
  → arcs !! j1 = Some z1
    → arcs !! j2 = Some z2
      → frac_sum j1 z1 (frac_sum j2 z2 y) = frac_sum j2 z2 (frac_sum j1 z1 y).
Proof. intros. by rewrite /frac_sum Qp.add_assoc (Qp.add_comm z1.1.1.1.1 z2.1.1.1.1) -Qp.add_assoc. Qed.

(* FIXME: A lemma [map_fold_singleton] exists in the latest stdpp, but current version does not include it *)
Lemma map_fold_singleton_frac_sum b i x :
  map_fold frac_sum b {[i:=x]} = frac_sum i x b.
Proof. rewrite map_fold_insert_L; [|by apply frac_sum_wf|done]. by rewrite map_fold_empty. Qed.

Lemma map_fold_singleton_view_join_total b i x :
  map_fold view_join_total b {[i:=x]} = view_join_total i x b.
Proof. rewrite map_fold_insert_L; [|solve_lat|done]. by rewrite map_fold_empty. Qed.

Lemma map_fold_init_frac_op arcs qb1 qb2 :
  map_fold frac_sum (qb1 + qb2)%Qp arcs = (qb1 + map_fold frac_sum qb2 arcs)%Qp.
Proof.
  generalize dependent arcs. induction arcs using map_ind; [done|].
  do 2 (rewrite map_fold_insert_L; [|by apply frac_sum_wf|done]).
  by rewrite IHarcs /frac_sum /= Qp.add_assoc (Qp.add_comm (x.1.1.1.1)) -Qp.add_assoc.
Qed.

Lemma map_fold_init_frac arcs qb :
  map_fold frac_sum qb arcs = (qb/2 + map_fold frac_sum (qb/2) arcs)%Qp.
Proof.
  have EQ : (qb = qb/2 + qb/2)%Qp by rewrite Qp.add_diag Qp.mul_div_r.
  rewrite {1}EQ. apply map_fold_init_frac_op.
Qed.

Lemma EventIdValid_update E eV
    (EIDVAL : EventIdValid E)
    (NEWVAL : match eV.(type) with
              | Clone e' | WeakClone e' | WeakDrop e' _ | StrongDrop e' _ | UnwrapFail e' => e' < length E
              | _ => True
              end) :
  EventIdValid (E ++ [eV]).
Proof.
  unfold EventIdValid. intros. destruct (decide (e = length E)) as [->|NEQ].
  - rewrite lookup_app_1_eq in H. inversion H. subst eV0.
    destruct (eV.(type)); try done; rewrite app_length /=; lia.
  - rewrite lookup_app_1_ne in H; [|done]. apply EIDVAL in H.
    destruct (eV0.(type)); try done; rewrite app_length /=; lia.
Qed.

Lemma sarc_update_1 sarc e ainfo ainfo' qsa E warc st (sarc' := <[e:=ainfo']> (delete e sarc))
    (He : sarc !! e = Some ainfo)
    (Hq : ainfo'.1.1.1.1 = ainfo.1.1.1.1)
    (Hv : ainfo.1.1.1.2 ⊑ ainfo'.1.1.1.2)
    (HM : ainfo.1.1.2 ⊆ ainfo'.1.1.2)
    (HMw : ainfo.1.2 ⊆ ainfo'.1.2)
    (Hqsa : map_fold frac_sum qsa sarc = 1%Qp)
    (VALsarc : ArcsValid E (dom sarc))
    (VALsarcwarc : ArcsValid2 E (dom sarc) (dom warc))
    (HSeenClone : SeenClone E sarc)
    (HDOM : dom sarc = st.1.1.1) :
  map_fold frac_sum qsa sarc' = 1%Qp ∧ ArcsValid E (dom sarc') ∧ ArcsValid2 E (dom sarc') (dom warc) ∧ SeenClone E sarc' ∧ dom sarc' = st.1.1.1.
Proof.
  subst sarc'. apply (dom_same _ _ _ ainfo') in He as EQdom. rewrite -EQdom. split_and!; try done.
  - rewrite map_fold_insert_L; [|by apply frac_sum_wf|by apply lookup_delete].
    have EQ : frac_sum e ainfo' (map_fold frac_sum qsa (delete e sarc)) = frac_sum e ainfo (map_fold frac_sum qsa (delete e sarc)).
    { by rewrite /frac_sum Hq. }
    rewrite EQ. clear EQ. rewrite -map_fold_delete_L; [done|..|done].
    intros. by rewrite /frac_sum Qp.add_assoc (Qp.add_comm z1.1.1.1.1 z2.1.1.1.1) -Qp.add_assoc.
  - unfold SeenClone. intros. destruct (decide (e0 = e)) as [->|NEQ].
    + specialize (HSeenClone _ _ _ _ He H0 H1). rewrite lookup_insert in H. inversion H. set_solver.
    + eapply HSeenClone; try done. rewrite lookup_insert_ne in H; [|done]. rewrite lookup_delete_ne in H; [|done]. done.
Qed.

Lemma warc_update_1 warc e ainfo ainfo' qwa E sarc st (warc' := <[e:=ainfo']> (delete e warc))
    (He : warc !! e = Some ainfo)
    (Hq : ainfo'.1.1.1.1 = ainfo.1.1.1.1)
    (Hv : ainfo.1.1.1.2 ⊑ ainfo'.1.1.1.2)
    (HM : ainfo.1.1.2 ⊆ ainfo'.1.1.2)
    (HMw : ainfo.1.2 ⊆ ainfo'.1.2)
    (Hqwa : map_fold frac_sum qwa warc = 1%Qp)
    (VALwarc : ArcsValid E (dom warc))
    (VALsarcwarc : ArcsValid2 E (dom sarc) (dom warc))
    (HSeenWeakClone : SeenWeakClone E warc)
    (HDOM : dom warc = st.2.1.1) :
  map_fold frac_sum qwa warc' = 1%Qp ∧ ArcsValid E (dom warc') ∧ ArcsValid2 E (dom sarc) (dom warc')
  ∧ SeenWeakClone E warc' ∧ dom warc' = st.2.1.1.
Proof.
  subst warc'. apply (dom_same _ _ _ ainfo') in He as EQdom. rewrite -EQdom. split_and!; try done.
  - rewrite map_fold_insert_L; [|by apply frac_sum_wf|by apply lookup_delete].
    have EQ : frac_sum e ainfo' (map_fold frac_sum qwa (delete e warc)) = frac_sum e ainfo (map_fold frac_sum qwa (delete e warc)).
    { by rewrite /frac_sum Hq. }
    rewrite EQ. clear EQ. rewrite -map_fold_delete_L; [done|..|done].
    intros. by rewrite /frac_sum Qp.add_assoc (Qp.add_comm z1.1.1.1.1 z2.1.1.1.1) -Qp.add_assoc.
  - unfold SeenWeakClone. intros. destruct (decide (e0 = e)) as [->|NEQ].
    + specialize (HSeenWeakClone _ _ _ _ He H0 H1). rewrite lookup_insert in H. inversion H. set_solver.
    + eapply HSeenWeakClone; try done. rewrite lookup_insert_ne in H; [|done]. rewrite lookup_delete_ne in H; [|done]. done.
Qed.

Lemma sarc_update_snoc_1 sarc e ainfo ainfo' qsa E eV warc st (sarc' := <[e:=ainfo']> (delete e sarc)) (E' := E ++ [eV])
    (He : sarc !! e = Some ainfo)
    (Hq : ainfo'.1.1.1.1 = ainfo.1.1.1.1)
    (Hv : ainfo.1.1.1.2 ⊑ ainfo'.1.1.1.2)
    (HM : ainfo.1.1.2 ⊆ ainfo'.1.1.2)
    (HMw : ainfo.1.2 ⊆ ainfo'.1.2)
    (Hqsa : map_fold frac_sum qsa sarc = 1%Qp)
    (VALsarc : ArcsValid E (dom sarc))
    (VALwarc : ArcsValid E (dom warc))
    (VALsarcwarc : ArcsValid2 E (dom sarc) (dom warc))
    (HSeenClone : SeenClone E sarc)
    (HSeenWeakClone : SeenWeakClone E warc)
    (HDOM : dom sarc = st.1.1.1)
    (HeV : match eV.(type) with
           | Clone e' => e = e' ∧ length E ∈ ainfo'.1.1.2
           | WeakClone _ => False
           | StrongDrop e' _ => e' ∉ dom sarc
           | WeakDrop e' _ => e' ∉ dom warc
           | _ => True
           end) :
  map_fold frac_sum qsa sarc' = 1%Qp ∧ ArcsValid E' (dom sarc') ∧ ArcsValid E' (dom warc)
  ∧ ArcsValid2 E' (dom sarc') (dom warc) ∧ SeenClone E' sarc' ∧ SeenWeakClone E' warc ∧ dom sarc' = st.1.1.1.
Proof.
  subst sarc' E'. apply (dom_same _ _ _ ainfo') in He as EQdom. rewrite -EQdom. split_and!; try done.
  - rewrite map_fold_insert_L; [|by apply frac_sum_wf|by apply lookup_delete].
    have EQ : frac_sum e ainfo' (map_fold frac_sum qsa (delete e sarc)) = frac_sum e ainfo (map_fold frac_sum qsa (delete e sarc)).
    { by rewrite /frac_sum Hq. }
    rewrite EQ. clear EQ. rewrite -map_fold_delete_L; [done|..|done].
    intros. by rewrite /frac_sum Qp.add_assoc (Qp.add_comm z1.1.1.1.1 z2.1.1.1.1) -Qp.add_assoc.
  - unfold ArcsValid. intros. apply VALsarc in H. rewrite app_length /=. lia.
  - unfold ArcsValid. intros. apply VALwarc in H. rewrite app_length /=. lia.
  - unfold ArcsValid2. intros. destruct (decide (e0 = length E)) as [->|NEQ].
    + rewrite lookup_app_1_eq in H. inversion H. subst eV0. destruct (eV.(type)); try done.
    + rewrite lookup_app_1_ne in H; [|done]. apply VALsarcwarc in H. done.
  - unfold SeenClone. intros. destruct (decide (e' = length E)) as [->|NEQ].
    + rewrite lookup_app_1_eq in H0. inversion H0. subst eV0.
      rewrite H1 in HeV. destruct HeV as [<- eIN]. rewrite lookup_insert in H. inversion H. subst ainfo0. done.
    + rewrite lookup_app_1_ne in H0; [|done]. destruct (decide (e0 = e)) as [->|NEQ'].
      * specialize (HSeenClone _ _ _ _ He H0 H1). rewrite lookup_insert in H. inversion H. set_solver.
      * eapply HSeenClone; try done. rewrite lookup_insert_ne in H; [|done]. rewrite lookup_delete_ne in H; [|done]. done.
  - unfold SeenWeakClone. intros. destruct (decide (e' = length E)) as [->|NEQ].
    + rewrite lookup_app_1_eq in H0. inversion H0. subst eV0. rewrite H1 in HeV. done.
    + rewrite lookup_app_1_ne in H0; [|done]. eapply HSeenWeakClone; try done.
Qed.

Lemma warc_update_snoc_1 warc e ainfo ainfo' qwa E eV sarc sarc' st (warc' := <[e:=ainfo']> (delete e warc)) (E' := E ++ [eV])
    (He : warc !! e = Some ainfo)
    (Hq : ainfo'.1.1.1.1 = ainfo.1.1.1.1)
    (Hv : ainfo.1.1.1.2 ⊑ ainfo'.1.1.1.2)
    (HM : ainfo.1.1.2 ⊆ ainfo'.1.1.2)
    (HMw : ainfo.1.2 ⊆ ainfo'.1.2)
    (Hqsa : map_fold frac_sum qwa warc = 1%Qp)
    (VALsarc : ArcsValid E (dom sarc))
    (VALwarc : ArcsValid E (dom warc))
    (VALsarcwarc : ArcsValid2 E (dom sarc) (dom warc))
    (HSeenClone : SeenClone E sarc)
    (HSeenWeakClone : SeenWeakClone E warc)
    (HDOM : dom warc = st.2.1.1)
    (Subsarc : sarc' ⊆ sarc)
    (HeV : match eV.(type) with
           | Clone _ => False
           | WeakClone e' => e = e' ∧ length E ∈ ainfo'.1.1.2
           | StrongDrop e' _ => e' ∉ dom sarc'
           | WeakDrop e' _ => e' ∉ dom warc
           | _ => True
           end) :
  map_fold frac_sum qwa warc' = 1%Qp ∧ ArcsValid E' (dom sarc') ∧ ArcsValid E' (dom warc')
  ∧ ArcsValid2 E' (dom sarc') (dom warc') ∧ SeenClone E' sarc' ∧ SeenWeakClone E' warc' ∧ dom warc' = st.2.1.1.
Proof.
  apply subseteq_dom in Subsarc as DSubarc.
  subst warc' E'. apply (dom_same _ _ _ ainfo') in He as EQdom. rewrite -EQdom. split_and!; try done.
  - rewrite map_fold_insert_L; [|by apply frac_sum_wf|by apply lookup_delete].
    have EQ : frac_sum e ainfo' (map_fold frac_sum qwa (delete e warc)) = frac_sum e ainfo (map_fold frac_sum qwa (delete e warc)).
    { by rewrite /frac_sum Hq. }
    rewrite EQ. clear EQ. rewrite -map_fold_delete_L; [done|..|done].
    intros. by rewrite /frac_sum Qp.add_assoc (Qp.add_comm z1.1.1.1.1 z2.1.1.1.1) -Qp.add_assoc.
  - unfold ArcsValid. intros. have H' : e0 ∈ dom sarc by set_solver. apply VALsarc in H'. rewrite app_length /=. lia.
  - unfold ArcsValid. intros. apply VALwarc in H. rewrite app_length /=. lia.
  - unfold ArcsValid2. intros. destruct (decide (e0 = length E)) as [->|NEQ].
    + rewrite lookup_app_1_eq in H. inversion H. subst eV0. destruct (eV.(type)); try done.
    + rewrite lookup_app_1_ne in H; [|done]. apply VALsarcwarc in H. destruct (eV0.(type)); try done; try set_solver.
  - unfold SeenClone. intros. destruct (decide (e' = length E)) as [->|NEQ].
    + rewrite lookup_app_1_eq in H0. inversion H0. subst eV0. by rewrite H1 in HeV.
    + rewrite lookup_app_1_ne in H0; [|done]. eapply lookup_weaken in H; [|done]. eapply HSeenClone; try done.
  - unfold SeenWeakClone. intros. destruct (decide (e' = length E)) as [->|NEQ].
    + rewrite lookup_app_1_eq in H0. inversion H0. subst eV0. rewrite H1 in HeV.
      destruct HeV as [<- IN]. rewrite lookup_insert in H. inversion H. subst ainfo0. set_solver.
    + rewrite lookup_app_1_ne in H0; [|done]. destruct (decide (e0 = e)) as [->|NEQ'].
      * rewrite lookup_insert in H. inversion H. subst ainfo0. set_solver.
      * rewrite lookup_insert_ne in H; [|done]. rewrite lookup_delete_ne in H; [|done]. eapply HSeenWeakClone; try done.
Qed.

Lemma sarc_update_2 sarc e ainfo ainfo' V Vp E dgds lcks lcks' ulcks (sarc' := <[e:=ainfo']> (delete e sarc))
    (He : sarc !! e = Some ainfo)
    (Hv : ainfo'.1.1.1.2 = ainfo.1.1.1.2 ⊔ V)
    (HM : ainfo.1.1.2 ⊆ ainfo'.1.1.2)
    (HMw : ainfo.1.2 ⊆ ainfo'.1.2)
    (Sublcks : lcks ⊆ lcks')
    (HSeenDowngrade : SeenDowngrade E sarc dgds)
    (HSeenUnlock : SeenUnlock sarc lcks ulcks)
    (LEsarc : ArcsSeen sarc Vp) :
  map_fold view_join_total Vp sarc' = map_fold view_join_total Vp sarc ⊔ V ∧ SeenDowngrade E sarc' dgds
  ∧ SeenUnlock sarc' lcks' ulcks ∧ ArcsSeen sarc' Vp.
Proof.
  subst sarc'. split_and!.
  - rewrite map_fold_insert_L; [|solve_lat|apply lookup_delete].
    have EQ : view_join_total e ainfo' (map_fold view_join_total Vp (delete e sarc)) =
          (view_join_total e ainfo (map_fold view_join_total Vp (delete e sarc))) ⊔ V.
    { rewrite /view_join_total Hv /=. solve_lat. }
    rewrite EQ. clear EQ. rewrite -map_fold_delete_L; [|solve_lat|done]. solve_lat.
  - unfold SeenDowngrade. intros. apply HSeenDowngrade in H. destruct (eV.(type)); try done.
    destruct H as [H|H]; [by left|]. right. destruct H as (e' & ainfo'' & He' & IN). destruct (decide (e' = e)) as [->|NEQ].
    + rewrite He in He'. inversion He'. subst ainfo''. exists e,ainfo'. split; [|set_solver].
      rewrite lookup_insert. done.
    + exists e',ainfo''. split; [|done]. rewrite lookup_insert_ne; [|done]. rewrite lookup_delete_ne; [|done]. done.
  - unfold SeenUnlock. intros. apply HSeenUnlock in H. destruct H as [H|H]; [by left;set_solver|].
    destruct H as (e' & ainfo'' & He' & IN). right. destruct (decide (e' = e)) as [->|NEQ].
    + rewrite He in He'. inversion He'. subst ainfo''.
      exists e,ainfo'. rewrite lookup_insert. split; [done|]. set_solver.
    + exists e',ainfo''. rewrite lookup_insert_ne; [|done]. rewrite lookup_delete_ne; [|done]. done.
  - unfold ArcsSeen. intros. destruct (decide (e0 = e)) as [->|NEQ].
    + rewrite lookup_insert in H. inversion H. subst ainfo0.
      apply LEsarc in He. rewrite Hv. solve_lat.
    + rewrite lookup_insert_ne in H; [|done]. rewrite lookup_delete_ne in H; [|done].
      apply LEsarc in H. done.
Qed.

Lemma warc_update_2 warc e ainfo ainfo' V Vp E upds (warc' := <[e:=ainfo']> (delete e warc))
    (He : warc !! e = Some ainfo)
    (Hv : ainfo'.1.1.1.2 = ainfo.1.1.1.2 ⊔ V)
    (HM : ainfo.1.1.2 ⊆ ainfo'.1.1.2)
    (HSeenUpgrade : SeenUpgrade E warc upds)
    (LEwarc : ArcsSeen warc Vp) :
  map_fold view_join_total Vp warc' = map_fold view_join_total Vp warc ⊔ V ∧ SeenUpgrade E warc' upds ∧ ArcsSeen warc' Vp.
Proof.
  subst warc'. split_and!.
  - rewrite map_fold_insert_L; [|solve_lat|apply lookup_delete].
    have EQ : view_join_total e ainfo' (map_fold view_join_total Vp (delete e warc)) =
          (view_join_total e ainfo (map_fold view_join_total Vp (delete e warc))) ⊔ V.
    { rewrite /view_join_total Hv /=. solve_lat. }
    rewrite EQ. clear EQ. rewrite -map_fold_delete_L; [|solve_lat|done]. solve_lat.
  - unfold SeenUpgrade. intros. apply HSeenUpgrade in H. destruct (eV.(type)); try done.
    destruct H as [H|H]; [by left|]. right. destruct H as (e' & ainfo'' & He' & IN). destruct (decide (e' = e)) as [->|NEQ].
    + rewrite He in He'. inversion He'. subst ainfo''. exists e,ainfo'. split; [|set_solver].
      rewrite lookup_insert. done.
    + exists e',ainfo''. split; [|done]. rewrite lookup_insert_ne; [|done]. rewrite lookup_delete_ne; [|done]. done.
  - unfold ArcsSeen. intros. destruct (decide (e0 = e)) as [->|NEQ].
    + rewrite lookup_insert in H. inversion H. subst ainfo0.
      apply LEwarc in He. rewrite Hv. solve_lat.
    + rewrite lookup_insert_ne in H; [|done]. rewrite lookup_delete_ne in H; [|done].
      apply LEwarc in H. done.
Qed.

Lemma sarc_update_snoc_2 sarc e ainfo ainfo' V Vp E eV warc upds dgds dgds' lcks ulcks
    (sarc' := <[e:=ainfo']> (delete e sarc))
    (E' := E ++ [eV])
    (He : sarc !! e = Some ainfo)
    (Hv : ainfo'.1.1.1.2 = ainfo.1.1.1.2 ⊔ V)
    (HM : ainfo.1.1.2 ⊆ ainfo'.1.1.2)
    (HMw : ainfo.1.2 ⊆ ainfo'.1.2)
    (HSeenUpgrade : SeenUpgrade E warc upds)
    (HSeenDowngrade : SeenDowngrade E sarc dgds)
    (HSeenUnlock : SeenUnlock sarc lcks ulcks)
    (LEsarc : ArcsSeen sarc Vp)
    (Subdgds : dgds ⊆ dgds')
    (HeV : match eV.(type) with
           | Upgrade => False
           | Downgrade => length E ∈ dgds' ∨ length E ∈ ainfo'.1.1.2
           | _ => True
           end) :
  map_fold view_join_total Vp sarc' = map_fold view_join_total Vp sarc ⊔ V
  ∧ SeenUpgrade E' warc upds ∧ SeenDowngrade E' sarc' dgds' ∧ SeenUnlock sarc' lcks ulcks ∧ ArcsSeen sarc' Vp.
Proof.
  subst sarc' E'. split_and!.
  - rewrite map_fold_insert_L; [|solve_lat|apply lookup_delete].
    have EQ : view_join_total e ainfo' (map_fold view_join_total Vp (delete e sarc)) =
          (view_join_total e ainfo (map_fold view_join_total Vp (delete e sarc))) ⊔ V.
    { rewrite /view_join_total Hv /=. solve_lat. }
    rewrite EQ. clear EQ. rewrite -map_fold_delete_L; [|solve_lat|done]. solve_lat.
  - unfold SeenUpgrade. intros. destruct (decide (e0 = length E)) as [->|NEQ].
    + rewrite lookup_app_1_eq in H. inversion H. subst eV0. destruct (eV.(type)); try done.
    + rewrite lookup_app_1_ne in H; [|done]. apply HSeenUpgrade in H. done.
  - unfold SeenDowngrade. intros. destruct (decide (e0 = length E)) as [->|NEQ].
    + rewrite lookup_app_1_eq in H. inversion H. subst eV0. destruct (eV.(type)); try done.
      destruct HeV as [IN|IN]; [by left|]. right. exists e,ainfo'. rewrite lookup_insert. done.
    + rewrite lookup_app_1_ne in H; [|done]. apply HSeenDowngrade in H. destruct (eV0.(type)); try done.
      destruct H as [IN|IN]; [by left; set_solver|]. right.
      destruct IN as (e' & ainfo'' & He' & IN). destruct (decide (e' = e)) as [->|NEQ'].
      * rewrite He in He'. inversion He'. subst ainfo''.
        exists e,ainfo'. rewrite lookup_insert. split; [done|]. set_solver.
      * exists e',ainfo''. rewrite lookup_insert_ne; [|done]. rewrite lookup_delete_ne; [|done]. done.
  - unfold SeenUnlock. intros. apply HSeenUnlock in H. destruct H as [H|H]; [by left|]. right.
    destruct H as (e' & ainfo'' & He' & IN). destruct (decide (e' = e)) as [->|NEQ].
    + rewrite He in He'. inversion He'. subst ainfo''.
      exists e,ainfo'. rewrite lookup_insert. split; [done|]. set_solver.
    + exists e',ainfo''. rewrite lookup_insert_ne; [|done]. rewrite lookup_delete_ne; [|done]. done.
  - unfold ArcsSeen. intros. destruct (decide (e0 = e)) as [->|NEQ].
    + rewrite lookup_insert in H. inversion H. subst ainfo0.
      apply LEsarc in He. rewrite Hv. solve_lat.
    + rewrite lookup_insert_ne in H; [|done]. rewrite lookup_delete_ne in H; [|done].
      apply LEsarc in H. done.
Qed.

Lemma strong_arc_persist e eidx eV E omo stlist sdom wdom
    (OMO_GOOD : Linearizability_omo E omo stlist)
    (Heidx : lookup_omo omo eidx = Some e)
    (He : E !! e = Some eV)
    (HeV : (eV.(type) = StrongInit ∨ (∃ e', eV.(type) = Clone e') ∨ eV.(type) = Upgrade))
    (eINdom : e ∈ sdom)
    (VALsarcwarc : ArcsValid2 E sdom wdom) :
  ∀ i st, stlist !! i = Some st → gen_of eidx ≤ i → e ∈ st.1.1.1.
Proof.
  eapply omo_stlist_length in OMO_GOOD as EQlenST.
  destruct eidx.
  { (* [e] cannot be a read-only event since it should be either [StrongInit], [Clone], or [Upgrade] *)
    have [st Hst] : is_Some (stlist !! gen).
    { rewrite lookup_lt_is_Some -EQlenST. apply lookup_omo_lt_Some in Heidx. simpl in Heidx. done. }
    eapply omo_read_op_step in OMO_GOOD as STEP; [|exact Heidx|done|done].
    exfalso. inversion STEP; rewrite EVENT in HeV; des; try done;
    destruct st as [[[? ?] ?] [? ?]]; simpl in *; inversion NST; clear -FRESH H4; set_solver. }

  intros i st Hst LEi. generalize dependent st. induction LEi as [|i]; intros.
  - rewrite lookup_omo_wr_event in Heidx. destruct gen.
    + eapply omo_write_op_init_step in OMO_GOOD as STEP; [|exact Heidx|done|done].
      inversion STEP; rewrite EVENT in HeV; des; try done.
    + have [st' Hst'] : is_Some (stlist !! gen).
      { rewrite lookup_lt_is_Some. apply lookup_lt_Some in Hst. simpl in Hst. lia. }
      replace (S gen) with (gen + 1) in Hst, Heidx by lia.
      eapply omo_write_op_step in OMO_GOOD as STEP; try done.
      inversion STEP; rewrite EVENT in HeV; des; try done; subst st; set_solver-.
  - have [st' Hst'] : is_Some (stlist !! i).
    { rewrite lookup_lt_is_Some. apply lookup_lt_Some in Hst. lia. }
    apply IHLEi in Hst' as eIN.
    have [e' He'] : is_Some (omo_write_op omo !! (S i)).
    { rewrite lookup_lt_is_Some -omo_write_op_length EQlenST. apply lookup_lt_Some in Hst. done. }
    rewrite -lookup_omo_wr_event in He'. eapply lookup_omo_event_valid in He' as HeV'; [|done].
    rewrite lookup_omo_wr_event in He'. destruct HeV' as [eV' HeV'].
    replace (S i) with (i + 1) in He', Hst by lia.
    eapply omo_write_op_step in OMO_GOOD as STEP; try done. inversion STEP; try (subst; set_solver +eIN).
    + apply VALsarcwarc in HeV'. rewrite EVENT in HeV'.
      have NEQ' : e ≠ e'0 by set_solver +eINdom HeV'. subst st. set_solver +eIN NEQ'.
    + apply VALsarcwarc in HeV'. rewrite EVENT in HeV'.
      have NEQ' : e ≠ e'0 by set_solver +eINdom HeV'. rewrite STRONG in eIN. set_solver +eIN NEQ'.
Qed.

Lemma weak_arc_persist e eidx eV E omo stlist sdom wdom
    (OMO_GOOD : Linearizability_omo E omo stlist)
    (Heidx : lookup_omo omo eidx = Some e)
    (He : E !! e = Some eV)
    (HeV : (eV.(type) = StrongInit ∨ eV.(type) = WeakInit ∨ (∃ e', eV.(type) = WeakClone e') ∨ eV.(type) = Downgrade))
    (eINdom : e ∈ wdom)
    (VALsarcwarc : ArcsValid2 E sdom wdom) :
  ∀ i st, stlist !! i = Some st → gen_of eidx ≤ i → e ∈ st.2.1.1.
Proof.
  eapply omo_stlist_length in OMO_GOOD as EQlenST.
  destruct eidx.
  { (* [e] cannot be a read-only event since it should be either [WeakInit], [WeakClone], or [Downgrade] *)
    have [st Hst] : is_Some (stlist !! gen).
    { rewrite lookup_lt_is_Some -EQlenST. apply lookup_omo_lt_Some in Heidx. simpl in Heidx. done. }
    eapply omo_read_op_step in OMO_GOOD as STEP; [|exact Heidx|done|done].
    exfalso. inversion STEP; rewrite EVENT in HeV; des; try done;
    destruct st as [? [[? ?] ?]]; simpl in *; inversion NST; set_solver +FRESH H4. }

  intros i st Hst LEi. generalize dependent st. induction LEi as [|i]; intros.
  - rewrite lookup_omo_wr_event in Heidx. destruct gen.
    + eapply omo_write_op_init_step in OMO_GOOD as STEP; [|exact Heidx|done|done].
      inversion STEP; rewrite EVENT in HeV; des; try done.
    + have [st' Hst'] : is_Some (stlist !! gen).
      { rewrite lookup_lt_is_Some. apply lookup_lt_Some in Hst. simpl in Hst. lia. }
      replace (S gen) with (gen + 1) in Hst, Heidx by lia.
      eapply omo_write_op_step in OMO_GOOD as STEP; try done.
      inversion STEP; rewrite EVENT in HeV; des; try done; subst st; set_solver-.
  - have [st' Hst'] : is_Some (stlist !! i).
    { rewrite lookup_lt_is_Some. apply lookup_lt_Some in Hst. lia. }
    apply IHLEi in Hst' as eIN.
    have [e' He'] : is_Some (omo_write_op omo !! (S i)).
    { rewrite lookup_lt_is_Some -omo_write_op_length EQlenST. apply lookup_lt_Some in Hst. done. }
    rewrite -lookup_omo_wr_event in He'. eapply lookup_omo_event_valid in He' as HeV'; [|done].
    rewrite lookup_omo_wr_event in He'. destruct HeV' as [eV' HeV'].
    replace (S i) with (i + 1) in He', Hst by lia.
    eapply omo_write_op_step in OMO_GOOD as STEP; try done. inversion STEP; try (subst; set_solver +eIN).
    + apply VALsarcwarc in HeV'. rewrite EVENT in HeV'.
      have NEQ' : e ≠ e'0 by set_solver +eINdom HeV'. subst st. set_solver +eIN NEQ'.
    + apply VALsarcwarc in HeV'. rewrite EVENT in HeV'.
      have NEQ' : e ≠ e'0 by set_solver +eINdom HeV'. rewrite WEAK in eIN. set_solver +eIN NEQ'.
Qed.

Lemma weak_state_valid E omo stlist i st
    (OMO_GOOD : Linearizability_omo E omo stlist)
    (Hst : stlist !! i = Some st) :
  ∀ e, e ∈ st.2.1.1 → e < length E.
Proof.
  apply omo_stlist_length in OMO_GOOD as EQlenST.
  generalize dependent st. induction i; intros.
  - have [ew Hew] : is_Some (omo_write_op omo !! 0).
    { rewrite lookup_lt_is_Some -omo_write_op_length EQlenST. apply lookup_lt_Some in Hst. done. }
    rewrite -lookup_omo_wr_event in Hew.
    eapply lookup_omo_event_valid in Hew as HeVw; [|done]. destruct HeVw as [eVw HeVw].
    rewrite lookup_omo_wr_event in Hew.
    eapply omo_write_op_init_step in OMO_GOOD as STEP; try done. apply lookup_lt_Some in HeVw.
    inversion STEP; subst st; simpl in *; try done; (have EQ : e = ew by set_solver); subst e; done.
  - have [st' Hst'] : is_Some (stlist !! i).
    { rewrite lookup_lt_is_Some. apply lookup_lt_Some in Hst. lia. }
    have [ew Hew] : is_Some (omo_write_op omo !! (S i)).
    { rewrite lookup_lt_is_Some -omo_write_op_length EQlenST. apply lookup_lt_Some in Hst. done. }
    rewrite -lookup_omo_wr_event in Hew.
    eapply lookup_omo_event_valid in Hew as HeVw; [|done]. destruct HeVw as [eVw HeVw].
    rewrite lookup_omo_wr_event in Hew. replace (S i) with (i + 1) in Hew,Hst by lia.
    eapply omo_write_op_step in OMO_GOOD as STEP; try done. apply lookup_lt_Some in HeVw as LTew.
    specialize (IHi _ Hst').

    inversion STEP; subst; simpl in *; try (by apply IHi);
    try ((have [CASE|CASE] : e ∈ st'.2.1.1 ∨ e = ew by set_solver); [by apply IHi|by subst e]).
    + rewrite elem_of_singleton in H. subst e. done.
    + rewrite elem_of_singleton in H. subst e. done.
Qed.

Lemma OmoSnap_update γg γs γs' q E omo stlist pst nst stlist' eV e gen st eidx' (E' := E ++ [eV]) (omo' := omo_insert_w omo (gen + 1) (length E) []) (stlist'' := take (gen + 1) stlist ++ nst :: stlist') :
  e ≠ length E →
  gen < length omo →
  (∀ i stp stn, stlist !! (gen + 1 + i) = Some stp → stlist' !! i = Some stn → stn.1 = stp.1) →
  lookup_omo omo' eidx' = Some e →
  interp_omo E' ((length E, []) :: drop (gen + 1) omo) pst (nst :: stlist') →
  length omo = length stlist →
  OmoAuth γg γs' q E' omo' stlist'' _ -∗
  OmoSnap γg γs e st -∗
  OmoSnapStates γg γs omo stlist -∗
  ∃ st', OmoSnap γg γs' e st' ∗ ⌜ st.1 = st'.1 ⌝.
Proof.
  iIntros "%NEe %LTgen %Hstlist' %Heidx' %Hgengood %EQlenST M● #e↪st #ST◯".
  iDestruct (OmoAuth_wf with "M●") as %[OMO_GOOD _].
  apply interp_omo_length in Hgengood as EQlenST'.
  have EQlen1 : length (take (gen + 1) (omo_write_op omo)) = gen + 1.
  { rewrite take_length Nat.min_l; [done|]. rewrite -omo_write_op_length. lia. }

  destruct (decide (eidx' = wr_event (gen + 1))) as [->|NEQ].
  { subst omo'. rewrite lookup_omo_wr_event omo_insert_w_write_op lookup_app_r in Heidx'; [|lia].
    rewrite EQlen1 in Heidx'. replace (gen + 1 - (gen + 1)) with 0 in Heidx' by lia. by inversion Heidx'. }

  eapply lookup_omo_before_insert_w in Heidx' as Heidx; [|done|lia].
  destruct Heidx as [eidx [Heidx CASE]].

  iDestruct (OmoSnapStates_OmoSnap with "ST◯ e↪st") as %Hst; [done|].
  have EQlenSgen1 : length (take (gen + 1) stlist) = gen + 1.
  { rewrite take_length Nat.min_l; [done|]. rewrite -EQlenST. apply lookup_omo_lt_Some in Heidx. lia. }

  destruct (le_lt_dec (gen + 1) (gen_of eidx')) as [LE|LT].
  - rewrite decide_False in CASE; [|lia].
    destruct CASE as (LTSgen & EQgen' & EQeidx).
    replace (gen_of eidx) with (gen + 1 + (gen_of eidx - 1 - gen)) in Hst by lia.
    have [st' Hst'] : is_Some (stlist' !! (gen_of eidx - 1 - gen)).
    { rewrite lookup_lt_is_Some. inversion EQlenST'.
      rewrite drop_length. apply lookup_omo_lt_Some in Heidx. lia. }
    specialize (Hstlist' _ _ _ Hst Hst').
    iDestruct (OmoSnap_get _ _ _ _ _ _ _ eidx' (gen_of eidx') with "M●") as "#e↪st'"; [|done|done|].
    { rewrite lookup_app_r; [|lia]. rewrite EQlenSgen1 lookup_cons.
      replace (gen_of eidx' - (gen + 1)) with (S (gen_of eidx - 1 - gen)) by lia. done. }
    iExists st'. iFrame "e↪st'". rewrite Hstlist'. done.
  - rewrite decide_True in CASE; [|done]. subst eidx'.
    iDestruct (OmoSnap_get _ _ _ _ _ _ _ eidx (gen_of eidx) with "M●") as "#e↪st'"; [|done|done|].
    { rewrite lookup_app_l; [|lia]. rewrite lookup_take_Some. done. }
    iExists st. iFrame "e↪st'". done.
Qed.

Lemma weak_arc_insert_gen_good E omo stlist eVop gen st (E' := E ++ [eVop]) (opId := length E) (nst := (st.1, (st.2.1.1 ∪ {[opId]}, st.2.1.2, st.2.2)))
    (OMO_GOOD : Linearizability_omo E omo stlist)
    (Hst : stlist !! gen = Some st)
    (STEP : step opId eVop st nst)
    (HInitWrite : omo_write_op omo !! 0 = Some 0)
    (HAlive : ArcAlive E) :
  ∃ stlist', interp_omo E' ((opId, []) :: drop (gen + 1) omo) st (nst :: stlist')
      ∧ (∀ i stp stn, stlist !! (gen + 1 + i)%nat = Some stp → stlist' !! i = Some stn → stn = (stp.1, (stp.2.1.1 ∪ {[opId]}, stp.2.1.2, stp.2.2))).
Proof.
  apply omo_stlist_length in OMO_GOOD as EQlenST.

  have H : ∀ len, ∃ stlist', interp_omo E' ((opId, []) :: take len (drop (gen + 1) omo)) st (nst :: stlist')
      ∧ (∀ i stp stn, stlist !! (gen + 1 + i)%nat = Some stp → stlist' !! i = Some stn → stn = (stp.1, (stp.2.1.1 ∪ {[opId]}, stp.2.1.2, stp.2.2))); last first.
  { specialize (H (length (drop (gen + 1) omo))). rewrite take_ge in H; [|done]. done. }

  intros. induction len.
  - exists []. split; [|done].
    rewrite take_0 -(app_nil_l [(opId, [])]) -(app_nil_l [nst]).
    apply (interp_omo_snoc _ _ _ eVop _ _ st). split_and!; try done; [by rewrite lookup_app_1_eq|by apply interp_omo_nil].
  - destruct IHlen as (stlist' & GEN_GOOD & Hstlist').
    destruct (le_lt_dec (length (drop (gen + 1) omo)) len) as [LE|LT].
    { rewrite take_ge in GEN_GOOD; [|done]. rewrite take_ge; [|lia]. by exists stlist'. }
    rewrite -lookup_lt_is_Some in LT. destruct LT as [[e' es'] Hlen].
    erewrite take_S_r; [|done].

    have [stlen Hstlen] : is_Some (stlist !! ((gen + len) + 1)).
    { rewrite lookup_lt_is_Some -EQlenST. apply lookup_lt_Some in Hlen. rewrite drop_length in Hlen. lia. }
    set nstlen := (stlen.1, (stlen.2.1.1 ∪ {[opId]}, stlen.2.1.2, stlen.2.2)).

    have [stlen' Hstlen'] : is_Some (stlist !! (gen + len)).
    { rewrite lookup_lt_is_Some. apply lookup_lt_Some in Hstlen. lia. }
    set nstlen' : arc_state := (stlen'.1, (stlen'.2.1.1 ∪ {[opId]}, stlen'.2.1.2, stlen'.2.2)).

    apply interp_omo_length in GEN_GOOD as EQlenST'. simpl in EQlenST'.
    inversion EQlenST'. rename H0 into EQlenST''.
    rewrite take_length Nat.min_l in EQlenST''; [|by apply lookup_lt_Some in Hlen; lia].

    have Hst' : last (nst :: stlist') = Some nstlen'.
    { destruct len.
      - destruct stlist'; [|done]. simpl. rewrite Nat.add_0_r Hst in Hstlen'. inversion Hstlen'. subst stlen'. done.
      - have [st' Hst'] : is_Some (stlist' !! len) by rewrite lookup_lt_is_Some; lia.
        replace (gen + S len) with (gen + 1 + len) in Hstlen' by lia.
        specialize (Hstlist' _ _ _ Hstlen' Hst').
        rewrite last_cons last_lookup- EQlenST'' /= Hst' Hstlist'. done. }

    have He' : lookup_omo omo (wr_event (gen + 1 + len)) = Some e'.
    { rewrite lookup_drop in Hlen. by rewrite lookup_omo_wr_event /omo_write_op list_lookup_fmap Hlen. }
    have [eV' HeV'] : is_Some (E !! e') by eapply lookup_omo_event_valid.
    apply lookup_lt_Some in HeV' as LTe'.

    exists (stlist' ++ [nstlen]). split.
    + replace ((opId, []) :: take len (drop (gen + 1) omo) ++ [(e', es')]) with
        (((opId, []) :: take len (drop (gen + 1) omo)) ++ [(e', es')]); [|by clear; simplify_list_eq].
      replace (nst :: stlist' ++ [nstlen]) with ((nst :: stlist') ++ [nstlen]); [|by clear; simplify_list_eq].
      eapply interp_omo_snoc. split_and!; try done.
      * rewrite lookup_app_l; [done|]. done.
      * rewrite lookup_omo_wr_event in He'. replace (gen + 1 + len) with ((gen + len) + 1) in He' by lia.
        eapply (omo_write_op_step _ _ _ _ _ _ stlen' stlen) in OMO_GOOD as STEP'; try done. inversion STEP'.
        -- subst e'. rewrite -!lookup_omo_wr_event in He',HInitWrite.
            specialize (lookup_omo_inj _ _ _ _ _ _ OMO_GOOD He' HInitWrite) as H. inversion H. lia.
        -- subst e'. rewrite -!lookup_omo_wr_event in He',HInitWrite.
            specialize (lookup_omo_inj _ _ _ _ _ _ OMO_GOOD He' HInitWrite) as H. inversion H. lia.
        -- eapply arc_step_Clone; try done. subst. done.
        -- eapply arc_step_WeakClone; [done|done|..].
            ++ subst nstlen'. simpl. set_solver +IDVAL.
            ++ subst nstlen'. simpl. unfold not. intros. have EQ : e' = opId; [set_solver +FRESH H3|rewrite EQ in LTe'; lia].
            ++ subst nstlen' nstlen. rewrite NST /=.
               replace (stlen'.2.1.1 ∪ {[e']} ∪ {[opId]}) with (stlen'.2.1.1 ∪ {[opId]} ∪ {[e']}); [done|set_solver-].
        -- eapply arc_step_Downgrade; [done|done|..].
            ++ subst nstlen'. simpl. unfold not. intros. done.
            ++ subst nstlen' nstlen. simpl in *. have NEQ : e' ≠ opId by lia. set_solver +FRESH NEQ.
            ++ subst nstlen' nstlen. rewrite NST /=.
               replace (stlen'.2.1.1 ∪ {[e']} ∪ {[opId]}) with (stlen'.2.1.1 ∪ {[opId]} ∪ {[e']}); [done|set_solver-].
        -- eapply arc_step_Upgrade; [done|done|done|done|]. subst nstlen nstlen'. rewrite NST /=. done.
        -- subst nstlen' nstlen. rewrite H2 /=. by eapply arc_step_UpgradeFail.
        -- eapply arc_step_WeakDrop; [done|done|..].
            ++ subst nstlen'. set_solver +STRICT.
            ++ subst nstlen nstlen'. rewrite NST /=. destruct (decide (e'0 = opId)) as [->|NEQ].
              ** specialize (weak_state_valid _ _ _ _ _ OMO_GOOD Hstlen') as VAL.
                  have IN : opId ∈ stlen'.2.1.1; [set_solver +STRICT|apply VAL in IN; lia].
              ** replace (stlen'.2.1.1 ∖ {[e'0]} ∪ {[opId]}) with ((stlen'.2.1.1 ∪ {[opId]}) ∖ {[e'0]}); [done|set_solver +NEQ].
        -- rewrite /ArcAlive Forall_lookup in HAlive. apply HAlive in HeV'. by rewrite EVENT in HeV'.
        -- eapply arc_step_StrongDrop; try done. subst nstlen' nstlen. rewrite NST /=. done.
        -- eapply arc_step_StrongDrop_last; try done. subst nstlen nstlen'. rewrite NST /=. done.
        -- subst nstlen' nstlen. rewrite H2 /=. eapply arc_step_UnwrapFail; try done.
        -- rewrite /ArcAlive Forall_lookup in HAlive. apply HAlive in HeV'. by rewrite EVENT in HeV'.
      * rewrite lookup_drop in Hlen.
        eapply omo_gen_info in OMO_GOOD as (?&?&?&?&?&?&?&?& RO); [|exact Hlen].
        rewrite Forall_lookup. intros. rewrite Forall_lookup in RO. apply RO in H4.
        destruct H4 as (eV'' & HeV'' & STEP' & LT).
        replace (gen + len + 1) with (gen + 1 + len) in Hstlen by lia.
        rewrite Hstlen in H2. inversion H2. subst x1.
        exists eV''. split_and!; try done.
        { rewrite lookup_app_l; [done|]. apply lookup_lt_Some in HeV''. done. }
        inversion STEP';
        try (destruct stlen as [[[? ?] ?] [[? ?] ?]]; simpl in *; inversion NST; set_solver +FRESH H9);
        try (destruct stlen as [[[? ?] ?] [[? ?] ?]]; simpl in *; inversion NST; subst; set_solver +H9).
        -- eapply arc_step_UpgradeFail; try done.
        -- destruct stlen as [[[? ?] ?] [[? ?] ?]]. simpl in *. inversion NST. set_solver +STRICT H9.
        -- destruct stlen as [[[? ?] ?] [[? ?] ?]]. simpl in *. inversion NST. subst. set_solver +STRICT H9.
        -- eapply arc_step_UnwrapFail; try done.
        -- rewrite /ArcAlive Forall_lookup in HAlive. apply HAlive in HeV''. by rewrite EVENT in HeV''.
    + intros. destruct (decide (i = len)) as [->|NEQ].
      * rewrite EQlenST'' lookup_app_1_eq in H0. inversion H0. subst stn.
        replace (gen + len + 1) with (gen + 1 + len) in Hstlen by lia.
        rewrite Hstlen in H. inversion H. subst stp. done.
      * rewrite lookup_app_1_ne in H0; [|by rewrite -EQlenST'']. eapply Hstlist'; try done.
Qed.

Lemma weak_arc_delete_gen_good E omo stlist eVop gen st e V lV (E' := E ++ [eVop]) (opId := length E) (nst := (st.1, (st.2.1.1 ∖ {[e]}, st.2.1.2 ⊔ V, st.2.2 ∪ lV)))
    (OMO_GOOD : Linearizability_omo E omo stlist)
    (Hst : stlist !! gen = Some st)
    (STEP : step opId eVop st nst)
    (HInitWrite : omo_write_op omo !! 0 = Some 0)
    (SSub : ∀ i st, stlist !! i = Some st → gen ≤ i → {[e]} ⊂ st.2.1.1)
    (NoWeakClone : ∀ e' eidx' eV', lookup_omo omo eidx' = Some e' → E !! e' = Some eV' → gen < gen_of eidx' → eV'.(type) ≠ WeakClone e)
    (HAlive : ArcAlive E) :
  ∃ stlist', interp_omo E' ((opId, []) :: drop (gen + 1) omo) st (nst :: stlist')
      ∧ (∀ i stp stn, stlist !! (gen + 1 + i)%nat = Some stp → stlist' !! i = Some stn → stn = (stp.1, (stp.2.1.1 ∖ {[e]}, stp.2.1.2 ⊔ V, stp.2.2 ∪ lV))).
Proof.
  apply omo_stlist_length in OMO_GOOD as EQlenST.

  have H : ∀ len, ∃ stlist', interp_omo E' ((opId, []) :: take len (drop (gen + 1) omo)) st (nst :: stlist')
      ∧ (∀ i stp stn, stlist !! (gen + 1 + i)%nat = Some stp → stlist' !! i = Some stn
            → stn = (stp.1, (stp.2.1.1 ∖ {[e]}, stp.2.1.2 ⊔ V, stp.2.2 ∪ lV))); last first.
  { specialize (H (length (drop (gen + 1) omo))). rewrite take_ge in H; [|done]. done. }

  intros. induction len.
  - exists []. split; [|done]. rewrite take_0 -(app_nil_l [(opId, [])]) -(app_nil_l [nst]).
    apply (interp_omo_snoc _ _ _ eVop _ _ st). split_and!; try done; [by rewrite lookup_app_1_eq|by apply interp_omo_nil].
  - destruct IHlen as (stlist' & GEN_GOOD & Hstlist').
    destruct (le_lt_dec (length (drop (gen + 1) omo)) len) as [LE|LT].
    { rewrite take_ge in GEN_GOOD; [|done]. rewrite take_ge; [|lia]. by exists stlist'. }
    rewrite -lookup_lt_is_Some in LT. destruct LT as [[e' es'] Hlen]. erewrite take_S_r; [|done].

    have [stlen Hstlen] : is_Some (stlist !! ((gen + len) + 1)).
    { rewrite lookup_lt_is_Some -EQlenST. apply lookup_lt_Some in Hlen. rewrite drop_length in Hlen. lia. }
    set nstlen := (stlen.1, (stlen.2.1.1 ∖ {[e]}, stlen.2.1.2 ⊔ V, stlen.2.2 ∪ lV)).

    have [stlen' Hstlen'] : is_Some (stlist !! (gen + len)).
    { rewrite lookup_lt_is_Some. apply lookup_lt_Some in Hstlen. lia. }
    have eIN : e ∈ stlen'.2.1.1 by apply SSub in Hstlen'; [|lia]; set_solver +Hstlen'.
    set nstlen' : arc_state := (stlen'.1, (stlen'.2.1.1 ∖ {[e]}, stlen'.2.1.2 ⊔ V, stlen'.2.2 ∪ lV)).

    apply interp_omo_length in GEN_GOOD as EQlenST'. simpl in EQlenST'.
    inversion EQlenST'. rename H0 into EQlenST''.
    rewrite take_length Nat.min_l in EQlenST''; [|by apply lookup_lt_Some in Hlen; lia].

    have Hst' : last (nst :: stlist') = Some nstlen'.
    { destruct len.
      - destruct stlist'; [|done]. simpl. rewrite Nat.add_0_r Hst in Hstlen'. inversion Hstlen'. subst stlen'. done.
      - have [st' Hst'] : is_Some (stlist' !! len) by rewrite lookup_lt_is_Some; lia.
        replace (gen + S len) with (gen + 1 + len) in Hstlen' by lia.
        specialize (Hstlist' _ _ _ Hstlen' Hst').
        rewrite last_cons last_lookup- EQlenST'' /= Hst' Hstlist'. done. }

    have He' : lookup_omo omo (wr_event (gen + 1 + len)) = Some e'.
    { rewrite lookup_drop in Hlen. by rewrite lookup_omo_wr_event /omo_write_op list_lookup_fmap Hlen. }
    have [eV' HeV'] : is_Some (E !! e') by eapply lookup_omo_event_valid.
    apply lookup_lt_Some in HeV' as LTe'.

    exists (stlist' ++ [nstlen]). split.
    + replace ((opId, []) :: take len (drop (gen + 1) omo) ++ [(e', es')]) with
        (((opId, []) :: take len (drop (gen + 1) omo)) ++ [(e', es')]); [|by clear; simplify_list_eq].
      replace (nst :: stlist' ++ [nstlen]) with ((nst :: stlist') ++ [nstlen]); [|by clear; simplify_list_eq].
      eapply interp_omo_snoc. split_and!; try done.
      * rewrite lookup_app_l; [done|]. done.
      * rewrite lookup_omo_wr_event in He'. replace (gen + 1 + len) with ((gen + len) + 1) in He' by lia.
        eapply (omo_write_op_step _ _ _ _ _ _ stlen' stlen) in OMO_GOOD as STEP'; try done. inversion STEP'.
        -- subst e'. rewrite -!lookup_omo_wr_event in He',HInitWrite.
           specialize (lookup_omo_inj _ _ _ _ _ _ OMO_GOOD He' HInitWrite) as H. inversion H. lia.
        -- subst e'. rewrite -!lookup_omo_wr_event in He',HInitWrite.
           specialize (lookup_omo_inj _ _ _ _ _ _ OMO_GOOD He' HInitWrite) as H. inversion H. lia.
        -- eapply arc_step_Clone; try done. subst. simpl. done.
        -- eapply arc_step_WeakClone; [done|done|..].
            ++ subst nstlen'. simpl. destruct (decide (e'0 = e)) as [->|NEQ]; [|set_solver +IDVAL NEQ].
               rewrite -lookup_omo_wr_event in He'. eapply NoWeakClone in He'; try done. simpl. lia.
            ++ subst nstlen'. simpl. unfold not. intros. have EQ : e' = opId; [set_solver +FRESH H3|rewrite EQ in LTe'; lia].
            ++ subst nstlen' nstlen. rewrite NST /=. have NEQ : e' ≠ e by set_solver +FRESH eIN.
               replace ((stlen'.2.1.1 ∪ {[e']}) ∖ {[e]}) with (stlen'.2.1.1 ∖ {[e]} ∪ {[e']}); [done|set_solver +NEQ].
        -- eapply arc_step_Downgrade; [done|done|..].
            ++ subst nstlen'. simpl. unfold not. intros. done.
            ++ subst nstlen' nstlen. simpl in *. set_solver +FRESH.
            ++ subst nstlen' nstlen. rewrite NST /=. have NEQ : e' ≠ e by set_solver +FRESH eIN.
               replace ((stlen'.2.1.1 ∪ {[e']}) ∖ {[e]}) with (stlen'.2.1.1 ∖ {[e]} ∪ {[e']}); [done|set_solver +NEQ].
        -- eapply arc_step_Upgrade; [done|done|done|done|]. subst nstlen nstlen'. rewrite NST /=. done.
        -- subst nstlen' nstlen. rewrite H2 /=. by eapply arc_step_UpgradeFail.
        -- eapply arc_step_WeakDrop; [done|done|..].
            ++ subst nstlen'. simpl. apply SSub in Hstlen; [|lia]. rewrite NST /= in Hstlen.
               destruct (decide (e'0 = e)) as [->|NEQ]; [set_solver +Hstlen|].
               have e'0IN' : e'0 ∈ stlen'.2.1.1 ∖ {[e]} by set_solver +STRICT NEQ.
               destruct (decide (stlen'.2.1.1 ∖ {[e]} = {[e'0]})) as [EQ'|NEQ']; [|set_solver +e'0IN' NEQ'].
               have EQ'' : stlen'.2.1.1 = {[e; e'0]}.
               { apply set_eq. intros. split; intros.
                 - destruct (decide (x = e)) as [->|NEQx]; [set_solver-|].
                   have xIN : x ∈ stlen'.2.1.1 ∖ {[e]} by set_solver +H3 NEQx.
                   rewrite EQ' elem_of_singleton in xIN. subst x. set_solver-.
                 - have [EQx|EQx] : x = e ∨ x = e'0; [set_solver +H3|by subst x|by subst x; set_solver +e'0IN']. }
               rewrite EQ'' in Hstlen. set_solver +Hstlen.
            ++ subst nstlen nstlen'. rewrite NST /=. destruct (decide (e'0 = opId)) as [->|NEQ].
              ** specialize (weak_state_valid _ _ _ _ _ OMO_GOOD Hstlen') as VAL.
                  have IN : opId ∈ stlen'.2.1.1; [set_solver +STRICT|apply VAL in IN; lia].
              ** replace (stlen'.2.1.1 ∖ {[e'0]} ∖ {[e]}) with ((stlen'.2.1.1 ∖ {[e]}) ∖ {[e'0]}); [|set_solver-].
                 replace ((stlen'.2.1.2 ⊔ eV'.(sync)) ⊔ V) with ((stlen'.2.1.2 ⊔ V) ⊔ eV'.(sync)) by solve_lat.
                 replace (stlen'.2.2 ∪ eV'.(eview) ∪ lV) with (stlen'.2.2 ∪ lV ∪ eV'.(eview)) by set_solver-. done.
        -- rewrite /ArcAlive Forall_lookup in HAlive. apply HAlive in HeV'. by rewrite EVENT in HeV'.
        -- eapply arc_step_StrongDrop; try done. subst nstlen' nstlen. rewrite NST /=. done.
        -- eapply arc_step_StrongDrop_last; try done. subst nstlen nstlen'. rewrite NST /=. done.
        -- subst nstlen' nstlen. rewrite H2 /=. eapply arc_step_UnwrapFail; try done.
        -- rewrite /ArcAlive Forall_lookup in HAlive. apply HAlive in HeV'. by rewrite EVENT in HeV'.
      * rewrite lookup_drop in Hlen.
        eapply omo_gen_info in OMO_GOOD as (?&?&?&?&?&?&?&?& RO); [|exact Hlen].
        rewrite Forall_lookup. intros. rewrite Forall_lookup in RO. apply RO in H4.
        destruct H4 as (eV'' & HeV'' & STEP' & LT).
        replace (gen + len + 1) with (gen + 1 + len) in Hstlen by lia.
        rewrite Hstlen in H2. inversion H2. subst x1.
        exists eV''. split_and!; try done.
        { rewrite lookup_app_l; [done|]. apply lookup_lt_Some in HeV''. done. }
        inversion STEP';
        try (destruct stlen as [[[? ?] ?] [[? ?] ?]]; simpl in *; inversion NST; set_solver +FRESH H9);
        try (destruct stlen as [[[? ?] ?] [[? ?] ?]]; simpl in *; inversion NST; subst; set_solver +H9).
        -- eapply arc_step_UpgradeFail; try done.
        -- destruct stlen as [[[? ?] ?] [[? ?] ?]]. simpl in *. inversion NST. set_solver +STRICT H9.
        -- destruct stlen as [[[? ?] ?] [[? ?] ?]]. simpl in *. inversion NST. subst. set_solver +STRICT H9.
        -- eapply arc_step_UnwrapFail; try done.
        -- rewrite /ArcAlive Forall_lookup in HAlive. apply HAlive in HeV''. by rewrite EVENT in HeV''.
    + intros. destruct (decide (i = len)) as [->|NEQ].
      * rewrite EQlenST'' lookup_app_1_eq in H0. inversion H0. subst stn.
        replace (gen + len + 1) with (gen + 1 + len) in Hstlen by lia.
        rewrite Hstlen in H. inversion H. subst stp. done.
      * rewrite lookup_app_1_ne in H0; [|by rewrite -EQlenST'']. eapply Hstlist'; try done.
Qed.

Lemma SeenPrevStrong_after_weak_event e M eidx γg γs γs' γes γss γew γsw γm E Es Ew omo omos omow stlist mos mow Mono eVop Vbs Ms nst stlist' l ewn (opId := length E) :
  e ∈ M →
  lookup_omo omo eidx = Some e →
  is_Some (E !! e) →
  OmoHbToken γg γs' (E ++ [eVop]) (omo_insert_w omo (gen_of eidx + 1) (length E) []) (take (gen_of eidx + 1) stlist ++ nst :: stlist') opId _ -∗
  OmoAuth γes γss (1/2)%Qp Es omos mos _ -∗
  OmoAuth γew γsw (1/2)%Qp Ew omow mow _ -∗
  @{Vbs} append_only_loc l γes ∅ cas_only -∗
  CWMono γg γes γm Mono -∗
  @{eVop.(sync)} OmoEview γes Ms -∗
  HbIncluded γg γes M Ms -∗
  AllEvents γg γes γm E (omo_write_op omos) -∗
  AllStrongs γg γes γs γss γm (omo_write_op omos) -∗
  OmoEinfo γg opId eVop -∗
  OmoCW γg γew opId ewn
  ==∗
  SeenPrevStrong γg γes (omo_write_op omos) opId ∗
  OmoAuth γg γs' 1%Qp (E ++ [eVop]) (omo_insert_w omo (gen_of eidx + 1) (length E) []) (take (gen_of eidx + 1) stlist ++ nst :: stlist') _ ∗
  OmoAuth γes γss (1 / 2) Es omos mos _ ∗
  OmoAuth γew γsw (1 / 2) Ew omow mow _ ∗
  @{Vbs} append_only_loc l γes ∅ cas_only ∗
  CWMono γg γes γm Mono ∗
  HbIncluded γg γes M Ms.
Proof.
  iIntros "%eM %Heidx %He M● Ms● Mw● omos↦ Hγm #⊒Ms M⊢Ms #AllEvents #AllStrongs #opId✓eVop #opId↦ewn".
  destruct He as [eV HeV].
  iDestruct (big_sepL_lookup with "AllEvents") as "eInner"; [exact HeV|].

  have EQlenWR : length (take (gen_of eidx + 1) (omo_write_op omo)) = gen_of eidx + 1.
  { rewrite take_length Nat.min_l; [done|]. rewrite -omo_write_op_length. apply lookup_omo_lt_Some in Heidx. lia. }
  have EQlenRO : length (take (gen_of eidx + 1) (omo_read_op omo)) = gen_of eidx + 1.
  { rewrite take_length Nat.min_l; [done|]. rewrite -omo_read_op_length. apply lookup_omo_lt_Some in Heidx. lia. }

  have Heidxn : lookup_omo (omo_insert_w omo (gen_of eidx + 1) (length E) []) eidx = Some e.
  { destruct eidx.
    - have LTgen : gen < length (take (gen + 1) (omo_read_op omo)).
      { rewrite take_length -omo_read_op_length Nat.min_l; [lia|]. apply lookup_omo_lt_Some in Heidx. simpl in Heidx. lia. }
      rewrite lookup_omo_ro_event omo_insert_w_read_op /= lookup_app_l; [|done].
      rewrite lookup_omo_ro_event -(take_drop (gen + 1) (omo_read_op omo)) lookup_app_l in Heidx; [|done]. done.
    - have LTgen : gen < length (take (gen + 1) (omo_write_op omo)).
      { rewrite take_length -omo_write_op_length Nat.min_l; [lia|]. apply lookup_omo_lt_Some in Heidx. simpl in Heidx. lia. }
      rewrite lookup_omo_wr_event omo_insert_w_write_op /= lookup_app_l; [|done].
      rewrite lookup_omo_wr_event -(take_drop (gen + 1) (omo_write_op omo)) lookup_app_l in Heidx; [|done]. done. }
  have HopId : lookup_omo (omo_insert_w omo (gen_of eidx + 1) (length E) []) (wr_event (gen_of eidx + 1)) = Some opId.
  { rewrite lookup_omo_wr_event omo_insert_w_write_op lookup_app_r; [|lia].
    rewrite EQlenWR. replace (gen_of eidx + 1 - (gen_of eidx + 1)) with 0 by lia. simpl. done. }

    iAssert (OmoLe γg e opId)%I with "[-]" as "#e≤opId".
    { iDestruct (OmoHbToken_finish with "M●") as "M●".
      iApply (OmoLe_get _ _ _ _ _ _ eidx (wr_event (gen_of eidx + 1)) with "M●"); [done|..|simpl; lia].
      rewrite lookup_omo_wr_event omo_insert_w_write_op lookup_app_r; [|lia]. rewrite EQlenWR.
      replace (gen_of eidx + 1 - (gen_of eidx + 1)) with 0 by lia. simpl. done. }

    iAssert ( (∃ es, OmoCW γg γes e es ∗ OmoHb γg γes e es ∗ CWMonoValid γm e)
            ∨ SeenPrevStrong γg γes (omo_write_op omos) e)%I with "[]" as "[(%es & e↦es & e⊒es & MONO✓e)|[CASE|CASE]]".
    { destruct (eV.(type)); try (iLeft; iFrame "eInner"); try (iRight; iFrame "eInner"). }
    - iDestruct (OmoAuth_OmoCW_r' with "Ms● e↦es") as %[eidxs Heidxs].
      have [es' Hes'] : is_Some (lookup_omo omos (wr_event (gen_of eidxs))).
      { rewrite lookup_omo_wr_event lookup_lt_is_Some -omo_write_op_length. apply lookup_omo_lt_Some in Heidxs. done. }
      iDestruct (OmoEq_get with "Ms●") as "#es'=es"; [exact Hes'|exact Heidxs|done|].
      iDestruct (big_sepL_lookup with "AllStrongs") as (e' ? eVs') "(e'↦es' & _ & _ & es'✓eVs' & MONO✓e' & _)";
        [rewrite lookup_omo_wr_event in Hes'; exact Hes'|]. clear st.
      iDestruct (OmoLe_get_from_Eq with "es'=es") as "es'≤es".
      iDestruct (CWMono_acc with "Hγm MONO✓e' MONO✓e e'↦es' e↦es es'≤es") as "#e'≤e".
      iDestruct (OmoLe_trans with "e'≤e e≤opId") as "e'≤opId".

      iDestruct (OmoHb_HbIncluded with "e⊒es M⊢Ms") as %esMs; [done|].
      iMod (OmoHb_new_2 _ _ _ _ _ _ _ _ es Ms with "M● [] opId✓eVop") as "[M● #opId⊒es]"; [done|iFrame "⊒Ms"|].
      iDestruct (OmoHbToken_finish with "M●") as "M●".

      destruct (decide (gen_of eidxs = length omos - 1)) as [EQgens|NEQgens].
      + iModIntro. iFrame "M● Ms● Mw● omos↦ Hγm M⊢Ms". iLeft. iExists e',es',es. iFrame "e'≤opId es'=es opId⊒es e'↦es'". iPureIntro.
        rewrite last_lookup -omo_write_op_length. replace (Init.Nat.pred (length omos)) with (gen_of eidxs) by lia.
        rewrite lookup_omo_wr_event in Hes'. done.
      + have [es'' Hes''] : is_Some (lookup_omo omos (wr_event (S (gen_of eidxs)))).
        { rewrite lookup_omo_wr_event lookup_lt_is_Some. rewrite lookup_omo_wr_event in Hes'. apply lookup_lt_Some in Hes'.
          rewrite omo_write_op_length in NEQgens. lia. }
        iDestruct (big_sepL_lookup with "AllStrongs") as (e'' st'' eVs'') "(e''↦es'' & _ & _ & es''✓eVs'' & MONO✓e'' & _ & Hgen)";
          [rewrite lookup_omo_wr_event in Hes''; exact Hes''|].
        iDestruct "Hgen" as (omos' e''' es''' eV'' eVs''' st''') "(Ms◯ & e'''↦es''' & _ & _ & _ & e'<e'' & [%Hes''' _])".
        iDestruct (OmoAuth_OmoSnapOmo with "Ms● Ms◯") as %PREFIXomos.
        replace (S (gen_of eidxs) - 1) with (gen_of eidxs) in Hes''' by lia.
        rewrite -lookup_omo_wr_event in Hes'''. eapply omo_prefix_lookup_Some in Hes'''; [|done].
        rewrite Hes' in Hes'''. inversion Hes'''. subst es'''. clear Hes'''.

        iDestruct (OmoCW_agree_2 with "e'↦es' e'''↦es'''") as %[_ <-].
        iDestruct (OmoEq_sym with "es'=es") as "es=es'".
        iDestruct (OmoLe_get_from_Eq with "es=es'") as "es≤es'".
        iDestruct (CWMono_acc with "Hγm MONO✓e MONO✓e' e↦es e'↦es' es≤es'") as "#e≤e'".
        iDestruct (OmoLe_Lt_trans with "e≤e' e'<e''") as "#e<e''".
        iDestruct (OmoAuth_OmoCW_l' with "M● e''↦es''") as %[eidx'' Heidx''].
        iDestruct (OmoLt_Lt with "M● e<e''") as %LTgen1; [done|done|].
        destruct (le_lt_dec (gen_of eidx'') (gen_of eidx + 1)) as [LEgen2|LTgen2].
        { have EQgen : gen_of eidx'' = gen_of eidx + 1 by lia. destruct eidx''; simpl in EQgen; subst gen.
          - rewrite lookup_omo_ro_event omo_insert_w_read_op lookup_app_r in Heidx''; [|lia].
            rewrite EQlenRO in Heidx''. replace (gen_of eidx + 1 - (gen_of eidx + 1)) with 0 in Heidx'' by lia. simpl in Heidx''. done.
          - rewrite lookup_omo_wr_event omo_insert_w_write_op lookup_app_r in Heidx''; [|lia].
            rewrite EQlenWR in Heidx''. replace (gen_of eidx + 1 - (gen_of eidx + 1)) with 0 in Heidx'' by lia. inversion Heidx''. subst e''.
            iDestruct (OmoCW_agree_1 with "opId↦ewn e''↦es''") as %[-> _].
            iDestruct (OmoAuth_agree with "Ms● Mw●") as %(-> & -> & -> & ->). iCombine "Ms● Mw●" as "Ms●".
            iDestruct (OmoAuth_append_only_loc_frac_valid_obj with "Ms● omos↦") as %LE.
            rewrite -{1}Qp.half_half in LE. by apply Qp.not_add_le_l in LE. }
        iDestruct (OmoLt_get _ _ _ _ _ _ (wr_event (gen_of eidx + 1)) eidx'' with "M●") as "#opId<e''"; [done|done|simpl;lia|].

        iModIntro. iFrame "M● Ms● Mw● omos↦ Hγm M⊢Ms". iRight.
        iExists e',e'',es',es,es'',(gen_of eidxs). iFrame "e'≤opId opId<e'' es'=es e'↦es' e''↦es'' opId⊒es". iPureIntro.
        split; [done|]. replace (gen_of eidxs + 1) with (S (gen_of eidxs)) by lia. done.
    - iDestruct "CASE" as (???) "(ef≤e & esf=esfeq & ef↦esf & e⊒esfeq & %LASTesf)".
      iDestruct (OmoLe_trans with "ef≤e e≤opId") as "ef≤opId".

      iDestruct (OmoHb_HbIncluded with "e⊒esfeq M⊢Ms") as %esfeqMs; [done|].
      iMod (OmoHb_new_2 _ _ _ _ _ _ _ _ esfeq Ms with "M● [] opId✓eVop") as "[M● #opId⊒esfeq]"; [done|iFrame "⊒Ms"|].
      iDestruct (OmoHbToken_finish with "M●") as "M●".

      iModIntro. iFrame "M● Ms● Mw● omos↦ Hγm M⊢Ms". iLeft.
      iExists ef,esf,esfeq. iFrame "ef≤opId esf=esfeq ef↦esf opId⊒esfeq". done.
    - iDestruct "CASE" as (??????) "(el≤e & e<er & esl=esleq & el↦esl & er↦esr & e⊒esleq & Pures)".

      iDestruct (OmoHb_HbIncluded with "e⊒esleq M⊢Ms") as %esleqMs; [done|].
      iMod (OmoHb_new_2 _ _ _ _ _ _ _ _ esleq Ms with "M● [] opId✓eVop") as "[M● #opId⊒esleq]"; [done|iFrame "⊒Ms"|].
      iDestruct (OmoHbToken_finish with "M●") as "M●".

      iDestruct (OmoLe_trans with "el≤e e≤opId") as "el≤opId".
      iDestruct (OmoAuth_OmoCW_l' with "M● er↦esr") as %[eidxr Heidxr].
      iDestruct (OmoLt_Lt with "M● e<er") as %LTgen1; [done|done|].
      destruct (le_lt_dec (gen_of eidxr) (gen_of eidx + 1)) as [LEgen2|LTgen2].
      { have EQgen : gen_of eidxr = gen_of eidx + 1 by lia. destruct eidxr; simpl in EQgen; subst gen0.
        - rewrite lookup_omo_ro_event omo_insert_w_read_op lookup_app_r in Heidxr; [|lia].
          rewrite EQlenRO in Heidxr. replace (gen_of eidx + 1 - (gen_of eidx + 1)) with 0 in Heidxr by lia. inversion Heidxr.
        - rewrite lookup_omo_wr_event omo_insert_w_write_op lookup_app_r in Heidxr; [|lia].
          rewrite EQlenWR in Heidxr. replace (gen_of eidx + 1 - (gen_of eidx + 1)) with 0 in Heidxr by lia. inversion Heidxr. subst er.
          iDestruct (OmoCW_agree_1 with "opId↦ewn er↦esr") as %[-> _].
          iDestruct (OmoAuth_agree with "Ms● Mw●") as %(-> & -> & -> & ->). iCombine "Ms● Mw●" as "Ms●".
          iDestruct (OmoAuth_append_only_loc_frac_valid_obj with "Ms● omos↦") as %LE.
          rewrite -{1}Qp.half_half in LE. by apply Qp.not_add_le_l in LE. }
      iDestruct (OmoLt_get _ _ _ _ _ _ (wr_event (gen_of eidx + 1)) eidxr with "M●") as "#opId<er"; [done|done|simpl;lia|].

      iModIntro. iFrame "M● Ms● Mw● omos↦ Hγm M⊢Ms". iRight. repeat iExists _. iFrame "#".
Qed.

Lemma AllStrongs_update γg γs γs' γes γss γew γsw γm q E Es Ew omo omos omow stlist stlist' mos mow Vbs l eVop ewn gen pst nst (E' := E ++ [eVop]) (opId := length E) :
  interp_omo E' ((opId, []) :: drop (gen + 1) omo) pst (nst :: stlist') →
  (∀ (i : nat) (stp stn : arc_state),
          stlist !! (gen + 1 + i) = Some stp → stlist' !! i = Some stn → stn.1 = stp.1) →
  Linearizability_omo E omo stlist →
  gen < length omo →
  OmoAuth γg γs' q (E ++ [eVop]) (omo_insert_w omo (gen + 1) (length E) []) (take (gen + 1) stlist ++ nst :: stlist') _ -∗
  OmoAuth γes γss (1/2)%Qp Es omos mos _ -∗
  OmoAuth γew γsw (1/2)%Qp Ew omow mow _ -∗
  @{Vbs} append_only_loc l γes ∅ cas_only -∗
  AllStrongs γg γes γs γss γm (omo_write_op omos) -∗
  OmoCW γg γew opId ewn -∗
  OmoSnapStates γg γs omo stlist -∗
  AllStrongs γg γes γs' γss γm (omo_write_op omos).
Proof.
  iIntros "%Hgengood %Hstlist' %OMO_GOOD %LTgen M● Ms● Mw● omos↦ #AllStrongs #opId↦ewn #ST◯".
  iApply big_sepL_forall. iIntros "%i %es %Hes".
  iDestruct (big_sepL_lookup with "AllStrongs") as (ei sti eVs)
    "(ei↦es & ei⊒es & ei↪sti & es✓eVs & MONO✓ei & %eVsEV & Hi)"; [exact Hes|].
  iDestruct (OmoAuth_OmoCW_l' with "M● ei↦es") as %[eidxi Heidxi].

  iAssert (⌜ ei ≠ opId ⌝)%I with "[-]" as %NEQei.
  { iIntros "%EQei". subst ei.
    iDestruct (OmoCW_agree_1 with "opId↦ewn ei↦es") as %[<- _].
    iDestruct (OmoAuth_agree with "Ms● Mw●") as %(<- & <- & <- & <-). iCombine "Ms● Mw●" as "Ms●".
    iDestruct (OmoAuth_append_only_loc_frac_valid_obj with "Ms● omos↦") as %LE.
    rewrite -{1}Qp.half_half in LE. by apply Qp.not_add_le_l in LE. }

  eapply omo_stlist_length in OMO_GOOD as EQlenST.
  iDestruct (OmoSnap_update with "M● ei↪sti ST◯") as (sti') "[#ei↪sti' %EQsti]"; [done..|].
  iExists ei,sti',eVs. iFrame "ei↦es ei⊒es ei↪sti' es✓eVs MONO✓ei".
  rewrite eVsEV -EQsti. iSplit; [done|]. destruct i; [done|].
  iDestruct "Hi" as (omos' e' es' eVi eVs' st') "(Ms◯ & e'↦es' & ei✓eVi & es'✓eVs' & e'↪st' & Pures)".

  iAssert (⌜ e' ≠ opId ⌝)%I with "[-]" as %NEQe'.
  { iIntros "%EQe'". subst e'.
    iDestruct (OmoCW_agree_1 with "opId↦ewn e'↦es'") as %[<- _].
    iDestruct (OmoAuth_agree with "Ms● Mw●") as %(<- & <- & <- & <-). iCombine "Ms● Mw●" as "Ms●".
    iDestruct (OmoAuth_append_only_loc_frac_valid_obj with "Ms● omos↦") as %LE.
    rewrite -{1}Qp.half_half in LE. by apply Qp.not_add_le_l in LE. }
  iDestruct (OmoAuth_OmoCW_l' with "M● e'↦es'") as %[eidx' Heidx'].
  iDestruct (OmoSnap_update with "M● e'↪st' ST◯") as (st'') "[#e'↪st'' %EQst']"; [done..|].

  iExists omos',e',es',eVi,eVs',st''. rewrite -EQst'. iFrame "Ms◯ e'↦es' ei✓eVi es'✓eVs' e'↪st'' Pures".
Qed.

Lemma weak_arc_insert_new_state E omo stlist stlist' gen eVop stf pst
    (E' := E ++ [eVop]) (opId := length E) (nst := (pst.1, (pst.2.1.1 ∪ {[opId]}, pst.2.1.2, pst.2.2)))
    (OMO_GOOD : Linearizability_omo E omo stlist)
    (OMO_GOOD' : Linearizability_omo E' (omo_insert_w omo (gen + 1) opId []) (take (gen + 1) stlist ++ nst :: stlist'))
    (LASTstf : last stlist = Some stf)
    (Hpst : stlist !! gen = Some pst)
    (Hstlist' : (∀ (i : nat) (stp stn : arc_state),
          stlist !! (gen + 1 + i) = Some stp
          → stlist' !! i = Some stn
            → stn = (stp.1, (stp.2.1.1 ∪ {[length E]}, stp.2.1.2, stp.2.2)))) :
  ∃ nstf, last (take (gen + 1) stlist ++ nst :: stlist') = Some nstf ∧ nstf = (stf.1, (stf.2.1.1 ∪ {[opId]}, stf.2.1.2, stf.2.2)).
Proof.
  have [nstf Hnstf] : is_Some (last (take (gen + 1) stlist ++ nst :: stlist')).
  { rewrite last_is_Some. unfold not. intros. apply (f_equal length) in H. rewrite app_length /= in H. lia. }
  apply omo_stlist_length in OMO_GOOD as EQlenST. apply omo_stlist_length in OMO_GOOD' as EQlenST'.
  rewrite last_app in Hnstf.
  have [nstf' Hnstf'] : is_Some (last (nst :: stlist')) by rewrite last_is_Some.
  rewrite Hnstf' in Hnstf. inversion Hnstf. subst nstf'. destruct (decide (stlist' = [])) as [->|NEQstlist'].
  - inversion Hnstf'. subst nstf. rewrite omo_insert_w_length app_length /= in EQlenST'.
    have EQlenST'' : length omo = length (take (gen + 1) stlist) by lia.
    rewrite take_length Nat.min_l in EQlenST''; [|apply lookup_lt_Some in Hpst; lia].
    rewrite last_lookup -EQlenST EQlenST'' in LASTstf. replace (Init.Nat.pred (gen + 1)) with gen in LASTstf by lia.
    rewrite Hpst in LASTstf. inversion LASTstf. subst stf. exists nst. rewrite last_snoc. done.
  - rewrite last_lookup -EQlenST in LASTstf.
    rewrite omo_insert_w_length app_length /= take_length Nat.min_l in EQlenST'; [|apply lookup_lt_Some in Hpst; lia].
    replace (Init.Nat.pred (length omo)) with (gen + 1 + Init.Nat.pred (length stlist')) in LASTstf; last first.
    { have NZstlist' : length stlist' ≠ 0 by destruct stlist'. lia. }
    have [nstf' Hnstf''] : is_Some (last stlist') by rewrite last_is_Some.
    rewrite last_cons Hnstf'' in Hnstf'. inversion Hnstf'. subst nstf'.
    exists nstf. rewrite last_app last_cons Hnstf''.
    rewrite last_lookup in Hnstf''. specialize (Hstlist' _ _ _ LASTstf Hnstf''). done.
Qed.

Lemma weak_arc_delete_new_state E omo stlist stlist' gen eVop stf pst e V lV
    (E' := E ++ [eVop]) (opId := length E) (nst := (pst.1, (pst.2.1.1 ∖ {[e]}, pst.2.1.2 ⊔ V, pst.2.2 ∪ lV)))
    (OMO_GOOD : Linearizability_omo E omo stlist)
    (OMO_GOOD' : Linearizability_omo E' (omo_insert_w omo (gen + 1) opId []) (take (gen + 1) stlist ++ nst :: stlist'))
    (LASTstf : last stlist = Some stf)
    (Hpst : stlist !! gen = Some pst)
    (Hstlist' : (∀ (i : nat) (stp stn : arc_state),
          stlist !! (gen + 1 + i) = Some stp
          → stlist' !! i = Some stn
            → stn = (stp.1, (stp.2.1.1 ∖ {[e]}, stp.2.1.2 ⊔ V, stp.2.2 ∪ lV)))) :
  ∃ nstf, last (take (gen + 1) stlist ++ nst :: stlist') = Some nstf ∧ nstf = (stf.1, (stf.2.1.1 ∖ {[e]}, stf.2.1.2 ⊔ V, stf.2.2 ∪ lV)).
Proof.
  have [nstf Hnstf] : is_Some (last (take (gen + 1) stlist ++ nst :: stlist')).
  { rewrite last_is_Some. unfold not. intros. apply (f_equal length) in H. rewrite app_length /= in H. lia. }
  apply omo_stlist_length in OMO_GOOD as EQlenST. apply omo_stlist_length in OMO_GOOD' as EQlenST'.
  rewrite last_app in Hnstf.
  have [nstf' Hnstf'] : is_Some (last (nst :: stlist')) by rewrite last_is_Some.
  rewrite Hnstf' in Hnstf. inversion Hnstf. subst nstf'. destruct (decide (stlist' = [])) as [->|NEQstlist'].
  - inversion Hnstf'. subst nstf. rewrite omo_insert_w_length app_length /= in EQlenST'.
    have EQlenST'' : length omo = length (take (gen + 1) stlist) by lia.
    rewrite take_length Nat.min_l in EQlenST''; [|apply lookup_lt_Some in Hpst; lia].
    rewrite last_lookup -EQlenST EQlenST'' in LASTstf. replace (Init.Nat.pred (gen + 1)) with gen in LASTstf by lia.
    rewrite Hpst in LASTstf. inversion LASTstf. subst stf. exists nst. rewrite last_snoc. done.
  - rewrite last_lookup -EQlenST in LASTstf.
    rewrite omo_insert_w_length app_length /= take_length Nat.min_l in EQlenST'; [|apply lookup_lt_Some in Hpst; lia].
    replace (Init.Nat.pred (length omo)) with (gen + 1 + Init.Nat.pred (length stlist')) in LASTstf; last first.
    { have NZstlist' : length stlist' ≠ 0 by destruct stlist'. lia. }
    have [nstf' Hnstf''] : is_Some (last stlist') by rewrite last_is_Some.
    rewrite last_cons Hnstf'' in Hnstf'. inversion Hnstf'. subst nstf'.
    exists nstf. rewrite last_app last_cons Hnstf''.
    rewrite last_lookup in Hnstf''. specialize (Hstlist' _ _ _ LASTstf Hnstf''). done.
Qed.

Lemma weak_counter_load_valid genw ew eVw (zw zwf : Z) ewf (eVwf : omo_event loc_event) γg γew γsw γwa γb γul Ew omow mow ulcks sarc warc nsf ty stf qu qd Vp (P1 : Qp → vProp) q1 q2 dgds lcks Vsf e ainfo Mw :
  omo_write_op omow !! genw = Some ew →
  last (omo_write_op omow) = Some ewf →
  (loc_event_msg eVw.(type)).1 = #zw →
  (loc_event_msg eVwf.(type)).1 = #zwf →
  nsf = size stf.1.1.1 →
  (-1 ≤ zw)%Z →
  dom warc = stf.2.1.1 →
  ulcks ⊆ Mw →
  OmoAuth γew γsw (1/2)%Qp Ew omow mow _ -∗
  ⎡ghost_map_auth γwa 1 warc⎤ -∗
  AllWeaks γg γew γsw (dom warc) ulcks (omo_write_op omow) -∗
  OmoUB γew Mw ew -∗
  OmoEinfo γew ew eVw -∗
  OmoEinfo γew ewf eVwf -∗
  ⎡e ↪[γwa] ainfo⎤ -∗
  (match nsf with
    | 0 => emp
    | S _ =>
      @{Vp} (P1 q1) ∗ @{Vsf} (P1 q2 ∗ OmoEview γg dgds ∗ OmoEview γew lcks) ∗ (∃ eV0, OmoEinfo γg 0 eV0 ∗ ⌜ eV0.(type) = StrongInit ⌝) ∗
      ⎡0 ↪[γwa] ((1/2)%Qp, Vp, ∅, ∅, cas_only)⎤ ∗ ⎡ghost_var γb (1/2/2)%Qp true⎤ ∗ ⎡ghost_var γul (1/2)%Qp ulcks⎤ ∗
      ⌜ qd = 1%Qp ⌝
    end) -∗
  (match ty with
    | cas_only =>
      ( (∃ e, OmoHb γg γew e ewf) ∨ (∃ e ainfo, ⌜ sarc !! e = Some ainfo ∧ ewf ∈ ainfo.1.2 ⌝) ∨ ⌜ nsf = 0 ⌝) ∗
      ⌜ zwf = Z.of_nat (size stf.2.1.1) ∧ qu = 1%Qp ⌝
    | swriter =>
      ⌜ zwf = (-1)%Z ∧ size stf.2.1.1 = 1
      ∧ (∃ e ainfo, e ∈ stf.1.1.1 ∧ sarc !! e = Some ainfo ∧ ainfo.2 = swriter)
      ∧ qu = (1/2)%Qp ⌝
    end) -∗
  ⌜ (1 ≤ zw)%Z ⌝.
Proof.
  iIntros "%Hgenw %LASTewf %eVwEV %eVwfEV %EQnstf %GEzw %DOMwarc %SubulcksMw Mw● Hγwa #AllWeaks #MAXew #ew✓eVw #ewf✓eVwf e↪ainfo Hnsf Hty".

  destruct (decide (zw = (-1)%Z)) as [->|NEQzw1].
  { destruct (decide (genw = length omow - 1)) as [->|NEQ].
    - replace (length omow - 1) with (Init.Nat.pred (length omow)) in Hgenw by lia.
      rewrite omo_write_op_length -last_lookup LASTewf in Hgenw. inversion Hgenw. subst ew.
      iDestruct (OmoEinfo_agree with "ewf✓eVwf ew✓eVw") as %<-.
      rewrite eVwfEV in eVwEV. inversion eVwEV. subst zwf.

      destruct ty; [by iDestruct "Hty" as "[_ [%SZstf _]]"; lia|].
      iDestruct "Hty" as %(_ & SZstf & (e' & ainfo' & He' & _) & _).
      destruct nsf.
      + symmetry in EQnstf. apply size_empty_inv in EQnstf. fold_leibniz.
        rewrite EQnstf in He'. done.
      + iDestruct "Hnsf" as "(_ & _ & _ & e0↪ainfo & _)".
        iDestruct (ghost_map_lookup with "Hγwa e↪ainfo") as %Hwarce.
        iDestruct (ghost_map_lookup with "Hγwa e0↪ainfo") as %Hwarce0.
        apply size_1_elem_of in SZstf as [x Hstf]. fold_leibniz.
        rewrite Hstf in DOMwarc. apply dom_singleton_inv_L in DOMwarc as [x' Hwarc].
        rewrite !Hwarc !lookup_singleton_Some in Hwarce,Hwarce0.
        destruct Hwarce as [-> _]. destruct Hwarce0 as [-> _].
        by iDestruct (ghost_map_elem_valid_2 with "e↪ainfo e0↪ainfo") as %[? _].
    - have [ew' Hew'] : is_Some (omo_write_op omow !! (S genw)).
      { rewrite lookup_lt_is_Some. apply lookup_lt_Some in Hgenw. rewrite omo_write_op_length in NEQ. lia. }
      iDestruct (big_sepL_lookup with "AllWeaks") as (eVw' zw') "(ew'✓eVw' & [%eVw'EV %GEzw'] & Hgenw')"; [exact Hew'|].
      iDestruct "Hgenw'" as (omow' ew'' eVw'' zw'') "(Mw◯ & ew''✓eVw'' & [%Hew'' %eVw''EV] & CASE)".
      replace (S genw - 1) with genw in Hew'' by lia.
      rewrite -lookup_omo_wr_event in Hew''.
      iDestruct (OmoAuth_OmoSnapOmo with "Mw● Mw◯") as %PREFIXomow.
      eapply omo_prefix_lookup_Some in Hew''; [|exact PREFIXomow].
      rewrite lookup_omo_wr_event Hgenw in Hew''. inversion Hew''. subst ew''.
      iDestruct (OmoEinfo_agree with "ew✓eVw ew''✓eVw''") as %<-.
      rewrite eVwEV /= in eVw''EV. inversion eVw''EV. subst zw''.

      iDestruct "CASE" as "[(%&%& _ & _ & _ & [% _])|[[% _]|[[% _]|(_ & _ & %ew'IN)]]]"; [lia..|].
      iDestruct (big_sepS_elem_of _ _ ew' with "MAXew") as "ew'≤ew"; [set_solver +ew'IN SubulcksMw|].
      iDestruct (OmoLe_Le _ _ _ _ _ _ (wr_event (S genw)) (wr_event genw) with "Mw● ew'≤ew") as %LE.
      { by rewrite lookup_omo_wr_event. } { by rewrite lookup_omo_wr_event. } simpl in LE. lia. }

  destruct (decide (zw = 0%Z)) as [->|NEQzw2]; [|iPureIntro; lia].
  destruct (decide (genw = length omow - 1)) as [->|NEQ].
  - replace (length omow - 1) with (Init.Nat.pred (length omow)) in Hgenw by lia.
    rewrite omo_write_op_length -last_lookup LASTewf in Hgenw. inversion Hgenw. subst ew.
    iDestruct (OmoEinfo_agree with "ewf✓eVwf ew✓eVw") as %<-.
    rewrite eVwfEV in eVwEV. inversion eVwEV. subst zwf.

    destruct ty; [|by iDestruct "Hty" as %[? _]; lia].
    iDestruct "Hty" as "[_ [%Zsz _]]".
    have Zstf2 : size stf.2.1.1 = 0 by lia.
    apply size_empty_inv in Zstf2. fold_leibniz. rewrite Zstf2 dom_empty_iff_L in DOMwarc.
    iDestruct (ghost_map_lookup with "Hγwa e↪ainfo") as %Hwarce. rewrite DOMwarc in Hwarce. done.
  - have [ew' Hew'] : is_Some (omo_write_op omow !! (S genw)).
    { rewrite lookup_lt_is_Some. apply lookup_lt_Some in Hgenw. rewrite omo_write_op_length in NEQ. lia. }
    iDestruct (big_sepL_lookup with "AllWeaks") as (eVw' zw') "(ew'✓eVw' & [%eVw'EV %GEzw'] & Hgenw')"; [exact Hew'|].
    iDestruct "Hgenw'" as (omow' ew'' eVw'' zw'') "(Mw◯ & ew''✓eVw'' & [%Hew'' %eVw''EV] & CASE)".
    replace (S genw - 1) with genw in Hew'' by lia.
    rewrite -lookup_omo_wr_event in Hew''.
    iDestruct (OmoAuth_OmoSnapOmo with "Mw● Mw◯") as %PREFIXomow.
    eapply omo_prefix_lookup_Some in Hew''; [|exact PREFIXomow].
    rewrite lookup_omo_wr_event Hgenw in Hew''. inversion Hew''. subst ew''.
    iDestruct (OmoEinfo_agree with "ew✓eVw ew''✓eVw''") as %<-.
    rewrite eVwEV /= in eVw''EV. inversion eVw''EV. subst zw''.
    iDestruct "CASE" as "[(%&%& _ & _ & _ & [% _])|[[% _]|[[% _]|[% _]]]]"; lia.
Qed.

Lemma weak_init_no_strong E omo stlist eV0
    (OMO_GOOD : Linearizability_omo E omo stlist)
    (HInitWrite : omo_write_op omo !! 0 = Some 0)
    (HeV0 : E !! 0 = Some eV0)
    (EVENT : eV0.(type) = WeakInit) :
  ∀ i st, stlist !! i = Some st → st.1.1.1 = ∅.
Proof.
  apply omo_stlist_length in OMO_GOOD as EQlenST.
  intros. generalize dependent st. induction i; intros.
  - eapply omo_write_op_init_step in OMO_GOOD as STEP; try done. inversion STEP; rewrite EVENT in EVENT0; try done.
  - have [st' Hst'] : is_Some (stlist !! i).
    { rewrite lookup_lt_is_Some. apply lookup_lt_Some in H. lia. }
    apply IHi in Hst' as EQst'.
    have [e He] : is_Some (omo_write_op omo !! (i + 1)%nat).
    { rewrite lookup_lt_is_Some -omo_write_op_length EQlenST. apply lookup_lt_Some in H. lia. }
    replace (S i) with (i + 1) in H by lia.
    rewrite -lookup_omo_wr_event in He. eapply lookup_omo_event_valid in He as HeV; [|done].
    destruct HeV as [eV HeV]. rewrite lookup_omo_wr_event in He.
    eapply omo_write_op_step in OMO_GOOD as STEP; try done.
    inversion STEP; subst; simpl in *; try done.
    + rewrite HeV0 in HeV. inversion HeV. subst eV0. rewrite EVENT in EVENT0. done.
    + rewrite EQst' in IDVAL. done.
    + rewrite EQst' in STRICT. set_solver +STRICT.
Qed.

Lemma AllEvents_after_strong_write_event γg γs γes γm q E omo omos stlist eV esn (opId := length E) :
  length omos ≠ 0 →
  match eV.(type) with
  | StrongInit | WeakInit | Clone _ | Upgrade | StrongDrop _ _ => True
  | _ => False
  end →
  AllEvents γg γes γm E (omo_write_op omos) -∗
  OmoAuth γg γs q (E ++ [eV]) (omo_append_w omo opId []) stlist _ -∗
  OmoCW γg γes opId esn -∗
  OmoHb γg γes opId esn -∗
  CWMonoValid γm opId -∗
  AllEvents γg γes γm (E ++ [eV]) (omo_write_op omos ++ [esn]).
Proof.
  iIntros "%NZomos %eVEV #AllEvents M● #opId↦esn #opId⊒esn #MONO✓opId". iApply big_sepL_snoc. iSplit.
  - iApply big_sepL_forall; [intros; destruct x.(type); apply _|]. iIntros (e' eV') "%HeV'".
    iAssert (SeenPrevStrong γg γes (omo_write_op omos) e' -∗ SeenPrevStrong γg γes (omo_write_op omos ++ [esn]) e')%I with "[-]" as "H".
      { iIntros "[(%ef & %esf & %esfeq & #ef≤e' & #esf=esfeq & #ef↦esf & #e'⊒esfeq & %LASTesf)|(%el & %er & %esl & %esleq &
          %esr & %gensl & #el≤e' & #e'<er & #esl=esleq & #el↦esl & #er↦esr & #e'⊒esleq & [%Hesl %Hesr])]"; iRight.
        - iExists ef,opId,esf,esfeq,esn,(length omos - 1).
          have NEQ : e' ≠ opId by apply lookup_lt_Some in HeV'; lia.
          iDestruct (OmoEinfo_get _ _ _ _ _ _ e' with "M●") as "#e'✓eV'"; [by rewrite lookup_app_1_ne|].
          iDestruct (OmoLt_get_append_w _ _ _ _ _ _ opId e' with "M● e'✓eV'") as "#e'<opId"; [done|].
          iFrame "ef≤e' e'<opId esf=esfeq ef↦esf opId↦esn e'⊒esfeq". iPureIntro.
          rewrite Nat.sub_add; [|lia]. rewrite omo_write_op_length lookup_app_1_eq lookup_app_1_ne; [|rewrite -omo_write_op_length;lia].
          replace (length (omo_write_op omos) - 1) with (Init.Nat.pred (length (omo_write_op omos))) by lia. rewrite -last_lookup. done.
        - iExists el,er,esl,esleq,esr,gensl. iFrame "#". iPureIntro.
          rewrite lookup_app_l; [|by apply lookup_lt_Some in Hesl]. rewrite lookup_app_l; [|by apply lookup_lt_Some in Hesr]. done. }
    iDestruct (big_sepL_lookup with "AllEvents") as "Inner"; [exact HeV'|].
    destruct (eV'.(type)); try done; by iApply "H".
  - destruct (eV.(type)); try done; iExists esn; iFrame "opId↦esn opId⊒esn MONO✓opId".
Qed.

Lemma append_only_type_condition_update γg γew sarc e ainfo nainfo ty ewf zwf nsf (stf : arc_state) qu (sarc' := <[e := nainfo]> (delete e sarc)) :
  sarc !! e = Some ainfo →
  ainfo.1.2 ⊆ nainfo.1.2 →
  ainfo.2 = cas_only →
  match ty with
  | cas_only =>
    ( (∃ e0, OmoHb γg γew e0 ewf) ∨ (∃ e0 ainfo0, ⌜ sarc !! e0 = Some ainfo0 ∧ ewf ∈ ainfo0.1.2 ⌝) ∨ ⌜ nsf = 0 ⌝) ∗
    ⌜ zwf = Z.of_nat (size stf.2.1.1) ∧ qu = 1%Qp ⌝
  | swriter =>
    ⌜ zwf = (-1)%Z ∧ size stf.2.1.1 = 1
    ∧ (∃ e0 ainfo0, e0 ∈ stf.1.1.1 ∧ sarc !! e0 = Some ainfo0 ∧ ainfo0.2 = swriter)
    ∧ qu = (1/2)%Qp ⌝
  end -∗
  match ty with
  | cas_only =>
    ( (∃ e0, OmoHb γg γew e0 ewf) ∨ (∃ e0 ainfo0, ⌜ sarc' !! e0 = Some ainfo0 ∧ ewf ∈ ainfo0.1.2 ⌝) ∨ ⌜ nsf = 0 ⌝) ∗
    ⌜ zwf = Z.of_nat (size stf.2.1.1) ∧ qu = 1%Qp ⌝
  | swriter =>
    ⌜ zwf = (-1)%Z ∧ size stf.2.1.1 = 1
    ∧ (∃ e0 ainfo0, e0 ∈ stf.1.1.1 ∧ sarc' !! e0 = Some ainfo0 ∧ ainfo0.2 = swriter)
    ∧ qu = (1/2)%Qp ⌝
  end.
Proof.
  iIntros "%Hsarce %Subainfo %Hainfo2 Hty". destruct ty.
  - iDestruct "Hty" as "[[H|[(%e' & %ainfo' & %Hsarce' & %ewfIN)|%ZSZ]] H']"; iFrame "H'"; [iLeft; iFrame "H"|..].
    + iRight. iLeft. destruct (decide (e' = e)) as [->|NEQ].
      * rewrite Hsarce in Hsarce'. inversion Hsarce'. subst ainfo'. iExists e,nainfo. iPureIntro.
        rewrite lookup_insert. split; [done|]. set_solver +ewfIN Subainfo.
      * iExists e',ainfo'. iPureIntro. rewrite lookup_insert_ne; [|done]. rewrite lookup_delete_ne; [|done]. done.
    + iRight. iRight. done.
  - iDestruct "Hty" as %(H1 & H2 & H3 & H4). iPureIntro. split_and!; try done. des. destruct (decide (e0 = e)) as [->|NEQ].
    + rewrite Hsarce in H0. inversion H0. subst ainfo0. rewrite Hainfo2 in H5. done.
    + exists e0,ainfo0. rewrite lookup_insert_ne; [|done]. rewrite lookup_delete_ne; [|done]. done.
Qed.

Lemma weak_state_no_decrease E omo stlist i e sti sdom wdom
    (OMO_GOOD : Linearizability_omo E omo stlist)
    (Hsti : stlist !! i = Some sti)
    (EQsti : sti.2.1.1 = {[e]})
    (VALsarcwarc : ArcsValid2 E sdom wdom)
    (HInitWrite : omo_write_op omo !! 0 = Some 0)
    (eIN : e ∈ wdom) :
  ∀ j stj, i ≤ j → stlist !! j = Some stj →
    (sti.2.1.1 = stj.2.1.1 ∨ (∃ k ek eVk stk', i < k ∧ k ≤ j ∧ stlist !! (k - 1) = Some stk' ∧ sti.2.1.1 = stk'.2.1.1
                              ∧ omo_write_op omo !! k = Some ek ∧ E !! ek = Some eVk ∧ (eVk.(type) = WeakClone e ∨ eVk.(type) = Downgrade))).
Proof.
  intros. apply omo_stlist_length in OMO_GOOD as EQlenST. generalize dependent stj. induction H as [|j]; intros.
  - rewrite Hsti in H0. inversion H0. subst stj. by left.
  - have [stj' Hstj'] : is_Some (stlist !! j).
    { rewrite lookup_lt_is_Some. apply lookup_lt_Some in H0. lia. }
    apply IHle in Hstj' as CASE. destruct CASE as [EQstj'|(k & ek & eVk & stk' & LEk1 & LEk2 & Hstk' & EQstk' & Hek & HeVk & eVkEV)]; last first.
    { right. exists k,ek,eVk,stk'. split_and!; try done. lia. }
    have [ej Hej] : is_Some (omo_write_op omo !! (j + 1)%nat).
    { rewrite lookup_lt_is_Some -omo_write_op_length EQlenST. apply lookup_lt_Some in H0. lia. }
    rewrite -lookup_omo_wr_event in Hej. eapply lookup_omo_event_valid in Hej as HeVj; [|done].
    destruct HeVj as [eVj HeVj]. rewrite lookup_omo_wr_event in Hej.
    replace (S j) with (j + 1)%nat in H0 by lia.
    eapply omo_write_op_step in OMO_GOOD as STEP; try done. inversion STEP; subst; simpl in *; try (by left);
    try (rewrite -!lookup_omo_wr_event in Hej, HInitWrite2;
        (eapply lookup_omo_inj in HInitWrite2; [|done|exact Hej]); inversion HInitWrite2; lia).
    + rewrite -!lookup_omo_wr_event in HInitWrite Hej. eapply lookup_omo_inj in HInitWrite; [|done|exact Hej]. inversion HInitWrite. lia.
    + rewrite -!lookup_omo_wr_event in HInitWrite Hej. eapply lookup_omo_inj in HInitWrite; [|done|exact Hej]. inversion HInitWrite. lia.
    + right. exists (j + 1),ej,eVj,stj'. split_and!; try done; [lia|lia|by rewrite Nat.add_sub|]. left.
      rewrite -EQstj' EQsti elem_of_singleton in IDVAL. subst e'. done.
    + right. exists (j + 1),ej,eVj,stj'. split_and!; try done; [lia|lia|by rewrite Nat.add_sub|]. right. done.
    + rewrite -EQstj' EQsti in STRICT. set_solver +STRICT.
    + rewrite -EQstj' EQsti set_eq in WEAK. specialize (WEAK e'). rewrite !elem_of_singleton in WEAK.
      have EQ' : e' = e by rewrite WEAK. subst e'. apply VALsarcwarc in HeVj. rewrite EVENT in HeVj. done.
Qed.

Lemma ArcInv_Linearizable_instance :
  ∀ γg γs l E omo stlist, ArcInv γg γs l E omo stlist ⊢ ⌜ Linearizability_omo E omo stlist ⌝.
Proof. intros. iIntros "M●". by iDestruct (OmoAuth_Linearizable with "M●") as %?. Qed.

Lemma ArcInv_OmoAuth_acc_instance :
  ∀ γg γs l E omo stlist,
    ArcInv γg γs l E omo stlist ⊢ OmoAuth γg γs (1/2)%Qp E omo stlist _ ∗ (OmoAuth γg γs (1/2)%Qp E omo stlist _ -∗ ArcInv γg γs l E omo stlist).
Proof. intros. do 2 (iIntros "M●"; iFrame "M●"). Qed.

Lemma StrongArc_OmoEview_instance :
  ∀ N γg l q P1 P2 M e, StrongArc N γg l q P1 P2 M e ⊢ OmoEview γg M.
Proof. intros. by iDestruct 1 as (??????????) "(%&%&%&%&%&%& #HN & #AInv & #⊒M & _)". Qed.

Lemma WeakArc_OmoEview_instance :
  ∀ N γg l P1 P2 M e, WeakArc N γg l P1 P2 M e ⊢ OmoEview γg M.
Proof. intros. by iDestruct 1 as (??????????) "(%&%&%&%&%&%&%& #HN & #AInv & #⊒M & _)". Qed.

Lemma FakeArc_OmoEview_instance :
  ∀ N γg l P1 P2 M, FakeArc N γg l P1 P2 M ⊢ OmoEview γg M.
Proof. intros. by iDestruct 1 as (??????????) "(%&%&%&%&%&%&%&%&%&%&%& #HN & #AInv & #⊒M & _)". Qed.

Lemma StrongArc_Eview_update_instance :
  ∀ N γg l q P1 P2 e M1 M2, StrongArc N γg l q P1 P2 M1 e -∗ OmoEview γg M2 -∗ StrongArc N γg l q P1 P2 (M1 ∪ M2) e.
Proof.
  intros. iIntros "SArc #⊒M2".
  iDestruct "SArc" as (??????????) "(%&%&%&%&%&%& #HN & #AInv & #⊒M & #⊒Ms & #⊒Mw & #e✓eV & #⊒ainfo & Hγb & e↪ainfo &
    (-> & %Hainfo2 & %eM & %eVEV & %SubainfoM & %SubainfoMw))".
  iDestruct (OmoEview_union with "⊒M ⊒M2") as "⊒M'".
  repeat iExists _. iFrame "HN AInv ⊒M' ⊒Ms ⊒Mw e✓eV ⊒ainfo Hγb e↪ainfo". iPureIntro. split_and!; try done; try set_solver.
Qed.

Lemma WeakArc_Eview_update_instance :
  ∀ N γg l P1 P2 e M1 M2, WeakArc N γg l P1 P2 M1 e -∗ OmoEview γg M2 -∗ WeakArc N γg l P1 P2 (M1 ∪ M2) e.
Proof.
  intros. iIntros "WArc #⊒M2".
  iDestruct "WArc" as (??????????) "(%&%&%&%&%&%&%& #HN & #AInv & #⊒M & #⊒Ms & #⊒Mw & #e✓eV & #⊒ainfo & Hγb & e↪ainfo & Hγul & HeP2 &
    (%Hainfo2 & %eM & %eVEV & %SubainfoM & %SubainfoMw))".
  iDestruct (OmoEview_union with "⊒M ⊒M2") as "⊒M'".
  repeat iExists _. iFrame "HN AInv ⊒M' ⊒Ms ⊒Mw e✓eV ⊒ainfo Hγb e↪ainfo Hγul HeP2". iPureIntro. split_and!; try done; try set_solver.
Qed.

Lemma FakeArc_Eview_update_instance :
  ∀ N γg l P1 P2 M1 M2, FakeArc N γg l P1 P2 M1 -∗ OmoEview γg M2 -∗ FakeArc N γg l P1 P2 (M1 ∪ M2).
Proof.
  intros. iIntros "FArc #⊒M2".
  iDestruct "FArc" as (??????????) "(%&%&%&%&%&%&%&%&%&%&%& #HN & #AInv & #⊒M & #⊒Ms & #⊒Mw & #e0✓eV0 & #e✓eV & #⊒ainfo & Hγb & e0↪ainfo &
    Hγul & Hγd & (%Hainfo2 & %eM & %eV0EV & %eVEV & %SubainfoM & %SubainfoMw))".
  iDestruct (OmoEview_union with "⊒M ⊒M2") as "⊒M'".
  repeat iExists _. iFrame "HN AInv ⊒M' ⊒Ms ⊒Mw e✓eV ⊒ainfo Hγb Hγul e0↪ainfo Hγd e0✓eV0". iPureIntro. split_and!; try done; try set_solver.
Qed.

Lemma create_strong :
  create_strong' ArcInv StrongArc.
Proof.
  intros Ec l P1 P2 V0 N. iIntros "%PasFrac #⊒V0 ls↦ lw↦ P1".

  iCombine "ls↦ lw↦ P1" as "RES".
  iDestruct (view_at_intro_incl with "RES ⊒V0") as (V1) "(#⊒V1 & %LeV0V1 & (ls↦@V1 & lw↦@V1 & P1@V1))".

  iAssert (@{V1} ⊒V1)%I with "[]" as "#⊒V1@V1"; [done|].
  iAssert (|==> @{V1} (∃ γes γss V1' (eVs0 : omo_event loc_event), ⊒V1' ∗
    OmoAuth γes γss (1/2)%Qp [eVs0] (omo_append_w [] 0 []) [(0, (#1, V1'))] _ ∗ @{V1'} OmoEview γes {[0]} ∗
    append_only_loc l γes ∅ cas_only ∗ OmoTokenW γes 0 ∗ OmoEinfo γes 0 eVs0 ∗ ⌜ eVs0.(type) = WriteE (#1, V1') ∧ V1 ⊑ V1' ⌝))%I
      with "[ls↦@V1]" as ">(%γes & %γss & %V1' & %eVs0 & #⊒V1'@V1 & Ms● & #⊒Ms@V1 & omos↦ & WCOMMITs & #es0✓eVs0 & [%eVs0EV %LeV1V1'])".
  { iCombine "ls↦@V1 ⊒V1@V1" as "RES". rewrite -view_at_bupd. iApply (view_at_mono with "RES"); [done|].
    iIntros "[ls↦ #⊒V1]". iMod (append_only_loc_cas_only_from_na_rel with "⊒V1 ls↦")
      as (γes γss V1' eVs0) "(#⊒V1' & Ms● & [#⊒Ms@V1' #⊒V1'@V1] & omos↦ & WCOMMITs & #es0✓eVs0 & [%eVs0EV _])"; [done|].
    iModIntro. repeat iExists _. iFrame "⊒V1' Ms● omos↦ WCOMMITs ⊒Ms@V1' es0✓eVs0".
    rewrite !view_at_unfold !monPred_at_in. iDestruct "⊒V1'@V1" as %?. done. }
  iAssert (|==> @{V1} (∃ γew γsw V1'' (eVw0 : omo_event loc_event), ⊒V1'' ∗
    OmoAuth γew γsw (1/2)%Qp [eVw0] (omo_append_w [] 0 []) [(0, (#1, V1''))] _ ∗ @{V1''} OmoEview γew {[0]} ∗
    append_only_loc (l >> 1) γew ∅ cas_only ∗ OmoTokenW γew 0 ∗ OmoEinfo γew 0 eVw0 ∗ ⌜ eVw0.(type) = WriteE (#1, V1'') ∧ V1 ⊑ V1'' ⌝))%I
      with "[lw↦@V1]" as ">(%γew & %γsw & %V1'' & %eVw0 & #⊒V1''@V1 & Mw● & #⊒Mw@V1 & omow↦ & WCOMMITw & #ew0✓eVw0 & [%eVw0EV %LeV1V1''])".
  { iCombine "lw↦@V1 ⊒V1@V1" as "RES". rewrite -view_at_bupd. iApply (view_at_mono with "RES"); [done|].
    iIntros "[lw↦ #⊒V1]". iMod (append_only_loc_cas_only_from_na_rel with "⊒V1 lw↦")
      as (γew γsw V1'' eVw0) "(#⊒V1'' & Mw● & [#⊒Mw@V1'' #⊒V1''@V1] & omow↦ & WCOMMITw & #ew0✓eVw0 & [%eVw0EV _])"; [done|].
    iModIntro. repeat iExists _. iFrame "⊒V1'' Mw● omow↦ WCOMMITw ⊒Mw@V1'' ew0✓eVw0".
    rewrite !view_at_unfold !monPred_at_in. iDestruct "⊒V1''@V1" as %?. done. }

  rewrite !view_at_objective_iff.
  iAssert (⌜ V1' ⊑ V1 ∧ V1'' ⊑ V1 ⌝)%I with "[]" as %[LeV1'V1 LeV1''V1].
  { rewrite !view_at_unfold !monPred_at_in. iDestruct "⊒V1'@V1" as %?. iDestruct "⊒V1''@V1" as %?. done. }
  have [EQV1' EQV1''] : V1 = V1' ∧ V1 = V1'' by solve_lat. subst V1' V1''.

  set M := {[0%nat]}.
  set eVop := mkOmoEvent StrongInit V1 M.
  set stf : arc_state := (({[0]}, V1, M), ({[0]}, V1, M)).

  iMod (@mono_list_own_alloc gname _ _ []) as (γnl) "[Hγnl _]".

  iMod (@OmoAuth_alloc_Gname _ _ _ _ _ eVop stf _ γnl _ arc_interpretable with "WCOMMITs")
    as (γg γs) "(M● & #⊒M@V1 & #opId↦es0 & #opId✓eVop & #opId↪stf & #Hγx & WCOMMIT)"; [by eapply arc_step_StrongInit|done|].
  iMod (OmoHb_new_2 _ _ _ _ _ _ _ _ 0 M with "M● [] opId✓eVop") as "[M● #opId⊒es0]"; [set_solver-|iFrame "⊒Ms@V1"|].
  iMod (OmoHb_new_2 _ _ _ _ _ _ _ _ 0 M with "M● [] opId✓eVop") as "[M● #opId⊒ew0]"; [set_solver-|iFrame "⊒Mw@V1"|].
  iDestruct (OmoHbToken_finish with "M●") as "[M● M●']".
  iMod (CWMono_new γg γes) as (γm) "Hγm".
  iMod (CWMono_insert_last_last (wr_event 0) with "Hγm M● Ms● opId↦es0") as "(Hγm & #MONO✓opId & M● & Ms●)"; [done|done|].

  iMod (@ghost_map_alloc_empty _ event_id ainfo_type) as (γsa) "Hγsa".
  iMod (@ghost_map_alloc_empty _ event_id ainfo_type) as (γwa) "Hγwa".
  iMod (@ghost_var_alloc _ bool _ true) as (γb) "Hγb".
  iMod (@ghost_var_alloc _ (gset event_id) _ M) as (γu) "Hγu".
  iMod (@ghost_var_alloc _ (gset event_id) _ M) as (γd) "Hγd".
  iMod (@ghost_var_alloc _ (gset event_id) _ M) as (γl) "Hγl".
  iMod (@ghost_var_alloc _ (gset event_id) _ M) as (γul) "[Hγul Hγul']".
  remember (encode (γsa,γwa,γb,γm,γes,γss,γew,γsw,γu,γd,γl,γul)) as γn eqn:Hγn.
  iMod (mono_list_auth_own_update [γn] with "Hγnl") as "[_ Hγnl']"; [by rewrite -(app_nil_l [γn]); apply prefix_app_r|].
  iDestruct (mono_list_idx_own_get 0 γn with "Hγnl'") as "#Hγnl"; [done|].

  iAssert (ArcGname γg γsa γwa γb γm γes γss γew γsw γu γd γl γul)%I with "[]" as "#HN"; [by repeat iExists _; iFrame "#"|].

  set ainfo : ainfo_type := ((1/2)%Qp, V1, ∅, ∅, cas_only).
  iMod (ghost_map_insert 0 ainfo with "Hγsa") as "[Hγsa opId↪ainfo]"; [done|].
  iMod (ghost_map_insert 0 ainfo with "Hγwa") as "[Hγwa e0↪ainfo]"; [done|].
  have Hfrac : (1 = (1/2/2 + 1/2/2) + 1/2/2 + 1/2/2)%Qp by compute_done. rewrite {6}Hfrac. clear Hfrac.
  iDestruct "Hγb" as "[[Hγb Hγb'] Hγb0]". iDestruct "P1@V1" as "[[P1@V1a P1@V1b] P1@V1']".

  iMod (inv_alloc (arcN N) _ (ArcInternalInv γg l P1 P2) with "[-P1@V1' M●' opId↪ainfo Hγb' WCOMMIT]") as "#AInv".
  { iNext. repeat iExists _. iFrame "HN M● Ms● Mw● Hγsa Hγwa Hγm Hγb". simpl.
    do 4 iExists _. iExists stf,0,0,eVs0,eVw0,1,1%Z. iExists V1,V1,V1,(1/2/2)%Qp,(1/2/2)%Qp,_,_. iExists M,M,M,M.
    iFrame "omos↦ omow↦". iFrame "Hγu Hγd Hγul Hγl es0✓eVs0 ew0✓eVw0 P1@V1a P1@V1b Hγb0 Hγul' e0↪ainfo ⊒M@V1 ⊒Mw@V1".
    iSplit; last iSplit; last iSplit; last iSplit; last iSplit; last iSplit.
    - iApply big_sepL_singleton. iExists 0. iFrame "opId↦es0 opId⊒es0 MONO✓opId".
    - iApply big_sepL_singleton. iExists 0,stf,eVs0. iFrame "opId↦es0 opId⊒es0 opId↪stf es0✓eVs0 MONO✓opId".
      subst stf. rewrite eVs0EV size_singleton /=. replace (Z.of_nat 1) with 1%Z by lia. done.
    - iApply big_sepL_singleton. iExists eVw0,1%Z. iFrame "ew0✓eVw0". rewrite eVw0EV /=. done.
    - iApply big_sepL_singleton. iExists eVw0,1%Z. iFrame "ew0✓eVw0". rewrite eVw0EV /=. done.
    - iSplit; [|done]. iExists eVop. iFrame "opId✓eVop". done.
    - subst stf. rewrite size_singleton. iSplit; [|iPureIntro; split; try done; lia]. iLeft. iExists 0. iFrame "opId⊒ew0".
    - iPureIntro. rewrite !last_singleton eVs0EV eVw0EV /= dom_insert_L dom_empty_L.
      have EQ : M ∪ ∅ = M by set_solver-. rewrite EQ. split_and!; try done.
      + rewrite map_fold_insert_L; [|by apply frac_sum_wf|done]. rewrite map_fold_empty. compute_done.
      + rewrite map_fold_insert_L; [|by apply frac_sum_wf|done]. rewrite map_fold_empty. compute_done.
      + unfold ArcsValid. intros. subst M. rewrite elem_of_singleton in H. subst e. simpl. lia.
      + unfold ArcsValid. intros. subst M. rewrite elem_of_singleton in H. subst e. simpl. lia.
      + unfold ArcsValid2. intros. destruct e; [|done]. inversion H. subst eV. done.
      + unfold SeenClone. intros. destruct e'; [|done]. inversion H0. subst eV. done.
      + unfold SeenWeakClone. intros. destruct e'; [|done]. inversion H0. subst eV. done.
      + compute_done.
      + rewrite /ArcAlive Forall_singleton. done.
      + unfold EventIdValid. intros. destruct e; [|done]. inversion H. done.
      + rewrite !map_fold_insert_L; [|solve_lat|done]. rewrite !map_fold_empty. solve_lat.
      + unfold SeenUpgrade. intros. destruct e; [|done]. inversion H. subst eV. done.
      + unfold SeenDowngrade. intros. destruct e; [|done]. inversion H. subst eV. done.
      + unfold SeenUnlock. intros. left. done.
      + unfold ArcsSeen. intros. destruct (decide (e = 0)) as [->|NEQ].
        * rewrite lookup_insert in H. inversion H. subst ainfo0. done.
        * rewrite lookup_insert_ne in H; [|done]. done.
      + unfold ArcsSeen. intros. destruct (decide (e = 0)) as [->|NEQ].
        * rewrite lookup_insert in H. inversion H. subst ainfo0. done.
        * rewrite lookup_insert_ne in H; [|done]. done.
      + rewrite /StlistValid Forall_singleton. intros. done. }

  iModIntro. iExists γg,γs,V1,M,(1/2)%Qp. iFrame "M●' P1@V1' WCOMMIT ⊒V1". iSplit; [|done].
  repeat iExists _. iFrame "HN AInv ⊒M@V1 ⊒Ms@V1 ⊒Mw@V1 opId✓eVop opId↪ainfo Hγb'". iSplit.
  - iApply view_at_unfold. rewrite monPred_at_in. iPureIntro. solve_lat.
  - iPureIntro. split_and!; try done. by left.
Qed.

Lemma create_weak :
  create_weak' ArcInv WeakArc.
Proof.
  intros Ec l P1 P2 V0 N. iIntros "#⊒V0 ls↦ lw↦ P2".

  iCombine "ls↦ lw↦ P2" as "RES".
  iDestruct (view_at_intro_incl with "RES ⊒V0") as (V1) "(#⊒V1 & %LeV0V1 & (ls↦@V1 & lw↦@V1 & P2@V1))".

  iAssert (@{V1} ⊒V1)%I with "[]" as "#⊒V1@V1"; [done|].
  iAssert (|==> @{V1} (∃ γes γss V1' (eVs0 : omo_event loc_event), ⊒V1' ∗
    OmoAuth γes γss (1/2)%Qp [eVs0] (omo_append_w [] 0 []) [(0, (#0, V1'))] _ ∗ @{V1'} OmoEview γes {[0]} ∗
    append_only_loc l γes ∅ cas_only ∗ OmoTokenW γes 0 ∗ OmoEinfo γes 0 eVs0 ∗ ⌜ eVs0.(type) = WriteE (#0, V1') ∧ V1 ⊑ V1' ⌝))%I
      with "[ls↦@V1]" as ">(%γes & %γss & %V1' & %eVs0 & #⊒V1'@V1 & Ms● & #⊒Ms@V1 & omos↦ & WCOMMITs & #es0✓eVs0 & [%eVs0EV %LeV1V1'])".
  { iCombine "ls↦@V1 ⊒V1@V1" as "RES". rewrite -view_at_bupd. iApply (view_at_mono with "RES"); [done|].
    iIntros "[ls↦ #⊒V1]". iMod (append_only_loc_cas_only_from_na_rel with "⊒V1 ls↦")
      as (γes γss V1' eVs0) "(#⊒V1' & Ms● & [#⊒Ms@V1' #⊒V1'@V1] & omos↦ & WCOMMITs & #es0✓eVs0 & [%eVs0EV _])"; [done|].
    iModIntro. repeat iExists _. iFrame "⊒V1' Ms● omos↦ WCOMMITs ⊒Ms@V1' es0✓eVs0".
    rewrite !view_at_unfold !monPred_at_in. iDestruct "⊒V1'@V1" as %?. done. }
  iAssert (|==> @{V1} (∃ γew γsw V1'' (eVw0 : omo_event loc_event), ⊒V1'' ∗
    OmoAuth γew γsw (1/2)%Qp [eVw0] (omo_append_w [] 0 []) [(0, (#1, V1''))] _ ∗ @{V1''} OmoEview γew {[0]} ∗
    append_only_loc (l >> 1) γew ∅ cas_only ∗ OmoTokenW γew 0 ∗ OmoEinfo γew 0 eVw0 ∗ ⌜ eVw0.(type) = WriteE (#1, V1'') ∧ V1 ⊑ V1'' ⌝))%I
      with "[lw↦@V1]" as ">(%γew & %γsw & %V1'' & %eVw0 & #⊒V1''@V1 & Mw● & #⊒Mw@V1 & omow↦ & WCOMMITw & #ew0✓eVw0 & [%eVw0EV %LeV1V1''])".
  { iCombine "lw↦@V1 ⊒V1@V1" as "RES". rewrite -view_at_bupd. iApply (view_at_mono with "RES"); [done|].
    iIntros "[lw↦ #⊒V1]". iMod (append_only_loc_cas_only_from_na_rel with "⊒V1 lw↦")
      as (γew γsw V1'' eVw0) "(#⊒V1'' & Mw● & [#⊒Mw@V1'' #⊒V1''@V1] & omow↦ & WCOMMITw & #ew0✓eVw0 & [%eVw0EV _])"; [done|].
    iModIntro. repeat iExists _. iFrame "⊒V1'' Mw● omow↦ WCOMMITw ⊒Mw@V1'' ew0✓eVw0".
    rewrite !view_at_unfold !monPred_at_in. iDestruct "⊒V1''@V1" as %?. done. }

  rewrite !view_at_objective_iff.
  iAssert (⌜ V1' ⊑ V1 ∧ V1'' ⊑ V1 ⌝)%I with "[]" as %[LeV1'V1 LeV1''V1].
  { rewrite !view_at_unfold !monPred_at_in. iDestruct "⊒V1'@V1" as %?. iDestruct "⊒V1''@V1" as %?. done. }
  have [EQV1' EQV1''] : V1 = V1' ∧ V1 = V1'' by solve_lat. subst V1' V1''.

  set M := {[0%nat]}.
  set eVop := mkOmoEvent WeakInit V1 M.
  set stf : arc_state := ((∅, V1, M), ({[0]}, V1, M)).

  iMod (@mono_list_own_alloc gname _ _ []) as (γnl) "[Hγnl _]".

  iMod (@OmoAuth_alloc_Gname _ _ _ _ _ eVop stf _ γnl _ arc_interpretable with "WCOMMITs")
    as (γg γs) "(M● & #⊒M@V1 & #opId↦es0 & #opId✓eVop & #opId↪stf & #Hγx & WCOMMIT)"; [by eapply arc_step_WeakInit|done|].
  iMod (OmoHb_new_2 _ _ _ _ _ _ _ _ 0 M with "M● [] opId✓eVop") as "[M● #opId⊒es0]"; [set_solver-|iFrame "⊒Ms@V1"|].
  iMod (OmoHb_new_2 _ _ _ _ _ _ _ _ 0 M with "M● [] opId✓eVop") as "[M● #opId⊒ew0]"; [set_solver-|iFrame "⊒Mw@V1"|].
  iDestruct (OmoHbToken_finish with "M●") as "[M● M●']".
  iMod (CWMono_new γg γes) as (γm) "Hγm".
  iMod (CWMono_insert_last_last (wr_event 0) with "Hγm M● Ms● opId↦es0") as "(Hγm & #MONO✓opId & M● & Ms●)"; [done|done|].

  iMod (@ghost_map_alloc_empty _ event_id ainfo_type) as (γsa) "Hγsa".
  iMod (@ghost_map_alloc_empty _ event_id ainfo_type) as (γwa) "Hγwa".
  iMod (@ghost_var_alloc _ bool _ true) as (γb) "Hγb".
  iMod (@ghost_var_alloc _ (gset event_id) _ M) as (γu) "Hγu".
  iMod (@ghost_var_alloc _ (gset event_id) _ M) as (γd) "Hγd".
  iMod (@ghost_var_alloc _ (gset event_id) _ M) as (γl) "Hγl".
  iMod (@ghost_var_alloc _ (gset event_id) _ M) as (γul) "[Hγul Hγul']".
  remember (encode (γsa,γwa,γb,γm,γes,γss,γew,γsw,γu,γd,γl,γul)) as γn eqn:Hγn.
  iMod (mono_list_auth_own_update [γn] with "Hγnl") as "[_ Hγnl']"; [by rewrite -(app_nil_l [γn]); apply prefix_app_r|].
  iDestruct (mono_list_idx_own_get 0 γn with "Hγnl'") as "#Hγnl"; [done|].

  iAssert (ArcGname γg γsa γwa γb γm γes γss γew γsw γu γd γl γul)%I with "[]" as "#HN"; [by repeat iExists _; iFrame "#"|].

  set ainfo : ainfo_type := ((1/2)%Qp, V1, ∅, ∅, cas_only).
  iMod (ghost_map_insert 0 ainfo with "Hγwa") as "[Hγwa opId↪ainfo]"; [done|].
  have Hfrac : (1 = (1/2 + 1/2/2) + 1/2/2)%Qp by compute_done. rewrite {6}Hfrac. clear Hfrac.
  iDestruct "Hγb" as "[Hγb Hγb']".

  iMod (inv_alloc (arcN N) _ (ArcInternalInv γg l P1 P2) with "[-P2@V1 M●' opId↪ainfo Hγb' WCOMMIT Hγul']") as "#AInv".
  { iNext. repeat iExists _. iFrame "HN M● Ms● Mw● Hγsa Hγwa Hγm Hγb". simpl.
    do 4 iExists _. iExists stf,0,0,eVs0,eVw0,0,1%Z. iExists V1,V1,V1,(1/2)%Qp,(1/2)%Qp,_,_. iExists M,M,M,M.
    iFrame "omos↦ omow↦". iFrame "Hγu Hγd Hγul Hγl es0✓eVs0 ew0✓eVw0 ⊒M@V1 ⊒Mw@V1".
    iSplit; last iSplit; last iSplit; last iSplit; last iSplit; last iSplit.
    - iApply big_sepL_singleton. iExists 0. iFrame "opId↦es0 opId⊒es0 MONO✓opId".
    - iApply big_sepL_singleton. iExists 0,stf,eVs0. iFrame "opId↦es0 opId⊒es0 opId↪stf es0✓eVs0 MONO✓opId".
      subst stf. rewrite eVs0EV size_empty /=. replace (Z.of_nat 0) with 0%Z by lia. done.
    - iApply big_sepL_singleton. iExists eVw0,1%Z. iFrame "ew0✓eVw0". rewrite eVw0EV /=. done.
    - iApply big_sepL_singleton. iExists eVw0,1%Z. iFrame "ew0✓eVw0". rewrite eVw0EV /=. done.
    - iSplit; [|done]. iRight. iRight. done.
    - iPureIntro. set_solver-.
    - iPureIntro. rewrite !last_singleton eVs0EV eVw0EV /= dom_insert_L dom_empty_L Qp.half_half.
      have EQ : M ∪ ∅ = M by set_solver-. rewrite EQ. split_and!; try done.
      + rewrite map_fold_insert_L; [|by apply frac_sum_wf|done]. rewrite map_fold_empty. compute_done.
      + unfold ArcsValid. intros. subst M. rewrite elem_of_singleton in H. subst e. simpl. lia.
      + unfold ArcsValid2. intros. destruct e; [|done]. inversion H. subst eV. done.
      + unfold SeenWeakClone. intros. destruct e'; [|done]. inversion H0. subst eV. done.
      + rewrite /ArcAlive Forall_singleton. done.
      + unfold EventIdValid. intros. destruct e; [|done]. inversion H. done.
      + rewrite !map_fold_insert_L; [|solve_lat|done]. rewrite !map_fold_empty. solve_lat.
      + unfold SeenUpgrade. intros. destruct e; [|done]. inversion H. subst eV. done.
      + unfold SeenDowngrade. intros. destruct e; [|done]. inversion H. subst eV. done.
      + unfold SeenUnlock. intros. left. done.
      + unfold ArcsSeen. intros. destruct (decide (e = 0)) as [->|NEQ].
        * rewrite lookup_insert in H. inversion H. subst ainfo0. done.
        * rewrite lookup_insert_ne in H; [|done]. done.
      + rewrite /StlistValid Forall_singleton. intros. done.
      + solve_lat. }

  iModIntro. iExists γg,γs,V1,M. iFrame "M●' WCOMMIT ⊒V1". iSplit; [|done].
  repeat iExists _. iFrame "HN AInv ⊒M@V1 ⊒Ms@V1 ⊒Mw@V1 opId✓eVop opId↪ainfo Hγb' Hγul' P2@V1". iSplit.
  - iApply view_at_unfold. rewrite monPred_at_in. iPureIntro. solve_lat.
  - iPureIntro. split_and!; try done; [by right; left|]. set_solver-.
Qed.

Lemma strong_count_spec :
  strong_count_spec' code.strong_count ArcInv StrongArc.
Proof.
  intros N DISJ l tid γg q M e V0 P1 P2. iIntros "#⊒V0 SArc" (Φ) "AU".
  iDestruct "SArc" as (??????????) "(%&%&%&%&%&%& #HN & #AInv & #⊒M & #⊒Ms & #⊒Mw & #e✓eV & #⊒ainfo & Hγb & e↪ainfo &
    (-> & %Hainfo2 & %eM & %eVEV & %SubainfoM & %SubainfoMw))".

  (* Inv access 1 *)
  wp_lam. iInv "AInv" as "H" "Hclose".
  iDestruct "H" as (?? γs1 ???????) "(%&%&%& %sarc1 & %warc1 & %qsa1 & %qwa1 & %alive1 & %E1 & %Es1 & %Ew1 & %omo1 & %omos1 &
    %omow1 & %stlist1 & %mos1 & %mow1 & %Mono1 & >HN' & >M●1 & >Ms●1 & >Mw●1 & >Hγsa1 & >Hγwa1 & >Hγb1 & >Hγm1 & Alive1)".
  gname_agree with "HN HN'". iClear "HN'".
  iDestruct (ghost_var_agree with "Hγb Hγb1") as %<-.

  iCombine "⊒V0 ⊒ainfo" as "⊒V0'". rewrite monPred_in_view_op. set V0' := V0 ⊔ ainfo.1.1.1.2.
  iDestruct "Alive1" as (Vbs1 Vbw1 ty1 uf1 stf1 esf1 ewf1 eVsf1 eVwf1 nsf1) "(%zwf1 & %Vsf1 & %Vwf1 & %Vp1 & %qsa1a & %qsa1b & %qu1 & %qd1 & %upds1 &
    %dgds1 & %lcks1 & %ulcks1 & >#AllEvents1 & >#AllStrongs1 & >#AllWeaks1 & >omos↦1 & >omow↦1 & >Hγu1 & >Hγd1 & >Hγl1 & >Hγul1 &
    >#AllLocks1 & [>#⊒upds1@Vwf1 >#⊒ulcks1@Vwf1] & >#esf1✓eVsf1 & >#ewf1✓eVwf1 & Hnsf1 & P2 & Hty1 & >#⊒stf1s@Vsf1 & >#⊒stf1w@Vwf1 & >Pures)".
  iDestruct "Pures" as %(Subuf1 & LASTesf1 & LASTewf1 & eVsf1EV & eVwf1EV & Hqsa1 & Hqwa1 & VALsarc1 & VALwarc1 & VALsarcwarc1 & SeenClone1 &
    SeenWeakClone1 & HInitWrite1 & LASTstf1 & DOMsarc1 & DOMwarc1 & EQqsa1 & Alive1 & VALeid1 & LeVbs1Vbw1 & GeVsf1 & GeVwf1 &
    SeenUpgrade1 & SeenDowngrade1 & SeenUnlock1 & LEsarc1 & LEwarc1 & VALstlist1 & LeVsf1 & EQnsf1).

  wp_apply (append_only_loc_relaxed_read with "[$Ms●1 $⊒Ms $omos↦1 $⊒V0']"); [solve_ndisj|].
  iIntros (es1 gens1 vs1 Vs1 V1 eVs1 eVsn1) "(Pures & Ms●1 & RCOMMIT & #MAXes1 & #es1✓eVs1 & #esn1✓eVsn1 & #es1=esn1 & #⊒V1 & _ & #⊒Ms1@V1 & omos↦1)".
  iDestruct "Pures" as %(Hgens1 & eVs1EV & LeV0'V1 & eVsn1EV & eVsn1SYNC).

  iDestruct (big_sepL_lookup with "AllStrongs1") as (e1 st1 eVs1')
    "(e1↦es1 & e1⊒es1 & e1↪st1 & es1✓eVs1' & MONO✓e1 & %eVs1'EV & Hgens1)"; [exact Hgens1|].
  iDestruct (OmoEinfo_agree with "es1✓eVs1 es1✓eVs1'") as %<-.
  rewrite eVs1EV /= in eVs1'EV. subst vs1.
  iDestruct (ghost_map_lookup with "Hγsa1 e↪ainfo") as %Hsarc1e.

  (* Prove that the message that we read is nonzero *)
  iAssert (⌜ size st1.1.1.1 ≠ 0 ⌝)%I with "[-]" as %NZSZ.
  { iIntros "%ZSZ". destruct (decide (gens1 = length omos1 - 1)) as [->|NEQ].
    - replace (length omos1 - 1) with (Init.Nat.pred (length omos1)) in Hgens1 by lia.
      rewrite omo_write_op_length -last_lookup LASTesf1 in Hgens1. inversion Hgens1. subst es1.
      iDestruct (OmoEinfo_agree with "esf1✓eVsf1 es1✓eVs1") as %<-. rewrite eVsf1EV in eVs1EV. inversion eVs1EV. subst nsf1 Vs1.
      have Zstf1 : size stf1.1.1.1 = 0 by lia. apply size_empty_inv in Zstf1. fold_leibniz.
      apply elem_of_dom_2 in Hsarc1e. rewrite DOMsarc1 Zstf1 in Hsarc1e. done.
    - have [es1' Hes1'] : is_Some (omo_write_op omos1 !! (S gens1)).
      { rewrite lookup_lt_is_Some. apply lookup_lt_Some in Hgens1. rewrite omo_write_op_length in NEQ. lia. }
      iDestruct (big_sepL_lookup with "AllStrongs1") as (e1' st1' eVs1')
        "(e1'↦es1' & e1'⊒es1' & e1'↪st1' & es1'✓eVs1'' & MONO✓e1' & %eVs1'EV' & Hgens1')"; [exact Hes1'|].
      iDestruct "Hgens1'" as (omos e1'' es1'' eV1 eVs1'' st1'') "(Ms◯ & e1''↦es1'' & e1✓eV1 & es1✓eVs1'' & e1↪st1'' &
        _ & (%Hes1'' & %eVs1''EV & %NZ & _))".
      iDestruct (OmoAuth_OmoSnapOmo with "Ms●1 Ms◯") as %PREFIXomos1.
      replace (S gens1 - 1) with gens1 in Hes1'' by lia. rewrite -lookup_omo_wr_event in Hes1''.
      eapply omo_prefix_lookup_Some in Hes1'' as Hes1'''; [|done].
      rewrite lookup_omo_wr_event omo_insert_r_write_op Hgens1 in Hes1'''. inversion Hes1'''. subst es1''.
      iDestruct (OmoCW_agree_2 with "e1↦es1 e1''↦es1''") as %[_ <-]. iDestruct (OmoSnap_agree with "e1↪st1 e1↪st1''") as %<-. lia. }

  set ainfo1 := (ainfo.1.1.1.1, ainfo.1.1.1.2 ⊔ V1, ainfo.1.1.2, ainfo.1.2, cas_only).
  set sarc1' := <[e := ainfo1]> (delete e sarc1).
  iMod (ghost_map_delete with "Hγsa1 e↪ainfo") as "Hγsa1".
  iMod (ghost_map_insert e ainfo1 with "Hγsa1") as "[Hγsa1 e↪ainfo1]"; [by apply lookup_delete|].

  iMod "AU" as (????) "[M●1' [_ Commit]]".
  iMod ("Commit" $! (size st1.1.1.1) with "[$M●1' Hγb e↪ainfo1]") as "HΦ".
  { iSplit; [|iPureIntro;lia]. repeat iExists _. iFrame "HN AInv ⊒M ⊒Ms ⊒Mw e↪ainfo1 Hγb e✓eV".
    replace ainfo1.1.1.1.2 with V1; [|solve_lat]. iFrame "⊒V1". iPureIntro. split_and!; try done. }

  iMod ("Hclose" with "[-HΦ]") as "_".
  { repeat iExists _. iFrame "HN M●1 Ms●1 Mw●1 Hγsa1 Hγwa1 Hγm1 Hγb1". rewrite omo_insert_r_write_op.
    iNext. repeat iExists _. eapply (dom_same _ _ _ ainfo1) in Hsarc1e as EQdom. rewrite -EQdom.
    iFrame "AllEvents1 AllStrongs1 AllWeaks1 omos↦1 omow↦1 Hγu1 Hγd1 Hγl1 Hγul1 Hnsf1 esf1✓eVsf1 ewf1✓eVwf1".
    iFrame "⊒upds1@Vwf1 ⊒ulcks1@Vwf1 ⊒stf1s@Vsf1 ⊒stf1w@Vwf1 P2". iSplitR; last iSplitL.
    - iApply big_sepL_forall. iIntros "%i %ew %Hew".
      iDestruct (big_sepL_lookup with "AllLocks1") as (eVw zw) "[ew✓eVw [%eVwEV %COND]]"; [exact Hew|].
      iExists eVw,zw. iFrame "ew✓eVw". iPureIntro. split; [done|]. intros. apply COND in H. clear eVEV. des; [by left|].
      right. destruct (decide (e0 = e)) as [->|NEQ].
      + rewrite Hsarc1e in H. inversion H. subst ainfo0. exists e,ainfo1. rewrite lookup_insert. split; [done|]. set_solver +H0.
      + exists e0,ainfo0. rewrite lookup_insert_ne; [|done]. rewrite lookup_delete_ne; [|done]. done.
    - iApply (append_only_type_condition_update with "Hty1"); try done.
    - rewrite EQdom. eapply (sarc_update_1 _ _ _ ainfo1) in Hsarc1e as H; try done; [|solve_lat].
      eapply (sarc_update_2 _ _ _ ainfo1 _ _ _ _ lcks1 lcks1) in Hsarc1e as H0; try done. clear eVEV. des. iPureIntro. split_and!; try done.
      rewrite H0. replace ((Vbs1 ⊔ V1) ⊔ Vbw1) with ((Vbs1 ⊔ Vbw1) ⊔ V1) by solve_lat. clear -LeVbs1Vbw1. solve_lat. }

  iModIntro. wp_pures. by iApply "HΦ".
Qed.

Lemma weak_count_spec :
  weak_count_spec' code.weak_count ArcInv StrongArc.
Proof.
  intros N DISJ l tid γg q M e V0 P1 P2. iIntros "#⊒V0 SArc" (Φ) "AU".
  iDestruct "SArc" as (??????????) "(%&%&%&%&%&%& #HN & #AInv & #⊒M & #⊒Ms & #⊒Mw & #e✓eV & #⊒ainfo & Hγb & e↪ainfo &
    (-> & %Hainfo2 & %eM & %eVEV & %SubainfoM & %SubainfoMw))".
  wp_lam. wp_pures. rewrite -[Z.to_nat 1]/(1%nat).

  (* Inv access 1 *)
  iInv "AInv" as "H" "Hclose".
  iDestruct "H" as (?? γs1 ???????) "(%&%&%& %sarc1 & %warc1 & %qsa1 & %qwa1 & %alive1 & %E1 & %Es1 & %Ew1 & %omo1 & %omos1 &
    %omow1 & %stlist1 & %mos1 & %mow1 & %Mono1 & >HN' & >M●1 & >Ms●1 & >Mw●1 & >Hγsa1 & >Hγwa1 & >Hγb1 & >Hγm1 & Alive1)".
  gname_agree with "HN HN'". iClear "HN'".
  iDestruct (ghost_var_agree with "Hγb Hγb1") as %<-.

  iCombine "⊒V0 ⊒ainfo" as "⊒V0'". rewrite monPred_in_view_op. set V0' := V0 ⊔ ainfo.1.1.1.2.
  iDestruct "Alive1" as (Vbs1 Vbw1 ty1 uf1 stf1 esf1 ewf1 eVsf1 eVwf1 nsf1) "(%zwf1 & %Vsf1 & %Vwf1 & %Vp1 & %qsa1a & %qsa1b & %qu1 & %qd1 & %upds1 &
    %dgds1 & %lcks1 & %ulcks1 & >#AllEvents1 & >#AllStrongs1 & >#AllWeaks1 & >omos↦1 & >omow↦1 & >Hγu1 & >Hγd1 & >Hγl1 & >Hγul1 &
    >#AllLocks1 & [>#⊒upds1@Vwf1 >#⊒ulcks1@Vwf1] & >#esf1✓eVsf1 & >#ewf1✓eVwf1 & Hnsf1 & P2 & Hty1 & >#⊒stf1s@Vsf1 &
    >#⊒stf1w@Vwf1 & >Pures)".
  iDestruct "Pures" as %(Subuf1 & LASTesf1 & LASTewf1 & eVsf1EV & eVwf1EV & Hqsa1 & Hqwa1 & VALsarc1 & VALwarc1 & VALsarcwarc1 & SeenClone1 &
    SeenWeakClone1 & HInitWrite1 & LASTstf1 & DOMsarc1 & DOMwarc1 & EQqsa1 & Alive1 & VALeid1 & LeVbs1Vbw1 & GeVsf1 & GeVwf1 &
    SeenUpgrade1 & SeenDowngrade1 & SeenUnlock1 & LEsarc1 & LEwarc1 & VALstlist1 & LeVsf1 & EQnsf1).

  wp_apply (append_only_loc_relaxed_read with "[$Mw●1 $⊒Mw $omow↦1 $⊒V0']"); [solve_ndisj|].
  iIntros (ew1 genw1 vw1 Vw1 V1 eVw1 eVwn1) "(Pures & Mw●1 & _ & #MAXew1 & #ew1✓eVw1 & #ewn1✓eVwn1 & _ & #⊒V1 & _ & #⊒Mw1@V1 & omow↦1)".
  iDestruct "Pures" as %(Hgenw1 & eVw1EV & LeV0'V1 & eVwn1EV & eVwn1SYNC).
  iDestruct (big_sepL_lookup with "AllWeaks1") as (eVw1' zw1) "(ew1✓eVw1' & [%eVw1'EV %GEzw1] & Hgenw1)"; [exact Hgenw1|].
  iDestruct (OmoEinfo_agree with "ew1✓eVw1 ew1✓eVw1'") as %<-. rewrite eVw1EV /= in eVw1'EV. subst vw1.

  set ainfo1 := (ainfo.1.1.1.1, ainfo.1.1.1.2 ⊔ V1, ainfo.1.1.2, ainfo.1.2, cas_only).
  set sarc1' := <[e := ainfo1]> (delete e sarc1).
  iDestruct (ghost_map_lookup with "Hγsa1 e↪ainfo") as %Hsarc1e.
  iMod (ghost_map_delete with "Hγsa1 e↪ainfo") as "Hγsa1".
  iMod (ghost_map_insert e ainfo1 with "Hγsa1") as "[Hγsa1 e↪ainfo1]"; [by apply lookup_delete|].

  iMod "AU" as (????) "[M●1' [_ Commit]]".
  iMod ("Commit" $! zw1 with "[$M●1' Hγb e↪ainfo1]") as "HΦ".
  { iSplit; [|iPureIntro;lia]. repeat iExists _. iFrame "HN AInv ⊒M ⊒Ms ⊒Mw e↪ainfo1 Hγb e✓eV".
    replace ainfo1.1.1.1.2 with V1; [|solve_lat]. iFrame "⊒V1". iPureIntro. split_and!; try done. }

  iMod ("Hclose" with "[-HΦ]") as "_".
  { repeat iExists _. iFrame "HN M●1 Ms●1 Mw●1 Hγsa1 Hγwa1 Hγm1 Hγb1". rewrite omo_insert_r_write_op.
    iNext. repeat iExists _. iFrame "AllEvents1 AllStrongs1 AllWeaks1 omos↦1 omow↦1 Hγu1 Hγd1 Hγl1 Hγul1 esf1✓eVsf1 ewf1✓eVwf1 Hnsf1 P2 ⊒upds1@Vwf1
      ⊒ulcks1@Vwf1 ⊒stf1s@Vsf1 ⊒stf1w@Vwf1". iSplitR; last iSplitL.
    - iApply big_sepL_forall. iIntros "%i %ew %Hew".
      iDestruct (big_sepL_lookup with "AllLocks1") as (eVw zw) "[ew✓eVw [%eVwEV %COND]]"; [exact Hew|].
      iExists eVw,zw. iFrame "ew✓eVw". iPureIntro. split; [done|]. intros. apply COND in H. clear eVEV. des; [by left|].
      right. destruct (decide (e0 = e)) as [->|NEQ].
      + rewrite Hsarc1e in H. inversion H. subst ainfo0. exists e,ainfo1. rewrite lookup_insert. split; [done|]. set_solver +H0.
      + exists e0,ainfo0. rewrite lookup_insert_ne; [|done]. rewrite lookup_delete_ne; [|done]. done.
    - iApply (append_only_type_condition_update with "Hty1"); try done.
    - iPureIntro. eapply (sarc_update_1 _ _ _ ainfo1) in Hsarc1e as H; try done; [|solve_lat]. clear eVEV.
      eapply (sarc_update_2 _ _ _ ainfo1 _ _ _ _ lcks1 _ ulcks1) in Hsarc1e as H0; try done. des. split_and!; try done.
      rewrite H0. replace (Vbs1 ⊔ (Vbw1 ⊔ V1)) with ((Vbs1 ⊔ Vbw1) ⊔ V1) by solve_lat. clear -LeVbs1Vbw1. solve_lat. }

  iModIntro. wp_pures. by iApply "HΦ".
Qed.

Lemma try_unwrap_spec :
  try_unwrap_spec' code.try_unwrap ArcInv StrongArc FakeArc.
Proof.
  intros N DISJ l tid γg q M e V0 P1 P2. iIntros "%PasFrac #⊒V0 SArc P1" (Φ) "AU".
  iDestruct "SArc" as (??????????) "(%&%&%&%&%&%& #HN & #AInv & #⊒M & #⊒Ms & #⊒Mw & #e✓eV & #⊒ainfo & Hγb & e↪ainfo &
    (-> & %Hainfo2 & %eM & %eVEV & %SubainfoM & %SubainfoMw))".
  wp_lam. wp_bind (casʳᵉˡ(_,_,_))%E.

  (* Inv access 1 *)
  iInv "AInv" as "H" "Hclose".
  iDestruct "H" as (?? γs1 ???????) "(%&%&%& %sarc1 & %warc1 & %qsa1 & %qwa1 & %alive1 & %E1 & %Es1 & %Ew1 & %omo1 & %omos1 &
    %omow1 & %stlist1 & %mos1 & %mow1 & %Mono1 & >HN' & >M●1 & >Ms●1 & >Mw●1 & >Hγsa1 & >Hγwa1 & >Hγb1 & >Hγm1 & Alive1)".
  gname_agree with "HN HN'". iClear "HN'".
  iDestruct (ghost_var_agree with "Hγb Hγb1") as %<-.

  iDestruct (OmoEview_update with "M●1 ⊒M ⊒Mw") as (Mw') "(M●1 & #⊒Mw' & M⊢Mw' & %SubMwMw')".
  iDestruct (OmoEview_update with "M●1 ⊒M ⊒Ms") as (Ms') "(M●1 & #⊒Ms' & M⊢Ms' & %SubMsMs')".
  iCombine "⊒V0 ⊒ainfo" as "⊒V0'". rewrite monPred_in_view_op. set V0' := V0 ⊔ ainfo.1.1.1.2.
  iCombine "⊒M ⊒Ms ⊒Mw ⊒ainfo ⊒Mw' P1 AU" as "RES".
  iDestruct (view_at_intro_incl with "RES ⊒V0'") as (V0'')
    "(#⊒V0'' & %LeV0'V0'' & (#⊒M@V0'' & #⊒Ms@V0'' & #⊒Mw@V0'' & #⊒ainfo@V0'' & #⊒Mw'@V0'' & P1@V0'' & AU@V0''))".

  iDestruct "Alive1" as (Vbs1 Vbw1 ty1 uf1 stf1 esf1 ewf1 eVsf1 eVwf1 nsf1) "(%zwf1 & %Vsf1 & %Vwf1 & %Vp1 & %qsa1a & %qsa1b & %qu1 & %qd1 & %upds1 &
    %dgds1 & %lcks1 & %ulcks1 & >#AllEvents1 & >#AllStrongs1 & >#AllWeaks1 & >omos↦1 & >omow↦1 & >Hγu1 & >Hγd1 & >Hγl1 & >Hγul1 &
    >#AllLocks1 & [>#⊒upds1@Vwf1 >#⊒ulcks1@Vwf1] & >#esf1✓eVsf1 & >#ewf1✓eVwf1 & Hnsf1 & P2 & Hty1 & >#⊒stf1s@Vsf1 & >#⊒stf1w@Vwf1 & >Pures)".
  iDestruct "Pures" as %(Subuf1 & LASTesf1 & LASTewf1 & eVsf1EV & eVwf1EV & Hqsa1 & Hqwa1 & VALsarc1 & VALwarc1 & VALsarcwarc1 & SeenClone1 &
    SeenWeakClone1 & HInitWrite1 & LASTstf1 & DOMsarc1 & DOMwarc1 & EQqsa1 & Alive1 & VALeid1 & LeVbs1Vbw1 & GeVsf1 & GeVwf1 &
    SeenUpgrade1 & SeenDowngrade1 & SeenUnlock1 & LEsarc1 & LEwarc1 & VALstlist1 & LeVsf1 & EQnsf1).
  iDestruct (OmoAuth_omo_nonempty with "Ms●1") as %Nomos1.
  iDestruct (OmoSnapOmo_get with "Ms●1") as "#Ms◯1".
  iDestruct (OmoAuth_wf with "M●1") as %[OMO_GOOD1 _].
  iDestruct (OmoAuth_wf with "Ms●1") as %[OMO_GOODs1 _].
  eapply omo_stlist_length in OMO_GOOD1 as EQlenST1.
  iDestruct (OmoAuth_OmoEview with "M●1 ⊒M") as %VALM.

  iMod (rel_objectively_intro (⊒∅) tid with "[]") as "#⊒∅".
  { iApply objective_objectively. iApply monPred_in_bot. }

  wp_apply (append_only_loc_cas_only_cas _ _ _ _ _ _ _ _ _ _ _ _ _ _ ∅ with "[$Ms●1 $⊒Ms' $omos↦1 $⊒V0'']"); try done; [solve_ndisj|].
  iIntros (b1 es1 gens1 vs1 Vs1 V1 mos1' omos1' eVs1 eVsn1)
    "(Pures & #MAXes1 & #es1✓eVs1 & #esn1✓eVsn1 & Ms●1 & #⊒V1 & #⊒Ms1@V1 & omos↦1 & CASE)".
  iDestruct "Pures" as %(Eqgens1 & eVs1EV & LeV0''V1).
  iDestruct "CASE" as "[(Pures & _ & #es1=esn1 & RCOMMIT) | [Pures sVs1]]".
  { (* CAS failed, commit [UnwrapFail] event *)
    iDestruct "Pures" as %(-> & NEQvs1 & -> & Homos1' & eVsn1EV & eVsn1SYNC).

    set ainfo' := (ainfo.1.1.1.1, ainfo.1.1.1.2 ⊔ V1, ainfo.1.1.2, ainfo.1.2, cas_only).
    set sarc1' := <[e := ainfo']> (delete e sarc1).
    iDestruct (ghost_map_lookup with "Hγsa1 e↪ainfo") as %Hsarc1e.
    iMod (ghost_map_delete with "Hγsa1 e↪ainfo") as "Hγsa1".
    iMod (ghost_map_insert e ainfo' with "Hγsa1") as "[Hγsa1 e↪ainfo]"; [by apply lookup_delete|].

    have LeV0V1 : V0 ⊑ V1 by solve_lat.
    set opId := length E1.
    set M1 : eView := {[opId]} ∪ M.
    set eVop := mkOmoEvent (UnwrapFail e) V1 M1.

    (* Commit position: largest generation
        among events in current eView and corresponding event of the strong count that we've just read *)
    iDestruct (big_sepL_lookup with "AllStrongs1") as (e1 st1 eVs1')
      "(e1↦es1 & e1⊒es1 & e1↪st1 & es1✓eVs1' & MONO✓e1 & %eVs1'EV & Hgens1)"; [exact Eqgens1|].
    iDestruct (OmoEinfo_agree with "es1✓eVs1 es1✓eVs1'") as %<-.
    rewrite eVs1EV /= in eVs1'EV. inversion eVs1'EV. subst vs1.
    iDestruct (OmoAuth_OmoCW_l' with "M●1 e1↦es1") as %[eidx1 Heidx1].
    set gen1 := gen_of eidx1. (* candidate #1 *)

    iDestruct (OmoEview_latest_elem with "⊒M") as (e2) "[MAXe2 %e2IN]".
    apply VALM in e2IN as He2. eapply lookup_omo_surjective in He2 as Heidx2; [|done].
    destruct Heidx2 as [eidx2 Heidx2].
    set gen2 := gen_of eidx2. (* candidate #2 *)

    set gen := gen1 `max` gen2.
    have LEgen1gen : gen1 ≤ gen by lia.
    iAssert (⌜ size st1.1.1.1 ≠ 0 ⌝ ∗ ((⌜ gens1 = length omos1 - 1 ⌝) ∨ (∃ e1' es1' eidx1', OmoCW γg γes e1' es1' ∗
      ⌜ omo_write_op omos1 !! (gens1 + 1)%nat = Some es1' ∧ lookup_omo omo1 eidx1' = Some e1' ∧ gen < gen_of eidx1' ⌝)))%I with "[-]" as "[%NZst1 #UBgen]".
    { destruct (decide (gens1 = length omos1 - 1)) as [->|NEQ].
      { iSplit; [|by iLeft]. iIntros "%Zsz".
        replace (length omos1 - 1) with (Init.Nat.pred (length omos1)) in Eqgens1 by lia.
        rewrite omo_write_op_length -last_lookup LASTesf1 in Eqgens1. inversion Eqgens1. subst es1.
        iDestruct (OmoEinfo_agree with "esf1✓eVsf1 es1✓eVs1") as %<-.
        rewrite eVsf1EV in eVs1EV. inversion eVs1EV. subst nsf1 Vs1. rewrite Zsz in H0.
        have SZstf1 : size stf1.1.1.1 = 0 by lia.
        apply size_empty_inv in SZstf1. fold_leibniz. rewrite SZstf1 in DOMsarc1.
        apply elem_of_dom_2 in Hsarc1e. rewrite DOMsarc1 in Hsarc1e. done. }

      have [es1' Hes1'] : is_Some (omo_write_op omos1 !! (gens1 + 1)%nat).
      { rewrite lookup_lt_is_Some. apply lookup_lt_Some in Eqgens1. rewrite omo_write_op_length in NEQ. lia. }
      iDestruct (big_sepL_lookup with "AllStrongs1") as (e1' st1' eVs1')
        "(e1'↦es1' & e1'⊒es1' & e1'↪st1' & es1'✓eVs1' & MONO✓e1' & %eVs1'EV' & Hgens1')"; [exact Hes1'|].
      replace (gens1 + 1) with (S gens1) by lia.
      iDestruct "Hgens1'" as (omos1'' e1'' es1'' eV1' eVs1'' st1'')
        "(Ms◯1' & e1''↦es1'' & e1'✓eV1' & es1''✓eVs1'' & e1''↪st1'' & _ & (%Hes1'' & %eVs1''EV & %NZst1'' & %CASE))".
      iDestruct (OmoAuth_OmoSnapOmo with "Ms●1 Ms◯1'") as %PREFIXomos1.
      replace (S gens1 - 1) with gens1 in Hes1'' by lia. rewrite -lookup_omo_wr_event in Hes1''.
      eapply omo_prefix_lookup_Some in Hes1''; [|exact PREFIXomos1].
      rewrite lookup_omo_wr_event Homos1' omo_insert_r_write_op Eqgens1 in Hes1''. inversion Hes1''. subst es1''.
      iDestruct (OmoCW_agree_2 with "e1↦es1 e1''↦es1''") as %[_ <-].
      iDestruct (OmoSnap_agree with "e1↪st1 e1''↪st1''") as %<-. iSplit; [done|]. iRight.

      iDestruct (OmoAuth_OmoCW_l' with "M●1 e1'↦es1'") as %[eidx1' Heidx1'].
      iDestruct (OmoLe_get _ _ _ _ _ _ (wr_event gens1) (wr_event (gens1 + 1)) with "Ms●1") as "#es1≤es1'".
      { by rewrite lookup_omo_wr_event Homos1' omo_insert_r_write_op. }
      { by rewrite lookup_omo_wr_event Homos1' omo_insert_r_write_op. } { simpl. lia. }
      iDestruct (CWMono_acc with "Hγm1 MONO✓e1 MONO✓e1' e1↦es1 e1'↦es1' es1≤es1'") as "#e1≤e1'".
      iDestruct (OmoLe_Le with "M●1 e1≤e1'") as %LEgen; [done|done|].

      destruct (decide (gen_of eidx1 = gen_of eidx1')) as [EQgen|NEQgen].
      { (* Contradiction. Generations of two events of adjacent strong count messages cannot be the same *)
        iDestruct (OmoEq_get with "M●1") as "#e1=e1'"; [exact Heidx1|exact Heidx1'|done|].
        iDestruct (OmoSnap_agree' with "e1↪st1 e1'↪st1' e1=e1'") as %<-. destruct CASE as [[EQ _]|[EQ _]]; lia. }
      have LTgen : gen_of eidx1 < gen_of eidx1' by lia.

      destruct (le_lt_dec gen2 gen1) as [LEgen21|LTgen12].
      { iExists e1',es1',eidx1'. iFrame "e1'↦es1'". iPureIntro. replace (S gens1) with (gens1 + 1) by lia.
        split_and!; try done. lia. }

      iAssert ( (∃ es2, OmoCW γg γes e2 es2 ∗ OmoHb γg γes e2 es2 ∗ CWMonoValid γm e2)
              ∨ SeenPrevStrong γg γes (omo_write_op omos1) e2)%I with "[-]" as "#CASE".
      { destruct He2 as [eV2 HeV2].
        iDestruct (big_sepL_lookup with "AllEvents1") as "Inner"; [exact HeV2|].
        destruct (eV2.(type)); try (by iLeft); try (by iRight). }
      iDestruct "CASE" as "[(%es2 & e2↦es2 & e2⊒es2 & MONO✓e2)|He2]".
      - iDestruct (OmoHb_HbIncluded with "e2⊒es2 M⊢Ms'") as %es2Ms'; [done|].
        iDestruct (big_sepS_elem_of with "MAXes1") as "es2≤es1"; [exact es2Ms'|].
        iDestruct (CWMono_acc with "Hγm1 MONO✓e2 MONO✓e1 e2↦es2 e1↦es1 es2≤es1") as "#e2≤e1".
        iDestruct (OmoLe_Le with "M●1 e2≤e1") as %LE; [done|done|]. lia.
      - iDestruct "He2" as "[(%ef1 & %esf1' & %esf1eq & ef1≤e2 & esf1=esf1eq & ef1↦esf1 & e2⊒esf1eq & %LASTesf1')|
          (%el1 & %er1 & %esl1 & %esl1eq & %esr1 & %gensl1 & el1≤e2 & e2<er1 & esl1=esl1eq & el1↦esl1 & er1↦esr1 &
            e2⊒esl1eq & [%Hesl1 %Hesr1])]".
        + rewrite LASTesf1 in LASTesf1'. inversion LASTesf1'. subst esf1'. clear LASTesf1'.
          rewrite last_lookup -omo_write_op_length in LASTesf1.
          replace (Init.Nat.pred (length omos1)) with (length omos1 - 1) in LASTesf1 by lia.
          iDestruct (OmoHb_HbIncluded with "e2⊒esf1eq M⊢Ms'") as %esf1eqMs'; [done|].
          iDestruct (big_sepS_elem_of with "MAXes1") as "esf1eq≤es1"; [exact esf1eqMs'|].
          iDestruct (OmoEq_Le_trans with "esf1=esf1eq esf1eq≤es1") as "esf1≤es1".
          iDestruct (OmoLe_Le _ _ _ _ _ _ (wr_event (length omos1 - 1)) (wr_event gens1) with "Ms●1 esf1≤es1") as %LE.
          { by rewrite lookup_omo_wr_event Homos1' omo_insert_r_write_op. }
          { by rewrite lookup_omo_wr_event Homos1' omo_insert_r_write_op. }
          simpl in LE. apply lookup_lt_Some in Eqgens1. rewrite -omo_write_op_length in Eqgens1. lia.
        + destruct (le_lt_dec gensl1 gens1) as [LE|LT].
          * iDestruct (OmoLe_get _ _ _ _ _ _ (wr_event (gensl1 + 1)) (wr_event (gens1 + 1)) with "Ms●1") as "#esr1≤es1'".
            { by rewrite lookup_omo_wr_event Homos1' omo_insert_r_write_op. }
            { by rewrite lookup_omo_wr_event Homos1' omo_insert_r_write_op. } { simpl. lia. }
            iDestruct (big_sepL_lookup with "AllStrongs1") as (er1' str1 eVsr1) "(er1'↦esr1 & _ & _ & _ & MONO✓er1 & _)"; [exact Hesr1|].
            iDestruct (OmoCW_agree_2 with "er1↦esr1 er1'↦esr1") as %[_ <-].
            iDestruct (CWMono_acc with "Hγm1 MONO✓er1 MONO✓e1' er1↦esr1 e1'↦es1' esr1≤es1'") as "#er1≤e1'".
            iDestruct (OmoLt_Le_trans with "e2<er1 er1≤e1'") as "e2<e1'".
            iDestruct (OmoLt_Lt with "M●1 e2<e1'") as %LT; [done|done|].
            iExists e1',es1',eidx1'. iFrame "e1'↦es1'". iPureIntro. replace (S gens1) with (gens1 + 1) by lia.
            split_and!; try done. lia.
          * iDestruct (OmoHb_HbIncluded with "e2⊒esl1eq M⊢Ms'") as %esl1eqMs'; [done|].
            iDestruct (big_sepS_elem_of with "MAXes1") as "esl1eq≤es1"; [exact esl1eqMs'|].
            iDestruct (OmoEq_Le_trans with "esl1=esl1eq esl1eq≤es1") as "esl1≤es1".
            iDestruct (OmoLe_Le _ _ _ _ _ _ (wr_event gensl1) (wr_event gens1) with "Ms●1 esl1≤es1") as %LE; [..|simpl in LE; lia];
            by rewrite lookup_omo_wr_event Homos1' omo_insert_r_write_op. }

    iDestruct (OmoAuth_OmoEinfo with "M●1 e✓eV") as %HeV.
    iDestruct (OmoAuth_OmoEinfo' with "M●1 e✓eV") as %[eidx Heidx].
    have eINdom : e ∈ dom sarc1 by apply elem_of_dom_2 in Hsarc1e.
    specialize (strong_arc_persist e eidx eV _ _ _ _ _ OMO_GOOD1 Heidx HeV eVEV eINdom VALsarcwarc1) as Hstlist1.

    iAssert (⌜ gen_of eidx ≤ gen1 ⌝)%I with "[-]" as %LEgene1.
    { iDestruct (big_sepL_lookup with "AllEvents1") as "Inner"; [exact HeV|]. des;
      rewrite eVEV; iDestruct "Inner" as (es) "(e↦es & e⊒es & MONO✓e)";
      (iDestruct (OmoHb_HbIncluded with "e⊒es M⊢Ms'") as %esMs'; [done|]);
      (iDestruct (big_sepS_elem_of with "MAXes1") as "es≤es1"; [exact esMs'|]);
      iDestruct (CWMono_acc with "Hγm1 MONO✓e MONO✓e1 e↦es e1↦es1 es≤es1") as "#e≤e1";
      iDestruct (OmoLe_Le with "M●1 e≤e1") as %LE; done. }

    iDestruct (OmoAuth_OmoSnap with "M●1 e1↪st1") as %Hst1; [done|].
    eapply Hstlist1 in Hst1 as eINst1; [|done].
    have SSub : {[e]} ⊂ st1.1.1.1.
    { have Sub : {[e]} ⊆ st1.1.1.1 by clear -eINst1; set_solver.
      destruct (decide (st1.1.1.1 = {[e]})) as [EQ|NEQ]; [|set_solver +Sub NEQ].
      apply (f_equal size) in EQ. rewrite size_singleton in EQ. rewrite EQ in NEQvs1. inversion NEQvs1. lia. }

    iAssert (∀ i st, ⌜ stlist1 !! i = Some st → gen_of eidx1 ≤ i → i ≤ gen → st1.1.1.1 = st.1.1.1 ⌝)%I with "[M●1 Ms●1 Hγm1]" as %EQst1.
    { iIntros (i st) "%Hst %LE1 %LE2". iInduction LE1 as [|i] "IH" forall (st LE2 Hst).
      - rewrite Hst1 in Hst. inversion Hst. subst st. done.
      - have [st' Hst'] : is_Some (stlist1 !! i) by rewrite lookup_lt_is_Some; apply lookup_lt_Some in Hst; lia.
        iDestruct ("IH" $! st' with "[] [] M●1 Ms●1 Hγm1") as %EQst1st'; [iPureIntro; lia|done|].
        have [e' He'] : is_Some (omo_write_op omo1 !! (i + 1)%nat).
        { apply lookup_lt_is_Some. rewrite -omo_write_op_length EQlenST1. apply lookup_lt_Some in Hst. lia. }
        replace (S i) with (i + 1) in Hst by lia. rewrite -lookup_omo_wr_event in He'.
        eapply lookup_omo_event_valid in He' as HeV'; [|done]. destruct HeV' as [eV' HeV'].
        eapply omo_write_op_step in OMO_GOOD1 as STEP; try done.

        iAssert (⌜ st1.1.1.1 = st.1.1.1 ⌝ ∨
          (∃ es', OmoCW γg γes e' es' ∗ OmoHb γg γes e' es' ∗ CWMonoValid γm e'))%I with "[]" as "#CASE".
        { inversion STEP; try (iLeft; iPureIntro; subst st; rewrite EQst1st'; done);
          (iDestruct (big_sepL_lookup with "AllEvents1") as "Inner"; [exact HeV'|]);
          rewrite EVENT; iRight; subst; iFrame "Inner". }
        iDestruct "CASE" as "[%|(%es' & e'↦es' & e'⊒es' & MONO✓e')]"; [done|].

        iDestruct (OmoAuth_OmoCW_r' with "Ms●1 e'↦es'") as %[seidx' Hseidx'].
        destruct (le_lt_dec (gen_of seidx') gens1) as [LE|LT].
        { (* Contradicting case *)
          iDestruct (OmoLe_get _ _ _ _ _ _ seidx' (wr_event gens1) with "Ms●1") as "#es'≤es1".
          { done. } { by rewrite lookup_omo_wr_event Homos1' omo_insert_r_write_op. } { simpl. done. }
          iDestruct (CWMono_acc with "Hγm1 MONO✓e' MONO✓e1 e'↦es' e1↦es1 es'≤es1") as "#e'≤e1".
          iDestruct (OmoLe_Le with "M●1 e'≤e1") as %LE'; [done|done|]. simpl in LE'. lia. }

        iDestruct "UBgen" as "[%|(%er1 & %esr1 & %eidxr1 & er1↦esr1 & (%Hesr1 & %Her1 & %LT'))]".
        { apply lookup_omo_lt_Some in Hseidx'. rewrite Homos1' omo_insert_r_length in Hseidx'. lia. }

        iDestruct (big_sepL_lookup with "AllStrongs1") as (er1' str1 eVsr1) "(er1'↦esr1 & _ & _ & _ & MONO✓er1 & _)"; [exact Hesr1|].
        iDestruct (OmoCW_agree_2 with "er1↦esr1 er1'↦esr1") as %[_ <-].
        iDestruct (OmoLe_get _ _ _ _ _ _ (wr_event (gens1 + 1)) seidx' with "Ms●1") as "#esr1≤es'".
        { by rewrite lookup_omo_wr_event Homos1' omo_insert_r_write_op. } { done. } { simpl. lia. }
        iDestruct (CWMono_acc with "Hγm1 MONO✓er1 MONO✓e' er1↦esr1 e'↦es' esr1≤es'") as "#er1≤e'".
        iDestruct (OmoLe_Le with "M●1 er1≤e'") as %LE; [done|done|]. simpl in *. lia. }

    have [st Hst] : is_Some (stlist1 !! gen).
    { rewrite lookup_lt_is_Some -EQlenST1. apply lookup_omo_lt_Some in Heidx1, Heidx2. lia. }
    eapply EQst1 in Hst as EQst1st; [|done|done]. rewrite EQst1st in SSub.

    iDestruct (view_at_elim with "⊒V0'' AU@V0''") as "AU".
    iMod "AU" as (????) "[>M●1' [_ Commit]]".
    iDestruct (OmoAuth_agree with "M●1 M●1'") as %(<- & <- & <- & <-). iCombine "M●1 M●1'" as "M●1".
    iDestruct (view_at_mono_2 _ V1 with "⊒M@V0''") as "⊒M@V1"; [solve_lat|].
    iDestruct (OmoUB_into_gen with "M●1 MAXe2") as %MAXe2; [done|].
    apply (OmoUBgen_mono _ _ _ gen) in MAXe2 as MAXgen; [|lia].
    iMod (OmoAuth_insert_ro_gen with "M●1 ⊒M@V1 RCOMMIT []") as "(M●1 & #⊒M1@V1 & #opId↦esn1 & #opId↪st & #opId✓eVop & RCOMMIT)".
    { have ? : step opId eVop st st by eapply arc_step_UnwrapFail; try done; set_solver-. done. }
    iMod (OmoHb_new_2 _ _ _ _ _ _ _ _ (length Es1) ({[length Es1]} ∪ Ms') with "M●1 [] opId✓eVop") as "[M●1 #opId⊒esn1]".
    { set_solver-. } { iFrame "⊒Ms1@V1". }
    iDestruct (OmoHbToken_finish with "M●1") as "[M●1 M●1']".

    iAssert (OmoLe γg e1 opId)%I with "[-]" as "#e1≤opId".
    { have [egen Hegen] : is_Some (omo_read_op omo1 !! gen).
      { rewrite lookup_lt_is_Some -omo_read_op_length. apply lookup_omo_lt_Some in Heidx1, Heidx2. lia. }
      iApply (OmoLe_get _ _ _ _ _ _ eidx1 (ro_event gen (length egen)) with "M●1"); [..|simpl;lia].
      - eapply (lookup_omo_before_insert_r _ eidx1 _ _ (length E1)) in Hegen as Heidx1'. rewrite Heidx1'.
        rewrite decide_False; [done|]. unfold not. intros. rewrite H in Heidx1.
        rewrite lookup_omo_ro_event Hegen /= in Heidx1. apply lookup_lt_Some in Heidx1. lia.
      - rewrite lookup_omo_ro_event omo_insert_r_read_op. rewrite list_lookup_alter Hegen /= lookup_app_1_eq. done. }

    iAssert (⌜ gens1 = length omos1 - 1 ⌝ ∨
      (∃ (e1' es1' : event_id), OmoCW γg γes e1' es1' ∗ OmoLt γg opId e1' ∗
        ⌜omo_write_op omos1 !! (gens1 + 1)%nat = Some es1'⌝))%I with "[-]" as "#UBopId".
    { iDestruct "UBgen" as "[%Hgens1|(%e1' & %es1' & %eidx1' & e1'↦es1' & (%Hes1' & %Heidx1' & %LTeidx1'))]"; [by iLeft|].
      have [egen Hegen] : is_Some (omo_read_op omo1 !! gen).
      { rewrite lookup_lt_is_Some -omo_read_op_length. apply lookup_omo_lt_Some in Heidx1, Heidx2. lia. }
      iDestruct (OmoLt_get _ _ _ _ _ _ (ro_event gen (length egen)) eidx1' with "M●1") as "#opId<e1'".
      { rewrite lookup_omo_ro_event omo_insert_r_read_op list_lookup_alter Hegen /= lookup_app_1_eq. done. }
      { eapply (lookup_omo_before_insert_r _ eidx1' _ _ (length E1)) in Hegen as Heidx1''. rewrite Heidx1''.
        rewrite decide_False; [done|]. unfold not. intros. rewrite H lookup_omo_ro_event Hegen /= in Heidx1'.
        apply lookup_lt_Some in Heidx1'. lia. } { done. }
      iRight. iExists e1',es1'. iFrame "e1'↦es1' opId<e1'". done. }

    iMod ("Commit" $! false V1 _ _ _ M1 with "[$⊒V1 $M●1' $⊒M1@V1 $RCOMMIT Hγb e↪ainfo $P1@V0'']") as "HΦ".
    { iSplitR; [iPureIntro; split_and!; try done; set_solver-|]. iSplitL.
      - repeat iExists _. iFrame "HN AInv e↪ainfo ⊒Ms@V0'' ⊒Mw@V0'' e✓eV". subst ainfo'. simpl. iFrame "Hγb". iSplit.
        + iApply view_at_unfold. rewrite monPred_at_in. iPureIntro. clear -LeV0'V0'' LeV0''V1. solve_lat.
        + iPureIntro. split_and!; try done; clear -eM SubainfoM; set_solver.
      - iPureIntro. split_and!; try done. exists gen. split; [done|]. apply lookup_omo_lt_Some in Heidx1, Heidx2. lia. }

    iMod ("Hclose" with "[-HΦ]") as "_".
    { iNext. repeat iExists _. iFrame "HN M●1 Ms●1 Mw●1 Hγwa1 Hγsa1 Hγb1 Hγm1". rewrite Homos1' omo_insert_r_write_op.
      repeat iExists _. iFrame "AllStrongs1 AllWeaks1 omos↦1 omow↦1 Hγu1 Hγd1 Hγl1 Hγul1 Hnsf1 P2 ⊒upds1@Vwf1 ⊒ulcks1@Vwf1
        esf1✓eVsf1 ewf1✓eVwf1 ⊒stf1s@Vsf1 ⊒stf1w@Vwf1". iSplitR; last iSplitR; last iSplitL.
      - iApply big_sepL_snoc. iFrame "AllEvents1". simpl.
        iDestruct "UBopId" as "[%Hgens1|(%e1' & %es1' & e1'↦es1' & opId<e1' & %Hes1')]".
        + iLeft. iExists e1,es1,(length Es1). iFrame "e1≤opId es1=esn1 e1↦es1 opId⊒esn1".
          rewrite Hgens1 in Eqgens1. replace (length omos1 - 1) with (Init.Nat.pred (length omos1)) in Eqgens1 by lia.
          rewrite omo_write_op_length -last_lookup in Eqgens1. done.
        + iRight. iExists e1,e1',es1,(length Es1),es1',gens1. iFrame "e1≤opId opId<e1' es1=esn1 e1↦es1 e1'↦es1' opId⊒esn1". done.
      - iApply big_sepL_forall. iIntros (i ew) "%Hew".
        iDestruct (big_sepL_lookup with "AllLocks1") as (eVw z) "[ew✓eVw [%eVwEV %COND]]"; [exact Hew|].
        iExists eVw,z. iFrame "ew✓eVw". iPureIntro. split; [done|]. intros. apply COND in H. destruct H as [H|H]; [by left|].
        destruct H as (e' & ainfo'' & He' & e'IN). right. destruct (decide (e' = e)) as [->|NEQ].
        + rewrite Hsarc1e in He'. inversion He'. subst ainfo''.
          exists e,ainfo'. rewrite lookup_insert. split; [done|]. clear -e'IN. set_solver.
        + exists e',ainfo''. rewrite lookup_insert_ne; [|done]. rewrite lookup_delete_ne; [|done]. done.
      - iApply (append_only_type_condition_update with "Hty1"); try done.
      - iPureIntro. eapply (sarc_update_snoc_1 _ _ _ ainfo' _ _ eVop) in Hsarc1e as H; try done; [|solve_lat].
        eapply (sarc_update_snoc_2 _ _ _ ainfo' _ _ _ eVop) in Hsarc1e as H0; try done. clear eVEV. des. split_and!; try done.
        + by rewrite omo_insert_r_write_op.
        + by rewrite /ArcAlive Forall_app Forall_singleton.
        + apply EventIdValid_update; [done|]. simpl. apply VALM in eM. rewrite lookup_lt_is_Some in eM. done.
        + rewrite H0. replace ((Vbs1 ⊔ V1) ⊔ Vbw1) with ((Vbs1 ⊔ Vbw1) ⊔ V1) by solve_lat. clear -LeVbs1Vbw1. solve_lat. }

    iModIntro. wp_pures. by iApply "HΦ". }

  (* CAS success, commit [StrongDrop] event *)
  iDestruct "Pures" as %(-> & -> & ->).
  iDestruct "sVs1" as (Vm1) "((%Hmos1' & -> & %eVsn1EV & %eVsn1SYNC & %LeVs1Vm1 & %NEqVs1Vm1 & %NLeV1Vs1 &
    %NEqV0''V1 & %LeV1Vm1) & _ & #⊒Vm1 & WCOMMIT)".

  set sarc1' := delete e sarc1.
  iDestruct (ghost_map_lookup with "Hγsa1 e↪ainfo") as %Hsarc1e.
  iMod (ghost_map_delete with "Hγsa1 e↪ainfo") as "Hγsa1".

  replace (length omos1 - 1) with (Init.Nat.pred (length omos1)) in Eqgens1 by lia.
  rewrite omo_write_op_length -last_lookup LASTesf1 in Eqgens1. inversion Eqgens1. subst es1. clear Eqgens1.
  iDestruct (OmoEinfo_agree with "esf1✓eVsf1 es1✓eVs1") as %<-.
  rewrite eVsf1EV in eVs1EV. inversion eVs1EV. subst nsf1 Vs1.
  have SZstf1 : size stf1.1.1.1 = 1 by lia. rewrite SZstf1. clear H0.
  have EQstf1 : stf1.1.1.1 = {[e]}.
  { apply size_1_elem_of in SZstf1 as [x EQstf1]. fold_leibniz.
    apply elem_of_dom_2 in Hsarc1e. rewrite DOMsarc1 EQstf1 elem_of_singleton in Hsarc1e. subst x. done. }
  have EQsarc1' : sarc1' = ∅.
  { apply map_size_empty_inv. apply (f_equal size) in DOMsarc1. rewrite SZstf1 size_dom in DOMsarc1.
    rewrite map_size_delete Hsarc1e DOMsarc1. done. }

  iDestruct "Hnsf1" as "(P1@Vp1 & (P1@Vsf1 & #⊒dgds1@Vsf1 & #⊒lcks1@Vsf1) & #He0 & e0↪ainfo & Hγb' & Hγul & ->)".
  set V1' := V1 ⊔ Vm1.
  (* FIXME: The following replaces ((1 / 2)%Qp, Vp1, ∅, ∅, cas_only) into ainfo1, which is incorrect. *)
  (* set ainfo1 := ((1/2)%Qp, ainfo.1.1.1.2 ⊔ V1, ∅, ∅, cas_only). *)
  have [ainfo1 Hainfo1] : ∃ (ainfo1 : ainfo_type), ainfo1 = ((1/2)%Qp, ainfo.1.1.1.2 ⊔ V1', ∅, ∅, cas_only) by eexists.
  set warc1' := <[0:=ainfo1]> (delete 0 warc1).
  set dgds1' := dgds1 ∪ M.
  set lcks1' := lcks1 ∪ Mw.
  iDestruct (ghost_map_lookup with "Hγwa1 e0↪ainfo") as %Hwarc1e0.
  iMod (ghost_map_delete with "Hγwa1 e0↪ainfo") as "Hγwa1".
  iMod (ghost_map_insert 0 ainfo1 with "Hγwa1") as "[Hγwa1 e0↪ainfo1]"; [by rewrite lookup_delete|].
  iMod (ghost_var_update dgds1' with "Hγd1") as "[Hγd1 Hγd1']".
  iMod (ghost_var_update lcks1' with "Hγl1") as "[Hγl1 Hγl1']".

  rewrite EQstf1 in DOMsarc1. apply dom_singleton_inv_L in DOMsarc1 as [x EQsarc1].
  rewrite EQsarc1 lookup_singleton in Hsarc1e. inversion Hsarc1e. subst x.
  rewrite EQsarc1 map_fold_singleton_frac_sum /frac_sum /= in Hqsa1.

  have LeV0V1' : V0 ⊑ V1' by clear -LeV0'V0'' LeV0''V1; solve_lat.
  set opId := length E1.
  (* FIXME: Below command goes wrong *)
  (* set M1 : eView := {[opId]} ∪ (M ∪ stf1.1.2 ∪ dgds1). *)
  have [M1 HM1] : ∃ (M1 : eView), M1 = {[opId]} ∪ (M ∪ dgds1 ∪ stf1.1.2) by eexists.
  set eVop := mkOmoEvent (StrongDrop e true) V1' M1.
  set stnf1 : arc_state := ((∅, stf1.1.1.2, stf1.1.2), stf1.2).

  (* Collect P1 into full ownership *)
  have LeVp1ainfo : Vp1 ⊑ ainfo.1.1.1.2 by apply (LEsarc1 e); rewrite EQsarc1 lookup_singleton.
  iAssert (@{V1'} P1 1%Qp)%I with "[P1@Vp1 P1@Vsf1 P1@V0'']" as "P1@V1'".
  { iDestruct (view_at_mono_2 _ V1' with "P1@Vp1") as "P1@V1'".
    { clear -LeVp1ainfo LeV0'V0'' LeV0''V1. solve_lat. }
    iDestruct (view_at_mono_2 _ V1' with "P1@Vsf1") as "P1@V1''"; [solve_lat|].
    iDestruct (view_at_mono_2 _ V1' with "P1@V0''") as "P1@V1'''"; [solve_lat|].
    iCombine "P1@V1' P1@V1'' P1@V1'''" as "P1". rewrite Qp.add_assoc -EQqsa1 Qp.add_comm Hqsa1. done. }

  iCombine "Hγb Hγb1" as "Hγb1".
  replace (ainfo.1.1.1.1/2 + (qsa1/2 + qwa1/2))%Qp with (1/2 + qwa1/2)%Qp; [|by rewrite -Hqsa1 Qp.div_add_distr Qp.add_assoc].

  iAssert (|={_,_}=> @{V1'} ((emp -∗ Φ #true) ∗
    OmoAuth γg γs1 (1/2)%Qp (E1 ++ [eVop]) (omo_append_w omo1 opId []) (stlist1 ++ [stnf1]) _ ∗ OmoEinfo γg opId eVop ∗
    OmoCW γg γes opId (length Es1) ∗ OmoHb γg γes opId (length Es1) ∗ OmoSnap γg γs1 opId stnf1))%I
      with "[AU@V0'' M●1 P1@V1' Hγb' Hγul Hγd1 WCOMMIT e0↪ainfo1]" as ">(HΦ & M●1 & #opId✓eVop & #opId↦esn1 & #opId⊒esn1 & #opId↪stnf1)".
  { iDestruct "He0" as (eV0) "[e0✓eV0 %eV0EV]". iCombine "⊒M@V0'' ⊒Ms@V0'' ⊒Mw@V0'' ⊒stf1s@Vsf1 ⊒dgds1@Vsf1 M●1
      Hγb' Hγul Hγd1 e0✓eV0 P1@V1' WCOMMIT ⊒Ms1@V1 HN AInv e0↪ainfo1 ⊒lcks1@Vsf1" as "RES".
    iDestruct (view_at_objective_iff _ V1' with "RES") as "RES".
    iDestruct (view_at_mono_2 _ V1' with "AU@V0''") as "AU@V1'"; [solve_lat|].
    iAssert (@{V1'} ⊒V1')%I with "[]" as "#⊒V1'@V1'"; [done|].
    iCombine "RES AU@V1' ⊒V1'@V1'" as "RES". rewrite -view_at_fupd. iApply (view_at_mono with "RES"); [done|].

    iIntros "((#⊒M@V0'' & #⊒Ms@V0'' & #⊒Mw@V0'' & #⊒stf1s@Vsf1 & #⊒dgds1@Vsf1 &
      M●1 & Hγb' & Hγul & Hγd1 & #e0✓eV0 & P1@V1' & WCOMMIT & #⊒Ms1@V1 & #HN & #AInv & e0↪ainfo1 & #⊒lcks1@Vsf1) & AU & #⊒V1')".
    iDestruct (view_at_mono_2 _ V1' with "⊒stf1s@Vsf1") as "⊒stf1s@V1'"; [solve_lat|].
    iDestruct (view_at_mono_2 _ V1' with "⊒dgds1@Vsf1") as "⊒dgds1@V1'"; [solve_lat|].
    iDestruct (view_at_mono_2 _ V1' with "⊒M@V0''") as "⊒M@V1'"; [solve_lat|].
    iDestruct (OmoEview_union_obj with "⊒M@V1' ⊒dgds1@V1'") as "⊒dgds1'@V1'".
    iDestruct (OmoEview_union_obj with "⊒dgds1'@V1' ⊒stf1s@V1'") as "⊒M1@V1'".

    iMod "AU" as (????) "[>M●1' [_ Commit]]".
    iDestruct (OmoAuth_agree with "M●1 M●1'") as %(<- & <- & <- & <-). iCombine "M●1 M●1'" as "M●1".
    iMod (OmoAuth_insert_last with "M●1 ⊒M1@V1' WCOMMIT []") as
      "(M●1 & #⊒M1'@V1' & #opId↦esn1 & #opId✓eVop & #opId↪stnf1 & WCOMMIT)".
    { have ? : step opId eVop stf1 stnf1; [|iPureIntro; split_and!; try done].
      eapply arc_step_StrongDrop_last; try done; [|solve_lat]. subst eVop M1. simpl. set_solver-. }
    iMod (OmoHb_new_2 _ _ _ _ _ _ _ _ (length Es1) ({[length Es1]} ∪ Ms') with "M●1 [] opId✓eVop")
      as "[M●1 #opId⊒esn1]"; [set_solver-|iFrame "⊒Ms1@V1"|].
    iDestruct (OmoHbToken_finish with "M●1") as "[M●1 M●1']".

    iDestruct (view_at_mono_2 _ V1' with "⊒Mw@V0''") as "⊒Mw@V1'"; [solve_lat|].
    iDestruct (view_at_mono_2 _ V1' with "⊒lcks1@Vsf1") as "⊒lcks1@V1'"; [solve_lat|].
    iDestruct (OmoEview_union_obj with "⊒Mw@V1' ⊒lcks1@V1'") as "⊒Mw'@V1'".

    iMod ("Commit" $! true V1' _ _ _ M1 with "[$⊒V1' $M●1' $P1@V1' $WCOMMIT Hγb' Hγul Hγd1 e0↪ainfo1]") as "HΦ".
    { subst M1. iSplitR; [iPureIntro; split_and!; try done; set_solver-|]. iSplitL; [|iPureIntro; split_and!; try done; by eexists].
      do 14 iExists _. iExists opId. repeat iExists _. iFrame "HN AInv ⊒M1'@V1' ⊒Ms@V0'' ⊒Mw'@V1' e0✓eV0 opId✓eVop e0↪ainfo1".
      subst ainfo1. simpl. iFrame "Hγb' Hγul Hγd1". iSplit.
      - iApply view_at_unfold. rewrite monPred_at_in. iPureIntro. solve_lat.
      - iPureIntro. split_and!; try done; [set_solver-|by eexists|set_solver-|].
        replace (∅ ∪ ulcks1) with ulcks1 by set_solver-. rewrite elem_of_subseteq. intros.
        apply SeenUnlock1 in H. clear eVEV. des; [set_solver +H|].
        rewrite EQsarc1 lookup_singleton_Some in H. destruct H as [<- <-]. set_solver +H0 SubainfoMw. }

    iModIntro. iFrame "HΦ M●1 opId✓eVop opId↦esn1 opId⊒esn1 opId↪stnf1". }

  rewrite !view_at_objective_iff.

  iMod (CWMono_insert_last_last (wr_event (length omo1)) with "Hγm1 M●1 Ms●1 opId↦esn1")
    as "(Hγm1 & #MONO✓opId & M●1 & Ms●1)".
  { by rewrite lookup_omo_wr_event omo_append_w_write_op omo_write_op_length lookup_app_1_eq. }
  { by rewrite omo_append_w_length /= Nat.add_sub. }

  iAssert (AllStrongsInner γg γes γs1 γss γm (length (omo_write_op omos1)) (length Es1))%I with "[-]" as "#NewStrongInner".
  { iExists opId,stnf1,eVsn1. subst stnf1. rewrite eVsn1EV size_empty.
    iFrame "opId↦esn1 opId⊒esn1 opId↪stnf1 esn1✓eVsn1 MONO✓opId". iSplit; [done|].
    rewrite -omo_write_op_length. destruct (length omos1) eqn:Hlen; [done|]. rewrite -Hlen. clear Hlen n.
    rewrite last_lookup -omo_write_op_length in LASTesf1.
    replace (Init.Nat.pred (length omos1)) with (length omos1 - 1) in LASTesf1 by lia.
    iDestruct (big_sepL_lookup with "AllStrongs1") as (ef1 stf1' eVsf1')
      "(ef1↦esf1 & _ & ef1↪stf1' & esf1✓eVsf1' & _ & %eVsf1'EV & _)"; [exact LASTesf1|].
    iDestruct (OmoEinfo_agree with "esf1✓eVsf1 esf1✓eVsf1'") as %<-.
    rewrite eVsf1EV /= in eVsf1'EV. inversion eVsf1'EV.
    have EQsz : size stf1.1.1.1 = size stf1'.1.1.1 by lia. clear H0.

    iDestruct (OmoAuth_OmoCW_l with "M●1 ef1↦esf1") as %[eVf1 HeVf1].
    iDestruct (OmoEinfo_get with "M●1") as "#ef1✓eVf1"; [exact HeVf1|].
    iAssert (⌜ opId ≠ ef1 ⌝)%I with "[-]" as %NEQef1.
    { iIntros "%EQef1". subst ef1. iDestruct (OmoCW_agree_1 with "opId↦esn1 ef1↦esf1") as %[_ <-].
      rewrite -lookup_omo_wr_event in LASTesf1. eapply lookup_omo_event_valid in LASTesf1; [|done].
      rewrite lookup_lt_is_Some in LASTesf1. lia. }
    iDestruct (OmoLt_get_append_w with "M●1 ef1✓eVf1") as "#ef1<opId"; [done|].

    iExists omos1,ef1,esf1,eVop,eVsf1,stf1'. iFrame "Ms◯1 ef1↦esf1 opId✓eVop esf1✓eVsf1 ef1↪stf1' ef1<opId".
    iPureIntro. split_and!; try done; [by rewrite eVsf1EV EQsz|by rewrite -EQsz EQstf1 size_singleton|].
    right. rewrite -EQsz EQstf1 size_singleton. split; [lia|]. exists e,true. done. }

  iDestruct (AllEvents_after_strong_write_event with "AllEvents1 M●1 opId↦esn1 opId⊒esn1 MONO✓opId") as "#AllEvents1'"; [by destruct omos1|done|].

  iMod ("Hclose" with "[-HΦ]") as "_".
  { repeat iExists _. iFrame "HN M●1 Ms●1 Mw●1 Hγsa1 Hγwa1 Hγb1 Hγm1". rewrite omo_append_w_write_op.
    do 4 iExists _. iExists stnf1,(length Es1),ewf1,eVsn1,eVwf1. iExists 0,zwf1,Vm1,Vwf1,Vp1,(1/2)%Qp,(1/2)%Qp.
    iExists qu1,(1/2)%Qp,upds1,dgds1',lcks1',ulcks1.
    apply (dom_same _ _ _ ainfo1) in Hwarc1e0 as EQdomwarc1. rewrite -EQdomwarc1 lookup_insert Qp.half_half.
    iFrame "AllEvents1' AllWeaks1 omos↦1 omow↦1 Hγu1 Hγd1' Hγl1' Hγul1 esn1✓eVsn1 ewf1✓eVwf1 ⊒stf1w@Vwf1 ⊒stf1s@Vsf1
      ⊒upds1@Vwf1 ⊒ulcks1@Vwf1". destruct ty1; last first.
    { (* Weak counter cannot be in locked state *)
      iDestruct "Hty1" as %(_ & _ & (e' & ainfo' & _ & He' & EQSW) & _).
      rewrite EQsarc1 lookup_singleton_Some in He'. destruct He' as [<- <-]. rewrite Hainfo2 in EQSW. done. }
    iDestruct "Hty1" as "[_ Hty1]". iFrame "Hty1". iSplitL; last iSplitL; last iSplitL.
    - iApply big_sepL_snoc. iFrame "AllStrongs1 NewStrongInner".
    - iApply big_sepL_forall. iIntros "%i %ew %Hew".
      iDestruct (big_sepL_lookup with "AllLocks1") as (eVw z) "[ew↦eVw [%eVwEV %COND]]"; [exact Hew|].
      iExists eVw,z. iFrame "ew↦eVw". iPureIntro. split; [done|]. intros.
      apply COND in H. destruct H as [H|H]; left; [set_solver +H|].
      destruct H as (e' & ainfo' & He' & ewIN).
      rewrite EQsarc1 lookup_singleton_Some in He'. destruct He' as [<- <-].
      set_solver +ewIN SubainfoMw.
    - iRight. iRight. done.
    - iPureIntro. eapply (warc_update_snoc_1 _ _ _ ainfo1 _ _ eVop sarc1 sarc1') in Hwarc1e0 as H; try done; last first.
      { subst eVop. rewrite /= dom_delete_L. set_solver-. } { by apply delete_subseteq. } { subst ainfo1. solve_lat. } { subst ainfo1. done. }
      subst sarc1'. rewrite last_snoc EQsarc1' eVsn1EV.
      have LeainfoV1 : ainfo.1.1.1.2 ⊑ V1 by clear -LeV0'V0'' LeV0''V1; solve_lat.
      eapply (warc_update_2 _ _ _ ainfo1 V1') in Hwarc1e0 as H0; try done; [|subst ainfo1;solve_lat]. clear eVEV. des. split_and!; try done.
      + by rewrite -EQdomwarc1 in H4.
      + by rewrite EQsarc1 delete_singleton -EQdomwarc1 in H5.
      + rewrite omo_append_w_write_op lookup_app_l; [done|]. apply lookup_lt_Some in HInitWrite1. done.
      + by rewrite last_snoc.
      + subst stnf1. rewrite dom_empty_L. done.
      + by rewrite /ArcAlive Forall_app Forall_singleton.
      + apply EventIdValid_update; [done|]. simpl. apply VALM in eM. rewrite lookup_lt_is_Some in eM. done.
      + rewrite H0 map_fold_empty. replace ((Vbs1 ⊔ V1) ⊔ Vbw1) with ((Vbs1 ⊔ Vbw1) ⊔ V1) by solve_lat.
        rewrite EQsarc1 map_fold_singleton_view_join_total {1}/view_join_total in LeVbs1Vbw1.
        clear -LeVbs1Vbw1 LeVs1Vm1 LeainfoV1. solve_lat.
      + subst stnf1. simpl. solve_lat.
      + unfold SeenUpgrade. intros. destruct (decide (e0 = length E1)) as [->|NEQ].
        * rewrite lookup_app_1_eq in H9. inversion H9. subst eV0. done.
        * rewrite lookup_app_1_ne in H9; [|done]. apply SeenUpgrade1 in H9. destruct (eV0.(type)); try done.
          destruct H9 as [H9|H9]; [by left|]. right. destruct H9 as (e' & ainfo' & He' & e'IN).
          destruct (decide (e' = 0)) as [->|NEQ'].
          -- rewrite Hwarc1e0 in He'. inversion He'. subst ainfo'. exists 0,ainfo1.
             rewrite lookup_insert. split; [done|]. set_solver.
          -- exists e',ainfo'. rewrite lookup_insert_ne; [|done]. rewrite lookup_delete_ne; [|done]. done.
      + unfold SeenDowngrade. intros. destruct (decide (e0 = length E1)) as [->|NEQ].
        * rewrite lookup_app_1_eq in H9. inversion H9. subst eV0. done.
        * rewrite lookup_app_1_ne in H9; [|done]. apply SeenDowngrade1 in H9. destruct (eV0.(type)); try done.
          destruct H9 as [H9|H9]; left; [by set_solver +H9|]. destruct H9 as (e' & ainfo' & He' & e'IN).
          rewrite EQsarc1 lookup_singleton_Some in He'. destruct He' as [<- <-]. set_solver +e'IN SubainfoM.
      + unfold SeenUnlock. intros. apply SeenUnlock1 in H9. destruct H9 as [e0IN|(e' & ainfo' & He' & e0IN)]; left; [set_solver +e0IN|].
        rewrite EQsarc1 lookup_singleton_Some in He'. destruct He' as [<- <-]. set_solver +SubainfoMw e0IN.
      + rewrite /StlistValid Forall_app Forall_singleton. split; [done|]. subst stnf1. done.
      + rewrite H0 /=. solve_lat. }

  iModIntro. wp_pures. wp_apply (wp_acq_fence with "⊒Vm1"); [solve_ndisj|]. iClear "⊒Vm1". iIntros "#⊒Vm1".
  iCombine "⊒V1 ⊒Vm1" as "⊒V1'". rewrite monPred_in_view_op. iDestruct (view_at_elim with "⊒V1' HΦ") as "HΦ". wp_pures. by iApply "HΦ".
Qed.

Lemma clone_arc_spec :
  clone_arc_spec' code.clone_arc ArcInv StrongArc.
Proof.
  intros N DISJ l tid γg q M e V0 P1 P2. iIntros "%PasFrac #⊒V0 SArc" (Φ) "AU".
  iDestruct "SArc" as (??????????) "(%&%&%&%&%&%& #HN & #AInv & #⊒M & #⊒Ms & #⊒Mw & #e✓eV & #⊒ainfo & Hγb & e↪ainfo &
    (-> & %Hainfo2 & %eM & %eVEV & %SubainfoM & %SubainfoMw))".
  iLöb as "IH" forall (ainfo Hainfo2 SubainfoM SubainfoMw) "⊒ainfo". wp_lam. wp_bind (!ʳˡˣ_)%E.

  (* Inv access 1 *)
  iInv "AInv" as "H" "Hclose".
  iDestruct "H" as (?? γs1 ???????) "(%&%&%& %sarc1 & %warc1 & %qsa1 & %qwa1 & %alive1 & %E1 & %Es1 & %Ew1 & %omo1 & %omos1 &
    %omow1 & %stlist1 & %mos1 & %mow1 & %Mono1 & >HN' & >M●1 & >Ms●1 & >Mw●1 & >Hγsa1 & >Hγwa1 & >Hγb1 & >Hγm1 & Alive1)".
  gname_agree with "HN HN'". iClear "HN'".
  iDestruct (ghost_var_agree with "Hγb Hγb1") as %<-.

  iDestruct (OmoEview_update with "M●1 ⊒M ⊒Mw") as (Mw') "(M●1 & #⊒Mw' & M⊢Mw' & %SubMwMw')".
  iDestruct (OmoEview_update with "M●1 ⊒M ⊒Ms") as (Ms') "(M●1 & #⊒Ms' & M⊢Ms' & %SubMsMs')".
  iCombine "⊒V0 ⊒ainfo" as "⊒V0'". rewrite monPred_in_view_op. set V0' := V0 ⊔ ainfo.1.1.1.2.
  iCombine "⊒M ⊒Ms ⊒Mw ⊒ainfo ⊒Mw' ⊒Ms'" as "RES".
  iDestruct (view_at_intro_incl with "RES ⊒V0'") as (V0'')
    "(#⊒V0'' & %LeV0'V0'' & (#⊒M@V0'' & #⊒Ms@V0'' & #⊒Mw@V0'' & #⊒ainfo@V0'' & #⊒Mw'@V0'' & #⊒Ms'@V0''))". iClear "RES".

  iDestruct "Alive1" as (Vbs1 Vbw1 ty1 uf1 stf1 esf1 ewf1 eVsf1 eVwf1 nsf1) "(%zwf1 & %Vsf1 & %Vwf1 & %Vp1 & %qsa1a & %qsa1b & %qu1 & %qd1 & %upds1 &
    %dgds1 & %lcks1 & %ulcks1 & >#AllEvents1 & >#AllStrongs1 & >#AllWeaks1 & >omos↦1 & >omow↦1 & >Hγu1 & >Hγd1 & >Hγl1 & >Hγul1 &
    >#AllLocks1 & [>#⊒upds1@Vwf1 >#⊒ulcks1@Vwf1] & >#esf1✓eVsf1 & >#ewf1✓eVwf1 & Hnsf1 & P2 & Hty1 & >#⊒stf1s@Vsf1 & >#⊒stf1w@Vwf1 & >Pures)".
  iDestruct "Pures" as %(Subuf1 & LASTesf1 & LASTewf1 & eVsf1EV & eVwf1EV & Hqsa1 & Hqwa1 & VALsarc1 & VALwarc1 & VALsarcwarc1 & SeenClone1 &
    SeenWeakClone1 & HInitWrite1 & LASTstf1 & DOMsarc1 & DOMwarc1 & EQqsa1 & Alive1 & VALeid1 & LeVbs1Vbw1 & GeVsf1 & GeVwf1 &
    SeenUpgrade1 & SeenDowngrade1 & SeenUnlock1 & LEsarc1 & LEwarc1 & VALstlist1 & LeVsf1 & EQnsf1).

  wp_apply (append_only_loc_relaxed_read with "[$Ms●1 $⊒Ms' $omos↦1 $⊒V0'']"); [solve_ndisj|].
  iIntros (es1 gens1 vs1 Vs1 V1 eVs1 eVsn1) "(Pures & Ms●1 & RCOMMIT & #MAXes1 & #es1✓eVs1 & #esn1✓eVsn1 & #es1=esn1 & #⊒V1 & _ & #⊒Ms1@V1 & omos↦1)".
  iDestruct "Pures" as %(Hgens1 & eVs1EV & LeV0''V1 & eVsn1EV & eVsn1SYNC).

  iDestruct (big_sepL_lookup with "AllStrongs1") as (e1 st1 eVs1')
    "(e1↦es1 & e1⊒es1 & e1↪st1 & es1✓eVs1' & MONO✓e1 & %eVs1'EV & Hgens1)"; [exact Hgens1|].
  iDestruct (OmoEinfo_agree with "es1✓eVs1 es1✓eVs1'") as %<-.
  rewrite eVs1EV /= in eVs1'EV. subst vs1.

  set ainfo1 := (ainfo.1.1.1.1, ainfo.1.1.1.2 ⊔ V1, ainfo.1.1.2, ainfo.1.2, cas_only).
  set sarc1' := <[e := ainfo1]> (delete e sarc1).
  iDestruct (ghost_map_lookup with "Hγsa1 e↪ainfo") as %Hsarc1e.
  iMod (ghost_map_delete with "Hγsa1 e↪ainfo") as "Hγsa1".
  iMod (ghost_map_insert e ainfo1 with "Hγsa1") as "[Hγsa1 e↪ainfo1]"; [by apply lookup_delete|].

  iMod ("Hclose" with "[-Hγb AU M⊢Mw' M⊢Ms' e↪ainfo1]") as "_".
  { repeat iExists _. iFrame "HN M●1 Ms●1 Mw●1 Hγsa1 Hγwa1 Hγm1 Hγb1". rewrite omo_insert_r_write_op.
    iNext. repeat iExists _. eapply (dom_same _ _ _ ainfo1) in Hsarc1e as EQdom. rewrite -EQdom.
    iFrame "AllEvents1 AllStrongs1 AllWeaks1 omos↦1 omow↦1 Hγu1 Hγd1 Hγl1 Hγul1 Hnsf1 esf1✓eVsf1 ewf1✓eVwf1".
    iFrame "⊒upds1@Vwf1 ⊒ulcks1@Vwf1 ⊒stf1s@Vsf1 ⊒stf1w@Vwf1 P2". iSplitR; last iSplitL.
    - iApply big_sepL_forall. iIntros "%i %ew %Hew".
      iDestruct (big_sepL_lookup with "AllLocks1") as (eVw zw) "[ew✓eVw [%eVwEV %COND]]"; [exact Hew|].
      iExists eVw,zw. iFrame "ew✓eVw". iPureIntro. split; [done|]. intros. apply COND in H. clear eVEV. des; [by left|].
      right. destruct (decide (e0 = e)) as [->|NEQ].
      + rewrite Hsarc1e in H. inversion H. subst ainfo0. exists e,ainfo1. rewrite lookup_insert. split; [done|]. set_solver +H0.
      + exists e0,ainfo0. rewrite lookup_insert_ne; [|done]. rewrite lookup_delete_ne; [|done]. done.
    - iApply (append_only_type_condition_update with "Hty1"); try done.
    - rewrite EQdom. eapply (sarc_update_1 _ _ _ ainfo1) in Hsarc1e as H; try done; [|solve_lat].
      eapply (sarc_update_2 _ _ _ ainfo1 _ _ _ _ lcks1 lcks1) in Hsarc1e as H0; try done. clear eVEV. des. iPureIntro. split_and!; try done.
      rewrite H0. replace ((Vbs1 ⊔ V1) ⊔ Vbw1) with ((Vbs1 ⊔ Vbw1) ⊔ V1) by solve_lat. clear -LeVbs1Vbw1. solve_lat. }

  iModIntro. wp_pures. wp_bind (casʳˡˣ(_,_,_))%E.

  (* Inv access 2 *)
  iInv "AInv" as "H" "Hclose".
  iDestruct "H" as (?? γs2 ???????) "(%&%&%& %sarc2 & %warc2 & %qsa2 & %qwa2 & %alive2 & %E2 & %Es2 & %Ew2 & %omo2 & %omos2 &
    %omow2 & %stlist2 & %mos2 & %mow2 & %Mono2 & >HN' & >M●2 & >Ms●2 & >Mw●2 & >Hγsa2 & >Hγwa2 & >Hγb2 & >Hγm2 & Alive2)".
  gname_agree with "HN HN'". iClear "HN'".
  iDestruct (ghost_var_agree with "Hγb Hγb2") as %<-.

  iDestruct "Alive2" as (Vbs2 Vbw2 ty2 uf2 stf2 esf2 ewf2 eVsf2 eVwf2 nsf2) "(%zwf2 & %Vsf2 & %Vwf2 & %Vp2 & %qsa2a & %qsa2b & %qu2 & %qd2 & %upds2 &
    %dgds2 & %lcks2 & %ulcks2 & >#AllEvents2 & >#AllStrongs2 & >#AllWeaks2 & >omos↦2 & >omow↦2 & >Hγu2 & >Hγd2 & >Hγl2 & >Hγul2 &
    >#AllLocks2 & [>#⊒upds2@Vwf2 >#⊒ulcks2@Vwf2] & >#esf2✓eVsf2 & >#ewf2✓eVwf2 & Hnsf2 & P2 & Hty2 & >#⊒stf2s@Vsf2 & >#⊒stf2w@Vwf2 & >Pures)".
  iDestruct "Pures" as %(Subuf2 & LASTesf2 & LASTewf2 & eVsf2EV & eVwf2EV & Hqsa2 & Hqwa2 & VALsarc2 & VALwarc2 & VALsarcwarc2 & SeenClone2 &
    SeenWeakClone2 & HInitWrite2 & LASTstf2 & DOMsarc2 & DOMwarc2 & EQqsa2 & Alive2 & VALeid2 & LeVbs2Vbw2 & GeVsf2 & GeVwf2 &
    SeenUpgrade2 & SeenDowngrade2 & SeenUnlock2 & LEsarc2 & LEwarc2 & VALstlist2 & LeVsf2 & EQnsf2).
  iDestruct (OmoAuth_wf with "M●2") as %[OMO_GOOD2 _]. iDestruct (OmoAuth_omo_nonempty with "M●2") as %Nomo2.
  have NZomo2 : length omo2 ≠ 0 by destruct omo2.
  iDestruct (OmoAuth_wf with "Ms●2") as %[OMO_GOODs2 _]. iDestruct (OmoAuth_omo_nonempty with "Ms●2") as %Nomos2.
  have NZomos2 : length omos2 ≠ 0 by destruct omos2.
  iDestruct (OmoSnapOmo_get with "Ms●2") as "#Ms◯2". iDestruct (OmoAuth_OmoEview with "M●2 ⊒M") as %VALM.
  apply omo_stlist_length in OMO_GOODs2 as EQlenMOs2.
  iDestruct (ghost_map_lookup with "Hγsa2 e↪ainfo1") as %Hsarc2e.
  apply elem_of_dom_2 in Hsarc2e as eIN.

  (* The below is necessary for asserting [AllStrongsInner] for new strong message *)
  iDestruct (OmoAuth_OmoEinfo with "M●2 e✓eV") as %HeV.
  iDestruct (OmoAuth_OmoEinfo' with "M●2 e✓eV") as %[eidx Heidx].
  iAssert (∃ es, OmoCW γg γes e es ∗ OmoHb γg γes e es ∗ CWMonoValid γm e)%I with "[]" as (es) "(#e↦es & _ & #MONO✓e)".
  { iDestruct (big_sepL_lookup with "AllEvents2") as "Inner"; [exact HeV|]. des; rewrite eVEV; done. }
  iDestruct (OmoAuth_OmoCW_r' with "Ms●2 e↦es") as %[eidxs Heidxs].
  iDestruct (OmoLe_get _ _ _ _ _ _ eidxs (wr_event (length omos2 - 1)) with "Ms●2") as "#es≤esf2"; [done|..].
  { rewrite last_lookup -lookup_omo_wr_event -omo_write_op_length in LASTesf2.
    replace (Init.Nat.pred (length omos2)) with (length omos2 - 1) in LASTesf2 by lia. done. }
  { simpl. apply lookup_omo_lt_Some in Heidxs. lia. }
  iDestruct (big_sepL_lookup with "AllStrongs2") as (ef2 stf2' eVsf2')
    "(ef2↦esf2 & _ & ef2↪stf2' & _ & MONO✓ef2 & _)"; [rewrite last_lookup in LASTesf2;exact LASTesf2|]. clear eVsf2'.
  iDestruct (CWMono_acc with "Hγm2 MONO✓e MONO✓ef2 e↦es ef2↦esf2 es≤esf2") as "#e≤ef2".
  iDestruct (OmoAuth_OmoCW_l' with "M●2 ef2↦esf2") as %[eidxf2 Heidxf2].
  iDestruct (OmoLe_Le with "M●2 e≤ef2") as %LEeef2; [done|done|].
  iDestruct (OmoAuth_OmoSnap with "M●2 ef2↪stf2'") as %Hstf2'; [done|].
  specialize (strong_arc_persist _ _ _ _ _ _ _ _ OMO_GOOD2 Heidx HeV eVEV eIN VALsarcwarc2 _ _ Hstf2' LEeef2) as eINstf2'.
  iMod (rel_objectively_intro (⊒∅) tid with "[]") as "#⊒∅"; [iApply objective_objectively; iApply monPred_in_bot|].

  wp_apply (append_only_loc_cas_only_cas with "[$Ms●2 $⊒Ms' $omos↦2 $⊒V1]"); try done; [solve_ndisj|].
  iIntros (b2 es2 gens2 vs2 Vs2 V2 mos2' omos2' eVs2 eVsn2)
    "(Pures & #MAXes2 & #es2✓eVs2 & #esn2✓eVsn2 & Ms●2 & #⊒V2 & #⊒Ms2@V2 & omos↦2 & CASE)".
  iDestruct "Pures" as %(Eqgens2 & eVs2EV & LeV1V2).
  iDestruct "CASE" as "[(Pures & _ & #es2=esn2 & RCOMMIT) | [Pures sVs2]]".
  { (* CAS failed, retry *)
    iDestruct "Pures" as %(-> & NEQvs2 & -> & -> & eVsn2EV & eVsn2SYNC).

    set ainfo2 := (ainfo1.1.1.1.1, ainfo1.1.1.1.2 ⊔ V2, ainfo1.1.1.2, ainfo1.1.2, cas_only).
    set sarc2' := <[e := ainfo2]> (delete e sarc2).
    iMod (ghost_map_delete with "Hγsa2 e↪ainfo1") as "Hγsa2".
    iMod (ghost_map_insert e ainfo2 with "Hγsa2") as "[Hγsa2 e↪ainfo2]"; [by apply lookup_delete|].

    iMod ("Hclose" with "[-Hγb AU M⊢Mw' M⊢Ms' e↪ainfo2]") as "_".
    { repeat iExists _. iFrame "HN M●2 Ms●2 Mw●2 Hγsa2 Hγwa2 Hγm2 Hγb2". rewrite omo_insert_r_write_op.
      iNext. repeat iExists _. eapply (dom_same _ _ _ ainfo2) in Hsarc2e as EQdom. rewrite -EQdom.
      iFrame "AllEvents2 AllStrongs2 AllWeaks2 omos↦2 omow↦2 Hγu2 Hγd2 Hγl2 Hγul2 Hnsf2 esf2✓eVsf2 ewf2✓eVwf2".
      iFrame "⊒upds2@Vwf2 ⊒ulcks2@Vwf2 ⊒stf2s@Vsf2 ⊒stf2w@Vwf2 P2". iSplitR; last iSplitL.
      - iApply big_sepL_forall. iIntros "%i %ew %Hew".
        iDestruct (big_sepL_lookup with "AllLocks2") as (eVw zw) "[ew✓eVw [%eVwEV %COND]]"; [exact Hew|].
        iExists eVw,zw. iFrame "ew✓eVw". iPureIntro. split; [done|]. intros. apply COND in H. clear eVEV. des; [by left|].
        right. destruct (decide (e0 = e)) as [->|NEQ].
        + rewrite Hsarc2e in H. inversion H. subst ainfo0. exists e,ainfo2. rewrite lookup_insert. split; [done|]. set_solver +H0.
        + exists e0,ainfo0. rewrite lookup_insert_ne; [|done]. rewrite lookup_delete_ne; [|done]. done.
      - iApply (append_only_type_condition_update with "Hty2"); try done.
      - rewrite EQdom. eapply (sarc_update_1 _ _ _ ainfo2) in Hsarc2e as H; try done; [|solve_lat].
        eapply (sarc_update_2 _ _ _ ainfo2 _ _ _ _ lcks2 lcks2) in Hsarc2e as H0; try done. clear eVEV. des. iPureIntro. split_and!; try done.
        rewrite H0. replace ((Vbs2 ⊔ V2) ⊔ Vbw2) with ((Vbs2 ⊔ Vbw2) ⊔ V2) by solve_lat. clear -LeVbs2Vbw2. solve_lat. }

    iModIntro. wp_if. iApply ("IH" $! ainfo2 with "[] [] [] Hγb e↪ainfo2 AU []"); try done.
    replace ainfo2.1.1.1.2 with V2 by solve_lat. iFrame "⊒V2". }

  (* CAS success, commit [Clone e] event *)
  iDestruct "Pures" as %(-> & -> & ->).
  iDestruct "sVs2" as (Vm2) "((%Hmos2' & -> & %eVsn2EV & %eVsn2SYNC & %LeVs2Vm2 & %NEqVs2Vm2 & %NLeV2Vs2 & %NEqV1V2 & %LeV2Vm2) &
    #⊒Ms2@Vm2 & #⊒Vm2 & WCOMMIT)".
  replace (length omos2 - 1) with (Init.Nat.pred (length omos2)) in Eqgens2 by lia.
  rewrite omo_write_op_length -last_lookup LASTesf2 in Eqgens2. inversion Eqgens2. subst es2. clear Eqgens2.
  iDestruct (OmoEinfo_agree with "esf2✓eVsf2 es2✓eVs2") as %<-. rewrite eVsf2EV in eVs2EV. inversion eVs2EV. subst nsf2 Vs2.
  have NZSZstf2 : size stf2.1.1.1 ≠ 0.
  { unfold not. intros ZSZstf2. apply size_empty_inv in ZSZstf2. fold_leibniz. rewrite ZSZstf2 dom_empty_iff_L in DOMsarc2.
    rewrite DOMsarc2 in Hsarc2e. done. }
  have EQsz : size stf2.1.1.1 = S (size stf2.1.1.1 - 1) by lia. rewrite {1}EQsz. clear EQsz.

  have LeV0V2 : V0 ⊑ V2 by solve_lat.
  set opId := length E2.
  set M2 : eView := {[opId]} ∪ M.
  set eVop := mkOmoEvent (Clone e) V2 M2.
  set E2' := E2 ++ [eVop].
  set nstf2 : arc_state := ((stf2.1.1.1 ∪ {[opId]}, stf2.1.1.2, stf2.1.2), stf2.2).
  have LeVp2ainfo1 : Vp2 ⊑ ainfo1.1.1.1.2 by eapply LEsarc2.

  iMod "AU" as (????) "[>M●2' [_ Commit]]".
  iDestruct (OmoAuth_agree with "M●2 M●2'") as %(<- & <- & <- & <-).
  iCombine "M●2 M●2'" as "M●2".
  iDestruct (view_at_mono_2 _ V2 with "⊒M@V0''") as "⊒M@V2"; [solve_lat|].
  iMod (OmoAuth_insert_last with "M●2 ⊒M@V2 WCOMMIT []") as "(M●2 & #⊒M2@V2 & #opId↦esn2 & #opId✓eVop & #opId↪nstf2 & WCOMMIT)".
  { have ? : step opId eVop stf2 nstf2; [|iPureIntro; split_and!; try done].
    eapply arc_step_Clone; try done; [set_solver-|by apply elem_of_dom_2 in Hsarc2e; rewrite DOMsarc2 in Hsarc2e|].
    unfold not. intros. rewrite -DOMsarc2 in H. apply VALsarc2 in H. lia. }
  iMod (OmoHb_new_2 _ _ _ _ _ _ _ _ (length Es2) ({[length Es2]} ∪ Ms') with "M●2 [] opId✓eVop") as "[M●2 #opId⊒esn2]".
  { set_solver-. } { iFrame "⊒Ms2@V2". }
  iDestruct (OmoHbToken_finish with "M●2") as "[M●2 M●2']".

  iDestruct "Hnsf2" as "(P1@Vp2 & RES@Vsf2 & #He0 & e0↪ainfo & Hγb0 & Hγul0 & ->)".
  iDestruct (ghost_map_lookup with "Hγwa2 e0↪ainfo") as %Hwarc2e0.
  have EQqsa2a : (qsa2a/2 + qsa2a/2 = qsa2a)%Qp by rewrite -{3}(Qp.mul_div_r qsa2a 2%Qp) -Qp.add_diag.
  replace (qsa2/2 + qwa2/2)%Qp with (((qsa2a/2 + qsa2b)/2 + qwa2/2) + qsa2a/2/2)%Qp; last first.
  { rewrite EQqsa2 -{3}EQqsa2a !Qp.div_add_distr -(Qp.add_assoc (qsa2a/2/2 + qsa2a/2/2)%Qp) -(Qp.add_assoc _ (qsa2a/2/2)%Qp).
    rewrite (Qp.add_comm (qsa2a/2/2)%Qp (qsa2b/2 + qwa2/2)%Qp) !(Qp.add_assoc (qsa2a/2/2)%Qp). done. }
  iDestruct "P1@Vp2" as "[P1@Vp2 P1@Vp2']". iDestruct "Hγb2" as "[Hγb2 Hγb']".

  set ainfo2 := (ainfo1.1.1.1.1, ainfo1.1.1.1.2 ⊔ V2, ainfo1.1.1.2 ∪ {[opId]}, ainfo1.1.2, cas_only).
  set ainfo2' := ((qsa2a/2)%Qp, ainfo2.1.1.1.2, ainfo2.1.1.2, ainfo2.1.2, cas_only).
  set sarc2' := <[opId := ainfo2']> (<[e := ainfo2]> (delete e sarc2)).
  iMod (ghost_map_delete with "Hγsa2 e↪ainfo1") as "Hγsa2".
  iMod (ghost_map_insert e ainfo2 with "Hγsa2") as "[Hγsa2 e↪ainfo2]"; [by apply lookup_delete|].
  iMod (ghost_map_insert opId ainfo2' with "Hγsa2") as "[Hγsa2 opId↪ainfo2']".
  { eapply (dom_same _ _ _ ainfo2) in Hsarc2e. rewrite -not_elem_of_dom -Hsarc2e. unfold not. intros. apply VALsarc2 in H. lia. }

  have LeVp2V2 : Vp2 ⊑ V2 by clear -LeVp2ainfo1 LeV0'V0'' LeV0''V1 LeV1V2; solve_lat.
  iMod ("Commit" $! V2 nstf2 M2 (qsa2a/2)%Qp with "[$⊒V2 $M●2' $WCOMMIT e↪ainfo2 opId↪ainfo2' Hγb Hγb' $P1@Vp2']") as "HΦ".
  { iSplitL; [|iPureIntro; split_and!; try done; set_solver-]. iSplitL "e↪ainfo2 Hγb".
    - repeat iExists _. iFrame "HN AInv ⊒M2@V2 ⊒Mw@V0'' ⊒Ms@V0'' e✓eV e↪ainfo2 Hγb". iSplit.
      + iApply view_at_unfold. rewrite monPred_at_in. iPureIntro. clear -LeV0'V0'' LeV0''V1 LeV1V2. solve_lat.
      + iPureIntro. split_and!; try done; [set_solver +eM|set_solver +SubainfoM].
    - repeat iExists _. iFrame "HN AInv ⊒M2@V2 ⊒Mw@V0'' ⊒Ms@V0'' opId✓eVop opId↪ainfo2' Hγb'". iSplit.
      + iApply view_at_unfold. rewrite monPred_at_in. iPureIntro. clear -LeV0'V0'' LeV0''V1 LeV1V2. solve_lat.
      + iPureIntro. split_and!; try done; [set_solver-|by right;left;eexists|set_solver +SubainfoM]. }

  iMod (CWMono_insert_last_last (wr_event (length omo2)) with "Hγm2 M●2 Ms●2 opId↦esn2")
    as "(Hγm2 & #MONO✓opId & M●2 & Ms●2)".
  { by rewrite lookup_omo_wr_event omo_append_w_write_op omo_write_op_length lookup_app_1_eq. }
  { by rewrite omo_append_w_length /= Nat.add_sub. }

  iAssert (AllStrongsInner γg γes γs2 γss γm (length (omo_write_op omos2)) (length Es2))%I with "[-]" as "#NewStrongInner".
  { iExists opId,nstf2,eVsn2. subst nstf2. rewrite eVsn2EV -H0 size_union; last first.
    { have NIN : opId ∉ stf2.1.1.1; [|set_solver +NIN]. unfold not. intros. rewrite -DOMsarc2 in H. apply VALsarc2 in H. lia. }
    have EQsz : size stf2.1.1.1 = size st1.1.1.1 by lia. rewrite EQsz size_singleton.
    replace (Z.of_nat (size st1.1.1.1) + 1)%Z with (Z.of_nat (size st1.1.1.1 + 1)) by lia.
    iFrame "opId↦esn2 opId⊒esn2 opId↪nstf2 esn2✓eVsn2 MONO✓opId". iSplit; [done|].
    rewrite -{1}omo_write_op_length. replace (length omos2) with (S (length omos2 - 1)) by lia.
    iDestruct (big_sepL_lookup with "AllStrongs2") as (ef2' stf2'' eVsf2')
      "(ef2'↦esf2 & _ & ef2'↪stf2'' & esf2✓eVsf2' & _ & %eVsf2'EV & _)"; [rewrite last_lookup in LASTesf2;exact LASTesf2|].
    iDestruct (OmoCW_agree_2 with "ef2↦esf2 ef2'↦esf2") as %[_ <-].
    iDestruct (OmoSnap_agree with "ef2↪stf2' ef2'↪stf2''") as %<-.
    iDestruct (OmoEinfo_agree with "esf2✓eVsf2 esf2✓eVsf2'") as %<-.
    rewrite eVsf2EV /= in eVsf2'EV. inversion eVsf2'EV.
    have EQsz' : size stf2.1.1.1 = size stf2'.1.1.1 by lia. clear H1.

    iDestruct (OmoAuth_OmoCW_l with "M●2 ef2↦esf2") as %[eVf2 HeVf2].
    iDestruct (OmoEinfo_get with "M●2") as "#ef2✓eVf2"; [exact HeVf2|].
    iAssert (⌜ opId ≠ ef2 ⌝)%I with "[-]" as %NEQef2.
    { iIntros "%EQef2". subst ef2. iDestruct (OmoCW_agree_1 with "opId↦esn2 ef2↦esf2") as %[_ <-].
      rewrite last_lookup -lookup_omo_wr_event in LASTesf2. eapply lookup_omo_event_valid in LASTesf2; [|done].
      rewrite lookup_lt_is_Some in LASTesf2. lia. }
    iDestruct (OmoLt_get_append_w with "M●2 ef2✓eVf2") as "#ef2<opId"; [done|].

    iExists omos2,ef2,esf2,eVop,eVsf2,stf2'. iFrame "Ms◯2 ef2↦esf2 opId✓eVop esf2✓eVsf2 ef2↪stf2' ef2<opId". iPureIntro.
    replace (length (omo_write_op omos2) - 1) with (Init.Nat.pred (length (omo_write_op omos2))) by lia.
    rewrite -last_lookup -EQsz eVsf2EV /=. split_and!; try done; [lia|]. left. split; [lia|]. left. exists e. done. }

  iDestruct (AllEvents_after_strong_write_event with "AllEvents2 M●2 opId↦esn2 opId⊒esn2 MONO✓opId") as "#AllEvents2'"; [done|done|].
  have NEQe : e ≠ opId by unfold not; intros; subst e; apply VALsarc2 in eIN; lia.

  iMod ("Hclose" with "[-HΦ]") as "_".
  { repeat iExists _. iFrame "HN M●2 Ms●2 Mw●2 Hγsa2 Hγwa2 Hγm2 Hγb2". rewrite omo_append_w_write_op.
    iNext. do 4 iExists _. iExists nstf2,_,_,_,_,(size st1.1.1.1 + 1),_. iExists Vm2,Vwf2,Vp2. repeat iExists _.
    iFrame "AllEvents2' AllWeaks2 omos↦2 omow↦2 Hγu2 Hγd2 Hγl2 Hγul2 ⊒upds2@Vwf2 ⊒ulcks2@Vwf2 esn2✓eVsn2 ewf2✓eVwf2".
    have EQ : size st1.1.1.1 + 1 = S (size st1.1.1.1) by lia. rewrite {1}EQ. clear EQ.
    iFrame "P1@Vp2 RES@Vsf2 He0 e0↪ainfo Hγb0 Hγul0 P2 ⊒stf2s@Vsf2 ⊒stf2w@Vwf2".
    iSplitR; last iSplitR; last iSplitR; last iSplitL; try done.
    - iApply big_sepL_snoc. iFrame "AllStrongs2 NewStrongInner".
    - iApply big_sepL_forall. iIntros "%i %ew %Hew".
      iDestruct (big_sepL_lookup with "AllLocks2") as (eVw zw) "[ew✓eVw [%eVwEV %COND]]"; [exact Hew|].
      iExists eVw,zw. iFrame "ew✓eVw". iPureIntro. split; [done|]. intros. apply COND in H. clear eVEV. des; [by left|].
      right. destruct (decide (e0 = e)) as [->|NEQ].
      + rewrite Hsarc2e in H. inversion H. subst ainfo0.
        exists e,ainfo2. rewrite lookup_insert_ne; [by rewrite lookup_insert|done].
      + exists e0,ainfo0. rewrite lookup_insert_ne.
        * rewrite lookup_insert_ne; [|done]. rewrite lookup_delete_ne; [|done]. done.
        * unfold not. intros. subst e0. apply elem_of_dom_2 in H. apply VALsarc2 in H. lia.
    - destruct ty2.
      + iDestruct "Hty2" as "[[H|[(%e' & %ainfo' & %Hsarc2e' & %ewf2IN)|%ZSZ]] H']"; iFrame "H'"; [iLeft; iFrame "H"|..|lia].
        iRight. iLeft. destruct (decide (e' = e)) as [->|NEQ].
        * rewrite Hsarc2e in Hsarc2e'. inversion Hsarc2e'. subst ainfo'. iExists e,ainfo2. iPureIntro.
          rewrite lookup_insert_ne; [by rewrite lookup_insert|done].
        * iExists e',ainfo'. iPureIntro. rewrite lookup_insert_ne.
          -- rewrite lookup_insert_ne; [|done]. by rewrite lookup_delete_ne.
          -- unfold not. intros. subst e'. apply elem_of_dom_2 in Hsarc2e'. apply VALsarc2 in Hsarc2e'. lia.
      + iDestruct "Hty2" as %(H1 & H2 & H3 & H4). iPureIntro. split_and!; try done. clear eVEV. des. destruct (decide (e0 = e)) as [->|NEQ].
        * rewrite Hsarc2e in H5. inversion H5. subst ainfo0. done.
        * exists e0,ainfo0. split_and!; try done; [set_solver +H3|]. rewrite lookup_insert_ne.
          -- rewrite lookup_insert_ne; [|done]. by rewrite lookup_delete_ne.
          -- unfold not. intros. subst e0. apply elem_of_dom_2, VALsarc2 in H5. lia.
    - iPureIntro. eapply (sarc_update_1 _ _ _ ainfo2) in Hsarc2e as H; try done; [|solve_lat|set_solver-].
      eapply (sarc_update_2 _ _ _ ainfo2 _ _ _ _ lcks2 lcks2) in Hsarc2e as H1; try done; [|set_solver-].
      rewrite !last_snoc eVsn2EV /= size_union; last first.
      { have FRESH : opId ∉ stf2.1.1.1; [|set_solver +FRESH].
        unfold not. intros. rewrite -DOMsarc2 in H2. apply VALsarc2 in H2. lia. }
      rewrite size_singleton. replace (Z.of_nat (size st1.1.1.1) + 1)%Z with (Z.of_nat (size st1.1.1.1 + 1)) by lia.
      eapply (dom_same _ _ _ ainfo2) in Hsarc2e as EQdom. clear eVEV. des. split_and!; try done.
      + rewrite map_fold_insert_L; [|by apply frac_sum_wf|]; last first.
        { rewrite -not_elem_of_dom -EQdom. unfold not. intros. apply VALsarc2 in H9. lia. }
        by rewrite {1}/frac_sum /= -map_fold_init_frac_op Qp.add_assoc EQqsa2a -EQqsa2.
      + rewrite dom_insert_L /ArcsValid. intros. rewrite app_length /=.
        have [e0EQ|e0IN] : e0 = opId ∨ e0 ∈ dom (<[e := ainfo2]> (delete e sarc2)); [set_solver +H9|subst e0; lia|apply H5 in e0IN; lia].
      + unfold ArcsValid. intros. rewrite app_length /=. apply VALwarc2 in H9. lia.
      + rewrite dom_insert_L -EQdom /ArcsValid2. intros. destruct (decide (e0 = length E2)) as [->|NEQ].
        * rewrite lookup_app_1_eq in H9. inversion H9. subst eV0. done.
        * rewrite lookup_app_1_ne in H9; [|done]. apply VALsarcwarc2 in H9 as H10. destruct (eV0.(type)) eqn:HeV0; try done;
          unfold not; intros; (have [e2EQ|e2IN] : e2 = opId ∨ e2 ∈ dom sarc2; [set_solver +H11|..|done]); subst e2;
          apply VALeid2 in H9; rewrite HeV0 in H9; lia.
      + unfold SeenClone. intros. destruct (decide (e' = length E2)) as [->|NEQ].
        * rewrite lookup_app_1_eq in H10. inversion H10. subst eV0. inversion H11. subst e0.
          rewrite lookup_insert_ne in H9; [|done]. rewrite lookup_insert in H9. inversion H9. subst ainfo0. set_solver-.
        * rewrite lookup_app_1_ne in H10; [|done]. destruct (decide (e0 = opId)) as [->|NEQ'].
          { apply VALeid2 in H10. rewrite H11 in H10. lia. }
          rewrite lookup_insert_ne in H9; [|done]. destruct (decide (e0 = e)) as [->|NEQ''].
          -- rewrite lookup_insert in H9. inversion H9. subst ainfo0.
             specialize (SeenClone2 _ _ _ _ Hsarc2e H10 H11). set_solver +SeenClone2.
          -- rewrite lookup_insert_ne in H9; [|done]. rewrite lookup_delete_ne in H9; [|done]. eapply SeenClone2; try done.
      + unfold SeenWeakClone. intros. destruct (decide (e' = length E2)) as [->|NEQ].
        * rewrite lookup_app_1_eq in H10. inversion H10. subst eV0. done.
        * rewrite lookup_app_1_ne in H10; [|done]. eapply SeenWeakClone2; try done.
      + rewrite omo_append_w_write_op lookup_app_l; [done|]. rewrite -omo_write_op_length. lia.
      + rewrite dom_insert_L -EQdom DOMsarc2. set_solver-.
      + by rewrite /ArcAlive Forall_app Forall_singleton.
      + eapply EventIdValid_update; try done. simpl. apply lookup_lt_Some in HeV. done.
      + rewrite map_fold_insert_L; [rewrite H1 {1}/view_join_total|solve_lat|]; last first.
        { rewrite -not_elem_of_dom -EQdom. unfold not. intros. apply VALsarc2 in H9. lia. }
        replace ((Vbs2 ⊔ V2) ⊔ Vbw2) with ((Vbs2 ⊔ Vbw2) ⊔ V2) by solve_lat.
        have Leainfo2'V2 : ainfo2'.1.1.1.2 ⊑ V2.
        { subst ainfo2' ainfo2 ainfo1. simpl in *. clear -LeV0'V0'' LeV0''V1 LeV1V2. solve_lat. }
        have Temp : ∀ (V1 V2 V3 V4 V5 V6 : view), V1 ⊑ V3 → (((V1 ⊔ (V2 ⊔ V3)) ⊔ V4) ⊔ V5) ⊔ V6 = ((V2 ⊔ V4) ⊔ V5 ⊔ V6) ⊔ V3 by solve_lat.
        rewrite Temp; [|done]. clear -LeVbs2Vbw2 LeVs2Vm2. solve_lat.
      + solve_lat.
      + unfold SeenUpgrade. intros. destruct (decide (e0 = length E2)) as [->|NEQ].
        * rewrite lookup_app_1_eq in H9. inversion H9. subst eV0. done.
        * rewrite lookup_app_1_ne in H9; [|done]. by eapply SeenUpgrade2.
      + unfold SeenDowngrade. intros. destruct (decide (e0 = length E2)) as [->|NEQ].
        * rewrite lookup_app_1_eq in H9. inversion H9. subst eV0. done.
        * rewrite lookup_app_1_ne in H9; [|done]. apply SeenDowngrade2 in H9. destruct (eV0.(type)); try done. des; [by left|].
          right. have NEQ' : e' ≠ opId by unfold not; intros; subst e'; apply elem_of_dom_2, VALsarc2 in H9; lia.
          destruct (decide (e' = e)) as [->|NEQ''].
          -- rewrite Hsarc2e in H9. inversion H9. subst ainfo0. exists e,ainfo2. split; [|set_solver +H10].
             rewrite lookup_insert_ne; [|done]. rewrite lookup_insert. done.
          -- exists e',ainfo0. do 2 (rewrite lookup_insert_ne; [|done]). rewrite lookup_delete_ne; [|done]. done.
      + unfold SeenUnlock. intros. apply SeenUnlock2 in H9. des; [by left|]. right.
        have NEQ : e' ≠ opId by unfold not; intros; subst e'; apply elem_of_dom_2, VALsarc2 in H9; lia.
        destruct (decide (e' = e)) as [->|NEQ'].
        * rewrite Hsarc2e in H9. inversion H9. subst ainfo0. exists e,ainfo2. split; [|set_solver +H10].
          rewrite lookup_insert_ne; [|done]. by rewrite lookup_insert.
        * exists e',ainfo0. do 2 (rewrite lookup_insert_ne; [|done]). rewrite lookup_delete_ne; [|done]. done.
      + unfold ArcsSeen. intros. destruct (decide (e0 = opId)) as [->|NEQ]; last destruct (decide (e0 = e)) as [->|NEQ'].
        * rewrite lookup_insert in H9. inversion H9. subst ainfo0. solve_lat.
        * rewrite lookup_insert_ne in H9; [|done]. rewrite lookup_insert in H9. inversion H9. solve_lat.
        * do 2 (rewrite lookup_insert_ne in H9; [|done]). rewrite lookup_delete_ne in H9; [|done]. eapply LEsarc2. done.
      + rewrite /StlistValid Forall_app Forall_singleton. split; [done|]. intros. subst nstf2. simpl in *.
        apply elem_of_dom_2 in Hwarc2e0. rewrite DOMwarc2 in Hwarc2e0. done.
      + rewrite decide_False; [done|]. lia.
      + lia. }

  iModIntro. wp_pures. by iApply "HΦ".
Qed.

Lemma drop_arc_spec :
  drop_arc_spec' code.drop_arc ArcInv StrongArc FakeArc.
Proof.
  intros N DISJ l tid γg q M e V0 P1 P2. iIntros "%PasFrac #⊒V0 SArc P1" (Φ) "AU".
  iDestruct "SArc" as (??????????) "(%&%&%&%&%&%& #HN & #AInv & #⊒M & #⊒Ms & #⊒Mw & #e✓eV & #⊒ainfo & Hγb & e↪ainfo &
    (-> & %Hainfo2 & %eM & %eVEV & %SubainfoM & %SubainfoMw))".
  iLöb as "IH" forall (ainfo Hainfo2 SubainfoM SubainfoMw) "⊒ainfo". wp_lam. wp_bind (!ʳˡˣ_)%E.

  (* Inv access 1 *)
  iInv "AInv" as "H" "Hclose".
  iDestruct "H" as (?? γs1 ???????) "(%&%&%& %sarc1 & %warc1 & %qsa1 & %qwa1 & %alive1 & %E1 & %Es1 & %Ew1 & %omo1 & %omos1 &
    %omow1 & %stlist1 & %mos1 & %mow1 & %Mono1 & >HN' & >M●1 & >Ms●1 & >Mw●1 & >Hγsa1 & >Hγwa1 & >Hγb1 & >Hγm1 & Alive1)".
  gname_agree with "HN HN'". iClear "HN'".
  iDestruct (ghost_var_agree with "Hγb Hγb1") as %<-.

  iDestruct (OmoEview_update with "M●1 ⊒M ⊒Mw") as (Mw') "(M●1 & #⊒Mw' & M⊢Mw' & %SubMwMw')".
  iDestruct (OmoEview_update with "M●1 ⊒M ⊒Ms") as (Ms') "(M●1 & #⊒Ms' & M⊢Ms' & %SubMsMs')".
  iCombine "⊒V0 ⊒ainfo" as "⊒V0'". rewrite monPred_in_view_op. set V0' := V0 ⊔ ainfo.1.1.1.2.
  iCombine "⊒M ⊒Ms ⊒Mw ⊒ainfo ⊒Mw' ⊒Ms' P1 AU" as "RES".
  iDestruct (view_at_intro_incl with "RES ⊒V0'") as (V0'')
    "(#⊒V0'' & %LeV0'V0'' & (#⊒M@V0'' & #⊒Ms@V0'' & #⊒Mw@V0'' & #⊒ainfo@V0'' & #⊒Mw'@V0'' & #⊒Ms'@V0'' & P1@V0'' & AU@V0''))".

  iDestruct "Alive1" as (Vbs1 Vbw1 ty1 uf1 stf1 esf1 ewf1 eVsf1 eVwf1 nsf1) "(%zwf1 & %Vsf1 & %Vwf1 & %Vp1 & %qsa1a & %qsa1b & %qu1 & %qd1 & %upds1 &
    %dgds1 & %lcks1 & %ulcks1 & >#AllEvents1 & >#AllStrongs1 & >#AllWeaks1 & >omos↦1 & >omow↦1 & >Hγu1 & >Hγd1 & >Hγl1 & >Hγul1 &
    >#AllLocks1 & [>#⊒upds1@Vwf1 >#⊒ulcks1@Vwf1] & >#esf1✓eVsf1 & >#ewf1✓eVwf1 & Hnsf1 & P2 & Hty1 & >#⊒stf1s@Vsf1 & >#⊒stf1w@Vwf1 & >Pures)".
  iDestruct "Pures" as %(Subuf1 & LASTesf1 & LASTewf1 & eVsf1EV & eVwf1EV & Hqsa1 & Hqwa1 & VALsarc1 & VALwarc1 & VALsarcwarc1 & SeenClone1 &
    SeenWeakClone1 & HInitWrite1 & LASTstf1 & DOMsarc1 & DOMwarc1 & EQqsa1 & Alive1 & VALeid1 & LeVbs1Vbw1 & GeVsf1 & GeVwf1 &
    SeenUpgrade1 & SeenDowngrade1 & SeenUnlock1 & LEsarc1 & LEwarc1 & VALstlist1 & LeVsf1 & EQnsf1).

  wp_apply (append_only_loc_relaxed_read with "[$Ms●1 $⊒Ms' $omos↦1 $⊒V0'']"); [solve_ndisj|].
  iIntros (es1 gens1 vs1 Vs1 V1 eVs1 eVsn1) "(Pures & Ms●1 & RCOMMIT & #MAXes1 & #es1✓eVs1 & #esn1✓eVsn1 & #es1=esn1 & #⊒V1 & _ & #⊒Ms1@V1 & omos↦1)".
  iDestruct "Pures" as %(Hgens1 & eVs1EV & LeV0''V1 & eVsn1EV & eVsn1SYNC).

  iDestruct (big_sepL_lookup with "AllStrongs1") as (e1 st1 eVs1')
    "(e1↦es1 & e1⊒es1 & e1↪st1 & es1✓eVs1' & MONO✓e1 & %eVs1'EV & Hgens1)"; [exact Hgens1|].
  iDestruct (OmoEinfo_agree with "es1✓eVs1 es1✓eVs1'") as %<-.
  rewrite eVs1EV /= in eVs1'EV. subst vs1.

  set ainfo1 := (ainfo.1.1.1.1, ainfo.1.1.1.2 ⊔ V1, ainfo.1.1.2, ainfo.1.2, cas_only).
  set sarc1' := <[e := ainfo1]> (delete e sarc1).
  iDestruct (ghost_map_lookup with "Hγsa1 e↪ainfo") as %Hsarc1e.
  iMod (ghost_map_delete with "Hγsa1 e↪ainfo") as "Hγsa1".
  iMod (ghost_map_insert e ainfo1 with "Hγsa1") as "[Hγsa1 e↪ainfo1]"; [by apply lookup_delete|].

  iMod ("Hclose" with "[-Hγb AU@V0'' M⊢Mw' M⊢Ms' P1@V0'' e↪ainfo1]") as "_".
  { repeat iExists _. iFrame "HN M●1 Ms●1 Mw●1 Hγsa1 Hγwa1 Hγm1 Hγb1". rewrite omo_insert_r_write_op.
    iNext. repeat iExists _. eapply (dom_same _ _ _ ainfo1) in Hsarc1e as EQdom. rewrite -EQdom.
    iFrame "AllEvents1 AllStrongs1 AllWeaks1 omos↦1 omow↦1 Hγu1 Hγd1 Hγl1 Hγul1 Hnsf1 esf1✓eVsf1 ewf1✓eVwf1".
    iFrame "⊒upds1@Vwf1 ⊒ulcks1@Vwf1 ⊒stf1s@Vsf1 ⊒stf1w@Vwf1 P2". iSplitR; last iSplitL.
    - iApply big_sepL_forall. iIntros "%i %ew %Hew".
      iDestruct (big_sepL_lookup with "AllLocks1") as (eVw zw) "[ew✓eVw [%eVwEV %COND]]"; [exact Hew|].
      iExists eVw,zw. iFrame "ew✓eVw". iPureIntro. split; [done|]. intros. apply COND in H. clear eVEV. des; [by left|].
      right. destruct (decide (e0 = e)) as [->|NEQ].
      + rewrite Hsarc1e in H. inversion H. subst ainfo0. exists e,ainfo1. rewrite lookup_insert. split; [done|]. set_solver +H0.
      + exists e0,ainfo0. rewrite lookup_insert_ne; [|done]. rewrite lookup_delete_ne; [|done]. done.
    - iApply (append_only_type_condition_update with "Hty1"); try done.
    - rewrite EQdom. eapply (sarc_update_1 _ _ _ ainfo1) in Hsarc1e as H; try done; [|solve_lat].
      eapply (sarc_update_2 _ _ _ ainfo1 _ _ _ _ lcks1 lcks1) in Hsarc1e as H0; try done. clear eVEV. des. iPureIntro. split_and!; try done.
      rewrite H0. replace ((Vbs1 ⊔ V1) ⊔ Vbw1) with ((Vbs1 ⊔ Vbw1) ⊔ V1) by solve_lat. clear -LeVbs1Vbw1. solve_lat. }

  iModIntro. wp_pures. wp_bind (casʳᵉˡ(_,_,_))%E.

  (* Inv access 2 *)
  iInv "AInv" as "H" "Hclose".
  iDestruct "H" as (?? γs2 ???????) "(%&%&%& %sarc2 & %warc2 & %qsa2 & %qwa2 & %alive2 & %E2 & %Es2 & %Ew2 & %omo2 & %omos2 &
    %omow2 & %stlist2 & %mos2 & %mow2 & %Mono2 & >HN' & >M●2 & >Ms●2 & >Mw●2 & >Hγsa2 & >Hγwa2 & >Hγb2 & >Hγm2 & Alive2)".
  gname_agree with "HN HN'". iClear "HN'".
  iDestruct (ghost_var_agree with "Hγb Hγb2") as %<-.

  iDestruct "Alive2" as (Vbs2 Vbw2 ty2 uf2 stf2 esf2 ewf2 eVsf2 eVwf2 nsf2) "(%zwf2 & %Vsf2 & %Vwf2 & %Vp2 & %qsa2a & %qsa2b & %qu2 & %qd2 & %upds2 &
    %dgds2 & %lcks2 & %ulcks2 & >#AllEvents2 & >#AllStrongs2 & >#AllWeaks2 & >omos↦2 & >omow↦2 & >Hγu2 & >Hγd2 & >Hγl2 & >Hγul2 &
    >#AllLocks2 & [>#⊒upds2@Vwf2 >#⊒ulcks2@Vwf2] & >#esf2✓eVsf2 & >#ewf2✓eVwf2 & Hnsf2 & P2 & Hty2 & >#⊒stf2s@Vsf2 & >#⊒stf2w@Vwf2 & >Pures)".
  iDestruct "Pures" as %(Subuf2 & LASTesf2 & LASTewf2 & eVsf2EV & eVwf2EV & Hqsa2 & Hqwa2 & VALsarc2 & VALwarc2 & VALsarcwarc2 & SeenClone2 &
    SeenWeakClone2 & HInitWrite2 & LASTstf2 & DOMsarc2 & DOMwarc2 & EQqsa2 & Alive2 & VALeid2 & LeVbs2Vbw2 & GeVsf2 & GeVwf2 &
    SeenUpgrade2 & SeenDowngrade2 & SeenUnlock2 & LEsarc2 & LEwarc2 & VALstlist2 & LeVsf2 & EQnsf2).
  iDestruct (OmoAuth_wf with "M●2") as %[OMO_GOOD2 _]. iDestruct (OmoAuth_omo_nonempty with "M●2") as %Nomo2.
  have NZomo2 : length omo2 ≠ 0 by destruct omo2.
  iDestruct (OmoAuth_wf with "Ms●2") as %[OMO_GOODs2 _]. iDestruct (OmoAuth_omo_nonempty with "Ms●2") as %Nomos2.
  have NZomos2 : length omos2 ≠ 0 by destruct omos2.
  iDestruct (OmoSnapOmo_get with "Ms●2") as "#Ms◯2". iDestruct (OmoAuth_OmoEview with "M●2 ⊒M") as %VALM.

  wp_apply (append_only_loc_cas_only_cas _ _ _ _ _ _ _ _ _ _ _ _ _ _ ∅ with "[$Ms●2 $⊒Ms' $omos↦2 $⊒V1]"); try done; [solve_ndisj|].
  iIntros (b2 es2 gens2 vs2 Vs2 V2 mos2' omos2' eVs2 eVsn2)
    "(Pures & #MAXes2 & #es2✓eVs2 & #esn2✓eVsn2 & Ms●2 & #⊒V2 & #⊒Ms2@V2 & omos↦2 & CASE)".
  iDestruct "Pures" as %(Eqgens2 & eVs2EV & LeV1V2).
  iDestruct "CASE" as "[(Pures & _ & #es2=esn2 & RCOMMIT) | [Pures sVs2]]".
  { (* CAS failed, try again *)
    iDestruct "Pures" as %(-> & NEQvs2 & -> & -> & eVsn2EV & eVsn2SYNC).

    set ainfo2 := (ainfo1.1.1.1.1, ainfo1.1.1.1.2 ⊔ V2, ainfo1.1.1.2, ainfo1.1.2, cas_only).
    set sarc2' := <[e := ainfo2]> (delete e sarc2).
    iDestruct (ghost_map_lookup with "Hγsa2 e↪ainfo1") as %Hsarc2e.
    iMod (ghost_map_delete with "Hγsa2 e↪ainfo1") as "Hγsa2".
    iMod (ghost_map_insert e ainfo2 with "Hγsa2") as "[Hγsa2 e↪ainfo2]"; [by apply lookup_delete|].

    iMod ("Hclose" with "[-Hγb AU@V0'' M⊢Mw' M⊢Ms' P1@V0'' e↪ainfo2]") as "_".
    { repeat iExists _. iFrame "HN M●2 Ms●2 Mw●2 Hγsa2 Hγwa2 Hγm2 Hγb2". rewrite omo_insert_r_write_op.
      iNext. repeat iExists _. eapply (dom_same _ _ _ ainfo2) in Hsarc2e as EQdom. rewrite -EQdom.
      iFrame "AllEvents2 AllStrongs2 AllWeaks2 omos↦2 omow↦2 Hγu2 Hγd2 Hγl2 Hγul2 Hnsf2 esf2✓eVsf2 ewf2✓eVwf2".
      iFrame "⊒upds2@Vwf2 ⊒ulcks2@Vwf2 ⊒stf2s@Vsf2 ⊒stf2w@Vwf2 P2". iSplitR; last iSplitL.
      - iApply big_sepL_forall. iIntros "%i %ew %Hew".
        iDestruct (big_sepL_lookup with "AllLocks2") as (eVw zw) "[ew✓eVw [%eVwEV %COND]]"; [exact Hew|].
        iExists eVw,zw. iFrame "ew✓eVw". iPureIntro. split; [done|]. intros. apply COND in H. clear eVEV. des; [by left|].
        right. destruct (decide (e0 = e)) as [->|NEQ].
        + rewrite Hsarc2e in H. inversion H. subst ainfo0. exists e,ainfo2. rewrite lookup_insert. split; [done|]. set_solver +H0.
        + exists e0,ainfo0. rewrite lookup_insert_ne; [|done]. rewrite lookup_delete_ne; [|done]. done.
      - iApply (append_only_type_condition_update with "Hty2"); try done.
      - rewrite EQdom. eapply (sarc_update_1 _ _ _ ainfo2) in Hsarc2e as H; try done; [|solve_lat].
        eapply (sarc_update_2 _ _ _ ainfo2 _ _ _ _ lcks2 lcks2) in Hsarc2e as H0; try done. clear eVEV. des. iPureIntro. split_and!; try done.
        rewrite H0. replace ((Vbs2 ⊔ V2) ⊔ Vbw2) with ((Vbs2 ⊔ Vbw2) ⊔ V2) by solve_lat. clear -LeVbs2Vbw2. solve_lat. }

    iModIntro. wp_if. iDestruct (view_at_elim with "⊒V0'' AU@V0''") as "AU".
    iDestruct (view_at_elim with "⊒V0'' P1@V0''") as "P1".
    iApply ("IH" $! ainfo2 with "[] [] [] Hγb e↪ainfo2 P1 AU []"); try done.
    replace ainfo2.1.1.1.2 with V2 by solve_lat. iFrame "⊒V2". }

  (* CAS success *)
  iDestruct "Pures" as %(-> & -> & ->).
  iDestruct "sVs2" as (Vm2) "((%Hmos2' & -> & %eVsn2EV & %eVsn2SYNC & %LeVs2Vm2 & %NEqVs2Vm2 & %NLeV2Vs2 & %NEqV1V2 & %LeV2Vm2) &
    #⊒Ms2@Vm2 & #⊒Vm2 & WCOMMIT)".
  replace (length omos2 - 1) with (Init.Nat.pred (length omos2)) in Eqgens2 by lia.
  rewrite omo_write_op_length -last_lookup LASTesf2 in Eqgens2. inversion Eqgens2. subst es2. clear Eqgens2.
  iDestruct (OmoEinfo_agree with "esf2✓eVsf2 es2✓eVs2") as %<-. rewrite eVsf2EV in eVs2EV. inversion eVs2EV. subst nsf2 Vs2.
  iDestruct (ghost_map_lookup with "Hγsa2 e↪ainfo1") as %Hsarc2e.
  have NZSZstf2 : size stf2.1.1.1 ≠ 0.
  { unfold not. intros ZSZstf2. apply size_empty_inv in ZSZstf2. fold_leibniz. rewrite ZSZstf2 dom_empty_iff_L in DOMsarc2.
    rewrite DOMsarc2 in Hsarc2e. done. }
  have EQsz : size stf2.1.1.1 = S (size stf2.1.1.1 - 1) by lia. rewrite {1}EQsz. clear EQsz.

  destruct (decide (size stf2.1.1.1 = 1)) as [EqSZstf2|NEqSZstf2].
  - (* Current StrongArc is the last one. Commit [StrongDrop e true] *)
    set V2' := V2 ⊔ Vm2.
    set opId := length E2.
    set M2 : eView := {[opId]} ∪ (M ∪ stf2.1.2 ∪ dgds2).
    set eVop := mkOmoEvent (StrongDrop e true) V2' M2.
    set E2' := E2 ++ [eVop].
    set nstf2 : arc_state := ((∅, stf2.1.1.2, stf2.1.2), stf2.2).
    have LeVp2ainfo1 : Vp2 ⊑ ainfo1.1.1.1.2 by eapply LEsarc2.

    (* Collect all StrongArc fractions *)
    apply size_1_elem_of in EqSZstf2 as [x Hstf2]. fold_leibniz.
    rewrite Hstf2 in DOMsarc2. apply dom_singleton_inv_L in DOMsarc2 as [x' Hsarc2].
    rewrite Hsarc2 lookup_singleton_Some in Hsarc2e. destruct Hsarc2e as [-> ->].
    rewrite Hsarc2 map_fold_singleton_frac_sum /frac_sum /= in Hqsa2.

    iDestruct "Hnsf2" as "(P1@Vp2 & (P1@Vsf2 & #⊒dgds2@Vsf2 & #⊒lcks2@Vsf2) & (%eV0 & #e0✓eV0 & %eV0EV) & e0↪ainfo & Hγb' & Hγul' & ->)".
    iDestruct (ghost_map_lookup with "Hγwa2 e0↪ainfo") as %Hwarc2e0.
    iAssert (@{V2'} P1 1%Qp)%I with "[P1@V0'' P1@Vp2 P1@Vsf2]" as "P1@V2'".
    { iDestruct (view_at_mono_2 _ V2' with "P1@Vp2") as "P1@V2'a"; [solve_lat|].
      iDestruct (view_at_mono_2 _ V2' with "P1@Vsf2") as "P1@V2'b"; [solve_lat|].
      iDestruct (view_at_mono_2 _ V2' with "P1@V0''") as "P1@V2'c"; [solve_lat|].
      iCombine "P1@V2'a P1@V2'b P1@V2'c" as "P1@V2'". rewrite Qp.add_assoc -EQqsa2 Qp.add_comm Hqsa2. iFrame. }

    set lcks2' := lcks2 ∪ Mw.
    set dgds2' := dgds2 ∪ M.
    iMod (ghost_var_update lcks2' with "Hγl2") as "[Hγl2 _]".
    iMod (ghost_var_update dgds2' with "Hγd2") as "[Hγd2 Hγd]".

    set ainfo2 := ((1/2)%Qp, ainfo1.1.1.1.2 ⊔ V2', ainfo1.1.1.2, ainfo1.1.2 ∪ lcks2, cas_only).
    set warc2' := <[0 := ainfo2]> (delete 0 warc2).
    set sarc2' := delete e sarc2.
    iMod (ghost_map_delete with "Hγwa2 e0↪ainfo") as "Hγwa2".
    iMod (ghost_map_insert 0 ainfo2 with "Hγwa2") as "[Hγwa2 e0↪ainfo2]"; [by apply lookup_delete|].
    iMod (ghost_map_delete with "Hγsa2 e↪ainfo1") as "Hγsa2".
    iCombine "Hγb2 Hγb" as "Hγb2". replace (qsa2/2 + qwa2/2 + ainfo.1.1.1.1/2)%Qp with (1/2 + qwa2/2)%Qp; last first.
    { rewrite -Qp.add_assoc (Qp.add_comm _ (ainfo.1.1.1.1/2)%Qp) Qp.add_assoc -(Qp.div_add_distr qsa2 ainfo.1.1.1.1).
      rewrite (Qp.add_comm _ ainfo.1.1.1.1) Hqsa2. done. }

    iAssert (|={_,_}=> @{V2'} ((emp -∗ Φ #true) ∗ OmoAuth γg γs2 (1/2)%Qp E2' (omo_append_w omo2 opId []) (stlist2 ++ [nstf2]) _ ∗
        OmoEinfo γg opId eVop ∗ OmoCW γg γes opId (length Es2) ∗ OmoHb γg γes opId (length Es2) ∗ OmoSnap γg γs2 opId nstf2))%I
          with "[AU@V0'' M●2 e0↪ainfo2 Hγb' Hγul' Hγd P1@V2' WCOMMIT]" as ">(HΦ & M●2 & #opId✓eVop & #opId↦esn2 & #opId⊒esn2 & #opId↪nstf2)".
    { iAssert (@{V2'} ⊒V2')%I with "[]" as "#⊒V2'@V2'"; [done|].
      iCombine "M●2 e0↪ainfo2 Hγb' Hγul' Hγd WCOMMIT P1@V2' ⊒M@V0'' ⊒Mw@V0'' ⊒Ms@V0'' ⊒stf2s@Vsf2 ⊒lcks2@Vsf2 ⊒Ms2@V2 ⊒dgds2@Vsf2 e0✓eV0 HN AInv" as "RES".
      iDestruct (view_at_objective_iff _ V2' with "RES") as "RES".
      iDestruct (view_at_mono_2 _ V2' with "AU@V0''") as "AU@V2'"; [solve_lat|].
      iCombine "AU@V2' ⊒V2'@V2' RES" as "RES". rewrite -view_at_fupd. iApply (view_at_mono with "RES"); [done|].

      iIntros "(AU & #⊒V2' & (M●2 & e0↪ainfo2 & Hγb' & Hγul' & Hγd & WCOMMIT & P1@V2' & #⊒M@V0'' & #⊒Mw@V0''
        & #⊒Ms@V0'' & #⊒stf2s@Vsf2 & #⊒lcks2@Vsf2 & #⊒Ms2@V2 & #⊒dgds2@Vsf2 & #e0✓eV0 & #HN & #AInv))".
      iDestruct (view_at_mono_2 _ V2' with "⊒M@V0''") as "⊒M@V2'"; [solve_lat|].
      iDestruct (view_at_mono_2 _ V2' with "⊒stf2s@Vsf2") as "⊒stf2s@V2'"; [solve_lat|].
      iDestruct (view_at_mono_2 _ V2' with "⊒lcks2@Vsf2") as "⊒lcks2@V2'"; [solve_lat|].
      iDestruct (view_at_mono_2 _ V2' with "⊒dgds2@Vsf2") as "⊒dgds2@V2'"; [solve_lat|].
      iDestruct (view_at_mono_2 _ V2' with "⊒Mw@V0''") as "⊒Mw@V2'"; [solve_lat|].
      iDestruct (OmoEview_union_obj with "⊒M@V2' ⊒stf2s@V2'") as "⊒M'@V2'".
      iDestruct (OmoEview_union_obj with "⊒M'@V2' ⊒dgds2@V2'") as "⊒M''@V2'".
      iDestruct (OmoEview_union_obj with "⊒Mw@V2' ⊒lcks2@V2'") as "⊒Mw'@V2'".

      iMod "AU" as (????) "[>M●2' [_ Commit]]".
      iDestruct (OmoAuth_agree with "M●2 M●2'") as %(<- & <- & <- & <-). iCombine "M●2 M●2'" as "M●2".
      iMod (OmoAuth_insert_last with "M●2 ⊒M''@V2' WCOMMIT []") as "(M●2 & #⊒M2@V2' & #opId↦esn2 & #opId✓eVop & #eVop↪nstf2 & WCOMMIT)".
      { have ? : step opId eVop stf2 nstf2; [|done]. eapply arc_step_StrongDrop_last; try done; [set_solver-|solve_lat]. }
      iMod (OmoHb_new_2 _ _ _ _ _ _ _ _ (length Es2) ({[length Es2]} ∪ Ms') with "M●2 [] opId✓eVop") as "[M●2 #opId⊒esn2]".
      { set_solver-. } { iFrame "⊒Ms2@V2". }
      iDestruct (OmoHbToken_finish with "M●2") as "[M●2 M●2']".

      iMod ("Commit" $! true V2' nstf2 M2 with "[$⊒V2' $M●2' $WCOMMIT $P1@V2' e0↪ainfo2 Hγb' Hγul' Hγd]") as "HΦ".
      { iSplitR; [iPureIntro; split_and!; try done; try solve_lat; set_solver-|].
        do 14 iExists _. iExists opId,eV0,eVop. repeat iExists _.
        iFrame "HN AInv ⊒M2@V2' ⊒Ms@V0'' ⊒Mw'@V2' e0✓eV0 opId✓eVop e0↪ainfo2 Hγb' Hγul' Hγd". iSplit.
        - iApply view_at_unfold. rewrite monPred_at_in. iPureIntro. clear -LeV0'V0'' LeV0''V1 LeV1V2. solve_lat.
        - iPureIntro. split_and!; try done; [set_solver-|by exists e|set_solver +SubainfoM|].
          subst ainfo2 ainfo1. simpl in *. have Sub : ulcks2 ⊆ ainfo.1.2 ∪ lcks2; [|set_solver +SubainfoMw Sub].
          rewrite elem_of_subseteq. intros. apply SeenUnlock2 in H. clear eVEV. des; [set_solver +H|].
          rewrite Hsarc2 lookup_singleton_Some in H. destruct H as [<- <-]. simpl in *. set_solver +H1. }

      iModIntro. iFrame "HΦ M●2 opId✓eVop opId↦esn2 opId⊒esn2 eVop↪nstf2". }

    rewrite !view_at_objective_iff.

    iMod (CWMono_insert_last_last (wr_event (length omo2)) with "Hγm2 M●2 Ms●2 opId↦esn2")
      as "(Hγm2 & #MONO✓opId & M●2 & Ms●2)".
    { by rewrite lookup_omo_wr_event omo_append_w_write_op omo_write_op_length lookup_app_1_eq. }
    { by rewrite omo_append_w_length /= Nat.add_sub. }

    iAssert (AllStrongsInner γg γes γs2 γss γm (length (omo_write_op omos2)) (length Es2))%I with "[-]" as "#NewStrongInner".
    { iExists opId,nstf2,eVsn2. subst nstf2. rewrite eVsn2EV -H0 Hstf2 size_singleton size_empty.
      replace (Z.of_nat 1 - 1)%Z with (Z.of_nat 0) by lia. iFrame "opId↦esn2 opId⊒esn2 opId↪nstf2 esn2✓eVsn2 MONO✓opId". iSplit; [done|].
      rewrite -{1}omo_write_op_length. replace (length omos2) with (S (length omos2 - 1)) by lia.
      iDestruct (big_sepL_lookup with "AllStrongs2") as (ef2 stf2' eVsf2')
        "(ef2↦esf2 & _ & ef2↪stf2' & esf2✓eVsf2' & _ & %eVsf2'EV & _)"; [rewrite last_lookup in LASTesf2;exact LASTesf2|].
      iDestruct (OmoEinfo_agree with "esf2✓eVsf2 esf2✓eVsf2'") as %<-.
      rewrite eVsf2EV /= in eVsf2'EV. inversion eVsf2'EV.
      have EQsz : size stf2.1.1.1 = size stf2'.1.1.1 by lia. clear H1.

      iDestruct (OmoAuth_OmoCW_l with "M●2 ef2↦esf2") as %[eVf2 HeVf2].
      iDestruct (OmoEinfo_get with "M●2") as "#ef2✓eVf2"; [exact HeVf2|].
      iAssert (⌜ opId ≠ ef2 ⌝)%I with "[-]" as %NEQef2.
      { iIntros "%EQef2". subst ef2. iDestruct (OmoCW_agree_1 with "opId↦esn2 ef2↦esf2") as %[_ <-].
        rewrite last_lookup -lookup_omo_wr_event in LASTesf2. eapply lookup_omo_event_valid in LASTesf2; [|done].
        rewrite lookup_lt_is_Some in LASTesf2. lia. }
      iDestruct (OmoLt_get_append_w with "M●2 ef2✓eVf2") as "#ef2<opId"; [done|].

      iExists omos2,ef2,esf2,eVop,eVsf2,stf2'. iFrame "Ms◯2 ef2↦esf2 opId✓eVop esf2✓eVsf2 ef2↪stf2' ef2<opId". iPureIntro.
      replace (length (omo_write_op omos2) - 1) with (Init.Nat.pred (length (omo_write_op omos2))) by lia.
      rewrite -last_lookup -EQsz eVsf2EV /=. split_and!; try done. right. rewrite Hstf2 size_singleton. split; [lia|]. by exists e,true. }

    iDestruct (AllEvents_after_strong_write_event with "AllEvents2 M●2 opId↦esn2 opId⊒esn2 MONO✓opId") as "#AllEvents2'"; [done|done|].

    iMod ("Hclose" with "[-HΦ]") as "_".
    { repeat iExists _. iFrame "HN M●2 Ms●2 Mw●2 Hγsa2 Hγwa2 Hγm2 Hγb2". rewrite omo_append_w_write_op.
      iNext. do 4 iExists _. iExists nstf2,_,_,_,_,0,_. iExists Vm2,Vwf2,Vp2,(1/2)%Qp,(1/2)%Qp. repeat iExists _.
      eapply (dom_same _ _ _ ainfo2) in Hwarc2e0 as EQdom. rewrite -EQdom lookup_insert.
      iFrame "AllEvents2' AllWeaks2 omos↦2 omow↦2 Hγu2 Hγd2 Hγl2 Hγul2 esn2✓eVsn2 ewf2✓eVwf2".
      iFrame "⊒upds2@Vwf2 ⊒ulcks2@Vwf2 ⊒stf2s@Vsf2 ⊒stf2w@Vwf2". iSplitR; last iSplitR; last iSplitL.
      - iApply big_sepL_snoc. iFrame "AllStrongs2 NewStrongInner".
      - rewrite Hsarc2 delete_singleton. iApply big_sepL_forall. iIntros "%i %ew %Hew".
        iDestruct (big_sepL_lookup with "AllLocks2") as (eVw zw) "[ew✓eVw [%eVwEV %COND]]"; [exact Hew|].
        iExists eVw,zw. iFrame "ew✓eVw". iPureIntro. split; [done|]. intros. apply COND in H. clear eVEV. des; [by left;set_solver +H|].
        rewrite lookup_singleton_Some in H. destruct H as [<- <-]. left. set_solver +H1 SubainfoMw.
      - destruct ty2.
        + iDestruct "Hty2" as "[[H|[(%e' & %ainfo' & %Hsarc2e' & %ewf2IN)|%ZSZ]] H']"; iFrame "H'"; (by iRight; iRight).
        + iDestruct "Hty2" as %(H1 & H2 & H3 & H4). exfalso. clear eVEV. des. rewrite Hsarc2 lookup_singleton_Some in H5.
          destruct H5 as [<- <-]. subst ainfo1. done.
      - iPureIntro. eapply (warc_update_snoc_1 _ _ _ ainfo2 _ _ eVop sarc2 sarc2') in Hwarc2e0 as H; try done; last first.
        { subst sarc2'. rewrite Hsarc2 delete_singleton dom_empty_L /=. done. } { apply delete_subseteq. } { simpl. solve_lat. }
        eapply (warc_update_2 _ _ _ ainfo2 V2') in Hwarc2e0 as H1; try done; [|solve_lat].
        rewrite !last_snoc eVsn2EV -H0 Hstf2 size_singleton !EQdom Qp.half_half. replace (Z.of_nat 1 - 1)%Z with (Z.of_nat 0) by lia.
        clear eVEV. des. split_and!; try done.
        + by rewrite Hsarc2 delete_singleton map_fold_empty.
        + rewrite omo_append_w_write_op lookup_app_1_ne; [done|]. rewrite -omo_write_op_length. lia.
        + by rewrite Hsarc2 delete_singleton dom_empty_L.
        + by rewrite /ArcAlive Forall_app Forall_singleton.
        + eapply EventIdValid_update; try done. simpl. apply VALM in eM. rewrite lookup_lt_is_Some in eM. done.
        + rewrite H1. rewrite (map_fold_delete_L _ _ e ainfo1 sarc2) in LeVbs2Vbw2; [|solve_lat|by rewrite Hsarc2 lookup_singleton].
          replace ((Vbs2 ⊔ V2) ⊔ Vbw2) with ((Vbs2 ⊔ Vbw2) ⊔ V2) by solve_lat.
          replace (((view_join_total e ainfo1 (map_fold view_join_total Vp2 (delete e sarc2)) ⊔ map_fold view_join_total Vp2 warc2) ⊔ Vsf2) ⊔ Vwf2) with
            (((map_fold view_join_total Vp2 (delete e sarc2) ⊔ map_fold view_join_total Vp2 warc2) ⊔ Vsf2) ⊔ Vwf2 ⊔ V1) in LeVbs2Vbw2; [|solve_lat].
          replace (((map_fold view_join_total Vp2 (delete e sarc2) ⊔ (map_fold view_join_total Vp2 warc2 ⊔ V2')) ⊔ Vm2) ⊔ Vwf2) with
            ((((map_fold view_join_total Vp2 (delete e sarc2) ⊔ map_fold view_join_total Vp2 warc2) ⊔ Vm2) ⊔ Vwf2) ⊔ V2'); [|solve_lat].
          have LE : Vbs2 ⊔ Vbw2 ⊑ ((map_fold view_join_total Vp2 (delete e sarc2) ⊔ map_fold view_join_total Vp2 warc2) ⊔ Vm2) ⊔ Vwf2; [|solve_lat].
          clear -LeVbs2Vbw2 LeV1V2 LeV2Vm2 LeVs2Vm2. solve_lat.
        + subst nstf2. simpl. solve_lat.
        + subst E2'. unfold SeenUpgrade. intros. destruct (decide (e0 = length E2)) as [->|NEQ].
          * rewrite lookup_app_1_eq in H10. inversion H10. subst eV1. done.
          * rewrite lookup_app_1_ne in H10; [|done]. apply SeenUpgrade2 in H10. destruct (eV1.(type)); try done. des; [by left|].
            right. destruct (decide (e' = 0)) as [->|NEQ'].
            -- rewrite Hwarc2e0 in H10. inversion H10. subst ainfo0. simpl in *. done.
            -- exists e',ainfo0. rewrite lookup_insert_ne; [|done]. rewrite lookup_delete_ne; [|done]. done.
        + subst E2'. unfold SeenDowngrade. intros. destruct (decide (e0 = length E2)) as [->|NEQ].
          * rewrite lookup_app_1_eq in H10. inversion H10. subst eV1. done.
          * rewrite lookup_app_1_ne in H10; [|done]. apply SeenDowngrade2 in H10. destruct (eV1.(type)); try done. des; [by left;set_solver +H10|].
            rewrite Hsarc2 lookup_singleton_Some in H10. destruct H10 as [<- <-]. left. set_solver +SubainfoM H11.
        + rewrite Hsarc2 delete_singleton. unfold SeenUnlock. intros. left. subst lcks2'. simpl. apply SeenUnlock2 in H10. des; [set_solver +H10|].
          rewrite Hsarc2 lookup_singleton_Some in H10. destruct H10 as [<- <-]. set_solver +H11 SubainfoMw.
        + unfold ArcsSeen. intros. rewrite lookup_delete_Some in H10. destruct H10 as [_ H10]. apply LEsarc2 in H10. done.
        + rewrite /StlistValid Forall_app Forall_singleton. split; [done|]. intros. done.
        + simpl in *. rewrite H1. solve_lat. }

    iModIntro. wp_pures. rewrite bool_decide_true; [|by rewrite Hstf2 size_singleton; lia].
    wp_apply (wp_acq_fence with "⊒Vm2"); [solve_ndisj|]. iClear "⊒Vm2". iIntros "#⊒Vm2". iCombine "⊒V2 ⊒Vm2" as "⊒V2'".
    rewrite monPred_in_view_op. iDestruct (view_at_elim with "⊒V2' HΦ") as "HΦ". wp_pures. by iApply "HΦ".
  - (* Current StrongArc is not the last one. Commit [StrongDrop e false] *)
    have LeV0V2 : V0 ⊑ V2 by solve_lat.
    set opId := length E2.
    set M2 : eView := {[opId]} ∪ M.
    set eVop := mkOmoEvent (StrongDrop e false) V2 M2.
    set E2' := E2 ++ [eVop].
    set nstf2 : arc_state := ((stf2.1.1.1 ∖ {[e]}, stf2.1.1.2 ⊔ V2, stf2.1.2 ∪ M2), stf2.2).
    have LeVp2ainfo1 : Vp2 ⊑ ainfo1.1.1.1.2 by eapply LEsarc2.

    have SSub : {[e]} ⊂ stf2.1.1.1.
    { apply elem_of_dom_2 in Hsarc2e. rewrite DOMsarc2 in Hsarc2e.
      destruct (decide (stf2.1.1.1 = {[e]})) as [EQstf2|NEQstf2]; [|set_solver +Hsarc2e NEQstf2].
      apply (f_equal size) in EQstf2. rewrite size_singleton in EQstf2. done. }

    iDestruct (view_at_elim with "⊒V0'' AU@V0''") as "AU".
    iMod "AU" as (????) "[>M●2' [_ Commit]]".
    iDestruct (OmoAuth_agree with "M●2 M●2'") as %(<- & <- & <- & <-). iCombine "M●2 M●2'" as "M●2".
    iDestruct (view_at_mono_2 _ V2 with "⊒M@V0''") as "⊒M@V2"; [solve_lat|].
    iMod (OmoAuth_insert_last with "M●2 ⊒M@V2 WCOMMIT []") as "(M●2 & #⊒M2@V2 & #opId↦esn2 & #opId✓eVop & #opId↪nstf2 & WCOMMIT)".
    { have ? : step opId eVop stf2 nstf2; [by eapply arc_step_StrongDrop; try done; set_solver-|iPureIntro; split_and!; try done]. }
    iMod (OmoHb_new_2 _ _ _ _ _ _ _ _ (length Es2) ({[length Es2]} ∪ Ms') with "M●2 [] opId✓eVop") as "[M●2 #opId⊒esn2]".
    { set_solver-. } { iFrame "⊒Ms2@V2". }

    iAssert (|==> OmoAuth γg γs2 1 (E2 ++ [eVop]) (omo_append_w omo2 opId []) (stlist2 ++ [nstf2]) _ ∗
        (⌜ ewf2 ∈ ainfo1.1.2 ⌝ -∗ OmoHb γg γew opId ewf2))%I with "[M●2]" as ">[[M●2 M●2'] #opId⊒ewf2]".
    { destruct (decide (ewf2 ∈ ainfo1.1.2)) as [ewf2IN|ewf2NIN].
      - iDestruct (view_at_mono_2 _ V2 with "⊒Mw@V0''") as "⊒Mw@V2"; [solve_lat|].
        iMod (OmoHb_new_2 _ _ _ _ _ _ _ _ ewf2 Mw with "M●2 [] opId✓eVop") as "[M●2 #opId⊒ewf2]".
        { set_solver +SubainfoMw ewf2IN. } { iFrame "⊒Mw@V2". }
        iDestruct (OmoHbToken_finish with "M●2") as "M●2".
        iModIntro. iFrame "M●2". iIntros "_". iFrame "opId⊒ewf2".
      - iModIntro. iDestruct (OmoHbToken_finish with "M●2") as "M●2". iFrame "M●2". iIntros "%ewf2IN". done. }

    iMod ("Commit" $! false V2 nstf2 M2 with "[$⊒V2 $M●2' $WCOMMIT $⊒M2@V2]") as "HΦ".
    { iPureIntro. split_and!; try done. set_solver-. }

    iMod (CWMono_insert_last_last (wr_event (length omo2)) with "Hγm2 M●2 Ms●2 opId↦esn2")
      as "(Hγm2 & #MONO✓opId & M●2 & Ms●2)".
    { by rewrite lookup_omo_wr_event omo_append_w_write_op omo_write_op_length lookup_app_1_eq. }
    { by rewrite omo_append_w_length /= Nat.add_sub. }

    iAssert (AllStrongsInner γg γes γs2 γss γm (length (omo_write_op omos2)) (length Es2))%I with "[-]" as "#NewStrongInner".
    { iExists opId,nstf2,eVsn2. subst nstf2. rewrite eVsn2EV -H0 size_difference; [|set_solver +SSub]. rewrite size_singleton.
      replace (Z.of_nat (size stf2.1.1.1) - 1)%Z with (Z.of_nat (size stf2.1.1.1 - 1)) by lia.
      iFrame "opId↦esn2 opId⊒esn2 opId↪nstf2 esn2✓eVsn2 MONO✓opId". iSplit; [done|].
      rewrite -{1}omo_write_op_length. replace (length omos2) with (S (length omos2 - 1)) by lia.
      iDestruct (big_sepL_lookup with "AllStrongs2") as (ef2 stf2' eVsf2')
        "(ef2↦esf2 & _ & ef2↪stf2' & esf2✓eVsf2' & _ & %eVsf2'EV & _)"; [rewrite last_lookup in LASTesf2;exact LASTesf2|].
      iDestruct (OmoEinfo_agree with "esf2✓eVsf2 esf2✓eVsf2'") as %<-.
      rewrite eVsf2EV /= in eVsf2'EV. inversion eVsf2'EV.
      have EQsz : size stf2.1.1.1 = size stf2'.1.1.1 by lia. clear H1.

      iDestruct (OmoAuth_OmoCW_l with "M●2 ef2↦esf2") as %[eVf2 HeVf2].
      iDestruct (OmoEinfo_get with "M●2") as "#ef2✓eVf2"; [exact HeVf2|].
      iAssert (⌜ opId ≠ ef2 ⌝)%I with "[-]" as %NEQef2.
      { iIntros "%EQef2". subst ef2. iDestruct (OmoCW_agree_1 with "opId↦esn2 ef2↦esf2") as %[_ <-].
        rewrite last_lookup -lookup_omo_wr_event in LASTesf2. eapply lookup_omo_event_valid in LASTesf2; [|done].
        rewrite lookup_lt_is_Some in LASTesf2. lia. }
      iDestruct (OmoLt_get_append_w with "M●2 ef2✓eVf2") as "#ef2<opId"; [done|].

      iExists omos2,ef2,esf2,eVop,eVsf2,stf2'. iFrame "Ms◯2 ef2↦esf2 opId✓eVop esf2✓eVsf2 ef2↪stf2' ef2<opId". iPureIntro.
      replace (length (omo_write_op omos2) - 1) with (Init.Nat.pred (length (omo_write_op omos2))) by lia.
      rewrite -last_lookup -EQsz eVsf2EV /=. split_and!; try done. right. split; [done|]. exists e,false. done. }

    iDestruct (AllEvents_after_strong_write_event with "AllEvents2 M●2 opId↦esn2 opId⊒esn2 MONO✓opId") as "#AllEvents2'"; [done|done|].

    iDestruct "Hnsf2" as "(P1@Vp2 & (P1@Vsf2 & #⊒dgds2@Vsf2 & #⊒lcks2@Vsf2) & (%eV0 & #e0✓eV0 & %eV0EV) & e0↪ainfo & Hγb' & Hγul' & ->)".
    iDestruct (ghost_map_lookup with "Hγwa2 e0↪ainfo") as %Hwarc2e0.
    set lcks2' := lcks2 ∪ Mw. set dgds2' := dgds2 ∪ M. set sarc2' := delete e sarc2.
    iMod (ghost_var_update lcks2' with "Hγl2") as "Hγl2".
    iMod (ghost_var_update dgds2' with "Hγd2") as "Hγd2".
    iMod (ghost_map_delete with "Hγsa2 e↪ainfo1") as "Hγsa2".
    iCombine "P1@V0'' ⊒M@V0'' ⊒Mw@V0''" as "RES@V0''".
    iCombine "P1@Vsf2 ⊒dgds2@Vsf2 ⊒lcks2@Vsf2 ⊒stf2s@Vsf2" as "RES@Vsf2".
    iDestruct (view_at_mono_2 _ Vm2 with "RES@V0''") as "(P1@Vm2a & #⊒M@Vm2 & #⊒Mw@Vm2)"; [solve_lat|].
    iDestruct (view_at_mono_2 _ Vm2 with "RES@Vsf2") as "(P1@Vm2b & #⊒dgds2@Vm2 & #⊒lcks2@Vm2 & #⊒stf2s@Vm2)"; [solve_lat|].
    iDestruct (view_at_mono_2 _ Vm2 with "⊒M2@V2") as "⊒M2@Vm2"; [solve_lat|].
    iDestruct (OmoEview_union_obj with "⊒lcks2@Vm2 ⊒Mw@Vm2") as "#⊒lcks2'@Vm2".
    iDestruct (OmoEview_union_obj with "⊒dgds2@Vm2 ⊒M@Vm2") as "⊒dgds2'@Vm2".
    iDestruct (OmoEview_union_obj with "⊒stf2s@Vm2 ⊒M2@Vm2") as "⊒nstf2s@Vm2".
    (* iDestruct (view_at_elim with "⊒V0'' HP1@V0''") as "HP1". iDestruct ("HP1" $! ainfo1.1.1.1.1 qsa2b) as "HP1'". *)
    replace ainfo.1.1.1.1 with ainfo1.1.1.1.1 by done.
    iCombine "Hγb2 Hγb" as "Hγb2". iCombine "P1@Vm2a P1@Vm2b" as "P1@Vm2".
    replace (qsa2/2 + qwa2/2 + ainfo1.1.1.1.1/2)%Qp with ((qsa2 + ainfo1.1.1.1.1)/2 + qwa2/2)%Qp; last first.
    { by rewrite Qp.div_add_distr -(Qp.add_assoc _ (ainfo1.1.1.1.1/2)%Qp) (Qp.add_comm (ainfo1.1.1.1.1/2)%Qp) Qp.add_assoc. }

    iMod ("Hclose" with "[-HΦ]") as "_".
    { repeat iExists _. iFrame "HN M●2 Ms●2 Mw●2 Hγsa2 Hγwa2 Hγm2 Hγb2". rewrite omo_append_w_write_op.
      iNext. do 4 iExists _. iExists nstf2,_,_,_,_,(size st1.1.1.1 - 1),_. iExists Vm2,Vwf2,Vp2. repeat iExists _.
      iFrame "AllEvents2' AllWeaks2 omos↦2 omow↦2 Hγu2 Hγd2 Hγl2 Hγul2 esn2✓eVsn2 ewf2✓eVwf2 P2".
      have EQ : size st1.1.1.1 - 1 = S (size st1.1.1.1 - 2) by lia. rewrite {1}EQ. clear EQ.
      iFrame "⊒upds2@Vwf2 ⊒ulcks2@Vwf2 ⊒nstf2s@Vm2 ⊒stf2w@Vwf2 P1@Vm2 P1@Vp2 ⊒lcks2'@Vm2 ⊒dgds2'@Vm2 e0↪ainfo Hγb' Hγul'".
      iSplitR; last iSplitR; last iSplitR; last iSplitL.
      - iApply big_sepL_snoc. iFrame "AllStrongs2 NewStrongInner".
      - iApply big_sepL_forall. iIntros "%i %ew %Hew".
        iDestruct (big_sepL_lookup with "AllLocks2") as (eVw zw) "[ew✓eVw [%eVwEV %COND]]"; [exact Hew|].
        iExists eVw,zw. iFrame "ew✓eVw". iPureIntro. split; [done|]. intros. apply COND in H. clear eVEV. des; [by left;set_solver +H|].
        destruct (decide (e0 = e)) as [->|NEQ].
        + rewrite Hsarc2e in H. inversion H. subst ainfo0. left. set_solver +H1 SubainfoMw.
        + right. exists e0,ainfo0. rewrite lookup_delete_ne; [|done]. done.
      - iSplit; [|done]. iExists eV0. iFrame "e0✓eV0". done.
      - destruct ty2.
        + iDestruct "Hty2" as "[[H|[(%e' & %ainfo' & %Hsarc2e' & %ewf2IN)|%ZSZ]] H']";
          iFrame "H'"; [by iLeft; iFrame "H"|..|done]. destruct (decide (e' = e)) as [->|NEQ].
          * rewrite Hsarc2e in Hsarc2e'. inversion Hsarc2e'. subst ainfo'. iLeft. iExists opId. iApply "opId⊒ewf2". done.
          * iRight. iLeft. iExists e',ainfo'. iPureIntro. by rewrite lookup_delete_ne.
        + iDestruct "Hty2" as %(H1 & H2 & H3 & H4). iPureIntro. clear eVEV. des. split_and!; try done. have NEQ : e0 ≠ e.
          { unfold not. intros. subst e0. rewrite Hsarc2e in H5. inversion H5. subst ainfo0 ainfo1. simpl in *. done. }
          exists e0,ainfo0. split_and!; try done; [set_solver +H3 NEQ|]. by rewrite lookup_delete_ne.
      - iPureIntro. subst nstf2. simpl in *. rewrite !last_snoc eVsn2EV size_difference; [|set_solver +SSub].
        replace (Z.of_nat (size st1.1.1.1) - 1)%Z with (Z.of_nat (size st1.1.1.1 - 1)) by lia.
        have EQsz : size stf2.1.1.1 = size st1.1.1.1 by lia. clear H0. rewrite -!EQsz size_singleton dom_delete_L -DOMsarc2.
        clear eVEV. split_and!; try done.
        + rewrite (map_fold_delete_L _ _ e ainfo1 sarc2) in Hqsa2; [|by apply frac_sum_wf|done]. rewrite {1}/frac_sum /= in Hqsa2.
          rewrite Qp.add_comm map_fold_init_frac_op. done.
        + unfold ArcsValid. intros. have H' : e0 ∈ dom sarc2 by set_solver +H. apply VALsarc2 in H'. rewrite app_length /=. lia.
        + unfold ArcsValid. intros. apply VALwarc2 in H. rewrite app_length /=. lia.
        + unfold ArcsValid2. intros. destruct (decide (e0 = length E2)) as [->|NEQ].
          * rewrite lookup_app_1_eq in H. inversion H. subst eV1. simpl. set_solver-.
          * rewrite lookup_app_1_ne in H; [|done]. apply VALsarcwarc2 in H. destruct (eV1.(type)); try done;
            (destruct (decide (e2 = e)) as [->|NEQ']; [set_solver-|]); set_solver +H NEQ'.
        + unfold SeenClone. intros. destruct (decide (e' = length E2)) as [->|NEQ].
          * rewrite lookup_app_1_eq in H0. inversion H0. subst eV1. done.
          * rewrite lookup_app_1_ne in H0; [|done]. eapply SeenClone2; try done. rewrite lookup_delete_Some in H. by des.
        + unfold SeenWeakClone. intros. destruct (decide (e' = length E2)) as [->|NEQ].
          * rewrite lookup_app_1_eq in H0. inversion H0. subst eV1. done.
          * rewrite lookup_app_1_ne in H0; [|done]. by eapply SeenWeakClone2.
        + rewrite omo_append_w_write_op lookup_app_1_ne; [done|]. rewrite -omo_write_op_length. lia.
        + by rewrite (Qp.add_comm ainfo.1.1.1.1) Qp.add_assoc EQqsa2.
        + by rewrite /ArcAlive Forall_app Forall_singleton.
        + eapply EventIdValid_update; [done|]. simpl. apply VALM in eM. rewrite lookup_lt_is_Some in eM. done.
        + rewrite (map_fold_delete_L _ _ e ainfo1 sarc2) in LeVbs2Vbw2; [|solve_lat|done].
          replace ((Vbs2 ⊔ V2) ⊔ Vbw2) with ((Vbs2 ⊔ Vbw2) ⊔ V2) by solve_lat.
          have LE : ainfo1.1.1.1.2 ⊑ V2 by clear -LeV0'V0'' LeV0''V1 LeV1V2; solve_lat.
          replace (((view_join_total e ainfo1 (map_fold view_join_total Vp2 (delete e sarc2)) ⊔ map_fold view_join_total Vp2 warc2) ⊔ Vsf2) ⊔ Vwf2) with
            (((map_fold view_join_total Vp2 (delete e sarc2) ⊔ map_fold view_join_total Vp2 warc2) ⊔ Vsf2) ⊔ Vwf2 ⊔ ainfo1.1.1.1.2) in LeVbs2Vbw2 by solve_lat.
          have LE' : (Vbs2 ⊔ Vbw2) ⊔ V2 ⊑ (((map_fold view_join_total Vp2 (delete e sarc2) ⊔ map_fold view_join_total Vp2 warc2) ⊔ Vsf2) ⊔ Vwf2) ⊔ V2.
          { clear -LeVbs2Vbw2 LE. solve_lat. } clear -LE' LeVs2Vm2 LeV2Vm2. solve_lat.
        + solve_lat.
        + unfold SeenUpgrade. intros. destruct (decide (e0 = length E2)) as [->|NEQ].
          * rewrite lookup_app_1_eq in H. inversion H. subst eV1. done.
          * rewrite lookup_app_1_ne in H; [|done]. by eapply SeenUpgrade2.
        + unfold SeenDowngrade. intros. destruct (decide (e0 = length E2)) as [->|NEQ].
          * rewrite lookup_app_1_eq in H. inversion H. subst eV1. done.
          * rewrite lookup_app_1_ne in H; [|done]. apply SeenDowngrade2 in H. destruct (eV1.(type)); try done. des; [by left;set_solver +H|].
            destruct (decide (e' = e)) as [->|NEQ'].
            -- rewrite Hsarc2e in H. inversion H. subst ainfo0. left. set_solver +H0 SubainfoM.
            -- right. exists e',ainfo0. rewrite lookup_delete_ne; [|done]. done.
        + unfold SeenUnlock. intros. apply SeenUnlock2 in H. des; [by left;set_solver +H|]. destruct (decide (e' = e)) as [->|NEQ].
          * rewrite Hsarc2e in H. inversion H. subst ainfo0. left. set_solver +H0 SubainfoMw.
          * right. exists e',ainfo0. rewrite lookup_delete_ne; [|done]. done.
        + unfold ArcsSeen. intros. rewrite lookup_delete_Some in H. des. by eapply LEsarc2.
        + rewrite /StlistValid Forall_app Forall_singleton. split; [done|]. intros. simpl in H.
          apply elem_of_dom_2 in Hwarc2e0. rewrite DOMwarc2 in Hwarc2e0. done.
        + rewrite decide_False; [done|]. rewrite DOMsarc2. lia. }

    iModIntro. wp_pures. rewrite bool_decide_false; [|lia]. wp_pures. by iApply "HΦ".
Qed.

Lemma upgrade_spec :
  upgrade_spec' code.upgrade ArcInv StrongArc WeakArc.
Proof.
  intros N DISJ l tid γg M e V0 P1 P2. iIntros "%PasFrac #⊒V0 WArc" (Φ) "AU".
  iDestruct "WArc" as (??????????) "(%&%&%&%&%&%&%& #HN & #AInv & #⊒M & #⊒Ms & #⊒Mw & #e✓eV & #⊒ainfo & Hγb & e↪ainfo & Hγul & HeP2 &
    (%Hainfo2 & %eM & %eVEV & %SubainfoM & %SubainfoMw))".
  iLöb as "IH" forall (ainfo Hainfo2 SubainfoM SubainfoMw) "⊒ainfo". wp_lam. wp_pures. wp_bind (!ʳˡˣ _)%E.

  (* Inv access 1 *)
  iInv "AInv" as "H" "Hclose".
  iDestruct "H" as (?? γs1 ???????) "(%&%&%& %sarc1 & %warc1 & %qsa1 & %qwa1 & %alive1 & %E1 & %Es1 & %Ew1 & %omo1 & %omos1 &
    %omow1 & %stlist1 & %mos1 & %mow1 & %Mono1 & >HN' & >M●1 & >Ms●1 & >Mw●1 & >Hγsa1 & >Hγwa1 & >Hγb1 & >Hγm1 & Alive1)".
  gname_agree with "HN HN'". iClear "HN'".
  iDestruct (ghost_var_agree with "Hγb Hγb1") as %<-.

  iDestruct (OmoEview_update with "M●1 ⊒M ⊒Mw") as (Mw') "(M●1 & #⊒Mw' & M⊢Mw' & %SubMwMw')".
  iDestruct (OmoEview_update with "M●1 ⊒M ⊒Ms") as (Ms') "(M●1 & #⊒Ms' & M⊢Ms' & %SubMsMs')".
  iCombine "⊒V0 ⊒ainfo" as "⊒V0'". rewrite monPred_in_view_op. set V0' := V0 ⊔ ainfo.1.1.1.2.
  iCombine "⊒M ⊒Ms ⊒Mw ⊒ainfo ⊒Mw' ⊒Ms' HeP2" as "RES".
  iDestruct (view_at_intro_incl with "RES ⊒V0'") as (V0'')
    "(#⊒V0'' & %LeV0'V0'' & (#⊒M@V0'' & #⊒Ms@V0'' & #⊒Mw@V0'' & #⊒ainfo@V0'' & #⊒Mw'@V0'' & #⊒Ms'@V0'' & HeP2@V0''))".

  iDestruct "Alive1" as (Vbs1 Vbw1 ty1 uf1 stf1 esf1 ewf1 eVsf1 eVwf1 nsf1) "(%zwf1 & %Vsf1 & %Vwf1 & %Vp1 & %qsa1a & %qsa1b & %qu1 & %qd1 & %upds1 &
    %dgds1 & %lcks1 & %ulcks1 & >#AllEvents1 & >#AllStrongs1 & >#AllWeaks1 & >omos↦1 & >omow↦1 & >Hγu1 & >Hγd1 & >Hγl1 & >Hγul1 &
    >#AllLocks1 & [>#⊒upds1@Vwf1 >#⊒ulcks1@Vwf1] & >#esf1✓eVsf1 & >#ewf1✓eVwf1 & Hnsf1 & P2 & Hty1 & >#⊒stf1s@Vsf1 & >#⊒stf1w@Vwf1 & >Pures)".
  iDestruct "Pures" as %(Subuf1 & LASTesf1 & LASTewf1 & eVsf1EV & eVwf1EV & Hqsa1 & Hqwa1 & VALsarc1 & VALwarc1 & VALsarcwarc1 & SeenClone1 &
    SeenWeakClone1 & HInitWrite1 & LASTstf1 & DOMsarc1 & DOMwarc1 & EQqsa1 & Alive1 & VALeid1 & LeVbs1Vbw1 & GeVsf1 & GeVwf1 &
    SeenUpgrade1 & SeenDowngrade1 & SeenUnlock1 & LEsarc1 & LEwarc1 & VALstlist1 & LeVsf1 & EQnsf1).
  iDestruct (OmoAuth_wf with "M●1") as %[OMO_GOOD1 _]. iDestruct (OmoAuth_omo_nonempty with "M●1") as %Nomo1.
  have NZomo1 : length omo1 ≠ 0 by destruct omo1.
  apply omo_stlist_length in OMO_GOOD1 as EQlenST1.

  wp_apply (append_only_loc_relaxed_read with "[$Ms●1 $⊒Ms' $omos↦1 $⊒V0'']"); [solve_ndisj|].
  iIntros (es1 gens1 vs1 Vs1 V1 eVs1 eVsn1) "(Pures & Ms●1 & RCOMMIT & #MAXes1 & #es1✓eVs1 & #esn1✓eVsn1 & #es1=esn1 & #⊒V1 & _ & #⊒Ms1@V1 & omos↦1)".
  iDestruct "Pures" as %(Hgens1 & eVs1EV & LeV0''V1 & eVsn1EV & eVsn1SYNC).

  iDestruct (big_sepL_lookup with "AllStrongs1") as (e1 st1 eVs1')
    "(e1↦es1 & e1⊒es1 & e1↪st1 & es1✓eVs1' & MONO✓e1 & %eVs1'EV & Hgens1)"; [exact Hgens1|].
  iDestruct (OmoEinfo_agree with "es1✓eVs1 es1✓eVs1'") as %<-.
  rewrite eVs1EV /= in eVs1'EV. subst vs1.

  set ainfo1 := (ainfo.1.1.1.1, ainfo.1.1.1.2 ⊔ V1, ainfo.1.1.2, ainfo.1.2, cas_only).
  set warc1' := <[e := ainfo1]> (delete e warc1).
  iDestruct (ghost_map_lookup with "Hγwa1 e↪ainfo") as %Hwarc1e.
  iMod (ghost_map_delete with "Hγwa1 e↪ainfo") as "Hγwa1".
  iMod (ghost_map_insert e ainfo1 with "Hγwa1") as "[Hγwa1 e↪ainfo1]"; [by apply lookup_delete|].

  destruct (decide (size st1.1.1.1 = 0)) as [EQszst1|NEQszst1].
  { (* Read `0` from strong counter. Commit [UpgradeFail] event *)
    (* The message that we read should be the last one *)
    destruct (decide (gens1 = length omos1 - 1)) as [->|NEQgens1]; last first.
    { have [es1' Hes1'] : is_Some (omo_write_op omos1 !! (S gens1)).
      { rewrite lookup_lt_is_Some. apply lookup_lt_Some in Hgens1. rewrite omo_write_op_length in NEQgens1. lia. }
      iDestruct (big_sepL_lookup with "AllStrongs1") as (e1' st1' eVs1')
        "(e1'↦es1' & e1'⊒es1' & e1'↪st1' & es1'✓eVs1' & MONO✓e1' & %eVs1'EV & Hgens1')"; [exact Hes1'|].
      iDestruct "Hgens1'" as (omos e1'' es1'' eV1 eVs1'' st1'')
        "(Ms◯ & e1''↦es1'' & e1''✓eV1 & es1''✓eVs1'' & e1''↪st1'' & e1''<e1' & (%Hes1'' & %eVs1''EV & %NEQszst1'' & _))".
      iDestruct (OmoAuth_OmoSnapOmo with "Ms●1 Ms◯") as %PREFIXomos1.
      replace (S gens1 - 1) with gens1 in Hes1'' by lia. rewrite -lookup_omo_wr_event in Hes1''. eapply omo_prefix_lookup_Some in Hes1''; try done.
      rewrite lookup_omo_wr_event omo_insert_r_write_op Hgens1 in Hes1''. inversion Hes1''. subst es1''.
      iDestruct (OmoCW_agree_2 with "e1↦es1 e1''↦es1''") as %[_ <-]. iDestruct (OmoSnap_agree with "e1↪st1 e1''↪st1''") as %<-. done. }

    replace (length omos1 - 1) with (Init.Nat.pred (length omos1)) in Hgens1 by lia.
    rewrite omo_write_op_length -last_lookup LASTesf1 in Hgens1. inversion Hgens1. subst es1.
    iDestruct (OmoEinfo_agree with "esf1✓eVsf1 es1✓eVs1") as %<-. rewrite eVsf1EV in eVs1EV. inversion eVs1EV. subst nsf1 Vs1.

    have LeV0V1 : V0 ⊑ V1 by solve_lat.
    set opId := length E1.
    set M1 : eView := {[opId]} ∪ M.
    set eVop := mkOmoEvent UpgradeFail V1 M1.

    iMod "AU" as (????) "[>M●1' [_ Commit]]".
    iDestruct (OmoAuth_agree with "M●1 M●1'") as %(<- & <- & <- & <-). iCombine "M●1 M●1'" as "M●1".
    iDestruct (view_at_mono_2 _ V1 with "⊒M@V0''") as "⊒M@V1"; [done|].
    iDestruct (OmoAuth_OmoEview with "M●1 ⊒M") as %VALM.
    have MAXgen : OmoUBgen omo1 M (length omo1 - 1).
    { unfold OmoUBgen. intros. apply VALM in H. eapply lookup_omo_surjective in H as [eidx Heidx]; [|done].
      exists eidx. split; [done|]. apply lookup_omo_lt_Some in Heidx. lia. }
    iMod (OmoAuth_insert_ro_gen with "M●1 ⊒M@V1 RCOMMIT []") as "(M●1 & #⊒M1@V1 & #opId↦esn1 & #opId↪stf1 & #opId✓eVop & RCOMMIT)".
    { rewrite last_lookup -EQlenST1 in LASTstf1. replace (Init.Nat.pred (length omo1)) with (length omo1 - 1) in LASTstf1 by lia.
      have ? : step opId eVop stf1 stf1; [|iPureIntro; split_and!; try done].
      eapply arc_step_UpgradeFail; try done; [set_solver-|]. unfold_leibniz. apply size_empty_inv. fold_leibniz. lia. }
    iMod (OmoHb_new_2 _ _ _ _ _ _ _ _ (length Es1) ({[length Es1]} ∪ Ms') with "M●1 [] opId✓eVop") as "[M●1 #opId⊒esn1]".
    { set_solver-. } { iFrame "⊒Ms1@V1". }
    iDestruct (OmoHbToken_finish with "M●1") as "[M●1 M●1']".
    iDestruct (OmoAuth_OmoCW_l' with "M●1 e1↦es1") as %[eidx1 Heidx1].
    have [es Hes] : is_Some (omo_read_op omo1 !! (length omo1 - 1)%nat) by rewrite lookup_lt_is_Some -omo_read_op_length; lia.
    iDestruct (OmoLe_get _ _ _ _ _ _ eidx1 (ro_event (length omo1 - 1) (length es))  with "M●1") as "#e1≤opId"; [done|..].
    { by rewrite lookup_omo_ro_event omo_insert_r_read_op list_lookup_alter Hes /= lookup_app_1_eq. }
    { apply lookup_omo_lt_Some in Heidx1. simpl in *. rewrite omo_insert_r_length in Heidx1. lia. }

    iMod ("Commit" $! false V1 _ _ _ M1 with "[$⊒V1 $M●1' $RCOMMIT Hγb e↪ainfo1 Hγul HeP2@V0'']") as "HΦ".
    { iSplitL.
      - repeat iExists _. iFrame "HN AInv ⊒M1@V1 ⊒Ms@V0'' ⊒Mw@V0'' e✓eV e↪ainfo1 Hγb Hγul HeP2@V0''". iSplit.
        + iApply view_at_unfold. rewrite monPred_at_in. iPureIntro. clear -LeV0'V0'' LeV0''V1. solve_lat.
        + iPureIntro. split_and!; try done; [set_solver +eM|set_solver +SubainfoM].
      - iPureIntro. split_and!; try done; [set_solver-|]. exists (length omo1 - 1). split; [done|]. lia. }

    iMod ("Hclose" with "[-HΦ]") as "_".
    { repeat iExists _. iFrame "HN M●1 Ms●1 Mw●1 Hγsa1 Hγwa1 Hγm1 Hγb1". rewrite omo_insert_r_write_op.
      iNext. repeat iExists _. eapply (dom_same _ _ _ ainfo1) in Hwarc1e as EQdom. rewrite -EQdom.
      iFrame "AllStrongs1 AllWeaks1 AllLocks1 omos↦1 omow↦1 Hγu1 Hγd1 Hγl1 Hγul1 Hnsf1 esf1✓eVsf1 ewf1✓eVwf1 Hty1 ⊒upds1@Vwf1 ⊒ulcks1@Vwf1".
      iFrame "⊒stf1s@Vsf1 ⊒stf1w@Vwf1". iSplitR; last iSplitL.
      - iApply big_sepL_snoc. iFrame "AllEvents1". iLeft. iExists e1,esf1,(length Es1). iFrame "e1≤opId es1=esn1 e1↦es1 opId⊒esn1". done.
      - destruct (decide (e = 0)) as [->|NEQ]; [by rewrite lookup_insert|].
        rewrite lookup_insert_ne; [|done]. rewrite lookup_delete_ne; [|done]. done.
      - eapply (warc_update_snoc_1 _ _ _ ainfo1 _ _ eVop sarc1 sarc1) in Hwarc1e as H; try done; [|solve_lat].
        eapply (warc_update_2 _ _ _ ainfo1) in Hwarc1e as H1; try done.
        rewrite omo_insert_r_write_op EQdom. iPureIntro. clear eVEV. des; split_and!; try done.
        + by rewrite /ArcAlive Forall_app Forall_singleton.
        + by eapply EventIdValid_update.
        + rewrite H1. replace ((Vbs1 ⊔ V1) ⊔ Vbw1) with ((Vbs1 ⊔ Vbw1) ⊔ V1) by solve_lat. solve_lat.
        + unfold SeenUpgrade. intros. destruct (decide (e0 = length E1)) as [->|NEQ].
          * rewrite lookup_app_1_eq in H10. inversion H10. subst eV0. done.
          * rewrite lookup_app_1_ne in H10; [|done]. apply SeenUpgrade1 in H10. destruct (eV0.(type)); try done.
            des; [by left|]. right. destruct (decide (e' = e)) as [->|NEQ'].
            -- rewrite Hwarc1e in H10. inversion H10. subst ainfo0. exists e,ainfo1. rewrite lookup_insert. split; [done|]. set_solver +H11.
            -- exists e',ainfo0. rewrite lookup_insert_ne; [|done]. rewrite lookup_delete_ne; [|done]. done.
        + unfold SeenDowngrade. intros. destruct (decide (e0 = length E1)) as [->|NEQ].
          * rewrite lookup_app_1_eq in H10. inversion H10. subst eV0. done.
          * rewrite lookup_app_1_ne in H10; [|done]. by eapply SeenDowngrade1.
        + rewrite H1. destruct (decide (size stf1.1.1.1 = 0)); [|done]. solve_lat. }

    iModIntro. wp_pures. rewrite bool_decide_true; [|lia]. wp_pures. by iApply "HΦ". }

  (* Read nonzero value from strong counter. Proceed *)
  iMod ("Hclose" with "[-Hγb Hγul AU M⊢Mw' M⊢Ms' HeP2@V0'' e↪ainfo1]") as "_".
  { repeat iExists _. iFrame "HN M●1 Ms●1 Mw●1 Hγsa1 Hγwa1 Hγm1 Hγb1". rewrite omo_insert_r_write_op.
    iNext. repeat iExists _. eapply (dom_same _ _ _ ainfo1) in Hwarc1e as EQdom. rewrite -EQdom.
    iFrame "AllEvents1 AllStrongs1 AllWeaks1 AllLocks1 omos↦1 omow↦1 Hγu1 Hγd1 Hγl1 Hγul1 Hnsf1 Hty1 esf1✓eVsf1 ewf1✓eVwf1".
    iFrame "⊒upds1@Vwf1 ⊒ulcks1@Vwf1 ⊒stf1s@Vsf1 ⊒stf1w@Vwf1". iSplitL.
    - destruct (decide (e = 0)) as [->|NEQ]; [by rewrite lookup_insert|].
      rewrite lookup_insert_ne; [|done]. rewrite lookup_delete_ne; [|done]. done.
    - rewrite EQdom. eapply (warc_update_1 _ _ _ ainfo1) in Hwarc1e as H; try done; [|solve_lat].
      eapply (warc_update_2 _ _ _ ainfo1) in Hwarc1e as H0; try done. clear eVEV. des. iPureIntro. split_and!; try done.
      + rewrite H0. replace ((Vbs1 ⊔ V1) ⊔ Vbw1) with ((Vbs1 ⊔ Vbw1) ⊔ V1) by solve_lat. clear -LeVbs1Vbw1. solve_lat.
      + rewrite H0. destruct (decide (nsf1 = 0)); [|done]. clear -LeVsf1. solve_lat. }

  iModIntro. wp_pures. rewrite bool_decide_false; [|lia]. wp_pures. wp_bind (casʳˡˣ(_,_,_))%E.

  (* Inv access 2 *)
  iInv "AInv" as "H" "Hclose".
  iDestruct "H" as (?? γs2 ???????) "(%&%&%& %sarc2 & %warc2 & %qsa2 & %qwa2 & %alive2 & %E2 & %Es2 & %Ew2 & %omo2 & %omos2 &
    %omow2 & %stlist2 & %mos2 & %mow2 & %Mono2 & >HN' & >M●2 & >Ms●2 & >Mw●2 & >Hγsa2 & >Hγwa2 & >Hγb2 & >Hγm2 & Alive2)".
  gname_agree with "HN HN'". iClear "HN'".
  iDestruct (ghost_var_agree with "Hγb Hγb2") as %<-.

  iDestruct "Alive2" as (Vbs2 Vbw2 ty2 uf2 stf2 esf2 ewf2 eVsf2 eVwf2 nsf2) "(%zwf2 & %Vsf2 & %Vwf2 & %Vp2 & %qsa2a & %qsa2b & %qu2 & %qd2 & %upds2 &
    %dgds2 & %lcks2 & %ulcks2 & >#AllEvents2 & >#AllStrongs2 & >#AllWeaks2 & >omos↦2 & >omow↦2 & >Hγu2 & >Hγd2 & >Hγl2 & >Hγul2 &
    >#AllLocks2 & [>#⊒upds2@Vwf2 >#⊒ulcks2@Vwf2] & >#esf2✓eVsf2 & >#ewf2✓eVwf2 & Hnsf2 & P2 & Hty2 & >#⊒stf2s@Vsf2 & >#⊒stf2w@Vwf2 & >Pures)".
  iDestruct "Pures" as %(Subuf2 & LASTesf2 & LASTewf2 & eVsf2EV & eVwf2EV & Hqsa2 & Hqwa2 & VALsarc2 & VALwarc2 & VALsarcwarc2 & SeenClone2 &
    SeenWeakClone2 & HInitWrite2 & LASTstf2 & DOMsarc2 & DOMwarc2 & EQqsa2 & Alive2 & VALeid2 & LeVbs2Vbw2 & GeVsf2 & GeVwf2 &
    SeenUpgrade2 & SeenDowngrade2 & SeenUnlock2 & LEsarc2 & LEwarc2 & VALstlist2 & LeVsf2 & EQnsf2).
  iDestruct (OmoAuth_wf with "M●2") as %[OMO_GOOD2 _]. iDestruct (OmoAuth_omo_nonempty with "M●2") as %Nomo2.
  have NZomo2 : length omo2 ≠ 0 by destruct omo2.
  iDestruct (OmoAuth_wf with "Ms●2") as %[OMO_GOODs2 _]. iDestruct (OmoAuth_omo_nonempty with "Ms●2") as %Nomos2.
  have NZomos2 : length omos2 ≠ 0 by destruct omos2.
  iDestruct (OmoSnapOmo_get with "Ms●2") as "#Ms◯2".
  iMod (rel_objectively_intro (⊒∅) tid with "[]") as "#⊒∅"; [by iApply objective_objectively; iApply monPred_in_bot|].

  wp_apply (append_only_loc_cas_only_cas with "[$Ms●2 $⊒Ms' $omos↦2 $⊒V1]"); try done; [solve_ndisj|].
  iIntros (b2 es2 gens2 vs2 Vs2 V2 mos2' omos2' eVs2 eVsn2)
    "(Pures & #MAXes2 & #es2✓eVs2 & #esn2✓eVsn2 & Ms●2 & #⊒V2 & #⊒Ms2@V2 & omos↦2 & CASE)".
  iDestruct "Pures" as %(Eqgens2 & eVs2EV & LeV1V2).
  iDestruct "CASE" as "[(Pures & _ & #es2=esn2 & RCOMMIT) | [Pures sVs2]]".
  { (* CAS failed, try again *)
    iDestruct "Pures" as %(-> & NEQvs2 & -> & Homos2' & eVsn2EV & eVsn2SYNC).

    set ainfo2 := (ainfo1.1.1.1.1, ainfo1.1.1.1.2 ⊔ V2, ainfo1.1.1.2, ainfo1.1.2, cas_only).
    set warc2' := <[e := ainfo2]> (delete e warc2).
    iDestruct (ghost_map_lookup with "Hγwa2 e↪ainfo1") as %Hwarc2e.
    iMod (ghost_map_delete with "Hγwa2 e↪ainfo1") as "Hγwa2".
    iMod (ghost_map_insert e ainfo2 with "Hγwa2") as "[Hγwa2 e↪ainfo2]"; [by apply lookup_delete|].

    iMod ("Hclose" with "[-Hγb Hγul AU e↪ainfo2 HeP2@V0'']") as "_".
    { repeat iExists _. iFrame "HN M●2 Ms●2 Mw●2 Hγsa2 Hγwa2 Hγm2 Hγb2". rewrite Homos2' omo_insert_r_write_op.
      iNext. repeat iExists _. eapply (dom_same _ _ _ ainfo2) in Hwarc2e as EQdom. rewrite -EQdom.
      iFrame "AllEvents2 AllStrongs2 AllWeaks2 AllLocks2 omos↦2 omow↦2 Hγu2 Hγd2 Hγl2 Hγul2 Hnsf2 esf2✓eVsf2 ewf2✓eVwf2 Hty2".
      iFrame "⊒upds2@Vwf2 ⊒ulcks2@Vwf2 ⊒stf2s@Vsf2 ⊒stf2w@Vwf2". iSplitL.
      - destruct (decide (e = 0)) as [->|NEQ]; [by rewrite lookup_insert|].
        rewrite lookup_insert_ne; [|done]. rewrite lookup_delete_ne; [|done]. done.
      - rewrite EQdom. eapply (warc_update_1 _ _ _ ainfo2) in Hwarc2e as H; try done; [|solve_lat].
        eapply (warc_update_2 _ _ _ ainfo2) in Hwarc2e as H0; try done. clear eVEV. des. iPureIntro. split_and!; try done.
        + rewrite H0. replace ((Vbs2 ⊔ V2) ⊔ Vbw2) with ((Vbs2 ⊔ Vbw2) ⊔ V2) by solve_lat. clear -LeVbs2Vbw2. solve_lat.
        + rewrite H0. destruct (decide (nsf2 = 0)); [|done]. clear -LeVsf2. solve_lat. }

    iModIntro. wp_if. iDestruct (view_at_elim with "⊒V0'' HeP2@V0''") as "HeP2".
    iApply ("IH" $! ainfo2 with "[] [] [] Hγb e↪ainfo2 Hγul HeP2 AU"); try done.
    subst ainfo2 ainfo1. simpl. replace ((ainfo.1.1.1.2 ⊔ V1) ⊔ V2) with V2; [done|]. solve_lat. }

  (* CAS success, commit [Upgrade] event *)
  iDestruct "Pures" as %(-> & -> & ->).
  iDestruct "sVs2" as (Vm2) "((%Hmos2' & -> & %eVsn2EV & %eVsn2SYNC & %LeVs2Vm2 & %NEqVs2Vm2 & %NLeV2Vs2 & %NEqV1V2 & _) &
    _ & _ & WCOMMIT)".
  replace (length omos2 - 1) with (Init.Nat.pred (length omos2)) in Eqgens2 by lia.
  rewrite omo_write_op_length -last_lookup LASTesf2 in Eqgens2. inversion Eqgens2. subst es2. clear Eqgens2.
  iDestruct (OmoEinfo_agree with "esf2✓eVsf2 es2✓eVs2") as %<-. rewrite eVsf2EV in eVs2EV. inversion eVs2EV. subst nsf2 Vs2.
  have EQsz : size stf2.1.1.1 = S (size stf2.1.1.1 - 1) by lia. rewrite {1}EQsz. clear EQsz.

  have LeV0V2 : V0 ⊑ V2 by solve_lat.
  set opId := length E2.
  set M2 : eView := {[opId]} ∪ M.
  set eVop := mkOmoEvent Upgrade V2 M2.
  set nstf2 : arc_state := ((stf2.1.1.1 ∪ {[opId]}, stf2.1.1.2, stf2.1.2), stf2.2).
  have FRESH : opId ∉ stf2.1.1.1 by unfold not; intros; rewrite -DOMsarc2 in H; apply VALsarc2 in H; lia.

  iMod "AU" as (????) "[>M●2' [_ Commit]]".
  iDestruct (OmoAuth_agree with "M●2 M●2'") as %(<- & <- & <- & <-). iCombine "M●2 M●2'" as "M●2".
  iDestruct (view_at_mono_2 _ V2 with "⊒M@V0''") as "⊒M@V2"; [solve_lat|].
  iMod (OmoAuth_insert_last with "M●2 ⊒M@V2 WCOMMIT []") as "(M●2 & #⊒M2@V2 & #opId↦esn2 & #opId✓eVop & #opId↪nstf2 & WCOMMIT)".
  { have ? : step opId eVop stf2 nstf2; [|done]. eapply arc_step_Upgrade; try done; [set_solver-|].
    unfold not. intros. apply (f_equal size) in H. rewrite size_empty in H. lia. }
  iMod (OmoHb_new_2 _ _ _ _ _ _ _ _ (length Es2) ({[length Es2]} ∪ Ms') with "M●2 [] opId✓eVop") as "[M●2 #opId⊒esn2]".
  { set_solver-. } { iFrame "⊒Ms2@V2". }
  iDestruct (OmoHbToken_finish with "M●2") as "[M●2 M●2']".

  iMod (CWMono_insert_last_last (wr_event (length omo2)) with "Hγm2 M●2 Ms●2 opId↦esn2")
    as "(Hγm2 & #MONO✓opId & M●2 & Ms●2)".
  { by rewrite lookup_omo_wr_event omo_append_w_write_op omo_write_op_length lookup_app_1_eq. }
  { by rewrite omo_append_w_length /= Nat.add_sub. }

  iAssert (AllStrongsInner γg γes γs2 γss γm (length (omo_write_op omos2)) (length Es2))%I with "[-]" as "#NewStrongInner".
  { iExists opId,nstf2,eVsn2. subst nstf2. rewrite eVsn2EV /= size_union; [|set_solver +FRESH].
    rewrite size_singleton. replace (Z.of_nat (size st1.1.1.1) + 1)%Z with (Z.of_nat (size stf2.1.1.1 + 1)) by lia.
    iFrame "opId↦esn2 opId⊒esn2 opId↪nstf2 esn2✓eVsn2 MONO✓opId". iSplit; [done|].
    rewrite -{1}omo_write_op_length. replace (length omos2) with (S (length omos2 - 1)) by lia.
    iDestruct (big_sepL_lookup with "AllStrongs2") as (ef2 stf2' eVsf2')
      "(ef2↦esf2 & _ & ef2↪stf2' & esf2✓eVsf2' & _ & %eVsf2'EV & _)"; [rewrite last_lookup in LASTesf2;exact LASTesf2|].
    iDestruct (OmoEinfo_agree with "esf2✓eVsf2 esf2✓eVsf2'") as %<-.
    rewrite eVsf2EV /= in eVsf2'EV. inversion eVsf2'EV.
    have EQsz : size stf2.1.1.1 = size stf2'.1.1.1 by lia. clear H1.

    iDestruct (OmoAuth_OmoCW_l with "M●2 ef2↦esf2") as %[eVf2 HeVf2].
    iDestruct (OmoEinfo_get with "M●2") as "#ef2✓eVf2"; [exact HeVf2|].
    iAssert (⌜ opId ≠ ef2 ⌝)%I with "[-]" as %NEQef2.
    { iIntros "%EQef2". subst ef2. iDestruct (OmoCW_agree_1 with "opId↦esn2 ef2↦esf2") as %[_ <-].
      rewrite last_lookup -lookup_omo_wr_event in LASTesf2. eapply lookup_omo_event_valid in LASTesf2; [|done].
      rewrite lookup_lt_is_Some in LASTesf2. lia. }
    iDestruct (OmoLt_get_append_w with "M●2 ef2✓eVf2") as "#ef2<opId"; [done|].

    iExists omos2,ef2,esf2,eVop,eVsf2,stf2'. iFrame "Ms◯2 ef2↦esf2 opId✓eVop esf2✓eVsf2 ef2↪stf2' ef2<opId". iPureIntro.
    replace (length (omo_write_op omos2) - 1) with (Init.Nat.pred (length (omo_write_op omos2))) by lia.
    rewrite -last_lookup -EQsz eVsf2EV /=. split_and!; try done; [lia|]. left. split; [done|]. right. done. }

  iDestruct (AllEvents_after_strong_write_event with "AllEvents2 M●2 opId↦esn2 opId⊒esn2 MONO✓opId") as "#AllEvents2'"; [done|done|].

  set ainfo2 := (ainfo1.1.1.1.1, ainfo1.1.1.1.2 ⊔ V2, ainfo1.1.1.2 ∪ {[opId]}, ainfo1.1.2, cas_only).
  set ainfo2' := ((qsa2a/2)%Qp, ainfo2.1.1.1.2, ainfo2.1.1.2, ainfo2.1.2, cas_only).
  set warc2' := <[e := ainfo2]> (delete e warc2).
  set sarc2' := <[opId := ainfo2']> sarc2.
  iDestruct (ghost_map_lookup with "Hγwa2 e↪ainfo1") as %Hwarc2e.
  iMod (ghost_map_delete with "Hγwa2 e↪ainfo1") as "Hγwa2".
  iMod (ghost_map_insert e ainfo2 with "Hγwa2") as "[Hγwa2 e↪ainfo2]"; [by rewrite lookup_delete|].
  iMod (ghost_map_insert opId ainfo2' with "Hγsa2") as "[Hγsa2 opId↪ainfo2']".
  { rewrite -not_elem_of_dom. unfold not. intros. apply VALsarc2 in H. lia. }

  (* Take out resources (e.g. P1, ...) from invariant *)
  iDestruct "Hnsf2" as "(P1@Vp2 & RES@Vsf2 & #He0 & e0↪ainfo & Hγb0 & Hγul0 & ->)".
  iDestruct (ghost_map_lookup with "Hγwa2 e0↪ainfo") as %Hwarc2e0.
  have EQqsa2a : (qsa2a = qsa2a/2 + qsa2a/2)%Qp by rewrite -{1}(Qp.mul_div_r qsa2a 2%Qp) Qp.add_diag.
  replace (qsa2/2 + qwa2/2)%Qp with ((qsa2a/2 + qsa2b)/2 + qwa2/2 + qsa2a/2/2)%Qp; last first.
  { rewrite EQqsa2 {3}EQqsa2a !Qp.div_add_distr -(Qp.add_assoc (qsa2a/2/2 + qsa2a/2/2)%Qp _) -(Qp.add_assoc _ (qsa2a/2/2)%Qp).
    rewrite (Qp.add_comm _ (qsa2b/2 + qwa2/2)%Qp) (Qp.add_assoc _ (qsa2b/2 + qwa2/2)%Qp) (Qp.add_assoc _ (qsa2b/2)%Qp). done. }
  iDestruct "P1@Vp2" as "[P1@Vp2 P1'@Vp2]". iDestruct "Hγb2" as "[Hγb2 Hγb']". iDestruct (view_at_mono_2 _ V2 with "P1'@Vp2") as "P1@V2".
  { apply LEwarc2 in Hwarc2e. clear -Hwarc2e LeV0'V0'' LeV0''V1 LeV1V2. solve_lat. }

  iMod ("Commit" $! true V2 _ _ _ M2 with "[$⊒V2 $M●2' $WCOMMIT Hγb Hγb' Hγul HeP2@V0'' e↪ainfo2 opId↪ainfo2' P1@V2]") as "HΦ".
  { iSplitL "Hγb Hγul HeP2@V0'' e↪ainfo2"; last iSplitR; last iSplitL.
    - repeat iExists _. iFrame "HN AInv ⊒M2@V2 ⊒Ms@V0'' ⊒Mw@V0'' e✓eV e↪ainfo2 Hγb Hγul HeP2@V0''". iSplit.
      + iApply view_at_unfold. rewrite monPred_at_in. iPureIntro. clear -LeV0'V0'' LeV0''V1 LeV1V2. solve_lat.
      + iPureIntro. split_and!; try done; [set_solver +eM|set_solver +SubainfoM].
    - iPureIntro. split_and!; try done. set_solver-.
    - iExists (qsa2a/2)%Qp. iFrame "P1@V2". repeat iExists _.
      iFrame "HN AInv ⊒M2@V2 ⊒Ms@V0'' ⊒Mw@V0'' opId✓eVop opId↪ainfo2' Hγb'". iSplit.
      + iApply view_at_unfold. rewrite monPred_at_in. iPureIntro. clear -LeV0'V0'' LeV0''V1 LeV1V2. solve_lat.
      + iPureIntro. split_and!; try done; [set_solver-|by right;right|set_solver +SubainfoM|set_solver +SubainfoMw].
    - iPureIntro. split_and!; try done. by eexists. }

  iMod ("Hclose" with "[-HΦ]") as "_".
  { repeat iExists _. iFrame "HN M●2 Ms●2 Mw●2 Hγsa2 Hγwa2 Hγm2 Hγb2". rewrite omo_append_w_write_op.
    iNext. do 4 iExists _. iExists nstf2,_,ewf2,eVsn2,eVwf2,(S (size st1.1.1.1)),_. iExists Vm2,Vwf2. repeat iExists _.
    eapply (dom_same _ _ _ ainfo2) in Hwarc2e as EQdom. rewrite -EQdom. replace (S (size st1.1.1.1)) with (size st1.1.1.1 + 1) by lia.
    iFrame "AllEvents2' AllWeaks2 omos↦2 omow↦2 Hγu2 Hγd2 Hγl2 Hγul2 esn2✓eVsn2 ewf2✓eVwf2 P1@Vp2 RES@Vsf2 e0↪ainfo Hγb0 Hγul0 He0".
    iFrame "⊒upds2@Vwf2 ⊒ulcks2@Vwf2 ⊒stf2s@Vsf2 ⊒stf2w@Vwf2". iSplitR; last iSplitR; last iSplitR; last iSplitL "P2"; last iSplitL.
    - iApply big_sepL_snoc. iFrame "AllStrongs2 NewStrongInner".
    - iApply big_sepL_forall. iIntros "%i %ew %Hew".
      iDestruct (big_sepL_lookup with "AllLocks2") as (eVw zw) "[ew✓eVw [%eVwEV %COND]]"; [exact Hew|].
      iExists eVw,zw. iFrame "ew✓eVw". iPureIntro. split; [done|]. intros. apply COND in H. clear eVEV. des; [by left|]. right.
      exists e0,ainfo0. split; [|done]. rewrite lookup_insert_ne; [done|]. apply elem_of_dom_2, VALsarc2 in H. lia.
    - done.
    - destruct (decide (e = 0)) as [->|NEQ]; [by rewrite lookup_insert|].
      rewrite lookup_insert_ne; [|done]. rewrite lookup_delete_ne; [|done]. done.
    - destruct ty2.
      + iDestruct "Hty2" as "[[H|[(%e' & %ainfo' & %Hsarc2e' & %ewf2IN)|%ZSZ]] H']"; iFrame "H'"; [iLeft; iFrame "H"|..|lia].
        iRight. iLeft. iExists e',ainfo'. iPureIntro. split; [|done]. rewrite lookup_insert_ne; [done|]. apply elem_of_dom_2, VALsarc2 in Hsarc2e'. lia.
      + iDestruct "Hty2" as %(H1 & H2 & H3 & H4). iPureIntro. split_and!; try done. clear eVEV. des.
        exists e0,ainfo0. split_and!; try done; [set_solver +H3|]. rewrite lookup_insert_ne; [done|]. apply elem_of_dom_2, VALsarc2 in H5. lia.
    - iPureIntro. eapply (warc_update_snoc_1 _ _ _ ainfo2 _ _ eVop sarc2 sarc2) in Hwarc2e as H; try done; [|solve_lat|set_solver-].
      eapply (warc_update_2 _ _ _ ainfo2 V2 Vp2) in Hwarc2e as H1; try done; [|set_solver-].
      rewrite !EQdom !last_snoc eVsn2EV /= size_union; [|set_solver +FRESH]. rewrite size_singleton /=.
      replace (Z.of_nat (size st1.1.1.1) + 1)%Z with (Z.of_nat (size st1.1.1.1 + 1)) by lia.
      clear eVEV. des. split_and!; try done.
      + rewrite map_fold_insert_L; [|by apply frac_sum_wf|]; last first.
        { rewrite -not_elem_of_dom. unfold not. intros. apply VALsarc2 in H10. lia. }
        rewrite {1}/frac_sum /=. rewrite -map_fold_init_frac_op Qp.add_assoc -EQqsa2a -EQqsa2. done.
      + rewrite dom_insert_L. unfold ArcsValid. intros. rewrite app_length /=.
        have [EQe0|e0IN] : e0 = opId ∨ e0 ∈ dom sarc2; [set_solver +H10|subst e0;lia|]. apply VALsarc2 in e0IN. lia.
      + rewrite -EQdom dom_insert_L. unfold ArcsValid2. intros. destruct (decide (e0 = length E2)) as [->|NEQ].
        * rewrite lookup_app_1_eq in H10. inversion H10. subst eV0. done.
        * rewrite lookup_app_1_ne in H10; [|done]. apply VALsarcwarc2 in H10 as H11. destruct (eV0.(type)) eqn:HeV0; try done;
          apply VALeid2 in H10; rewrite HeV0 in H10; (have NEQe2 : e2 ≠ opId by lia); set_solver +H11 NEQe2.
      + unfold SeenClone. intros. destruct (decide (e' = length E2)) as [->|NEQe'].
        * rewrite lookup_app_1_eq in H11. inversion H11. subst eV0. done.
        * rewrite lookup_app_1_ne in H11; [|done]. eapply SeenClone2; try done.
          rewrite lookup_insert_ne in H10; [done|]. apply VALeid2 in H11. rewrite H12 in H11. lia.
      + rewrite omo_append_w_write_op lookup_app_1_ne; [done|]. rewrite -omo_write_op_length. lia.
      + rewrite dom_insert_L DOMsarc2. set_solver-.
      + by rewrite /ArcAlive Forall_app Forall_singleton.
      + by eapply EventIdValid_update.
      + rewrite H1 map_fold_insert_L; [|solve_lat|]; last first.
        { rewrite -not_elem_of_dom. unfold not. intros. apply VALsarc2 in H10. lia. }
        replace ((Vbs2 ⊔ V2) ⊔ Vbw2) with ((Vbs2 ⊔ Vbw2) ⊔ V2) by solve_lat.
        replace (((view_join_total opId ainfo2' (map_fold view_join_total Vp2 sarc2) ⊔ (map_fold view_join_total Vp2 warc2 ⊔ V2)) ⊔ Vm2) ⊔ Vwf2)
          with (((map_fold view_join_total Vp2 sarc2 ⊔ map_fold view_join_total Vp2 warc2) ⊔ Vm2) ⊔ Vwf2 ⊔ V2); [solve_lat|].
        rewrite {3}/view_join_total /=. replace ((ainfo.1.1.1.2 ⊔ V1) ⊔ V2) with V2; clear -LeV0'V0'' LeV0''V1 LeV1V2; solve_lat.
      + solve_lat.
      + unfold SeenUpgrade. intros. destruct (decide (e0 = length E2)) as [->|NEQ].
        * rewrite lookup_app_1_eq in H10. inversion H10. subst eV0. right. exists e,ainfo2. rewrite lookup_insert. split; [done|]. set_solver-.
        * rewrite lookup_app_1_ne in H10; [|done]. apply SeenUpgrade2 in H10. destruct (eV0.(type)); try done. des; [by left|].
          right. destruct (decide (e' = e)) as [->|NEQ'].
          -- rewrite Hwarc2e in H10. inversion H10. subst ainfo0. exists e,ainfo2. rewrite lookup_insert. split; [done|]. set_solver +H11.
          -- exists e',ainfo0. rewrite lookup_insert_ne; [|done]. rewrite lookup_delete_ne; [|done]. done.
      + unfold SeenDowngrade. intros. destruct (decide (e0 = length E2)) as [->|NEQ].
        * rewrite lookup_app_1_eq in H10. inversion H10. subst eV0. done.
        * rewrite lookup_app_1_ne in H10; [|done]. apply SeenDowngrade2 in H10. destruct (eV0.(type)); try done. des; [by left|].
          right. exists e',ainfo0. split; [|done]. rewrite lookup_insert_ne; [done|]. apply elem_of_dom_2, VALsarc2 in H10. lia.
      + unfold SeenUnlock. intros. apply SeenUnlock2 in H10. des; [by left|]. right. exists e',ainfo0. split; [|done].
        rewrite lookup_insert_ne; [done|]. apply elem_of_dom_2, VALsarc2 in H10. lia.
      + unfold ArcsSeen. intros. destruct (decide (e0 = opId)) as [->|NEQ].
        * rewrite lookup_insert in H10. inversion H10. subst ainfo0. apply LEwarc2 in Hwarc2e. solve_lat.
        * rewrite lookup_insert_ne in H10; [|done]. by eapply LEsarc2.
      + rewrite /StlistValid Forall_app Forall_singleton. split; [done|]. intros. subst nstf2. simpl in *.
        apply elem_of_dom_2 in Hwarc2e0. rewrite -EQdom DOMwarc2 in Hwarc2e0. done.
      + rewrite decide_False; [done|]. lia.
      + lia. }

  iModIntro. wp_pures. by iApply "HΦ".
Qed.

Lemma drop_fake_spec :
  drop_fake_spec' code.drop_weak ArcInv FakeArc.
Proof.
  intros N DISJ l tid γg M V0 P1 P2. iIntros "#⊒V0 FArc HP2" (Φ) "AU".
  iDestruct "FArc" as (??????????) "(%&%&%&%&%&%&%&%&%&%&%& #HN & #AInv & #⊒M & #⊒Ms & #⊒Mw & #e0✓eV0 & #e✓eV & #⊒ainfo & Hγb & e0↪ainfo &
    Hγul & Hγd & (%Hainfo2 & %eM & %eV0EV & %eVEV & %SubainfoM & %SubainfoMw))".
  iLöb as "IH" forall (ainfo Hainfo2 SubainfoM SubainfoMw) "⊒ainfo".
  wp_lam. wp_pures. rewrite -[Z.to_nat 1]/(1%nat). wp_bind (!ʳˡˣ _)%E.

  (* Inv access 1 *)
  iInv "AInv" as "H" "Hclose".
  iDestruct "H" as (?? γs1 ???????) "(%&%&%& %sarc1 & %warc1 & %qsa1 & %qwa1 & %alive1 & %E1 & %Es1 & %Ew1 & %omo1 & %omos1 &
    %omow1 & %stlist1 & %mos1 & %mow1 & %Mono1 & >HN' & >M●1 & >Ms●1 & >Mw●1 & >Hγsa1 & >Hγwa1 & >Hγb1 & >Hγm1 & Alive1)".
  gname_agree with "HN HN'". iClear "HN'".
  iDestruct (ghost_var_agree with "Hγb Hγb1") as %<-.

  iDestruct (OmoEview_update with "M●1 ⊒M ⊒Mw") as (Mw') "(M●1 & #⊒Mw' & M⊢Mw' & %SubMwMw')".
  iDestruct (OmoEview_update with "M●1 ⊒M ⊒Ms") as (Ms') "(M●1 & #⊒Ms' & M⊢Ms' & %SubMsMs')".
  iCombine "⊒V0 ⊒ainfo" as "⊒V0'". rewrite monPred_in_view_op. set V0' := V0 ⊔ ainfo.1.1.1.2.
  iCombine "⊒M ⊒Ms ⊒Mw ⊒ainfo ⊒Mw' ⊒Ms' AU HP2" as "RES".
  iDestruct (view_at_intro_incl with "RES ⊒V0'") as (V0'')
    "(#⊒V0'' & %LeV0'V0'' & (#⊒M@V0'' & #⊒Ms@V0'' & #⊒Mw@V0'' & #⊒ainfo@V0'' & #⊒Mw'@V0'' & #⊒Ms'@V0'' & AU@V0'' & HP2@V0''))".

  iDestruct "Alive1" as (Vbs1 Vbw1 ty1 uf1 stf1 esf1 ewf1 eVsf1 eVwf1 nsf1) "(%zwf1 & %Vsf1 & %Vwf1 & %Vp1 & %qsa1a & %qsa1b & %qu1 & %qd1 & %upds1 &
    %dgds1 & %lcks1 & %ulcks1 & >#AllEvents1 & >#AllStrongs1 & >#AllWeaks1 & >omos↦1 & >omow↦1 & >Hγu1 & >Hγd1 & >Hγl1 & >Hγul1 &
    >#AllLocks1 & [>#⊒upds1@Vwf1 >#⊒ulcks1@Vwf1] & >#esf1✓eVsf1 & >#ewf1✓eVwf1 & Hnsf1 & P2 & Hty1 & >#⊒stf1s@Vsf1 & >#⊒stf1w@Vwf1 & >Pures)".
  iDestruct "Pures" as %(Subuf1 & LASTesf1 & LASTewf1 & eVsf1EV & eVwf1EV & Hqsa1 & Hqwa1 & VALsarc1 & VALwarc1 & VALsarcwarc1 & SeenClone1 &
    SeenWeakClone1 & HInitWrite1 & LASTstf1 & DOMsarc1 & DOMwarc1 & EQqsa1 & Alive1 & VALeid1 & LeVbs1Vbw1 & GeVsf1 & GeVwf1 &
    SeenUpgrade1 & SeenDowngrade1 & SeenUnlock1 & LEsarc1 & LEwarc1 & VALstlist1 & LeVsf1 & EQnsf1).

  wp_apply (append_only_loc_relaxed_read with "[$Mw●1 $⊒Mw' $omow↦1 $⊒V0'']"); [solve_ndisj|].
  iIntros (ew1 genw1 vw1 Vw1 V1 eVw1 eVwn1) "(Pures & Mw●1 & _ & #MAXew1 & #ew1✓eVw1 & #ewn1✓eVwn1 & _ & #⊒V1 & _ & #⊒Mw1@V1 & omow↦1)".
  iDestruct "Pures" as %(Hgenw1 & eVw1EV & LeV0''V1 & eVwn1EV & eVwn1SYNC).
  iDestruct (big_sepL_lookup with "AllWeaks1") as (eVw1' zw1) "(ew1✓eVw1' & [%eVw1'EV %GEzw1] & Hgenw1)"; [exact Hgenw1|].
  iDestruct (OmoEinfo_agree with "ew1✓eVw1 ew1✓eVw1'") as %<-. rewrite eVw1EV /= in eVw1'EV. subst vw1.

  (* Prove that 1 ≤ zw1 *)
  iDestruct (ghost_var_agree with "Hγul Hγul1") as %<-.
  iDestruct (weak_counter_load_valid with "Mw●1 Hγwa1 [] MAXew1 ew1✓eVw1 ewf1✓eVwf1 e0↪ainfo Hnsf1 Hty1") as %GEzw1'.
  { by rewrite omo_insert_r_write_op. } { by rewrite omo_insert_r_write_op. } { by rewrite eVw1EV. } { by rewrite eVwf1EV. } { done. }
  { done. } { done. } { set_solver +SubainfoMw SubMwMw'. } { rewrite omo_insert_r_write_op. iFrame "AllWeaks1". }
  have NEQzw1 : zw1 ≠ (-1)%Z by lia.

  set ainfo1 := (ainfo.1.1.1.1, ainfo.1.1.1.2 ⊔ V1, ainfo.1.1.2, ainfo.1.2, cas_only).
  set warc1' := <[0 := ainfo1]> (delete 0 warc1).
  iDestruct (ghost_map_lookup with "Hγwa1 e0↪ainfo") as %Hwarc1e0.
  iMod (ghost_map_delete with "Hγwa1 e0↪ainfo") as "Hγwa1".
  iMod (ghost_map_insert 0 ainfo1 with "Hγwa1") as "[Hγwa1 e0↪ainfo1]"; [by apply lookup_delete|].

  iMod ("Hclose" with "[-AU@V0'' Hγb e0↪ainfo1 M⊢Mw' M⊢Ms' Hγul Hγd HP2@V0'']") as "_".
  { repeat iExists _. iFrame "HN M●1 Ms●1 Mw●1 Hγb1 Hγsa1 Hγwa1 Hγm1". rewrite omo_insert_r_write_op.
    iNext. repeat iExists _. apply (dom_same _ _ _ ainfo1) in Hwarc1e0 as EQdom. rewrite -EQdom.
    iFrame "AllEvents1 AllStrongs1 AllWeaks1 omos↦1 omow↦1 Hγu1 Hγd1 Hγl1 Hγul1 AllLocks1 Hnsf1 Hty1".
    iFrame "esf1✓eVsf1 ewf1✓eVwf1 ⊒upds1@Vwf1 ⊒ulcks1@Vwf1 ⊒stf1s@Vsf1 ⊒stf1w@Vwf1". iSplitL.
    - by rewrite lookup_insert.
    - iPureIntro. eapply (warc_update_1 _ _ _ ainfo1) in Hwarc1e0 as H; try done; [|solve_lat].
      eapply (warc_update_2 _ _ _ ainfo1) in Hwarc1e0 as H0; try done. clear eVEV. des. split_and!; try done.
      + rewrite H0. replace (Vbs1 ⊔ (Vbw1 ⊔ V1)) with ((Vbs1 ⊔ Vbw1) ⊔ V1) by solve_lat. clear -LeVbs1Vbw1. solve_lat.
      + rewrite H0. destruct (decide (nsf1 = 0)); [|done]. solve_lat. }

  iModIntro. wp_pures. rewrite -[Z.to_nat 1]/(1%nat). wp_bind (casʳᵉˡ(_,_,_))%E.
  iApply wp_hist_inv; [done|]. iIntros "#HInv".

  (* Inv access 2 *)
  iInv "AInv" as "H" "Hclose".
  iDestruct "H" as (?? γs2 ???????) "(%&%&%& %sarc2 & %warc2 & %qsa2 & %qwa2 & %alive2 & %E2 & %Es2 & %Ew2 & %omo2 & %omos2 &
    %omow2 & %stlist2 & %mos2 & %mow2 & %Mono2 & >HN' & >M●2 & >Ms●2 & >Mw●2 & >Hγsa2 & >Hγwa2 & >Hγb2 & >Hγm2 & Alive2)".
  gname_agree with "HN HN'". iClear "HN'".
  iDestruct (ghost_var_agree with "Hγb Hγb2") as %<-.

  iDestruct "Alive2" as (Vbs2 Vbw2 ty2 uf2 stf2 esf2 ewf2 eVsf2 eVwf2 nsf2) "(%zwf2 & %Vsf2 & %Vwf2 & %Vp2 & %qsa2a & %qsa2b & %qu2 & %qd2 & %upds2 &
    %dgds2 & %lcks2 & %ulcks2 & >#AllEvents2 & >#AllStrongs2 & >#AllWeaks2 & >omos↦2 & >omow↦2 & >Hγu2 & >Hγd2 & >Hγl2 & >Hγul2 &
    >#AllLocks2 & [>#⊒upds2@Vwf2 >#⊒ulcks2@Vwf2] & >#esf2✓eVsf2 & >#ewf2✓eVwf2 & Hnsf2 & P2 & Hty2 & >#⊒stf2s@Vsf2 & >#⊒stf2w@Vwf2 & >Pures)".
  iDestruct "Pures" as %(Subuf2 & LASTesf2 & LASTewf2 & eVsf2EV & eVwf2EV & Hqsa2 & Hqwa2 & VALsarc2 & VALwarc2 & VALsarcwarc2 & SeenClone2 &
    SeenWeakClone2 & HInitWrite2 & LASTstf2 & DOMsarc2 & DOMwarc2 & EQqsa2 & Alive2 & VALeid2 & LeVbs2Vbw2 & GeVsf2 & GeVwf2 &
    SeenUpgrade2 & SeenDowngrade2 & SeenUnlock2 & LEsarc2 & LEwarc2 & VALstlist2 & LeVsf2 & EQnsf2).
  iDestruct (OmoAuth_wf with "M●2") as %[OMO_GOOD2 _]. iDestruct (OmoAuth_omo_nonempty with "M●2") as %Nomo2.
  have NZomo2 : length omo2 ≠ 0 by destruct omo2.
  iDestruct (OmoSnapOmo_get with "Mw●2") as "#Mw◯2".
  iMod (rel_objectively_intro (⊒∅) tid with "[]") as "#⊒∅"; [by iApply objective_objectively; iApply monPred_in_bot|].

  wp_apply (append_only_loc_cas_general _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ∅ with "[$Mw●2 $⊒Mw' $omow↦2 $⊒V1]");
    try done; [solve_ndisj|..]; [set_solver +NEQzw1 Subuf2|].
  iIntros (b2 ew2 genw2 vw2 Vw2 V2 mow2' omow2' eVw2 eVwn2)
    "(Pures & #MAXew2 & #ew2✓eVw2 & #ewn2✓eVwn2 & Mw●2 & #⊒V2 & #⊒Mw2@V2 & CASE)".
  iDestruct "Pures" as %(Eqgenw2 & eVw2EV & LeV1V2).
  iDestruct "CASE" as "[(Pures & _ & omow↦2 & _) | [Pures sVw2]]".
  { (* CAS failed, try again *)
    iDestruct "Pures" as %(-> & NEQvw2 & -> & -> & eVwn2EV & eVwn2SYNC).

    set ainfo2 := (ainfo1.1.1.1.1, ainfo1.1.1.1.2 ⊔ V2, ainfo1.1.1.2, ainfo1.1.2, cas_only).
    set warc2' := <[0 := ainfo2]> (delete 0 warc2).
    iDestruct (ghost_map_lookup with "Hγwa2 e0↪ainfo1") as %Hwarc2e0.
    iMod (ghost_map_delete with "Hγwa2 e0↪ainfo1") as "Hγwa2".
    iMod (ghost_map_insert 0 ainfo2 with "Hγwa2") as "[Hγwa2 e0↪ainfo2]"; [by apply lookup_delete|].

    iMod ("Hclose" with "[-Hγb e0↪ainfo2 AU@V0'' Hγul Hγd HP2@V0'']") as "_".
    { repeat iExists _. iFrame "HN M●2 Ms●2 Mw●2 Hγsa2 Hγwa2 Hγm2 Hγb2". rewrite omo_insert_r_write_op.
      iNext. repeat iExists _. eapply (dom_same _ _ _ ainfo2) in Hwarc2e0 as EQdom. rewrite -EQdom.
      iFrame "AllEvents2 AllStrongs2 AllWeaks2 omos↦2 omow↦2 Hγu2 Hγd2 Hγl2 Hγul2 AllLocks2 Hnsf2 Hty2".
      iFrame "esf2✓eVsf2 ewf2✓eVwf2 ⊒upds2@Vwf2 ⊒ulcks2@Vwf2 ⊒stf2s@Vsf2 ⊒stf2w@Vwf2". iSplitL.
      - by rewrite lookup_insert.
      - iPureIntro. eapply (warc_update_1 _ _ _ ainfo2) in Hwarc2e0 as H; try done; [|solve_lat].
        eapply (warc_update_2 _ _ _ ainfo2) in Hwarc2e0 as H0; try done. clear eVEV. des. split_and!; try done.
        + rewrite H0. replace (Vbs2 ⊔ (Vbw2 ⊔ V2)) with ((Vbs2 ⊔ Vbw2) ⊔ V2) by solve_lat. clear -LeVbs2Vbw2. solve_lat.
        + destruct (decide (nsf2 = 0)); [|done]. rewrite H0. clear -LeVsf2. solve_lat. }

    iModIntro. wp_if. replace (ainfo.1.1.1.1/2)%Qp with (ainfo2.1.1.1.1/2)%Qp by done.
    iDestruct (view_at_elim with "⊒V0'' AU@V0''") as "AU".
    iDestruct (view_at_elim with "⊒V0'' HP2@V0''") as "HP2".
    iApply ("IH" with "[] [] [] Hγb e0↪ainfo2 Hγul Hγd HP2 AU []"); [done..|].
    subst ainfo2 ainfo1. simpl. replace ((ainfo.1.1.1.2 ⊔ V1) ⊔ V2) with V2; [done|]. solve_lat. }

  (* CAS success, commit [WeakDrop] *)
  iDestruct "Pures" as %(-> & -> & ->).
  iDestruct "sVw2" as (Vm2) "((%Hmow2' & %Homow2' & %eVwn2EV & %eVwn2SYNC & %LeVw2Vm2 & %NEqVw2Vm2 & %NLeV2Vw2 & %NEqV1V2 & %LeV2Vm2) &
    #⊒Mw2@Vm2 & omow↦2 & #⊒Vm2 & WCOMMIT)".

  rewrite last_lookup -omo_write_op_length in LASTewf2.
  replace (Init.Nat.pred (length omow2)) with (length omow2 - 1) in LASTewf2 by lia.
  rewrite LASTewf2 in Eqgenw2. inversion Eqgenw2. subst ew2.
  iDestruct (OmoEinfo_agree with "ewf2✓eVwf2 ew2✓eVw2") as %<-.
  rewrite eVwf2EV in eVw2EV. inversion eVw2EV. subst zwf2 Vw2.

  destruct ty2; [|by iDestruct "Hty2" as %[? _]].
  iDestruct "Hty2" as "[_ [%Hzw1 ->]]". subst zw1.
  destruct (decide (size stf2.2.1.1 = 1)) as [EQstf2|NEQstf2].
  - (* This FakeArc is the last one. Commit [WeakDrop 0 true] *)
    set V2' := V2 ⊔ Vm2.
    have LeV0V2' : V0 ⊑ V2' by solve_lat.
    set opId := length E2.
    set M2 : eView := {[opId]} ∪ (M ∪ stf2.1.2 ∪ stf2.2.2).
    set eVop := mkOmoEvent (WeakDrop 0 true) V2' M2.
    set E2' := E2 ++ [eVop].
    set nstf2 : arc_state := (stf2.1, (∅, stf2.2.1.2, stf2.2.2)).

    iDestruct (ghost_map_lookup with "Hγwa2 e0↪ainfo1") as %Hwarc2e0.
    apply size_1_elem_of in EQstf2 as Hstf2. destruct Hstf2 as [x Hstf2]. fold_leibniz.
    rewrite Hstf2 in DOMwarc2. apply dom_singleton_inv_L in DOMwarc2 as [x' Hwarc2].
    rewrite Hwarc2 lookup_singleton_Some in Hwarc2e0. destruct Hwarc2e0 as [-> ->].

    (* Prove that there is no other StrongArc *)
    destruct nsf2; last first.
    { iDestruct "Hnsf2" as "(_ & _ & _ & e0↪ainfo & _)". by iDestruct (ghost_map_elem_valid_2 with "e0↪ainfo1 e0↪ainfo") as %[? _]. }
    symmetry in EQnsf2. apply size_empty_inv in EQnsf2. fold_leibniz.
    rewrite EQnsf2 dom_empty_iff_L in DOMsarc2.

    have LeVp2ainfo1 : Vp2 ⊑ ainfo1.1.1.1.2 by apply (LEwarc2 0); rewrite Hwarc2 lookup_singleton.

    iAssert (|={_,_}=> @{V2'} (OmoAuth γg γs2 (1/2)%Qp E2' (omo_append_w omo2 opId []) (stlist2 ++ [nstf2]) _ ∗
                               ((P2 ∗ l ↦ #0 ∗ (l >> 1) ↦ #0) -∗ Φ #true)))%I with "[M●2 WCOMMIT AU@V0'']" as ">[M●2 HΦ]".
    { iDestruct (view_at_mono_2 _ V2' with "AU@V0''") as "AU@V2'"; [solve_lat|].
      iCombine "M●2 WCOMMIT ⊒stf2s@Vsf2 ⊒stf2w@Vwf2 ⊒M@V0''" as "RES".
      iDestruct (view_at_objective_iff _ V2' with "RES") as "RES@V2'".
      iAssert (@{V2'} ⊒V2')%I with "[-]" as "#⊒V2'@V2'"; [done|].
      iCombine "RES@V2' AU@V2' ⊒V2'@V2'" as "RES".
      rewrite -view_at_fupd. iApply (view_at_mono with "RES"); [done|].

      iIntros "((M●2 & WCOMMIT & #⊒stf2s@Vsf2 & #⊒stf2w@Vwf2 & #⊒M@V0'') & AU & #⊒V2')".
      iDestruct (view_at_mono_2 _ V2' with "⊒M@V0''") as "⊒M@V2'"; [solve_lat|].
      have LeVsf2V2' : Vsf2 ⊑ V2' by rewrite Hwarc2 map_fold_singleton_view_join_total /= in LeVsf2; solve_lat.
      iDestruct (view_at_mono_2 _ V2' with "⊒stf2s@Vsf2") as "⊒stf2s@V2'"; [done|].
      iDestruct (view_at_mono_2 _ V2' with "⊒stf2w@Vwf2") as "⊒stf2w@V2'"; [solve_lat|].
      iDestruct (OmoEview_union_obj with "⊒M@V2' ⊒stf2s@V2'") as "⊒M'@V2'".
      iDestruct (OmoEview_union_obj with "⊒M'@V2' ⊒stf2w@V2'") as "⊒M''@V2'".

      iMod "AU" as (????) "[>M●2' [_ Commit]]".
      iDestruct (OmoAuth_agree with "M●2 M●2'") as %(<- & <- & <- & <-). iCombine "M●2 M●2'" as "M●2".
      iMod (OmoAuth_insert_last with "M●2 ⊒M''@V2' WCOMMIT []") as "(M●2 & #⊒M2@V2' & _ & _ & _ & WCOMMIT)".
      { have ? : step opId eVop stf2 nstf2; [|done]. eapply arc_step_WeakDrop_last; try done; subst eVop; [set_solver-|solve_lat]. }
      iDestruct (OmoHbToken_finish with "M●2") as "[M●2 M●2']".

      iMod ("Commit" $! true V2' γs2 _ _ M2 with "[$⊒V2' $M●2' $WCOMMIT $⊒M2@V2']") as "HΦ".
      { iPureIntro. split_and!; try done; [set_solver-|]. exists (length omo2). rewrite omo_insert_w_append_w; done. }

      iModIntro. iFrame "M●2 HΦ". }

    (* Collect all fractions *)
    rewrite DOMsarc2 map_fold_empty in Hqsa2. rewrite Hqsa2.
    rewrite Hwarc2 map_fold_singleton_frac_sum /frac_sum Qp.add_comm in Hqwa2.
    iCombine "Hγb2 Hγb" as "Hγb2". rewrite -Qp.add_assoc -Qp.div_add_distr Hqwa2 Qp.half_half.
    iMod (ghost_var_update false with "Hγb2") as "Hγb2". rewrite -{13}Qp.half_half.
    iMod (ghost_map_delete with "Hγwa2 e0↪ainfo1") as "Hγwa2".
    have Hwarc2' : delete 0 warc2 = ∅ by rewrite Hwarc2 delete_singleton. rewrite DOMsarc2 Hwarc2'.

    (* Collect all resources *)
    rewrite DOMsarc2 Hwarc2 map_fold_empty map_fold_singleton_view_join_total /view_join_total in LeVbs2Vbw2.
    rewrite Hwarc2 map_fold_singleton_view_join_total /= /view_join_total in LeVsf2.
    have LeVbs2Vbw2V2 : Vbs2 ⊔ Vbw2 ⊑ V2' by solve_lat.
    iDestruct (view_at_mono_2 _ V2' with "omos↦2") as "omos↦2"; [solve_lat|].
    iDestruct (view_at_mono_2 _ V2' with "omow↦2") as "omow↦2"; [solve_lat|].

    iAssert (|={_,_}=> @{V2'} (OmoAuth γes γss (1 / 2) Es2 omos2 mos2 _ ∗
        OmoAuth γew γsw (1 / 2) (Ew2 ++ [eVwn2]) omow2' mow2' _ ∗
        l ↦ #0 ∗ (l >> 1) ↦ #0))%I with "[Ms●2 Mw●2 omos↦2 omow↦2]" as ">(Ms●2 & Mw●2 & ls↦ & lw↦)".
    { iCombine "Ms●2 Mw●2 esf2✓eVsf2 ewn2✓eVwn2 HInv" as "RES".
      iDestruct (view_at_objective_iff _ V2' with "RES") as "RES". iCombine "RES omos↦2 omow↦2" as "RES".
      rewrite -view_at_fupd. iApply (view_at_mono with "RES"); [done|].

      iIntros "((Ms●2 & Mw●2 & #esf2✓eVsf2 & #ewn2✓eVwn2 & #HInv) & omos↦2 & omow↦2)".
      iMod (append_only_loc_to_na with "HInv Ms●2 omos↦2") as (vs es eVs) "(ls↦ & [Ms●2 _] & #es✓eVs & [%Hes %eVsEV])"; [solve_ndisj|].
      iMod (append_only_loc_to_na with "HInv Mw●2 omow↦2") as (vw ew eVw) "(lw↦ & [Mw●2 _] & #ew✓eVw & [%Hew %eVwEV])"; [solve_ndisj|].

      rewrite LASTesf2 in Hes. inversion Hes. subst es.
      iDestruct (OmoEinfo_agree with "esf2✓eVsf2 es✓eVs") as %<-.
      rewrite eVsf2EV in eVsEV. subst vs.

      rewrite Homow2' omo_append_w_write_op last_snoc in Hew. inversion Hew. subst ew.
      iDestruct (OmoEinfo_agree with "ewn2✓eVwn2 ew✓eVw") as %<-.
      rewrite eVwn2EV in eVwEV. subst vw. simpl.
      rewrite Hstf2 size_singleton. replace (Z.of_nat 1 - 1)%Z with 0%Z by lia.

      iModIntro. iFrame "Ms●2 Mw●2 ls↦ lw↦". }

    rewrite !view_at_objective_iff.
    iMod ("Hclose" with "[-HΦ HP2@V0'' ls↦ lw↦]") as "_"; [repeat iExists _; iFrame "HN M●2 Ms●2 Mw●2 Hγsa2 Hγwa2 Hγb2 Hγm2"|].

    iModIntro. wp_pures. rewrite bool_decide_true; [|lia].
    wp_apply (wp_acq_fence with "⊒Vm2"); [solve_ndisj|]. iClear "⊒Vm2". iIntros "#⊒Vm2". wp_pures.

    iCombine "⊒V2 ⊒Vm2" as "⊒V2'". rewrite monPred_in_view_op. iCombine "HΦ ls↦ lw↦" as "RES".
    iDestruct (view_at_elim with "⊒V2' RES") as "(HΦ & ls↦ & lw↦)".
    iDestruct (view_at_elim with "⊒V0'' HP2@V0''") as "P2".
    iApply ("HΦ" with "[$P2 $ls↦ $lw↦]").
  - (* This FakeArc is not the last one. Commit [WeakDrop 0 false] *)
    (* Insert [WeakDrop] event right after the latest observation in eView *)
    iDestruct (OmoEview_latest_elem with "⊒M") as (e1) "[MAXe1 %e1IN]".
    iDestruct (OmoAuth_OmoEview with "M●2 ⊒M") as %VALM.
    apply VALM in e1IN as He1.
    eapply lookup_omo_surjective in He1 as Heidx1; [|done]. destruct Heidx1 as [eidx1 Heidx1].
    eapply omo_stlist_length in OMO_GOOD2 as EQlenST2.
    have [st1 Hst1] : is_Some (stlist2 !! (gen_of eidx1)).
    { rewrite lookup_lt_is_Some -EQlenST2. apply lookup_omo_lt_Some in Heidx1. done. }

    iDestruct (OmoAuth_OmoEinfo with "M●2 e0✓eV0") as %HeV0.
    iDestruct (ghost_map_lookup with "Hγwa2 e0↪ainfo1") as %Hwarc2e0.
    have [st0 Hst0] : is_Some (stlist2 !! 0) by rewrite lookup_lt_is_Some -EQlenST2; lia.
    have e0INdom : 0 ∈ dom warc2 by apply elem_of_dom_2 in Hwarc2e0.
    have LEgen0gen1 : 0 ≤ gen_of eidx1 by lia.

    iDestruct (OmoAuth_OmoEinfo with "M●2 e✓eV") as %HeV.
    iDestruct (OmoAuth_OmoEinfo' with "M●2 e✓eV") as %[eidx Heidx].
    iDestruct (big_sepS_elem_of _ _ e with "MAXe1") as "e≤e1"; [done|].
    iDestruct (OmoLe_Le with "M●2 e≤e1") as %LEgengen1; [done|done|].

    have LeV0V2 : V0 ⊑ V2 by solve_lat.
    set opId := length E2.
    set M2 : eView := {[opId]} ∪ M.
    set eVop := mkOmoEvent (WeakDrop 0 false) V2 M2.
    set E2' := E2 ++ [eVop].
    set nst1 : arc_state := (st1.1, (st1.2.1.1 ∖ {[0]}, st1.2.1.2 ⊔ eVop.(sync), st1.2.2 ∪ eVop.(eview))).

    have eV0EV' : eV0.(type) = StrongInit ∨ eV0.(type) = WeakInit ∨ (∃ e', eV0.(type) = WeakClone e') ∨ eV0.(type) = Downgrade by left.
    rewrite -lookup_omo_wr_event in HInitWrite2.
    specialize (weak_arc_persist _ _ _ _ _ _ (dom sarc2) (dom warc2) OMO_GOOD2 HInitWrite2 HeV0 eV0EV' e0INdom VALsarcwarc2) as Hstlist2.
    clear eV0EV'. rewrite lookup_omo_wr_event in HInitWrite2.
    iDestruct (OmoUB_into_gen with "M●2 MAXe1") as %MAXe1; [done|].
    iAssert (∀ i sti, ⌜ stlist2 !! i = Some sti → gen_of eidx1 ≤ i → {[0]} ⊂ sti.2.1.1 ⌝)%I with "[-]" as %SSub.
    { iIntros (i sti) "%Hsti %LEi".
      apply Hstlist2 in Hsti as e0INsti; [|simpl;lia].
      have Sub : {[0]} ⊆ sti.2.1.1 by clear -e0INsti; set_solver.
      destruct (decide (sti.2.1.1 = {[0]})) as [EQ|NEQ]; [|iPureIntro;set_solver +Sub NEQ].

      specialize (weak_state_no_decrease _ _ _ _ _ _ _ _ OMO_GOOD2 Hsti EQ VALsarcwarc2 HInitWrite2 e0INdom) as Hstweak2.
      rewrite last_lookup -EQlenST2 in LASTstf2.
      replace (Init.Nat.pred (length omo2)) with (length omo2 - 1) in LASTstf2 by lia.
      have LECOND : i ≤ length omo2 - 1 by apply lookup_lt_Some in Hsti; rewrite -EQlenST2 in Hsti; lia.
      specialize (Hstweak2 _ _ LECOND LASTstf2). clear eVEV. des.
      - apply (f_equal size) in Hstweak2. rewrite EQ size_singleton in Hstweak2. lia.
      - unfold SeenWeakClone in SeenWeakClone2. eapply SeenWeakClone2 in Hwarc2e0; [|done|done].
        have ekIN : ek ∈ M by set_solver +Hwarc2e0 SubainfoM.
        apply MAXe1 in ekIN as (eidxk & Heidxk & LEgen). rewrite -lookup_omo_wr_event in Hstweak4.
        eapply lookup_omo_inj in Heidxk; [|done|exact Hstweak4]. subst eidxk. simpl in LEgen. lia.
      - destruct nsf2; last first.
        { iDestruct "Hnsf2" as "(_ & _ & _ & e0↪ainfo & _)". by iDestruct (ghost_map_elem_valid_2 with "e0↪ainfo1 e0↪ainfo") as %[? _]. }
        symmetry in EQnsf2. apply size_empty_inv in EQnsf2. fold_leibniz.
        rewrite EQnsf2 dom_empty_iff_L in DOMsarc2. apply SeenDowngrade2 in Hstweak5.
        rewrite Hstweak6 in Hstweak5. des; [|by rewrite DOMsarc2 in Hstweak5].
        iDestruct (ghost_var_agree with "Hγd Hγd2") as %<-.
        have ekIN : ek ∈ M by set_solver +SubainfoM Hstweak5.
        apply MAXe1 in ekIN as (eidxk & Heidxk & LE). rewrite -lookup_omo_wr_event in Hstweak4.
        eapply lookup_omo_inj in Heidxk; [|done|exact Hstweak4]. subst eidxk. simpl in LE. lia. }
    apply SSub in Hst1 as SSubst1; [|done].

    have HNoStrong : ∀ i sti, stlist2 !! i = Some sti → gen_of eidx ≤ i → sti.1.1.1 = ∅.
    { intros. generalize dependent sti. induction H0 as [|i]; intros.
      - destruct eidx; last destruct gen.
        + eapply omo_read_op_step in Heidx as STEP; try done. des;
          inversion STEP; subst; simpl in *; rewrite eVEV in EVENT; try done;
          rewrite NST in STRONG; set_solver +STRONG.
        + rewrite lookup_omo_wr_event HInitWrite2 in Heidx. inversion Heidx. subst e.
          rewrite HeV0 in HeV. inversion HeV. subst eV0. des; rewrite eV0EV in eVEV; done.
        + rewrite lookup_omo_wr_event in Heidx. replace (S gen) with (gen + 1) in H, Heidx by lia. simpl in H.
          have [sti' H'] : is_Some (stlist2 !! gen).
          { rewrite lookup_lt_is_Some. apply lookup_lt_Some in H. lia. }
          eapply omo_write_op_step in H as STEP; try done. des; inversion STEP; subst; simpl in *; rewrite eVEV in EVENT; try done.
      - replace (S i) with (i + 1) in H by lia.
        have [sti' H'] : is_Some (stlist2 !! i) by rewrite lookup_lt_is_Some; apply lookup_lt_Some in H; lia.
        have [ei Hei] : is_Some (omo_write_op omo2 !! (i + 1)%nat).
        { rewrite lookup_lt_is_Some -omo_write_op_length EQlenST2. apply lookup_lt_Some in H. done. }
        rewrite -lookup_omo_wr_event in Hei. eapply lookup_omo_event_valid in Hei as HeVi; [|done].
        destruct HeVi as [eVi HeVi]. rewrite lookup_omo_wr_event in Hei.
        apply IHle in H' as EQsti'. eapply omo_write_op_step in OMO_GOOD2 as STEP; try done.
        inversion STEP; subst; simpl in *; try done.
        + rewrite -!lookup_omo_wr_event in Hei,HInitWrite2. eapply lookup_omo_inj in Hei; [|done|exact HInitWrite2]. inversion Hei. lia.
        + rewrite EQsti' in IDVAL. done.
        + rewrite EQsti' in STRICT. set_solver +STRICT. }

    have STEPop : step opId eVop st1 nst1 by eapply arc_step_WeakDrop; try done; set_solver-.
    have NoWeakClone : ∀ e' eidx' eV', lookup_omo omo2 eidx' = Some e' → E2 !! e' = Some eV' → gen_of eidx1 < gen_of eidx' → eV'.(type) ≠ WeakClone 0.
    { intros. unfold not. intros. unfold SeenWeakClone in SeenWeakClone2. eapply SeenWeakClone2 in Hwarc2e0; [|done..].
      have e'IN : e' ∈ M by set_solver +Hwarc2e0 SubainfoM. apply MAXe1 in e'IN as (eidx'' & Heidx'' & LE).
      eapply lookup_omo_inj in H; [|done|exact Heidx'']. subst eidx''. lia. }
    specialize (weak_arc_delete_gen_good _ _ _ _ _ _ _ _ _ OMO_GOOD2 Hst1 STEPop HInitWrite2 SSub NoWeakClone Alive2) as (stlist2' & Hgengood2 & Hstlist2').

    iDestruct (view_at_elim with "⊒V0'' AU@V0''") as "AU".
    iMod "AU" as (????) "[>M●2' [_ Commit]]".
    iDestruct (OmoAuth_agree with "M●2 M●2'") as %(<- & <- & <- & <-). iCombine "M●2 M●2'" as "M●2".
    iDestruct (OmoSnapStates_get with "M●2") as "#ST◯2".

    iDestruct (view_at_mono_2 _ V2 with "⊒M@V0''") as "⊒M@V2"; [solve_lat|].
    iMod (OmoAuth_insert _ _ _ _ _ _ _ _ _ _ (gen_of eidx1) with "M●2 ⊒M@V2 WCOMMIT []") as (γs2')
      "(M●2 & #⊒M2@V2 & #opId↦ewn2 & #opId✓eVop & WCOMMIT)"; [iPureIntro; split_and!; try done; [by subst eVop|set_solver-]|].
    iMod (OmoHb_new_2 _ _ _ _ _ _ _ _ (length Ew2) ({[length Ew2]} ∪ Mw') with "M●2 [] opId✓eVop") as "[M●2 #opId⊒ewn2]".
    { set_solver-. } { iFrame "⊒Mw2@V2". }

    iMod (SeenPrevStrong_after_weak_event with "M●2 Ms●2 Mw●2 omos↦2 Hγm2 [] M⊢Ms' AllEvents2 AllStrongs2 opId✓eVop opId↦ewn2")
      as "(#SeenPrevStrongopId & [M●2 M●2'] & Ms●2 & Mw●2 & omos↦2 & Hγm2 & M⊢Ms')"; [exact e1IN|done|done|..].
    { iDestruct (view_at_mono_2 _ V2 with "⊒Ms'@V0''") as "⊒Ms'@V2"; [solve_lat|]. iFrame "⊒Ms'@V2". }

    iDestruct (AllStrongs_update with "M●2 Ms●2 Mw●2 omos↦2 AllStrongs2 opId↦ewn2 ST◯2") as "#AllStrongs2'";
      [done|..|done|by apply lookup_omo_lt_Some in Heidx1|]. { intros. eapply Hstlist2' in H; [|done]. rewrite H. done. }

    iMod (ghost_map_delete with "Hγwa2 e0↪ainfo1") as "Hγwa2".
    iCombine "Hγb2 Hγb" as "Hγb2". rewrite -Qp.add_assoc -Qp.div_add_distr.
    iDestruct (ghost_var_agree with "Hγul Hγul2") as %<-. iCombine "Hγul2 Hγul" as "Hγul2".

    iMod ("Commit" $! false V2 γs2' _ _ M2 with "[$⊒V2 $M●2' $WCOMMIT $⊒M2@V2]") as "HΦ".
    { iPureIntro. split_and!; try done; [set_solver-|]. by eexists. }

    iDestruct (OmoAuth_wf with "M●2") as %[OMO_GOOD2' _].
    eapply weak_arc_delete_new_state in OMO_GOOD2 as Hnstf2'; [|exact OMO_GOOD2'|done..]. destruct Hnstf2' as (nstf2 & Hnstf2 & Hnstf2').
    set upds2' := upds2 ∪ ainfo1.1.1.2.
    iMod (ghost_var_update upds2' with "Hγu2") as "Hγu2".

    iMod ("Hclose" with "[-HΦ]") as "_".
    { repeat iExists _. iFrame "HN M●2 Ms●2 Mw●2 Hγsa2 Hγwa2 Hγb2 Hγm2".
      iNext. do 4 iExists _. iExists nstf2. repeat iExists _. iCombine "⊒upds2@Vwf2 ⊒ulcks2@Vwf2 ⊒stf2w@Vwf2" as "RES".
      iDestruct (view_at_mono_2 _ Vm2 with "RES") as "(⊒upds2@Vm2 & ⊒ulcks2@Vm2 & ⊒stf2w@Vm2)"; [solve_lat|].
      iFrame "AllStrongs2' omos↦2 omow↦2 Hγu2 Hγd2 Hγl2 Hγul2 Hnsf2 esf2✓eVsf2 ewn2✓eVwn2 ⊒ulcks2@Vm2".
      iDestruct (view_at_mono_2 _ Vm2 with "⊒M2@V2") as "⊒M2@Vm2"; [done|].
      iDestruct (view_at_mono_2 _ Vm2 with "HP2@V0''") as "HP2@Vm2"; [solve_lat|].
      iDestruct (OmoEview_union_obj with "⊒stf2w@Vm2 ⊒M2@Vm2") as "⊒nstf2w@Vm2".
      iDestruct (OmoEview_union_obj with "⊒upds2@Vm2 ⊒M2@Vm2") as "⊒upds2'@Vm2".
      iDestruct (OmoEview_nonempty_obj with "⊒upds2@Vm2") as %Nupds2.
      iDestruct (OmoEview_mono_obj _ _ upds2' with "⊒upds2'@Vm2") as "⊒upds2''@Vm2"; [set_solver +SubainfoM|set_solver +Nupds2|].
      rewrite Hnstf2' lookup_delete /=. iFrame "HP2@Vm2 ⊒upds2''@Vm2 ⊒stf2s@Vsf2 ⊒nstf2w@Vm2". iSplit; last iSplit; last iSplit; last iSplit.
      - iApply big_sepL_snoc. iFrame "AllEvents2 SeenPrevStrongopId".
      - rewrite Homow2' omo_append_w_write_op. iApply big_sepL_snoc. iSplit.
        + iApply big_sepL_forall. iIntros "%i %ew %Hew".
          iDestruct (big_sepL_lookup with "AllWeaks2") as (eVw zw) "(ew✓eVw & [%eVwEV %GEzw] & Hi)"; [exact Hew|].
          rewrite dom_delete_L. iExists eVw,zw. iFrame "ew✓eVw". iSplit; [done|]. destruct i; [done|].
          iDestruct "Hi" as (????) "(Mw◯ & ew'✓eVw' & Pures & CASE)". repeat iExists _. iFrame "Mw◯ ew'✓eVw' Pures".
          iDestruct "CASE" as "[CASE|[CASE|[CASE|CASE]]]"; [|by iRight;iLeft|by iRight;iRight;iLeft|by iRight;iRight;iRight].
          iLeft. iDestruct "CASE" as (e' eV') "(e'↦ew & e'✓eV' & e'⊒ew & %)". repeat iExists _. iFrame "e'↦ew e'✓eV' e'⊒ew".
          iPureIntro. clear eVEV. des; split_and!; try done; [by left|].
          right. exists e'0. split; [done|]. intros. apply H2. des. split; [done|]. set_solver +H4.
        + rewrite dom_delete_L. iExists eVwn2,(size stf2.2.1.1 - 1)%Z. iFrame "ewn2✓eVwn2". iSplit.
          { iPureIntro. rewrite eVwn2EV. split; [|lia]. simpl. done. }
          rewrite -omo_write_op_length. destruct (length omow2) eqn:Hlen; [done|]. rewrite -Hlen. rewrite -Hlen in LASTewf2. clear Hlen n.
          iExists omow2,ewf2,eVwf2,(size stf2.2.1.1). iFrame "Mw◯2 ewf2✓eVwf2". iSplit; [by rewrite eVwf2EV|].
          iRight. iLeft. iPureIntro. split; try done.
      - rewrite Homow2' omo_append_w_write_op. iApply big_sepL_snoc. iFrame "AllLocks2".
        iExists eVwn2,(size stf2.2.1.1 - 1)%Z. iFrame "ewn2✓eVwn2". iPureIntro.
        rewrite eVwn2EV. split; [done|]. intros. lia.
      - iSplit; [|done]. iLeft. iExists opId. iFrame "opId⊒ewn2".
      - rewrite Homow2' omo_append_w_write_op last_snoc size_difference; last first.
        { apply elem_of_dom_2 in Hwarc2e0. rewrite DOMwarc2 in Hwarc2e0. set_solver +Hwarc2e0. }
        rewrite size_singleton eVwn2EV Hnstf2 Hnstf2' dom_delete_L DOMwarc2 /ArcAlive Forall_app Forall_singleton /=.
        replace (Z.of_nat (size stf2.2.1.1) - 1)%Z with (Z.of_nat (size stf2.2.1.1 - 1)) by lia.
        iPureIntro. split_and!; try done.
        + rewrite Qp.add_comm map_fold_init_frac_op. rewrite (map_fold_delete_L _ _ 0 ainfo1) in Hqwa2; [|by apply frac_sum_wf|done].
          rewrite {1}/frac_sum /= in Hqwa2. done.
        + unfold ArcsValid. intros. apply VALsarc2 in H. rewrite app_length /=. lia.
        + unfold ArcsValid. rewrite -DOMwarc2. intros. have e0IN : e0 ∈ dom warc2 by set_solver +H.
          apply VALwarc2 in e0IN. rewrite app_length /=. lia.
        + unfold ArcsValid2. rewrite -DOMwarc2. intros. destruct (decide (e0 = length E2)) as [->|NEQ].
          * rewrite lookup_app_1_eq in H. inversion H. subst eV1. simpl. set_solver-.
          * rewrite lookup_app_1_ne in H; [|done]. apply VALsarcwarc2 in H. destruct (eV1.(type)); try done. set_solver +H.
        + unfold SeenClone. intros. destruct (decide (e' = length E2)) as [->|NEQ].
          * rewrite lookup_app_1_eq in H0. inversion H0. subst eV1. done.
          * rewrite lookup_app_1_ne in H0; [|done]. eapply SeenClone2; try done.
        + unfold SeenWeakClone. intros. destruct (decide (e' = length E2)) as [->|NEQ].
          * rewrite lookup_app_1_eq in H0. inversion H0. subst eV1. done.
          * rewrite lookup_app_1_ne in H0; [|done]. rewrite lookup_delete_Some in H. destruct H as [H H']. eapply SeenWeakClone2; try done.
        + rewrite omo_insert_w_write_op lookup_app_l; [|rewrite take_length -omo_write_op_length; lia].
          rewrite lookup_take_Some. split; [done|]. lia.
        + apply EventIdValid_update; try done. simpl. apply lookup_lt_Some in HeV0. done.
        + rewrite (map_fold_delete_L _ _ 0 ainfo1 warc2) in LeVbs2Vbw2; [|solve_lat|done].
          replace (Vbs2 ⊔ (Vbw2 ⊔ V2)) with ((Vbs2 ⊔ Vbw2) ⊔ V2) by solve_lat.
          replace (((map_fold view_join_total Vp2 sarc2 ⊔ view_join_total 0 ainfo1 (map_fold view_join_total Vp2 (delete 0 warc2))) ⊔ Vsf2) ⊔ Vwf2) with
            (((map_fold view_join_total Vp2 sarc2 ⊔ map_fold view_join_total Vp2 (delete 0 warc2)) ⊔ Vsf2) ⊔ Vwf2 ⊔ V1) in LeVbs2Vbw2 by solve_lat.
          clear -LeVbs2Vbw2 LeVw2Vm2 LeV2Vm2 LeV1V2. solve_lat.
        + solve_lat.
        + unfold SeenUpgrade. intros. destruct (decide (e0 = length E2)) as [->|NEQ].
          * rewrite lookup_app_1_eq in H. inversion H. subst eV1. done.
          * rewrite lookup_app_1_ne in H; [|done]. apply SeenUpgrade2 in H. destruct (eV1.(type)); try done.
            clear eVEV. des; [by left;set_solver +H|]. destruct (decide (e' = 0)) as [->|NEQ'].
            -- rewrite Hwarc2e0 in H. inversion H. subst ainfo0. left. set_solver +H0.
            -- right. exists e',ainfo0. rewrite lookup_delete_ne; [|done]. done.
        + unfold SeenDowngrade. intros. destruct (decide (e0 = length E2)) as [->|NEQ].
          * rewrite lookup_app_1_eq in H. inversion H. subst eV1. done.
          * rewrite lookup_app_1_ne in H; [|done]. eapply SeenDowngrade2; try done.
        + unfold ArcsSeen. intros. rewrite lookup_delete_Some in H. destruct H as [H H']. eapply LEwarc2; try done.
        + rewrite /StlistValid Forall_app Forall_cons. rewrite /StlistValid Forall_lookup in VALstlist2. split_and!.
          * rewrite Forall_lookup. intros. rewrite lookup_take_Some in H. destruct H as [H _]. eapply VALstlist2; try done.
          * intros. simpl in *. eapply HNoStrong; try done.
          * rewrite Forall_lookup. intros.
            have [x' H'] : is_Some (stlist2 !! (gen_of eidx1 + 1 + i)).
            { eapply interp_omo_length in Hgengood2 as Hlen. inversion Hlen.
              rewrite drop_length in H2. rewrite lookup_lt_is_Some. apply lookup_lt_Some in H. lia. }
            specialize (Hstlist2' _ _ _ H' H). subst x. simpl in *. eapply HNoStrong; try done. lia.
        + destruct (decide (nsf2 = 0)); [|done]. rewrite (map_fold_delete_L _ _ 0 ainfo1) in LeVsf2; [|solve_lat|done].
          have LeainfoV1 : ainfo.1.1.1.2 ⊑ V1; [|solve_lat]. clear -LeV0'V0'' LeV0''V1. solve_lat. }

    iModIntro. wp_pures. rewrite bool_decide_false; [|lia]. wp_pures. by iApply "HΦ".
Qed.

Lemma drop_weak_spec :
  drop_weak_spec' code.drop_weak ArcInv WeakArc.
Proof.
  intros N DISJ l tid γg M e V0 P1 P2. iIntros "#⊒V0 WArc" (Φ) "AU".
  iDestruct "WArc" as (??????????) "(%&%&%&%&%&%&%& #HN & #AInv & #⊒M & #⊒Ms & #⊒Mw & #e✓eV & #⊒ainfo & Hγb & e↪ainfo & Hγul & HeP2 &
    (%Hainfo2 & %eM & %eVEV & %SubainfoM & %SubainfoMw))".
  iLöb as "IH" forall (ainfo Hainfo2 SubainfoM SubainfoMw) "⊒ainfo".
  wp_lam. wp_pures. rewrite -[Z.to_nat 1]/(1%nat). wp_bind (!ʳˡˣ _)%E.

  (* Inv access 1 *)
  iInv "AInv" as "H" "Hclose".
  iDestruct "H" as (?? γs1 ???????) "(%&%&%& %sarc1 & %warc1 & %qsa1 & %qwa1 & %alive1 & %E1 & %Es1 & %Ew1 & %omo1 & %omos1 &
    %omow1 & %stlist1 & %mos1 & %mow1 & %Mono1 & >HN' & >M●1 & >Ms●1 & >Mw●1 & >Hγsa1 & >Hγwa1 & >Hγb1 & >Hγm1 & Alive1)".
  gname_agree with "HN HN'". iClear "HN'".
  iDestruct (ghost_var_agree with "Hγb Hγb1") as %<-.

  iDestruct (OmoEview_update with "M●1 ⊒M ⊒Mw") as (Mw') "(M●1 & #⊒Mw' & M⊢Mw' & %SubMwMw')".
  iDestruct (OmoEview_update with "M●1 ⊒M ⊒Ms") as (Ms') "(M●1 & #⊒Ms' & M⊢Ms' & %SubMsMs')".
  iCombine "⊒V0 ⊒ainfo" as "⊒V0'". rewrite monPred_in_view_op. set V0' := V0 ⊔ ainfo.1.1.1.2.
  iCombine "⊒M ⊒Ms ⊒Mw ⊒ainfo ⊒Mw' ⊒Ms' HeP2 AU" as "RES".
  iDestruct (view_at_intro_incl with "RES ⊒V0'") as (V0'')
    "(#⊒V0'' & %LeV0'V0'' & (#⊒M@V0'' & #⊒Ms@V0'' & #⊒Mw@V0'' & #⊒ainfo@V0'' & #⊒Mw'@V0'' & #⊒Ms'@V0'' & HeP2@V0'' & AU@V0''))".

  iDestruct "Alive1" as (Vbs1 Vbw1 ty1 uf1 stf1 esf1 ewf1 eVsf1 eVwf1 nsf1) "(%zwf1 & %Vsf1 & %Vwf1 & %Vp1 & %qsa1a & %qsa1b & %qu1 & %qd1 & %upds1 &
    %dgds1 & %lcks1 & %ulcks1 & >#AllEvents1 & >#AllStrongs1 & >#AllWeaks1 & >omos↦1 & >omow↦1 & >Hγu1 & >Hγd1 & >Hγl1 & >Hγul1 &
    >#AllLocks1 & [>#⊒upds1@Vwf1 >#⊒ulcks1@Vwf1] & >#esf1✓eVsf1 & >#ewf1✓eVwf1 & Hnsf1 & P2 & Hty1 & >#⊒stf1s@Vsf1 & >#⊒stf1w@Vwf1 & >Pures)".
  iDestruct "Pures" as %(Subuf1 & LASTesf1 & LASTewf1 & eVsf1EV & eVwf1EV & Hqsa1 & Hqwa1 & VALsarc1 & VALwarc1 & VALsarcwarc1 & SeenClone1 &
    SeenWeakClone1 & HInitWrite1 & LASTstf1 & DOMsarc1 & DOMwarc1 & EQqsa1 & Alive1 & VALeid1 & LeVbs1Vbw1 & GeVsf1 & GeVwf1 &
    SeenUpgrade1 & SeenDowngrade1 & SeenUnlock1 & LEsarc1 & LEwarc1 & VALstlist1 & LeVsf1 & EQnsf1).

  wp_apply (append_only_loc_relaxed_read with "[$Mw●1 $⊒Mw' $omow↦1 $⊒V0'']"); [solve_ndisj|].
  iIntros (ew1 genw1 vw1 Vw1 V1 eVw1 eVwn1) "(Pures & Mw●1 & _ & #MAXew1 & #ew1✓eVw1 & #ewn1✓eVwn1 & _ & #⊒V1 & _ & #⊒Mw1@V1 & omow↦1)".
  iDestruct "Pures" as %(Hgenw1 & eVw1EV & LeV0''V1 & eVwn1EV & eVwn1SYNC).
  iDestruct (big_sepL_lookup with "AllWeaks1") as (eVw1' zw1) "(ew1✓eVw1' & [%eVw1'EV %GEzw1] & Hgenw1)"; [exact Hgenw1|].
  iDestruct (OmoEinfo_agree with "ew1✓eVw1 ew1✓eVw1'") as %<-. rewrite eVw1EV /= in eVw1'EV. subst vw1.

  (* Prove that 1 ≤ zw1 *)
  iDestruct (ghost_var_agree with "Hγul Hγul1") as %<-.
  iDestruct (weak_counter_load_valid with "Mw●1 Hγwa1 [] MAXew1 ew1✓eVw1 ewf1✓eVwf1 e↪ainfo Hnsf1 Hty1") as %GEzw1'.
  { by rewrite omo_insert_r_write_op. } { by rewrite omo_insert_r_write_op. } { by rewrite eVw1EV. } { by rewrite eVwf1EV. } { done. }
  { done. } { done. } { set_solver +SubainfoMw SubMwMw'. } { rewrite omo_insert_r_write_op. iFrame "AllWeaks1". }
  have NEQzw1 : zw1 ≠ (-1)%Z by lia.

  set ainfo1 := (ainfo.1.1.1.1, ainfo.1.1.1.2 ⊔ V1, ainfo.1.1.2, ainfo.1.2, cas_only).
  set warc1' := <[e := ainfo1]> (delete e warc1).
  iDestruct (ghost_map_lookup with "Hγwa1 e↪ainfo") as %Hwarc1e.
  iMod (ghost_map_delete with "Hγwa1 e↪ainfo") as "Hγwa1".
  iMod (ghost_map_insert e ainfo1 with "Hγwa1") as "[Hγwa1 e↪ainfo1]"; [by apply lookup_delete|].

  iMod ("Hclose" with "[-AU@V0'' Hγb e↪ainfo1 M⊢Mw' M⊢Ms' Hγul HeP2@V0'']") as "_".
  { repeat iExists _. iFrame "HN M●1 Ms●1 Mw●1 Hγb1 Hγsa1 Hγwa1 Hγm1". rewrite omo_insert_r_write_op.
    iNext. repeat iExists _. apply (dom_same _ _ _ ainfo1) in Hwarc1e as EQdom. rewrite -EQdom.
    iFrame "AllEvents1 AllStrongs1 AllWeaks1 omos↦1 omow↦1 Hγu1 Hγd1 Hγl1 Hγul1 AllLocks1 Hnsf1 Hty1".
    iFrame "esf1✓eVsf1 ewf1✓eVwf1 ⊒upds1@Vwf1 ⊒ulcks1@Vwf1 ⊒stf1s@Vsf1 ⊒stf1w@Vwf1". iSplitL.
    - destruct (decide (e = 0)) as [->|NEQ]; [by rewrite Hwarc1e lookup_insert|].
      rewrite lookup_insert_ne; [|done]. rewrite lookup_delete_ne; [|done]. done.
    - iPureIntro. eapply (warc_update_1 _ _ _ ainfo1) in Hwarc1e as H; try done; [|solve_lat].
      eapply (warc_update_2 _ _ _ ainfo1) in Hwarc1e as H0; try done. clear eVEV. des. split_and!; try done.
      + rewrite H0. replace (Vbs1 ⊔ (Vbw1 ⊔ V1)) with ((Vbs1 ⊔ Vbw1) ⊔ V1) by solve_lat. clear -LeVbs1Vbw1. solve_lat.
      + rewrite H0. destruct (decide (nsf1 = 0)); [|done]. solve_lat. }

  iModIntro. wp_pures. rewrite -[Z.to_nat 1]/(1%nat). wp_bind (casʳᵉˡ(_,_,_))%E.
  iApply wp_hist_inv; [done|]. iIntros "#HInv".

  (* Inv access 2 *)
  iInv "AInv" as "H" "Hclose".
  iDestruct "H" as (?? γs2 ???????) "(%&%&%& %sarc2 & %warc2 & %qsa2 & %qwa2 & %alive2 & %E2 & %Es2 & %Ew2 & %omo2 & %omos2 &
    %omow2 & %stlist2 & %mos2 & %mow2 & %Mono2 & >HN' & >M●2 & >Ms●2 & >Mw●2 & >Hγsa2 & >Hγwa2 & >Hγb2 & >Hγm2 & Alive2)".
  gname_agree with "HN HN'". iClear "HN'".
  iDestruct (ghost_var_agree with "Hγb Hγb2") as %<-.

  iDestruct "Alive2" as (Vbs2 Vbw2 ty2 uf2 stf2 esf2 ewf2 eVsf2 eVwf2 nsf2) "(%zwf2 & %Vsf2 & %Vwf2 & %Vp2 & %qsa2a & %qsa2b & %qu2 & %qd2 & %upds2 &
    %dgds2 & %lcks2 & %ulcks2 & >#AllEvents2 & >#AllStrongs2 & >#AllWeaks2 & >omos↦2 & >omow↦2 & >Hγu2 & >Hγd2 & >Hγl2 & >Hγul2 &
    >#AllLocks2 & [>#⊒upds2@Vwf2 >#⊒ulcks2@Vwf2] & >#esf2✓eVsf2 & >#ewf2✓eVwf2 & Hnsf2 & P2 & Hty2 & >#⊒stf2s@Vsf2 & >#⊒stf2w@Vwf2 & >Pures)".
  iDestruct "Pures" as %(Subuf2 & LASTesf2 & LASTewf2 & eVsf2EV & eVwf2EV & Hqsa2 & Hqwa2 & VALsarc2 & VALwarc2 & VALsarcwarc2 & SeenClone2 &
    SeenWeakClone2 & HInitWrite2 & LASTstf2 & DOMsarc2 & DOMwarc2 & EQqsa2 & Alive2 & VALeid2 & LeVbs2Vbw2 & GeVsf2 & GeVwf2 &
    SeenUpgrade2 & SeenDowngrade2 & SeenUnlock2 & LEsarc2 & LEwarc2 & VALstlist2 & LeVsf2 & EQnsf2).
  iDestruct (OmoAuth_wf with "M●2") as %[OMO_GOOD2 _]. iDestruct (OmoAuth_omo_nonempty with "M●2") as %Nomo2.
  have NZomo2 : length omo2 ≠ 0 by destruct omo2.
  iDestruct (OmoSnapOmo_get with "Mw●2") as "#Mw◯2".
  iMod (rel_objectively_intro (⊒∅) tid with "[]") as "#⊒∅"; [by iApply objective_objectively; iApply monPred_in_bot|].

  wp_apply (append_only_loc_cas_general _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ∅ with "[$Mw●2 $⊒Mw' $omow↦2 $⊒V1]");
    try done; [solve_ndisj|..]; [set_solver +NEQzw1 Subuf2|].
  iIntros (b2 ew2 genw2 vw2 Vw2 V2 mow2' omow2' eVw2 eVwn2)
    "(Pures & #MAXew2 & #ew2✓eVw2 & #ewn2✓eVwn2 & Mw●2 & #⊒V2 & #⊒Mw2@V2 & CASE)".
  iDestruct "Pures" as %(Eqgenw2 & eVw2EV & LeV1V2).
  iDestruct "CASE" as "[(Pures & _ & omow↦2 & _) | [Pures sVw2]]".
  { (* CAS failed, try again *)
    iDestruct "Pures" as %(-> & NEQvw2 & -> & -> & eVwn2EV & eVwn2SYNC).

    set ainfo2 := (ainfo1.1.1.1.1, ainfo1.1.1.1.2 ⊔ V2, ainfo1.1.1.2, ainfo1.1.2, cas_only).
    set warc2' := <[e := ainfo2]> (delete e warc2).
    iDestruct (ghost_map_lookup with "Hγwa2 e↪ainfo1") as %Hwarc2e.
    iMod (ghost_map_delete with "Hγwa2 e↪ainfo1") as "Hγwa2".
    iMod (ghost_map_insert e ainfo2 with "Hγwa2") as "[Hγwa2 e↪ainfo2]"; [by apply lookup_delete|].

    iMod ("Hclose" with "[-Hγb e↪ainfo2 AU@V0'' Hγul HeP2@V0'']") as "_".
    { repeat iExists _. iFrame "HN M●2 Ms●2 Mw●2 Hγsa2 Hγwa2 Hγm2 Hγb2". rewrite omo_insert_r_write_op.
      iNext. repeat iExists _. eapply (dom_same _ _ _ ainfo2) in Hwarc2e as EQdom. rewrite -EQdom.
      iFrame "AllEvents2 AllStrongs2 AllWeaks2 omos↦2 omow↦2 Hγu2 Hγd2 Hγl2 Hγul2 AllLocks2 Hnsf2 Hty2".
      iFrame "esf2✓eVsf2 ewf2✓eVwf2 ⊒upds2@Vwf2 ⊒ulcks2@Vwf2 ⊒stf2s@Vsf2 ⊒stf2w@Vwf2". iSplitL.
      - destruct (decide (e = 0)) as [->|NEQ]; [by rewrite lookup_insert|].
        rewrite lookup_insert_ne; [|done]. rewrite lookup_delete_ne; [|done]. done.
      - iPureIntro. eapply (warc_update_1 _ _ _ ainfo2) in Hwarc2e as H; try done; [|solve_lat].
        eapply (warc_update_2 _ _ _ ainfo2) in Hwarc2e as H0; try done. clear eVEV. des. split_and!; try done.
        + rewrite H0. replace (Vbs2 ⊔ (Vbw2 ⊔ V2)) with ((Vbs2 ⊔ Vbw2) ⊔ V2) by solve_lat. clear -LeVbs2Vbw2. solve_lat.
        + destruct (decide (nsf2 = 0)); [|done]. rewrite H0. clear -LeVsf2. solve_lat. }

    iModIntro. wp_if. replace (ainfo.1.1.1.1/2)%Qp with (ainfo2.1.1.1.1/2)%Qp by done.
    iDestruct (view_at_elim with "⊒V0'' AU@V0''") as "AU".
    iDestruct (view_at_elim with "⊒V0'' HeP2@V0''") as "HeP2".
    iApply ("IH" with "[] [] [] Hγb e↪ainfo2 Hγul HeP2 AU []"); [done..|].
    subst ainfo2 ainfo1. simpl. replace ((ainfo.1.1.1.2 ⊔ V1) ⊔ V2) with V2; [done|]. solve_lat. }

  (* CAS success, commit [WeakDrop] *)
  iDestruct "Pures" as %(-> & -> & ->).
  iDestruct "sVw2" as (Vm2) "((%Hmow2' & %Homow2' & %eVwn2EV & %eVwn2SYNC & %LeVw2Vm2 & %NEqVw2Vm2 & %NLeV2Vw2 & %NEqV1V2 & %LeV2Vm2) &
    #⊒Mw2@Vm2 & omow↦2 & #⊒Vm2 & WCOMMIT)".

  rewrite last_lookup -omo_write_op_length in LASTewf2.
  replace (Init.Nat.pred (length omow2)) with (length omow2 - 1) in LASTewf2 by lia.
  rewrite LASTewf2 in Eqgenw2. inversion Eqgenw2. subst ew2.
  iDestruct (OmoEinfo_agree with "ewf2✓eVwf2 ew2✓eVw2") as %<-.
  rewrite eVwf2EV in eVw2EV. inversion eVw2EV. subst zwf2 Vw2.

  destruct ty2; [|by iDestruct "Hty2" as %[? _]].
  iDestruct "Hty2" as "[_ [%Hzw1 ->]]". subst zw1.
  destruct (decide (size stf2.2.1.1 = 1)) as [EQstf2|NEQstf2].
  - (* This WeakArc is the last one. Commit [WeakDrop e true] *)
    set V2' := V2 ⊔ Vm2.
    have LeV0V2' : V0 ⊑ V2' by solve_lat.
    set opId := length E2.
    set M2 : eView := {[opId]} ∪ (M ∪ stf2.1.2 ∪ stf2.2.2).
    set eVop := mkOmoEvent (WeakDrop e true) V2' M2.
    set E2' := E2 ++ [eVop].
    set nstf2 : arc_state := (stf2.1, (∅, stf2.2.1.2, stf2.2.2)).

    iDestruct (ghost_map_lookup with "Hγwa2 e↪ainfo1") as %Hwarc2e.
    apply size_1_elem_of in EQstf2 as Hstf2. destruct Hstf2 as [x Hstf2]. fold_leibniz.
    rewrite Hstf2 in DOMwarc2. apply dom_singleton_inv_L in DOMwarc2 as [x' Hwarc2].
    rewrite Hwarc2 lookup_singleton_Some in Hwarc2e. destruct Hwarc2e as [-> ->].

    (* Prove that there is no other StrongArc *)
    destruct nsf2; last first.
    { iDestruct "Hnsf2" as "(_ & _ & _ & e0↪ainfo & _)". iDestruct (ghost_map_lookup with "Hγwa2 e0↪ainfo") as %Hwarc2e0.
      rewrite Hwarc2 lookup_singleton_Some in Hwarc2e0. destruct Hwarc2e0 as [-> _].
      by iDestruct (ghost_map_elem_valid_2 with "e↪ainfo1 e0↪ainfo") as %[? _]. }
    symmetry in EQnsf2. apply size_empty_inv in EQnsf2. fold_leibniz.
    rewrite EQnsf2 dom_empty_iff_L in DOMsarc2.

    have LeVp2ainfo1 : Vp2 ⊑ ainfo1.1.1.1.2 by apply (LEwarc2 e); rewrite Hwarc2 lookup_singleton.

    iAssert (|={_,_}=> @{V2'} (OmoAuth γg γs2 (1/2)%Qp E2' (omo_append_w omo2 opId []) (stlist2 ++ [nstf2]) _ ∗
                               ((P2 ∗ l ↦ #0 ∗ (l >> 1) ↦ #0) -∗ Φ #true)))%I with "[M●2 WCOMMIT AU@V0'']" as ">[M●2 HΦ]".
    { iDestruct (view_at_mono_2 _ V2' with "AU@V0''") as "AU@V2'"; [solve_lat|].
      iCombine "M●2 WCOMMIT ⊒stf2s@Vsf2 ⊒stf2w@Vwf2 ⊒M@V0''" as "RES".
      iDestruct (view_at_objective_iff _ V2' with "RES") as "RES@V2'".
      iAssert (@{V2'} ⊒V2')%I with "[-]" as "#⊒V2'@V2'"; [done|].
      iCombine "RES@V2' AU@V2' ⊒V2'@V2'" as "RES".
      rewrite -view_at_fupd. iApply (view_at_mono with "RES"); [done|].

      iIntros "((M●2 & WCOMMIT & #⊒stf2s@Vsf2 & #⊒stf2w@Vwf2 & #⊒M@V0'') & AU & #⊒V2')".
      iDestruct (view_at_mono_2 _ V2' with "⊒M@V0''") as "⊒M@V2'"; [solve_lat|].
      have LeVsf2V2' : Vsf2 ⊑ V2' by rewrite Hwarc2 map_fold_singleton_view_join_total /= in LeVsf2; solve_lat.
      iDestruct (view_at_mono_2 _ V2' with "⊒stf2s@Vsf2") as "⊒stf2s@V2'"; [done|].
      iDestruct (view_at_mono_2 _ V2' with "⊒stf2w@Vwf2") as "⊒stf2w@V2'"; [solve_lat|].
      iDestruct (OmoEview_union_obj with "⊒M@V2' ⊒stf2s@V2'") as "⊒M'@V2'".
      iDestruct (OmoEview_union_obj with "⊒M'@V2' ⊒stf2w@V2'") as "⊒M''@V2'".

      iMod "AU" as (????) "[>M●2' [_ Commit]]".
      iDestruct (OmoAuth_agree with "M●2 M●2'") as %(<- & <- & <- & <-). iCombine "M●2 M●2'" as "M●2".
      iMod (OmoAuth_insert_last with "M●2 ⊒M''@V2' WCOMMIT []") as "(M●2 & #⊒M2@V2' & _ & _ & _ & WCOMMIT)".
      { have ? : step opId eVop stf2 nstf2; [|done]. eapply arc_step_WeakDrop_last; try done; subst eVop; [set_solver-|solve_lat]. }
      iDestruct (OmoHbToken_finish with "M●2") as "[M●2 M●2']".

      iMod ("Commit" $! true V2' γs2 _ _ M2 with "[$⊒V2' $M●2' $WCOMMIT $⊒M2@V2']") as "HΦ".
      { iPureIntro. split_and!; try done; [set_solver-|]. exists (length omo2). rewrite omo_insert_w_append_w; done. }

      iModIntro. iFrame "M●2 HΦ". }

    (* Collect all fractions *)
    rewrite DOMsarc2 map_fold_empty in Hqsa2. rewrite Hqsa2.
    rewrite Hwarc2 map_fold_singleton_frac_sum /frac_sum Qp.add_comm in Hqwa2.
    iCombine "Hγb2 Hγb" as "Hγb2". rewrite -Qp.add_assoc -Qp.div_add_distr Hqwa2 Qp.half_half.
    iMod (ghost_var_update false with "Hγb2") as "Hγb2". rewrite -{13}Qp.half_half.
    iMod (ghost_map_delete with "Hγwa2 e↪ainfo1") as "Hγwa2".
    have Hwarc2' : delete e warc2 = ∅ by rewrite Hwarc2 delete_singleton. rewrite DOMsarc2 Hwarc2'.

    (* Collect all resources *)
    iAssert (@{V2'} P2)%I with "[P2 HeP2@V0'']" as "P2@V2'".
    { destruct (decide (e = 0)) as [->|NEQe].
      - iDestruct "HeP2@V0''" as "[HP2@V0'' _]". iApply (view_at_mono with "HP2@V0''"); [solve_lat|]. done.
      - destruct (warc2 !! 0) eqn:Hwarc2e0.
        + rewrite Hwarc2 lookup_singleton_Some in Hwarc2e0. des; done.
        + iApply (view_at_mono with "P2"); [|done]. solve_lat. }

    rewrite DOMsarc2 Hwarc2 map_fold_empty map_fold_singleton_view_join_total /view_join_total in LeVbs2Vbw2.
    rewrite Hwarc2 map_fold_singleton_view_join_total /= /view_join_total in LeVsf2.
    have LeVbs2Vbw2V2 : Vbs2 ⊔ Vbw2 ⊑ V2' by solve_lat.
    iDestruct (view_at_mono_2 _ V2' with "omos↦2") as "omos↦2"; [solve_lat|].
    iDestruct (view_at_mono_2 _ V2' with "omow↦2") as "omow↦2"; [solve_lat|].

    iAssert (|={_,_}=> @{V2'} (OmoAuth γes γss (1 / 2) Es2 omos2 mos2 _ ∗
        OmoAuth γew γsw (1 / 2) (Ew2 ++ [eVwn2]) omow2' mow2' _ ∗
        l ↦ #0 ∗ (l >> 1) ↦ #0))%I with "[Ms●2 Mw●2 omos↦2 omow↦2]" as ">(Ms●2 & Mw●2 & ls↦ & lw↦)".
    { iCombine "Ms●2 Mw●2 esf2✓eVsf2 ewn2✓eVwn2 HInv" as "RES".
      iDestruct (view_at_objective_iff _ V2' with "RES") as "RES". iCombine "RES omos↦2 omow↦2" as "RES".
      rewrite -view_at_fupd. iApply (view_at_mono with "RES"); [done|].

      iIntros "((Ms●2 & Mw●2 & #esf2✓eVsf2 & #ewn2✓eVwn2 & #HInv) & omos↦2 & omow↦2)".
      iMod (append_only_loc_to_na with "HInv Ms●2 omos↦2")
        as (vs es eVs) "(ls↦ & [Ms●2 _] & #es✓eVs & [%Hes %eVsEV])"; [solve_ndisj|].
      iMod (append_only_loc_to_na with "HInv Mw●2 omow↦2")
        as (vw ew eVw) "(lw↦ & [Mw●2 _] & #ew✓eVw & [%Hew %eVwEV])"; [solve_ndisj|].

      rewrite LASTesf2 in Hes. inversion Hes. subst es.
      iDestruct (OmoEinfo_agree with "esf2✓eVsf2 es✓eVs") as %<-.
      rewrite eVsf2EV in eVsEV. subst vs.

      rewrite Homow2' omo_append_w_write_op last_snoc in Hew. inversion Hew. subst ew.
      iDestruct (OmoEinfo_agree with "ewn2✓eVwn2 ew✓eVw") as %<-.
      rewrite eVwn2EV in eVwEV. subst vw. simpl.
      rewrite Hstf2 size_singleton. replace (Z.of_nat 1 - 1)%Z with 0%Z by lia.

      iModIntro. iFrame "Ms●2 Mw●2 ls↦ lw↦". }

    rewrite !view_at_objective_iff.
    iMod ("Hclose" with "[-HΦ P2@V2' ls↦ lw↦]") as "_"; [repeat iExists _; iFrame "HN M●2 Ms●2 Mw●2 Hγsa2 Hγwa2 Hγb2 Hγm2"|].

    iModIntro. wp_pures. rewrite bool_decide_true; [|lia].
    wp_apply (wp_acq_fence with "⊒Vm2"); [solve_ndisj|]. iClear "⊒Vm2". iIntros "#⊒Vm2". wp_pures.

    iCombine "⊒V2 ⊒Vm2" as "⊒V2'". rewrite monPred_in_view_op. iCombine "HΦ P2@V2' ls↦ lw↦" as "RES".
    iDestruct (view_at_elim with "⊒V2' RES") as "(HΦ & P2 & ls↦ & lw↦)". iApply ("HΦ" with "[$P2 $ls↦ $lw↦]").
  - (* This WeakArc is not the last one. Commit [WeakDrop e false] *)
    (* Insert [WeakDrop] event right after the latest observation in eView *)
    iDestruct (OmoEview_latest_elem with "⊒M") as (e1) "[MAXe1 %e1IN]".
    iDestruct (OmoAuth_OmoEview with "M●2 ⊒M") as %VALM.
    apply VALM in e1IN as He1.
    eapply lookup_omo_surjective in He1 as Heidx1; [|done]. destruct Heidx1 as [eidx1 Heidx1].
    eapply omo_stlist_length in OMO_GOOD2 as EQlenST2.
    have [st1 Hst1] : is_Some (stlist2 !! (gen_of eidx1)).
    { rewrite lookup_lt_is_Some -EQlenST2. apply lookup_omo_lt_Some in Heidx1. done. }

    iDestruct (OmoAuth_OmoEinfo with "M●2 e✓eV") as %HeV.
    iDestruct (OmoAuth_OmoEinfo' with "M●2 e✓eV") as %[eidx Heidx].
    iDestruct (ghost_map_lookup with "Hγwa2 e↪ainfo1") as %Hwarc2e.
    have [st Hst] : is_Some (stlist2 !! (gen_of eidx)).
    { rewrite lookup_lt_is_Some -EQlenST2. apply lookup_omo_lt_Some in Heidx. done. }
    have eINdom : e ∈ dom warc2 by apply elem_of_dom_2 in Hwarc2e.

    iDestruct (big_sepS_elem_of _ _ e with "MAXe1") as "e≤e1"; [done|].
    iDestruct (OmoLe_Le with "M●2 e≤e1") as %LEgengen1; [done|done|].

    have LeV0V2 : V0 ⊑ V2 by solve_lat.
    set opId := length E2.
    set M2 : eView := {[opId]} ∪ M.
    set eVop := mkOmoEvent (WeakDrop e false) V2 M2.
    set E2' := E2 ++ [eVop].
    set nst1 : arc_state := (st1.1, (st1.2.1.1 ∖ {[e]}, st1.2.1.2 ⊔ eVop.(sync), st1.2.2 ∪ eVop.(eview))).

    specialize (weak_arc_persist _ _ _ _ _ _ (dom sarc2) (dom warc2) OMO_GOOD2 Heidx HeV eVEV eINdom VALsarcwarc2) as Hstlist2.
    iDestruct (OmoUB_into_gen with "M●2 MAXe1") as %MAXe1; [done|].
    iAssert (∀ i sti, ⌜ stlist2 !! i = Some sti → gen_of eidx1 ≤ i → {[e]} ⊂ sti.2.1.1 ⌝)%I with "[-]" as %SSub.
    { iIntros (i sti) "%Hsti %LEi".
      apply Hstlist2 in Hsti as eINsti; [|lia].
      have Sub : {[e]} ⊆ sti.2.1.1 by clear -eINsti; set_solver.
      destruct (decide (sti.2.1.1 = {[e]})) as [EQ|NEQ]; [|iPureIntro;set_solver +Sub NEQ].

      specialize (weak_state_no_decrease _ _ _ _ _ _ _ _ OMO_GOOD2 Hsti EQ VALsarcwarc2 HInitWrite2 eINdom) as Hstweak2.
      rewrite last_lookup -EQlenST2 in LASTstf2.
      replace (Init.Nat.pred (length omo2)) with (length omo2 - 1) in LASTstf2 by lia.
      have LECOND : i ≤ length omo2 - 1.
      { apply lookup_lt_Some in Hsti. rewrite -EQlenST2 in Hsti. lia. }
      specialize (Hstweak2 _ _ LECOND LASTstf2). clear eVEV. des.
      - apply (f_equal size) in Hstweak2. rewrite EQ size_singleton in Hstweak2. lia.
      - unfold SeenWeakClone in SeenWeakClone2. eapply SeenWeakClone2 in Hwarc2e; [|done|done].
        have ekIN : ek ∈ M by set_solver +Hwarc2e SubainfoM.
        apply MAXe1 in ekIN as (eidxk & Heidxk & LEgen). rewrite -lookup_omo_wr_event in Hstweak4.
        eapply lookup_omo_inj in Heidxk; [|done|exact Hstweak4]. subst eidxk. simpl in LEgen. lia.
      - have [stk Hstk] : is_Some (stlist2 !! k) by rewrite lookup_lt_is_Some -EQlenST2; lia.
        iAssert (⌜ stk'.1.1.1 = ∅ ⌝)%I with "[-]" as %EQstk'.
        { destruct (decide (e = 0)) as [->|NEQe].
          - iDestruct "HeP2@V0''" as "[_ %eVWeakInit]". iPureIntro.
            specialize (weak_init_no_strong _ _ _ _ OMO_GOOD2 HInitWrite2 HeV eVWeakInit) as NSTRONG.
            eapply NSTRONG. done.
          - iPureIntro. rewrite /StlistValid Forall_lookup in VALstlist2. eapply VALstlist2; try done.
            rewrite -Hstweak3 EQ. set_solver +NEQe. }
        exfalso. replace k with ((k - 1) + 1) in Hstweak4,Hstk by lia.
        eapply omo_write_op_step in OMO_GOOD2 as STEP; try done.
        inversion STEP; subst; simpl in *; rewrite Hstweak6 in EVENT; try done. }
    apply SSub in Hst1 as SSubst1; [|done].

    have STEPop : step opId eVop st1 nst1 by eapply arc_step_WeakDrop; try done; set_solver-.
    have NoWeakClone : ∀ e' eidx' eV',
      lookup_omo omo2 eidx' = Some e' → E2 !! e' = Some eV' → gen_of eidx1 < gen_of eidx' → eV'.(type) ≠ WeakClone e.
    { intros. unfold not. intros. unfold SeenWeakClone in SeenWeakClone2. eapply SeenWeakClone2 in Hwarc2e; [|done..].
      have e'IN : e' ∈ M by set_solver +Hwarc2e SubainfoM. apply MAXe1 in e'IN as (eidx'' & Heidx'' & LE).
      eapply lookup_omo_inj in H; [|done|exact Heidx'']. subst eidx''. lia. }
    specialize (weak_arc_delete_gen_good _ _ _ _ _ _ _ _ _ OMO_GOOD2 Hst1 STEPop HInitWrite2 SSub NoWeakClone Alive2)
      as (stlist2' & Hgengood2 & Hstlist2').

    iDestruct (view_at_elim with "⊒V0'' AU@V0''") as "AU".
    iMod "AU" as (????) "[>M●2' [_ Commit]]".
    iDestruct (OmoAuth_agree with "M●2 M●2'") as %(<- & <- & <- & <-). iCombine "M●2 M●2'" as "M●2".
    iDestruct (OmoSnapStates_get with "M●2") as "#ST◯2".

    iDestruct (view_at_mono_2 _ V2 with "⊒M@V0''") as "⊒M@V2"; [solve_lat|].
    iMod (OmoAuth_insert _ _ _ _ _ _ _ _ _ _ (gen_of eidx1) with "M●2 ⊒M@V2 WCOMMIT []") as (γs2')
      "(M●2 & #⊒M2@V2 & #opId↦ewn2 & #opId✓eVop & WCOMMIT)"; [iPureIntro; split_and!; try done; [by subst eVop|set_solver-]|].
    iMod (OmoHb_new_2 _ _ _ _ _ _ _ _ (length Ew2) ({[length Ew2]} ∪ Mw') with "M●2 [] opId✓eVop") as "[M●2 #opId⊒ewn2]".
    { set_solver-. } { iFrame "⊒Mw2@V2". }

    iMod (SeenPrevStrong_after_weak_event with "M●2 Ms●2 Mw●2 omos↦2 Hγm2 [] M⊢Ms' AllEvents2 AllStrongs2 opId✓eVop opId↦ewn2")
      as "(#SeenPrevStrongopId & [M●2 M●2'] & Ms●2 & Mw●2 & omos↦2 & Hγm2 & M⊢Ms')"; [exact e1IN|done|done|..].
    { iDestruct (view_at_mono_2 _ V2 with "⊒Ms'@V0''") as "⊒Ms'@V2"; [solve_lat|]. iFrame "⊒Ms'@V2". }

    iDestruct (AllStrongs_update with "M●2 Ms●2 Mw●2 omos↦2 AllStrongs2 opId↦ewn2 ST◯2") as "#AllStrongs2'";
      [done|..|done|by apply lookup_omo_lt_Some in Heidx1|]. { intros. eapply Hstlist2' in H; [|done]. rewrite H. done. }

    iMod (ghost_map_delete with "Hγwa2 e↪ainfo1") as "Hγwa2".
    iCombine "Hγb2 Hγb" as "Hγb2". rewrite -Qp.add_assoc -Qp.div_add_distr.
    iDestruct (ghost_var_agree with "Hγul Hγul2") as %<-. iCombine "Hγul2 Hγul" as "Hγul2".

    iMod ("Commit" $! false V2 γs2' _ _ M2 with "[$⊒V2 $M●2' $WCOMMIT $⊒M2@V2]") as "HΦ".
    { iPureIntro. split_and!; try done; [set_solver-|]. by eexists. }

    iDestruct (OmoAuth_wf with "M●2") as %[OMO_GOOD2' _].
    eapply weak_arc_delete_new_state in OMO_GOOD2 as Hnstf2'; [|exact OMO_GOOD2'|done..].
    destruct Hnstf2' as (nstf2 & Hnstf2 & Hnstf2').
    set upds2' := upds2 ∪ ainfo1.1.1.2.
    iMod (ghost_var_update upds2' with "Hγu2") as "Hγu2".
    iAssert (⌜ if decide (e = 0) then eV.(type) = WeakInit else True ⌝)%I with "[-]" as %HWeakInit.
    { destruct (decide (e = 0)); [|done]. iDestruct "HeP2@V0''" as "[_ %eVWINIT]". done. }

    iMod ("Hclose" with "[-HΦ]") as "_".
    { repeat iExists _. iFrame "HN M●2 Ms●2 Mw●2 Hγsa2 Hγwa2 Hγb2 Hγm2".
      iNext. do 4 iExists _. iExists nstf2. repeat iExists _. iCombine "⊒upds2@Vwf2 ⊒ulcks2@Vwf2 ⊒stf2w@Vwf2" as "RES".
      iDestruct (view_at_mono_2 _ Vm2 with "RES") as "(⊒upds2@Vm2 & ⊒ulcks2@Vm2 & ⊒stf2w@Vm2)"; [solve_lat|].
      iFrame "AllStrongs2' omos↦2 omow↦2 Hγu2 Hγd2 Hγl2 Hγul2 Hnsf2 esf2✓eVsf2 ewn2✓eVwn2 ⊒ulcks2@Vm2".
      iDestruct (view_at_mono_2 _ Vm2 with "⊒M2@V2") as "⊒M2@Vm2"; [done|].
      iDestruct (OmoEview_union_obj with "⊒stf2w@Vm2 ⊒M2@Vm2") as "⊒nstf2w@Vm2".
      iDestruct (OmoEview_union_obj with "⊒upds2@Vm2 ⊒M2@Vm2") as "⊒upds2'@Vm2".
      iDestruct (OmoEview_nonempty_obj with "⊒upds2@Vm2") as %Nupds2.
      iDestruct (OmoEview_mono_obj _ _ upds2' with "⊒upds2'@Vm2") as "⊒upds2''@Vm2"; [set_solver +SubainfoM|set_solver +Nupds2|].
      rewrite Hnstf2' /=. iFrame "⊒upds2''@Vm2 ⊒stf2s@Vsf2 ⊒nstf2w@Vm2".
      iSplitR; last iSplitR; last iSplitR; last iSplitL; last iSplit.
      - iApply big_sepL_snoc. iFrame "AllEvents2 SeenPrevStrongopId".
      - rewrite Homow2' omo_append_w_write_op. iApply big_sepL_snoc. iSplit.
        + iApply big_sepL_forall. iIntros "%i %ew %Hew".
          iDestruct (big_sepL_lookup with "AllWeaks2") as (eVw zw) "(ew✓eVw & [%eVwEV %GEzw] & Hi)"; [exact Hew|].
          rewrite dom_delete_L. iExists eVw,zw. iFrame "ew✓eVw". iSplit; [done|]. destruct i; [done|].
          iDestruct "Hi" as (????) "(Mw◯ & ew'✓eVw' & Pures & CASE)". repeat iExists _. iFrame "Mw◯ ew'✓eVw' Pures".
          iDestruct "CASE" as "[CASE|[CASE|[CASE|CASE]]]"; [|by iRight;iLeft|by iRight;iRight;iLeft|by iRight;iRight;iRight].
          iLeft. iDestruct "CASE" as (??) "(e0↦ew & e0✓eV0 & e0⊒ew & %)". repeat iExists _. iFrame "e0↦ew e0✓eV0 e0⊒ew".
          iPureIntro. clear eVEV. des; split_and!; try done; [by left|].
          right. exists e'. split; [done|]. intros. apply H2. des. split; [done|]. set_solver +H4.
        + rewrite dom_delete_L. iExists eVwn2,(size stf2.2.1.1 - 1)%Z. iFrame "ewn2✓eVwn2". iSplit.
          { iPureIntro. rewrite eVwn2EV. split; [|lia]. simpl. done. }
          rewrite -omo_write_op_length. destruct (length omow2) eqn:Hlen; [done|].
          rewrite -Hlen. rewrite -Hlen in LASTewf2. clear Hlen n.
          iExists omow2,ewf2,eVwf2,(size stf2.2.1.1). iFrame "Mw◯2 ewf2✓eVwf2". iSplit; [by rewrite eVwf2EV|].
          iRight. iLeft. iPureIntro. split; try done.
      - rewrite Homow2' omo_append_w_write_op. iApply big_sepL_snoc. iFrame "AllLocks2".
        iExists eVwn2,(size stf2.2.1.1 - 1)%Z. iFrame "ewn2✓eVwn2". iPureIntro.
        rewrite eVwn2EV. split; [done|]. intros. lia.
      - destruct (decide (e = 0)) as [->|NEQe].
        + rewrite lookup_delete. iDestruct "HeP2@V0''" as "[P2@V0'' _]".
          iApply (view_at_mono with "P2@V0''"); [|done]. solve_lat.
        + rewrite lookup_delete_ne; [|done]. destruct (warc2 !! 0); [done|].
          iApply (view_at_mono with "P2"); [|done]. solve_lat.
      - iSplit; [|done]. iLeft. iExists opId. iFrame "opId⊒ewn2".
      - rewrite Homow2' omo_append_w_write_op last_snoc size_difference; last first.
        { apply elem_of_dom_2 in Hwarc2e. rewrite DOMwarc2 in Hwarc2e. set_solver +Hwarc2e. }
        rewrite size_singleton eVwn2EV Hnstf2 Hnstf2' dom_delete_L DOMwarc2 /ArcAlive Forall_app Forall_singleton /=.
        replace (Z.of_nat (size stf2.2.1.1) - 1)%Z with (Z.of_nat (size stf2.2.1.1 - 1)) by lia.
        iPureIntro. split_and!; try done.
        + rewrite Qp.add_comm map_fold_init_frac_op.
          rewrite (map_fold_delete_L _ _ e ainfo1) in Hqwa2; [|by apply frac_sum_wf|done].
          rewrite {1}/frac_sum /= in Hqwa2. done.
        + unfold ArcsValid. intros. apply VALsarc2 in H. rewrite app_length /=. lia.
        + unfold ArcsValid. rewrite -DOMwarc2. intros. have e0IN : e0 ∈ dom warc2 by set_solver +H.
          apply VALwarc2 in e0IN. rewrite app_length /=. lia.
        + unfold ArcsValid2. rewrite -DOMwarc2. intros. destruct (decide (e0 = length E2)) as [->|NEQ].
          * rewrite lookup_app_1_eq in H. inversion H. subst eV0. simpl. set_solver-.
          * rewrite lookup_app_1_ne in H; [|done]. apply VALsarcwarc2 in H.
            destruct (eV0.(type)); try done. set_solver +H.
        + unfold SeenClone. intros. destruct (decide (e' = length E2)) as [->|NEQ].
          * rewrite lookup_app_1_eq in H0. inversion H0. subst eV0. done.
          * rewrite lookup_app_1_ne in H0; [|done]. eapply SeenClone2; try done.
        + unfold SeenWeakClone. intros. destruct (decide (e' = length E2)) as [->|NEQ].
          * rewrite lookup_app_1_eq in H0. inversion H0. subst eV0. done.
          * rewrite lookup_app_1_ne in H0; [|done]. rewrite lookup_delete_Some in H.
            destruct H as [H H']. eapply SeenWeakClone2; try done.
        + rewrite omo_insert_w_write_op lookup_app_l; [|rewrite take_length -omo_write_op_length; lia].
          rewrite lookup_take_Some. split; [done|]. lia.
        + apply EventIdValid_update; try done. simpl. apply lookup_lt_Some in HeV. done.
        + rewrite (map_fold_delete_L _ _ e ainfo1 warc2) in LeVbs2Vbw2; [|solve_lat|done].
          replace (Vbs2 ⊔ (Vbw2 ⊔ V2)) with ((Vbs2 ⊔ Vbw2) ⊔ V2) by solve_lat.
          replace (((map_fold view_join_total Vp2 sarc2 ⊔ view_join_total e ainfo1 (map_fold view_join_total Vp2 (delete e warc2))) ⊔ Vsf2) ⊔ Vwf2) with
            (((map_fold view_join_total Vp2 sarc2 ⊔ map_fold view_join_total Vp2 (delete e warc2)) ⊔ Vsf2) ⊔ Vwf2 ⊔ V1) in LeVbs2Vbw2 by solve_lat.
          clear -LeVbs2Vbw2 LeVw2Vm2 LeV2Vm2 LeV1V2. solve_lat.
        + solve_lat.
        + unfold SeenUpgrade. intros. destruct (decide (e0 = length E2)) as [->|NEQ].
          * rewrite lookup_app_1_eq in H. inversion H. subst eV0. done.
          * rewrite lookup_app_1_ne in H; [|done]. apply SeenUpgrade2 in H. destruct (eV0.(type)); try done.
            clear eVEV. des; [by left;set_solver +H|]. destruct (decide (e' = e)) as [->|NEQ'].
            -- rewrite Hwarc2e in H. inversion H. subst ainfo0. left. set_solver +H0.
            -- right. exists e',ainfo0. rewrite lookup_delete_ne; [|done]. done.
        + unfold SeenDowngrade. intros. destruct (decide (e0 = length E2)) as [->|NEQ].
          * rewrite lookup_app_1_eq in H. inversion H. subst eV0. done.
          * rewrite lookup_app_1_ne in H; [|done]. eapply SeenDowngrade2; try done.
        + unfold ArcsSeen. intros. rewrite lookup_delete_Some in H. destruct H as [H H']. eapply LEwarc2; try done.
        + rewrite /StlistValid Forall_app Forall_cons. rewrite /StlistValid Forall_lookup in VALstlist2. split_and!.
          * rewrite Forall_lookup. intros. rewrite lookup_take_Some in H.
            destruct H as [H _]. eapply VALstlist2; try done.
          * intros. simpl in *. destruct (decide (e = 0)) as [->|NEQ].
            -- eapply weak_init_no_strong; [exact OMO_GOOD2|..]; try done.
            -- have H' : 0 ∉ st1.2.1.1 by set_solver +H NEQ. eapply VALstlist2; try done.
          * rewrite Forall_lookup. intros.
            have [x' H'] : is_Some (stlist2 !! (gen_of eidx1 + 1 + i)).
            { eapply interp_omo_length in Hgengood2 as Hlen. inversion Hlen.
              rewrite drop_length in H2. rewrite lookup_lt_is_Some. apply lookup_lt_Some in H. lia. }
            specialize (Hstlist2' _ _ _ H' H). subst x. simpl in *. destruct (decide (e = 0)) as [->|NEQ].
            -- eapply weak_init_no_strong; [exact OMO_GOOD2|..]; try done.
            -- apply VALstlist2 in H'; [done|]. set_solver +H0 NEQ.
        + destruct (decide (nsf2 = 0)); [|done]. rewrite (map_fold_delete_L _ _ e ainfo1) in LeVsf2; [|solve_lat|done].
          have LeainfoV1 : ainfo.1.1.1.2 ⊑ V1; [|solve_lat]. clear -LeV0'V0'' LeV0''V1. solve_lat. }

    iModIntro. wp_pures. rewrite bool_decide_false; [|lia]. wp_pures. by iApply "HΦ".
Qed.

Lemma downgrade_spec :
  downgrade_spec' code.downgrade ArcInv StrongArc WeakArc.
Proof.
  intros N DISJ l tid γg M q e V0 P1 P2. iIntros "#⊒V0 SArc" (Φ) "AU".
  iDestruct "SArc" as (??????????) "(%&%&%&%&%&%& #HN & #AInv & #⊒M & #⊒Ms & #⊒Mw & #e✓eV & #⊒ainfo & Hγb & e↪ainfo &
    (-> & %Hainfo2 & %eM & %eVEV & %SubainfoM & %SubainfoMw))".
  iLöb as "IH" forall (ainfo Hainfo2 SubainfoM SubainfoMw) "⊒ainfo".
  wp_lam. wp_pures. rewrite -[Z.to_nat 1]/(1%nat). wp_bind (!ʳˡˣ _)%E.

  (* Inv access 1 *)
  iInv "AInv" as "H" "Hclose".
  iDestruct "H" as (?? γs1 ???????) "(%&%&%& %sarc1 & %warc1 & %qsa1 & %qwa1 & %alive1 & %E1 & %Es1 & %Ew1 & %omo1 & %omos1 &
    %omow1 & %stlist1 & %mos1 & %mow1 & %Mono1 & >HN' & >M●1 & >Ms●1 & >Mw●1 & >Hγsa1 & >Hγwa1 & >Hγb1 & >Hγm1 & Alive1)".
  gname_agree with "HN HN'". iClear "HN'".
  iDestruct (ghost_var_agree with "Hγb Hγb1") as %<-.

  iDestruct (OmoEview_update with "M●1 ⊒M ⊒Mw") as (Mw') "(M●1 & #⊒Mw' & M⊢Mw' & %SubMwMw')".
  iDestruct (OmoEview_update with "M●1 ⊒M ⊒Ms") as (Ms') "(M●1 & #⊒Ms' & M⊢Ms' & %SubMsMs')".
  iCombine "⊒V0 ⊒ainfo" as "⊒V0'". rewrite monPred_in_view_op. set V0' := V0 ⊔ ainfo.1.1.1.2.
  iCombine "⊒M ⊒Ms ⊒Mw ⊒ainfo ⊒Mw' ⊒Ms'" as "RES".
  iDestruct (view_at_intro_incl with "RES ⊒V0'") as (V0'')
    "(#⊒V0'' & %LeV0'V0'' & (#⊒M@V0'' & #⊒Ms@V0'' & #⊒Mw@V0'' & #⊒ainfo@V0'' & #⊒Mw'@V0'' & #⊒Ms'@V0''))". iClear "RES".

  iDestruct "Alive1" as (Vbs1 Vbw1 ty1 uf1 stf1 esf1 ewf1 eVsf1 eVwf1 nsf1) "(%zwf1 & %Vsf1 & %Vwf1 & %Vp1 & %qsa1a & %qsa1b & %qu1 & %qd1 & %upds1 &
    %dgds1 & %lcks1 & %ulcks1 & >#AllEvents1 & >#AllStrongs1 & >#AllWeaks1 & >omos↦1 & >omow↦1 & >Hγu1 & >Hγd1 & >Hγl1 & >Hγul1 &
    >#AllLocks1 & [>#⊒upds1@Vwf1 >#⊒ulcks1@Vwf1] & >#esf1✓eVsf1 & >#ewf1✓eVwf1 & Hnsf1 & P2 & Hty1 & >#⊒stf1s@Vsf1 & >#⊒stf1w@Vwf1 & >Pures)".
  iDestruct "Pures" as %(Subuf1 & LASTesf1 & LASTewf1 & eVsf1EV & eVwf1EV & Hqsa1 & Hqwa1 & VALsarc1 & VALwarc1 & VALsarcwarc1 & SeenClone1 &
    SeenWeakClone1 & HInitWrite1 & LASTstf1 & DOMsarc1 & DOMwarc1 & EQqsa1 & Alive1 & VALeid1 & LeVbs1Vbw1 & GeVsf1 & GeVwf1 &
    SeenUpgrade1 & SeenDowngrade1 & SeenUnlock1 & LEsarc1 & LEwarc1 & VALstlist1 & LeVsf1 & EQnsf1).

  wp_apply (append_only_loc_relaxed_read with "[$Mw●1 $⊒Mw' $omow↦1 $⊒V0'']"); [solve_ndisj|].
  iIntros (ew1 genw1 vw1 Vw1 V1 eVw1 eVwn1) "(Pures & Mw●1 & _ & #MAXew1 & #ew1✓eVw1 & #ewn1✓eVwn1 & _ & #⊒V1 & _ & #⊒Mw1@V1 & omow↦1)".
  iDestruct "Pures" as %(Hgenw1 & eVw1EV & LeV0''V1 & eVwn1EV & eVwn1SYNC).
  iDestruct (big_sepL_lookup with "AllWeaks1") as (eVw1' zw1) "(ew1✓eVw1' & [%eVw1'EV %GEzw1] & Hgenw1)"; [exact Hgenw1|].
  iDestruct (OmoEinfo_agree with "ew1✓eVw1 ew1✓eVw1'") as %<-. rewrite eVw1EV /= in eVw1'EV. subst vw1.

  set ainfo1 := (ainfo.1.1.1.1, ainfo.1.1.1.2 ⊔ V1, ainfo.1.1.2, ainfo.1.2, cas_only).
  set sarc1' := <[e := ainfo1]> (delete e sarc1).
  iDestruct (ghost_map_lookup with "Hγsa1 e↪ainfo") as %Hsarc1e.
  iMod (ghost_map_delete with "Hγsa1 e↪ainfo") as "Hγsa1".
  iMod (ghost_map_insert e ainfo1 with "Hγsa1") as "[Hγsa1 e↪ainfo1]"; [by apply lookup_delete|].

  iMod ("Hclose" with "[-AU Hγb e↪ainfo1 M⊢Mw' M⊢Ms']") as "_".
  { repeat iExists _. iFrame "HN M●1 Ms●1 Mw●1 Hγsa1 Hγwa1 Hγm1 Hγb1". rewrite omo_insert_r_write_op.
    iNext. repeat iExists _. iFrame "AllEvents1 AllStrongs1 AllWeaks1 omos↦1 omow↦1 Hγu1 Hγd1 Hγl1
      Hγul1 esf1✓eVsf1 ewf1✓eVwf1 Hnsf1 P2 ⊒upds1@Vwf1 ⊒ulcks1@Vwf1 ⊒stf1s@Vsf1 ⊒stf1w@Vwf1". iSplitR; last iSplitL.
    - iApply big_sepL_forall. iIntros "%i %ew %Hew".
      iDestruct (big_sepL_lookup with "AllLocks1") as (eVw zw) "[ew✓eVw [%eVwEV %COND]]"; [exact Hew|].
      iExists eVw,zw. iFrame "ew✓eVw". iPureIntro. split; [done|]. intros. apply COND in H. clear eVEV. des; [by left|].
      right. destruct (decide (e0 = e)) as [->|NEQ].
      + rewrite Hsarc1e in H. inversion H. subst ainfo0. exists e,ainfo1. rewrite lookup_insert. split; [done|]. set_solver +H0.
      + exists e0,ainfo0. rewrite lookup_insert_ne; [|done]. rewrite lookup_delete_ne; [|done]. done.
    - iApply (append_only_type_condition_update with "Hty1"); try done.
    - iPureIntro. eapply (sarc_update_1 _ _ _ ainfo1) in Hsarc1e as H; try done; [|solve_lat]. clear eVEV.
      eapply (sarc_update_2 _ _ _ ainfo1 _ _ _ _ lcks1 _ ulcks1) in Hsarc1e as H0; try done. des. split_and!; try done.
      rewrite H0. replace (Vbs1 ⊔ (Vbw1 ⊔ V1)) with ((Vbs1 ⊔ Vbw1) ⊔ V1) by solve_lat. clear -LeVbs1Vbw1. solve_lat. }

  iModIntro. wp_pures. destruct (decide (zw1 = (-1)%Z)) as [->|NEQzw1].
  { rewrite bool_decide_true; [|done]. iApply ("IH" $! ainfo1 with "[] [] [] Hγb e↪ainfo1 AU []"); try done.
    replace ainfo1.1.1.1.2 with V1 by solve_lat. iFrame "⊒V1". }
  rewrite bool_decide_false; [|done]. wp_pures. rewrite -[Z.to_nat 1]/(1%nat). wp_bind (casᵃᶜ(_,_,_))%E.

  (* Inv access 2 *)
  iInv "AInv" as "H" "Hclose".
  iDestruct "H" as (?? γs2 ???????) "(%&%&%& %sarc2 & %warc2 & %qsa2 & %qwa2 & %alive2 & %E2 & %Es2 & %Ew2 & %omo2 & %omos2 &
    %omow2 & %stlist2 & %mos2 & %mow2 & %Mono2 & >HN' & >M●2 & >Ms●2 & >Mw●2 & >Hγsa2 & >Hγwa2 & >Hγb2 & >Hγm2 & Alive2)".
  gname_agree with "HN HN'". iClear "HN'".
  iDestruct (ghost_var_agree with "Hγb Hγb2") as %<-.
  iDestruct (OmoAuth_omo_nonempty with "M●2") as %Nomo2.
  have NZomo2 : length omo2 ≠ 0 by destruct omo2.
  iDestruct (OmoAuth_omo_nonempty with "Mw●2") as %Nomow2.
  iDestruct (OmoSnapOmo_get with "Mw●2") as "#Mw◯2".

  iDestruct "Alive2" as (Vbs2 Vbw2 ty2 uf2 stf2 esf2 ewf2 eVsf2 eVwf2 nsf2) "(%zwf2 & %Vsf2 & %Vwf2 & %Vp2 & %qsa2a & %qsa2b & %qu2 & %qd2 & %upds2 &
    %dgds2 & %lcks2 & %ulcks2 & >#AllEvents2 & >#AllStrongs2 & >#AllWeaks2 & >omos↦2 & >omow↦2 & >Hγu2 & >Hγd2 & >Hγl2 & >Hγul2 &
    >#AllLocks2 & [>#⊒upds2@Vwf2 >#⊒ulcks2@Vwf2] & >#esf2✓eVsf2 & >#ewf2✓eVwf2 & Hnsf2 & P2 & Hty2 & >#⊒stf2s@Vsf2 & >#⊒stf2w@Vwf2 & >Pures)".
  iDestruct "Pures" as %(Subuf2 & LASTesf2 & LASTewf2 & eVsf2EV & eVwf2EV & Hqsa2 & Hqwa2 & VALsarc2 & VALwarc2 & VALsarcwarc2 & SeenClone2 &
    SeenWeakClone2 & HInitWrite2 & LASTstf2 & DOMsarc2 & DOMwarc2 & EQqsa2 & Alive2 & VALeid2 & LeVbs2Vbw2 & GeVsf2 & GeVwf2 &
    SeenUpgrade2 & SeenDowngrade2 & SeenUnlock2 & LEsarc2 & LEwarc2 & VALstlist2 & LeVsf2 & EQnsf2).
  iMod (rel_objectively_intro (⊒∅) tid with "[]") as "#⊒∅"; [by iApply objective_objectively; iApply monPred_in_bot|].

  wp_apply (append_only_loc_cas_general with "[$Mw●2 $⊒Mw' $omow↦2 $⊒V1]"); try done; [solve_ndisj|..]; [set_solver +NEQzw1 Subuf2|].
  iIntros (b2 ew2 genw2 vw2 Vw2 V2 mow2' omow2' eVw2 eVwn2)
    "(Pures & #MAXew2 & #ew2✓eVw2 & #ewn2✓eVwn2 & Mw●2 & #⊒V2 & #⊒Mw2@V2 & CASE)".
  iDestruct "Pures" as %(Eqgenw2 & eVw2EV & LeV1V2).
  iDestruct "CASE" as "[(Pures & _ & omow↦2 & _) | [Pures sVw2]]".
  { (* CAS failed, try again *)
    iDestruct "Pures" as %(-> & NEQvw2 & -> & -> & eVwn2EV & eVwn2SYNC).

    set ainfo2 := (ainfo1.1.1.1.1, ainfo1.1.1.1.2 ⊔ V2, ainfo1.1.1.2, ainfo1.1.2, cas_only).
    set sarc2' := <[e := ainfo2]> (delete e sarc2).
    iDestruct (ghost_map_lookup with "Hγsa2 e↪ainfo1") as %Hsarc2e.
    iMod (ghost_map_delete with "Hγsa2 e↪ainfo1") as "Hγsa2".
    iMod (ghost_map_insert e ainfo2 with "Hγsa2") as "[Hγsa2 e↪ainfo2]"; [by apply lookup_delete|].

    iMod ("Hclose" with "[-AU Hγb e↪ainfo2 M⊢Mw' M⊢Ms']") as "_".
    { repeat iExists _. iFrame "HN M●2 Ms●2 Mw●2 Hγsa2 Hγwa2 Hγm2 Hγb2". rewrite omo_insert_r_write_op.
      iNext. repeat iExists _. iFrame "AllEvents2 AllStrongs2 AllWeaks2 omos↦2 omow↦2 Hγu2 Hγd2 Hγl2 Hγul2 esf2✓eVsf2 ewf2✓eVwf2 Hnsf2 P2 ⊒upds2@Vwf2
        ⊒ulcks2@Vwf2 ⊒stf2s@Vsf2 ⊒stf2w@Vwf2". iSplitR; last iSplitL.
      - iApply big_sepL_forall. iIntros "%i %ew %Hew".
        iDestruct (big_sepL_lookup with "AllLocks2") as (eVw zw) "[ew✓eVw [%eVwEV %COND]]"; [exact Hew|].
        iExists eVw,zw. iFrame "ew✓eVw". iPureIntro. split; [done|].
        intros. apply COND in H. clear eVEV. des; [by left|].
        right. destruct (decide (e0 = e)) as [->|NEQ].
        + rewrite Hsarc2e in H. inversion H. subst ainfo0. exists e,ainfo2. rewrite lookup_insert. split; [done|]. set_solver +H0.
        + exists e0,ainfo0. rewrite lookup_insert_ne; [|done]. rewrite lookup_delete_ne; [|done]. done.
      - iApply (append_only_type_condition_update with "Hty2"); try done.
      - iPureIntro. eapply (sarc_update_1 _ _ _ ainfo2) in Hsarc2e as H; try done; [|solve_lat].
        eapply (sarc_update_2 _ _ _ ainfo2 _ _ _ _ lcks2 _ ulcks2) in Hsarc2e as H0; try done. clear eVEV. des. split_and!; try done.
        rewrite H0. replace (Vbs2 ⊔ (Vbw2 ⊔ V2)) with ((Vbs2 ⊔ Vbw2) ⊔ V2) by solve_lat. clear -LeVbs2Vbw2. solve_lat. }

    iModIntro. wp_if. iApply ("IH" $! ainfo2 with "[] [] [] Hγb e↪ainfo2 AU []"); try done.
    replace ainfo2.1.1.1.2 with V2 by solve_lat. iFrame "⊒V2". }

  (* CAS success, commit [Downgrade] event *)
  iDestruct "Pures" as %(-> & -> & ->).
  iDestruct "sVw2" as (Vm2) "((%Hmow2' & %Homow2' & %eVwn2EV & %eVwn2SYNC & %LeVw2Vm2 & %NEqVw2Vm2 & %NLeV2Vw2 & %NEqV1V2 & _) &
    _ & omow↦2 & %LeVm2V2 & WCOMMIT)".

  rewrite last_lookup -omo_write_op_length in LASTewf2.
  replace (Init.Nat.pred (length omow2)) with (length omow2 - 1) in LASTewf2 by lia.
  rewrite LASTewf2 in Eqgenw2. inversion Eqgenw2. subst ew2.
  iDestruct (OmoEinfo_agree with "ewf2✓eVwf2 ew2✓eVw2") as %<-.
  rewrite eVwf2EV in eVw2EV. inversion eVw2EV. subst zwf2 Vw2.

  destruct ty2; [|by iDestruct "Hty2" as %[? _]].
  iDestruct "Hty2" as "[_ [%Hzw1 ->]]". subst zw1.

  (* Insert [Downgrade] event right after the latest observation in eView *)
  iDestruct (OmoEview_latest_elem with "⊒M") as (e1) "[MAXe1 %e1IN]".
  iDestruct (OmoAuth_OmoEview with "M●2 ⊒M") as %VALM.
  apply VALM in e1IN as He1.
  iDestruct (OmoAuth_wf with "M●2") as %[OMO_GOOD2 _].
  eapply lookup_omo_surjective in He1 as Heidx1; [|done]. destruct Heidx1 as [eidx1 Heidx1].
  eapply omo_stlist_length in OMO_GOOD2 as EQlenST2.
  have [st1 Hst1] : is_Some (stlist2 !! (gen_of eidx1)).
  { rewrite lookup_lt_is_Some -EQlenST2. apply lookup_omo_lt_Some in Heidx1. done. }

  iDestruct (OmoAuth_OmoEinfo with "M●2 e✓eV") as %HeV.
  iDestruct (OmoAuth_OmoEinfo' with "M●2 e✓eV") as %[eidx Heidx].
  iDestruct (ghost_map_lookup with "Hγsa2 e↪ainfo1") as %Hsarc2e.
  have [st Hst] : is_Some (stlist2 !! (gen_of eidx)).
  { rewrite lookup_lt_is_Some -EQlenST2. apply lookup_omo_lt_Some in Heidx. done. }
  have eINdom : e ∈ dom sarc2 by apply elem_of_dom_2 in Hsarc2e.

  iDestruct (big_sepS_elem_of _ _ e with "MAXe1") as "e≤e1"; [done|].
  iDestruct (OmoLe_Le with "M●2 e≤e1") as %LEgengen1; [done|done|].

  have LeV0V2 : V0 ⊑ V2 by clear -LeV0'V0'' LeV0''V1 LeV1V2; solve_lat.
  set opId := length E2.
  set M2 : eView := {[opId]} ∪ M.
  set eVop := mkOmoEvent Downgrade V2 M2.
  set E2' := E2 ++ [eVop].
  set gen1 := gen_of eidx1.
  set nst1 := (st1.1, (st1.2.1.1 ∪ {[opId]}, st1.2.1.2, st1.2.2)).

  have STEPop : step opId eVop st1 nst1.
  { eapply arc_step_Downgrade; try done; [set_solver-|..].
    - have eIN : e ∈ dom sarc2 by apply elem_of_dom_2 in Hsarc2e.
      specialize (strong_arc_persist _ _ _ _ _ _ _ _ OMO_GOOD2 Heidx HeV eVEV eIN VALsarcwarc2) as H.
      apply H in Hst1; [|done]. set_solver +Hst1.
    - unfold not. intros. specialize (weak_state_valid _ _ _ _ _ OMO_GOOD2 Hst1) as H'. apply H' in H. lia. }
  specialize (weak_arc_insert_gen_good _ _ _ _ _ _ OMO_GOOD2 Hst1 STEPop HInitWrite2 Alive2)
   as (stlist2' & Hgengood2 & Hstlist2').

  iMod "AU" as (????) "[>M●2' [_ Commit]]".
  iDestruct (OmoAuth_agree with "M●2 M●2'") as %(<- & <- & <- & <-). iCombine "M●2 M●2'" as "M●2".
  iDestruct (OmoSnapStates_get with "M●2") as "#ST◯2".
  iDestruct (OmoUB_into_gen with "M●2 MAXe1") as %MAXgen1; [done|].

  iDestruct (view_at_mono_2 _ V2 with "⊒M@V0''") as "⊒M@V2"; [solve_lat|].
  iMod (OmoAuth_insert _ _ _ _ _ _ _ _ _ _ (gen_of eidx1) with "M●2 ⊒M@V2 WCOMMIT []") as (γs2')
    "(M●2 & #⊒M2@V2 & #opId↦ewn2 & #opId✓eVop & WCOMMIT)"; [iPureIntro; split_and!; try done; [by subst eVop|set_solver-]|].
  iMod (OmoHb_new_2 _ _ _ _ _ _ _ _ (length Ew2) ({[length Ew2]} ∪ Mw') with "M●2 [] opId✓eVop") as "[M●2 #opId⊒ewn2]".
  { set_solver-. } { iFrame "⊒Mw2@V2". }

  iMod (SeenPrevStrong_after_weak_event with "M●2 Ms●2 Mw●2 omos↦2 Hγm2 [] M⊢Ms' AllEvents2 AllStrongs2 opId✓eVop opId↦ewn2")
    as "(#SeenPrevStrongopId & [M●2 M●2'] & Ms●2 & Mw●2 & omos↦2 & Hγm2 & M⊢Ms')"; [exact e1IN|done|done|..].
  { iDestruct (view_at_mono_2 _ V2 with "⊒Ms'@V0''") as "⊒Ms'@V2"; [solve_lat|]. iFrame "⊒Ms'@V2". }

  iDestruct (AllStrongs_update with "M●2 Ms●2 Mw●2 omos↦2 AllStrongs2 opId↦ewn2 ST◯2") as "#AllStrongs2'";
    [done|..|done|by apply lookup_omo_lt_Some in Heidx1|]. { intros. eapply Hstlist2' in H; [|done]. rewrite H. done. }

  iAssert (⌜ size stf2.2.1.1 ≠ 0 ⌝)%I with "[-]" as %NZstf2.
  { iIntros "%Zsz". apply size_empty_inv in Zsz. fold_leibniz. rewrite Zsz dom_empty_iff_L in DOMwarc2. destruct nsf2.
    - symmetry in EQnsf2. apply size_empty_inv in EQnsf2. fold_leibniz. rewrite EQnsf2 dom_empty_iff_L in DOMsarc2.
      rewrite DOMsarc2 in Hsarc2e. done.
    - iDestruct "Hnsf2" as "(_ & _ & _ & e0↪ainfo & _)". iDestruct (ghost_map_lookup with "Hγwa2 e0↪ainfo") as %Hwarc2e0.
      rewrite DOMwarc2 in Hwarc2e0. done. }

  iDestruct (view_at_mono_2 _ V2 with "⊒ulcks2@Vwf2") as "⊒ulcks2@V2"; [solve_lat|].
  iDestruct (view_at_mono_2 _ V2 with "⊒Mw@V0''") as "⊒Mw@V2"; [solve_lat|].
  iDestruct (OmoEview_union_obj with "⊒Mw@V2 ⊒ulcks2@V2") as "⊒Mw'@V2".
  set ainfo2 := (ainfo1.1.1.1.1, ainfo1.1.1.1.2 ⊔ V2, ainfo1.1.1.2 ∪ {[opId]}, ainfo1.1.2, cas_only).
  set ainfo2' := ((qwa2/2)%Qp, ainfo2.1.1.1.2, ainfo2.1.1.2, ainfo2.1.2 ∪ ulcks2, cas_only).
  set sarc2' := <[e := ainfo2]> (delete e sarc2).
  set warc2' := <[opId := ainfo2']> warc2.
  iMod (ghost_map_delete with "Hγsa2 e↪ainfo1") as "Hγsa2".
  iMod (ghost_map_insert e ainfo2 with "Hγsa2") as "[Hγsa2 e↪ainfo2]"; [by apply lookup_delete|].
  iMod (ghost_map_insert opId ainfo2' with "Hγwa2") as "[Hγwa2 opId↪ainfo2']".
  { rewrite -not_elem_of_dom. unfold not. intros. apply VALwarc2 in H. lia. }

  replace (qsa2/2 + qwa2/2)%Qp with ((qsa2/2 + qwa2/2/2) + qwa2/2/2)%Qp; last first.
  { by rewrite -Qp.add_assoc -Qp.div_add_distr Qp.add_diag Qp.mul_div_r. }
  iDestruct "Hγb2" as "[Hγb2 Hγb']". iDestruct "Hγul2" as "[Hγul2 Hγul']".

  iMod ("Commit" $! V2 γs2' _ _ M2 with "[$⊒V2 $M●2' $WCOMMIT Hγb e↪ainfo2 opId↪ainfo2' Hγb' Hγul']") as "HΦ".
  { iSplitL; first iSplitL "Hγb e↪ainfo2".
    - repeat iExists _. iFrame "HN AInv ⊒M2@V2 ⊒Mw@V0'' ⊒Ms@V0'' e✓eV e↪ainfo2 Hγb". iSplit.
      + iApply view_at_unfold. rewrite monPred_at_in. iPureIntro. clear -LeV0'V0'' LeV0''V1 LeV1V2. solve_lat.
      + iPureIntro. split_and!; try done; set_solver +eM SubainfoM.
    - repeat iExists _. iFrame "HN AInv ⊒M2@V2 ⊒Mw'@V2 ⊒Ms@V0'' opId✓eVop opId↪ainfo2' Hγb' Hγul'". iSplit; last iSplit.
      + iApply view_at_unfold. rewrite monPred_at_in. iPureIntro. clear -LeV0'V0'' LeV0''V1 LeV1V2. solve_lat.
      + rewrite decide_False; [done|]. unfold not. intros. rewrite lookup_lt_is_Some in He1. lia.
      + iPureIntro. split_and!; try done; [set_solver-|by right;right;right|set_solver +SubainfoM|set_solver +SubainfoMw].
    - iPureIntro. split_and!; try done; [set_solver-|]. by eexists. }

  iDestruct (OmoAuth_wf with "M●2") as %[OMO_GOOD2' _].
  eapply weak_arc_insert_new_state in OMO_GOOD2 as (nstf2 & Hnstf2 & Hnstf2'); [|exact OMO_GOOD2'|done..].

  iMod ("Hclose" with "[-HΦ]") as "_".
  { repeat iExists _. iFrame "HN M●2 Ms●2 Mw●2 Hγsa2 Hγwa2 Hγb2 Hγm2".
    iNext. do 4 iExists _. iExists nstf2. repeat iExists _. iCombine "⊒upds2@Vwf2 ⊒ulcks2@Vwf2 ⊒stf2w@Vwf2" as "RES".
    iDestruct (view_at_mono_2 _ Vm2 with "RES") as "(⊒upds2@Vm2 & ⊒ulcks2@Vm2 & ⊒stf2w@Vm2)"; [solve_lat|].
    iFrame "AllStrongs2' omos↦2 omow↦2 Hγu2 Hγd2 Hγl2 Hγul2 Hnsf2 esf2✓eVsf2 ewn2✓eVwn2 ⊒upds2@Vm2 ⊒ulcks2@Vm2".
    rewrite Hnstf2' /=. iFrame "⊒stf2s@Vsf2 ⊒stf2w@Vm2". iSplitR; last iSplitR; last iSplitR; last iSplitL; last iSplit.
    - iApply big_sepL_snoc. iFrame "AllEvents2 SeenPrevStrongopId".
    - rewrite Homow2' omo_append_w_write_op. iApply big_sepL_snoc. iSplit.
      + iApply big_sepL_forall. iIntros "%i %ew %Hew".
        iDestruct (big_sepL_lookup with "AllWeaks2") as (eVw zw) "(ew✓eVw & [%eVwEV %GEzw] & Hi)"; [exact Hew|].
        rewrite dom_insert_L. iExists eVw,zw. iFrame "ew✓eVw". iSplit; [done|]. destruct i; [done|].
        iDestruct "Hi" as (????) "(Mw◯ & ew'✓eVw' & Pures & CASE)". repeat iExists _. iFrame "Mw◯ ew'✓eVw' Pures".
        iDestruct "CASE" as "[CASE|[CASE|[CASE|CASE]]]"; [|by iRight;iLeft|by iRight;iRight;iLeft|by iRight;iRight;iRight].
        iLeft. iDestruct "CASE" as (??) "(e0↦ew & e0✓eV0 & e0⊒ew & %)". repeat iExists _. iFrame "e0↦ew e0✓eV0 e0⊒ew".
        iPureIntro. clear eVEV. des; split_and!; try done; [by left|].
        right. exists e'. split; [done|]. intros. apply H2. des. split; [done|].
        have [EQopId|IN] : 0 = opId ∨ 0 ∈ dom warc2; [set_solver +H4|subst opId; rewrite lookup_lt_is_Some in He1; lia|done].
      + rewrite dom_insert_L. iExists eVwn2,(size stf2.2.1.1 + 1)%Z. iFrame "ewn2✓eVwn2". iSplit.
        { iPureIntro. rewrite eVwn2EV. split; [done|]. lia. }
        rewrite -omo_write_op_length. destruct (length omow2) eqn:Hlen; [done|].
        rewrite -Hlen. rewrite -Hlen in LASTewf2. clear Hlen n.
        iExists omow2,ewf2,eVwf2,(size stf2.2.1.1). iFrame "Mw◯2 ewf2✓eVwf2". iSplit; [by rewrite eVwf2EV|].
        iLeft. iExists opId,eVop. iFrame "opId↦ewn2 opId✓eVop opId⊒ewn2".
        iPureIntro. split_and!; try done; [lia|]. left. done.
    - rewrite Homow2' omo_append_w_write_op. iApply big_sepL_snoc. iSplit.
      + iApply big_sepL_forall. iIntros "%i %ew %Hew".
        iDestruct (big_sepL_lookup with "AllLocks2") as (eVw zw) "[ew✓eVw [%eVwEV %COND]]"; [exact Hew|].
        iExists eVw,zw. iFrame "ew✓eVw". iPureIntro. split; [done|]. intros. apply COND in H. clear eVEV. des; [by left|].
        right. destruct (decide (e0 = e)) as [->|NEQ].
        * rewrite Hsarc2e in H. inversion H. subst ainfo0.
          exists e,ainfo2. rewrite lookup_insert. split; [done|]. set_solver +H0.
        * exists e0,ainfo0. rewrite lookup_insert_ne; [|done]. rewrite lookup_delete_ne; [|done]. done.
      + iExists eVwn2,(size stf2.2.1.1 + 1)%Z. iFrame "ewn2✓eVwn2".
        iPureIntro. rewrite eVwn2EV. split; [done|]. intros. lia.
    - rewrite lookup_insert_ne; last first.
      { unfold not. intros. subst opId. rewrite lookup_lt_is_Some in He1. lia. }
      destruct (warc2 !! 0); [done|]. iFrame "P2".
    - iSplit; [|done]. iLeft. iExists opId. iFrame "opId⊒ewn2".
    - rewrite size_union; last first.
      { have NOTIN : opId ∉ stf2.2.1.1; [|set_solver +NOTIN]. unfold not. intros.
        rewrite -DOMwarc2 in H. apply VALwarc2 in H. lia. }
      rewrite size_singleton Homow2' omo_append_w_write_op last_snoc eVwn2EV.
      eapply (sarc_update_snoc_1 _ _ _ ainfo2 _ _ eVop) in Hsarc2e as H; try done; [|solve_lat|set_solver-].
      eapply (sarc_update_snoc_2 _ _ _ ainfo2 _ _ _ eVop) in Hsarc2e as H0; try done; [|set_solver-|by right;set_solver-].
      clear eVEV. des. iPureIntro. split_and!; try done.
      + simpl. replace (Z.of_nat (size stf2.2.1.1) + 1)%Z with (Z.of_nat (size stf2.2.1.1 + 1)) by lia. done.
      + rewrite map_fold_insert_L; [|by apply frac_sum_wf|]; last first.
        { rewrite -not_elem_of_dom. unfold not. intros. apply VALwarc2 in H11. lia. }
        rewrite map_fold_init_frac in Hqwa2. rewrite {1}/frac_sum /=. done.
      + rewrite dom_insert_L. unfold ArcsValid. intros. rewrite app_length /=.
        have [EQe0|e0IN] : e0 = opId ∨ e0 ∈ dom warc2; [set_solver +H11|subst e0; lia|apply VALwarc2 in e0IN; lia].
      + eapply (dom_same _ _ _ ainfo2) in Hsarc2e as EQdom. rewrite -EQdom dom_insert_L.
        unfold ArcsValid2. intros. destruct (decide (e0 = length E2)) as [->|NEQ].
        * rewrite lookup_app_1_eq in H11. inversion H11. subst eV0. done.
        * rewrite lookup_app_1_ne in H11; [|done].
          apply VALsarcwarc2 in H11 as H12. destruct (eV0.(type)) eqn:HeV0; try done.
          unfold not. intros. have [EQe2|INe2] : e2 = opId ∨ e2 ∈ dom warc2; [set_solver +H13|..|done].
          subst e2. apply VALeid2 in H11. rewrite HeV0 in H11. lia.
      + unfold SeenWeakClone. intros. destruct (decide (e' = length E2)) as [->|NEQ].
        * rewrite lookup_app_1_eq in H12. inversion H12. subst eV0. inversion H13.
        * rewrite lookup_app_1_ne in H12; [|done]. apply VALeid2 in H12 as H14. rewrite H13 in H14.
          rewrite lookup_insert_ne in H11; [|lia]. eapply SeenWeakClone2; try done.
      + rewrite omo_insert_w_write_op lookup_app_l; [|by rewrite take_length -omo_write_op_length; lia].
        rewrite lookup_take_Some. split; [done|]. lia.
      + rewrite Hnstf2. subst nstf2. simpl. done.
      + rewrite dom_insert_L DOMwarc2. set_solver-.
      + by rewrite /ArcAlive Forall_app Forall_singleton.
      + apply EventIdValid_update; try done.
      + rewrite H0 map_fold_insert_L; [|solve_lat|]; last first.
        { rewrite -not_elem_of_dom. unfold not. intros. apply VALwarc2 in H11. lia. }
        rewrite {2}/view_join_total /=.
        have LEainfoV1 : ainfo.1.1.1.2 ⊑ V1 by solve_lat.
        replace (Vbs2 ⊔ (Vbw2 ⊔ V2)) with ((Vbs2 ⊔ Vbw2) ⊔ V2) by solve_lat.
        replace ((((map_fold view_join_total Vp2 sarc2 ⊔ V2) ⊔ (((ainfo.1.1.1.2 ⊔ V1) ⊔ V2) ⊔ map_fold view_join_total Vp2 warc2)) ⊔ Vsf2) ⊔ Vm2)
          with ((((map_fold view_join_total Vp2 sarc2 ⊔ map_fold view_join_total Vp2 warc2) ⊔ Vsf2) ⊔ Vm2) ⊔ V2) by solve_lat. solve_lat.
      + solve_lat.
      + unfold SeenUpgrade. intros. destruct (decide (e0 = length E2)) as [->|NEQ].
        * rewrite lookup_app_1_eq in H11. inversion H11. subst eV0. done.
        * rewrite lookup_app_1_ne in H11; [|done]. apply SeenUpgrade2 in H11. destruct (eV0.(type)); try done.
          des; [by left|]. right. exists e',ainfo0. rewrite lookup_insert_ne; [done|]. unfold not. intros. subst e'.
          apply elem_of_dom_2, VALwarc2 in H11. lia.
      + unfold ArcsSeen. intros. destruct (decide (e0 = opId)) as [->|NEQ].
        * rewrite lookup_insert in H11. inversion H11. subst ainfo0. apply LEsarc2 in Hsarc2e. solve_lat.
        * rewrite lookup_insert_ne in H11; [|done]. apply LEwarc2 in H11. done.
      + rewrite /StlistValid Forall_app Forall_cons. rewrite /StlistValid Forall_lookup in VALstlist2. split_and!.
        * rewrite Forall_lookup. intros. rewrite lookup_take_Some in H11. des. eapply VALstlist2; try done.
        * simpl in *. intros. eapply VALstlist2; [done|]. set_solver +H11.
        * rewrite Forall_lookup. intros.
          have [x' H11'] : is_Some (stlist2 !! (gen_of eidx1 + 1 + i)).
          { eapply interp_omo_length in Hgengood2 as Hlen. inversion Hlen.
            rewrite drop_length in H14. rewrite lookup_lt_is_Some. apply lookup_lt_Some in H11. lia. }
          specialize (Hstlist2' _ _ _ H11' H11). subst x.
          apply VALstlist2 in H11'; [|set_solver +H12]. done.
      + destruct (decide (nsf2 = 0)); [|done]. rewrite map_fold_insert_L; [solve_lat|solve_lat|].
        rewrite -not_elem_of_dom. unfold not. intros. apply VALwarc2 in H11. lia. }

  iModIntro. wp_pures. by iApply "HΦ".
Qed.

Lemma clone_weak_spec :
  clone_weak_spec' code.clone_weak ArcInv WeakArc.
Proof.
  intros N DISJ l tid γg M e V0 P1 P2. iIntros "#⊒V0 WArc" (Φ) "AU".
  iDestruct "WArc" as (??????????) "(%&%&%&%&%&%&%& #HN & #AInv & #⊒M & #⊒Ms & #⊒Mw & #e✓eV & #⊒ainfo & Hγb & e↪ainfo & Hγul & HeP2 &
    (%Hainfo2 & %eM & %eVEV & %SubainfoM & %SubainfoMw))".
  iLöb as "IH" forall (ainfo Hainfo2 SubainfoM SubainfoMw) "⊒ainfo".
  wp_lam. wp_pures. rewrite -[Z.to_nat 1]/(1%nat). wp_bind (!ʳˡˣ _)%E.

  (* Inv access 1 *)
  iInv "AInv" as "H" "Hclose".
  iDestruct "H" as (?? γs1 ???????) "(%&%&%& %sarc1 & %warc1 & %qsa1 & %qwa1 & %alive1 & %E1 & %Es1 & %Ew1 & %omo1 & %omos1 &
    %omow1 & %stlist1 & %mos1 & %mow1 & %Mono1 & >HN' & >M●1 & >Ms●1 & >Mw●1 & >Hγsa1 & >Hγwa1 & >Hγb1 & >Hγm1 & Alive1)".
  gname_agree with "HN HN'". iClear "HN'".
  iDestruct (ghost_var_agree with "Hγb Hγb1") as %<-.

  iDestruct (OmoEview_update with "M●1 ⊒M ⊒Mw") as (Mw') "(M●1 & #⊒Mw' & M⊢Mw' & %SubMwMw')".
  iDestruct (OmoEview_update with "M●1 ⊒M ⊒Ms") as (Ms') "(M●1 & #⊒Ms' & M⊢Ms' & %SubMsMs')".
  iCombine "⊒V0 ⊒ainfo" as "⊒V0'". rewrite monPred_in_view_op. set V0' := V0 ⊔ ainfo.1.1.1.2.
  iCombine "⊒M ⊒Ms ⊒Mw ⊒ainfo ⊒Mw' ⊒Ms' HeP2" as "RES".
  iDestruct (view_at_intro_incl with "RES ⊒V0'") as (V0'')
    "(#⊒V0'' & %LeV0'V0'' & (#⊒M@V0'' & #⊒Ms@V0'' & #⊒Mw@V0'' & #⊒ainfo@V0'' & #⊒Mw'@V0'' & #⊒Ms'@V0'' & HeP2@V0''))".

  iDestruct "Alive1" as (Vbs1 Vbw1 ty1 uf1 stf1 esf1 ewf1 eVsf1 eVwf1 nsf1) "(%zwf1 & %Vsf1 & %Vwf1 & %Vp1 & %qsa1a & %qsa1b & %qu1 & %qd1 & %upds1 &
    %dgds1 & %lcks1 & %ulcks1 & >#AllEvents1 & >#AllStrongs1 & >#AllWeaks1 & >omos↦1 & >omow↦1 & >Hγu1 & >Hγd1 & >Hγl1 & >Hγul1 &
    >#AllLocks1 & [>#⊒upds1@Vwf1 >#⊒ulcks1@Vwf1] & >#esf1✓eVsf1 & >#ewf1✓eVwf1 & Hnsf1 & P2 & Hty1 & >#⊒stf1s@Vsf1 & >#⊒stf1w@Vwf1 & >Pures)".
  iDestruct "Pures" as %(Subuf1 & LASTesf1 & LASTewf1 & eVsf1EV & eVwf1EV & Hqsa1 & Hqwa1 & VALsarc1 & VALwarc1 & VALsarcwarc1 & SeenClone1 &
    SeenWeakClone1 & HInitWrite1 & LASTstf1 & DOMsarc1 & DOMwarc1 & EQqsa1 & Alive1 & VALeid1 & LeVbs1Vbw1 & GeVsf1 & GeVwf1 &
    SeenUpgrade1 & SeenDowngrade1 & SeenUnlock1 & LEsarc1 & LEwarc1 & VALstlist1 & LeVsf1 & EQnsf1).

  wp_apply (append_only_loc_relaxed_read with "[$Mw●1 $⊒Mw' $omow↦1 $⊒V0'']"); [solve_ndisj|].
  iIntros (ew1 genw1 vw1 Vw1 V1 eVw1 eVwn1) "(Pures & Mw●1 & _ & #MAXew1 & #ew1✓eVw1 & #ewn1✓eVwn1 & _ & #⊒V1 & _ & #⊒Mw1@V1 & omow↦1)".
  iDestruct "Pures" as %(Hgenw1 & eVw1EV & LeV0''V1 & eVwn1EV & eVwn1SYNC).
  iDestruct (big_sepL_lookup with "AllWeaks1") as (eVw1' zw1) "(ew1✓eVw1' & [%eVw1'EV %GEzw1] & Hgenw1)"; [exact Hgenw1|].
  iDestruct (OmoEinfo_agree with "ew1✓eVw1 ew1✓eVw1'") as %<-. rewrite eVw1EV /= in eVw1'EV. subst vw1.

  (* Prove that 1 ≤ zw1 *)
  iDestruct (ghost_var_agree with "Hγul Hγul1") as %<-.
  iDestruct (weak_counter_load_valid with "Mw●1 Hγwa1 [] MAXew1 ew1✓eVw1 ewf1✓eVwf1 e↪ainfo Hnsf1 Hty1") as %GEzw1'.
  { by rewrite omo_insert_r_write_op. } { by rewrite omo_insert_r_write_op. } { by rewrite eVw1EV. } { by rewrite eVwf1EV. } { done. }
  { done. } { done. } { set_solver +SubainfoMw SubMwMw'. } { rewrite omo_insert_r_write_op. iFrame "AllWeaks1". }
  have NEQzw1 : zw1 ≠ (-1)%Z by lia.

  set ainfo1 := (ainfo.1.1.1.1, ainfo.1.1.1.2 ⊔ V1, ainfo.1.1.2, ainfo.1.2, cas_only).
  set warc1' := <[e := ainfo1]> (delete e warc1).
  iDestruct (ghost_map_lookup with "Hγwa1 e↪ainfo") as %Hwarc1e.
  iMod (ghost_map_delete with "Hγwa1 e↪ainfo") as "Hγwa1".
  iMod (ghost_map_insert e ainfo1 with "Hγwa1") as "[Hγwa1 e↪ainfo1]"; [by apply lookup_delete|].

  iMod ("Hclose" with "[-AU Hγb e↪ainfo1 M⊢Mw' M⊢Ms' Hγul HeP2@V0'']") as "_".
  { repeat iExists _. iFrame "HN M●1 Ms●1 Mw●1 Hγb1 Hγsa1 Hγwa1 Hγm1". rewrite omo_insert_r_write_op.
    iNext. repeat iExists _. apply (dom_same _ _ _ ainfo1) in Hwarc1e as EQdom. rewrite -EQdom.
    iFrame "AllEvents1 AllStrongs1 AllWeaks1 omos↦1 omow↦1 Hγu1 Hγd1 Hγl1 Hγul1 AllLocks1 Hnsf1 Hty1".
    iFrame "esf1✓eVsf1 ewf1✓eVwf1 ⊒upds1@Vwf1 ⊒ulcks1@Vwf1 ⊒stf1s@Vsf1 ⊒stf1w@Vwf1". iSplitL.
    - destruct (decide (e = 0)) as [->|NEQ]; [by rewrite Hwarc1e lookup_insert|].
      rewrite lookup_insert_ne; [|done]. rewrite lookup_delete_ne; [|done]. done.
    - iPureIntro. eapply (warc_update_1 _ _ _ ainfo1) in Hwarc1e as H; try done; [|solve_lat].
      eapply (warc_update_2 _ _ _ ainfo1) in Hwarc1e as H0; try done. clear eVEV. des. split_and!; try done.
      + rewrite H0. replace (Vbs1 ⊔ (Vbw1 ⊔ V1)) with ((Vbs1 ⊔ Vbw1) ⊔ V1) by solve_lat. clear -LeVbs1Vbw1. solve_lat.
      + rewrite H0. destruct (decide (nsf1 = 0)); [|done]. solve_lat. }

  iModIntro. wp_pures. rewrite -[Z.to_nat 1]/(1%nat). wp_bind (casʳˡˣ(_,_,_))%E.

  (* Inv access 2 *)
  iInv "AInv" as "H" "Hclose".
  iDestruct "H" as (?? γs2 ???????) "(%&%&%& %sarc2 & %warc2 & %qsa2 & %qwa2 & %alive2 & %E2 & %Es2 & %Ew2 & %omo2 & %omos2 &
    %omow2 & %stlist2 & %mos2 & %mow2 & %Mono2 & >HN' & >M●2 & >Ms●2 & >Mw●2 & >Hγsa2 & >Hγwa2 & >Hγb2 & >Hγm2 & Alive2)".
  gname_agree with "HN HN'". iClear "HN'".
  iDestruct (ghost_var_agree with "Hγb Hγb2") as %<-.
  iDestruct (OmoAuth_omo_nonempty with "M●2") as %Nomo2.
  have NZomo2 : length omo2 ≠ 0 by destruct omo2.
  iDestruct (OmoSnapOmo_get with "Mw●2") as "#Mw◯2".

  iDestruct "Alive2" as (Vbs2 Vbw2 ty2 uf2 stf2 esf2 ewf2 eVsf2 eVwf2 nsf2) "(%zwf2 & %Vsf2 & %Vwf2 & %Vp2 & %qsa2a & %qsa2b & %qu2 & %qd2 & %upds2 &
    %dgds2 & %lcks2 & %ulcks2 & >#AllEvents2 & >#AllStrongs2 & >#AllWeaks2 & >omos↦2 & >omow↦2 & >Hγu2 & >Hγd2 & >Hγl2 & >Hγul2 &
    >#AllLocks2 & [>#⊒upds2@Vwf2 >#⊒ulcks2@Vwf2] & >#esf2✓eVsf2 & >#ewf2✓eVwf2 & Hnsf2 & P2 & Hty2 & >#⊒stf2s@Vsf2 & >#⊒stf2w@Vwf2 & >Pures)".
  iDestruct "Pures" as %(Subuf2 & LASTesf2 & LASTewf2 & eVsf2EV & eVwf2EV & Hqsa2 & Hqwa2 & VALsarc2 & VALwarc2 & VALsarcwarc2 & SeenClone2 &
    SeenWeakClone2 & HInitWrite2 & LASTstf2 & DOMsarc2 & DOMwarc2 & EQqsa2 & Alive2 & VALeid2 & LeVbs2Vbw2 & GeVsf2 & GeVwf2 &
    SeenUpgrade2 & SeenDowngrade2 & SeenUnlock2 & LEsarc2 & LEwarc2 & VALstlist2 & LeVsf2 & EQnsf2).
  iMod (rel_objectively_intro (⊒∅) tid with "[]") as "#⊒∅"; [by iApply objective_objectively; iApply monPred_in_bot|].

  wp_apply (append_only_loc_cas_general with "[$Mw●2 $⊒Mw' $omow↦2 $⊒V1]"); try done; [solve_ndisj|..]; [set_solver +NEQzw1 Subuf2|].
  iIntros (b2 ew2 genw2 vw2 Vw2 V2 mow2' omow2' eVw2 eVwn2)
    "(Pures & #MAXew2 & #ew2✓eVw2 & #ewn2✓eVwn2 & Mw●2 & #⊒V2 & #⊒Mw2@V2 & CASE)".
  iDestruct "Pures" as %(Eqgenw2 & eVw2EV & LeV1V2).
  iDestruct "CASE" as "[(Pures & _ & omow↦2 & _) | [Pures sVw2]]".
  { (* CAS failed, try again *)
    iDestruct "Pures" as %(-> & NEQvw2 & -> & -> & eVwn2EV & eVwn2SYNC).

    set ainfo2 := (ainfo1.1.1.1.1, ainfo1.1.1.1.2 ⊔ V2, ainfo1.1.1.2, ainfo1.1.2, cas_only).
    set warc2' := <[e := ainfo2]> (delete e warc2).
    iDestruct (ghost_map_lookup with "Hγwa2 e↪ainfo1") as %Hwarc2e.
    iMod (ghost_map_delete with "Hγwa2 e↪ainfo1") as "Hγwa2".
    iMod (ghost_map_insert e ainfo2 with "Hγwa2") as "[Hγwa2 e↪ainfo2]"; [by apply lookup_delete|].

    iMod ("Hclose" with "[-Hγb e↪ainfo2 AU Hγul HeP2@V0'']") as "_".
    { repeat iExists _. iFrame "HN M●2 Ms●2 Mw●2 Hγsa2 Hγwa2 Hγm2 Hγb2". rewrite omo_insert_r_write_op.
      iNext. repeat iExists _. eapply (dom_same _ _ _ ainfo2) in Hwarc2e as EQdom. rewrite -EQdom.
      iFrame "AllEvents2 AllStrongs2 AllWeaks2 omos↦2 omow↦2 Hγu2 Hγd2 Hγl2 Hγul2 AllLocks2 Hnsf2 Hty2".
      iFrame "esf2✓eVsf2 ewf2✓eVwf2 ⊒upds2@Vwf2 ⊒ulcks2@Vwf2 ⊒stf2s@Vsf2 ⊒stf2w@Vwf2". iSplitL.
      - destruct (decide (e = 0)) as [->|NEQ]; [by rewrite lookup_insert|].
        rewrite lookup_insert_ne; [|done]. rewrite lookup_delete_ne; [|done]. done.
      - iPureIntro. eapply (warc_update_1 _ _ _ ainfo2) in Hwarc2e as H; try done; [|solve_lat].
        eapply (warc_update_2 _ _ _ ainfo2) in Hwarc2e as H0; try done. clear eVEV. des. split_and!; try done.
        + rewrite H0. replace (Vbs2 ⊔ (Vbw2 ⊔ V2)) with ((Vbs2 ⊔ Vbw2) ⊔ V2) by solve_lat. clear -LeVbs2Vbw2. solve_lat.
        + destruct (decide (nsf2 = 0)); [|done]. rewrite H0. clear -LeVsf2. solve_lat. }

    iModIntro. wp_if. replace (ainfo.1.1.1.1/2)%Qp with (ainfo2.1.1.1.1/2)%Qp by done.
    iDestruct (view_at_elim with "⊒V0'' HeP2@V0''") as "HeP2".
    iApply ("IH" with "[] [] [] Hγb e↪ainfo2 Hγul HeP2 AU []"); [done..|].
    subst ainfo2 ainfo1. simpl. replace ((ainfo.1.1.1.2 ⊔ V1) ⊔ V2) with V2; [done|]. solve_lat. }

  (* CAS success, commit [WeakClone] *)
  iDestruct "Pures" as %(-> & -> & ->).
  iDestruct "sVw2" as (Vm2) "((%Hmow2' & %Homow2' & %eVwn2EV & %eVwn2SYNC & %LeVw2Vm2 & %NEqVw2Vm2 & %NLeV2Vw2 & %NEqV1V2 & _) &
    _ & omow↦2 & _ & WCOMMIT)".

  rewrite last_lookup -omo_write_op_length in LASTewf2.
  replace (Init.Nat.pred (length omow2)) with (length omow2 - 1) in LASTewf2 by lia.
  rewrite LASTewf2 in Eqgenw2. inversion Eqgenw2. subst ew2.
  iDestruct (OmoEinfo_agree with "ewf2✓eVwf2 ew2✓eVw2") as %<-.
  rewrite eVwf2EV in eVw2EV. inversion eVw2EV. subst zwf2 Vw2.

  destruct ty2; [|by iDestruct "Hty2" as %[? _]].
  iDestruct "Hty2" as "[_ [%Hzw1 ->]]". subst zw1.

  (* Insert [WeakClone] event right after the latest observation in eView *)
  iDestruct (OmoEview_latest_elem with "⊒M") as (e1) "[MAXe1 %e1IN]".
  iDestruct (OmoAuth_OmoEview with "M●2 ⊒M") as %VALM.
  apply VALM in e1IN as He1.
  iDestruct (OmoAuth_wf with "M●2") as %[OMO_GOOD2 _].
  eapply lookup_omo_surjective in He1 as Heidx1; [|done]. destruct Heidx1 as [eidx1 Heidx1].
  eapply omo_stlist_length in OMO_GOOD2 as EQlenST2.
  have [st1 Hst1] : is_Some (stlist2 !! (gen_of eidx1)).
  { by rewrite lookup_lt_is_Some -EQlenST2; apply lookup_omo_lt_Some in Heidx1. }

  iDestruct (OmoAuth_OmoEinfo with "M●2 e✓eV") as %HeV.
  iDestruct (OmoAuth_OmoEinfo' with "M●2 e✓eV") as %[eidx Heidx].
  iDestruct (ghost_map_lookup with "Hγwa2 e↪ainfo1") as %Hwarc2e.
  have [st Hst] : is_Some (stlist2 !! (gen_of eidx)) by rewrite lookup_lt_is_Some -EQlenST2; apply lookup_omo_lt_Some in Heidx.
  have eINdom : e ∈ dom warc2 by apply elem_of_dom_2 in Hwarc2e.
  specialize (weak_arc_persist _ _ _ _ _ _ (dom sarc2) (dom warc2) OMO_GOOD2 Heidx HeV eVEV eINdom VALsarcwarc2) as Hstlist2.

  iDestruct (big_sepS_elem_of _ _ e with "MAXe1") as "e≤e1"; [done|].
  iDestruct (OmoLe_Le with "M●2 e≤e1") as %LEgengen1; [done|done|].
  apply Hstlist2 in Hst1 as eINst1; [|done].

  have LeV0V2 : V0 ⊑ V2 by solve_lat.
  set opId := length E2.
  set M2 : eView := {[opId]} ∪ M.
  set eVop := mkOmoEvent (WeakClone e) V2 M2.
  set E2' := E2 ++ [eVop].
  set gen1 := gen_of eidx1.
  set nst1 := (st1.1, (st1.2.1.1 ∪ {[opId]}, st1.2.1.2, st1.2.2)).

  have STEPop : step opId eVop st1 nst1.
  { eapply arc_step_WeakClone; try done; [set_solver-|]. unfold not. intros.
    specialize (weak_state_valid _ _ _ _ _ OMO_GOOD2 Hst1) as H'. apply H' in H. lia. }
  specialize (weak_arc_insert_gen_good _ _ _ _ _ _ OMO_GOOD2 Hst1 STEPop HInitWrite2 Alive2)
    as (stlist2' & Hgengood2 & Hstlist2').

  iMod "AU" as (????) "[>M●2' [_ Commit]]".
  iDestruct (OmoAuth_agree with "M●2 M●2'") as %(<- & <- & <- & <-). iCombine "M●2 M●2'" as "M●2".
  iDestruct (OmoSnapStates_get with "M●2") as "#ST◯2".
  iDestruct (OmoUB_into_gen with "M●2 MAXe1") as %MAXgen1; [done|].

  iDestruct (view_at_mono_2 _ V2 with "⊒M@V0''") as "⊒M@V2"; [solve_lat|].
  iMod (OmoAuth_insert _ _ _ _ _ _ _ _ _ _ (gen_of eidx1) with "M●2 ⊒M@V2 WCOMMIT []") as (γs2')
    "(M●2 & #⊒M1@V2 & #opId↦ewn2 & #opId✓eVop & WCOMMIT)"; [iPureIntro; split_and!; try done; [by subst eVop|set_solver-]|].
  iMod (OmoHb_new_2 _ _ _ _ _ _ _ _ (length Ew2) ({[length Ew2]} ∪ Mw') with "M●2 [] opId✓eVop") as "[M●2 #opId⊒ewn2]".
  { set_solver-. } { iFrame "⊒Mw2@V2". }

  iMod (SeenPrevStrong_after_weak_event with "M●2 Ms●2 Mw●2 omos↦2 Hγm2 [] M⊢Ms' AllEvents2 AllStrongs2 opId✓eVop opId↦ewn2")
    as "(#SeenPrevStrongopId & [M●2 M●2'] & Ms●2 & Mw●2 & omos↦2 & Hγm2 & M⊢Ms')"; [exact e1IN|done|done|..].
  { iDestruct (view_at_mono_2 _ V2 with "⊒Ms'@V0''") as "⊒Ms'@V2"; [solve_lat|]. iFrame "⊒Ms'@V2". }

  iDestruct (AllStrongs_update with "M●2 Ms●2 Mw●2 omos↦2 AllStrongs2 opId↦ewn2 ST◯2") as "#AllStrongs2'";
    [done|..|done|by apply lookup_omo_lt_Some in Heidx1|]. { intros. eapply Hstlist2' in H; [|done]. rewrite H. done. }

  set ainfo2 := (ainfo1.1.1.1.1, ainfo1.1.1.1.2 ⊔ V2, ainfo1.1.1.2 ∪ {[opId]}, ainfo1.1.2, cas_only).
  set ainfo2' := ((qwa2/2)%Qp, ainfo2.1.1.1.2, ainfo2.1.1.2, ainfo2.1.2, cas_only).
  set warc2' := <[opId := ainfo2']> (<[e := ainfo2]> (delete e warc2)).
  iMod (ghost_map_delete with "Hγwa2 e↪ainfo1") as "Hγwa2".
  iMod (ghost_map_insert e ainfo2 with "Hγwa2") as "[Hγwa2 e↪ainfo2]"; [by apply lookup_delete|].
  iMod (ghost_map_insert opId ainfo2' with "Hγwa2") as "[Hγwa2 opId↪ainfo2]".
  { eapply (dom_same _ _ _ ainfo2) in Hwarc2e. rewrite -not_elem_of_dom -Hwarc2e. unfold not. intros. apply VALwarc2 in H. lia. }
  replace (qsa2/2 + qwa2/2)%Qp with ((qsa2/2 + (qwa2/2/2)) + (qwa2/2/2))%Qp; last first.
  { by rewrite -Qp.add_assoc -Qp.div_add_distr Qp.add_diag Qp.mul_div_r. }
  iDestruct (ghost_var_agree with "Hγul Hγul2") as %<-.
  iDestruct "Hγb2" as "[Hγb2 Hγb']". iDestruct "Hγul2" as "[Hγul2 Hγul']".

  iMod ("Commit" $! V2 _ _ _ M2 with "[$⊒V2 $M●2' $WCOMMIT e↪ainfo2 opId↪ainfo2 Hγb Hγb' Hγul Hγul' HeP2@V0'']") as "HΦ".
  { have LE1 : ainfo.1.1.1.2 ⊑ V1 by solve_lat.
    iSplitL; [iSplitL "e↪ainfo2 Hγb Hγul HeP2@V0''"|].
    - repeat iExists _. iFrame "HN AInv ⊒M1@V2 e↪ainfo2 ⊒Ms@V0'' ⊒Mw@V0'' e✓eV Hγb Hγul HeP2@V0''". iSplit.
      + iApply view_at_unfold. rewrite monPred_at_in. iPureIntro. solve_lat.
      + iPureIntro. split_and!; try done; [set_solver +eM|set_solver +SubainfoM].
    - repeat iExists _. iFrame "HN AInv ⊒M1@V2 opId↪ainfo2 ⊒Ms@V0'' ⊒Mw@V0'' opId✓eVop Hγb' Hγul'". iSplit; last iSplit.
      + iApply view_at_unfold. rewrite monPred_at_in. iPureIntro. solve_lat.
      + iClear "IH". rewrite decide_False; [done|]. unfold not. intros. rewrite lookup_lt_is_Some in He1. lia.
      + iPureIntro. split_and!; try done; [set_solver-|by right;right;left;eexists|set_solver +SubainfoM].
    - iPureIntro. split_and!; try done; [set_solver-|]. by eexists. }

  have NEQeopId : e ≠ opId by unfold not; intros; apply VALM in eM; rewrite lookup_lt_is_Some in eM; lia.
  iDestruct (OmoAuth_wf with "M●2") as %[OMO_GOOD2' _].
  eapply weak_arc_insert_new_state in OMO_GOOD2 as (nstf2 & Hnstf2 & Hnstf2'); [|exact OMO_GOOD2'|done..].

  iMod ("Hclose" with "[-HΦ]") as "_".
  { repeat iExists _. iFrame "HN M●2 Ms●2 Mw●2 Hγsa2 Hγwa2 Hγb2 Hγm2".
    iNext. do 4 iExists _. iExists nstf2. repeat iExists _. iCombine "⊒upds2@Vwf2 ⊒ulcks2@Vwf2 ⊒stf2w@Vwf2" as "RES".
    iDestruct (view_at_mono_2 _ Vm2 with "RES") as "(⊒upds2@Vm2 & ⊒ulcks2@Vm2 & ⊒stf2w@Vm2)"; [done|].
    iFrame "AllStrongs2' omos↦2 omow↦2 Hγu2 Hγd2 Hγl2 Hγul2 Hnsf2 esf2✓eVsf2 ewn2✓eVwn2 ⊒upds2@Vm2 ⊒ulcks2@Vm2".
    rewrite Hnstf2' /=. iFrame "⊒stf2s@Vsf2 ⊒stf2w@Vm2".
    iSplitR; last iSplitR; last iSplitR; last iSplitL; last iSplit.
    - iApply big_sepL_snoc. iFrame "AllEvents2 SeenPrevStrongopId".
    - eapply (dom_same _ _ _ ainfo2) in Hwarc2e as EQdom.
      rewrite dom_insert_L -EQdom Homow2' omo_append_w_write_op. iApply big_sepL_snoc. iSplit.
      + iApply big_sepL_forall. iIntros "%i %ew %Hew".
        iDestruct (big_sepL_lookup with "AllWeaks2") as (eVw zw) "(ew✓eVw & [%eVwEV %GEzw] & Hi)"; [exact Hew|].
        iExists eVw,zw. iFrame "ew✓eVw". iSplit; [done|]. destruct i; [done|].
        iDestruct "Hi" as (????) "(Mw◯ & ew'✓eVw' & [%Hew' %eVw'EV] & CASE)".
        iExists omow,ew',eVw',v'. iFrame "Mw◯ ew'✓eVw'". iSplit; [done|].
        iDestruct "CASE" as "[(%&%& H1 & H2 & H3 & %)|CASE]"; [|by iRight].
        iLeft. iExists _,_. iFrame "H1 H2 H3". iPureIntro. clear eVEV. des.
        * split_and!; try done. left. done.
        * split_and!; try done. right. exists e'. split; [done|]. intros. des. apply H2. split; [done|].
          have [EQ0|IN] : 0 = opId ∨ 0 ∈ dom warc2; [set_solver +H4|by rewrite lookup_lt_is_Some in He1; lia|done].
      + iExists eVwn2,(size stf2.2.1.1 + 1)%Z. iFrame "ewn2✓eVwn2". iSplit.
        { iPureIntro. rewrite eVwn2EV. split; [done|]. lia. }
        destruct (length (omo_write_op omow2)) eqn:Hlen; [done|]. rewrite -Hlen. clear Hlen n.
        iExists omow2,ewf2,eVwf2,(size stf2.2.1.1)%Z. iFrame "Mw◯2 ewf2✓eVwf2". iSplit.
        * iPureIntro. rewrite -omo_write_op_length eVwf2EV. done.
        * iLeft. iExists opId,eVop. iFrame "opId↦ewn2 opId✓eVop opId⊒ewn2". iPureIntro. split_and!; try done.
          right. exists e. split; [done|]. intros. clear eVEV. des.
          have [EQopId|IN] : 0 = opId ∨ 0 ∈ dom warc2; [set_solver +H0|by rewrite lookup_lt_is_Some in He1; lia|].
          have SZ1 : size stf2.2.1.1 = 1 by lia. apply size_1_elem_of in SZ1 as [x Hstf2]. fold_leibniz.
          apply elem_of_dom_2 in Hwarc2e. rewrite DOMwarc2 Hstf2 elem_of_singleton in Hwarc2e. subst x.
          rewrite DOMwarc2 Hstf2 elem_of_singleton in IN. done.
    - rewrite Homow2' omo_append_w_write_op. iApply big_sepL_snoc. iFrame "AllLocks2".
      iExists eVwn2,(size stf2.2.1.1 + 1)%Z. iFrame "ewn2✓eVwn2". iPureIntro. rewrite eVwn2EV. split; [done|]. intros. lia.
    - destruct (decide (opId = 0)) as [->|NEQ1]; last destruct (decide (e = 0)) as [->|NEQ2].
      + by rewrite lookup_insert.
      + rewrite lookup_insert_ne; [|done]. rewrite lookup_insert. done.
      + do 2 (rewrite lookup_insert_ne; [|done]). rewrite lookup_delete_ne; [|done].
        destruct (warc2 !! 0); [done|]. iFrame "P2".
    - iSplit; [|iPureIntro; split_and!; try done]. iLeft. iExists opId. iFrame "opId⊒ewn2".
    - iPureIntro. rewrite Hnstf2' in Hnstf2.
      eapply (warc_update_2 _ _ _ ainfo2 V2 Vp2) in Hwarc2e as H; try done; [|set_solver-].
      clear eVEV. des. split_and!; try done.
      + by rewrite Homow2' omo_append_w_write_op last_snoc.
      + rewrite eVwn2EV. rewrite size_union.
        * rewrite size_singleton. simpl.
          replace (Z.of_nat (size stf2.2.1.1) + 1)%Z with (Z.of_nat (size stf2.2.1.1 + 1)) by lia. done.
        * have NOTIN : opId ∉ stf2.2.1.1; [|set_solver +NOTIN].
          unfold not. intros. rewrite -DOMwarc2 in H2. apply VALwarc2 in H2. lia.
      + rewrite map_fold_insert_L; [|by apply frac_sum_wf|]; last first.
        { eapply (dom_same _ _ _ ainfo2) in Hwarc2e. rewrite -not_elem_of_dom -Hwarc2e.
          unfold not. intros. apply VALwarc2 in H2. lia. }
        rewrite map_fold_insert_L; [|by apply frac_sum_wf|by apply lookup_delete].
        replace (frac_sum e ainfo2 (map_fold frac_sum (qwa2 / 2)%Qp (delete e warc2))) with
          (frac_sum e ainfo1 (map_fold frac_sum (qwa2 / 2)%Qp (delete e warc2))) by done.
        rewrite -map_fold_delete_L; [|by apply frac_sum_wf|done].
        rewrite map_fold_init_frac in Hqwa2. by rewrite -Hqwa2.
      + unfold ArcsValid. intros. apply VALsarc2 in H2. rewrite app_length /=. lia.
      + unfold ArcsValid. intros. rewrite dom_insert_L in H2.
        eapply (dom_same _ _ _ ainfo2) in Hwarc2e. rewrite -Hwarc2e in H2.
        have [EQe0|e0IN] : e0 = opId ∨ e0 ∈ dom warc2; [set_solver +H2|subst e0; rewrite app_length /=; lia|].
        apply VALwarc2 in e0IN. rewrite app_length /=. lia.
      + unfold ArcsValid2. intros. destruct (decide (e0 = length E2)) as [->|NEQ].
        * rewrite lookup_app_1_eq in H2. inversion H2. subst eV0. done.
        * rewrite lookup_app_1_ne in H2; [|done]. apply VALsarcwarc2 in H2 as HeV0.
          apply VALeid2 in H2 as HeV0'. destruct (eV0.(type)); try done.
          eapply (dom_same _ _ _ ainfo2) in Hwarc2e. rewrite dom_insert_L -Hwarc2e. unfold not. intros.
          have [EQe2|e2IN] : e2 = opId ∨ e2 ∈ dom warc2; [|lia|done]. set_solver +H3.
      + unfold SeenClone. intros. destruct (decide (e' = length E2)) as [->|NEQ].
        * rewrite lookup_app_1_eq in H3. inversion H3. subst eV0. done.
        * rewrite lookup_app_1_ne in H3; [|done]. eapply SeenClone2; try done.
      + unfold SeenWeakClone. intros. destruct (decide (e' = length E2)) as [->|NEQ].
        * rewrite lookup_app_1_eq in H3. inversion H3. subst eV0. inversion H4. subst e0.
          rewrite lookup_insert_ne in H2; [|done]. rewrite lookup_insert in H2.
          inversion H2. subst ainfo0. set_solver-.
        * rewrite lookup_app_1_ne in H3; [|done].
          destruct (decide (e0 = opId)) as [->|NEQ1]; last destruct (decide (e0 = e)) as [->|NEQ2].
          -- apply VALeid2 in H3. rewrite H4 in H3. lia.
          -- rewrite lookup_insert_ne in H2; [|done]. rewrite lookup_insert in H2. inversion H2. subst ainfo0.
             specialize (SeenWeakClone2 _ _ _ _ Hwarc2e H3 H4). set_solver +SeenWeakClone2.
          -- do 2 (rewrite lookup_insert_ne in H2; [|done]). rewrite lookup_delete_ne in H2; [|done].
             specialize (SeenWeakClone2 _ _ _ _ H2 H3 H4). set_solver +SeenWeakClone2.
      + rewrite omo_insert_w_write_op lookup_app_l; [|by rewrite take_length -omo_write_op_length; lia].
        rewrite lookup_take_Some. split; [|lia]. done.
      + eapply (dom_same _ _ _ ainfo2) in Hwarc2e. rewrite dom_insert_L -Hwarc2e DOMwarc2 /=. set_solver-.
      + by rewrite /ArcAlive Forall_app Forall_singleton.
      + unfold EventIdValid. intros. destruct (decide (e0 = length E2)) as [->|NEQ].
        * rewrite lookup_app_1_eq in H2. inversion H2. subst eV0. simpl. rewrite app_length /=.
          apply VALM in eM. rewrite lookup_lt_is_Some in eM. lia.
        * rewrite lookup_app_1_ne in H2; [|done]. apply VALeid2 in H2. destruct (eV0.(type)); try done; rewrite app_length /=; lia.
      + rewrite map_fold_insert_L; [|solve_lat|]; last first.
        { eapply (dom_same _ _ _ ainfo2) in Hwarc2e as EQdom. rewrite -not_elem_of_dom -EQdom.
          unfold not. intros. apply VALwarc2 in H2. lia. }
        rewrite H {2}/view_join_total /=.
        have LEainfoV1 : ainfo.1.1.1.2 ⊑ V1 by solve_lat.
        replace (Vbs2 ⊔ (Vbw2 ⊔ V2)) with ((Vbs2 ⊔ Vbw2) ⊔ V2) by solve_lat.
        replace (((map_fold view_join_total Vp2 sarc2 ⊔ (((ainfo.1.1.1.2 ⊔ V1) ⊔ V2) ⊔ (map_fold view_join_total Vp2 warc2 ⊔ V2))) ⊔ Vsf2) ⊔ Vm2)
          with ((((map_fold view_join_total Vp2 sarc2 ⊔ map_fold view_join_total Vp2 warc2) ⊔ Vsf2) ⊔ Vm2) ⊔ V2) by solve_lat. solve_lat.
      + solve_lat.
      + unfold SeenUpgrade. intros. destruct (decide (e0 = length E2)) as [->|NEQ].
        * rewrite lookup_app_1_eq in H2. inversion H2. subst eV0. done.
        * rewrite lookup_app_1_ne in H2; [|done]. apply SeenUpgrade2 in H2. destruct (eV0.(type)); try done.
          des; [by left|]. right. destruct (decide (e' = e)) as [->|NEQ'].
          -- exists e,ainfo2. rewrite lookup_insert_ne; [|done]. rewrite lookup_insert. split; [done|].
             rewrite Hwarc2e in H2. inversion H2. subst ainfo0. set_solver +H3.
          -- exists e',ainfo0. rewrite lookup_insert_ne; [|apply elem_of_dom_2, VALwarc2 in H2; lia].
             rewrite lookup_insert_ne; [|done]. rewrite lookup_delete_ne; [|done]. done.
      + unfold SeenDowngrade. intros. destruct (decide (e0 = length E2)) as [->|NEQ].
        * rewrite lookup_app_1_eq in H2. inversion H2. subst eV0. done.
        * rewrite lookup_app_1_ne in H2; [|done]. apply SeenDowngrade2 in H2. destruct (eV0.(type)); try done.
      + unfold ArcsSeen. intros. destruct (decide (e0 = opId)) as [->|NEQ].
        * rewrite lookup_insert in H2. inversion H2. subst ainfo0. apply LEwarc2 in Hwarc2e. solve_lat.
        * rewrite lookup_insert_ne in H2; [|done]. apply H1 in H2. done.
      + rewrite /StlistValid Forall_app Forall_cons. rewrite /StlistValid Forall_lookup in VALstlist2. split_and!.
        * rewrite Forall_lookup. intros. rewrite lookup_take_Some in H2. des. eapply VALstlist2; try done.
        * intros. simpl. eapply VALstlist2; try done. set_solver +H2.
        * rewrite Forall_lookup. intros. have [x' H2'] : is_Some (stlist2 !! (gen_of eidx1 + 1 + i)).
          { eapply interp_omo_length in Hgengood2 as Hlen. inversion Hlen.
            rewrite drop_length in H5. rewrite lookup_lt_is_Some. apply lookup_lt_Some in H2. lia. }
          specialize (Hstlist2' _ _ _ H2' H2). subst x. apply VALstlist2 in H2'; [|set_solver +H3]. done.
      + destruct (decide (nsf2 = 0)); [|done]. rewrite map_fold_insert_L; [rewrite H; solve_lat|solve_lat|].
        rewrite -not_elem_of_dom. eapply (dom_same _ _ _ ainfo2) in Hwarc2e as EQdom. rewrite -EQdom.
        unfold not. intros. apply VALwarc2 in H2. lia. }

  iModIntro. wp_pures. by iApply "HΦ".
Qed.

Lemma try_unwrap_full_spec :
  try_unwrap_full_spec' code.try_unwrap_full ArcInv StrongArc FakeArc.
Proof.
  intros N DISJ l l' tid γg q M e V0 P1 P2. iIntros "%PasFrac #⊒V0 SArc P1 l'↦" (Φ) "AU".
  iDestruct "SArc" as (??????????) "(%&%&%&%&%&%& #HN & #AInv & #⊒M & #⊒Ms & #⊒Mw & #e✓eV & #⊒ainfo & Hγb & e↪ainfo &
    (-> & %Hainfo2 & %eM & %eVEV & %SubainfoM & %SubainfoMw))".
  wp_lam. wp_bind (casᵃᶜ(_,_,_))%E.

  (* Inv access 1 *)
  iInv "AInv" as "H" "Hclose".
  iDestruct "H" as (?? γs1 ???????) "(%&%&%& %sarc1 & %warc1 & %qsa1 & %qwa1 & %alive1 & %E1 & %Es1 & %Ew1 & %omo1 & %omos1 &
    %omow1 & %stlist1 & %mos1 & %mow1 & %Mono1 & >HN' & >M●1 & >Ms●1 & >Mw●1 & >Hγsa1 & >Hγwa1 & >Hγb1 & >Hγm1 & Alive1)".
  gname_agree with "HN HN'". iClear "HN'".
  iDestruct (ghost_var_agree with "Hγb Hγb1") as %<-.

  iDestruct (OmoEview_update with "M●1 ⊒M ⊒Mw") as (Mw') "(M●1 & #⊒Mw' & M⊢Mw' & %SubMwMw')".
  iDestruct (OmoEview_update with "M●1 ⊒M ⊒Ms") as (Ms') "(M●1 & #⊒Ms' & M⊢Ms' & %SubMsMs')".
  iCombine "⊒V0 ⊒ainfo" as "⊒V0'". rewrite monPred_in_view_op. set V0' := V0 ⊔ ainfo.1.1.1.2.
  iCombine "⊒M ⊒Ms ⊒Mw ⊒ainfo ⊒Mw' P1" as "RES".
  iDestruct (view_at_intro_incl with "RES ⊒V0'") as (V0'')
    "(#⊒V0'' & %LeV0'V0'' & (#⊒M@V0'' & #⊒Ms@V0'' & #⊒Mw@V0'' & #⊒ainfo@V0'' & #⊒Mw'@V0'' & P1@V0''))".

  iDestruct "Alive1" as (Vbs1 Vbw1 ty1 uf1 stf1 esf1 ewf1 eVsf1 eVwf1 nsf1) "(%zwf1 & %Vsf1 & %Vwf1 & %Vp1 & %qsa1a & %qsa1b & %qu1 & %qd1 & %upds1 &
    %dgds1 & %lcks1 & %ulcks1 & >#AllEvents1 & >#AllStrongs1 & >#AllWeaks1 & >omos↦1 & >omow↦1 & >Hγu1 & >Hγd1 & >Hγl1 & >Hγul1 &
    >#AllLocks1 & [>#⊒upds1@Vwf1 >#⊒ulcks1@Vwf1] & >#esf1✓eVsf1 & >#ewf1✓eVwf1 & Hnsf1 & P2 & Hty1 & >#⊒stf1s@Vsf1 & >#⊒stf1w@Vwf1 & >Pures)".
  iDestruct "Pures" as %(Subuf1 & LASTesf1 & LASTewf1 & eVsf1EV & eVwf1EV & Hqsa1 & Hqwa1 & VALsarc1 & VALwarc1 & VALsarcwarc1 & SeenClone1 &
    SeenWeakClone1 & HInitWrite1 & LASTstf1 & DOMsarc1 & DOMwarc1 & EQqsa1 & Alive1 & VALeid1 & LeVbs1Vbw1 & GeVsf1 & GeVwf1 &
    SeenUpgrade1 & SeenDowngrade1 & SeenUnlock1 & LEsarc1 & LEwarc1 & VALstlist1 & LeVsf1 & EQnsf1).
  iDestruct (OmoAuth_wf with "M●1") as %[OMO_GOOD1 _].
  iDestruct (OmoSnapOmo_get with "Ms●1") as "#Ms◯1".
  iDestruct (OmoAuth_wf with "Ms●1") as %[OMO_GOODs1 _].
  iDestruct (OmoAuth_omo_nonempty with "Ms●1") as %Nomos1.
  eapply omo_stlist_length in OMO_GOOD1 as EQlenST1.
  iMod (rel_objectively_intro (⊒∅) tid with "[]") as "#⊒∅"; [by iApply objective_objectively; iApply monPred_in_bot|].

  wp_apply (append_only_loc_cas_only_cas with "[$Ms●1 $⊒Ms' $omos↦1 $⊒V0'']"); try done; [solve_ndisj|].
  iIntros (b1 es1 gens1 vs1 Vs1 V1 mos1' omos1' eVs1 eVsn1)
    "(Pures & #MAXes1 & #es1✓eVs1 & #esn1✓eVsn1 & Ms●1 & #⊒V1 & #⊒Ms1@V1 & omos↦1 & CASE)".
  iDestruct "Pures" as %(Eqgens1 & eVs1EV & LeV0''V1).
  iDestruct "CASE" as "[(Pures & _ & #es1=esn1 & RCOMMIT) | [Pures sVs1]]".
  { (* CAS failed, commit [UnwrapFail] event *)
    iDestruct "Pures" as %(-> & NEQvs1 & -> & Homos1' & eVsn1EV & eVsn1SYNC).

    set ainfo' := (ainfo.1.1.1.1, ainfo.1.1.1.2 ⊔ V1, ainfo.1.1.2, ainfo.1.2, cas_only).
    set sarc1' := <[e := ainfo']> (delete e sarc1).
    iDestruct (ghost_map_lookup with "Hγsa1 e↪ainfo") as %Hsarc1e.
    iMod (ghost_map_delete with "Hγsa1 e↪ainfo") as "Hγsa1".
    iMod (ghost_map_insert e ainfo' with "Hγsa1") as "[Hγsa1 e↪ainfo]"; [by apply lookup_delete|].

    have LeV0V1 : V0 ⊑ V1 by solve_lat.
    set opId := length E1.
    set M1 : eView := {[opId]} ∪ M.
    set eVop := mkOmoEvent (UnwrapFail e) V1 M1.

    (* Commit position: largest generation
        among events in current eView and corresponding event of the strong count that we've just read *)
    iDestruct (big_sepL_lookup with "AllStrongs1") as (e1 st1 eVs1')
      "(e1↦es1 & e1⊒es1 & e1↪st1 & es1✓eVs1' & MONO✓e1 & %eVs1'EV & Hgens1)"; [exact Eqgens1|].
    iDestruct (OmoEinfo_agree with "es1✓eVs1 es1✓eVs1'") as %<-.
    rewrite eVs1EV /= in eVs1'EV. inversion eVs1'EV. subst vs1.
    iDestruct (OmoAuth_OmoCW_l' with "M●1 e1↦es1") as %[eidx1 Heidx1].
    set gen1 := gen_of eidx1. (* candidate #1 *)

    iDestruct (OmoEview_latest_elem with "⊒M") as (e2) "[MAXe2 %e2IN]".
    iDestruct (OmoAuth_OmoEview with "M●1 ⊒M") as %VALM.
    apply VALM in e2IN as He2. eapply lookup_omo_surjective in He2 as Heidx2; [|done].
    destruct Heidx2 as [eidx2 Heidx2].
    set gen2 := gen_of eidx2. (* candidate #2 *)

    set gen := gen1 `max` gen2.
    have LEgen1gen : gen1 ≤ gen by lia.
    iAssert (⌜ size st1.1.1.1 ≠ 0 ⌝ ∗ ((⌜ gens1 = length omos1 - 1 ⌝) ∨ (∃ e1' es1' eidx1', OmoCW γg γes e1' es1' ∗
      ⌜ omo_write_op omos1 !! (gens1 + 1)%nat = Some es1' ∧ lookup_omo omo1 eidx1' = Some e1' ∧ gen < gen_of eidx1' ⌝)))%I with "[-]" as "[%NZst1 #UBgen]".
    { destruct (decide (gens1 = length omos1 - 1)) as [->|NEQ].
      { iSplit; [|by iLeft]. iIntros "%Zsz".
        replace (length omos1 - 1) with (Init.Nat.pred (length omos1)) in Eqgens1 by lia.
        rewrite omo_write_op_length -last_lookup LASTesf1 in Eqgens1. inversion Eqgens1. subst es1.
        iDestruct (OmoEinfo_agree with "esf1✓eVsf1 es1✓eVs1") as %<-.
        rewrite eVsf1EV in eVs1EV. inversion eVs1EV. subst nsf1 Vs1. rewrite Zsz in H0.
        have SZstf1 : size stf1.1.1.1 = 0 by lia.
        apply size_empty_inv in SZstf1. fold_leibniz. rewrite SZstf1 in DOMsarc1.
        apply elem_of_dom_2 in Hsarc1e. rewrite DOMsarc1 in Hsarc1e. done. }

      have [es1' Hes1'] : is_Some (omo_write_op omos1 !! (gens1 + 1)%nat).
      { rewrite lookup_lt_is_Some. apply lookup_lt_Some in Eqgens1. rewrite omo_write_op_length in NEQ. lia. }
      iDestruct (big_sepL_lookup with "AllStrongs1") as (e1' st1' eVs1')
        "(e1'↦es1' & e1'⊒es1' & e1'↪st1' & es1'✓eVs1' & MONO✓e1' & %eVs1'EV' & Hgens1')"; [exact Hes1'|].
      replace (gens1 + 1) with (S gens1) by lia.
      iDestruct "Hgens1'" as (omos1'' e1'' es1'' eV1' eVs1'' st1'')
        "(Ms◯1' & e1''↦es1'' & e1'✓eV1' & es1''✓eVs1'' & e1''↪st1'' & _ & (%Hes1'' & %eVs1''EV & %NZst1'' & %CASE))".
      iDestruct (OmoAuth_OmoSnapOmo with "Ms●1 Ms◯1'") as %PREFIXomos1.
      replace (S gens1 - 1) with gens1 in Hes1'' by lia.
      rewrite -lookup_omo_wr_event in Hes1''.
      eapply omo_prefix_lookup_Some in Hes1''; [|exact PREFIXomos1].
      rewrite lookup_omo_wr_event Homos1' omo_insert_r_write_op Eqgens1 in Hes1''. inversion Hes1''. subst es1''.
      iDestruct (OmoCW_agree_2 with "e1↦es1 e1''↦es1''") as %[_ <-].
      iDestruct (OmoSnap_agree with "e1↪st1 e1''↪st1''") as %<-. iSplit; [done|]. iRight.

      iDestruct (OmoAuth_OmoCW_l' with "M●1 e1'↦es1'") as %[eidx1' Heidx1'].
      iDestruct (OmoLe_get _ _ _ _ _ _ (wr_event gens1) (wr_event (gens1 + 1)) with "Ms●1") as "#es1≤es1'".
      { by rewrite lookup_omo_wr_event Homos1' omo_insert_r_write_op. }
      { by rewrite lookup_omo_wr_event Homos1' omo_insert_r_write_op. } { simpl. lia. }
      iDestruct (CWMono_acc with "Hγm1 MONO✓e1 MONO✓e1' e1↦es1 e1'↦es1' es1≤es1'") as "#e1≤e1'".
      iDestruct (OmoLe_Le with "M●1 e1≤e1'") as %LEgen; [done|done|].

      destruct (decide (gen_of eidx1 = gen_of eidx1')) as [EQgen|NEQgen].
      { (* Contradiction. Generations of two events of adjacent strong count messages cannot be the same *)
        iDestruct (OmoEq_get with "M●1") as "#e1=e1'"; [exact Heidx1|exact Heidx1'|done|].
        iDestruct (OmoSnap_agree' with "e1↪st1 e1'↪st1' e1=e1'") as %<-. destruct CASE as [[EQ _]|[EQ _]]; lia. }
      have LTgen : gen_of eidx1 < gen_of eidx1' by lia.

      destruct (le_lt_dec gen2 gen1) as [LEgen21|LTgen12].
      { iExists e1',es1',eidx1'. iFrame "e1'↦es1'".
        iPureIntro. replace (S gens1) with (gens1 + 1) by lia. split_and!; try done. lia. }

      iAssert ( (∃ es2, OmoCW γg γes e2 es2 ∗ OmoHb γg γes e2 es2 ∗ CWMonoValid γm e2)
              ∨ SeenPrevStrong γg γes (omo_write_op omos1) e2)%I with "[-]" as "#CASE".
      { destruct He2 as [eV2 HeV2]. iDestruct (big_sepL_lookup with "AllEvents1") as "Inner"; [exact HeV2|].
        destruct (eV2.(type)); try (by iLeft); try (by iRight). }
      iDestruct "CASE" as "[(%es2 & e2↦es2 & e2⊒es2 & MONO✓e2)|He2]".
      - iDestruct (OmoHb_HbIncluded with "e2⊒es2 M⊢Ms'") as %es2Ms'; [done|].
        iDestruct (big_sepS_elem_of with "MAXes1") as "es2≤es1"; [exact es2Ms'|].
        iDestruct (CWMono_acc with "Hγm1 MONO✓e2 MONO✓e1 e2↦es2 e1↦es1 es2≤es1") as "#e2≤e1".
        iDestruct (OmoLe_Le with "M●1 e2≤e1") as %LE; [done|done|]. lia.
      - iDestruct "He2" as "[(%ef1 & %esf1' & %esf1eq & ef1≤e2 & esf1=esf1eq & ef1↦esf1 & e2⊒esf1eq & %LASTesf1')|
          (%el1 & %er1 & %esl1 & %esl1eq & %esr1 & %gensl1 & el1≤e2 & e2<er1 & esl1=esl1eq & el1↦esl1 & er1↦esr1 & e2⊒esl1eq & [%Hesl1 %Hesr1])]".
        + rewrite LASTesf1 in LASTesf1'. inversion LASTesf1'. subst esf1'. clear LASTesf1'.
          rewrite last_lookup -omo_write_op_length in LASTesf1.
          replace (Init.Nat.pred (length omos1)) with (length omos1 - 1) in LASTesf1 by lia.
          iDestruct (OmoHb_HbIncluded with "e2⊒esf1eq M⊢Ms'") as %esf1eqMs'; [done|].
          iDestruct (big_sepS_elem_of with "MAXes1") as "esf1eq≤es1"; [exact esf1eqMs'|].
          iDestruct (OmoEq_Le_trans with "esf1=esf1eq esf1eq≤es1") as "esf1≤es1".
          iDestruct (OmoLe_Le _ _ _ _ _ _ (wr_event (length omos1 - 1)) (wr_event gens1) with "Ms●1 esf1≤es1") as %LE;
          try (by rewrite lookup_omo_wr_event Homos1' omo_insert_r_write_op).
          simpl in LE. apply lookup_lt_Some in Eqgens1. rewrite -omo_write_op_length in Eqgens1. lia.
        + destruct (le_lt_dec gensl1 gens1) as [LE|LT].
          * iDestruct (OmoLe_get _ _ _ _ _ _ (wr_event (gensl1 + 1)) (wr_event (gens1 + 1)) with "Ms●1") as "#esr1≤es1'";
            try (by rewrite lookup_omo_wr_event Homos1' omo_insert_r_write_op); [simpl; lia|].
            iDestruct (big_sepL_lookup with "AllStrongs1") as (er1' str1 eVsr1) "(er1'↦esr1 & _ & _ & _ & MONO✓er1 & _)"; [exact Hesr1|].
            iDestruct (OmoCW_agree_2 with "er1↦esr1 er1'↦esr1") as %[_ <-].
            iDestruct (CWMono_acc with "Hγm1 MONO✓er1 MONO✓e1' er1↦esr1 e1'↦es1' esr1≤es1'") as "#er1≤e1'".
            iDestruct (OmoLt_Le_trans with "e2<er1 er1≤e1'") as "e2<e1'".
            iDestruct (OmoLt_Lt with "M●1 e2<e1'") as %LT; [done|done|].
            iExists e1',es1',eidx1'. iFrame "e1'↦es1'". iPureIntro. replace (S gens1) with (gens1 + 1) by lia. split_and!; try done. lia.
          * iDestruct (OmoHb_HbIncluded with "e2⊒esl1eq M⊢Ms'") as %esl1eqMs'; [done|].
            iDestruct (big_sepS_elem_of with "MAXes1") as "esl1eq≤es1"; [exact esl1eqMs'|].
            iDestruct (OmoEq_Le_trans with "esl1=esl1eq esl1eq≤es1") as "esl1≤es1".
            iDestruct (OmoLe_Le _ _ _ _ _ _ (wr_event gensl1) (wr_event gens1) with "Ms●1 esl1≤es1") as %LE;
            try (by rewrite lookup_omo_wr_event Homos1' omo_insert_r_write_op). simpl in LE. lia. }

    iDestruct (OmoAuth_OmoEinfo with "M●1 e✓eV") as %HeV.
    iDestruct (OmoAuth_OmoEinfo' with "M●1 e✓eV") as %[eidx Heidx].
    have eINdom : e ∈ dom sarc1 by apply elem_of_dom_2 in Hsarc1e.
    specialize (strong_arc_persist e eidx eV _ _ _ _ _ OMO_GOOD1 Heidx HeV eVEV eINdom VALsarcwarc1) as Hstlist1.

    iAssert (⌜ gen_of eidx ≤ gen1 ⌝)%I with "[-]" as %LEgene1.
    { iDestruct (big_sepL_lookup with "AllEvents1") as "Inner"; [exact HeV|]. des;
      rewrite eVEV; iDestruct "Inner" as (es) "(e↦es & e⊒es & MONO✓e)";
      (iDestruct (OmoHb_HbIncluded with "e⊒es M⊢Ms'") as %esMs'; [done|]);
      (iDestruct (big_sepS_elem_of with "MAXes1") as "es≤es1"; [exact esMs'|]);
      iDestruct (CWMono_acc with "Hγm1 MONO✓e MONO✓e1 e↦es e1↦es1 es≤es1") as "#e≤e1";
      iDestruct (OmoLe_Le with "M●1 e≤e1") as %LE; done. }

    iDestruct (OmoAuth_OmoSnap with "M●1 e1↪st1") as %Hst1; [done|].
    eapply Hstlist1 in Hst1 as eINst1; [|done].
    have SSub : {[e]} ⊂ st1.1.1.1.
    { have Sub : {[e]} ⊆ st1.1.1.1 by clear -eINst1; set_solver.
      destruct (decide (st1.1.1.1 = {[e]})) as [EQ|NEQ]; [|set_solver +Sub NEQ].
      apply (f_equal size) in EQ. rewrite size_singleton in EQ. rewrite EQ in NEQvs1. inversion NEQvs1. lia. }

    iAssert (∀ i st, ⌜ stlist1 !! i = Some st → gen_of eidx1 ≤ i → i ≤ gen → st1.1.1.1 = st.1.1.1 ⌝)%I with "[M●1 Ms●1 Hγm1]" as %EQst1.
    { iIntros (i st) "%Hst %LE1 %LE2". iInduction LE1 as [|i] "IH" forall (st LE2 Hst).
      - rewrite Hst1 in Hst. inversion Hst. subst st. done.
      - have [st' Hst'] : is_Some (stlist1 !! i) by rewrite lookup_lt_is_Some; apply lookup_lt_Some in Hst; lia.
        iDestruct ("IH" $! st' with "[] [] M●1 Ms●1 Hγm1") as %EQst1st'; [iPureIntro; lia|done|].
        have [e' He'] : is_Some (omo_write_op omo1 !! (i + 1)%nat).
        { apply lookup_lt_is_Some. rewrite -omo_write_op_length EQlenST1. apply lookup_lt_Some in Hst. lia. }
        replace (S i) with (i + 1) in Hst by lia. rewrite -lookup_omo_wr_event in He'.
        eapply lookup_omo_event_valid in He' as HeV'; [|done]. destruct HeV' as [eV' HeV'].
        eapply omo_write_op_step in OMO_GOOD1 as STEP; try done.

        iAssert (⌜ st1.1.1.1 = st.1.1.1 ⌝ ∨
          (∃ es', OmoCW γg γes e' es' ∗ OmoHb γg γes e' es' ∗ CWMonoValid γm e'))%I with "[]" as "#CASE".
        { inversion STEP; try (iLeft; iPureIntro; subst st; rewrite EQst1st'; done);
          (iDestruct (big_sepL_lookup with "AllEvents1") as "Inner"; [exact HeV'|]);
          rewrite EVENT; iRight; subst; iFrame "Inner". }
        iDestruct "CASE" as "[%|(%es' & e'↦es' & e'⊒es' & MONO✓e')]"; [done|].

        iDestruct (OmoAuth_OmoCW_r' with "Ms●1 e'↦es'") as %[seidx' Hseidx'].
        destruct (le_lt_dec (gen_of seidx') gens1) as [LE|LT].
        { (* Contradicting case *)
          iDestruct (OmoLe_get _ _ _ _ _ _ seidx' (wr_event gens1) with "Ms●1") as "#es'≤es1".
          { done. } { by rewrite lookup_omo_wr_event Homos1' omo_insert_r_write_op. } { simpl. done. }
          iDestruct (CWMono_acc with "Hγm1 MONO✓e' MONO✓e1 e'↦es' e1↦es1 es'≤es1") as "#e'≤e1".
          iDestruct (OmoLe_Le with "M●1 e'≤e1") as %LE'; [done|done|]. simpl in LE'. lia. }

        iDestruct "UBgen" as "[%|(%er1 & %esr1 & %eidxr1 & er1↦esr1 & (%Hesr1 & %Her1 & %LT'))]".
        { apply lookup_omo_lt_Some in Hseidx'. rewrite Homos1' omo_insert_r_length in Hseidx'. lia. }

        iDestruct (big_sepL_lookup with "AllStrongs1")
          as (er1' str1 eVsr1) "(er1'↦esr1 & _ & _ & _ & MONO✓er1 & _)"; [exact Hesr1|].
        iDestruct (OmoCW_agree_2 with "er1↦esr1 er1'↦esr1") as %[_ <-].
        iDestruct (OmoLe_get _ _ _ _ _ _ (wr_event (gens1 + 1)) seidx' with "Ms●1") as "#esr1≤es'".
        { by rewrite lookup_omo_wr_event Homos1' omo_insert_r_write_op. } { done. } { simpl. lia. }
        iDestruct (CWMono_acc with "Hγm1 MONO✓er1 MONO✓e' er1↦esr1 e'↦es' esr1≤es'") as "#er1≤e'".
        iDestruct (OmoLe_Le with "M●1 er1≤e'") as %LE; [done|done|]. simpl in *. lia. }

    have [st Hst] : is_Some (stlist1 !! gen).
    { rewrite lookup_lt_is_Some -EQlenST1. apply lookup_omo_lt_Some in Heidx1, Heidx2. lia. }
    eapply EQst1 in Hst as EQst1st; [|done|done]. rewrite EQst1st in SSub.

    iMod "AU" as (????) "[>M●1' [_ Commit]]".
    iDestruct (OmoAuth_agree with "M●1 M●1'") as %(<- & <- & <- & <-). iCombine "M●1 M●1'" as "M●1".
    iDestruct (view_at_mono_2 _ V1 with "⊒M@V0''") as "⊒M@V1"; [solve_lat|].
    iDestruct (OmoUB_into_gen with "M●1 MAXe2") as %MAXe2; [done|].
    apply (OmoUBgen_mono _ _ _ gen) in MAXe2 as MAXgen; [|lia].
    iMod (OmoAuth_insert_ro_gen with "M●1 ⊒M@V1 RCOMMIT []")
      as "(M●1 & #⊒M1@V1 & #opId↦esn1 & #opId↪st & #opId✓eVop & RCOMMIT)".
    { have ? : step opId eVop st st; [|done]. eapply arc_step_UnwrapFail; try done; set_solver-. }
    iMod (OmoHb_new_2 _ _ _ _ _ _ _ _ (length Es1) ({[length Es1]} ∪ Ms') with "M●1 [] opId✓eVop") as "[M●1 #opId⊒esn1]".
    { set_solver-. } { iFrame "⊒Ms1@V1". }
    iDestruct (OmoHbToken_finish with "M●1") as "[M●1 M●1']".

    iAssert (OmoLe γg e1 opId)%I with "[-]" as "#e1≤opId".
    { have [egen Hegen] : is_Some (omo_read_op omo1 !! gen).
      { rewrite lookup_lt_is_Some -omo_read_op_length. apply lookup_omo_lt_Some in Heidx1, Heidx2. lia. }
      iApply (OmoLe_get _ _ _ _ _ _ eidx1 (ro_event gen (length egen)) with "M●1"); [..|simpl;lia].
      - eapply (lookup_omo_before_insert_r _ eidx1 _ _ (length E1)) in Hegen as Heidx1'. rewrite Heidx1'.
        rewrite decide_False; [done|]. unfold not. intros. rewrite H in Heidx1.
        rewrite lookup_omo_ro_event Hegen /= in Heidx1. apply lookup_lt_Some in Heidx1. lia.
      - rewrite lookup_omo_ro_event omo_insert_r_read_op. rewrite list_lookup_alter Hegen /= lookup_app_1_eq. done. }

    iAssert (⌜ gens1 = length omos1 - 1 ⌝ ∨ (∃ (e1' es1' : event_id), OmoCW γg γes e1' es1' ∗ OmoLt γg opId e1' ∗
        ⌜omo_write_op omos1 !! (gens1 + 1)%nat = Some es1'⌝))%I with "[-]" as "#UBopId".
    { iDestruct "UBgen" as "[%Hgens1|(%e1' & %es1' & %eidx1' & e1'↦es1' & (%Hes1' & %Heidx1' & %LTeidx1'))]"; [by iLeft|].
      have [egen Hegen] : is_Some (omo_read_op omo1 !! gen).
      { rewrite lookup_lt_is_Some -omo_read_op_length. apply lookup_omo_lt_Some in Heidx1, Heidx2. lia. }
      iDestruct (OmoLt_get _ _ _ _ _ _ (ro_event gen (length egen)) eidx1' with "M●1") as "#opId<e1'".
      { rewrite lookup_omo_ro_event omo_insert_r_read_op list_lookup_alter Hegen /= lookup_app_1_eq. done. }
      { eapply (lookup_omo_before_insert_r _ eidx1' _ _ (length E1)) in Hegen as Heidx1''. rewrite Heidx1''.
        rewrite decide_False; [done|]. unfold not. intros. rewrite H lookup_omo_ro_event Hegen /= in Heidx1'.
        apply lookup_lt_Some in Heidx1'. lia. } { done. }
      iRight. iExists e1',es1'. iFrame "e1'↦es1' opId<e1'". done. }

    iMod ("Commit" $! false V1 _ _ _ M1 with "[$⊒V1 $M●1' $⊒M1@V1 $RCOMMIT Hγb e↪ainfo $P1@V0'']") as "HΦ".
    { iSplitR; [iPureIntro; split_and!; try done; set_solver-|]. iSplitL.
      - repeat iExists _. iFrame "HN AInv e↪ainfo ⊒Ms@V0'' ⊒Mw@V0'' e✓eV". subst ainfo'. simpl. iFrame "Hγb". iSplit.
        + iApply view_at_unfold. rewrite monPred_at_in. iPureIntro. clear -LeV0'V0'' LeV0''V1. solve_lat.
        + iPureIntro. split_and!; try done; clear -eM SubainfoM; set_solver.
      - iPureIntro. split_and!; try done. exists gen. split; [done|]. apply lookup_omo_lt_Some in Heidx1, Heidx2. lia. }

    iMod ("Hclose" with "[-l'↦ HΦ]") as "_".
    { iNext. repeat iExists _. iFrame "HN M●1 Ms●1 Mw●1 Hγwa1 Hγsa1 Hγb1 Hγm1". rewrite Homos1' omo_insert_r_write_op.
      repeat iExists _. iFrame "AllStrongs1 AllWeaks1 omos↦1 omow↦1 Hγu1 Hγd1 Hγl1 Hγul1 Hnsf1 P2 ⊒upds1@Vwf1 ⊒ulcks1@Vwf1
        esf1✓eVsf1 ewf1✓eVwf1 ⊒stf1s@Vsf1 ⊒stf1w@Vwf1". iSplitR; last iSplitR; last iSplitL.
      - iApply big_sepL_snoc. iFrame "AllEvents1". simpl.
        iDestruct "UBopId" as "[%Hgens1|(%e1' & %es1' & e1'↦es1' & opId<e1' & %Hes1')]".
        + iLeft. iExists e1,es1,(length Es1). iFrame "e1≤opId es1=esn1 e1↦es1 opId⊒esn1".
          rewrite Hgens1 in Eqgens1. replace (length omos1 - 1) with (Init.Nat.pred (length omos1)) in Eqgens1 by lia.
          rewrite omo_write_op_length -last_lookup in Eqgens1. done.
        + iRight. iExists e1,e1',es1,(length Es1),es1',gens1. iFrame "e1≤opId opId<e1' es1=esn1 e1↦es1 e1'↦es1' opId⊒esn1". done.
      - iApply big_sepL_forall. iIntros (i ew) "%Hew".
        iDestruct (big_sepL_lookup with "AllLocks1") as (eVw z) "[ew✓eVw [%eVwEV %COND]]"; [exact Hew|].
        iExists eVw,z. iFrame "ew✓eVw". iPureIntro. split; [done|].
        intros. apply COND in H. destruct H as [H|H]; [by left|].
        destruct H as (e' & ainfo'' & He' & e'IN). right. destruct (decide (e' = e)) as [->|NEQ].
        + rewrite Hsarc1e in He'. inversion He'. subst ainfo''.
          exists e,ainfo'. rewrite lookup_insert. split; [done|]. clear -e'IN. set_solver.
        + exists e',ainfo''. rewrite lookup_insert_ne; [|done]. rewrite lookup_delete_ne; [|done]. done.
      - iApply (append_only_type_condition_update with "Hty1"); try done.
      - iPureIntro. eapply (sarc_update_snoc_1 _ _ _ ainfo' _ _ eVop) in Hsarc1e as H; try done; [|solve_lat].
        eapply (sarc_update_snoc_2 _ _ _ ainfo' _ _ _ eVop) in Hsarc1e as H0; try done. clear eVEV. des. split_and!; try done.
        + by rewrite omo_insert_r_write_op.
        + by rewrite /ArcAlive Forall_app Forall_singleton.
        + apply EventIdValid_update; [done|]. simpl. apply VALM in eM. rewrite lookup_lt_is_Some in eM. done.
        + rewrite H0. replace ((Vbs1 ⊔ V1) ⊔ Vbw1) with ((Vbs1 ⊔ Vbw1) ⊔ V1) by solve_lat.
          clear -LeVbs1Vbw1. solve_lat. }

    iModIntro. wp_pures. iDestruct "l'↦" as (?) "l'↦". wp_write. iApply "HΦ". iExists 2. iFrame "l'↦". done. }

  (* CAS success, commit [StrongDrop] event *)
  iDestruct "Pures" as %(-> & -> & ->).
  iDestruct "sVs1" as (Vm1) "((%Hmos1' & -> & %eVsn1EV & %eVsn1SYNC & %LeVs1Vm1 & %NEqVs1Vm1 & %NLeV1Vs1 &
    %NEqV0''V1 & _) & _ & %LeVm1V1 & WCOMMIT)".

  set sarc1' := delete e sarc1.
  iDestruct (ghost_map_lookup with "Hγsa1 e↪ainfo") as %Hsarc1e.
  iMod (ghost_map_delete with "Hγsa1 e↪ainfo") as "Hγsa1".

  replace (length omos1 - 1) with (Init.Nat.pred (length omos1)) in Eqgens1 by lia.
  rewrite omo_write_op_length -last_lookup LASTesf1 in Eqgens1. inversion Eqgens1. subst es1. clear Eqgens1.
  iDestruct (OmoEinfo_agree with "esf1✓eVsf1 es1✓eVs1") as %<-.
  rewrite eVsf1EV in eVs1EV. inversion eVs1EV. subst nsf1 Vs1. rewrite H0.
  have SZstf1 : size stf1.1.1.1 = 1 by lia. clear H0.
  have EQstf1 : stf1.1.1.1 = {[e]}.
  { apply size_1_elem_of in SZstf1 as [x EQstf1]. fold_leibniz.
    apply elem_of_dom_2 in Hsarc1e. rewrite DOMsarc1 EQstf1 elem_of_singleton in Hsarc1e. subst x. done. }
  have EQsarc1' : sarc1' = ∅.
  { apply map_size_empty_inv. apply (f_equal size) in DOMsarc1. rewrite SZstf1 size_dom in DOMsarc1.
    rewrite map_size_delete Hsarc1e DOMsarc1. done. }

  rewrite SZstf1. iDestruct "Hnsf1" as "(P1@Vp1 & (P1@Vsf1 & #⊒dgds1@Vsf1 & #⊒lcks1@Vsf1) & #He0 & e0↪ainfo & Hγb' & Hγul & ->)".
  (* FIXME: The following replaces ((1 / 2)%Qp, Vp1, ∅, ∅, cas_only) into ainfo1, which is incorrect. *)
  (* set ainfo1 := ((1/2)%Qp, ainfo.1.1.1.2 ⊔ V1, ∅, ∅, cas_only). *)
  have [ainfo1 Hainfo1] : ∃ (ainfo1 : ainfo_type), ainfo1 = ((1/2)%Qp, ainfo.1.1.1.2 ⊔ V1, ∅, ∅, cas_only) by eexists.
  set warc1' := <[0:=ainfo1]> (delete 0 warc1).
  set dgds1' := dgds1 ∪ M.
  set lcks1' := lcks1 ∪ Mw.
  iDestruct (ghost_map_lookup with "Hγwa1 e0↪ainfo") as %Hwarc1e0.
  iMod (ghost_map_delete with "Hγwa1 e0↪ainfo") as "Hγwa1".
  iMod (ghost_map_insert 0 ainfo1 with "Hγwa1") as "[Hγwa1 e0↪ainfo1]"; [by rewrite lookup_delete|].
  iMod (ghost_var_update dgds1' with "Hγd1") as "[Hγd1 Hγd1']".
  iMod (ghost_var_update lcks1' with "Hγl1") as "[Hγl1 Hγl1']".

  rewrite EQstf1 in DOMsarc1. apply dom_singleton_inv_L in DOMsarc1 as [x EQsarc1].
  rewrite EQsarc1 lookup_singleton in Hsarc1e. inversion Hsarc1e. subst x.
  rewrite EQsarc1 map_fold_singleton_frac_sum /frac_sum /= in Hqsa1.

  iDestruct (view_at_mono_2 _ V1 with "⊒stf1s@Vsf1") as "⊒stf1s@V1"; [solve_lat|].
  iDestruct (view_at_mono_2 _ V1 with "⊒dgds1@Vsf1") as "⊒dgds1@V1"; [solve_lat|].
  iDestruct (view_at_mono_2 _ V1 with "⊒M@V0''") as "⊒M@V1"; [solve_lat|].
  iDestruct (OmoEview_union_obj with "⊒M@V1 ⊒dgds1@V1") as "⊒dgds1'@V1".
  iDestruct (OmoEview_union_obj with "⊒dgds1'@V1 ⊒stf1s@V1") as "⊒M1@V1".
  iDestruct (OmoAuth_OmoEview with "M●1 ⊒M") as %VALM.

  have LeV0V1 : V0 ⊑ V1 by clear -LeV0'V0'' LeV0''V1; solve_lat.
  set opId := length E1.
  (* FIXME: Below command goes wrong *)
  (* set M1 : eView := {[opId]} ∪ (M ∪ stf1.1.2 ∪ dgds1). *)
  have [M1 HM1] : ∃ (M1 : eView), M1 = {[opId]} ∪ (M ∪ dgds1 ∪ stf1.1.2) by eexists.
  set eVop := mkOmoEvent (StrongDrop e true) V1 M1.
  set stnf1 : arc_state := ((∅, stf1.1.1.2, stf1.1.2), stf1.2).

  iMod "AU" as (????) "[>M●1' [_ Commit]]".
  iDestruct (OmoAuth_agree with "M●1 M●1'") as %(<- & <- & <- & <-). iCombine "M●1 M●1'" as "M●1".
  iMod (OmoAuth_insert_last with "M●1 ⊒M1@V1 WCOMMIT []") as
    "(M●1 & #⊒M1'@V1 & #opId↦esn1 & #opId✓eVop & #opId↪stnf1 & WCOMMIT)".
  { have ? : step opId eVop stf1 stnf1; [|done]. eapply arc_step_StrongDrop_last; try done; [|solve_lat].
    subst eVop M1. simpl. set_solver-. }
  iMod (OmoHb_new_2 _ _ _ _ _ _ _ _ (length Es1) ({[length Es1]} ∪ Ms') with "M●1 [] opId✓eVop")
    as "[M●1 #opId⊒esn1]"; [set_solver-|iFrame "⊒Ms1@V1"|].
  iDestruct (OmoHbToken_finish with "M●1") as "[M●1 M●1']".

  iMod (CWMono_insert_last_last (wr_event (length omo1)) with "Hγm1 M●1 Ms●1 opId↦esn1")
    as "(Hγm1 & #MONO✓opId & M●1 & Ms●1)".
  { by rewrite lookup_omo_wr_event omo_append_w_write_op omo_write_op_length lookup_app_1_eq. }
  { by rewrite omo_append_w_length /= Nat.add_sub. }

  iAssert (AllStrongsInner γg γes γs1 γss γm (length (omo_write_op omos1)) (length Es1))%I with "[-]" as "#NewStrongInner".
  { iExists opId,stnf1,eVsn1. subst stnf1. rewrite eVsn1EV size_empty.
    iFrame "opId↦esn1 opId⊒esn1 opId↪stnf1 esn1✓eVsn1 MONO✓opId". iSplit; [done|].
    rewrite -omo_write_op_length. destruct (length omos1) eqn:Hlen; [done|]. rewrite -Hlen. clear Hlen n.
    rewrite last_lookup -omo_write_op_length in LASTesf1.
    replace (Init.Nat.pred (length omos1)) with (length omos1 - 1) in LASTesf1 by lia.
    iDestruct (big_sepL_lookup with "AllStrongs1") as (ef1 stf1' eVsf1')
      "(ef1↦esf1 & _ & ef1↪stf1' & esf1✓eVsf1' & _ & %eVsf1'EV & _)"; [exact LASTesf1|].
    iDestruct (OmoEinfo_agree with "esf1✓eVsf1 esf1✓eVsf1'") as %<-.
    rewrite eVsf1EV /= in eVsf1'EV. inversion eVsf1'EV.
    have EQsz : size stf1.1.1.1 = size stf1'.1.1.1 by lia. clear H0.

    iDestruct (OmoAuth_OmoCW_l with "M●1 ef1↦esf1") as %[eVf1 HeVf1].
    iDestruct (OmoEinfo_get with "M●1") as "#ef1✓eVf1"; [exact HeVf1|].
    iAssert (⌜ opId ≠ ef1 ⌝)%I with "[-]" as %NEQef1.
    { iIntros "%EQef1". subst ef1. iDestruct (OmoCW_agree_1 with "opId↦esn1 ef1↦esf1") as %[_ <-].
      rewrite -lookup_omo_wr_event in LASTesf1. eapply lookup_omo_event_valid in LASTesf1; [|done].
      rewrite lookup_lt_is_Some in LASTesf1. lia. }
    iDestruct (OmoLt_get_append_w with "M●1 ef1✓eVf1") as "#ef1<opId"; [done|].

    iExists omos1,ef1,esf1,eVop,eVsf1,stf1'. iFrame "Ms◯1 ef1↦esf1 opId✓eVop esf1✓eVsf1 ef1↪stf1' ef1<opId".
    iPureIntro. split_and!; try done; [by rewrite eVsf1EV EQsz|by rewrite -EQsz EQstf1 size_singleton|].
    right. rewrite -EQsz EQstf1 size_singleton. split; [lia|]. exists e,true. done. }

  iDestruct (AllEvents_after_strong_write_event with "AllEvents1 M●1 opId↦esn1 opId⊒esn1 MONO✓opId") as "#AllEvents1'"; [by destruct omos1|done|].

  (* Collect P1 into full ownership *)
  have LeVp1ainfo : Vp1 ⊑ ainfo.1.1.1.2 by apply (LEsarc1 e); rewrite EQsarc1 lookup_singleton.
  iAssert (@{V1} P1 1%Qp)%I with "[P1@Vp1 P1@Vsf1 P1@V0'']" as "P1@V1".
  { iDestruct (view_at_mono_2 _ V1 with "P1@Vp1") as "P1@V1".
    { clear -LeVp1ainfo LeV0'V0'' LeV0''V1. solve_lat. }
    iDestruct (view_at_mono_2 _ V1 with "P1@Vsf1") as "P1@V1'"; [solve_lat|].
    iDestruct (view_at_mono_2 _ V1 with "P1@V0''") as "P1@V1''"; [done|].
    iCombine "P1@V1 P1@V1' P1@V1''" as "P1". rewrite Qp.add_assoc -EQqsa1 Qp.add_comm Hqsa1. done. }

  iCombine "Hγb Hγb1" as "Hγb1".
  replace (ainfo.1.1.1.1/2 + (qsa1/2 + qwa1/2))%Qp with (1/2 + qwa1/2)%Qp; [|by rewrite -Hqsa1 Qp.div_add_distr Qp.add_assoc].

  iMod ("Commit" $! true V1 _ _ _ M1 with "[$⊒V1 $M●1' $P1@V1 $WCOMMIT]") as "HΦ".
  { subst M1. iFrame "⊒M1'@V1". iPureIntro. split_and!; try done; [set_solver-|]. by eexists. }

  iMod ("Hclose" with "[-HΦ l'↦ e0↪ainfo1 Hγb' Hγul M⊢Mw' M⊢Ms' Hγd1 Hγl1]") as "_".
  { repeat iExists _. iFrame "HN M●1 Ms●1 Mw●1 Hγsa1 Hγwa1 Hγb1 Hγm1". rewrite omo_append_w_write_op.
    do 4 iExists _. iExists stnf1,(length Es1),ewf1,eVsn1,eVwf1. iExists 0,zwf1,Vm1,Vwf1,Vp1,(1/2)%Qp,(1/2)%Qp.
    iExists qu1,(1/2)%Qp,upds1,dgds1',lcks1',ulcks1.
    apply (dom_same _ _ _ ainfo1) in Hwarc1e0 as EQdomwarc1. rewrite -EQdomwarc1 lookup_insert Qp.half_half.
    iFrame "AllEvents1' AllWeaks1 omos↦1 omow↦1 Hγu1 Hγd1' Hγl1' Hγul1 esn1✓eVsn1 ewf1✓eVwf1 ⊒stf1w@Vwf1 ⊒stf1s@Vsf1
      ⊒upds1@Vwf1 ⊒ulcks1@Vwf1". destruct ty1; last first.
    { (* Weak counter cannot be in locked state *)
      iDestruct "Hty1" as %(_ & _ & (e' & ainfo' & _ & He' & EQSW) & _).
      rewrite EQsarc1 lookup_singleton_Some in He'. destruct He' as [<- <-]. rewrite Hainfo2 in EQSW. done. }
    iDestruct "Hty1" as "[_ Hty1]". iFrame "Hty1". iSplitL; last iSplitL; last iSplitL.
    - iApply big_sepL_snoc. iFrame "AllStrongs1 NewStrongInner".
    - iApply big_sepL_forall. iIntros "%i %ew %Hew".
      iDestruct (big_sepL_lookup with "AllLocks1") as (eVw z) "[ew↦eVw [%eVwEV %COND]]"; [exact Hew|].
      iExists eVw,z. iFrame "ew↦eVw". iPureIntro. split; [done|]. intros.
      apply COND in H. destruct H as [H|H]; left; [set_solver +H|].
      destruct H as (e' & ainfo' & He' & ewIN).
      rewrite EQsarc1 lookup_singleton_Some in He'. destruct He' as [<- <-].
      set_solver +ewIN SubainfoMw.
    - iRight. iRight. done.
    - iPureIntro. eapply (warc_update_snoc_1 _ _ _ ainfo1 _ _ eVop sarc1 sarc1') in Hwarc1e0 as H; try done; last first.
      { subst eVop. rewrite /= dom_delete_L. set_solver-. } { by apply delete_subseteq. } { subst ainfo1. solve_lat. } { subst ainfo1. done. }
      subst sarc1'. rewrite last_snoc EQsarc1' eVsn1EV.
      have LeainfoV1 : ainfo.1.1.1.2 ⊑ V1 by clear -LeV0'V0'' LeV0''V1; solve_lat.
      eapply (warc_update_2 _ _ _ ainfo1 V1) in Hwarc1e0 as H0; try done; [|subst ainfo1;solve_lat].
      clear eVEV. des. split_and!; try done.
      + by rewrite -EQdomwarc1 in H4.
      + by rewrite EQsarc1 delete_singleton -EQdomwarc1 in H5.
      + rewrite omo_append_w_write_op lookup_app_l; [done|]. apply lookup_lt_Some in HInitWrite1. done.
      + by rewrite last_snoc.
      + subst stnf1. rewrite dom_empty_L. done.
      + by rewrite /ArcAlive Forall_app Forall_singleton.
      + apply EventIdValid_update; [done|]. simpl. apply VALM in eM. rewrite lookup_lt_is_Some in eM. done.
      + rewrite H0 map_fold_empty. replace ((Vbs1 ⊔ V1) ⊔ Vbw1) with ((Vbs1 ⊔ Vbw1) ⊔ V1) by solve_lat.
        rewrite EQsarc1 map_fold_singleton_view_join_total {1}/view_join_total in LeVbs1Vbw1.
        clear -LeVbs1Vbw1 LeVm1V1 LeVs1Vm1 LeainfoV1. solve_lat.
      + solve_lat.
      + unfold SeenUpgrade. intros. destruct (decide (e0 = length E1)) as [->|NEQ].
        * rewrite lookup_app_1_eq in H9. inversion H9. subst eV0. done.
        * rewrite lookup_app_1_ne in H9; [|done]. apply SeenUpgrade1 in H9. destruct (eV0.(type)); try done.
          destruct H9 as [H9|H9]; [by left|]. right. destruct H9 as (e' & ainfo' & He' & e'IN).
          destruct (decide (e' = 0)) as [->|NEQ'].
          -- rewrite Hwarc1e0 in He'. inversion He'. subst ainfo'.
             exists 0,ainfo1. rewrite lookup_insert. split; [done|]. set_solver.
          -- exists e',ainfo'. rewrite lookup_insert_ne; [|done]. rewrite lookup_delete_ne; [|done]. done.
      + unfold SeenDowngrade. intros. destruct (decide (e0 = length E1)) as [->|NEQ].
        * rewrite lookup_app_1_eq in H9. inversion H9. subst eV0. done.
        * rewrite lookup_app_1_ne in H9; [|done]. apply SeenDowngrade1 in H9. destruct (eV0.(type)); try done.
          destruct H9 as [H9|H9]; left; [by set_solver +H9|]. destruct H9 as (e' & ainfo' & He' & e'IN).
          rewrite EQsarc1 lookup_singleton_Some in He'. destruct He' as [<- <-]. set_solver +e'IN SubainfoM.
      + unfold SeenUnlock. intros. apply SeenUnlock1 in H9. destruct H9 as [e0IN|(e' & ainfo' & He' & e0IN)]; left; [set_solver +e0IN|].
        rewrite EQsarc1 lookup_singleton_Some in He'. destruct He' as [<- <-]. set_solver +SubainfoMw e0IN.
      + rewrite /StlistValid Forall_app Forall_singleton. split; [done|]. subst stnf1. done.
      + rewrite H0 /=. solve_lat. }

  iModIntro. wp_pures. rewrite -[Z.to_nat 1]/(1%nat). wp_bind (!ᵃᶜ _)%E.
  iApply wp_hist_inv; [done|]. iIntros "#HInv".

  (* Inv access 2 *)
  iInv "AInv" as "H" "Hclose".
  iDestruct "H" as (?? γs2 ???????) "(%&%&%& %sarc2 & %warc2 & %qsa2 & %qwa2 & %alive2 & %E2 & %Es2 & %Ew2 & %omo2 & %omos2 &
    %omow2 & %stlist2 & %mos2 & %mow2 & %Mono2 & >HN' & >M●2 & >Ms●2 & >Mw●2 & >Hγsa2 & >Hγwa2 & >Hγb2 & >Hγm2 & Alive2)".
  gname_agree with "HN HN'". iClear "HN'".
  iDestruct (ghost_var_agree with "Hγb' Hγb2") as %<-.

  iDestruct "Alive2" as (Vbs2 Vbw2 ty2 uf2 stf2 esf2 ewf2 eVsf2 eVwf2 nsf2) "(%zwf2 & %Vsf2 & %Vwf2 & %Vp2 & %qsa2a & %qsa2b & %qu2 & %qd2 & %upds2 &
    %dgds2 & %lcks2 & %ulcks2 & >#AllEvents2 & >#AllStrongs2 & >#AllWeaks2 & >omos↦2 & >omow↦2 & >Hγu2 & >Hγd2 & >Hγl2 & >Hγul2 &
    >#AllLocks2 & [>#⊒upds2@Vwf2 >#⊒ulcks2@Vwf2] & >#esf2✓eVsf2 & >#ewf2✓eVwf2 & Hnsf2 & P2 & Hty2 & >#⊒stf2s@Vsf2 & >#⊒stf2w@Vwf2 & >Pures)".
  iDestruct "Pures" as %(Subuf2 & LASTesf2 & LASTewf2 & eVsf2EV & eVwf2EV & Hqsa2 & Hqwa2 & VALsarc2 & VALwarc2 & VALsarcwarc2 & SeenClone2 &
    SeenWeakClone2 & HInitWrite2 & LASTstf2 & DOMsarc2 & DOMwarc2 & EQqsa2 & Alive2 & VALeid2 & LeVbs2Vbw2 & GeVsf2 & GeVwf2 &
    SeenUpgrade2 & SeenDowngrade2 & SeenUnlock2 & LEsarc2 & LEwarc2 & VALstlist2 & LeVsf2 & EQnsf2).

  iDestruct (view_at_mono_2 _ V1 with "⊒lcks1@Vsf1") as "⊒lcks1@V1"; [solve_lat|].
  iDestruct (view_at_elim with "⊒V1 ⊒dgds1@V1") as "⊒dgds1".
  iDestruct (view_at_elim with "⊒V1 ⊒lcks1@V1") as "⊒lcks1".
  iDestruct (OmoEview_union_obj with "⊒M@V1 ⊒dgds1@V1") as "⊒M1''@V1".
  iDestruct (view_at_elim with "⊒V1 ⊒M1''@V1") as "⊒M1'".
  iDestruct (OmoEview_union with "⊒Mw ⊒lcks1") as "⊒lcks1'".
  iDestruct (OmoEview_update with "M●2 ⊒M1' ⊒lcks1'") as (Mw1'') "(M●2 & #⊒Mw1'' & M1'⊢Mw1'' & %Sublcks1'Mw1'')".

  wp_apply (append_only_loc_acquire_read with "[$Mw●2 $⊒Mw1'' $omow↦2 $⊒V1]"); [solve_ndisj|].
  iIntros (ew2 genw2 vw2 Vw2 V2 eVw2 eVwn2) "(Pures & Mw●2 & _ & #MAXew2 & #ew2✓eVw2 & #ewn2✓eVwn2 & _ & #⊒V2 & #⊒Mw2@V2 & omow↦2)".
  iDestruct "Pures" as %(Hgenw2 & eVw2EV & LeV1Vw2V2 & eVwn2EV & eVwn2SYNC).
  iDestruct (big_sepL_lookup with "AllWeaks2") as (eVw2' zw2) "(ew2✓eVw2' & [%eVw2'EV %GEzw2] & Hgenw2)"; [exact Hgenw2|].
  iDestruct (OmoEinfo_agree with "ew2✓eVw2 ew2✓eVw2'") as %<-. rewrite eVw2EV /= in eVw2'EV. subst vw2.
  iDestruct (ghost_map_lookup with "Hγwa2 e0↪ainfo1") as %Hwarc2e0.

  (* Prove that no other strong arcs exist *)
  destruct nsf2; last first.
  { iDestruct "Hnsf2" as "(_ & _ & _ & e0↪ainfo' & _)". by iDestruct (ghost_map_elem_valid_2 with "e0↪ainfo1 e0↪ainfo'") as %[? _]. }

  destruct (decide (zw2 = 1%Z)) as [->|NEQzw2]; last first.
  { (* Read non-`1` value. Other weak arcs might exist *)
    set ainfo2 := (ainfo1.1.1.1.1, ainfo1.1.1.1.2 ⊔ V2, ainfo1.1.1.2, ainfo1.1.2, cas_only).
    set warc2' := <[0:=ainfo2]> (delete 0 warc2).
    iMod (ghost_map_delete with "Hγwa2 e0↪ainfo1") as "Hγwa2".
    iMod (ghost_map_insert 0 ainfo2 with "Hγwa2") as "[Hγwa2 e0↪ainfo2]"; [by apply lookup_delete|].

    iDestruct (ghost_var_agree with "Hγl1 Hγl2") as %<-.
    iDestruct (ghost_var_agree with "Hγul Hγul2") as %<-.
    iDestruct (ghost_var_agree with "Hγd1 Hγd2") as %<-.
    iDestruct "Hγd2" as "[Hγd2 Hγd]". iDestruct "Hγl2" as "[Hγl2 _]".

    iMod ("Hclose" with "[-HΦ l'↦ Hγb' Hγul e0↪ainfo2 Hγd]") as "_".
    { repeat iExists _. iFrame "HN M●2 Ms●2 Mw●2 Hγsa2 Hγwa2 Hγb2 Hγm2". rewrite omo_insert_r_write_op.
      iNext. do 9 iExists _. iExists 0,_,Vsf2. repeat iExists _. eapply (dom_same _ _ _ ainfo2) in Hwarc2e0 as EQdom. rewrite -EQdom.
      iFrame "AllEvents2 AllStrongs2 AllWeaks2 omos↦2 omow↦2 Hγu2 Hγd2 Hγl2 Hγul2 AllLocks2 ⊒upds2@Vwf2 ⊒ulcks2@Vwf2
        esf2✓eVsf2 ewf2✓eVwf2 Hty2 ⊒stf2s@Vsf2 ⊒stf2w@Vwf2".
      rewrite Hwarc2e0 lookup_insert. iPureIntro. eapply (warc_update_1 _ _ _ ainfo2) in Hwarc2e0 as H; try done; [|solve_lat].
      eapply (warc_update_2 _ _ _ ainfo2) in Hwarc2e0 as H0; try done. clear eVEV. des. split_and!; try done.
      - rewrite H0. replace (Vbs2 ⊔ (Vbw2 ⊔ V2)) with ((Vbs2 ⊔ Vbw2) ⊔ V2) by solve_lat. clear -LeVbs2Vbw2. solve_lat.
      - rewrite H0. simpl in *. solve_lat. }

    have Subulcks1lcks1' : ulcks1 ⊆ lcks1'.
    { symmetry in EQnsf2. apply size_empty_inv in EQnsf2. fold_leibniz. rewrite EQnsf2 dom_empty_iff_L in DOMsarc2. rewrite DOMsarc2 in SeenUnlock2.
      unfold subseteq, set_subseteq_instance. intros. apply SeenUnlock2 in H. destruct H as [H|H]; [done|]. destruct H as (e' & ainfo' & He' & _). done. }

    iModIntro. wp_pures. rewrite bool_decide_false; [|lia].
    iDestruct "l'↦" as (?) "l'↦". iDestruct "He0" as (eV0) "[e0✓eV0 %eV0EV]".
    wp_write. iApply "HΦ". iExists 1. iFrame "l'↦". iExists V2. iFrame "⊒V2". iSplit.
    - do 14 iExists _. iExists opId,eV0,eVop. repeat iExists _. subst M1. iFrame "HN AInv ⊒M1'@V1 e0↪ainfo2 ⊒Ms@V0'' e0✓eV0 opId✓eVop Hγd".
      iDestruct (view_at_mono_2 _ V1 with "⊒Mw@V0''") as "⊒Mw@V1"; [solve_lat|].
      iDestruct (OmoEview_union_obj with "⊒Mw@V1 ⊒lcks1@V1") as "⊒Mw'@V1". iFrame "⊒Mw'@V1".
      subst ainfo2 ainfo1. simpl. iFrame "Hγb' Hγul". iSplit.
      + iApply view_at_unfold. rewrite monPred_at_in. iPureIntro. clear -LeV0'V0'' LeV0''V1 LeV1Vw2V2. solve_lat.
      + iPureIntro. split_and!; try done; [set_solver-|by exists e|set_solver-|set_solver +Subulcks1lcks1'].
    - iPureIntro. split; [done|]. solve_lat. }

  (* Read `1` from weak counter. No other weak arcs exist *)
  (* Prove that the message that we read is the last one *)
  destruct (decide (genw2 = length omow2 - 1)) as [->|NEQ]; last first.
  { (* Suppose next message exists *)
    have [ew2' Hew2'] : is_Some (omo_write_op omow2 !! (S genw2)).
    { rewrite lookup_lt_is_Some -omo_write_op_length. apply lookup_lt_Some in Hgenw2. rewrite -omo_write_op_length in Hgenw2. lia. }
    iDestruct (big_sepL_lookup with "AllWeaks2") as (eVw2' zw2') "(ew2'✓eVw2' & [%eVw2'EV %GZvw2'] & Hgenw2')"; [exact Hew2'|].
    iDestruct "Hgenw2'" as (omow2' ew2'' eVw2'' zw2'') "(Mw◯2 & ew2''✓eVw2'' & [%Hew2 %eVw2''EV] & CASE)".
    iDestruct (OmoAuth_OmoSnapOmo with "Mw●2 Mw◯2") as %PREFIXomow2.
    replace (S genw2 - 1) with genw2 in Hew2 by lia.
    rewrite -lookup_omo_wr_event in Hew2.
    eapply omo_prefix_lookup_Some in Hew2; [|exact PREFIXomow2].
    rewrite lookup_omo_wr_event omo_insert_r_write_op Hgenw2 in Hew2. inversion Hew2. subst ew2''.
    iDestruct (OmoEinfo_agree with "ew2✓eVw2 ew2''✓eVw2''") as %<-.
    rewrite eVw2EV /= in eVw2''EV. inversion eVw2''EV. subst zw2''.

    iDestruct (ghost_var_agree with "Hγd1 Hγd2") as %<-.
    iDestruct (ghost_var_agree with "Hγl1 Hγl2") as %<-.
    symmetry in EQnsf2. apply size_empty_inv in EQnsf2. fold_leibniz.
    rewrite EQnsf2 dom_empty_iff_L in DOMsarc2. subst sarc2.

    iDestruct "CASE" as "[(%e2' & %eV2' & e2'↦ew2' & e2'✓eV2' & e2'⊒ew2' & (_ & -> & %CASE))|[[_ ->]|[[_ ->]|[% _]]]]"; [..|done].
    - (* 1 -> 2 *) iDestruct (OmoAuth_OmoEinfo with "M●2 e2'✓eV2'") as %HeV2'.
      iAssert (⌜ e2' ∈ dgds1' ⌝)%I with "[-]" as %e2'IN.
      { destruct CASE as [eV2'EV|(e' & eV2'EV & He')].
        - apply SeenDowngrade2 in HeV2'. rewrite eV2'EV in HeV2'. by destruct HeV2' as [e2'IN|(e' & ainfo' & He' & _)].
        - have EQ : e' = 0 by apply He'; apply elem_of_dom_2 in Hwarc2e0. subst e'.
          specialize (SeenWeakClone2 _ _ _ _ Hwarc2e0 HeV2' eV2'EV).
          iPureIntro. clear -SubainfoM SeenWeakClone2 Hainfo1. set_solver. }
      iDestruct (OmoHb_HbIncluded with "e2'⊒ew2' M1'⊢Mw1''") as %ew2'Mw1''; [set_solver +e2'IN|].
      iDestruct (big_sepS_elem_of with "MAXew2") as "ew2'≤ew2"; [exact ew2'Mw1''|].
      iDestruct (OmoLe_Le _ _ _ _ _ _ (wr_event (S genw2)) (wr_event genw2) with "Mw●2 ew2'≤ew2") as %LE;
      try (by rewrite lookup_omo_wr_event omo_insert_r_write_op). simpl in LE. lia.
    - (* 1 -> 0 *) destruct (decide (S genw2 = length omow2 - 1)) as [EQ|NEQ']; last first.
      { have [ew2'' Hew2''] : is_Some (omo_write_op omow2 !! (S (S genw2))).
        { rewrite lookup_lt_is_Some -omo_write_op_length. apply lookup_lt_Some in Hew2'. rewrite -omo_write_op_length in Hew2'. lia. }
        iClear "ew2''✓eVw2''". clear eVw2''EV.
        iDestruct (big_sepL_lookup with "AllWeaks2") as (eVw2'' zw2'') "(ew2''✓eVw2'' & [%eVw2''EV %GZvw2''] & Hgenw2'')"; [exact Hew2''|].
        iDestruct "Hgenw2''" as (omow2'' ew2''' eVw2''' zw2''') "(Mw◯2' & ew2'''✓eVw2''' & [%Hew2''' %eVw2'''EV] & CASE)".
        iDestruct (OmoAuth_OmoSnapOmo with "Mw●2 Mw◯2'") as %PREFIXomow2'.
        replace (S (S genw2) - 1) with (S genw2) in Hew2''' by lia. rewrite -lookup_omo_wr_event in Hew2'''.
        eapply omo_prefix_lookup_Some in Hew2'''; [|exact PREFIXomow2'].
        rewrite lookup_omo_wr_event omo_insert_r_write_op Hew2' in Hew2'''. inversion Hew2'''. subst ew2'''.
        iDestruct (OmoEinfo_agree with "ew2'✓eVw2' ew2'''✓eVw2'''") as %<-.
        rewrite eVw2'EV /= in eVw2'''EV. inversion eVw2'''EV. subst zw2'''.
        iDestruct "CASE" as "[(%&%& _ & _ & _ & [% _])|[[% _]|[[% _]|[% _]]]]"; try lia. }

      rewrite EQ omo_write_op_length in Hew2'.
      replace (length (omo_write_op omow2) - 1) with (Init.Nat.pred (length (omo_write_op omow2))) in Hew2' by lia.
      rewrite -last_lookup LASTewf2 in Hew2'. inversion Hew2'. subst ew2'.
      iDestruct (OmoEinfo_agree with "ewf2✓eVwf2 ew2'✓eVw2'") as %<-.
      rewrite eVwf2EV /= in eVw2'EV. inversion eVw2'EV. subst zwf2. replace (1 - 1)%Z with 0%Z by lia.
      destruct ty2; [|by iDestruct "Hty2" as %[? _]; lia].
      iDestruct "Hty2" as "[_ [%SZstf2 _]]". symmetry in SZstf2.
      have SZstf2' : size stf2.2.1.1 = 0 by lia. apply size_empty_inv in SZstf2'. fold_leibniz.
      apply elem_of_dom_2 in Hwarc2e0. rewrite DOMwarc2 SZstf2' in Hwarc2e0. done.
    - (* 1 -> -1 *) iDestruct (big_sepL_lookup with "AllLocks2") as (eVw2'' zw2') "[ew2'✓eVw2'' [%eVw2''EV' %COND]]"; [exact Hew2'|].
      iDestruct (OmoEinfo_agree with "ew2'✓eVw2' ew2'✓eVw2''") as %<-.
      rewrite eVw2'EV in eVw2''EV'. inversion eVw2''EV'. subst zw2'.
      have COND' : (-1)%Z = (-1)%Z by lia. apply COND in COND' as [ew2'IN|(e' & ainfo' & He' & _)]; [|done].
      iDestruct (big_sepS_elem_of _ _ ew2' with "MAXew2") as "ew2'≤ew2"; [set_solver +Sublcks1'Mw1'' ew2'IN|].
      iDestruct (OmoLe_Le _ _ _ _ _ _ (wr_event (S genw2)) (wr_event genw2) with "Mw●2 ew2'≤ew2") as %LE;
      try (by rewrite lookup_omo_wr_event omo_insert_r_write_op). simpl in LE. lia. }

  replace (length omow2 - 1) with (Init.Nat.pred (length omow2)) in Hgenw2 by lia.
  rewrite omo_write_op_length -last_lookup LASTewf2 in Hgenw2. inversion Hgenw2. subst ew2.
  iDestruct (OmoEinfo_agree with "ewf2✓eVwf2 ew2✓eVw2") as %<-.
  rewrite eVwf2EV in eVw2EV. inversion eVw2EV. subst zwf2 Vw2.

  (* Collect all fractions *)
  destruct ty2; [|by iDestruct "Hty2" as %[? _]; lia].
  iDestruct "Hty2" as "[_ [%SZstf2 _]]".
  have SZstf2' : size stf2.2.1.1 = 1 by lia. apply size_1_elem_of in SZstf2' as [x Hstf2]. fold_leibniz.
  rewrite Hstf2 in DOMwarc2. apply elem_of_dom_2 in Hwarc2e0 as e0INdom. rewrite DOMwarc2 elem_of_singleton in e0INdom. subst x.
  apply dom_singleton_inv_L in DOMwarc2 as [x Hwarc2]. rewrite Hwarc2 lookup_singleton in Hwarc2e0. inversion Hwarc2e0. subst x.
  symmetry in EQnsf2. apply size_empty_inv in EQnsf2. fold_leibniz.
  rewrite EQnsf2 dom_empty_iff_L in DOMsarc2.

  rewrite DOMsarc2 map_fold_empty in Hqsa2. subst qsa2. rewrite Hqsa2.
  rewrite Hwarc2 map_fold_singleton_frac_sum /frac_sum in Hqwa2.
  iCombine "Hγb' Hγb2" as "Hγb2".
  have EQfrac : (1/2/2 + (1/2 + qwa2/2))%Qp = 1%Qp; [|rewrite EQfrac].
  { subst ainfo1. simpl in *. rewrite Qp.add_assoc (Qp.add_comm (1/2/2)%Qp (1/2)%Qp) -Qp.add_assoc -Qp.div_add_distr Hqwa2. compute_done. }
  iMod (ghost_var_update false with "Hγb2") as "Hγb2".
  rewrite -{14}EQfrac. iDestruct "Hγb2" as "[Hγb Hγb2]".

  (* Obtain na points-to from append_only_loc *)
  rewrite DOMsarc2 Hwarc2 map_fold_empty map_fold_singleton_view_join_total /view_join_total in LeVbs2Vbw2.
  rewrite Hwarc2 map_fold_singleton_view_join_total /view_join_total /= in LeVsf2.
  have LeVp2ainfo1 : Vp2 ⊑ ainfo1.1.1.1.2 by apply (LEwarc2 0); rewrite Hwarc2 lookup_singleton.
  have Leainfo1V2 : ainfo1.1.1.1.2 ⊑ V2 by subst; clear -LeV0'V0'' LeV0''V1 LeV1Vw2V2; solve_lat.
  have LeVwf2V2 : Vwf2 ⊑ V2 by clear -LeV1Vw2V2; solve_lat.
  have LeVbs2Vbw2' : Vbs2 ⊔ Vbw2 ⊑ V2 by solve_lat.

  iDestruct (view_at_mono_2 _ V2 with "omos↦2") as "omos↦2"; [solve_lat|]. iDestruct (view_at_mono_2 _ V2 with "omow↦2") as "omow↦2"; [solve_lat|].
  iDestruct (view_at_elim with "⊒V2 omos↦2") as "omos↦2". iDestruct (view_at_elim with "⊒V2 omow↦2") as "omow↦2".
  iMod (append_only_loc_to_na with "HInv Ms●2 omos↦2") as (vs es eVs) "(ls↦ & [Ms●2 _] & #es✓eVs & [%Hes %eVsEV])"; [solve_ndisj|].
  iMod (append_only_loc_to_na with "HInv Mw●2 omow↦2") as (vw ew eVw) "(lw↦ & [Mw●2 _] & #ew✓eVw & [%Hew %eVwEV])"; [solve_ndisj|].
  rewrite omo_insert_r_write_op LASTewf2 in Hew. inversion Hew. subst ew.
  iDestruct (OmoEinfo_agree with "ewf2✓eVwf2 ew✓eVw") as %<-.
  rewrite eVwf2EV /= in eVwEV. subst vw.

  iMod ("Hclose" with "[-HΦ l'↦ ls↦ lw↦]") as "_". { repeat iExists _. iFrame "HN M●2 Ms●2 Mw●2 Hγsa2 Hγwa2 Hγm2 Hγb2". }

  iModIntro. wp_pures. wp_write. iDestruct "l'↦" as (?) "l'↦".
  wp_write. wp_pures. iApply "HΦ". iExists 0. by iFrame "l'↦ ls↦ lw↦".
Qed.

Lemma is_unique_spec :
  is_unique_spec' code.is_unique ArcInv StrongArc.
Proof.
  intros N DISJ l tid γg q M e V0 P1 P2. iIntros "%PasFrac #⊒V0 SArc P1" (Φ) "AU".
  iDestruct "SArc" as (??????????) "(%&%&%&%&%&%& #HN & #AInv & #⊒M & #⊒Ms & #⊒Mw & #e✓eV & #⊒ainfo & Hγb & e↪ainfo &
    (-> & %Hainfo2 & %eM & %eVEV & %SubainfoM & %SubainfoMw))".
  wp_lam. wp_pures. rewrite -[Z.to_nat 1]/(1%nat). wp_bind (casᵃᶜ(_,_,_))%E.

  (* Inv access 1 *)
  iInv "AInv" as "H" "Hclose".
  iDestruct "H" as (?? γs1 ???????) "(%&%&%& %sarc1 & %warc1 & %qsa1 & %qwa1 & %alive1 & %E1 & %Es1 & %Ew1 & %omo1 & %omos1 &
    %omow1 & %stlist1 & %mos1 & %mow1 & %Mono1 & >HN' & >M●1 & >Ms●1 & >Mw●1 & >Hγsa1 & >Hγwa1 & >Hγb1 & >Hγm1 & Alive1)".
  gname_agree with "HN HN'". iClear "HN'".
  iDestruct (ghost_var_agree with "Hγb Hγb1") as %<-.

  iDestruct (OmoEview_update with "M●1 ⊒M ⊒Mw") as (Mw') "(M●1 & #⊒Mw' & M⊢Mw' & %SubMwMw')".
  iCombine "⊒V0 ⊒ainfo" as "⊒V0'". rewrite monPred_in_view_op. set V0' := V0 ⊔ ainfo.1.1.1.2.
  iCombine "⊒M ⊒Ms ⊒Mw ⊒ainfo ⊒Mw' P1" as "RES".
  iDestruct (view_at_intro_incl with "RES ⊒V0'") as (V0'')
    "(#⊒V0'' & %LeV0'V0'' & (#⊒M@V0'' & #⊒Ms@V0'' & #⊒Mw@V0'' & #⊒ainfo@V0'' & #⊒Mw'@V0'' & P1@V0''))".

  iDestruct "Alive1" as (Vbs1 Vbw1 ty1 uf1 stf1 esf1 ewf1 eVsf1 eVwf1 nsf1) "(%zwf1 & %Vsf1 & %Vwf1 & %Vp1 & %qsa1a & %qsa1b & %qu1 & %qd1 & %upds1 &
    %dgds1 & %lcks1 & %ulcks1 & >#AllEvents1 & >#AllStrongs1 & >#AllWeaks1 & >omos↦1 & >omow↦1 & >Hγu1 & >Hγd1 & >Hγl1 & >Hγul1 &
    >#AllLocks1 & [>#⊒upds1@Vwf1 >#⊒ulcks1@Vwf1] & >#esf1✓eVsf1 & >#ewf1✓eVwf1 & Hnsf1 & P2 & Hty1 & >#⊒stf1s@Vsf1 & >#⊒stf1w@Vwf1 & >Pures)".
  iDestruct "Pures" as %(Subuf1 & LASTesf1 & LASTewf1 & eVsf1EV & eVwf1EV & Hqsa1 & Hqwa1 & VALsarc1 & VALwarc1 & VALsarcwarc1 & SeenClone1 &
    SeenWeakClone1 & HInitWrite1 & LASTstf1 & DOMsarc1 & DOMwarc1 & EQqsa1 & Alive1 & VALeid1 & LeVbs1Vbw1 & GeVsf1 & GeVwf1 &
    SeenUpgrade1 & SeenDowngrade1 & SeenUnlock1 & LEsarc1 & LEwarc1 & VALstlist1 & LeVsf1 & EQnsf1).
  iDestruct (OmoAuth_omo_nonempty with "Mw●1") as %Nomow1. iDestruct (OmoSnapOmo_get with "Mw●1") as "#Mw◯1".
  iMod (rel_objectively_intro (⊒∅) tid with "[]") as "#⊒∅"; [by iApply objective_objectively; iApply monPred_in_bot|].

  wp_apply (append_only_loc_cas_general with "[$Mw●1 $⊒Mw' $omow↦1 $⊒V0'']"); try done; [solve_ndisj|set_solver|].
  iIntros (b1 ew1 genw1 vw1 Vw1 V1 mow1' omow1' eVw1 eVwn1)
    "(Pures & #MAXew1 & #ew1✓eVw1 & #ewn1✓eVwn1 & Mw●1 & #⊒V1 & #⊒Mw1@V1 & CASE)".
  iDestruct "Pures" as %(Eqgenw1 & eVw1EV & LeV0''V1).
  iDestruct "CASE" as "[(Pures & _ & omow↦1 & _) | [Pures sVw1]]".
  { (* CAS failed, commit *)
    iDestruct "Pures" as %(-> & NEQvw1 & -> & Homow1' & eVwn1EV & eVwn1SYNC).

    set ainfo' := (ainfo.1.1.1.1, ainfo.1.1.1.2 ⊔ V1, ainfo.1.1.2, ainfo.1.2, cas_only).
    set sarc1' := <[e := ainfo']> (delete e sarc1).
    iDestruct (ghost_map_lookup with "Hγsa1 e↪ainfo") as %Hsarc1e.
    iMod (ghost_map_delete with "Hγsa1 e↪ainfo") as "Hγsa1".
    iMod (ghost_map_insert e ainfo' with "Hγsa1") as "[Hγsa1 e↪ainfo]"; [by apply lookup_delete|].
    iAssert (⌜ nsf1 ≠ 0 ⌝)%I with "[-]" as %NZnsf1.
    { iIntros "%Znsf1". rewrite EQnsf1 in Znsf1. apply size_empty_inv in Znsf1. fold_leibniz.
      rewrite Znsf1 in DOMsarc1. apply elem_of_dom_2 in Hsarc1e. rewrite DOMsarc1 in Hsarc1e. set_solver +Hsarc1e. }

    iAssert (⌜ ¬is_unique_must_success E1 stlist1 M e ⌝)%I with "[-]" as %FAIL.
    { unfold not, is_unique_must_success. iIntros (H). destruct H as (stf & LASTstf & H1 & H2 & INCL).
      rewrite LASTstf1 in LASTstf. inversion LASTstf. subst stf. destruct ty1.
      - iDestruct "Hty1" as "[CASE [% %]]". subst zwf1 qu1.
        iAssert (⌜ ewf1 ∈ Mw' ⌝)%I with "[-]" as %e'Mw'.
        { iDestruct "CASE" as "[[%e' #e'⊒ewf1]|[(%e' & %ainfo'' & %He' & %ewf1IN)|%Znsf1]]"; [..|lia].
          - iDestruct (OmoAuth_OmoHb_l with "M●1 e'⊒ewf1") as %VALe'. apply INCL in VALe'.
            by iDestruct (OmoHb_HbIncluded with "e'⊒ewf1 M⊢Mw'") as %e'Mw'.
          - apply elem_of_dom_2 in He' as e'INdom. rewrite DOMsarc1 H1 elem_of_singleton in e'INdom. subst e'.
            rewrite Hsarc1e in He'. inversion He'. subst ainfo''. iPureIntro. set_solver. }
        rewrite last_lookup -omo_write_op_length in LASTewf1.
        replace (Init.Nat.pred (length omow1)) with (length omow1 - 1) in LASTewf1 by lia.

        iAssert (⌜ ewf1 ≠ ew1 ⌝)%I with "[-]" as %NEQ.
        { iIntros (EQ). subst ew1. iDestruct (OmoEinfo_agree with "ewf1✓eVwf1 ew1✓eVw1") as %<-.
          rewrite eVwf1EV in eVw1EV. inversion eVw1EV. subst vw1. rewrite H2 size_singleton in NEQvw1. inversion NEQvw1. lia. }
        iDestruct (OmoLt_get _ _ _ _ _ _ (wr_event genw1) (wr_event (length omow1 - 1)) with "Mw●1") as "#ew1<ewf1".
        { by rewrite Homow1' lookup_omo_wr_event omo_insert_r_write_op. } { by rewrite Homow1' lookup_omo_wr_event omo_insert_r_write_op. }
        { apply lookup_lt_Some in Eqgenw1 as LT. rewrite -omo_write_op_length in LT. simpl.
          destruct (decide (genw1 = length omow1 - 1)) as [->|NEQ']; [|lia].
          rewrite Eqgenw1 in LASTewf1. inversion LASTewf1. subst ew1. done. }
        iDestruct (big_sepS_elem_of with "MAXew1") as "ewf1≤ew1"; [exact e'Mw'|].
        by iDestruct (OmoLe_Lt_contra with "ewf1≤ew1 ew1<ewf1") as %?.
      - iDestruct "Hty1" as %(_ & _ & (e' & ainfo'' & IN & He' & EQswriter) & _). rewrite H1 in IN.
        have EQ : e' = e by set_solver. subst e'.
        rewrite Hsarc1e in He'. inversion He'. subst ainfo''. rewrite Hainfo2 in EQswriter. done. }

    have LeV0V1 : V0 ⊑ V1 by solve_lat.
    iMod "AU" as (????) "[>M●1' [_ Commit]]". iDestruct (OmoAuth_agree with "M●1 M●1'") as %(<- & <- & <- & <-).
    iMod ("Commit" $! false V1 E1 omo1 M with "[$M●1' $⊒V1 $P1@V0'' $⊒M@V0'']") as "HΦ"; [done|].

    iMod ("Hclose" with "[-HΦ Hγb e↪ainfo]") as "_".
    { repeat iExists _. iFrame "HN M●1 Ms●1 Mw●1 Hγwa1 Hγb1 Hγm1 Hγsa1". rewrite Homow1' omo_insert_r_write_op.
      repeat iExists _. iFrame "AllEvents1 AllStrongs1 AllWeaks1 omos↦1 omow↦1 Hγu1 Hγd1 Hγl1 Hγul1 esf1✓eVsf1 ewf1✓eVwf1 Hnsf1
        P2 ⊒stf1s@Vsf1 ⊒stf1w@Vwf1 ⊒upds1@Vwf1 ⊒ulcks1@Vwf1". iSplitR; last iSplitL.
      - iNext. iApply big_sepL_forall. iIntros "%i %ew %Hew".
        iDestruct (big_sepL_lookup with "AllLocks1") as (??) "[ew✓eVw [%eVwEV %COND]]"; [exact Hew|].
        repeat iExists _. iFrame "ew✓eVw". iPureIntro. split; [done|]. intros. apply COND in H as [H|H]; [by left|].
        right. destruct H as (e' & ainfo'' & Hainfo & IN). destruct (decide (e' = e)) as [->|NEQ].
        + rewrite Hsarc1e in Hainfo. inversion Hainfo. subst ainfo''.
          exists e,ainfo'. rewrite lookup_insert. split; [done|]. subst ainfo'. done.
        + exists e',ainfo''. rewrite lookup_insert_ne; [|done]. rewrite lookup_delete_ne; [|done]. done.
      - iApply (append_only_type_condition_update with "Hty1"); try done.
      - iPureIntro. eapply (sarc_update_1 _ _ _ ainfo') in Hsarc1e as H; try done; [|solve_lat].
        eapply (sarc_update_2 _ _ _ ainfo' _ _ _ _ lcks1 lcks1 ulcks1) in Hsarc1e as H0; try done. clear eVEV. des. split_and!; try done.
        rewrite H0. have EQ : Vbs1 ⊔ (Vbw1 ⊔ V1) = Vbs1 ⊔ Vbw1 ⊔ V1 by solve_lat. rewrite EQ. solve_lat. }

    iModIntro. wp_pures. iApply "HΦ". iExists V1. iFrame "⊒V1". iSplit; [|done].
    repeat iExists _. iFrame "HN AInv ⊒M@V0'' ⊒Ms@V0'' ⊒Mw@V0'' e✓eV e↪ainfo Hγb".
    iSplit; [|done]. iApply view_at_unfold. rewrite monPred_at_in. iPureIntro. clear -LeV0'V0'' LeV0''V1. solve_lat. }

  (* CAS success, locked the weak counter *)
  iDestruct "Pures" as %(-> & -> & EQgenw1).
  iDestruct "sVw1" as (Vm1) "((%Hmow1' & %Homow1' & %eVwn1EV & %eVwn1SYNC & %LeVw1Vm1 & %NEqVw1Vm1 & %NLeV1Vw1 & %NEqV0''V1 & _) &
    _ & omow↦1 & %LeVm1V1 & _)".
  rewrite last_lookup -omo_write_op_length in LASTewf1.
  replace (Init.Nat.pred (length omow1)) with (length omow1 - 1) in LASTewf1 by lia.
  rewrite EQgenw1 LASTewf1 in Eqgenw1. inversion Eqgenw1. subst ew1.
  iDestruct (OmoEinfo_agree with "ewf1✓eVwf1 ew1✓eVw1") as %<-.
  rewrite eVwf1EV in eVw1EV. inversion eVw1EV. subst zwf1 Vw1.

  (* ty1 = swriter: this location has been already locked, contradiction *)
  destruct ty1; [|by iDestruct "Hty1" as %[? _]].
  iDestruct "Hty1" as "[_ [%EQsz1 %Hqu1]]". subst qu1. iDestruct "Hγu1" as "[Hγu1 Hγu1']".

  iDestruct (view_at_elim with "⊒V1 ⊒Mw1@V1") as "⊒Mw1".
  iDestruct (cas_only_to_swriter_obj _ _ _ _ _ _ _ _ (length Ew1) (wr_event (length omow1)) with "Mw●1 ⊒Mw1 omow↦1") as "(Mw●1 & omow↦1 & SW)".
  { set_solver-. } { by rewrite Homow1' lookup_omo_wr_event omo_append_w_write_op omo_write_op_length lookup_app_1_eq. }
  { rewrite Homow1' omo_append_w_length /=. lia. }

  set ainfo1 := (ainfo.1.1.1.1, ainfo.1.1.1.2 ⊔ V1, ainfo.1.1.2, ainfo.1.2 ∪ {[(length Ew1)]}, swriter).
  set sarc1' := <[e := ainfo1]> (delete e sarc1).
  iDestruct (ghost_map_lookup with "Hγsa1 e↪ainfo") as %Hsarc1e.
  iMod (ghost_map_delete with "Hγsa1 e↪ainfo") as "Hγsa1".
  iMod (ghost_map_insert e ainfo1 with "Hγsa1") as "[Hγsa1 e↪ainfo1]"; [by apply lookup_delete|].

  iMod ("Hclose" with "[-Hγb AU e↪ainfo1 M⊢Mw' SW P1@V0'' Hγu1]") as "_".
  { repeat iExists _. iFrame "HN M●1 Ms●1 Mw●1 Hγsa1 Hγwa1 Hγb1 Hγm1".
    do 12 iExists _. iExists Vm1. repeat iExists _. iFrame "AllEvents1 AllStrongs1 omos↦1 omow↦1 Hγu1' Hγd1 Hγl1 Hγul1
      esf1✓eVsf1 ewn1✓eVwn1 Hnsf1 ⊒stf1s@Vsf1 ⊒stf1w@Vwf1 ⊒upds1@Vwf1 ⊒ulcks1@Vwf1". iSplitR; last iSplitR; last iSplitL.
    - rewrite Homow1' omo_append_w_write_op. iApply big_sepL_snoc. iFrame "AllWeaks1".
      repeat iExists _. iFrame "ewn1✓eVwn1". iSplit; [by rewrite eVwn1EV|].
      rewrite -omo_write_op_length. destruct (length omow1) eqn:Hlen; [by destruct omow1|].
      rewrite -Hlen in EQgenw1, LASTewf1. rewrite -Hlen. clear Hlen n.
      iExists omow1,ewf1,eVwf1,1%Z. iFrame "Mw◯1 ewf1✓eVwf1". rewrite eVwf1EV. iSplit; [done|]. iRight. iRight. iLeft. done.
    - rewrite Homow1' omo_append_w_write_op. iApply big_sepL_snoc. iSplit.
      + iApply big_sepL_forall. iIntros "%i %ew %Hew".
        iDestruct (big_sepL_lookup with "AllLocks1") as (eVw z) "[ew✓eVw [%eVwEV %COND]]"; [exact Hew|].
        iExists eVw,z. iFrame "ew✓eVw". iPureIntro. split; [done|]. intros. apply COND in H. destruct H as [H|H]; [by left|].
        destruct H as (e' & ainfo' & He' & IN). right. destruct (decide (e' = e)) as [->|NEQ].
        * rewrite Hsarc1e in He'. inversion He'. subst ainfo'.
          exists e,ainfo1. rewrite lookup_insert. split; [done|]. set_solver.
        * exists e',ainfo'. rewrite lookup_insert_ne; [|done]. rewrite lookup_delete_ne; [|done]. done.
      + iExists eVwn1,(-1)%Z. iFrame "ewn1✓eVwn1". iPureIntro. rewrite eVwn1EV. split; [done|]. intros. right.
        exists e,ainfo1. rewrite lookup_insert. split; [done|]. set_solver-.
    - destruct (warc1 !! 0); [done|]. iFrame "P2".
    - iPureIntro. eapply (sarc_update_1 _ _ _ ainfo1) in Hsarc1e as H; try done; [|solve_lat|set_solver].
      eapply (sarc_update_2 _ _ _ ainfo1 _ _ _ _ lcks1 lcks1 ulcks1) in Hsarc1e as H0; try done; [|set_solver-].
      clear eVEV. des. split_and!; try done; [lia|..].
      + exists e, ainfo1. split_and!; [by rewrite -DOMsarc1; eapply elem_of_dom_2|by rewrite lookup_insert|done].
      + rewrite Homow1' omo_append_w_write_op last_snoc. done.
      + rewrite eVwn1EV. simpl. done.
      + rewrite H0. have EQ : Vbs1 ⊔ (Vbw1 ⊔ V1) = Vbs1 ⊔ Vbw1 ⊔ V1 by solve_lat. rewrite EQ. solve_lat.
      + solve_lat.
      + destruct (decide (nsf1 = 0)) as [->|NEQ]; [|done]. solve_lat. }

  iModIntro. wp_pures. wp_bind (!ᵃᶜ _)%E. iApply wp_hist_inv; [done|]. iIntros "#HInv".

  (* Inv access 2 *)
  iInv "AInv" as "H" "Hclose".
  iDestruct "H" as (?? γs2 ???????) "(%&%&%& %sarc2 & %warc2 & %qsa2 & %qwa2 & %alive2 & %E2 & %Es2 & %Ew2 & %omo2 & %omos2 &
    %omow2 & %stlist2 & %mos2 & %mow2 & %Mono2 & >HN' & >M●2 & >Ms●2 & >Mw●2 & >Hγsa2 & >Hγwa2 & >Hγb2 & >Hγm2 & Alive2)".
  gname_agree with "HN HN'". iClear "HN'".
  iDestruct (ghost_var_agree with "Hγb Hγb2") as %<-.

  iDestruct "Alive2" as (Vbs2 Vbw2 ty2 uf2 stf2 esf2 ewf2 eVsf2 eVwf2 nsf2) "(%zwf2 & %Vsf2 & %Vwf2 & %Vp2 & %qsa2a & %qsa2b & %qu2 & %qd2 & %upds2 &
    %dgds2 & %lcks2 & %ulcks2 & >#AllEvents2 & >#AllStrongs2 & >#AllWeaks2 & >omos↦2 & >omow↦2 & >Hγu2 & >Hγd2 & >Hγl2 & >Hγul2 &
    >#AllLocks2 & [>#⊒upds2@Vwf2 >#⊒ulcks2@Vwf2] & >#esf2✓eVsf2 & >#ewf2✓eVwf2 & Hnsf2 & P2 & Hty2 & >#⊒stf2s@Vsf2 & >#⊒stf2w@Vwf2 & >Pures)".
  iDestruct "Pures" as %(Subuf2 & LASTesf2 & LASTewf2 & eVsf2EV & eVwf2EV & Hqsa2 & Hqwa2 & VALsarc2 & VALwarc2 & VALsarcwarc2 & SeenClone2 &
    SeenWeakClone2 & HInitWrite2 & LASTstf2 & DOMsarc2 & DOMwarc2 & EQqsa2 & Alive2 & VALeid2 & LeVbs2Vbw2 & GeVsf2 & GeVwf2 &
    SeenUpgrade2 & SeenDowngrade2 & SeenUnlock2 & LEsarc2 & LEwarc2 & VALstlist2 & LeVsf2 & EQnsf2).
  iDestruct (swriter_token_type_obj_2 with "SW omow↦2") as %->.
  iDestruct (ghost_map_lookup with "Hγsa2 e↪ainfo1") as %Hsarc2e.

  iDestruct (OmoAuth_wf with "M●2") as %[OMO_GOOD2 _].
  apply omo_stlist_length in OMO_GOOD2 as EQlenST2.

  (* Include local observation of Upgrade events by WeakArcs *)
  iDestruct (view_at_mono_2 _ V1 with "⊒upds1@Vwf1") as "⊒upds1@V1"; [solve_lat|].
  iDestruct (view_at_elim with "⊒V1 ⊒upds1@V1") as "⊒upds1".
  iDestruct (OmoEview_union with "⊒M ⊒upds1") as "⊒M1".
  iDestruct (OmoEview_update with "M●2 ⊒M1 ⊒Ms") as (Ms') "(M●2 & #⊒Ms' & M1⊢Ms' & %SubMsMs')".

  wp_apply (append_only_loc_acquire_read with "[$Ms●2 $⊒Ms' $omos↦2 $⊒V1]"); [solve_ndisj|].
  iIntros (es2 gens2 vs2 Vs2 V2 eVs2 eVsn2) "(Pures & Ms●2 & RCOMMIT & #MAXes2 & #es2✓eVs2 & #esn2✓eVsn2 & _ & #⊒V2 & #⊒Ms2@V2 & omos↦2)".
  iDestruct "Pures" as %(Hgens2 & eVs2EV & LeV1Vs2V2 & eVsn2EV & eVsn2SYNC).

  iDestruct (big_sepL_lookup with "AllStrongs2") as (e2 st2 eVs2')
    "(e2↦es2 & e2⊒es2 & e2↪st2 & es2✓eVs2' & MONO✓e2 & %eVs2'EV & Hgens2)"; [exact Hgens2|].
  iDestruct (OmoEinfo_agree with "es2✓eVs2 es2✓eVs2'") as %<-. iClear "es2✓eVs2'".
  rewrite eVs2EV /= in eVs2'EV. subst vs2. destruct (decide (size st2.1.1.1 = 1)) as [Hvs2|Hvs2].
  - (* Read `1` from strong counter. Commit [Unique] event *)
    (* Prove that we have read the last message *)
    destruct (decide (gens2 = (length omos2 - 1))) as [->|NEQ]; last first.
    { have [es2' Hes2'] : is_Some (omo_write_op omos2 !! (S gens2)).
      { rewrite lookup_lt_is_Some. apply lookup_lt_Some in Hgens2. rewrite omo_write_op_length in NEQ. lia. }
      iDestruct (big_sepL_lookup with "AllStrongs2") as (e2' st2' eVs2')
        "(e2'↦es2' & e2'⊒es2' & e2'↪st2' & es2'✓eVs2' & MONO✓e2' & %eVs2'EV & Hgens2')"; [exact Hes2'|].
      iDestruct "Hgens2'" as (omos2' e2'' es2'' eV2' eVs2'' st2'') "(Ms◯2 & e2''↦es2'' & e2'✓eV2' & es2''✓eVs2'' & e2''↪st2'' & _ & Pures)".
      iDestruct "Pures" as %(Hgens2' & eVs2''EV & NZst2'' & CASE).

      iDestruct (OmoAuth_OmoSnapOmo with "Ms●2 Ms◯2") as %PREFIXomos2.
      replace (S gens2 - 1) with gens2 in Hgens2' by lia.
      rewrite -lookup_omo_wr_event in Hgens2'.
      eapply omo_prefix_lookup_Some in Hgens2'; [|exact PREFIXomos2].
      rewrite lookup_omo_wr_event omo_insert_r_write_op Hgens2 in Hgens2'. inversion Hgens2'. subst es2''. clear Hgens2'.
      iDestruct (OmoCW_agree_2 with "e2↦es2 e2''↦es2''") as %[_ <-].
      iDestruct (OmoSnap_agree with "e2↪st2 e2''↪st2''") as %<-.
      rewrite Hvs2 /= in CASE.

      destruct CASE as [CASE|[Hvs2' _]].
      - (* If next message has value 2: contradiction since we must have observed it already *)
        destruct CASE as [_ [(e'' & eV2'EV & e''IN)|CASE]].
        + (* If next message is due to clone event: that clone event must have been performed by me *)
          iDestruct (OmoAuth_OmoEinfo with "M●2 e✓eV") as %HeV.
          iDestruct (OmoAuth_OmoEinfo' with "M●2 e✓eV") as %[eidx Heidx].
          iDestruct (OmoAuth_OmoCW_l' with "M●2 e2↦es2") as %[eidx2 Heidx2].
          iDestruct (OmoAuth_OmoSnap with "M●2 e2↪st2") as %Hst2; [done|].

          have eINdom : e ∈ dom sarc2 by apply elem_of_dom_2 in Hsarc2e.
          specialize (strong_arc_persist e eidx eV _ _ _ _ _ OMO_GOOD2 Heidx HeV eVEV eINdom VALsarcwarc2) as Hstlist2.

          iAssert (∃ es, OmoCW γg γes e es ∗ OmoHb γg γes e es ∗ CWMonoValid γm e)%I with "[]" as (es)
            "(#e↦es & #e⊒es & #MONO✓e)"; [by iDestruct (big_sepL_lookup with "AllEvents2") as "Inner"; [exact HeV|]; des; rewrite eVEV|].
          iDestruct (OmoHb_HbIncluded with "e⊒es M1⊢Ms'") as %esIN; [set_solver +eM|].
          iDestruct (big_sepS_elem_of with "MAXes2") as "es≤es2"; [exact esIN|].
          iDestruct (CWMono_acc with "Hγm2 MONO✓e MONO✓e2 e↦es e2↦es2 es≤es2") as "#e≤e2".
          iDestruct (OmoLe_Le with "M●2 e≤e2") as %LE; try done. simpl in LE.
          specialize (Hstlist2 _ _ Hst2 LE).

          apply size_1_elem_of in Hvs2 as [x Hvs2]. fold_leibniz. rewrite Hvs2 elem_of_singleton in Hstlist2. subst x.
          rewrite Hvs2 elem_of_singleton in e''IN. subst e''.
          iDestruct (OmoAuth_OmoEinfo with "M●2 e2'✓eV2'") as %HeV2'.
          specialize (SeenClone2 _ _ _ _ Hsarc2e HeV2' eV2'EV).
          have e2'IN : e2' ∈ M by set_solver +SeenClone2 SubainfoM.

          iDestruct (OmoHb_HbIncluded with "e2'⊒es2' M1⊢Ms'") as %e2'Ms'; [set_solver +e2'IN|].
          iDestruct (big_sepS_elem_of with "MAXes2") as "es2'≤es2"; [exact e2'Ms'|].
          iDestruct (OmoLe_Le _ _ _ _ _ _ (wr_event (S gens2)) (wr_event gens2) with "Ms●2 es2'≤es2") as %LE';
          try (by rewrite lookup_omo_wr_event omo_insert_r_write_op). simpl in LE'. lia.
        + (* If next message is due to upgrade event: it is observed by performing acquire cas on weak pointer *)
          iDestruct (ghost_var_agree with "Hγu1 Hγu2") as %<-.
          iDestruct (OmoAuth_OmoEinfo with "M●2 e2'✓eV2'") as %HeV2'.
          eapply SeenUpgrade2 in HeV2' as HeV2''. rewrite CASE in HeV2''. destruct HeV2'' as [e2'IN |(e' & ainfo' & He' & e'IN)]; last first.
          { iDestruct "Hty2" as %(-> & SZstf2 & _). destruct nsf2.
            { have EQ' : stf2.1.1.1 = ∅; [unfold_leibniz; apply size_empty_inv; fold_leibniz; lia|].
              rewrite EQ' dom_empty_iff_L in DOMsarc2. subst sarc2. done. }

            iDestruct "Hnsf2" as "(_ & _ & _ & e0↪ainfo & _)".
            iDestruct (ghost_map_lookup with "Hγwa2 e0↪ainfo") as %Hwarc2e0.

            have EQdom : dom warc2 = {[0]}.
            { apply (f_equal size) in DOMwarc2 as EQsz. rewrite SZstf2 in EQsz.
              apply size_1_elem_of in EQsz as [e'' EQdom]. fold_leibniz.
              apply elem_of_dom_2 in Hwarc2e0. rewrite EQdom in Hwarc2e0.
              have EQ : e'' = 0 by set_solver +Hwarc2e0. subst e''. done. }

            apply elem_of_dom_2 in He' as e'INdom. rewrite EQdom elem_of_singleton in e'INdom. subst e'.
            rewrite Hwarc2e0 in He'. inversion He'. subst ainfo'. simpl in e'IN. done. }

          iDestruct (OmoHb_HbIncluded with "e2'⊒es2' M1⊢Ms'") as %e2'Ms'; [set_solver +e2'IN|].
          iDestruct (big_sepS_elem_of with "MAXes2") as "es2'≤es2"; [exact e2'Ms'|].
          iDestruct (OmoLe_Le _ _ _ _ _ _ (wr_event (S gens2)) (wr_event gens2) with "Ms●2 es2'≤es2") as %LE;
          try (by rewrite lookup_omo_wr_event omo_insert_r_write_op). simpl in LE. lia.
      - (* If next message has value 0: contradiction since current strong arc is still alive *)
        destruct (decide (S gens2 = (length omos2 - 1))) as [EQ|NEQ'].
        + rewrite last_lookup -omo_write_op_length in LASTesf2.
          replace (Init.Nat.pred (length omos2)) with (length omos2 - 1) in LASTesf2 by lia.
          rewrite EQ LASTesf2 in Hes2'. inversion Hes2'. subst es2'.
          iDestruct (OmoEinfo_agree with "esf2✓eVsf2 es2'✓eVs2'") as %<-.
          rewrite eVsf2EV Hvs2' /= in eVs2'EV. inversion eVs2'EV. subst nsf2.

          have EQ' : stf2.1.1.1 = ∅ by unfold_leibniz; apply size_empty_inv; fold_leibniz; lia.
          rewrite EQ' dom_empty_iff_L in DOMsarc2. subst sarc2. done.
        + have [es2'' Hes2''] : is_Some (omo_write_op omos2 !! (S (S gens2))).
          { rewrite lookup_lt_is_Some. apply lookup_lt_Some in Hes2'. rewrite omo_write_op_length in NEQ'. lia. }
          iClear "e2''↦es2'' e2''↪st2''".
          iDestruct (big_sepL_lookup with "AllStrongs2") as (e2'' st2'' eVs2''')
            "(e2''↦es2'' & e2''⊒es2'' & e2''↪st2'' & es2''✓eVs2''' & MONO✓e2'' & %eVs2'''EV & Hgens2'')"; [exact Hes2''|].
          iDestruct "Hgens2''" as (omos2'' e2''' es2''' eV2'' eVs2'''' st2''')
            "(Ms◯2' & e2'''↦es2''' & e2''✓eV2'' & es2'''✓eVs2'''' & e2'''↪st2''' & _ & Pures)".
          iDestruct "Pures" as %(Hgens2'' & eVs2''''EV & NZst2''' & CASE).

          iDestruct (OmoAuth_OmoSnapOmo with "Ms●2 Ms◯2'") as %PREFIXomos2'.
          replace (S (S gens2) - 1) with (S gens2) in Hgens2'' by lia.
          rewrite -lookup_omo_wr_event in Hgens2''.
          eapply omo_prefix_lookup_Some in Hgens2''; [|exact PREFIXomos2'].
          rewrite lookup_omo_wr_event omo_insert_r_write_op Hes2' in Hgens2''. inversion Hgens2''. subst es2'''. clear Hgens2''.
          iDestruct (OmoCW_agree_2 with "e2'↦es2' e2'''↦es2'''") as %[_ <-].
          iDestruct (OmoSnap_agree with "e2'↪st2' e2'''↪st2'''") as %<-.
          rewrite Hvs2' in NZst2'''. done. }

    (* Now, we can collect all fractions into 1 *)
    rewrite last_lookup -omo_write_op_length in LASTesf2.
    replace (Init.Nat.pred (length omos2)) with (length omos2 - 1) in LASTesf2 by lia.
    rewrite LASTesf2 in Hgens2. inversion Hgens2. subst es2. clear Hgens2.
    iDestruct (OmoEinfo_agree with "esf2✓eVsf2 es2✓eVs2") as %<-.
    rewrite eVsf2EV in eVs2EV. inversion eVs2EV. subst Vs2. rewrite Hvs2 in H0. subst nsf2.
    have SZstf2 : size stf2.1.1.1 = 1 by lia. clear H0. rewrite SZstf2.

    apply size_1_elem_of in SZstf2 as [x EQstf2]. fold_leibniz.
    apply elem_of_dom_2 in Hsarc2e as eINdom. rewrite DOMsarc2 EQstf2 in eINdom. apply elem_of_singleton in eINdom. subst x.
    rewrite EQstf2 in DOMsarc2. apply dom_singleton_inv_L in DOMsarc2 as [x EQsarc2].
    rewrite EQsarc2 lookup_singleton in Hsarc2e. inversion Hsarc2e. subst x sarc2. clear Hsarc2e.
    rewrite map_fold_singleton_frac_sum /frac_sum /= in Hqsa2.

    iDestruct "Hty2" as %(-> & SZstf2 & _ & ->).
    apply size_1_elem_of in SZstf2 as [x EQstf2']. fold_leibniz.
    iDestruct "Hnsf2" as "(P1@Vp2 & [P1@Vsf2 _] & _ & e0↪ainfo & Hγb' & _ & %Hqd2)". subst qd2.
    iDestruct (ghost_map_lookup with "Hγwa2 e0↪ainfo") as %Hwarc2e0.
    apply elem_of_dom_2 in Hwarc2e0 as e0INdom. rewrite DOMwarc2 EQstf2' elem_of_singleton in e0INdom. subst x.
    rewrite EQstf2' in DOMwarc2. apply dom_singleton_inv_L in DOMwarc2 as [x EQwarc2].
    rewrite EQwarc2 lookup_singleton in Hwarc2e0. inversion Hwarc2e0. subst x warc2. clear Hwarc2e0.
    rewrite map_fold_singleton_frac_sum /frac_sum /= in Hqwa2.

    iCombine "Hγb Hγb' Hγb2" as "Hγb".
    have EQfrac : (ainfo.1.1.1.1/2 + (1/2/2 + (qsa2/2 + qwa2/2)) = 1)%Qp.
    { replace (ainfo.1.1.1.1/2 + (1/2/2 + (qsa2/2 + qwa2/2)))%Qp with ((ainfo.1.1.1.1 + qsa2)/2 + (1/2 + qwa2)/2)%Qp; last first.
      { rewrite !Qp.div_add_distr (Qp.add_assoc _ (1/2/2)%Qp) -(Qp.add_assoc _ (qsa2/2)%Qp (1/2/2)%Qp).
        by rewrite (Qp.add_comm (qsa2/2)%Qp (1/2/2)%Qp) (Qp.add_assoc _ (1/2/2)%Qp) -(Qp.add_assoc _ (qsa2/2)%Qp) -(Qp.add_assoc _ (1/2/2)%Qp). }
      rewrite Hqsa2 Hqwa2 Qp.half_half. done. }
    rewrite EQfrac. iMod (ghost_var_update false with "Hγb") as "Hγb". (* Signals deallocation of Arc *)
    rewrite -{19}EQfrac. iDestruct "Hγb" as "[Hγb [Hγb' Hγb'']]".

    iDestruct (view_at_mono_2 _ V2 with "P1@Vp2") as "P1@V2".
    { have COND1 : ({[e := ainfo1]} : gmap event_id ainfo_type) !! e = Some ainfo1 by rewrite lookup_singleton.
      apply LEsarc2 in COND1. subst ainfo1. simpl in *. have LE1 : ainfo.1.1.1.2 ⊑ V0'' by solve_lat. solve_lat. }
    iDestruct (view_at_mono_2 _ V2 with "P1@Vsf2") as "P1@V2'"; [solve_lat|].
    iDestruct (view_at_mono_2 _ V2 with "P1@V0''") as "P1@V2''"; [solve_lat|].
    iCombine "P1@V2 P1@V2' P1@V2''" as "P1@V2". rewrite Qp.add_assoc -EQqsa2 (Qp.add_comm qsa2) Hqsa2.

    (* Commit a [Unique] event *)
    have LeV0V2 : V0 ⊑ V2 by clear -LeV0'V0'' LeV0''V1 LeV1Vs2V2; solve_lat.
    set opId := length E2.
    (* FIXME: `set M2 : eView := {[opId]} ∪ (M ∪ stf2.1.2 ∪ stf2.2.2).` causes failure in applying OmoAuth_insert_ro_gen. *)
    have [Mop HMop] : ∃ (Mop : eView), Mop = {[opId]} by eexists.
    set M2 : eView := Mop ∪ (M ∪ stf2.1.2 ∪ stf2.2.2).
    set eVop := mkOmoEvent (Unique e) V2 M2.

    iDestruct (view_at_mono_2 _ V2 with "⊒M@V0''") as "⊒M@V2"; [clear -LeV0''V1 LeV1Vs2V2; solve_lat|].
    iDestruct (view_at_mono_2 _ V2 with "⊒stf2s@Vsf2") as "⊒stf2s@V2"; [clear -LeV1Vs2V2; solve_lat|].
    iDestruct (OmoAuth_swriter_token_agree_obj_2 with "Mw●2 omow↦2 SW") as %EQomow1'2.
    rewrite last_lookup -omo_write_op_length in LASTewf2.
    replace (Init.Nat.pred (length omow2)) with (length omow2 - 1) in LASTewf2 by lia.
    rewrite omo_write_op_length -EQomow1'2 Homow1' omo_append_w_write_op app_length /= Nat.add_sub lookup_app_1_eq in LASTewf2.
    inversion LASTewf2. subst ewf2. clear LASTewf2.
    iDestruct (OmoEinfo_agree with "ewn1✓eVwn1 ewf2✓eVwf2") as %<-.
    rewrite eVwn1EV in eVwf2EV. inversion eVwf2EV. subst Vwf2. clear eVwf2EV.
    iDestruct (view_at_mono_2 _ V2 with "⊒stf2w@Vwf2") as "⊒stf2w@V2"; [clear -LeVm1V1 LeV1Vs2V2; solve_lat|].
    iDestruct (OmoEview_union_obj with "⊒M@V2 ⊒stf2s@V2") as "⊒M'@V2".
    iDestruct (OmoEview_union_obj with "⊒M'@V2 ⊒stf2w@V2") as "⊒M2@V2".

    iMod "AU" as (????) "[>M●2' [_ Commit]]".
    iDestruct (OmoAuth_agree with "M●2 M●2'") as %(<- & <- & <- & <-). iCombine "M●2 M●2'" as "M●2".
    iDestruct (OmoAuth_OmoEview_obj with "M●2 ⊒M2@V2") as %VALM2.
    iDestruct (OmoAuth_omo_nonempty with "M●2") as %Nomo2.
    have NZomo2 : length omo2 ≠ 0 by destruct omo2; try done; lia.

    iMod (OmoAuth_insert_ro_gen _ _ _ _ _ _ _ _ _ _ (length omo2 - 1) with "M●2 ⊒M2@V2 RCOMMIT []") as
      "(M●2 & #⊒M2'@V2 & #opId↦esn2 & #opId↪stf2 & #opId✓eVop & RCOMMIT)".
    { rewrite EQlenST2. replace (length stlist2 - 1) with (Init.Nat.pred (length stlist2)) by lia. rewrite -last_lookup.
      have ? : step opId eVop stf2 stf2.
      { apply (arc_step_Unique _ _ e); try done.
        - subst eVop M2. simpl. rewrite HMop. set_solver-.
        - subst eVop. simpl. clear -GeVsf2 GeVwf2 LeVm1V1 LeV1Vs2V2. solve_lat. }
      iPureIntro. split_and!; try done.
      - unfold OmoUBgen. intros. replace (Init.Nat.pred (length stlist2)) with (length stlist2 - 1) by lia.
        apply VALM2 in H. eapply lookup_omo_surjective in H as [eidx Heidx]; [|done].
        exists eidx. split; [done|]. apply lookup_omo_lt_Some in Heidx. lia.
      - subst eVop M2 Mop. simpl. set_solver. }

    iMod (OmoHb_new_2 _ _ _ _ _ _ _ _ (length Es2) ({[length Es2]} ∪ Ms') with "M●2 [] opId✓eVop") as "[M●2 #opId⊒esn2]".
    { set_solver-. } { iFrame "#". }
    iDestruct (OmoHbToken_finish with "M●2") as "[M●2 M●2']".

    iMod ("Commit" $! true V2 with "[$⊒V2 $M●2' $⊒M2'@V2 $P1@V2 $RCOMMIT]") as "HΦ".
    { iPureIntro. split_and!; try done; [set_solver-|]. by subst eVop M2 Mop. }

    (* Obtain na points-to from append_only_loc *)
    rewrite !map_fold_singleton_view_join_total /view_join_total /= in LeVbs2Vbw2.
    have LE1 : ainfo.1.1.1.2 ⊑ V2 by clear -LeV0'V0'' LeV0''V1 LeV1Vs2V2; solve_lat.
    have LE2: V1 ⊑ V2 by clear -LeV1Vs2V2; solve_lat.
    have LE3 : Vp2 ⊑ V2.
    { have LE : Vp2 ⊑ ainfo1.1.1.1.2 by apply (LEsarc2 e ainfo1); rewrite lookup_singleton. solve_lat. }
    have [LE4 LE5] : Vsf2 ⊑ V2 ∧ Vm1 ⊑ V2 by clear -GeVsf2 GeVwf2 LeVm1V1 LeV1Vs2V2 LeVm1V1; solve_lat.
    have LE6 : Vbs2 ⊔ Vbw2 ⊑ V2 by clear -LE1 LE2 LE3 LE4 LE5 LeVbs2Vbw2; solve_lat.
    have [LE7 LE8] : Vbs2 ⊑ V2 ∧ Vbw2 ⊑ V2 by clear -LE6; solve_lat.
    iDestruct (view_at_mono_2 _ V2 with "omow↦2") as "omow↦2"; [done|].
    iDestruct (view_at_mono_2 _ V2 with "omos↦2") as "omos↦2"; [solve_lat|].
    iDestruct (view_at_elim with "⊒V2 omow↦2") as "omow↦2".
    iDestruct (view_at_elim with "⊒V2 omos↦2") as "omos↦2".
    iMod (append_only_loc_to_na with "HInv Ms●2 omos↦2") as (vs esf eVsf)
      "(l↦ & [Ms●2 _] & #esf✓eVsf & [%LASTesf %eVsfEV])"; [solve_ndisj|].
    iMod (append_only_loc_to_na with "HInv Mw●2 omow↦2") as (vw ewf eVwf)
      "(l↦1 & [Mw●2 _] & #ewf✓eVwf & [%LASTewf %eVwfEV])"; [solve_ndisj|].

    rewrite omo_insert_r_write_op last_lookup -omo_write_op_length in LASTesf.
    replace (Init.Nat.pred (length omos2)) with (length omos2 - 1) in LASTesf by lia.
    rewrite LASTesf2 in LASTesf. inversion LASTesf. subst esf.
    iDestruct (OmoEinfo_agree with "esf2✓eVsf2 esf✓eVsf") as %<-.
    rewrite eVsf2EV /= in eVsfEV. subst vs. rewrite EQstf2 size_singleton.

    rewrite -EQomow1'2 Homow1' omo_append_w_write_op last_snoc in LASTewf. inversion LASTewf. subst ewf.
    iDestruct (OmoEinfo_agree with "ewn1✓eVwn1 ewf✓eVwf") as %<-.
    rewrite eVwn1EV /= in eVwfEV. subst vw.

    iMod ("Hclose" with "[M●2 Ms●2 Mw●2 Hγb'' Hγsa2 Hγwa2 Hγm2]") as "_"; [repeat iExists _; iFrame "HN M●2 Ms●2 Mw●2 Hγb'' Hγsa2 Hγwa2 Hγm2"|].

    iModIntro. wp_pures. rewrite -[Z.to_nat 1]/(1%nat). wp_write. iApply ("HΦ" with "[$l↦ $l↦1]").
  - (* Read non-`1` value from strong counter. Commit nothing *)
    set ainfo2 := (ainfo1.1.1.1.1, ainfo1.1.1.1.2 ⊔ V2, ainfo1.1.1.2, ainfo1.1.2, swriter).
    set sarc2' := <[e := ainfo2]> (delete e sarc2).
    iMod (ghost_map_delete with "Hγsa2 e↪ainfo1") as "Hγsa2".
    iMod (ghost_map_insert e ainfo2 with "Hγsa2") as "[Hγsa2 e↪ainfo2]"; [by apply lookup_delete|].

    iAssert (⌜ ¬is_unique_must_success E2 stlist2 M e ⌝)%I with "[-]" as %FAIL.
    { unfold not, is_unique_must_success. iIntros (H). destruct H as (stf & LASTstf & H1 & H2 & INCL).

      (* Next strong counter message must exist in this case *)
      destruct (decide (gens2 = length omos2 - 1)) as [->|NEQ].
      { rewrite last_lookup -omo_write_op_length in LASTesf2.
        replace (Init.Nat.pred (length omos2)) with (length omos2 - 1) in LASTesf2 by lia.
        rewrite LASTesf2 in Hgens2. inversion Hgens2. subst es2.
        iDestruct (OmoEinfo_agree with "esf2✓eVsf2 es2✓eVs2") as %<-.
        rewrite eVsf2EV in eVs2EV. inversion eVs2EV. subst nsf2 Vs2.
        rewrite LASTstf2 in LASTstf. inversion LASTstf. subst stf.
        have EQsz : size stf2.1.1.1 = size st2.1.1.1 by lia.
        rewrite -EQsz H1 size_singleton in Hvs2. done. }

      have [es2' Hes2'] : is_Some (omo_write_op omos2 !! (gens2 + 1)%nat).
      { rewrite lookup_lt_is_Some. apply lookup_lt_Some in Hgens2. rewrite omo_write_op_length in NEQ. lia. }
      iDestruct (big_sepL_lookup with "AllStrongs2") as (e2' st2' eVs2')
        "(e2'↦es2' & e2'⊒es2' & _ & es2'✓eVs2' & MONO✓e2' & _)"; [exact Hes2'|].
      iDestruct (OmoAuth_OmoCW_l with "M●2 e2'↦es2'") as %He2'. apply INCL in He2'.
      iDestruct (OmoHb_HbIncluded with "e2'⊒es2' M1⊢Ms'") as %es2'Ms'; [set_solver +He2'|].
      iDestruct (big_sepS_elem_of with "MAXes2") as "es2'≤es2"; [exact es2'Ms'|].
      iDestruct (OmoLe_Le _ _ _ _ _ _ (wr_event (gens2 + 1)) (wr_event gens2) with "Ms●2 es2'≤es2") as %LE;
      try (by rewrite lookup_omo_wr_event omo_insert_r_write_op). simpl in LE. lia. }

    have LeV0V2 : V0 ⊑ V2 by clear -LeV0'V0'' LeV0''V1 LeV1Vs2V2; solve_lat.
    iMod "AU" as (????) "[>M●2' [_ Commit]]".
    iDestruct (OmoAuth_agree with "M●2 M●2'") as %(<- & <- & <- & <-).
    have LeV0''V2 : V0'' ⊑ V2 by clear -LeV0''V1 LeV1Vs2V2; solve_lat.
    iMod ("Commit" $! false V2 _ _ M with "[$M●2' $⊒V2 $⊒M@V0'' $P1@V0'']") as "HΦ"; [done|].

    iMod ("Hclose" with "[-Hγb M⊢Mw' SW e↪ainfo2 HΦ Hγu1]") as "_".
    { repeat iExists _. iFrame "HN M●2 Ms●2 Mw●2 Hγsa2 Hγwa2 Hγb2 Hγm2". rewrite omo_insert_r_write_op.
      iNext. repeat iExists _. iFrame "AllEvents2 AllStrongs2 AllWeaks2 omos↦2 omow↦2 Hγu2 Hγd2 Hγl2 Hγul2 Hnsf2 P2
        ⊒stf2s@Vsf2 ⊒stf2w@Vwf2 ⊒upds2@Vwf2 ⊒ulcks2@Vwf2 esf2✓eVsf2 ewf2✓eVwf2". iSplitR.
      - iApply big_sepL_forall. iIntros "%i %ew %Hew".
        iDestruct (big_sepL_lookup with "AllLocks2") as (eVw z) "[ew✓eVw [%eVwEV %COND]]"; [exact Hew|].
        iExists eVw,z. iFrame "ew✓eVw". iPureIntro. split; [done|]. intros. apply COND in H. destruct H as [H|H]; [by left|].
        right. destruct H as (e' & ainfo' & He' & e'IN). destruct (decide (e' = e)) as [->|NEQ].
        + exists e,ainfo2. rewrite lookup_insert. split; [done|].
          rewrite Hsarc2e in He'. inversion He'. subst ainfo'. done.
        + exists e',ainfo'. rewrite lookup_insert_ne; [|done]. rewrite lookup_delete_ne; [|done]. done.
      - iDestruct "Hty2" as %(EQzwf & EQsz & SWCOND & ->). iPureIntro.
        eapply (sarc_update_1 _ _ _ ainfo2) in Hsarc2e as H; try done; [|solve_lat].
        eapply (sarc_update_2 _ _ _ ainfo2 _ _ _ _ lcks2 lcks2 ulcks2) in Hsarc2e as H0; try done. clear eVEV. des. split_and!; try done.
        + exists e,ainfo2. split_and!; [|by rewrite lookup_insert|done].
          apply elem_of_dom_2 in Hsarc2e. rewrite DOMsarc2 in Hsarc2e. done.
        + rewrite H0. replace ((Vbs2 ⊔ V2) ⊔ Vbw2) with ((Vbs2 ⊔ Vbw2) ⊔ V2) by solve_lat.
          replace ((((map_fold view_join_total Vp2 sarc2 ⊔ V2) ⊔ map_fold view_join_total Vp2 warc2) ⊔ Vsf2) ⊔ Vwf2) with
            ((((map_fold view_join_total Vp2 sarc2 ⊔ map_fold view_join_total Vp2 warc2) ⊔ Vsf2) ⊔ Vwf2) ⊔ V2) by solve_lat. solve_lat. }

    iModIntro. wp_pures. rewrite -[Z.to_nat 1]/(1%nat). wp_bind (_ <-ʳᵉˡ _)%E.

    (* Inv access 3 *)
    iInv "AInv" as "H" "Hclose".
    iDestruct "H" as (?? γs3 ???????) "(%&%&%& %sarc3 & %warc3 & %qsa3 & %qwa3 & %alive3 & %E3 & %Es3 & %Ew3 & %omo3 & %omos3 &
      %omow3 & %stlist3 & %mos3 & %mow3 & %Mono3 & >HN' & >M●3 & >Ms●3 & >Mw●3 & >Hγsa3 & >Hγwa3 & >Hγb3 & >Hγm3 & Alive3)".
    gname_agree with "HN HN'". iClear "HN'".
    iDestruct (ghost_var_agree with "Hγb Hγb3") as %<-.

    iDestruct "Alive3" as (Vbs3 Vbw3 ty3 uf3 stf3 esf3 ewf3 eVsf3 eVwf3 nsf3) "(%zwf3 & %Vsf3 & %Vwf3 & %Vp3 & %qsa3a & %qsa3b & %qu3 & %qd3 & %upds3 &
      %dgds3 & %lcks3 & %ulcks3 & >#AllEvents3 & >#AllStrongs3 & >#AllWeaks3 & >omos↦3 & >omow↦3 & >Hγu3 & >Hγd3 & >Hγl3 & >Hγul3 &
      >#AllLocks3 & [>#⊒upds3@Vwf3 >#⊒ulcks3@Vwf3] & >#esf3✓eVsf3 & >#ewf3✓eVwf3 & Hnsf3 & P2 & Hty3 & >#⊒stf3s@Vsf3 & >#⊒stf3w@Vwf3 & >Pures)".
    iDestruct "Pures" as %(Subuf3 & LASTesf3 & LASTewf3 & eVsf3EV & eVwf3EV & Hqsa3 & Hqwa3 & VALsarc3 & VALwarc3 & VALsarcwarc3 & SeenClone3 &
      SeenWeakClone3 & HInitWrite3 & LASTstf3 & DOMsarc3 & DOMwarc3 & EQqsa3 & Alive3 & VALeid3 & LeVbs3Vbw3 & GeVsf3 & GeVwf3 &
      SeenUpgrade3 & SeenDowngrade3 & SeenUnlock3 & LEsarc3 & LEwarc3 & VALstlist3 & LeVsf3 & EQnsf3).
    iDestruct (swriter_token_type_obj_2 with "SW omow↦3") as %->.
    iDestruct (OmoAuth_swriter_token_agree_obj_2 with "Mw●3 omow↦3 SW") as %EQomow1'3.
    iDestruct (ghost_map_lookup with "Hγsa3 e↪ainfo2") as %Hsarc3e.
    iDestruct (OmoSnapOmo_get with "Mw●3") as "#Mw◯3".
    iDestruct (OmoAuth_omo_nonempty with "Mw●3") as %Nomow3.

    wp_apply (append_only_loc_release_write _ _ _ _ _ _ _ _ _ _ _ _ _ emp with "[$Mw●3 $⊒Mw1 $SW $omow↦3 $⊒V2]"); [solve_ndisj|done|].
    iIntros (V3 eVwn3 ew3 eVw3) "(Pures & #⊒V3 & Mw●3 & _ & #ew3✓eVw3 & #ewn3✓eVwn3 & (SW@V3 & #⊒Mw3@V3 & _) & omow↦3)".
    iDestruct "Pures" as %(LASTew3 & LeV2V3 & NEqV2V3 & eVwn3EV & eVwn3SYNC).
    iDestruct "Hty3" as %(-> & SZstf3 & _ & ->).

    rewrite LASTewf3 in LASTew3. inversion LASTew3. subst ew3.
    iDestruct (OmoEinfo_agree with "ewf3✓eVwf3 ew3✓eVw3") as %<-. rewrite eVwf3EV /=.
    rewrite -EQomow1'3 Homow1' omo_append_w_write_op last_snoc in LASTewf3. inversion LASTewf3. subst ewf3.
    iDestruct (OmoEinfo_agree with "ewn1✓eVwn1 ew3✓eVw3") as %<-. rewrite eVwn1EV in eVwf3EV.
    inversion eVwf3EV. subst Vwf3.
    iDestruct (swriter_to_cas_only_obj_1 with "omow↦3 SW@V3") as "omow↦3".

    set ainfo3 := (ainfo2.1.1.1.1, ainfo2.1.1.1.2 ⊔ V2, ainfo2.1.1.2, ainfo2.1.2 ∪ {[length Ew3]}, cas_only).
    set sarc3' := <[e := ainfo3]> (delete e sarc3).
    iMod (ghost_map_delete with "Hγsa3 e↪ainfo2") as "Hγsa3".
    iMod (ghost_map_insert e ainfo3 with "Hγsa3") as "[Hγsa3 e↪ainfo3]"; [by apply lookup_delete|].

    (* Update ulcks3 *)
    set ulcks3' := ulcks3 ∪ {[length Ew3]}.
    apply size_1_elem_of in SZstf3 as [x Hstf3]. fold_leibniz.
    rewrite Hstf3 in DOMwarc3. apply dom_singleton_inv_L in DOMwarc3 as [x' Hwarc3].
    destruct nsf3.
    { symmetry in EQnsf3. apply size_empty_inv in EQnsf3. fold_leibniz. rewrite EQnsf3 dom_empty_iff_L in DOMsarc3. by rewrite DOMsarc3 in Hsarc3e. }
    iDestruct "Hnsf3" as "(P1@Vp3 & (P1@Vsf3 & #⊒dgds3@Vsf3 & #⊒lcks3@Vsf3) & #He0 & e0↪ainfo & Hγb' & Hγul & ->)".
    iDestruct (ghost_map_lookup with "Hγwa3 e0↪ainfo") as %Hwarc3e0.
    rewrite Hwarc3 lookup_singleton_Some in Hwarc3e0. destruct Hwarc3e0 as [-> ->].
    rewrite Hwarc3 map_fold_singleton_frac_sum /frac_sum /= Qp.add_comm in Hqwa3.
    iCombine "Hγul3 Hγul" as "Hγul3". rewrite Hqwa3.
    iMod (ghost_var_update ulcks3' with "Hγul3") as "Hγul3".
    rewrite -{14}Hqwa3. iDestruct "Hγul3" as "[Hγul3 Hγul]".

    iDestruct (ghost_var_agree with "Hγu1 Hγu3") as %<-. iCombine "Hγu1 Hγu3" as "Hγu3".
    have LeVwf3V3 : Vm1 ⊑ V3 by clear -LeVm1V1 LeV1Vs2V2 LeV2V3; solve_lat.
    iMod ("Hclose" with "[-HΦ Hγb e↪ainfo3]") as "_".
    { repeat iExists _. iFrame "HN M●3 Ms●3 Mw●3 Hγsa3 Hγwa3 Hγb3 Hγm3".
      iNext. do 9 iExists _. iExists (S nsf3),_,Vsf3,V3. repeat iExists _.
      iDestruct (view_at_mono_2 _ V3 with "⊒ulcks3@Vwf3") as "⊒ulcks3@V3"; [solve_lat|].
      iDestruct (OmoEview_union_obj with "⊒ulcks3@V3 ⊒Mw3@V3") as "⊒ulcks3Mw3@V3".
      iDestruct (OmoEview_mono_obj _ _ ulcks3' with "⊒ulcks3Mw3@V3") as "⊒ulcks3'@V3"; [set_solver-|set_solver-|].
      iFrame "AllEvents3 AllStrongs3 omos↦3 omow↦3 Hγu3 Hγd3 Hγl3 Hγul3 esf3✓eVsf3 ewn3✓eVwn3".
      iFrame "P1@Vp3 P1@Vsf3 e0↪ainfo Hγb' ⊒upds3@Vwf3 Hγul ⊒dgds3@Vsf3 ⊒lcks3@Vsf3 ⊒stf3s@Vsf3 ⊒stf3w@Vwf3 ⊒ulcks3'@V3 He0".
      rewrite omo_append_w_write_op. iSplitR; last iSplitR; last iSplitR; last iSplitL; last iSplit.
      - iApply big_sepL_snoc. iSplit.
        + iApply big_sepL_forall. iIntros "%i %ew %Hew".
          iDestruct (big_sepL_lookup with "AllWeaks3") as (eVw zw) "(ew✓eVw & HeVw & Hi)"; [exact Hew|].
          iExists eVw,zw. iFrame "ew✓eVw HeVw". destruct i; [done|].
          iDestruct "Hi" as (omow ew' eVw' zw') "(Mw◯ & ew'✓eVw' & H1 & CASE)".
          iExists omow,ew',eVw',zw'. iFrame "Mw◯ ew'✓eVw' H1".
          iDestruct "CASE" as "[CASE|[CASE|[CASE|(-> & -> & %ewIN)]]]"; [by iLeft|by iRight;iLeft|by iRight;iRight;iLeft|].
          iRight. iRight. iRight. iPureIntro. split_and!; try done. set_solver +ewIN.
        + iExists eVwn3,1%Z. iFrame "ewn3✓eVwn3". rewrite eVwn3EV. iSplit; [done|].
          rewrite -omo_write_op_length. destruct (length omow3) eqn:Hlen; [by destruct omow3|]. rewrite -Hlen. clear Hlen n.
          iExists omow3,(length Ew1),eVwn1,(-1)%Z. iFrame "Mw◯3 ewn1✓eVwn1". iSplit.
          * by rewrite omo_write_op_length -EQomow1'3 Homow1' omo_append_w_write_op app_length /= Nat.add_sub lookup_app_1_eq eVwn1EV.
          * iRight. iRight. iRight. iPureIntro. split_and!; try done. set_solver-.
      - iApply big_sepL_snoc. iSplit.
        + iApply big_sepL_forall. iIntros "%i %ew %Hew".
          iDestruct (big_sepL_lookup with "AllLocks3") as (eVw z) "[ew✓eVw [%eVwEV %COND]]"; [exact Hew|].
          iExists eVw,z. iFrame "ew✓eVw". iPureIntro. split; [done|]. intros. apply COND in H. destruct H as [H|H]; [by left|].
          right. destruct H as (e' & ainfo' & He' & e'IN). destruct (decide (e' = e)) as [->|NEQ].
          * rewrite Hsarc3e in He'. inversion He'. subst ainfo'. exists e,ainfo3. rewrite lookup_insert.
            split; [done|]. subst ainfo3. clear -e'IN. set_solver.
          * exists e',ainfo'. rewrite lookup_insert_ne; [|done]. rewrite lookup_delete_ne; [|done]. done.
        + iExists eVwn3,1%Z. iFrame "ewn3✓eVwn3". rewrite eVwn3EV. done.
      - done.
      - destruct (warc3 !! 0); [done|]. iFrame "P2".
      - iSplit; [|done]. iRight. iLeft. iExists e,ainfo3. iPureIntro. rewrite lookup_insert. split; [done|]. set_solver-.
      - iPureIntro. eapply (sarc_update_1 _ _ _ ainfo3) in Hsarc3e as H; try done; [|solve_lat|set_solver-].
        eapply (sarc_update_2 _ _ _ ainfo3 _ _ _ _ lcks3 lcks3 ulcks3) in Hsarc3e as H0; try done; [|set_solver-].
        clear eVEV. des. split_and!; try done; [clear -Subuf3; set_solver|by rewrite last_snoc|..].
        + by rewrite eVwn3EV Hstf3 size_singleton.
        + by rewrite Hwarc3 map_fold_singleton_frac_sum /frac_sum /= Qp.add_comm.
        + by rewrite Hwarc3 dom_singleton_L.
        + rewrite H0. replace (Vbs3 ⊔ (Vbw3 ⊔ V3)) with ((Vbs3 ⊔ Vbw3) ⊔ V3) by solve_lat. clear -LeVbs3Vbw3 LeVm1V1 LeV1Vs2V2 LeV2V3. solve_lat.
        + solve_lat.
        + unfold SeenUnlock. intros. destruct (decide (e0 = length Ew3)) as [->|NEQ].
          * right. exists e,ainfo3. rewrite lookup_insert. split; [done|]. set_solver-.
          * apply H2. set_solver +H8 NEQ. }

    iModIntro. wp_pures. rewrite bool_decide_false; [|lia]. iApply "HΦ".
    iExists V3. iFrame "⊒V3". iSplit; [|done]. repeat iExists _. replace ainfo.1.1.1.1 with ainfo3.1.1.1.1; [|done].
    iFrame "HN AInv ⊒M@V0'' ⊒Ms@V0'' ⊒Mw3@V3 e✓eV e↪ainfo3 Hγb". iSplit.
    + iApply view_at_unfold. rewrite monPred_at_in. iPureIntro. clear -LeV0'V0'' LeV0''V1 LeV1Vs2V2 LeV2V3. solve_lat.
    + iPureIntro. split_and!; try done. clear -SubainfoMw SubMwMw'. set_solver.
Qed.

End Arc.

Definition arc_impl `{!noprolG Σ, !atomicG Σ, !arcG Σ}
  : arc_spec Σ := {|
    spec_composition.ArcInv_Linearizable := ArcInv_Linearizable_instance;
    spec_composition.ArcInv_OmoAuth_acc := ArcInv_OmoAuth_acc_instance;
    spec_composition.StrongArc_OmoEview := StrongArc_OmoEview_instance;
    spec_composition.WeakArc_OmoEview := WeakArc_OmoEview_instance;
    spec_composition.FakeArc_OmoEview := FakeArc_OmoEview_instance;
    spec_composition.StrongArc_Eview_update := StrongArc_Eview_update_instance;
    spec_composition.WeakArc_Eview_update := WeakArc_Eview_update_instance;
    spec_composition.FakeArc_Eview_update := FakeArc_Eview_update_instance;

    spec_composition.create_strong := create_strong;
    spec_composition.create_weak := create_weak;
    spec_composition.strong_count_spec := strong_count_spec;
    spec_composition.weak_count_spec := weak_count_spec;
    spec_composition.clone_arc_spec := clone_arc_spec;
    spec_composition.downgrade_spec := downgrade_spec;
    spec_composition.clone_weak_spec := clone_weak_spec;
    spec_composition.upgrade_spec := upgrade_spec;
    spec_composition.drop_weak_spec := drop_weak_spec;
    spec_composition.drop_fake_spec := drop_fake_spec;
    spec_composition.drop_arc_spec := drop_arc_spec;
    spec_composition.try_unwrap_spec := try_unwrap_spec;
    spec_composition.is_unique_spec := is_unique_spec;
    spec_composition.try_unwrap_full_spec := try_unwrap_full_spec;
  |}.
