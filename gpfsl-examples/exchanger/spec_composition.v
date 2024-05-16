From gpfsl.examples Require Import sflib.

From stdpp Require Import namespaces.

From gpfsl.logic Require Import logatom.

From gpfsl.examples.omo Require Export omo omo_preds append_only_loc.

Require Import iris.prelude.options.

Local Open Scope Z_scope.

Inductive xchg_event :=
  Init                        (* Initialization event *)
| Reg (v : Z)                 (* Registers an offer with value [v] *)
| Ack (e : event_id) (v : Z)  (* Acknowledges the acceptance of an offer [e], and reads exchanged value [v] *)
| Rvk (e : event_id)          (* Revokes an offer [e] *)
| Acp (v' v : Z)              (* Accepts an existing offer with value [v'] and puts [v] in turn *)
.
Notation xchg_state_l := (gmap event_id (Z * view * eView))%type.
Notation xchg_state_r := (gmap event_id (event_id * Z * view * eView))%type.
Notation xchg_state := (xchg_state_l * xchg_state_r)%type.

Local Notation history := (history xchg_event).
Implicit Types (E : history) (st : xchg_state) (stl : xchg_state_l) (str : xchg_state_r).

Inductive xchg_step : ∀ (e : event_id) (eV : omo_event xchg_event) st st', Prop :=
  | xchg_step_Init eV
    (INIT : eV.(type) = Init)
    (LVIEW : eV.(eview) = {[0%nat]})
    : xchg_step 0%nat eV (∅, ∅) (∅, ∅)
  | xchg_step_Reg e eV v stl str
    (REG : eV.(type) = Reg v)
    (LE : 0 ≤ v)
    (LVIEW : e ∈ eV.(eview))
    (FRESHl : stl !! e = None)
    (FRESHr : str !! e = None)
    : xchg_step e eV (stl, str) (<[ e := (v, eV.(sync), eV.(eview)) ]> stl, str)
  | xchg_step_Ack e eV e' e'' v V lV stl str
    (ACK : eV.(type) = Ack e' v)
    (LE : 0 ≤ v)
    (SYNC : V ⊑ eV.(sync))
    (LVIEW : {[e; e'']} ∪ lV ⊆ eV.(eview))
    (ACKS : str !! e' = Some (e'', v, V, lV))
    : xchg_step e eV (stl, str) (stl, str)
  | xchg_step_Rvk e eV e' stl str
    (RVK : eV.(type) = Rvk e')
    (LVIEW : e ∈ eV.(eview))
    (ACKS : is_Some (stl !! e'))
    : xchg_step e eV (stl, str) (delete e' stl, str)
  | xchg_step_Acp e eV v e' v' V' lV' stl str
    (ACP : eV.(type) = Acp v' v)
    (LE : 0 ≤ v)
    (SYNC : V' ⊑ eV.(sync))
    (LVIEW : {[e; e']} ∪ lV' ⊆ eV.(eview))
    (ACKS : stl !! e' = Some (v', V', lV'))
    (FRESH : str !! e' = None)
    : xchg_step e eV (stl, str) (delete e' stl, <[ e' := (e, v, eV.(sync), eV.(eview)) ]> str)
  .

Global Instance xchg_interpretable : Interpretable xchg_event xchg_state :=
  {
    init := (∅, ∅);
    step := xchg_step
  }.

Definition ExchangerLocalT Σ : Type :=
  ∀ (γg : gname) (l : loc) (M : eView), vProp Σ.
Definition ExchangerLocalNT Σ : Type :=
  ∀ (N : namespace), ExchangerLocalT Σ.
Definition ExchangerInvT Σ : Type :=
  ∀ (γg γs : gname) (l : loc) (E : history) (omo : omoT) (stlist : list xchg_state), vProp Σ.
Definition CheckTokenT Σ : Type :=
  ∀ (γg : gname) (l l' : loc) (e : event_id), vProp Σ.

Definition new_exchanger_spec' {Σ} `{!noprolG Σ, !omoGeneralG Σ}
  (new_exchanger : val) (ExchangerLocal : ExchangerLocalNT Σ) (ExchangerInv : ExchangerInvT Σ) : Prop :=
  ∀ N tid V,
  {{{ ⊒V }}}
    new_exchanger [] @ tid; ⊤
  {{{ γg γs (l: loc) V' M, RET #l;
      let eVinit := mkOmoEvent Init V' M in
      let E := [eVinit] in
      let initst : xchg_state := (∅, ∅) in
      ⊒V' ∗ ExchangerInv γg γs l E (omo_append_w [] 0%nat []) [initst] ∗ @{V'} ExchangerLocal N γg l M ∗
      OmoTokenW γg 0%nat ∗
      ⌜ V ⊑ V' ⌝}}}.

Definition new_offer_spec' {Σ} `{!noprolG Σ, !omoGeneralG Σ}
  (new_offer : val) (ExchangerLocal : ExchangerLocalNT Σ) (ExchangerInv : ExchangerInvT Σ) (CheckToken : CheckTokenT Σ) : Prop :=
  ∀ N (DISJ: N ## histN) (l: loc) tid γg M (V : view) (v : Z) (LEv: 0 ≤ v),
  (* PRIVATE PRE *)
  ⊒V -∗ ExchangerLocal N γg l M -∗
  (* PUBLIC PRE *)
  <<< ∀ γs E omo stlist, ▷ ExchangerInv γg γs l E omo stlist >>>
    new_offer [ #l; #v] @tid; ↑N
  <<< ∃ (v' : lit) V' E' omo' stlist' M',
      (* PUBLIC POST *)
      ⊒V' ∗ ▷ ExchangerInv γg γs l E' omo' stlist' ∗ @{V'} ExchangerLocal N γg l M' ∗
      if decide (v' = 0%V) then (
        ⌜ E' = E ∧ omo' = omo ∧ stlist' = stlist ∧ M' = M ⌝ (* FAIL_RACE case *)
      ) else (
        ⌜ (∃ (l' : loc), v' = l'%V) ∧
          V ⊑ V' ∧
          omo' = omo_append_w omo (length E) [] ∧ (∃ st, stlist' = stlist ++ [st]) ∧
          E' = E ++ [mkOmoEvent (Reg v) V' M'] ∧ M ⊆ M' ⌝ ∗
        OmoTokenW γg (length E)
      ),
      RET #v', if decide (v' = 0%V) then emp else ∃ (l' : loc), ⌜ v' = l'%V ⌝ ∗ CheckToken γg l l' (length E) >>>
  .

Definition check_offer_spec' {Σ} `{!noprolG Σ, !omoGeneralG Σ}
  (check_offer : val) (ExchangerLocal : ExchangerLocalNT Σ) (ExchangerInv : ExchangerInvT Σ) (CheckToken : CheckTokenT Σ) : Prop :=
  ∀ N (DISJ: N ## histN) (l l': loc) tid γg M (V : view) e,
  (* PRIVATE PRE *)
  ⊒V -∗ ExchangerLocal N γg l M -∗ CheckToken γg l l' e -∗
  (* PUBLIC PRE *)
  <<< ∀ γs E omo stlist P, ▷ ExchangerInv γg γs l E omo stlist ∗ ▷ P >>>
    check_offer [ #l; #l'] @tid; ↑N
  <<< ∃ (v : Z) V' op omo' stlist' M',
      (* PUBLIC POST *)
      let eVop := mkOmoEvent op V' M' in
      let E' := E ++ [eVop] in
      P ∗ ⊒V' ∗ ▷ ExchangerInv γg γs l E' omo' stlist' ∗ @{V'} ExchangerLocal N γg l M' ∗
      ⌜ V ⊑ V' ∧ M ⊆ M' ⌝ ∗
      if decide (v = -1) then ( (* CANCELLED case *)
        ⌜ op = Rvk e ∧ omo' = omo_append_w omo (length E) []
        ∧ (∃ st, stlist' = stlist ++ [st]) ⌝ ∗
        OmoTokenW γg (length E)
      ) else (
        ⌜ 0 ≤ v ∧ op = Ack e v ∧ stlist' = stlist ∧ omo' = omo_insert_r omo (length omo - 1)%nat (length E) ⌝ ∗
        OmoTokenR γg (length E)
      ),
      RET #v, emp >>>
  .

Definition take_offer_spec' {Σ} `{!noprolG Σ, !omoGeneralG Σ}
  (take_offer : val) (ExchangerLocal : ExchangerLocalNT Σ) (ExchangerInv : ExchangerInvT Σ) : Prop :=
  ∀ N (DISJ: N ## histN) (l: loc) tid γg M (V : view) (v : Z) (LEv: 0 ≤ v),
  (* PRIVATE PRE *)
  ⊒V -∗ ExchangerLocal N γg l M -∗
  (* PUBLIC PRE *)
  <<< ∀ γs E omo stlist P, ▷ ExchangerInv γg γs l E omo stlist ∗ ▷ P >>>
    take_offer [ #l; #v] @tid; ↑N
  <<< ∃ (v' : Z) V' E' omo' stlist' M',
      (* PUBLIC POST *)
      P ∗ ⊒V' ∗ ▷ ExchangerInv γg γs l E' omo' stlist' ∗ @{V'} ExchangerLocal N γg l M' ∗
      ⌜ V ⊑ V' ∧ M ⊆ M' ⌝ ∗
      if decide (v' = -1) then ( (* CANCELLED case *)
        ⌜ E' = E ∧ omo' = omo ∧ stlist' = stlist ∧ M = M' ⌝
      ) else (
        ⌜ E' = E ++ [mkOmoEvent (Acp v' v) V' M'] ∧ omo' = omo_append_w omo (length E) [] ∧ (∃ st, stlist' = stlist ++ [st]) ⌝ ∗
        OmoTokenW γg (length E)
      ),
      RET #v', emp >>>
  .

Record xchg_spec {Σ} `{!noprolG Σ, !omoGeneralG Σ, !omoSpecificG Σ xchg_event xchg_state} := ExchangerSpec {
  (** operations *)
  new_exchanger : val;
  new_offer : val;
  check_offer : val;
  take_offer : val;

  (** These are common elements in arbitrary composable linearizability spec *)
  (** predicates *)
  ExchangerLocal : ExchangerLocalNT Σ;
  ExchangerInv : ExchangerInvT Σ;
  CheckToken : CheckTokenT Σ;

  (** predicates properties *)
  ExchangerInv_Objective : ∀ γg γs l E omo stlist, Objective (ExchangerInv γg γs l E omo stlist);
  ExchangerInv_Timeless : ∀ γg γs l E omo stlist, Timeless (ExchangerInv γg γs l E omo stlist);
  ExchangerInv_Linearizable : ∀ γg γs l E omo stlist, ExchangerInv γg γs l E omo stlist ⊢ ⌜ Linearizability E ⌝;
  ExchangerInv_OmoAuth_acc : ∀ γg γs l E omo stlist,
    ExchangerInv γg γs l E omo stlist ⊢ OmoAuth γg γs (1/2)%Qp E omo stlist _ ∗ (OmoAuth γg γs (1/2)%Qp E omo stlist _ -∗ ExchangerInv γg γs l E omo stlist);
  ExchangerLocal_OmoEview : ∀ N γg l M, ExchangerLocal N γg l M ⊢ OmoEview γg M;
  ExchangerLocal_Persistent :
    ∀ N γg l M, Persistent (ExchangerLocal N γg l M);
  CheckToken_Timeless:
    ∀ γg l l' e, Timeless (CheckToken γg l l' e);
  (**************************************************************)

  (* operations specs *)
  new_exchanger_spec : new_exchanger_spec' new_exchanger ExchangerLocal ExchangerInv;
  new_offer_spec : new_offer_spec' new_offer ExchangerLocal ExchangerInv CheckToken;
  check_offer_spec : check_offer_spec' check_offer ExchangerLocal ExchangerInv CheckToken;
  take_offer_spec : take_offer_spec' take_offer ExchangerLocal ExchangerInv;
}.

Arguments xchg_spec _ {_ _ _}.
Global Existing Instances ExchangerInv_Objective ExchangerInv_Timeless ExchangerLocal_Persistent CheckToken_Timeless.
