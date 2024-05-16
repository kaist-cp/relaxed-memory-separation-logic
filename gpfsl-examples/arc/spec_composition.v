From gpfsl.examples Require Import sflib.

From iris.bi Require Import fractional.
From stdpp Require Import namespaces.

From gpfsl.logic Require Import logatom atomics invariants.
From gpfsl.logic Require Import repeat_loop new_delete.

From gpfsl.examples.omo Require Export omo omo_preds append_only_loc.

Require Import iris.prelude.options.

Local Open Scope nat_scope.

Inductive arc_event :=
  StrongInit                              (* Write,     strong count = 1, weak count = 1 *)
| WeakInit                                (* Write,     strong count = 0, weak count = 1 *)
| Clone       (e : event_id)              (* Write,     strong count += 1 *)
| WeakClone   (e : event_id)              (* Write,     weak count += 1 *)
| Downgrade                               (* Write,     weak count += 1 *)
| Upgrade                                 (* Write,     strong count += 1 *)
| UpgradeFail                             (* Read-only, strong count == 0 *)
| WeakDrop    (e : event_id) (b : bool)   (* Write,     weak count -= 1 *)
| StrongDrop  (e : event_id) (b : bool)   (* Write,     strong count -= 1 *)
| UnwrapFail  (e : event_id)              (* Read-only, strong count > 1 *)
| Unique      (e : event_id)              (* Read-only, strong count == weak count == 1 *)
.
(* (set of active arc objects) * (released view by [drop_arc] or [drop_weak]) * released eView *)
Notation arc_state_each := ((gset event_id) * view * eView)%type.
(* (strong counter state) * (weak counter state) *)
Notation arc_state := (arc_state_each * arc_state_each)%type.
Global Instance arc_event_inhabited : Inhabited arc_event := populate StrongInit.

Local Notation history := (history arc_event).
Implicit Types (E : history) (st : arc_state) (stl str : arc_state_each) (stlist : list arc_state).

Inductive arc_step : ∀ (e : event_id) (eV : omo_event arc_event) st st', Prop :=
  | arc_step_StrongInit eV
    (EVENT : eV.(type) = StrongInit)
    (LVIEW : eV.(eview) = {[0]})
    (* due to fake arc, set of active weak arc initially contains 0 *)
    : arc_step 0 eV ((∅, ∅, ∅), (∅, ∅, ∅)) (({[0]}, eV.(sync), eV.(eview)), ({[0]}, eV.(sync), eV.(eview)))
  | arc_step_WeakInit eV
    (EVENT : eV.(type) = WeakInit)
    (LVIEW : eV.(eview) = {[0]})
    : arc_step 0 eV ((∅, ∅, ∅), (∅, ∅, ∅)) ((∅, eV.(sync), eV.(eview)), ({[0]}, eV.(sync), eV.(eview)))
  | arc_step_Clone e eV e' st st'
    (EVENT : eV.(type) = Clone e')
    (LVIEW : e ∈ eV.(eview))
    (IDVAL : e' ∈ st.1.1.1)
    (FRESH : e ∉ st.1.1.1)
    (NST : st' = ((st.1.1.1 ∪ {[e]}, st.1.1.2, st.1.2), st.2))
    : arc_step e eV st st'
  | arc_step_WeakClone e eV e' st st'
    (EVENT : eV.(type) = WeakClone e')
    (LVIEW : e ∈ eV.(eview))
    (IDVAL : e' ∈ st.2.1.1)
    (FRESH : e ∉ st.2.1.1)
    (NST : st' = (st.1, (st.2.1.1 ∪ {[e]}, st.2.1.2, st.2.2)))
    : arc_step e eV st st'
  | arc_step_Downgrade e eV st st'
    (EVENT : eV.(type) = Downgrade)
    (LVIEW : e ∈ eV.(eview))
    (IDVAL : st.1.1.1 ≠ ∅)
    (FRESH : e ∉ st.2.1.1)
    (NST : st' = (st.1, (st.2.1.1 ∪ {[e]}, st.2.1.2, st.2.2)))
    : arc_step e eV st st'
  | arc_step_Upgrade e eV st st'
    (EVENT : eV.(type) = Upgrade)
    (LVIEW : e ∈ eV.(eview))
    (NEMP : st.1.1.1 ≠ ∅)
    (FRESH : e ∉ st.1.1.1)
    (NST : st' = ((st.1.1.1 ∪ {[e]}, st.1.1.2, st.1.2), st.2))
    : arc_step e eV st st'
  | arc_step_UpgradeFail e eV st
    (EVENT : eV.(type) = UpgradeFail)
    (LVIEW : e ∈ eV.(eview))
    (EMP : st.1.1.1 = ∅)
    : arc_step e eV st st
  | arc_step_WeakDrop e eV e' st st'
    (EVENT : eV.(type) = WeakDrop e' false)
    (LVIEW : e ∈ eV.(eview))
    (STRICT : {[e']} ⊂ st.2.1.1)
    (NST : st' = (st.1, (st.2.1.1 ∖ {[e']}, st.2.1.2 ⊔ eV.(sync), st.2.2 ∪ eV.(eview))))
    : arc_step e eV st st'
  | arc_step_WeakDrop_last e eV e' st st'
    (EVENT : eV.(type) = WeakDrop e' true)
    (LVIEW : {[e]} ∪ st.1.2 ∪ st.2.2 ⊆ eV.(eview))
    (SYNC : st.1.1.2 ⊔ st.2.1.2 ⊑ eV.(sync))
    (STRONG : st.1.1.1 = ∅)
    (WEAK : st.2.1.1 = {[e']})
    (NST : st' = (st.1, (∅, st.2.1.2, st.2.2)))
    : arc_step e eV st st'
  | arc_step_StrongDrop e eV e' st st'
    (EVENT : eV.(type) = StrongDrop e' false)
    (LVIEW : e ∈ eV.(eview))
    (STRICT : {[e']} ⊂ st.1.1.1)
    (NST : st' = ((st.1.1.1 ∖ {[e']}, st.1.1.2 ⊔ eV.(sync), st.1.2 ∪ eV.(eview)), st.2))
    : arc_step e eV st st'
  | arc_step_StrongDrop_last e eV e' st st'
    (EVENT : eV.(type) = StrongDrop e' true)
    (LVIEW : {[e]} ∪ st.1.2 ⊆ eV.(eview))
    (SYNC : st.1.1.2 ⊑ eV.(sync))
    (STRONG : st.1.1.1 = {[e']})
    (NST : st' = ((∅, st.1.1.2, st.1.2), st.2))
    : arc_step e eV st st'
  | arc_step_UnwrapFail e eV e' st
    (EVENT : eV.(type) = UnwrapFail e')
    (LVIEW : e ∈ eV.(eview))
    (STRICT : {[e']} ⊂ st.1.1.1)
    : arc_step e eV st st
  | arc_step_Unique e eV e' st
    (EVENT : eV.(type) = Unique e')
    (LVIEW : {[e]} ∪ st.1.2 ∪ st.2.2 ⊆ eV.(eview))
    (SYNC : st.1.1.2 ⊔ st.2.1.2 ⊑ eV.(sync))
    (STRONG : st.1.1.1 = {[e']})
    (WEAK : st.2.1.1 = {[0]})
    : arc_step e eV st st
  .

Global Instance arc_interpretable : Interpretable arc_event arc_state :=
  {
    init := ((∅, ∅, ∅), (∅, ∅, ∅));
    step := arc_step
  }.

Definition ArcInvT Σ : Type :=
  ∀ (γg γs : gname) (l : loc) (E : history) (omo : omoT) (stlist : list arc_state), vProp Σ.
Definition StrongArcT Σ : Type :=
  ∀ (N : namespace) (γg : gname) (l : loc) (q : Qp) (P1 : Qp → vProp Σ) (P2 : vProp Σ) (M : eView) (e : event_id), vProp Σ.
Definition WeakArcT Σ : Type :=
  ∀ (N : namespace) (γg : gname) (l : loc) (P1 : Qp → vProp Σ) (P2 : vProp Σ) (M : eView) (e : event_id), vProp Σ.
Definition FakeArcT Σ : Type :=
  ∀ (N : namespace) (γg : gname) (l : loc) (P1 : Qp → vProp Σ) (P2 : vProp Σ) (M : eView), vProp Σ.

Definition create_strong' {Σ} `{!noprolG Σ, !omoGeneralG Σ} (ArcInv : ArcInvT Σ) (StrongArc : StrongArcT Σ) : Prop :=
  ∀ Ec l P1 P2 V N,
    (∀ q, AsFractional (P1 q) P1 q) →
    ⊒V -∗ l ↦ #1 -∗ (l >> 1) ↦ #1 -∗ P1 1%Qp ={Ec}=∗
      ∃ γg γs V' M q,
        let eVinit := mkOmoEvent StrongInit V' M in
        let E := [eVinit] in
        let initst := (({[0]}, V', {[0]}), ({[0]}, V', {[0]})) in
        ⊒V' ∗ ArcInv γg γs l E (omo_append_w [] 0 []) [initst] ∗ @{V'} (StrongArc N γg l q P1 P2 M 0 ∗ P1 q) ∗
        OmoTokenW γg 0 ∗ ⌜ V ⊑ V' ⌝.

Definition create_weak' {Σ} `{!noprolG Σ, !omoGeneralG Σ} (ArcInv : ArcInvT Σ) (WeakArc : WeakArcT Σ) : Prop :=
  ∀ Ec l P1 P2 V N,
    ⊒V -∗ l ↦ #0 -∗ (l >> 1) ↦ #1 -∗ P2 ={Ec}=∗
      ∃ γg γs V' M,
        let eVinit := mkOmoEvent WeakInit V' M in
        let E := [eVinit] in
        let initst := ((∅, V', {[0]}), ({[0]}, V', {[0]})) in
        ⊒V' ∗ ArcInv γg γs l E (omo_append_w [] 0 []) [initst] ∗ @{V'} WeakArc N γg l P1 P2 M 0 ∗
        OmoTokenW γg 0 ∗ ⌜ V ⊑ V' ⌝.

Definition strong_count_spec' {Σ} `{!noprolG Σ} (strong_count : val) (ArcInv : ArcInvT Σ) (StrongArc : StrongArcT Σ) : Prop :=
  ∀ N (DISJ: N ## histN) (l: loc) tid γg q M e (V : view) P1 P2,
  (* PRIVATE PRE *)
  ⊒V -∗ StrongArc N γg l q P1 P2 M e -∗
  (* PUBLIC PRE *)
  <<< ∀ γs E omo stlist, ▷ ArcInv γg γs l E omo stlist >>>
    strong_count [ #l] @tid; ↑N
  <<< ∃ (v' : Z),
      (* PUBLIC POST *)
      ▷ ArcInv γg γs l E omo stlist ∗ StrongArc N γg l q P1 P2 M e ∗ ⌜ (0 < v')%Z ⌝,
      RET #v', emp >>>
  .

Definition weak_count_spec' {Σ} `{!noprolG Σ} (weak_count : val) (ArcInv : ArcInvT Σ) (StrongArc : StrongArcT Σ) : Prop :=
  ∀ N (DISJ: N ## histN) (l: loc) tid γg q M e (V : view) P1 P2,
  (* PRIVATE PRE *)
  ⊒V -∗ StrongArc N γg l q P1 P2 M e -∗
  (* PUBLIC PRE *)
  <<< ∀ γs E omo stlist, ▷ ArcInv γg γs l E omo stlist >>>
    weak_count [ #l] @tid; ↑N
  <<< ∃ (v' : Z),
      (* PUBLIC POST *)
      ▷ ArcInv γg γs l E omo stlist ∗ StrongArc N γg l q P1 P2 M e ∗ ⌜ (-1 ≤ v')%Z ⌝,
      RET #v', emp >>>
  .

Definition clone_arc_spec' {Σ} `{!noprolG Σ, !omoGeneralG Σ} (clone_arc : val) (ArcInv : ArcInvT Σ) (StrongArc : StrongArcT Σ) : Prop :=
  ∀ N (DISJ: N ## histN) (l: loc) tid γg q M e (V : view) P1 P2,
  (* PRIVATE PRE *)
  (∀ q, AsFractional (P1 q) P1 q) →
  ⊒V -∗ StrongArc N γg l q P1 P2 M e -∗
  (* PUBLIC PRE *)
  <<< ∀ γs E omo stlist, ▷ ArcInv γg γs l E omo stlist >>>
    clone_arc [ #l] @tid; ↑N
  <<< ∃ V' st M' q',
      (* PUBLIC POST *)
      let eVop := mkOmoEvent (Clone e) V' M' in
      let E' := E ++ [eVop] in
      let opId : event_id := length E in
      let omo' := omo_append_w omo opId [] in
      ⊒V' ∗ ▷ ArcInv γg γs l E' omo' (stlist ++ [st]) ∗ @{V'} (StrongArc N γg l q P1 P2 M' e ∗ StrongArc N γg l q' P1 P2 M' opId ∗ P1 q') ∗
      OmoTokenW γg opId ∗
      ⌜ V ⊑ V' ∧ M ⊆ M' ⌝,
      RET #☠, emp >>>
  .

Definition downgrade_spec' {Σ} `{!noprolG Σ, !omoGeneralG Σ} (downgrade : val) (ArcInv : ArcInvT Σ) (StrongArc : StrongArcT Σ) (WeakArc : WeakArcT Σ) : Prop :=
  ∀ N (DISJ: N ## histN) (l: loc) tid γg M q e (V : view) P1 P2,
  (* PRIVATE PRE *)
  ⊒V -∗ StrongArc N γg l q P1 P2 M e -∗
  (* PUBLIC PRE *)
  <<< ∀ γs E omo stlist, ▷ ArcInv γg γs l E omo stlist >>>
    downgrade [ #l] @tid; ↑N
  <<< ∃ V' γs' omo' stlist' M',
      (* PUBLIC POST *)
      let eVop := mkOmoEvent Downgrade V' M' in
      let E' := E ++ [eVop] in
      let opId : event_id := length E in
      ⊒V' ∗ ▷ ArcInv γg γs' l E' omo' stlist' ∗ @{V'} (StrongArc N γg l q P1 P2 M' e ∗ WeakArc N γg l P1 P2 M' opId) ∗
      OmoTokenW γg opId ∗
      ⌜ V ⊑ V' ∧ M ⊆ M'
      ∧ (∃ gen, omo' = omo_insert_w omo gen opId []) ⌝,
      RET #☠, emp >>>
  .

Definition clone_weak_spec' {Σ} `{!noprolG Σ, !omoGeneralG Σ} (clone_weak : val) (ArcInv : ArcInvT Σ) (WeakArc : WeakArcT Σ) : Prop :=
  ∀ N (DISJ: N ## histN) (l: loc) tid γg M e (V : view) P1 P2,
  (* PRIVATE PRE *)
  ⊒V -∗ WeakArc N γg l P1 P2 M e -∗
  (* PUBLIC PRE *)
  <<< ∀ γs E omo stlist, ▷ ArcInv γg γs l E omo stlist >>>
    clone_weak [ #l] @tid; ↑N
  <<< ∃ V' γs' omo' stlist' M',
      (* PUBLIC POST *)
      let eVop := mkOmoEvent (WeakClone e) V' M' in
      let E' := E ++ [eVop] in
      let opId : event_id := length E in
      ⊒V' ∗ ▷ ArcInv γg γs' l E' omo' stlist' ∗ @{V'} (WeakArc N γg l P1 P2 M' e ∗ WeakArc N γg l P1 P2 M' opId) ∗
      OmoTokenW γg opId ∗
      ⌜ V ⊑ V' ∧ M ⊆ M'
      ∧ (∃ gen, omo' = omo_insert_w omo gen opId []) ⌝,
      RET #☠, emp >>>
  .

Definition upgrade_spec' {Σ} `{!noprolG Σ, !omoGeneralG Σ} (upgrade : val) (ArcInv : ArcInvT Σ) (StrongArc : StrongArcT Σ) (WeakArc : WeakArcT Σ) : Prop :=
  ∀ N (DISJ: N ## histN) (l: loc) tid γg M e (V : view) P1 P2,
  (* PRIVATE PRE *)
  (∀ q, AsFractional (P1 q) P1 q) →
  ⊒V -∗ WeakArc N γg l P1 P2 M e -∗
  (* PUBLIC PRE *)
  <<< ∀ γs E omo stlist, ▷ ArcInv γg γs l E omo stlist >>>
    upgrade [ #l] @tid; ↑N
  <<< ∃ (b : bool) V' E' omo' stlist' M',
      (* PUBLIC POST *)
      ⊒V' ∗ ▷ ArcInv γg γs l E' omo' stlist' ∗ @{V'} WeakArc N γg l P1 P2 M' e ∗
      ⌜ V ⊑ V' ∧ M ⊆ M' ⌝ ∗
      if b then (
        (* Upgrade success *)
        (∃ q, @{V'} (StrongArc N γg l q P1 P2 M' (length E) ∗ P1 q)) ∗ OmoTokenW γg (length E) ∗
        ⌜ E' = E ++ [mkOmoEvent Upgrade V' M'] ∧ omo' = omo_append_w omo (length E) [] ∧ (∃ st, stlist' = stlist ++ [st]) ⌝
      ) else (
        (* Upgrade failed *)
        OmoTokenR γg (length E) ∗
        ⌜ E' = E ++ [mkOmoEvent UpgradeFail V' M'] ∧ (∃ gen, omo' = omo_insert_r omo gen (length E) ∧ gen < length omo) ∧ stlist' = stlist ⌝
      ),
      RET #b, emp >>>
  .

Definition drop_weak_spec' {Σ} `{!noprolG Σ, !omoGeneralG Σ} (drop_weak : val) (ArcInv : ArcInvT Σ) (WeakArc : WeakArcT Σ) : Prop :=
  ∀ N (DISJ: N ## histN) (l: loc) tid γg M e (V : view) P1 P2,
  (* PRIVATE PRE *)
  ⊒V -∗ WeakArc N γg l P1 P2 M e -∗
  (* PUBLIC PRE *)
  <<< ∀ γs E omo stlist, ▷ ArcInv γg γs l E omo stlist >>>
    drop_weak [ #l] @tid; ↑N
  <<< ∃ (b : bool) V' γs' omo' stlist' M',
      (* PUBLIC POST *)
      let eVop := mkOmoEvent (WeakDrop e b) V' M' in
      let E' := E ++ [eVop] in
      ⊒V' ∗ ▷ ArcInv γg γs' l E' omo' stlist' ∗ OmoTokenW γg (length E) ∗ @{V'} OmoEview γg M' ∗
      ⌜ V ⊑ V' ∧ M ⊆ M' ∧ (∃ gen, omo' = omo_insert_w omo gen (length E) []) ⌝,
      RET #b, if b then P2 ∗ l ↦ #0 ∗ (l >> 1) ↦ #0 else True >>>
  .

Definition drop_fake_spec' {Σ} `{!noprolG Σ, !omoGeneralG Σ} (drop_weak : val) (ArcInv : ArcInvT Σ) (FakeArc : FakeArcT Σ) : Prop :=
  ∀ N (DISJ: N ## histN) (l: loc) tid γg M (V : view) P1 P2,
  (* PRIVATE PRE *)
  ⊒V -∗ FakeArc N γg l P1 P2 M -∗ P2 -∗
  (* PUBLIC PRE *)
  <<< ∀ γs E omo stlist, ▷ ArcInv γg γs l E omo stlist >>>
    drop_weak [ #l] @tid; ↑N
  <<< ∃ (b : bool) V' γs' omo' stlist' M',
      (* PUBLIC POST *)
      let eVop := mkOmoEvent (WeakDrop 0 b) V' M' in
      let E' := E ++ [eVop] in
      ⊒V' ∗ ▷ ArcInv γg γs' l E' omo' stlist' ∗ OmoTokenW γg (length E) ∗ @{V'} OmoEview γg M' ∗
      ⌜ V ⊑ V' ∧ M ⊆ M' ∧ (∃ gen, omo' = omo_insert_w omo gen (length E) []) ⌝,
      RET #b, if b then P2 ∗ l ↦ #0 ∗ (l >> 1) ↦ #0 else True >>>
  .

Definition drop_arc_spec' {Σ} `{!noprolG Σ, !omoGeneralG Σ} (drop_arc : val) (ArcInv : ArcInvT Σ) (StrongArc : StrongArcT Σ) (FakeArc : FakeArcT Σ) : Prop :=
  ∀ N (DISJ: N ## histN) (l: loc) tid γg q M e (V : view) P1 P2,
  (* PRIVATE PRE *)
  (∀ q, AsFractional (P1 q) P1 q) →
  ⊒V -∗ StrongArc N γg l q P1 P2 M e -∗ P1 q -∗
  (* PUBLIC PRE *)
  <<< ∀ γs E omo stlist, ▷ ArcInv γg γs l E omo stlist >>>
    drop_arc [ #l] @tid; ↑N
  <<< ∃ (b : bool) V' st M',
      (* PUBLIC POST *)
      let eVop := mkOmoEvent (StrongDrop e b) V' M' in
      let E' := E ++ [eVop] in
      let omo' := omo_append_w omo (length E) [] in
      ⊒V' ∗ ▷ ArcInv γg γs l E' omo' (stlist ++ [st]) ∗ OmoTokenW γg (length E) ∗
      ⌜ V ⊑ V' ∧ M ⊆ M' ⌝ ∗
      if b then (@{V'} (FakeArc N γg l P1 P2 M' ∗ P1 1%Qp)) else (@{V'} OmoEview γg M'),
      RET #b, emp >>>
  .

Definition try_unwrap_spec' {Σ} `{!noprolG Σ, !omoGeneralG Σ} (try_unwrap : val) (ArcInv : ArcInvT Σ) (StrongArc : StrongArcT Σ) (FakeArc : FakeArcT Σ) : Prop :=
  ∀ N (DISJ: N ## histN) (l: loc) tid γg q M e (V : view) P1 P2,
  (* PRIVATE PRE *)
  (∀ q, AsFractional (P1 q) P1 q) →
  ⊒V -∗ StrongArc N γg l q P1 P2 M e -∗ P1 q -∗
  (* PUBLIC PRE *)
  <<< ∀ γs E omo stlist, ▷ ArcInv γg γs l E omo stlist >>>
    try_unwrap [ #l] @tid; ↑N
  <<< ∃ (b : bool) V' E' omo' stlist' M',
      (* PUBLIC POST *)
      ⊒V' ∗ ▷ ArcInv γg γs l E' omo' stlist' ∗
      ⌜ V ⊑ V' ∧ M ⊆ M' ⌝ ∗
      if b then (
        (* success *)
        @{V'} (FakeArc N γg l P1 P2 M' ∗ P1 1%Qp) ∗ OmoTokenW γg (length E) ∗
        ⌜ E' = E ++ [mkOmoEvent (StrongDrop e true) V' M'] ∧ omo' = omo_append_w omo (length E) [] ∧ (∃ st, stlist' = stlist ++ [st]) ⌝
      ) else (
        (* failure *)
        @{V'} (StrongArc N γg l q P1 P2 M' e ∗ P1 q) ∗ OmoTokenR γg (length E) ∗
        ⌜ E' = E ++ [mkOmoEvent (UnwrapFail e) V' M'] ∧ (∃ gen, omo' = omo_insert_r omo gen (length E) ∧ gen < length omo)
        ∧ stlist' = stlist ⌝
      ),
      RET #b, emp >>>
  .

Definition is_unique_must_success E stlist (M : eView) (e : event_id) : Prop :=
  ∃ stf, last stlist = Some stf ∧ stf.1.1.1 = {[e]} ∧ stf.2.1.1 = {[0]} ∧
    (∀ e, is_Some (E !! e) → e ∈ M).

Definition is_unique_spec' {Σ} `{!noprolG Σ, !omoGeneralG Σ} (is_unique : val) (ArcInv : ArcInvT Σ) (StrongArc : StrongArcT Σ) : Prop :=
  ∀ N (DISJ: N ## histN) (l: loc) tid γg q M e (V : view) P1 P2,
  (* PRIVATE PRE *)
  (∀ q, AsFractional (P1 q) P1 q) →
  ⊒V -∗ StrongArc N γg l q P1 P2 M e -∗ P1 q -∗
  (* PUBLIC PRE *)
  <<< ∀ γs E omo stlist, ▷ ArcInv γg γs l E omo stlist >>>
    is_unique [ #l] @tid; ↑N
  <<< ∃ (b : bool) V' E' omo' M',
      (* PUBLIC POST *)
      ⊒V' ∗ ▷ ArcInv γg γs l E' omo' stlist ∗ @{V'} OmoEview γg M' ∗
      ⌜ V ⊑ V' ∧ M ⊆ M' ∧ (is_unique_must_success E stlist M e → b = true) ⌝ ∗
      if b then (
        (* success *)
        @{V'} (P1 1%Qp) ∗ OmoTokenR γg (length E) ∗
        ⌜ E' = E ++ [mkOmoEvent (Unique e) V' M'] ∧ omo' = omo_insert_r omo (length omo - 1) (length E) ⌝
      ) else (
        (* failure *)
        (* Note1: Current spec of [is_unique] allows spurious failure.
           However, `is_unique_must_success` eliminates spurious failure in most realistic cases.
           To give stronger spec, sc fence is needed *)
        (* Note2: StrongArc cannot be returned here since ownership of StrongArc is further needed
                  to perform release store to weak counter after commit point. *)
        @{V'} (P1 q) ∗ ⌜ E' = E ∧ omo' = omo ∧ M' = M ⌝
      ),
      RET #b, if b then l ↦ #1 ∗ (l >> 1) ↦ #1 else (∃ V'', @{V''} (StrongArc N γg l q P1 P2 M' e) ∗ ⊒V'' ∗ ⌜ V' ⊑ V'' ⌝)>>>
  .

Definition try_unwrap_full_spec' {Σ} `{!noprolG Σ, !omoGeneralG Σ} (try_unwrap_full : val) (ArcInv : ArcInvT Σ) (StrongArc : StrongArcT Σ) (FakeArc : FakeArcT Σ) : Prop :=
  ∀ N (DISJ: N ## histN) (l l': loc) tid γg q M e (V : view) P1 P2,
  (* PRIVATE PRE *)
  (∀ q, AsFractional (P1 q) P1 q) →
  ⊒V -∗ StrongArc N γg l q P1 P2 M e -∗ P1 q -∗ l' ↦ - -∗
  (* PUBLIC PRE *)
  <<< ∀ γs E omo stlist, ▷ ArcInv γg γs l E omo stlist >>>
    try_unwrap_full [ #l; #l'] @tid; ↑N
  <<< ∃ (b : bool) V' E' omo' stlist' M',
      (* PUBLIC POST *)
      ⊒V' ∗ ▷ ArcInv γg γs l E' omo' stlist' ∗ @{V'} OmoEview γg M' ∗
      ⌜ V ⊑ V' ∧ M ⊆ M' ⌝ ∗
      if b then (
        (* No other strong: we get P1 *)
        @{V'} (P1 1%Qp) ∗ OmoTokenW γg (length E) ∗
        ⌜ E' = E ++ [mkOmoEvent (StrongDrop e true) V' M'] ∧ omo' = omo_append_w omo (length E) [] ∧ (∃ st, stlist' = stlist ++ [st]) ⌝
      ) else (
        (* There are other strong: we get back what we gave at the first place *)
        @{V'} (StrongArc N γg l q P1 P2 M' e ∗ P1 q) ∗ OmoTokenR γg (length E) ∗
        ⌜ E' = E ++ [mkOmoEvent (UnwrapFail e) V' M'] ∧ (∃ gen, omo' = omo_insert_r omo gen (length E) ∧ gen < length omo)
        ∧ stlist' = stlist ⌝
      ),
      RET #☠, ∃ (x : nat), l' ↦ #x ∗
                  match x with
                  (* No other reference: we get everything *)
                  | 0 => l ↦ #1 ∗ (l >> 1) ↦ #1 ∗ ⌜ b = true ⌝
                  (* No other strong, but there are weaks: we get the option to get a weak if we pay P2 *)
                  | 1 => ∃ V'', @{V''} (FakeArc N γg l P1 P2 M') ∗ ⊒V'' ∗ ⌜ b = true ∧ V' ⊑ V'' ⌝
                  (* There are other strong *)
                  | _ => ⌜ x = 2 ∧ b = false ⌝
                  end >>>
  .

Record arc_spec {Σ} `{!noprolG Σ, !omoGeneralG Σ, !omoSpecificG Σ arc_event arc_state} := ArcSpec {
  (** operations *)
  strong_count : val;
  weak_count : val;
  clone_arc : val;
  clone_weak : val;
  downgrade : val;
  upgrade : val;
  drop_weak : val;
  drop_arc : val;
  try_unwrap : val;
  is_unique : val;
  try_unwrap_full : val;

  (** These are common elements in arbitrary composable linearizability spec *)
  (** predicates *)
  ArcInv : ArcInvT Σ;
  StrongArc : StrongArcT Σ;
  WeakArc : WeakArcT Σ;
  FakeArc : FakeArcT Σ;

  (** predicates properties *)
  ArcInv_Objective : ∀ γg γs l E omo stlist, Objective (ArcInv γg γs l E omo stlist );
  ArcInv_Timeless : ∀ γg γs l E omo stlist, Timeless (ArcInv γg γs l E omo stlist);
  ArcInv_Linearizable : ∀ γg γs l E omo stlist, ArcInv γg γs l E omo stlist ⊢ ⌜ Linearizability_omo E omo stlist ⌝;
  ArcInv_OmoAuth_acc :
    ∀ γg γs l E omo stlist , ArcInv γg γs l E omo stlist ⊢
      OmoAuth γg γs (1/2)%Qp E omo stlist _ ∗ (OmoAuth γg γs (1/2)%Qp E omo stlist _ -∗ ArcInv γg γs l E omo stlist);
  StrongArc_OmoEview : ∀ N γg l q P1 P2 M e, StrongArc N γg l q P1 P2 M e ⊢ OmoEview γg M;
  WeakArc_OmoEview : ∀ N γg l P1 P2 M e, WeakArc N γg l P1 P2 M e ⊢ OmoEview γg M;
  FakeArc_OmoEview : ∀ N γg l P1 P2 M, FakeArc N γg l P1 P2 M ⊢ OmoEview γg M;
  StrongArc_Eview_update : ∀ N γg l q P1 P2 e M1 M2, StrongArc N γg l q P1 P2 M1 e -∗ OmoEview γg M2 -∗ StrongArc N γg l q P1 P2 (M1 ∪ M2) e;
  WeakArc_Eview_update : ∀ N γg l P1 P2 e M1 M2, WeakArc N γg l P1 P2 M1 e -∗ OmoEview γg M2 -∗ WeakArc N γg l P1 P2 (M1 ∪ M2) e;
  FakeArc_Eview_update : ∀ N γg l P1 P2 M1 M2, FakeArc N γg l P1 P2 M1 -∗ OmoEview γg M2 -∗ FakeArc N γg l P1 P2 (M1 ∪ M2);
  (**************************************************************)

  (* operations specs *)
  create_strong : create_strong' ArcInv StrongArc;
  create_weak : create_weak' ArcInv WeakArc;
  strong_count_spec : strong_count_spec' strong_count ArcInv StrongArc;
  weak_count_spec : weak_count_spec' weak_count ArcInv StrongArc;
  clone_arc_spec : clone_arc_spec' clone_arc ArcInv StrongArc;
  downgrade_spec : downgrade_spec' downgrade ArcInv StrongArc WeakArc;
  clone_weak_spec : clone_weak_spec' clone_weak ArcInv WeakArc;
  upgrade_spec : upgrade_spec' upgrade ArcInv StrongArc WeakArc;
  drop_weak_spec : drop_weak_spec' drop_weak ArcInv WeakArc;
  drop_fake_spec : drop_fake_spec' drop_weak ArcInv FakeArc;
  drop_arc_spec : drop_arc_spec' drop_arc ArcInv StrongArc FakeArc;
  try_unwrap_spec : try_unwrap_spec' try_unwrap ArcInv StrongArc FakeArc;
  is_unique_spec : is_unique_spec' is_unique ArcInv StrongArc;
  try_unwrap_full_spec : try_unwrap_full_spec' try_unwrap_full ArcInv StrongArc FakeArc;
}.

Arguments arc_spec _ {_ _ _}.
Global Existing Instances ArcInv_Objective ArcInv_Timeless.
