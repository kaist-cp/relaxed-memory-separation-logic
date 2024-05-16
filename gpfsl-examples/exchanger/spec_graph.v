From stdpp Require Import namespaces.
From iris.bi Require Import lib.fractional.

From gpfsl.logic Require Import logatom.
From gpfsl.examples.graph Require Export spec.

Require Import iris.prelude.options.

Notation CANCELLED := (-1) (only parsing).

(** Exchanger events *)
Inductive xchg_event := Exchange (v1 v2 : Z).
Notation dummy_exevt := (Exchange 0 0).

#[global] Instance xchg_event_eq_dec : EqDecision xchg_event.
Proof. solve_decision. Defined.
#[global] Instance xchg_event_countable : Countable xchg_event.
Proof.
  refine (
    inj_countable'
      (λ e, match e with
            | Exchange v1 v2 => (1, v1, v2)
            end)
      (λ x, match x with
            | (1, v1, v2) => Exchange v1 v2
            | _ => dummy_exevt end) _);
    by intros [].
Qed.

#[local] Notation graph := (graph xchg_event).

Implicit Type (G : graph) (M : logView).

Definition ExchangerLocalT Σ : Type :=
  gname → loc → graph → logView → vProp Σ.
Definition ExchangerLocalNT Σ : Type :=
  namespace → ExchangerLocalT Σ.
Definition ExchangerInvT Σ : Type :=
  gname → frac → graph → vProp Σ.

Record ExchangerConsistent (G : graph) : Prop := mkExchangerConsistent {
  (* The first one is our own side condition *)
  xchg_cons_dview : (* exchange is releasing *)
    graph_event_is_releasing G.(Es) (λ _, True) ;

  (* (1)-(5) Exchanger spec from Yacovet (POPL'19) paper *)
    (* (1) at most 1 Constructor event: we currently don't have initialization events *)
  xchg_cons_com :
    (* (2a) com is symmetric and irreflexive *)
    symmetric_pair G.(com) ∧ irreflexive_pair G.(com) ;
  xchg_cons_matches :
    (* (2b) com matches pair of events *)
    ∀ e1 e2, (e1, e2) ∈ G.(com) →
      (e1 = S e2 ∨ e2 = S e1) ∧
      ∃ eV1 eV2 (v1 v2 : Z), G.(Es) !! e1 = Some eV1 ∧ G.(Es) !! e2 = Some eV2 ∧
        eV1.(ge_event) = Exchange v1 v2 ∧ eV2.(ge_event) = Exchange v2 v1 ∧
        0 ≤ v1 ∧ 0 ≤ v2 ∧
        (* so is synchronizing *)
        eV1.(ge_view).(dv_in) ⊏ eV2.(ge_view).(dv_comm) ∧
        eV2.(ge_view).(dv_in) ⊏ eV1.(ge_view).(dv_comm) ;
  xchg_cons_com_functional :
    (* (3) com and com^-1 are functional: *)
    functional_pair G.(com) ;
  xchg_cons_unmatched :
    (* (4) unmatched exchanges return CANCELLED *)
    ∀ e eV, G.(Es) !! e = Some eV → e ∉ (elements G.(com)).*1 →
      ∃ (v1 : Z), eV.(ge_event) = Exchange v1 CANCELLED ;
  xchg_cons_so_com :
    (* (5) so and com agree *)
    G.(so) = G.(com) ;
}.

Lemma ExchangerConsistent_empty : ExchangerConsistent ∅.
Proof. done. Qed.

Section spec.
Context {Σ} `{!noprolG Σ, !inG Σ (graphR xchg_event)}.
Context (ExchangerLocal : ExchangerLocalNT Σ)
        (ExchangerInv : ExchangerInvT Σ).

Local Notation vProp := (vProp Σ).

Definition new_exchanger_spec' (new_exchanger : val) : Prop :=
  ∀ N tid,
  {{{ True }}}
    new_exchanger [] @ tid; ⊤
  {{{ γg (ex : loc), RET #ex;
      ExchangerLocal N γg ex ∅ ∅ ∗ ExchangerInv γg 1%Qp ∅ }}}.

Definition exchange_preT : Type := graph → vProp.
Definition exchange_postT : Type :=
  graph → view → graph → event_id → event_id → Z →
  dataView → dataView → logView → vProp.

Definition exchange_AU_atomic_pre γg : exchange_preT :=
  (λ G, ▷ ExchangerInv γg 1%Qp G)%I.
Definition exchange_priv_post N ex γg v1 : exchange_postT :=
  (λ G V' G' exId1 exId2 v2 Vex1 Vex2 M',
    ⌜ 0 ≤ v2 ∧ (exId1 < exId2)%nat ⌝ →
      (* if the exchange succeeds and my event comes in first *)
      ∃ G'',
      ⌜ G' ⊑ G'' ∧
        exId2 = length G'.(Es) ∧
        G''.(Es) = G'.(Es) ++ [mkGraphEvent (Exchange v2 v1) Vex2 M'] ∧
        G''.(so) = {[ (exId1, exId2); (exId2, exId1) ]} ∪ G.(so) ∧
        G''.(com) = {[ (exId1, exId2); (exId2, exId1) ]} ∪ G.(com) ∧
        exId1 ∉ (elements G'.(so)).*1 ∧ exId2 ∉ (elements G'.(so)).*1 ⌝ ∗
      @{V'} ExchangerLocal N γg ex G'' M'
  )%I.

Definition exchange_spec'
  (exchange : val) : Prop :=
  ∀ N (DISJ: N ## histN) (ex: loc) tid γg G1 M (V : view) (v1 : Z) (Posx: 0 ≤ v1),
  (* PRIVATE PRE *)
  (* G1 is a graph snapshot, locally observed by M *)
  ⊒V -∗ ExchangerLocal N γg ex G1 M -∗
  <<< ∀ G, exchange_AU_atomic_pre γg G >>>
    exchange [ #ex ; #v1] @ tid; ↑N
  <<< ∃ (V' : view) G' (exId1 exId2 : event_id) (v2 : Z) Vex1 Vex2 M',
      ▷ ExchangerInv γg 1%Qp G' ∗
      ⊒V' ∗
      ⌜ G ⊑ G' ∧ M ⊑ M' ∧
        Vex1.(dv_in) = V ∧ Vex1.(dv_comm) = V' ∧
        exId1 = length G.(Es) ∧
        G'.(Es) = G.(Es) ++ [mkGraphEvent (Exchange v1 v2) Vex1 M'] ∧
        exId1 ∈ M' ∧ exId1 ∉ M ⌝ ∗
      ( ⌜ (* CANCELLED case *)
          v2 = CANCELLED ∧ G'.(so) = G.(so) ∧ G'.(com) = G.(com) ∧
          eventgraph_consistent G' ∧ ExchangerConsistent G' ⌝ ∗
          @{V'} ExchangerLocal N γg ex G' M'
        ∨ (* SUCCESS case *)
        ⌜ 0 ≤ v2 ∧
          (length G1.(Es) ≤ exId2)%nat ∧
          exId2 ∈ M' ∧ exId2 ∉ M ∧ exId1 ≠ exId2
          (* This fixes the order in which the AUs are committed.
            TODO: generalize so that the client can pick the order *)
          ∧ (v1 ≠ v2 → (v1 > v2 ↔ (exId1 < exId2)%nat)) ⌝ ∗
          ( (* if my event comes in later *)
            ⌜ (exId2 < exId1)%nat ∧
              G.(Es) !! exId2 = Some (mkGraphEvent (Exchange v2 v1) Vex2 M') ∧
              G'.(so) = {[ (exId1, exId2); (exId2, exId1) ]} ∪ G.(so) ∧
              G'.(com) = {[ (exId1, exId2); (exId2, exId1) ]} ∪ G.(com) ∧
              exId1 ∉ (elements G.(so)).*1 ∧ exId2 ∉ (elements G.(so)).*1 ∧
              eventgraph_consistent G' ∧ ExchangerConsistent G' ⌝ ∗
            @{V'} ExchangerLocal N γg ex G' M'
            (* else if my event comes in earlier *)
            ∨ ⌜ (exId1 < exId2)%nat ∧ G'.(so) = G.(so) ∧ G'.(com) = G.(com) ⌝ ∗
            @{V'} ExchangerLocal N γg ex G' (M' ∖ {[exId2]}))) ,
    (* RETURN VALUE AT COMMITTING POINT *)
    RET #v2, exchange_priv_post N ex γg v1 G V' G' exId1 exId2 v2 Vex1 Vex2 M' >>>.

Definition ExchangerInv_ExchangerConsistent' : Prop :=
  ∀ N γg x q G G' M',
    ExchangerInv γg q G -∗ ExchangerLocal N γg x G' M'
    ={↑N}=∗ ⌜ eventgraph_consistent G ∧ ExchangerConsistent G ⌝ ∗
            ExchangerInv γg q G.

Definition ExchangerInv_graph_master_acc' : Prop :=
  ∀ γg q G, ExchangerInv γg q G ∗ ⌜ eventgraph_consistent G ⌝ ⊢
    ∃ q', graph_master γg q' G ∗
          (graph_master γg q' G -∗ ExchangerInv γg q G).

Definition ExchangerInv_graph_snap' : Prop :=
  ∀ γg q G G' M',
    ExchangerInv γg q G -∗ graph_snap γg G' M' -∗ ⌜ G' ⊑ G ⌝.

Definition ExchangerInv_agree' : Prop :=
  ∀ γg q G q' G',
    ExchangerInv γg q G -∗ ExchangerInv γg q' G' -∗ ⌜ G' = G ⌝.
End spec.

Definition ExchangerLocal_graph_snap'
  {Σ} `{!noprolG Σ, !inG Σ (graphR xchg_event)}
  (ExchangerLocal : ExchangerLocalT Σ)
  : Prop :=
  ∀ γg x G M, ExchangerLocal γg x G M ⊢ graph_snap γg G M.

Record exchanger_spec {Σ} `{!noprolG Σ, !inG Σ (graphR xchg_event)}
  := ExchangerSpec {
  (** operations *)
  new_exchanger : val;
  exchange : val;

  (** predicates *)
  ExchangerLocal : ExchangerLocalNT Σ;
  ExchangerInv : ExchangerInvT Σ;

  (** predicates properties *)
  (* ExchangerInv *)
  ExchangerInv_Timeless : ∀ γg q G, Timeless (ExchangerInv γg q G);
  ExchangerInv_Objective : ∀ γg q G, Objective (ExchangerInv γg q G);
  ExchangerInv_Fractional : ∀ γg G, Fractional (λ q, ExchangerInv γg q G);
  ExchangerInv_AsFractional :
    ∀ γg q G, AsFractional (ExchangerInv γg q G) (λ q, ExchangerInv γg q G) q ;

  ExchangerInv_ExchangerConsistent :
    ExchangerInv_ExchangerConsistent' ExchangerLocal ExchangerInv ;
  ExchangerInv_graph_master_acc :
    ExchangerInv_graph_master_acc' ExchangerInv ;
  ExchangerInv_graph_snap :
    ExchangerInv_graph_snap' ExchangerInv ;
  ExchangerInv_agree :
    ExchangerInv_agree' ExchangerInv ;

  (* ExchangerLocal *)
  ExchangerLocal_Persistent :
    ∀ N γg x G M, Persistent (ExchangerLocal N γg x G M) ;

  ExchangerLocal_graph_snap :
    ∀ N, ExchangerLocal_graph_snap' (ExchangerLocal N) ;

  (** operations specs *)
  new_exchanger_spec : new_exchanger_spec' ExchangerLocal ExchangerInv new_exchanger;
  exchange_spec : exchange_spec' ExchangerLocal ExchangerInv exchange;
}.

Arguments exchanger_spec _ {_ _}.
