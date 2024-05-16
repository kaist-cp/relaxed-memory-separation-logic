From iris.bi Require Import big_op lib.fractional.

From gpfsl.logic Require Import logatom invariants.
From gpfsl.examples.exchanger Require Export spec_graph_piggyback.

Require Import iris.prelude.options.

Implicit Types (G: graph xchg_event) (M : logView).

Section defs.
Context {Σ} `{!noprolG Σ, !inG Σ (graphR xchg_event)}.
Context
  (ExchangerLocal : (Z → vProp Σ) → ExchangerLocalNT Σ)
  (ExchangerInv : ExchangerInvT Σ).

(** Extends exchange_spec with resource, which we can only get out under a later.
  But reversely, we can also put them in under a later. *)
Definition exchange_resource_spec'
  (exchange : val) : Prop :=
  ∀ (P : Z → vProp Σ) N (DISJ: N ## histN)
    (ex: loc) tid γg G1 M (V : view) (v1 : Z) (Posx: 0 ≤ v1),
  (* PRIVATE PRE *)
  (* G1 is a snapshot of the graph, locally observed by M *)
  ⊒V -∗ ExchangerLocal P N γg ex G1 M -∗
  <<< ∀ G, ▷ ExchangerInv γg 1%Qp G ∗ (▷ @{V} P v1) >>>
    exchange [ #ex ; #v1] @ tid; ↑N
  <<< ∃ V' G' exId1 exId2 (v2 : Z) Vex1 Vex2 M' ,
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
          @{V'} ExchangerLocal P N γg ex G' M' ∗ (▷ @{V} P v1)
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
            @{V'} ExchangerLocal P N γg ex G' M' ∗ (▷ @{V'} P v2)
            (* else if my event comes in earlier *)
            ∨ ⌜ (exId1 < exId2)%nat ∧ G'.(so) = G.(so) ∧ G'.(com) = G.(com) ⌝ ∗
            @{V'} ExchangerLocal P N γg ex G' (M' ∖ {[exId2]}))),
    RET #v2,
      ⌜ 0 ≤ v2 ∧ (exId1 < exId2)%nat ⌝ →
      (* if the exchange succeeds and my event comes in first *)
      ∃ G'',
      ⌜ G' ⊑ G'' ∧
        exId2 = length G'.(Es) ∧
        G''.(Es) = G'.(Es) ++ [mkGraphEvent (Exchange v2 v1) Vex2 M'] ∧
        G''.(so) = {[ (exId1, exId2); (exId2, exId1) ]} ∪ G.(so) ∧
        G''.(com) = {[ (exId1, exId2); (exId2, exId1) ]} ∪ G.(com) ∧
        exId1 ∉ (elements G'.(so)).*1 ∧ exId2 ∉ (elements G'.(so)).*1 ⌝ ∗
      @{V'} ExchangerLocal P N γg ex G'' M' ∗ (▷ @{V'} P v2) >>>.

End defs.

Record exchanger_resource_spec {Σ} `{!noprolG Σ, !inG Σ (graphR xchg_event)}
  := ExchangerSpec {
  (** operations *)
  new_exchanger : val;
  exchange : val;
  (** predicates *)
  ExchangerLocal : (Z → vProp Σ) → ExchangerLocalNT Σ;
  ExchangerInv : ExchangerInvT Σ;

  (** predicates properties *)
  ExchangerInv_Timeless : ∀ γg q G, Timeless (ExchangerInv γg q G);
  ExchangerInv_Objective : ∀ γg q G, Objective (ExchangerInv γg q G);
  ExchangerInv_Fractional : ∀ γg G, Fractional (λ q, ExchangerInv γg q G);
  ExchangerInv_AsFractional :
    ∀ γg q G, AsFractional (ExchangerInv γg q G) (λ q, ExchangerInv γg q G) q ;

  ExchangerInv_ExchangerConsistent :
    ∀ P, ExchangerInv_ExchangerConsistent_piggyback (ExchangerLocal P) ExchangerInv ;
  ExchangerInv_graph_master_acc :
    ExchangerInv_graph_master_acc' ExchangerInv ;
  ExchangerInv_graph_snap :
    ExchangerInv_graph_snap' ExchangerInv ;
  ExchangerInv_agree :
    ExchangerInv_agree' ExchangerInv ;

  ExchangerLocal_Persistent :
    ∀ P N γg x G M, Persistent (ExchangerLocal P N γg x G M);

  ExchangerLocal_graph_snap :
    ∀ P N, ExchangerLocal_graph_snap' (ExchangerLocal P N) ;

  (* operations specs *)
  new_exchanger_spec P : new_exchanger_spec' (ExchangerLocal P) ExchangerInv new_exchanger;
  exchange_spec : exchange_resource_spec' ExchangerLocal ExchangerInv exchange;
}.

Arguments exchanger_resource_spec _ {_ _}.
