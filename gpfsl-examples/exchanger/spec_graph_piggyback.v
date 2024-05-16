From iris.bi Require Import lib.fractional.

From gpfsl.logic Require Import logatom invariants.

From gpfsl.examples.exchanger Require Export spec_graph.

Require Import iris.prelude.options.

Implicit Types (Eo Ei : coPset) (N : namespace) (G : graph xchg_event).

Section atomic.
  Context `{!noprolG Σ}.
  Context {TA TB TA' TB' : tele}.

  Notation vProp := (vProp Σ).

  Context (EI : bool → vProp).
  Definition atomic_update_open Eo Ei
    (α : TA → vProp) (β Φ : TA → TB → vProp)
    b1 b2 : vProp :=
    ((▷ EI b1) -∗ atomic_update Eo Ei α β (λ a b, Φ a b ∗ ▷ EI b2))%I.

  Definition atomic_update_proof Eo Ei
    (α' : TA' → vProp) (β' Φ' : TA' → TB' → vProp)
    (α : TA → vProp) (β : bool → bool → TA → TB → vProp) (Φ : TA → TB → vProp)
    : vProp :=
    ∀ b1 b2,
      atomic_update Eo Ei α' β' Φ' -∗
      atomic_update_open Eo Ei α (β b1 b2) Φ (orb b1 b2) (orb b1 (negb b2)).
End atomic.

(** A stronger exchanger spec that allows the client to rely on the fact that
  the matched AUs are committed atomically. *)

Definition xchgUN N := N .@ "uinv".

Section piggyback.
Context {Σ} `{!noprolG Σ, !inG Σ (graphR xchg_event)}.
Context
  (ExchangerLocal : (bool → vProp Σ) → ExchangerLocalNT Σ)
  (ExchangerInv : ExchangerInvT Σ).
Notation vProp := (vProp Σ).

Definition exchange_AU_atomic_post'
  EI N ex γg G1 M V v1 b1 b2 : @exchange_postT Σ :=
  (λ G V' G' exId1 exId2 v2 Vex1 Vex2 M',
    ▷ ExchangerInv γg 1%Qp G' ∗
    ⊒V' ∗
    ⌜ G ⊑ G' ∧ M ⊑ M' ∧
      Vex1.(dv_in) = V ∧ Vex1.(dv_comm) = V' ∧
      exId1 = length G.(Es) ∧
      G'.(Es) = G.(Es) ++ [mkGraphEvent (Exchange v1 v2) Vex1 M'] ∧
      exId1 ∈ M' ∧ exId1 ∉ M ⌝ ∗
    ( ⌜ (* CANCELLED case *)
        v2 = CANCELLED ∧ G'.(so) = G.(so) ∧ G'.(com) = G.(com) ∧
        eventgraph_consistent G' ∧ ExchangerConsistent G' ∧
        b1 = true ⌝ ∗
        @{V'} ExchangerLocal EI N γg ex G' M'
      ∨ (* SUCCESS case *)
      ⌜ 0 ≤ v2 ∧
        (length G1.(Es) ≤ exId2)%nat ∧
        exId2 ∈ M' ∧ exId2 ∉ M ∧ exId1 ≠ exId2
        (* This fixes the order in which the AUs are committed.
          TODO: generalize so that the client can pick the order *)
        ∧ (v1 ≠ v2 → (v1 > v2 ↔ (exId1 < exId2)%nat))
        ∧ b1 = false ⌝ ∗
        ( (* if my event comes in later *)
          ⌜ (exId2 < exId1)%nat ∧ b2 = false ∧
            G.(Es) !! exId2 = Some (mkGraphEvent (Exchange v2 v1) Vex2 M') ∧
            G'.(so) = {[ (exId1, exId2); (exId2, exId1) ]} ∪ G.(so) ∧
            G'.(com) = {[ (exId1, exId2); (exId2, exId1) ]} ∪ G.(com) ∧
            exId1 ∉ (elements G.(so)).*1 ∧ exId2 ∉ (elements G.(so)).*1 ∧
            eventgraph_consistent G' ∧ ExchangerConsistent G' ⌝ ∗
          @{V'} ExchangerLocal EI N γg ex G' M'
          (* else if my event comes in earlier *)
          ∨ ⌜ (exId1 < exId2)%nat ∧ b2 = true ∧
              G'.(so) = G.(so) ∧ G'.(com) = G.(com) ⌝ ∗
          @{V'} ExchangerLocal EI N γg ex G' (M' ∖ {[exId2]})))
  )%I.

Definition exchange_priv_post' EI N ex γg v1 (Φ : val → vProp) : exchange_postT :=
  (λ G V' G' exId1 exId2 v2 Vex1 Vex2 M',
    exchange_priv_post (ExchangerLocal EI) N ex γg v1 G V' G'
                       exId1 exId2 v2 Vex1 Vex2 M'
    -∗ Φ #v2)%I.

Definition exchange_AU_proof
  (EI : bool → vProp) N
  ex γg G1 M V v1 (Φ : val → vProp)
  {TA' TB' : tele} (α' : TA' → vProp) (β' Φ' : TA' → TB' → vProp)
  : vProp :=
  atomic_update_proof EI (⊤ ∖ ↑N) (↑histN)
    α' β' Φ'
    (tele_app (TT:= [tele _]) (exchange_AU_atomic_pre ExchangerInv γg))
    (λ b1 b2,
      tele_app (TT:= [tele _])
      (λ G, tele_app (TT:= [tele _ _ _ _ _ _ _ _])
      (exchange_AU_atomic_post' EI N ex γg G1 M V v1 b1 b2 G)))
    (tele_app (TT:= [tele _])
      (λ G, tele_app (TT:= [tele _ _ _ _ _ _ _ _])
      (exchange_priv_post' EI N ex γg v1 Φ G)))
  .

Definition exchange_piggyback_spec'
  (exchange : val) : Prop :=
  ∀ (EI : bool → vProp) `(∀ b, Objective (EI b))
    N (DISJ1 : N ## histN)
    (ex: loc) tid γg G1 M (V : view) (v1 : Z) (Posx: 0 ≤ v1),
  (* PRIVATE PRE *)
  (* G1 is a graph snapshot, locally observed by M *)
  ⊒V -∗ ExchangerLocal EI N γg ex G1 M -∗ inv (xchgUN N) (EI true) -∗
  ∀ (Φ : val → vProp),
    ∀ (TA' TB' : tele) (α' : TA' → vProp) (β' Φ' : TA' → TB' → vProp),
    (□ exchange_AU_proof EI N ex γg G1 M V v1 Φ α' β' Φ') -∗
    atomic_update (⊤ ∖ ↑N) (↑histN) α' β' Φ' -∗
    WP (exchange [ #ex ; #v1]) @ tid; ⊤ {{ Φ }}.

Definition new_exchanger_piggyback_spec'
  (new_exchanger : val) : Prop :=
  ∀ tid,
  {{{ True }}}
    new_exchanger [] @ tid; ⊤
  {{{ γg (ex : loc), RET #ex;
      ExchangerInv γg 1%Qp ∅ ∗ (∀ E EI N, |={E}=> ExchangerLocal EI N γg ex ∅ ∅) }}}.
End piggyback.

(** Difference with [ExchangerInv_ExchangerConsistent]: the mask [↑N ∖ ↑(xchgUN N)]. *)
Definition ExchangerInv_ExchangerConsistent_piggyback
  {Σ} `{!noprolG Σ, !inG Σ (graphR xchg_event)}
  (ExchangerLocal :  ExchangerLocalNT Σ)
  (ExchangerInv : ExchangerInvT Σ)
  : Prop :=
  ∀ N γg x q G G' M',
    ExchangerInv γg q G -∗ ExchangerLocal N γg x G' M'
    ={↑N ∖ ↑(xchgUN N)}=∗ ⌜ eventgraph_consistent G ∧ ExchangerConsistent G ⌝ ∗
            ExchangerInv γg q G.

Definition ExchangerLocal_union'
  {Σ} `{!noprolG Σ, !inG Σ (graphR xchg_event)}
  (ExchangerLocal :  ExchangerLocalNT Σ)
  (ExchangerInv : ExchangerInvT Σ)
  : Prop :=
  ∀ N γg x q G G1 G2 M1 M2,
    ExchangerInv γg q G -∗
    ExchangerLocal N γg x G1 M1 -∗ ExchangerLocal N γg x G2 M2 -∗
    ExchangerLocal N γg x G (M1 ∪ M2).

Definition ExchangerLocal_upgrade'
  {Σ} `{!noprolG Σ, !inG Σ (graphR xchg_event)}
  (ExchangerLocal :  ExchangerLocalT Σ)
  (ExchangerInv : ExchangerInvT Σ)
  : Prop :=
  ∀ γg x q G' G M,
  ExchangerInv γg q G' -∗
  ExchangerLocal γg x G M -∗ ExchangerLocal γg x G' M.

Definition ExchangerLocal_from'
  {Σ} `{!noprolG Σ, !inG Σ (graphR xchg_event)}
  (ExchangerLocal1 ExchangerLocal2 : ExchangerLocalT Σ)
  : Prop :=
  ∀ γg x G M, ExchangerLocal1 γg x G M ⊢ ExchangerLocal2 γg x G M.
Definition ExchangerLocal_to'
  {Σ} `{!noprolG Σ, !inG Σ (graphR xchg_event)}
  (ExchangerLocal1 ExchangerLocal2 : ExchangerLocalT Σ)
  : Prop :=
  ∀ γg x G' M' G M,
    ExchangerLocal2 γg x G M -∗ ExchangerLocal1 γg x G' M' -∗
    ExchangerLocal1 γg x G M.

Record exchanger_piggyback_spec {Σ} `{!noprolG Σ, !inG Σ (graphR xchg_event)}
  := ExchangerPiggyBackSpec {
  (** operations *)
  new_exchanger : val;
  exchange : val;

  (** predicates *)
  ExchangerLocal : (bool → vProp Σ) → ExchangerLocalNT Σ;
  ExchangerLocalLite : ExchangerLocalT Σ;
  ExchangerInv : ExchangerInvT Σ;

  (** predicates properties *)
  (* ExchangerInv *)
  ExchangerInv_Timeless : ∀ γg q G, Timeless (ExchangerInv γg q G);
  ExchangerInv_Objective : ∀ γg q G, Objective (ExchangerInv γg q G);
  ExchangerInv_Fractional : ∀ γg G, Fractional (λ q, ExchangerInv γg q G);
  ExchangerInv_AsFractional :
    ∀ γg q G, AsFractional (ExchangerInv γg q G) (λ q, ExchangerInv γg q G) q ;

  ExchangerInv_ExchangerConsistent :
    ∀ EI, ExchangerInv_ExchangerConsistent_piggyback (ExchangerLocal EI) ExchangerInv ;
  ExchangerInv_graph_master_acc :
    ExchangerInv_graph_master_acc' ExchangerInv ;
  ExchangerInv_graph_snap :
    ExchangerInv_graph_snap' ExchangerInv ;
  ExchangerInv_agree :
    ExchangerInv_agree' ExchangerInv ;

  (* ExchangerLocal *)
  ExchangerLocal_Persistent :
    ∀ EI N γg x G M, Persistent (ExchangerLocal EI N γg x G M);

  ExchangerLocal_graph_snap :
    ∀ EI N, ExchangerLocal_graph_snap' (ExchangerLocal EI N) ;
  ExchangerLocal_upgrade :
    ∀ EI N, ExchangerLocal_upgrade' (ExchangerLocal EI N) ExchangerInv ;
  ExchangerLocal_union :
    ∀ EI, ExchangerLocal_union' (ExchangerLocal EI) ExchangerInv ;

  (* ExchangerLocalLite *)
  ExchangerLocalLite_Persistent :
    ∀ γg x G M, Persistent (ExchangerLocalLite γg x G M);
  ExchangerLocalLite_Timeless :
    ∀ γg x G M, Timeless (ExchangerLocalLite γg x G M);

  ExchangerLocalLite_graph_snap :
    ExchangerLocal_graph_snap' ExchangerLocalLite ;
  ExchangerLocalLite_from :
    ∀ EI N, ExchangerLocal_from' (ExchangerLocal EI N) ExchangerLocalLite ;
  ExchangerLocalLite_to :
    ∀ EI N, ExchangerLocal_to' (ExchangerLocal EI N) ExchangerLocalLite ;
  ExchangerLocalLite_upgrade :
    ExchangerLocal_upgrade' ExchangerLocalLite ExchangerInv ;

  (** operations specs *)
  new_exchanger_spec : new_exchanger_piggyback_spec' ExchangerLocal ExchangerInv new_exchanger;
  exchange_spec : exchange_piggyback_spec' ExchangerLocal ExchangerInv exchange;
}.

Arguments exchanger_piggyback_spec _ {_ _}.
