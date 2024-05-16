From iris.algebra Require Import excl_auth.

From gpfsl.logic Require Import logatom invariants proofmode.

From gpfsl.examples.exchanger Require Import spec_graph.

Require Import iris.prelude.options.

Local Notation event_list := (event_list xchg_event).
Local Notation graph := (graph xchg_event).

Implicit Type (G : graph) (E : event_list) (N : namespace) (b : bool).

Local Notation flag := 0%Z (only parsing).

(* TODO: we need a simpler base spec, working directly with graphs is terrible *)

Section ex.
  Context `{!noprolG Σ, !inG Σ (graphR xchg_event),
            eaG: !inG Σ (excl_authR (leibnizO bool)) }.
  Context `(ex : exchanger_spec Σ).

  Local Notation vProp := (vProp Σ).

  (* TODO: we shouldn't need Σ and co to write this code *)
  Definition mp_exchange : val :=
    λ: ["ex"],
      Fork (
        ex.(exchange) [ "ex" ; #1 ]
      );;
      ex.(exchange) [ "ex" ; #2 ].

  Local Existing Instance ExchangerInv_Objective.
  Local Existing Instance ExchangerInv_Timeless.
  Local Existing Instance ExchangerLocal_Persistent.

  Local Definition list_max_2 E b1 b2 : Prop :=
    length E = ((Nat.b2n b1) + (Nat.b2n b2))%nat.

  Local Lemma list_max_2_max_2 E b1 b2 :
    list_max_2 E b1 b2 → (length E ≤ 2)%nat.
  Proof.
    rewrite /list_max_2. destruct b1, b2; simpl; intros ->; lia.
  Qed.

  (* Our internal invariant track if the threads have done their exchange,
    with b1 and b2. *)
  Local Definition ExInv γg γb1 γb2 : vProp :=
    ∃ G,
      ex.(ExchangerInv) γg 1%Qp G ∗
      ∃ b1 b2 , ⎡ own γb1 (●E b1) ∗ own γb2 (●E b2) ⎤ ∗
      ⌜ list_max_2 G.(Es) b1 b2 ∧
        (* if thread 1 is done, then the graph has the exchange of 1.
          We don't have the reverse for b2, because our spec is weak (see below). *)
        if b1 then ∃ i v2, ge_event <$> (G.(Es) !! i) = Some (Exchange 1 v2)
        else True ⌝.

  (* TODO: this is still a weak spec. It only says that the main thread's
    exchange, if succeeds, gets the value 1 from the forked thread.
    The stronger spec would be that if one thread's exchange succeeds, the other
    thread's exchange also succeeds, and they match.
    That is, ret_1 = 2 <-> ret_2 = 1.
    
    Furthermore, it should just work with the full ownership of any graph G, not
    just the initial graph ∅. *)
  Lemma mp_exchange_spec N N'
    (DISJ: N ## histN) (DISJ': N' ## histN) (DISJN : N ## N')
    γg (e : loc) tid :
    {{{ ex.(ExchangerLocal) N γg e ∅ ∅ ∗ ex.(ExchangerInv) γg 1%Qp ∅ }}}
      mp_exchange [ #e ] @ tid; ⊤
    {{{ v, RET #v; ⌜ v = 1 ∨ v = -1 ⌝ }}}.
  Proof using eaG.
    iIntros (Φ) "[#HLocal Hex] Post".
    wp_lam.

    (* Allocate the invariant *)
    iMod (own_alloc (●E false ⋅ ◯E false)) as (γ1) "[Tokγ12 Tokγ11]";
      [apply excl_auth_valid|].
    iMod (own_alloc (●E false ⋅ ◯E false)) as (γ2) "[Tokγ22 Tokγ21]";
      [apply excl_auth_valid|].
    iMod (inv_alloc N' _ (ExInv γg γ1 γ2) with "[Hex Tokγ12 Tokγ22]") as "#II".
    { iNext; iExists ∅; iFrame.
      iExists false, false. rewrite /list_max_2 /=. by iFrame. }

    iDestruct (view_at_intro True%I with "[//]") as (V0) "[#sV0 _]".
    wp_apply (wp_fork with "[Tokγ11]"); [done|..].
    - iIntros "!>" (t').
      awp_apply (ex.(exchange_spec) with "sV0 HLocal"); [done..|].
      rewrite /atomic_acc /=.
      (* Open our client invariant to get the ghost state *)
      iInv "II" as (G') "[EI Hown]" "Close".
      (* Open extra masks to match the masks *)
      iMod (fupd_mask_subseteq (↑histN)) as "Close2"; [solve_ndisj|].
      (* now we can provide the public (atomic) precondition *)
      iIntros "!>". iExists _. iFrame "EI".
      iSplit.
      { (* peeking case *)
        iIntros "EI". iMod "Close2" as "_".
        iMod ("Close" with "[EI Hown]") as "_". { iNext. iExists _. iFrame. }
        by iFrame. }
      (* committing case *)
      iIntros (V1 G1 xchg1 xchg2 v2 Vx1 Vx2 M1) "(EI & #sV1 & %F & CASE)".
      destruct F as (SubG' & _ & _ & _ & EqX1 & EqEs & _).
      have EqL : length G1.(Es) = S (length G'.(Es)).
      { rewrite EqEs app_length /=. lia. }
      have EqLX1 : G1.(Es) !! xchg1 = Some (mkGraphEvent (Exchange 1 v2) Vx1 M1).
      { by rewrite EqEs EqX1 lookup_app_1_eq. }

      (* Close other masks *)
      iMod "Close2" as "_".
      (* Update the ghost state *)
      iDestruct "Hown" as (b1 b2) "[[>Hown1 Hown2] >[%Hsize _]]".
      iCombine "Hown1 Tokγ11" gives %->%excl_auth_agree_L.
      iMod (own_update_2 with "Hown1 Tokγ11") as "[Hown1 Tokγ11]".
      { apply (excl_auth_update _ _ true). }
      (* Close the client invariant *)
      iMod ("Close" with "[EI Tokγ11 Hown1 Hown2]") as "_".
      { iNext. iExists G1; iFrame "EI". iExists true, b2; iFrame.
        iPureIntro. split.
        - by rewrite /list_max_2 EqL Hsize /=.
        - exists xchg1, v2. by rewrite EqLX1. }
      (* trivial post condition for this thread *)
      by iIntros "!> _".

    - (* 2nd Thread *)
      iIntros "_".
      wp_lam.
      (* this is to get away with the later in the post condition *)
      iApply (wp_step_fupd _ _ ⊤ _ (∀ n0 : Z, ⌜n0 = 1 ∨ n0 = -1⌝ -∗ Φ #n0)%I
        with "[$Post]"); auto.
      awp_apply (ex.(exchange_spec) with "sV0 HLocal"); [done..|].
      rewrite /atomic_acc /=.
      iInv "II" as (G') "[EI Hown]" "Close".

      iMod (fupd_mask_subseteq (↑histN)) as "Close2"; [solve_ndisj|].
      (* now we can provide the public (atomic) precondition *)
      iIntros "!>". iExists _. iFrame "EI".
      iSplit.
      { (* peeking case *)
        iIntros "EI". iMod "Close2" as "_".
        iMod ("Close" with "[EI Hown]") as "_". { iNext. iExists _. iFrame. }
        by iFrame. }
      (* committing case *)
      iIntros (V1 G1 xchg1 xchg2 v2 Vx1 Vx2 M1) "(EI & #sV1 & %F & CASE)".
      destruct F as (SubG' & _ & EqV0 & EqV1 & EqX1 & EqEs & _).
      (* Close other masks *)
      iMod "Close2" as "_".
      iDestruct "Hown" as (b1 b2) "[[>Hown1 >Hown2] >[%Hsize %Eqb1]]".
      iCombine "Hown2 Tokγ21" gives %->%excl_auth_agree_L.
      iMod (own_update_2 with "Hown2 Tokγ21") as "[Hown2 Tokγ21]".
      { apply (excl_auth_update _ _ true). }

      have EqL : length G1.(Es) = S (length G'.(Es)).
      { rewrite EqEs app_length /=. lia. }

      (* Close the client invariant *)
      iMod ("Close" with "[EI Tokγ21 Hown1 Hown2 ]") as "_".
      { iNext. iExists G1; iFrame "EI". iExists b1, true; iFrame. iPureIntro.
        split.
        - rewrite /list_max_2 EqL Hsize /=; lia.
        - destruct b1; [|done]. destruct Eqb1 as (i & vi & Eqvi).
          apply list_lookup_fmap_inv' in Eqvi as (eVi & Eqe & Eqi).
          exists i, vi. rewrite (prefix_lookup_Some _ _ _ _ Eqi) /=; [|apply SubG'].
          by rewrite Eqe. }
      clear Hsize Eqb1. (* clear to avoid name clash *)

      iIntros "!> Hv2 Post".
      iDestruct "CASE" as "[[F EL]|[F SCASE]]".
      { (* FAILURE. *)
        iDestruct "F" as %(-> & EqSo & EqCo).
        iIntros "!>". iApply "Post"; auto. }

      (* SUCCEED. *)
      iDestruct "F" as %(Lev2 & _ & _ & _ & NEq12 & _).
      iInv "II" as (G2') "[>EI Hown]" "Close".

      iAssert (∃ G1' M1',
          ⌜ G1 ⊑ G1' ∧
            G1'.(Es) !! xchg2 = Some $ mkGraphEvent (Exchange v2 2) Vx2 M1 ⌝ ∗
          @{V1} ExchangerLocal ex N γg e G1' M1')%I
        with "[SCASE Hv2]" as (G1' M1' [LeG0 EqX2]) "EL".
      { iDestruct "SCASE" as "[[F EL] | [F EL]]".
        * iDestruct "F" as %(? & ? & ? & _).
          iExists G1, M1; iFrame. iPureIntro. split; [done|].
          eapply prefix_lookup_Some; [eauto|apply SubG'].
        * iDestruct "F" as %(? & ?).
          iDestruct ("Hv2" with "[%//]")
            as (G2 (LeG1 & EqX2 & EqEs2 & _)) "EL2".
          iExists G2, M1; iFrame; iPureIntro. split; [done|].
          by rewrite EqEs2 EqX2 lookup_app_1_eq. }

      iDestruct (view_at_elim with "sV1 EL") as "EL".
      iDestruct (ExchangerLocal_graph_snap with "EL") as "#Gs2".
      iMod (fupd_mask_subseteq (↑N)) as "Hclose"; [solve_ndisj|].
      iMod (ExchangerInv_ExchangerConsistent with "EI EL") as "[[% _] EI]".
      iDestruct (ExchangerInv_graph_snap with "EI Gs2") as %LeG2%graph_sqsubseteq_E.

      iMod "Hclose" as "_".
      iDestruct "Hown" as (b1' b2') "[Hown >[%Hsize %Eqb1]]".
      iMod ("Close" with "[Hown EI]") as "_".
      { iNext. iExists G2'. iFrame. iExists b1', b2'. by iFrame. }

      iIntros "!>". iApply "Post". iPureIntro.

      have EqLX1 : ge_event <$> G2'.(Es) !! xchg1 = Some (Exchange 2 v2).
      { rewrite (prefix_lookup_Some G1.(Es) _ _ (mkGraphEvent (Exchange 2 v2) Vx1 M1));
          [done|..].
        - by rewrite EqEs EqX1 lookup_app_1_eq.
        - etrans; [apply LeG0|done]. }
      have EqLX2 : ge_event <$> G2'.(Es) !! xchg2 = Some (Exchange v2 2).
      { by rewrite (prefix_lookup_Some _ _ _ _ EqX2). }
      have Lt12 : (xchg1 < length G2'.(Es))%nat.
      { clear -EqLX1.
        by apply list_lookup_fmap_inv' in EqLX1 as (? & _ & ?%lookup_lt_Some). }
      have Lt22 : (xchg2 < length G2'.(Es))%nat.
      { clear -EqLX2.
        by apply list_lookup_fmap_inv' in EqLX2 as (? & _ & ?%lookup_lt_Some). }

      destruct b1'.
      + (* if both threads are done, our arguments:
          (1) we have 0 ≤ xchg1, xchg2, xchgt < length G2'.(Es) ≤ 2
          (2) xchg1 ≠ xchg2, and xchgt ≠ xchg1 because xchg1 has value (2,v2)
            while xchgt has value (1,vt)
          So xchgt = xchg2 and v2 = 1 and v2 = 2. *)
        have LenG2' := list_max_2_max_2 _ _ _ Hsize.
        destruct Eqb1 as (xchgt & vt & EqLXt).
        have NEqt1 : xchg1 ≠ xchgt.
        { clear -EqLX1 EqLXt. intros ->. rewrite EqLX1 in EqLXt. congruence. }
        have Ltt2 : (xchgt < 2)%nat.
        { clear -LenG2' EqLXt.
          apply list_lookup_fmap_inv' in EqLXt as (? & _ & ?%lookup_lt_Some). lia. }
        have ?: xchgt = xchg2.
        { clear -Lt12 Lt22 Ltt2 NEqt1 NEq12 LenG2'. lia. }
        subst xchgt. rewrite EqLX2 in EqLXt. clear -EqLXt.
        inversion EqLXt. by left.

      + (* if only this thread is done, but the other hasn't:
          we only have 1 event in the graph, but xchg1 ≠ xchg2. *)
        exfalso. clear -Lt12 Lt22 NEq12 Hsize.
        have LtG2' : (length G2'.(Es) <= 1)%nat.
        { rewrite Hsize /=. clear; destruct b2'; simpl; lia. }
        lia.
  Qed.
End ex.
