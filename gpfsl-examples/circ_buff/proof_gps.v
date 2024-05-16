From stdpp Require Import namespaces.
From iris.algebra Require Import coPset.
From iris.bi Require Import big_op.
From iris.proofmode Require Import proofmode.

From gpfsl.logic Require Import proofmode.
From gpfsl.gps Require Import surface_iSP protocols escrows.
From gpfsl.logic Require Import new_delete.

From gpfsl.examples Require Import nat_tokens.
From gpfsl.examples.circ_buff Require Import code.

Require Import iris.prelude.options.

Local Notation wi := 0%nat (only parsing).
Local Notation ri := 1%nat (only parsing).
Local Notation b := 2%nat (only parsing).

(** This is the formalization of Circular Buffer from the original GPS paper.
  This proof is further simplified by using single writer protocols. **)

Notation circBufR := (prodUR (coPset_disjUR) (coPset_disjUR)).

Class cbG Σ := CbG {
  cb_tokG : inG Σ circBufR ;
  cb_gps_protG : gpsG Σ natProtocol
}.
Local Existing Instances cb_tokG cb_gps_protG.

Definition cbΣ : gFunctors := #[GFunctor (constRF circBufR); gpsΣ natProtocol].

Global Instance subG_cbΣ {Σ} : subG cbΣ Σ → cbG Σ.
Proof. solve_inG. Qed.

(* Namespace for the invariant *)
Definition circbufN (q: loc) := nroot .@ "circbufN" .@ q.

Local Open Scope Z_scope.

Section Interp.
Context `{!noprolG Σ, cirbG: !cbG Σ, !atomicG Σ}
        (Ns: nat) (P: lit → vProp Σ).
Implicit Types (γ: gname) (i j: nat) (q: loc).

Local Notation vProp := (vProp Σ).

Definition pTok γ i : vProp := ⎡ own γ (CoPset {[Pos.of_succ_nat i]}, ε) ⎤%I.
Definition pToks_from γ i : vProp := ⎡ own γ (CoPset $ coPset_from_ex i, ε) ⎤%I.
Definition cTok γ i : vProp := ⎡ own γ (ε, CoPset {[Pos.of_succ_nat i]}) ⎤%I.
Definition cToks_from γ i : vProp := ⎡ own γ (ε, CoPset $ coPset_from_ex i) ⎤%I.

Definition loc_at q i : loc := q >> (b + i `mod` Ns).

Definition PE γ q i : vProp := [es pTok γ i ⇝ (loc_at q i) ↦ - ]%I.
Definition CE γ q i : vProp := [es cTok γ i ⇝ ∃ v, P v ∗ (loc_at q i) ↦ #v]%I.

Definition PP (γq: gname * loc) i (v: val): vProp :=
  (⌜∃ z: Z, v = #z ∧ z = i `mod` Ns⌝ ∧ ∀ (j: nat), ⌜j < i⌝ → CE (γq.1) (γq.2) j)%I.
Definition CP (γq: gname * loc) i (v: val): vProp :=
  (⌜∃ z: Z, v = #z ∧ z = i `mod` Ns⌝ ∧ ∀ (j: nat), ⌜j < i + Ns⌝ → PE (γq.1) (γq.2) j)%I.

Global Instance PP_persistent γq i v: Persistent (PP γq i v) := _.
Global Instance CP_persistent γq i v: Persistent (CP γq i v) := _.

Definition prodInt γ q : interpO Σ natProtocol :=
  (λ _ _ _ _ s v, PP (γ, q) s v)%I.
Definition consInt γ q : interpO Σ natProtocol :=
  (λ _ _ _ _ s v, CP (γ, q) s v)%I.

Definition Prod q : vProp :=
  (∃ γ i j, ⌜i < j + Ns⌝
      ∗ (∃ ti vi γi, GPS_iSP_Writer (circbufN q) (prodInt γ q) (prodInt γ q false)
                                    (q >> wi) ti i vi γi)
      ∗ (∃ tj vj γj, GPS_iSP_Reader (circbufN q) (consInt γ q) (consInt γ q false)
                                    (q >> ri) tj j vj γj)
      ∗ pToks_from γ i)%I.

Definition Cons q : vProp :=
  (∃ γ i j, ⌜j ≤ i⌝
      ∗ (∃ ti vi γi, GPS_iSP_Reader (circbufN q) (prodInt γ q) (prodInt γ q false)
                                    (q >> wi) ti i vi γi)
      ∗ (∃ tj vj γj, GPS_iSP_Writer (circbufN q) (consInt γ q) (consInt γ q false)
                                    (q >> ri) tj j vj γj)
      ∗ cToks_from γ j)%I.

End Interp.

Section Properties.
Context `{!noprolG Σ, cirbG: !cbG Σ, !atomicG Σ}.

Lemma pTok_exclusive γ i: pTok γ i ∗ pTok γ i ⊢ False.
Proof.
  iIntros "[T1 T2]".
  iCombine "T1 T2" gives %[Valid _].
  exfalso. simpl in Valid.
  rewrite -> coPset_disj_valid_op, disjoint_singleton_l in Valid.
  by apply Valid, elem_of_singleton.
Qed.

Lemma cTok_exclusive γ i: cTok γ i ∗ cTok γ i ⊢ False.
Proof.
  iIntros "[T1 T2]".
  iCombine "T1 T2" gives %[_ Valid].
  exfalso. simpl in Valid.
  rewrite ->coPset_disj_valid_op, disjoint_singleton_l in Valid.
  by apply Valid, elem_of_singleton.
Qed.

Lemma pToks_from_extract γ i :
  pToks_from γ i ⊢ pTok γ i ∗ pToks_from γ (S i).
Proof.
  rewrite -embed_sep -own_op -pair_op left_id.
  rewrite coPset_disj_union; [|apply coPset_from_disjoint].
  by rewrite -coPset_from_insert.
Qed.

Lemma cToks_from_extract γ i :
  cToks_from γ i ⊢ cTok γ i ∗ cToks_from γ (S i).
Proof.
  iIntros "Toks".
  rewrite -embed_sep -own_op -pair_op left_id.
  rewrite coPset_disj_union; [|apply coPset_from_disjoint].
  by rewrite -coPset_from_insert.
Qed.

Lemma pToks_cToks_split γ i:
  ⎡ own γ (CoPset $ coPset_from_ex i, CoPset $ coPset_from_ex i) ⎤%I
  ⊢ pToks_from γ i ∗ cToks_from γ i.
Proof.
  by rewrite -embed_sep -own_op -pair_op right_id left_id.
Qed.

Lemma cb_escrows_list_alloc Ns γ q (ni: nat):
  (ni ≤ Ns)%nat →
  (([∗ list] i ∈ seq b ni, (q >> (i: nat)) ↦ #☠)
  ={↑escrowN}=∗ [∗ list] i ∈ seq 0 ni, PE Ns γ q i).
Proof.
  move => Le. iIntros "OL".
  iApply big_sepL_fupd.
  rewrite -2!fmap_S_seq -list_fmap_compose big_sepL_fmap.
  iApply (big_sepL_mono with "OL").
  iIntros (? i H) "ol".
  apply lookup_seq in H as [H1 H2]. simpl in H1. subst k.
  rewrite (_: (S ∘ S) i = b + i `mod` Ns)%nat.
  - iApply (escrow_alloc with "[ol]"); [done|].
    iNext. by iExists _.
  - rewrite Nat.mod_small; [done|lia].
Qed.

End Properties.

Section proof.
Context `{!noprolG Σ, cirbG: !cbG Σ, !atomicG Σ}
        (Ns: nat) (P: lit → vProp Σ).
Implicit Types (γ: gname) (i j: nat) (q: loc).

Lemma new_buffer_spec tid (nGt1 : 0 < Ns):
  {{{ True }}}
      new_buffer Ns [] @ tid; ⊤
  {{{ (q: loc), RET #q; Prod Ns P q ∗ Cons Ns P q }}}.
Proof.
  iIntros (Φ) "_ Post".
  wp_lam. wp_op.
  (* allocate buffer *)
  wp_apply wp_new; [done|lia|done|].
  iIntros (q) "([H†|%] & oLs & Hm)"; [|lia].

  (* allocate ghost and escrows *)
  iMod (own_alloc (CoPset $ coPset_from_ex 0, CoPset $ coPset_from_ex 0))
      as (γ) "Toks"; [done|].
  iDestruct (pToks_cToks_split with "Toks") as "(Prod & Cons)".

  rewrite (_ : Z.to_nat (Ns + b) = S $ S $ Z.to_nat Ns); last first.
    { rewrite Z2Nat.inj_add; [|lia..].
      rewrite (_: Z.to_nat 2 = 2%nat); last auto. lia. }

  rewrite own_loc_na_vec_repeat 2!big_sepL_cons.
  iDestruct "oLs" as "(owi & ori & oLs)". rewrite -(Nat2Z.id 2).
  iPoseProof (cb_escrows_list_alloc Ns γ with "oLs") as "oLs"; [lia|].
  iMod (fupd_mask_mono with "oLs") as "#oLs"; [done|].

  (* init indexes *)
  (* sequential reasoning *)
  wp_pures. wp_write.

  iMod (GPS_iSP_Init (circbufN q) (consInt Ns γ q) (consInt Ns γ q false) _ O
          with "ori []") as (γj tj) "ConsP".
  { iIntros (t1 γ1) "!>". iSplit.
    - iPureIntro. by exists 0.
    - iIntros (i Lt). iApply (big_sepL_elem_of with "oLs").
      apply elem_of_list_In, in_seq. split; [lia|].
      rewrite Nat2Z.inj_lt Nat2Z.inj_add Z2Nat.id; lia. }

  iApply wp_fupd.

  wp_op. wp_write.

  iMod (GPS_iSP_Init (circbufN q) (prodInt Ns P γ q) (prodInt Ns P γ q false) _ O
          with "owi []") as (γi ti) "ProdP".
  { iIntros (t1 γ1) "!>". iSplit.
    - iPureIntro. by exists 0.
    - iIntros (j ?). lia. }

  iDestruct (GPS_iSP_SWWriter_Reader with "ConsP") as "#ConsPR".
  iDestruct (GPS_iSP_SWWriter_Reader with "ProdP") as "#ProdPR".

  (* can be automated *)
  iModIntro. iApply "Post". rewrite /Prod /Cons.
  iSplitL "ProdP Prod"; iExists γ, O, O;
    (iSplit; [iPureIntro; lia|]).
  - iSplitL "ProdP"; last iSplitR "Prod"; [..|done]; by iExists _,_,_.
  - iSplitL ""; last iSplitR "Cons"; [..|done]; by iExists _,_,_.
Qed.

Lemma try_prod_spec q v tid (nGt1 : 0 < Ns):
  {{{ Prod Ns P q ∗ P v }}}
      try_prod Ns [ #q; #v] @ tid; ⊤
  {{{ (b: Z), RET #b;
        Prod Ns P q ∗ (⌜b ≠ 0⌝ ∨ P v) }}}.
Proof.
  iIntros (Φ) "[Prod P] Post".
  wp_lam.

  iDestruct "Prod" as (γ i j0 Lti) "(pW & cR & pToks)".
  iDestruct "pW" as (ti vi γi) "pW".

  (* read wi *)
  wp_op.
  wp_apply (GPS_iSP_SWRead (circbufN q) (prodInt Ns P γ q) (prodInt Ns P γ q false)
              (prodInt Ns P γ q true (q >> wi) γi ti i vi) with "[$pW]");
              [solve_ndisj|done|done|by right|..].
  { by iIntros "!> !> #$". }

  iIntros "(pW & Eq & #CEs)". iDestruct "Eq" as %(w & -> & ->).
  wp_pures.

  (* read ri *)
  iDestruct "cR" as (tr vr γr) "#cR".
  wp_apply (GPS_iSP_Read (circbufN q) (consInt Ns γ q) (consInt Ns γ q false)
              (consInt Ns γ q false (q >> ri) γr) with "[$cR]");
              [solve_ndisj|done|done|by right|..].
  { iIntros "!>" (t' s' v' Lt') "!>"; iSplit; last iSplit; by iIntros "#$". }

  iIntros (t2 j rz) "([Lej _] & cR2 & Eq & #PEs)".
  iDestruct "Eq" as %(? & -> & ->). iDestruct "Lej" as %Lej%inj_le.

  wp_pures.

  rewrite -!Nat2Z.inj_mod -(Nat2Z.inj_add _ 1)
          -Nat2Z.inj_mod Nat.add_mod_idemp_l; [|lia].
  case (bool_decide _) eqn:Eqr.
  - (* buffer full *)
    wp_finish. iApply "Post". iSplitR "P"; last by iRight.
    iExists γ, i, j.
    iSplit; last iSplitL "pW"; last iSplitR "pToks"; [..|done].
    + iPureIntro. lia.
    + by iExists _, _, _.
    + by iExists _, _, _.

  - wp_pures.
    iDestruct (pToks_from_extract with "pToks") as "(iTok & pToks)".
    iPoseProof ("PEs" $! i with "[%]") as "PEi"; [lia|].

    iMod (escrow_elim (pTok γ i) with "[] PEi [$iTok]") as ">oL"; [done|..].
    { iIntros "pTok". iApply (pTok_exclusive with "pTok"). }

    iDestruct "oL" as (v1) "oL".
    rewrite Z2Nat.inj_add; [|lia..]. rewrite Nat2Z.id.
    wp_write. wp_op.

    iMod (escrow_alloc (cTok γ i) (∃ v, P v ∗ (loc_at Ns q i) ↦ #v)%I
          with "[P oL]") as "#CEi"; [done|..].
    { iNext. iExists v. by iFrame "P oL". }

    wp_apply (GPS_iSP_SWWrite_rel (circbufN q) (prodInt Ns P γ q)
                (prodInt Ns P γ q false) (q >> wi)
                (λ t, GPS_iSP_Writer (circbufN q) (prodInt Ns P γ q)
                      (prodInt Ns P γ q false)  (q >> wi) t ((i + 1)%nat : natProtocol)
                      #((i + 1) `mod` Ns)%nat γi)%I
                (prodInt Ns P γ q false (q >> wi) γi ti i #(i `mod` Ns)%nat)
                (prodInt Ns P γ q true (q >> wi) γi ti i #(i `mod` Ns)%nat)
                _ _ (i + 1)%nat _ #((i + 1) `mod` Ns)%nat
                with "[$pW]"); [solve_ndisj|done|done|apply Nat.le_add_r|..].
    { iSplitR ""; iNext; [|by iIntros "!> #$"].
      iIntros (t' Lt') "$ F !>". iSplitL ""; [by iIntros "!> $"|].
      iIntros "!>". iSplit.
      - iPureIntro. exists ((i + 1) `mod` Ns)%nat. by rewrite -Nat2Z.inj_mod.
      - iIntros (j1 Lt1%Nat2Z.inj_lt).
        rewrite Nat.add_1_r in Lt1.
        apply (Nat.lt_succ_r j1),  Nat.le_lteq in Lt1 as [Lt| ->].
        + iApply "CEs". iPureIntro. lia.
        + by iFrame "CEi". }
    iIntros (ti2) "(% & _ & pW)".
    wp_let. iApply "Post".
    iSplitR ""; [|by iLeft].
    iExists γ, (i + 1)%nat, j.
    iSplitL ""; last iSplitL "pW"; last iSplitR "pToks".
    + iPureIntro.
      have Lti' : i + 1 ≤ j + Ns by lia.
      apply Z.le_lteq in Lti' as [?|Eqi]; [lia|].
      exfalso.
      apply bool_decide_eq_false in Eqr. apply Eqr.
      move : Eqi. rewrite -Nat2Z.inj_add -(Nat2Z.inj_add _ 1).
      intros ->%Nat2Z.inj. f_equal.
      rewrite -{1}(Nat.mul_1_l Ns) Nat.mod_add; [done|lia].
    + by iExists _, _, _.
    + by iExists _, _, _.
    + rewrite Nat.add_1_r. by iFrame "pToks".
Qed.

Lemma try_cons_spec q tid (nGt1 : 0 < Ns):
  {{{ Cons Ns P q }}}
      try_cons Ns [ #q] @ tid; ⊤
  {{{ (v: lit), RET #v; Cons Ns P q ∗ (⌜v = 0⌝ ∨ P v) }}}.
Proof.
  iIntros (Φ) "Cons Post". iDestruct "Cons" as (γ i0 j Lej) "(pR & cW & cToks)".
  wp_lam.

  (* read wi *)
  wp_op. iDestruct "pR" as (ti vi γi) "pR".
  wp_apply (GPS_iSP_Read (circbufN q) (prodInt Ns P γ q)
              (prodInt Ns P γ q false)
              (prodInt Ns P γ q false (q >> wi) γi) with "[$pR]");
              [solve_ndisj|done|done|by right|..].
  { iIntros "!>" (t' s' v' Lt') "!>"; iSplit; last iSplit; by iIntros "#$". }

  iIntros (t1 i pz) "([Lei _] & pR2 & Eq & #CEs)".
  iDestruct "Eq" as %(p & ? & ?). subst pz p. iDestruct "Lei" as %Lei%inj_le.
  wp_let.

  (* read ci *)
  wp_op. iDestruct "cW" as (tj vj γj) "cW".
  wp_apply (GPS_iSP_SWRead (circbufN q) (consInt Ns γ q) (consInt Ns γ q false)
              (consInt Ns γ q true (q >> ri) γj tj j vj) with "[$cW]");
              [solve_ndisj|done|done|by right|..].
  { by iIntros "!> !> #$". }

  iIntros "(cW & Eq & #PEs)".
  iDestruct "Eq" as %(r & ? & ?). subst vj r.

  wp_let. wp_op.

  case (bool_decide _) eqn:Eqr.
  (* case (decide (i `mod` Ns = j `mod` Ns)) => [Eqr|NEqr]. *)
  - wp_case. iApply "Post". iSplitR ""; [|by iLeft].
    iExists γ, i, j.
    iSplit; last iSplitL "pR2"; last iSplitR "cToks"; [..|done].
    + iPureIntro. lia.
    + by iExists _, _, _.
    + by iExists _, _, _.
  - wp_case. wp_op. wp_op.

    apply bool_decide_eq_false in Eqr.
    assert (j < i). (* arithmetic *)
    { assert (HLe: j ≤ i) by lia.
      apply Z.le_lteq in HLe as [?|Eq]; first auto.
      exfalso. apply Eqr. by rewrite Eq. }

  (* consume the escrow *)
  iDestruct (cToks_from_extract with "cToks") as "(jTok & cToks)".
  iDestruct ("CEs" $! j with "[%]") as "CEj"; [done|].
  iMod (escrow_elim with "[] CEj jTok") as (v) "[P >oL]"; [done|..].
  { iIntros "cTok". iApply (cTok_exclusive with "cTok"). }

  rewrite -!Nat2Z.inj_mod Z2Nat.inj_add; [|lia..]. rewrite Nat2Z.id.
  (* read the value *)
  wp_read. wp_let.

  (* return the location as ready for reproducing, by putting it in an ecsrow *)
  iMod (escrow_alloc (pTok γ (j + Z.to_nat Ns)%nat)
              (loc_at Ns q (j + Z.to_nat Ns)%nat ↦ -)%I with "[oL]") as "#PEj";
              [done|..].
  { rewrite Nat2Z.id (_: loc_at Ns q (j + Ns) = loc_at Ns q j).
    - iExists #v. by iFrame "oL".
    - rewrite /loc_at. do 2 f_equal.
      rewrite -{1}(Nat.mul_1_l Ns) Nat.mod_add; [done|lia]. }

  wp_op. wp_op. wp_op.
  rewrite -(Nat2Z.inj_add _ 1) -Nat2Z.inj_mod Nat.add_mod_idemp_l; [|lia].

  wp_apply (GPS_iSP_SWWrite_rel (circbufN q) (consInt Ns γ q)
                (consInt Ns γ q false) (q >> ri)
                (λ t, GPS_iSP_Writer (circbufN q) (consInt Ns γ q)
                      (consInt Ns γ q false) (q >> ri) t ((j + 1)%nat : natProtocol)
                      #((j + 1) `mod` Ns)%nat γj)%I
                (consInt Ns γ q false (q >> ri) γj tj j #(j `mod` Ns)%nat)
                (consInt Ns γ q true (q >> ri) γj tj j #(j `mod` Ns)%nat)
                _ _ (j + 1)%nat _ #((j + 1) `mod` Ns)%nat
                with "[$cW]"); [solve_ndisj|done|done|apply Nat.le_add_r|..].
    { iSplitR ""; iNext; [|by iIntros "!> #$"].
      iIntros (t' Lt') "$ F !>". iSplitL ""; [by iIntros "!> $"|].
      iIntros "!>". iSplit.
      - iPureIntro. exists ((j + 1) `mod` Ns)%nat. by rewrite -Nat2Z.inj_mod.
      - iIntros (j1 Lt1).
        rewrite Nat.add_1_r Nat2Z.inj_succ Z.add_succ_l in Lt1.
        apply Zlt_succ_le, Z.le_lteq in Lt1 as [Lt|Eq].
        + by iApply ("PEs" $! _ Lt).
        + rewrite -(Nat2Z.id j) -Z2Nat.inj_add -?Eq ?Nat2Z.id;
            [by iFrame "PEj"|lia..]. }
    iIntros (tj2) "(% & _ & cW)".
    wp_let. iApply "Post".
    iSplitR "P"; [|by iRight].
    iExists γ, i, (j + 1)%nat.
    iSplitL ""; [iPureIntro; rewrite Nat2Z.inj_add; lia|].
    iSplitL "pR2"; last iSplitR "cToks".
    + by iExists _, _, _.
    + by iExists _, _, _.
    + rewrite Nat.add_1_r. by iFrame "cToks".
Qed.

End proof.

#[global] Typeclasses Opaque Prod Cons.
