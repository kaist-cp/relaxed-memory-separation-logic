From stdpp Require Import namespaces.
From iris.proofmode Require Import proofmode.

From gpfsl.base_logic Require Import frame_instances.
From gpfsl.logic Require Import proofmode.
From gpfsl.logic Require Import relacq new_delete.
From gpfsl.gps Require Import surface_iPP protocols.
From gpfsl.examples.stack Require Import spec_per_elem code_treiber.

Require Import iris.prelude.options.

Local Notation next := 0%nat (only parsing).
Local Notation data := 1%nat (only parsing).

(** Basic Treiber Stack in Release-Acquire **)
(* This implementation is memory-leaking, as it does not care about recollecting
   memory.
  Furthermore, this implementation uses 0 and -1 as flags for EMPTY and
  FAIL_RACE repsectively, so if the client should not push elements with those
  values, otherwise they'll lose resources.

  In order to support reclamation, we will need to track the freeable resources
  more closely, and abandon [ReachableD] (see below). That may mean abandoning
  GPS protocol altogether. *)

(* Namespace for the invariant *)
Definition tstackN (s: loc) := nroot .@ "tstackN" .@ s.

Section defs.
Context `{!noprolG Σ} (P: Z → vProp Σ).
Local Notation vProp := (vProp Σ).

(* Reachable takes a list [A] of values that are linked together by some
  locations. These locations are existentially quantified as [n']. *)
Definition Reachable'
  :  (lit -d> list Z -d> vPropO Σ) -d> lit -d> list Z -d> vPropO Σ
  := (fun F l A =>
        match A with
        | nil     => ⌜l = 0⌝
        | v :: A' => ∃ l', ⌜l = (LitLoc l')⌝ ∗
                      (* freeable resource is only needed for reclamation, which
                        is not done yet *)
                      ⎡ † l' … 2 ⎤ ∗
                      (l' >> data) ↦ #v ∗ P v ∗ ∃ q (n': lit),
                      (l' >> next) ↦{q} #n' ∗ ▷ F n' A'
        end)%I.

Instance Reachable'_contractive : Contractive Reachable'.
Proof.
  intros ? ? ? H ? A.
  destruct A as [|v A]; [done|].
  apply bi.exist_ne => ?.
  repeat (apply bi.sep_ne; [done|]).
  do 2 (apply bi.exist_ne => ?).
  repeat (apply bi.sep_ne; [done|]).
  f_contractive. by apply H.
Qed.

Definition Reachable := fixpoint Reachable'.

(* ReachableD takes a list [A] of locations that are linked together. *)
Definition ReachableD'
  :  (lit -d> list lit -d> vPropO Σ) -d> lit -d> list lit -d> vPropO Σ
  := (fun F l A =>
        match A with
        | nil     => ⌜l = 0⌝
        | v :: A' => ∃ l', ⌜l = (LitLoc l')⌝ ∗ ∃ q,
                      (l' >> next) ↦{q} #v ∗ ▷ F v A'
        end)%I.

Instance ReachableD'_contractive : Contractive ReachableD'.
Proof.
  intros ? ? ? H ? A.
  destruct A as [|v A]; [done|].
  apply bi.exist_ne => ?.
  apply bi.sep_ne; [done|].
  apply bi.exist_ne => ?.
  apply bi.sep_ne; [done|].
  f_contractive. by apply H.
Qed.

Definition ReachableD := fixpoint ReachableD'.

End defs.

Section prot.
Context `{!noprolG Σ, !gpsG Σ unitProtocol, !atomicG Σ} (P: Z → vProp Σ).
Local Notation vProp := (vProp Σ).

Definition Head : interpO Σ unitProtocol
  := (λ b _ _ _ _ v, ∃ (l: lit), ⌜v = #l⌝ ∧
      if b then ∃ A, Reachable P l A else ∃ A, ReachableD l A)%I.

Definition TStack s : vProp
  := (∃ γ t v, GPS_iPP (tstackN s) Head s t () v γ)%I.

Global Instance TStack_persistent s : Persistent (TStack s) := _.

Lemma Head_dup_dup l γ t s v:
  Head false l γ t s v -∗ Head false l γ t s v ∗ Head false l γ t s v.
Proof.
  iDestruct 1 as (h ?) "Head". subst v.
  iDestruct "Head" as (A) "Head".
  rewrite /ReachableD (fixpoint_unfold ReachableD' _ _).
  revert h. induction A as [|h' A' IH] => h.
  - iDestruct "Head" as "%". subst h.
    iSplitL; iExists 0; (iSplit; [done|]); iExists [];
      by rewrite /ReachableD (fixpoint_unfold ReachableD' _ _).
  - iDestruct "Head" as (h0 ? q) "[next Head]". subst h.
    iAssert (▷ (Head false l γ t s #h' ∗ Head false l γ t s #h'))%I
      with "[Head]" as "(Hn1 & Hn2)".
    { iNext. rewrite /ReachableD (fixpoint_unfold ReachableD' _ _ ).
      by apply IH. } clear IH.
    iDestruct "next" as "[Hq1 Hq2]".
    iSplitL "Hn1 Hq1"; iExists h0; (iSplit; [done|]).
    + iDestruct "Hn1" as (h) "[Eq Hn1]".
      iDestruct "Hn1" as (A) "Hn1".
      iExists (h' :: A).
      rewrite {2}/ReachableD (fixpoint_unfold ReachableD' _ _).
      iExists h0. iSplit; [done|]. iExists _. iFrame "Hq1".
      iNext. iDestruct "Eq" as "%". by simplify_eq.
    + iDestruct "Hn2" as (h) "[Eq Hn2]".
      iDestruct "Hn2" as (A) "Hn2".
      iExists (h' :: A).
      rewrite {2}/ReachableD (fixpoint_unfold ReachableD' _ _).
      iExists h0. iSplit; [done|]. iExists _. iFrame "Hq2".
      iNext. iDestruct "Eq" as "%". by simplify_eq.
Qed.

Lemma Head_main_dup l γ t s v:
  Head true l γ t s v -∗ Head true l γ t s v ∗ Head false l γ t s v.
Proof.
  iDestruct 1 as (h ? A) "Head". subst v.
  rewrite /Reachable (fixpoint_unfold (Reachable' P) _ _).
  revert h. induction A as [|v' A' IH] => h.
  - iDestruct "Head" as "%". subst h.
    iSplitL; iExists 0; (iSplit; [done|]); iExists [].
    + by rewrite /Reachable (fixpoint_unfold (Reachable' P) _ _).
    + by rewrite /ReachableD (fixpoint_unfold ReachableD' _ _).
  - iDestruct "Head" as (h0 ?) "(H† & Hh & HP & Head)". subst h.
    iDestruct "Head" as (q h1) "[next Head]".
    iAssert (▷ (Head true l γ t s #h1 ∗ Head false l γ t s #h1))%I
      with "[Head]" as "(Hn1 & Hn2)".
    { iNext. rewrite (fixpoint_unfold (Reachable' P) _ _ ).
      by apply IH. } clear IH.
    iDestruct "next" as "[Hq1 Hq2]".
    iSplitR "Hq2 Hn2"; iExists h0; (iSplit; [done|]).
    + iDestruct "Hn1" as (h) "[Eq Hn1]".
      iDestruct "Hn1" as (A) "Hn1".
      iExists (v' :: A).
      rewrite {2}/Reachable (fixpoint_unfold (Reachable' P) _ _).
      iExists h0. iSplitL ""; [done|]. iFrame "H† Hh HP".
      iExists _, h1. iFrame "Hq1".
      iNext. iDestruct "Eq" as "%". by simplify_eq.
    + iDestruct "Hn2" as (h) "[Eq Hn2]".
      iDestruct "Hn2" as (A) "Hn2".
      iExists (h1 :: A).
      rewrite {2}/ReachableD (fixpoint_unfold ReachableD' _ _).
      iExists h0. iSplit; [done|]. iExists _. iFrame "Hq2".
      iNext. iDestruct "Eq" as "%". by simplify_eq.
Qed.

Lemma Head_main_is_loc l γ t s v :
  Head true l γ t s v
  -∗ ⌜∃ vl: lit, v = #vl ∧ (vl = 0 ∨ ∃ l' : loc, vl = LitLoc l')⌝.
Proof.
  iDestruct 1 as (vl ? A) "Head". subst v.
  iExists vl. iSplit; [done|].
  rewrite /Reachable (fixpoint_unfold (Reachable' P) _ _).
  destruct A; simpl.
  - by iLeft.
  - iRight. iDestruct "Head" as (l' ?) "_". subst vl. by iExists l'.
Qed.

Lemma Head_dup_is_loc l γ t s v :
  Head false l γ t s v
  -∗ ⌜∃ vl: lit, v = #vl ∧ (vl = 0 ∨ ∃ l' : loc, vl = LitLoc l')⌝.
Proof.
  iDestruct 1 as (vl ? A) "Head". subst v.
  iExists vl. iSplit; [done|].
  rewrite /ReachableD (fixpoint_unfold ReachableD' _ _).
  destruct A; simpl.
  - by iLeft.
  - iRight. iDestruct "Head" as (l' ?) "_". subst vl. by iExists l'.
Qed.

Lemma Head_is_loc l γ t s v :
  (Head true l γ t s v ∨ Head false l γ t s v)
  -∗ ⌜∃ vl: lit, v = #vl ∧ (vl = 0 ∨ ∃ l' : loc, vl = LitLoc l')⌝.
Proof.
  iIntros "[?|?]"; [by iApply Head_main_is_loc|by iApply Head_dup_is_loc].
Qed.

Lemma Head_is_comparable_0 l γ t s v :
  (Head true l γ t s v ∨ Head false l γ t s v)
  -∗ ⌜∃ vl : lit, v = #vl ∧ lit_comparable 0 vl⌝.
Proof.
  iIntros "H".
  iDestruct (Head_is_loc with "H") as (vl) "[% %IL]". subst v. iPureIntro.
  exists vl. split; [done|].
  destruct IL as [?|[l' ?]]; subst vl; constructor.
Qed.

Lemma Head_is_comparable_loc l (l1: loc) γ t s v :
  (Head true l γ t s v ∨ Head false l γ t s v)
  -∗ ⌜∃ vl : lit, v = #vl ∧ lit_comparable l1 vl⌝.
Proof.
  iIntros "H".
  iDestruct (Head_is_loc with "H") as (vl) "[% %IL]". subst v. iPureIntro.
  exists vl. split; [done|].
  destruct IL as [?|[l' ?]]; subst vl; constructor.
Qed.

Lemma Head_has_fraction_loc (l l': loc) b γ t s :
  Head b l γ t s #l' -∗ ∃ q', l' ↦{q'} -.
Proof.
  iIntros "Head".
  iDestruct "Head" as (l1) "[% Head]". simplify_eq.
  destruct b.
  - iDestruct "Head" as (A) "Head".
    rewrite /Reachable (fixpoint_unfold (Reachable' P) _ _).
    destruct A as [|v1 A1].
    + iDestruct "Head" as "%". by simplify_eq.
    + iDestruct "Head" as (l2) "(% & ? & ? & ? & HH)". simplify_eq.
      iDestruct "HH" as (q' n') "[Hl2 ?]".
      rewrite shift_0. iExists q', #n'. by iFrame "Hl2".
  - iDestruct "Head" as (A) "Head".
    rewrite /ReachableD (fixpoint_unfold ReachableD' _ _).
    destruct A as [|v1 A1].
    + iDestruct "Head" as "%". by simplify_eq.
    + iDestruct "Head" as (l2) "(% & HH)". simplify_eq.
      iDestruct "HH" as (q') "[Hl2 ?]".
      rewrite shift_0. iExists q', #v1. by iFrame "Hl2".
Qed.

Lemma Head_has_fraction_loc_later (l l': loc) b γ t s :
  ▷ Head b l γ t s #l' -∗ ∃ q', ▷ l' ↦{q'} -.
Proof.
  rewrite -bi.later_exist. iApply bi.later_wand. iIntros "!>".
  by iApply Head_has_fraction_loc.
Qed.

End prot.

Section proof.
Context `{!noprolG Σ, !gpsG Σ unitProtocol, !atomicG Σ} (P: Z → vProp Σ).
Local Notation vProp := (vProp Σ).

Lemma new_tstack_spec tid :
  {{{ True }}}
      new_tstack [] @ tid; ⊤
  {{{ (s: loc), RET #s; TStack P s }}}.
Proof.
  iIntros (Φ) "_ Post".
  wp_lam.
  (* allocate head *)
  wp_apply wp_new; [done..|].
  iIntros (s) "([H†|%] & Hs & Hms)"; [|done].
  wp_let.
  (* initialize head as 0, and create protocol *)
  rewrite own_loc_na_vec_singleton.
  wp_apply (GPS_iPP_Init_write (tstackN s) (Head P) false s #0 () with "[Hs H†]");
    [done|..].
  { iPoseProof (own_loc_na_own_loc with "Hs") as "$".
    (* TODO: leaking freeable resource *)
    iIntros (t γ) "!>". iExists 0. iSplit; [done|]. iExists [].
    by rewrite /Reachable (fixpoint_unfold (Reachable' P) _ _). }
  iIntros (γ t) "PP".
  wp_seq. iApply ("Post"). by iExists γ, t, #null.
Qed.

Lemma try_push_spec s v tid :
  {{{ TStack P s ∗ P v }}}
      try_push [ #s; #v] @ tid; ⊤
  {{{ (b: bool), RET #b; if b then True else P v }}}.
Proof.
  iIntros (Φ) "[Stack P] Post".
  wp_lam.
  (* allocate new node *)
  wp_apply wp_new; [done..|].
  iIntros (n) "([H†|%] & Hn & Hmn)"; [|done].
  (* write data to new node *)
  rewrite own_loc_na_vec_cons own_loc_na_vec_singleton.
  iDestruct "Hn" as "[Hn Hd]".
  wp_pures. wp_write. wp_lam.

  iDestruct "Stack" as (γ ts vs) "#Stack".
  (* read possible head of stack *)
  wp_apply (GPS_iPP_Read (tstackN s) (Head P) (Head P false s γ) _
              with "[$Stack]"); [solve_ndisj|done|done|by left|..].
  { iIntros "!>" (t' s' v' Lt') "!>". iSplitL.
    - iIntros "D !>". iApply Head_dup_dup. by iFrame "D".
    - iIntros "F !>". iApply Head_main_dup. by iFrame "F". }

  iIntros (t' [] v') "(_ & PPs' & HD)".
  iDestruct "HD" as (s' ? A) "HD". subst v'.

  (* set the next field to the read head s' *)
  wp_pures. rewrite shift_0. wp_write.

  (* Case distinction: if s' is 0 (NULL), then this is a CAS without pointer
    comparison. Otherwise, we know from HD that s' is alive. We then only need
    to make sure that any CASable pointer values are also alive. *)
  rewrite /ReachableD (fixpoint_unfold ReachableD' _ _).
  set P' : vProp := (P v ∗ (n >> 1) ↦{1} #v ∗ n ↦{1} #s' ∗ ⎡ † n … 2 ⎤)%I.
  destruct A as [|h' A'].
  { (* s' is 0 (NULL) *)
    iDestruct "HD" as "%". subst s'.
    wp_apply (GPS_iPP_CAS_int_simple (tstackN s) (Head P) _ _ _ s _ 0 #n _ _ P'
                (λ _ _, True)%I
                (λ t0 s0, Head P false s γ t0 s0 #0)%I
                (λ t0 s0, Head P true s γ t0 s0 #0)%I (λ _ _ _, True)%I
                with "[$PPs' Hn Hd P H†]");
      [solve_ndisj|done|done|by left|by left|by right|..].
    { iSplitL ""; last iSplitL "".
      - iIntros "!> !>" (t0 [] v0 _). by iApply Head_is_comparable_0.
      - iIntros (t0 [] _). iSplitL ""; first iSplitL "".
        + rewrite -bi.later_sep. iIntros "!> Head !> !>".
          by iDestruct (Head_main_dup with "Head") as "[$ $]".
        + iIntros "(HP & Hn & Hd & H†) HH".
          iExists (). iSplitL""; [done|].
          iIntros "!>" (t _) "Hlc !>". iSplitL "".
          { iIntros "!> H !>". by iFrame. }
          iIntros "!> !> !>". iSplitL ""; [done|].
          iExists n. iSplit; [done|]. iExists [v].
          rewrite /Reachable (fixpoint_unfold (Reachable' P) _ _).
          iExists n. iSplit; [done|]. iFrame "H† Hn HP".
          iExists _, null. rewrite shift_0. iFrame "Hd".
          iModIntro.
          by rewrite (fixpoint_unfold (Reachable' P) _ _).
        + iIntros "!>" (v0 _) "!>". iSplit; by iIntros "$".
      - by iFrame "P Hd Hn H†". }
    iIntros (b t1 [] v1)
      "[_ [((%&%&%) & _ & _)|([% %] & _ & _ & HP & Hd & Hn & H†)]]".
    + (* succeeded *)
      subst. wp_case. by iApply "Post".
    + (* failed *)
      subst b. wp_case.
      (* free the node *)
      wp_apply (wp_delete _ tid 2 _ [ #0; #v] with "[Hn Hd H†]"); [done|done|..].
      { rewrite own_loc_na_vec_cons own_loc_na_vec_singleton. by iFrame. }
      iIntros "_". wp_seq. by iApply "Post". }

  (* From HD we know s' is alive. *)
  iDestruct "HD" as (s1 ? q) "[Hs1 HD]". subst s'.
  (* we are leaking fractions of s1 ("Hs1") and others ("HD") here.
    A non-leaking algorithm should have some way to retrieve/avoid this fraction.
    Then the setup in this proof will not work any more. *)
  rewrite shift_0.
  wp_apply (GPS_iPP_CAS_live_loc_simple (tstackN s) (Head P) _ _ _ s _ s1 #n _
              () P'
              (λ _ _, True)%I
              (λ t0 s0, Head P false s γ t0 s0 #s1)%I
              (λ t0 s0, Head P true s γ t0 s0 #s1)%I (λ _ _ _, True)%I
              with "[$PPs' Hn Hd P H†]");
      [solve_ndisj|done|done|by left|by left|by right|..].
  { iSplitL ""; last iSplitL ""; [..|iFrame].
    - iIntros "!> !>" (t0 [] v0 _). by iApply Head_is_comparable_loc.
    - iIntros (t0 [] _). iSplitL ""; first iSplitL ""; [|iSplitL ""|..].
      + iIntros "!>" (l' NEq) "Head". iIntros "!>".
        iDestruct (Head_has_fraction_loc_later with "Head") as (q' v') "Hs".
        iExists _. iIntros "!>". iExists _. iFrame.
      + rewrite -bi.later_sep. iIntros "!> Head !> !>".
        by iDestruct (Head_main_dup with "Head") as "[$ $]".
      + iIntros "(HP & Hn & Hd & H†) HH".
        iExists (). iSplitL""; [done|].
        iIntros "!>" (t _) "Hlc !>". iSplitL "". { by iIntros "!> $". }
        iIntros "!> !> !>". iSplitL ""; [done|].
        iExists n. iSplit; [done|].
        iDestruct "HH" as (l' ? A) "HH". simplify_eq.
        iExists (v :: A).
        rewrite {2}/Reachable (fixpoint_unfold (Reachable' P) _ _).
        iExists n. iSplit; [done|]. rewrite shift_0. iFrame "H† Hn HP".
        iExists _, s1. by iFrame "Hd HH".
      + iIntros "!>" (v0 _) "!>". iSplit; by iIntros "$". }

  iIntros (b t1 [] v1)
    "(? & [((%&%&%) & _ & _)|([% %] & _ & _ & HP & Hd & Hn & H†)])".
  + (* succeeded *)
    subst. wp_case. by iApply "Post".
  + (* failed *)
    subst b. wp_case.
    (* free the node *)
    wp_apply (wp_delete _ tid 2 _ [ #s1; #v] with "[Hn Hd H†]"); [done|done|..].
    { rewrite own_loc_na_vec_cons own_loc_na_vec_singleton. by iFrame. }
    iIntros "_". wp_seq. by iApply "Post".
Qed.

Lemma push_spec s v tid :
  {{{ TStack P s ∗ P v }}}
      push_slow [ #s; #v] @ tid; ⊤
  {{{ RET #☠; True }}}.
Proof.
  iIntros (Φ) "[#S P] Post".
  iLöb as "IH". wp_rec. wp_bind (try_push _)%E.
  iApply (try_push_spec with "[$S $P]").
  iIntros "!>" (b) "P". destruct b; wp_if.
  - by iApply "Post".
  - by iApply ("IH" with "P Post").
Qed.

Lemma try_pop_spec s tid :
  {{{ TStack P s }}}
    try_pop [ #s] @ tid; ⊤
  {{{ v, RET #v; ⌜v = EMPTY⌝ ∨ ⌜v = FAIL_RACE⌝ ∨ P v }}}.
Proof.
  iIntros (Φ) "Stack Post".
  wp_lam.

  iDestruct "Stack" as (γ ts vs) "#Stack".
  (* read possible head of stack *)
  wp_apply (GPS_iPP_Read (tstackN s) (Head P) (Head P false s γ) AcqRel
              with "[$Stack]"); [solve_ndisj|done|done|by right|..].
  { iIntros "!>" (t' s' v' Lt') "!>". iSplitL.
    - iIntros "D !>". iApply Head_dup_dup. by iFrame "D".
    - iIntros "F !>". iApply Head_main_dup. by iFrame "F". }

  iIntros (t' [] v') "(_ & PPs' & HD)".
  iDestruct "HD" as (s' ? A) "HD". subst v'.

  wp_let.

  (* Case distinction: if s' is not 0 (NULL), we know from HD that s' is alive.
    We then only need to make sure that any CASable pointer values are also
    alive. *)
  rewrite /ReachableD (fixpoint_unfold ReachableD' _ _).
  destruct A as [|h' A'].
  { (* s' is 0 (NULL), nothing to pop *)
    iDestruct "HD" as "%". subst s'. wp_pures. iApply "Post". by iLeft. }

  (* From HD we know s' is alive *)
  iDestruct "HD" as (s1 -> q) "[Hs1 HD]".
  (* we are leaking fractions of s1 ("Hs1") and others ("HD") here.
    A non-leaking algorithm should have some way to retrieve this fraction.
    Then the setup in this proof will not work any more. *)

  wp_pures.
  (* read the next field of s1 *)
  wp_read. wp_let.

  (* CAS-ing *)
  rewrite shift_0.
  iDestruct "Hs1" as "[Hs1 Hs2]".
  iDestruct (monPred_in_intro with "Hs2") as (Vs2) "[#In2 Hs2]".
  rewrite -monPred_objectively_embed.
  iMod (rel_objectively_intro _ tid with "Hs2") as "Hs2".
  iMod (rel_True_intro tid) as "#rTrue".
  set P' : vProp := ⎡ (s1 ↦{q/2} #h') Vs2 ⎤%I.

  wp_apply (GPS_iPP_CAS_live_loc_simple (tstackN s) (Head P) _ _ _ s _ s1 #h' _
              () P'
              (λ _ _, P' ∗ ∃ v : Z, (s1 >> 1) ↦ #v ∗ P v)%I
              (λ t0 s0, Head P false s γ t0 s0 #s1)%I
              (λ t0 s0, Head P true s γ t0 s0 #s1)%I (λ _ _ _, True)%I
              with "[$PPs' Hs2]");
      [solve_ndisj|done|done|by left|by right|by left|..].
  { iSplitL ""; last iSplitL ""; [..|by iFrame "Hs2"].
    - iIntros "!> !>" (t0 [] v0 _). by iApply Head_is_comparable_loc.
    - rewrite /= -(bi.True_sep' (∀ _, _)%I).
      iApply (rel_sep_objectively with "[$rTrue]").
      iIntros "!>" (t0 [] _). iSplit; first iSplitL ""; [|iSplitL ""|..].
      + iIntros "!>" (l' NEq) "Head".
        iApply (Head_has_fraction_loc_later with "Head").
      + rewrite -bi.later_sep. iIntros "!> Head !> !>".
        by iDestruct (Head_main_dup with "Head") as "[$ $]".
      + iIntros "Hs2 HH". iExists (). iSplitL ""; [done|].
        iIntros "!>" (t _) "Hlc !>". iSplitL "".
        { iIntros "!> H !>". by iFrame. }
        iIntros "!> !> !>". iDestruct "HH" as (l' ? A) "HH". simplify_eq.
        rewrite /Reachable (fixpoint_unfold (Reachable' P) _ _).
        destruct A as [|v1 A1].
        { by iDestruct "HH" as "%". }
        iDestruct "HH" as (l' ?) "(H† & Hs1 & HP & HH)". simplify_eq.
        (* TODO: leaking freeable ⎡ † l' … 2 ⎤ *)
        iDestruct "HH" as (q2 n') "[Hs2' HH]".
        iAssert (⌜#n' = #h'⌝%I) as "%".
        { iApply (own_loc_na_agree_subjectively with "Hs2'").
          rewrite shift_0 /P'. by iFrame "Hs2"; eauto. }
        simplify_eq.
        iSplitL "Hs1 HP Hs2". { by eauto with iFrame. }
        iExists h'. by eauto.
      + iIntros "!>" (v0 _) "!>". iSplit; by iIntros "$". }

  iIntros (b t1 [] v1)
    "(_ & [((%&%&%) & PP' & Hs2 & Hv)|((%&%&%) & PP' & _ & Hs2)])".
  - (* succeed *)
    subst. wp_case. iDestruct "Hv" as (v) "[Hv Pv]".
    (* read popped value *)
    wp_op. wp_read. iApply "Post".
    (* TODO: leaking data of s1 *)
    by iRight; iRight.
  - subst b. wp_case. iApply "Post". iRight; by iLeft.
Qed.

Lemma pop_spec s tid :
  {{{ TStack P s }}}
    pop [ #s] @ tid; ⊤
  {{{ v, RET #v; if decide (v = 0) then True else P v }}}.
Proof.
  iIntros (Φ) "#S Post".
  iLöb as "IH". wp_rec. wp_bind (try_pop _)%E.
  iApply (try_pop_spec with "S").
  iIntros "!>" (v) "P". wp_pures.
  case_bool_decide.
  - subst v. by iApply ("IH" with "Post").
  - wp_finish. iApply "Post". case decide => ?; [done|].
    by iDestruct "P" as "[%|[%|P]]".
Qed.
End proof.

#[global] Typeclasses Opaque TStack.

Definition TreiberStack_per_elem_instance
  `{!noprolG Σ, !gpsG Σ unitProtocol, !atomicG Σ} :
  stack_per_elem_spec Σ := {|
    spec_per_elem.new_stack_spec := new_tstack_spec ;
    spec_per_elem.push_spec      := push_spec ;
    spec_per_elem.pop_spec       := pop_spec ;
    spec_per_elem.try_push_spec  := try_push_spec ;
    spec_per_elem.try_pop_spec   := try_pop_spec ;
  |}.
