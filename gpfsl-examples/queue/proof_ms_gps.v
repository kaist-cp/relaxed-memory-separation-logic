From stdpp Require Import namespaces.
From iris.proofmode Require Import proofmode.

From gpfsl.logic Require Import proofmode.
From gpfsl.gps Require Import surface_iPP protocols escrows.
From gpfsl.logic Require Import repeat_loop new_delete.

From gpfsl.examples Require Import uniq_token.
From gpfsl.examples.queue Require Import spec_per_elem code_ms.

Require Import iris.prelude.options.

Local Notation link := 0%nat (only parsing).
Local Notation data := 1%nat (only parsing).
Local Notation head := 0%nat (only parsing).
Local Notation tail := 1%nat (only parsing).

(** Simplified formalization of Michael-Scott queue
      thanks to single-writer protocols **)

Definition LinkState: Type := () + loc.
Definition LSRel : relation LinkState :=
  λ a b, match a with
         | inl () => True
         | inr l =>
            match b with
            | inl () => False
            | inr l' => bool_decide (l = l')
            end
         end.

Global Instance LSRel_pre: PreOrder LSRel.
Proof.
  constructor.
  - intros [[]|]; [done|simpl; by rewrite bool_decide_true].
  - intros [[]|] [[]|] [[]|]; simpl; auto; [done|].
    rewrite !bool_decide_spec. intros. by subst.
Qed.
Definition LinkProtocol : protocolT :=  Build_protocolT LinkState _ _ _ LSRel _.

Local Notation Null := (inl () : pr_stateT LinkProtocol).
Local Notation Linked l := (inr l : pr_stateT LinkProtocol).

(** The CMRA & functor we need. *)
Class msqueueG Σ := MSQueueG {
  msq_linkG : gpsG Σ LinkProtocol;
  msq_hdtlG : gpsG Σ unitProtocol;
  msq_tokG : uniqTokG Σ;
}.
Local Existing Instances msq_linkG msq_hdtlG msq_tokG.

Definition msqueueΣ : gFunctors
  := #[gpsΣ LinkProtocol; gpsΣ unitProtocol; uniqTokΣ].

Global Instance subG_msqueueΣ {Σ} : subG msqueueΣ Σ → msqueueG Σ.
Proof. solve_inG. Qed.

(* Namespace for the invariants *)
Definition msqueQN (q: loc) := nroot .@ "msqueueHN" .@ q.
Definition msqueLN (l: loc) (γ: gname) := nroot .@ "msqueueLN" .@ l .@ γ.

Section Interp.
Context `{!noprolG Σ, !msqueueG Σ, !atomicG Σ} (P: Z → vProp Σ).
Local Notation vProp := (vProp Σ).

Definition DEQ (l : loc) (v : Z) (γ γ' : gname) : vProp :=
  ([es UTok γ ⇝ l ↦ #v ∗ P v ∗ UTok γ'])%I.

Definition Link' : (gname -d> _) -> gname -d> interpO Σ LinkProtocol :=
  (fun F γt _ _ _ _ s v =>
    match s with
    | inl _ => ⌜v = #null⌝
    | inr l' => ⌜v = #l'⌝
                ∗ ∃ γt' (v': Z), DEQ (l' >> data) v' γt γt'
                ∗ ∃ γ' t', GPS_iPP (msqueLN l' γt') (F γt') l' t' Null #null γ'
    end)%I.

Global Instance Link'_contractive: Contractive Link'.
Proof.
  intros ? ? ? H ? ? ? ? ? s ?.
  destruct s; [done|]. apply bi.sep_ne; [done|].
  do 2 apply bi.exist_ne => ?.
  apply bi.sep_ne; [done|].
  do 2 (apply bi.exist_ne => ?).
  apply GPS_iPP_contractive.
  dist_later_fin_intro. eapply H; si_solver.
Qed.

Definition Link : ∀ γ, interpO Σ LinkProtocol := fixpoint Link'.

Local Instance Link'_persistent γt F b l γ t s v :
  Persistent (Link' F γt b l γ t s v).
Proof. rewrite /Persistent. iIntros "L". destruct s; by iDestruct "L" as "#$". Qed.

Global Instance Link_persistent γt b l γ t s v :
  Persistent (Link γt b l γ t s v).
Proof.
  rewrite /Persistent /Link (fixpoint_unfold Link' _ _ _ _ _ _ _).
  apply (_ : Persistent _).
Qed.

Definition Head : interpO Σ unitProtocol :=
  (λ b _ _ _ _ v,
    ∃ x, ⌜v = #(LitLoc x)⌝ ∗
    ∃ γt, (∃ γ' t', GPS_iPP (msqueLN x γt) (Link γt) (x >> link) t' Null #null γ') ∗
    if b then UTok γt else True)%I.

Definition Tail : interpO Σ unitProtocol :=
  (λ _ _ _ _ _ v,
    ∃ x, ⌜v = #(LitLoc x)⌝ ∗
    ∃ γt, (∃ γ' t', GPS_iPP (msqueLN x γt) (Link γt) (x >> link) t' Null #null γ'))%I.

Definition Queue (q : loc) : vProp :=
  ((∃ th vh γh, GPS_iPP (msqueQN q) Head (q >> head) th () vh γh) ∗
   (∃ tl vl γl, GPS_iPP (msqueQN q) Tail (q >> tail) tl () vl γl))%I.

Global Instance Queue_persistent q : Persistent (Queue q) := _.

Lemma Head_dup_dup l γ t s v :
  Head false l γ t s v -∗ Head false l γ t s v ∗ Head false l γ t s v.
Proof. iIntros "#$". Qed.
(* automatable? forkable resources *)
Lemma Head_main_dup l γ t s v:
  Head true l γ t s v -∗ Head true l γ t s v ∗ Head false l γ t s v.
Proof.
  iDestruct 1 as (n) "[#Eq oH]".
  iDestruct "oH" as (γt) "[#oH Tok]".
  by iSplitL "Tok"; iExists n; iFrame "Eq"; iExists γt; iFrame "oH".
Qed.

Lemma Tail_dup l γ t s v b1 b2 b3:
  Tail b1 l γ t s v -∗ Tail b2 l γ t s v ∗ Tail b3 l γ t s v.
Proof. by iIntros "#$". Qed.

Lemma Link_dup γt l γ t s v b1 b2 b3 :
  Link γt b1 l γ t s v -∗ Link γt b2 l γ t s v ∗ Link γt b3 l γ t s v.
Proof. rewrite !/Link !(fixpoint_unfold Link' _ _ _ _ _ _ _). by iIntros "#$". Qed.

Lemma Link_comparable_0 γt b l γ t s v:
  Link γt b l γ t s v -∗ ⌜∃ vl : lit, v = #vl ∧ lit_comparable 0 vl⌝.
Proof.
  rewrite /Link (fixpoint_unfold Link' _ _ _ _ _ _ _).
  destruct s as [|n']; [iDestruct 1 as "%"|iDestruct 1 as "[% _]"];
    subst v; iPureIntro; eexists; (split; [done|constructor]).
Qed.

Lemma Head_is_loc b l γ t s v :
  Head b l γ t s v
  -∗ ⌜∃ vl: lit, v = #vl ∧ (vl = 0 ∨ ∃ l' : loc, vl = LitLoc l')⌝.
Proof.
  iDestruct 1 as (vl ? A) "Head". subst v.
  iExists vl. iSplit; [done|]. iPureIntro. right. by eexists.
Qed.

Lemma Head_is_comparable_loc l (l1: loc) γ t s v :
  (Head true l γ t s v ∨ Head false l γ t s v)
  -∗ ⌜∃ vl : lit, v = #vl ∧ lit_comparable l1 vl⌝.
Proof.
  iIntros "H".
  iAssert (⌜∃ vl: lit, v = #vl ∧ (vl = 0 ∨ ∃ l' : loc, vl = LitLoc l')⌝)%I
    with "[H]" as (vl) "[% %IL]".
  { iDestruct "H" as "[H|H]"; by iApply (Head_is_loc with "H"). }
  subst v. iPureIntro. exists vl. split; [done|].
  destruct IL as [?|[l' ?]]; subst vl; constructor.
Qed.

End Interp.

Section proof.
Context `{!noprolG Σ, !msqueueG Σ, !atomicG Σ} (P: Z → vProp Σ).
Local Notation vProp := (vProp Σ).

Lemma new_msqueue_spec tid :
  {{{ True }}}
      new_queue [] @ tid; ⊤
  {{{ (q: loc), RET #q; Queue P q }}}.
Proof.
  iIntros (Φ) "_ Post".
  wp_lam.
  (* allocate first node *)
  wp_apply wp_new; [done..|].
  iIntros (s) "([H†|%] & Hs & Hm)"; [|done].
  wp_pures. rewrite shift_0. rewrite own_loc_na_vec_singleton.
  (* initialize node, and create protocol *)
  iMod UTok_alloc as (γt) "Tok".
  wp_apply (GPS_iPP_Init_write (msqueLN s γt) (Link P γt) false s #null Null
              with "[Hs H†]"); [done|..].
  { iPoseProof (own_loc_na_own_loc with "Hs") as "$".
    (* TODO: leaking freeable resource *)
    iIntros (t γ) "!>".
    by rewrite /Link (fixpoint_unfold (Link' P) _ _ _ _ _ _ _). }

  iIntros (γi ti) "#PPi". wp_seq.
  (* allocate head & tail *)
  wp_apply wp_new; [done..|].
  iIntros (q) "([H†|%] & Hq & Hmq)"; [|done].
  rewrite own_loc_na_vec_cons own_loc_na_vec_singleton.
  iDestruct "Hq" as "[oH oT]".
  (* initialize head *)
  wp_pures. rewrite shift_0.
  wp_apply (GPS_iPP_Init_write (msqueQN q) (Head P) false q #s ()
              with "[oH Tok]"); [done|..].
  { iDestruct (own_loc_na_own_loc with "oH") as "$".
    iIntros (t γ). iExists s. iSplit; [done|]. iExists γt.
    iFrame "Tok". iExists γi, ti. rewrite shift_0. by iFrame "PPi". }

  iIntros (γh th) "PPh". wp_pures.
  (* initialize tail *)
  wp_apply (GPS_iPP_Init_write (msqueQN q) (Tail P) false (q >> tail) #s ()
              with "[oT]"); [done|..].
  { iPoseProof (own_loc_na_own_loc with "oT") as "$".
    iIntros (t γ). iExists s. iSplit; [done|]. iExists γt.
    iExists γi, ti. rewrite shift_0. by iFrame "PPi". }

  (* automatable? *)
  iIntros (γl tl) "PPl". wp_let.
  iApply "Post". iSplitL "PPh".
  - iExists th, #s, γh. rewrite shift_0. iFrame "PPh".
  - iExists tl, #s, γl. iFrame "PPl".
Qed.

Lemma find_tail_spec q tid :
  {{{ Queue P q }}}
      find_tail [ #q] @ tid; ⊤
  {{{ (n: lit), RET #n; ⌜n = 0⌝ ∨
      (∃ l: loc, ⌜n = l⌝ ∧ ∃ γt γ' t',
        GPS_iPP (msqueLN l γt) (Link P γt) (l >> link) t' Null #null γ')  }}}.
Proof.
  iIntros (Φ) "#[oH oT] Post".
  iDestruct "oH" as (th vh γh) "PPh". iDestruct "oT" as (tl vl γl) "PPl".
  wp_pures.

  (* read tail *)
  wp_apply (GPS_iPP_Read _ _ (Tail P false (q >> tail) γl)
              with "[$PPl]"); [solve_ndisj|done|done|by right| |].
  { iIntros (????) "!> !>". iSplit; by iIntros "#$". }

  iIntros (tl' [] vl') "(_ & PPl' & oT)".
  iDestruct "oT" as (n) "[% oT]". subst vl'.
  iDestruct "oT" as (γt γ' t') "oT".
  wp_pures.
  (* read node *)
  wp_apply (GPS_iPP_Read _ _ (Link P γt false (n >> link) γ') with "[$oT]");
    [solve_ndisj|done|done|by right| |].
  { iIntros (????) "!> !>". iSplit; [by iIntros "#$"|].
    iIntros "L !>". by iApply (Link_dup with "L"). }

  iIntros (tn' sn' vn') "(Le & PPn & oL)".
  rewrite {3}/Link (fixpoint_unfold (Link' P) _ _ _ _ _ _ _).
  destruct sn' as [[]|sn'].
  - (* found a probable tail *)
    iDestruct "oL" as "->". wp_pures. iApply "Post". iRight.
    iExists n. iSplit; [done|]. iExists γt, γ', tn'. iFrame "PPn".
  - (* haven't hit the last node, keep going *)
    iDestruct "oL" as "[-> oL]". iDestruct "oL" as (γt' v') "(ES & oL)".
    iDestruct "oL" as (γ1 t1) "oL".
    wp_pures.
    wp_apply (GPS_iPP_Write _ _ _ _ _ _ (() : unitProtocol) _ #sn'
                with "[$PPl oL]"); [solve_ndisj|done|done|by right|done|..].
    { iIntros "!>" (tl2 ?) "LL !>".
      iExists sn'. iSplit; [done|]. iExists γt', γ1, t1.
      rewrite (shift_0 sn'). by iFrame "oL". }
    iIntros (t2) "PPl2". wp_let.
    iApply "Post". by iLeft.
Qed.

Lemma find_tail_repeat_spec q tid :
  {{{ Queue P q }}}
      (repeat: (find_tail [ #q])) @ tid; ⊤
  {{{ (l: loc), RET #l; ∃ γt γ' t',
        GPS_iPP (msqueLN l γt) (Link P γt) (l >> link) t' Null #null γ' }}}.
Proof.
  iIntros (Φ) "#Queue Post".
  iLöb as "IH". iApply wp_repeat; [done|].
  iApply (find_tail_spec with "Queue").
  iIntros "!>" (n') "[%|oN']".
  { (* not found, keep looping *)
    subst n'. iExists 0. iSplit; [done|].
    simpl. iIntros "!> !>". by iApply ("IH" with "Post"). }
  iDestruct "oN'" as (l ?) "oL'".
  subst n'. iExists l. iSplit; [done|simpl].
  iIntros "!> !>". iApply ("Post" with "oL'").
Qed.

Lemma try_enq_spec q (x : Z) tid :
  {{{ Queue P q ∗ P x }}}
      try_enq [ #q; #x] @ tid; ⊤
  {{{ (b: bool), RET #b; if b is true then True else P x }}}.
Proof.
  iIntros (Φ) "[#Queue P] Post".
  wp_lam.
  (* allocate new node *)
  wp_apply wp_new; [done..|].
  iIntros (n)  "([H†|%] & Hn & Hmn)"; [|done].
  rewrite own_loc_na_vec_cons own_loc_na_vec_singleton.
  iDestruct "Hn" as "[oL oD]".
  wp_pures.
  (* write data *)
  wp_write.
  (* initialize link *)
  wp_op. rewrite (shift_0 n). wp_write.

  (* repeat loop to find tail *)
  wp_bind (repeat: _)%E.
  iApply (find_tail_repeat_spec with "Queue").
  iIntros "!>" (l') "oL'". iDestruct "oL'" as (γt' γ' t') "oL'".
  wp_pures.

  (* CAS to replace head *)
  set P' : vProp := (n ↦{1} #null ∗ P x ∗ (n >> data) ↦ #x)%I.
  wp_apply (GPS_iPP_CAS_int_simple _ _ _ _ _ _ _ null #n _ Null
              P' (λ _ _, ∃ γt t γ, GPS_iPP (msqueLN n γt) (Link P γt) n γ Null #null t)%I
              (λ t1 s1, Link P γt' false (l' >> link) γ' t1 s1 #null)
              (λ t1 s1, Link P γt' true (l' >> link) γ' t1 s1 #null)
              (λ _ _ _, True)%I with "[$oL' P oL oD]");
    [solve_ndisj|done|done|by left|by right|by right|..].
  { iSplitL ""; last iSplitL ""; last by iFrame.
    { iIntros "!> !>" (t1 s1 v1 Le).
      by iIntros "[L|L]"; iApply (Link_comparable_0 with "L"). }
    iIntros (t1 s1 Le1). iSplit; [iSplitL ""|].
    - iIntros "!> L !>". rewrite -bi.later_sep.
      iNext. iApply (Link_dup with "L").
    - iIntros "(oN & P & oD) #oL".
      (* WARNING: LEAKING H† *)
      iAssert (|={⊤ ∖ ↑msqueLN l' γt'}=> ⌜s1 = Null⌝)%I as ">%".
      { rewrite /Link (fixpoint_unfold (Link' P) _ _ _ _ _ _ _).
        destruct s1 as [[]|]; [done|]. clear.
        iDestruct "oL" as "[>% _]". by simplify_eq. } subst s1.
      iIntros "!>". iExists (Linked n). iSplit; [done|].
      iIntros (t2 Lt2) "PP' !>". iSplitL ""; [by iIntros "!> $"|].
      iIntros "!> !>".
      (* allocating escrow for n, to be used linked by l' *)
      iMod UTok_alloc as (γt) "Tok".
      iMod (escrow_alloc (UTok γt') ((n >> data) ↦{1} #x ∗ P x ∗ UTok γt)%I
          with "[$P $oD $Tok]") as "ESSt" ; [solve_ndisj|..].

      (* allocating protocol for n *)
      iMod (GPS_iPP_Init (msqueLN n γt) (Link P γt) n Null #null with "oN []")
        as (t γ) "#PP".
      { iIntros (t γ) "!>".
        by rewrite {2}/Link (fixpoint_unfold (Link' P) _ _ _ _ _ _ _). }
      iIntros "!>". iSplitL "".
      { iExists γt, t, γ. by iFrame "PP". }
      iNext.
      rewrite {3}/Link (fixpoint_unfold (Link' P) _ _ _ _ _ _ _) /=.
      iSplit; [done|]. iExists γt, x. iFrame "ESSt".
      iExists _, _. by iFrame "PP".
    - iIntros "!>" (v NE) "!>". by iSplit; iIntros "$". }

  iIntros (b t1 s1 v1) "[%Le1 CASE]".
  iDestruct "CASE" as "[[(->&->&%) [PP' Q]]|[(->&%&%) (PP' & _ & oN & P & oD)]]".
  - wp_pures.
    (* update tail with new node *)
    iDestruct "Queue" as "[oH oT]". iDestruct "oT" as (tl vl γl) "oT".
    wp_apply (GPS_iPP_Write _ _ _ _ _ _ (() : unitProtocol) _ #n
              with "[$oT Q]"); [solve_ndisj|done|done|by right|done|..].
    { iIntros "!>" (tl2 ?) "LL !>".
      iExists n. iSplit; [done|]. rewrite (shift_0 n). by iFrame "Q". }
    iIntros (t2) "PP2". wp_let. by iApply "Post".
  - wp_if.
    (* free the node *)
    wp_apply (wp_delete _ tid 2 _ [ #null; #x] with "[oN oD H†]"); [done|done|..].
    { rewrite own_loc_na_vec_cons own_loc_na_vec_singleton. by iFrame. }
    iIntros "_". wp_lam. iApply "Post". by iFrame "P".
Qed.

Lemma enqueue_spec q (x: Z) tid :
  {{{ Queue P q ∗ P x }}}
      enqueue [ #q; #x] @ tid; ⊤
  {{{ RET #☠; True }}}.
Proof.
  iIntros (Φ) "[#Q P] Post". iLöb as "IH". wp_rec.
  wp_apply (try_enq_spec with "[$Q $P]").
  iIntros ([]) "P".
  - wp_if. by iApply "Post".
  - wp_if. by iApply ("IH" with "P Post").
Qed.

Lemma try_deq_spec q tid :
  {{{ Queue P q }}}
      try_deq [ #q] @ tid; ⊤
  {{{ (x: Z), RET #x; ⌜x = EMPTY⌝ ∨ ⌜x = FAIL_RACE⌝ ∨ P x }}}.
Proof.
  iIntros (Φ) "#[oH oT] Post".
  wp_pures.
  (* read head *)
  iDestruct "oH" as (th vh γh) "PPh".
  wp_apply (GPS_iPP_Read _ _ (Head P false (q >> head) γh)
              with "[$PPh]"); [solve_ndisj|done|done|by right| |].
  { iIntros "!>" (t' [] v' Lt') "!>". iSplit; iIntros "oH !>".
    - iApply (Head_dup_dup with "oH").
    - iApply (Head_main_dup with "oH"). }
  iIntros (t1 [] v1) "(%Lt1 & PP1 & Hd)".
  iDestruct "Hd" as (s ?) "PPs". subst v1.
  iDestruct "PPs" as (γt) "[#PPs _]". iDestruct "PPs" as (γ' t') "PPs".
  wp_pures.

  (* read node's link *)
  wp_apply (GPS_iPP_Read _ _ (Link P γt false (s >> link) γ') with "[$PPs]");
    [solve_ndisj|done|done|by right| |].
  { iIntros (????) "!> !>". iSplit; [by iIntros "#$"|].
    iIntros "L !>". by iApply (Link_dup with "L"). }

  iIntros (t2 s2 v2) "(%Lt2 & PP2 & Link)".
  wp_let.
  rewrite {3}/Link (fixpoint_unfold (Link' P) _ _ _ _ _ _ _).
  destruct s2 as [[]|s2].
  - (* easy case: nothing to pop *)
    iDestruct "Link" as %?. subst v2. wp_pures. iApply "Post". by iLeft.
  - iDestruct "Link" as "[% os2]". subst v2.
    iDestruct "os2" as (γt2 v2) "#(ES & PPs2)".
    iDestruct "PPs2" as (γs2 ts2) "PPs2".
    wp_pures.

    (* CAS on head *)
    set Q : time → unitProtocol → vProp :=
      (λ _ _, (s2 >> data) ↦{1} #v2 ∗ ▷ P v2)%I.
    wp_apply (GPS_iPP_CAS_live_loc (msqueQN q) (Head P) _ _ _ (q >> head) _
                s #s2 _ () True%I Q
                (λ t0 s0, Head P false (q >> head) γh t0 s0 #s)%I
                (λ t0 s0, Head P true  (q >> head) γh t0 s0 #s)%I
                (λ _ _ _, True)%I _ _ _
                (λ l', ⊤ ∖ ↑msqueQN q ∖ ↑(nroot.@"msqueueLN".@l'))
                with "[$PPh]");
      [solve_ndisj|done|solve_ndisj|intros; solve_ndisj
      |by left|by right|by right| |].
    { iSplitL ""; last iSplitL ""; [..|done].
      { iIntros "!> !>" (t0 [] v0 _). by iApply Head_is_comparable_loc. }
      iIntros (t0 [] Lt0). iSplitL ""; first iSplitL ""; [|iSplitL ""|..].
      - iIntros "!>" (l' NEq).
        iDestruct 1 as (l3) "[>% HP]". simplify_eq.
        iDestruct "HP" as (γt3) "[HP Tok]". iNext.
        iDestruct "HP" as (γ3 t3) "HP".
        iMod (GPS_iPP_own_loc_prim _ _ _ _ _ _ _ _
                (⊤ ∖ ↑msqueQN q ∖ ↑nroot.@"msqueueLN".@l3) with "HP") as (C) "HP";
                [solve_ndisj|solve_ndisj|].
        iModIntro. iExists 1%Qp, C. rewrite shift_0. iFrame "HP".
      - rewrite -bi.later_sep. iIntros "!> Head !> !>".
        by iDestruct (Head_main_dup with "Head") as "[$ $]".
      - iIntros "_ Hd".
        iDestruct "Hd" as (s') "[>% Hd]". simplify_eq.
        iDestruct "Hd" as (γt') "[#PP' >Tok']".
        iModIntro. iExists (). iSplit; [done|].
        iIntros (t3 Lt3) "PPl !>". iSplitL ""; [by iIntros "!> $"|].
        iIntros "!> !>".
        iAssert (|={⊤ ∖ ↑msqueQN q}=> ⌜γt' = γt⌝)%I as ">%".
        { iDestruct "PP'" as (γs' ts') "PP'".
          case (decide (γt' = γt)) => ?; [done|].
          iMod (GPS_iPP_own_loc_prim _ _ _ _ _ _ _ _
                  (⊤ ∖ ↑msqueQN q ∖ ↑msqueLN (s' >> link) γt) with "PPs")
                  as (C1) ">own1"; [solve_ndisj|by rewrite shift_0|].
          iMod (GPS_iPP_own_loc_prim _ _ _ _ _ _ _ _
                  (⊤ ∖ ↑msqueQN q ∖ ↑msqueLN (s' >> link) γt ∖ ↑msqueLN (s' >> link) γt')
                  with "PP'") as (C2) ">own2";
                  [rewrite shift_0; solve_ndisj|by rewrite shift_0|].
          iClear "#".
          iCombine "own1" "own2" as "own". rewrite -view_subjectively_sep.
          iAssert (<subj> False)%I with "[own]" as "%"; [|done].
          iApply (monPred_subjectively_mono with "own").
          iIntros "[o1 o2]".
          iPoseProof (own_loc_prim_combine with "o1 o2") as "o".
          by iDestruct (own_loc_prim_frac_1 with "o") as %?. }
        subst γt'.

        iMod (escrow_elim with "[] ES [$Tok']") as "Q" ; [solve_ndisj|..].
        { (* automatable *)
          iIntros "[t1 t2]". by iApply (UTok_unique with "t1 t2"). }
        iDestruct "Q" as "(>Hv & Pv & >Tok2)".
        iModIntro. iSplitL "Hv Pv".
        + by iFrame.
        + iNext. iExists s2. iSplit; [done|].
          iExists γt2. iFrame "Tok2". iExists _, _.
          rewrite (shift_0 s2). by iFrame "PPs2".
      - iIntros "!>" (v0 _) "!>". iSplit; by iIntros "$". }

  iIntros (b t3 [] v3) "(_ & [((%&%&%) & PP' & HP)|((%&%&%) & PP' & _)])".
  + (* successful dequeue *)
    subst b. iDestruct "HP" as "[Hv HP]".
    wp_pures. wp_read. iApply "Post". by iRight; iRight.
  + (* fail, because losing a race against a concurrent try_deq *)
    subst b. wp_if. iApply "Post". by iRight; iLeft.
Qed.

Lemma dequeue_spec q tid :
  {{{ Queue P q }}}
      dequeue [ #q ] @ tid; ⊤
  {{{ (x : Z), RET #x; if decide (x = EMPTY) then True else P x }}}.
Proof.
  iIntros (Φ) "#Q Post". iLöb as "IH". wp_rec.
  wp_apply (try_deq_spec with "Q").
  iIntros (x) "P". wp_pures.
  case_bool_decide.
  - wp_finish. iApply "Post". iDestruct "P" as "[%Eq0|[%Eqm|P]]".
    + by rewrite decide_True.
    + lia.
    + by case_decide.
  - by iApply ("IH" with "Post").
Qed.

End proof.

#[global] Typeclasses Opaque Queue.

Definition MSQueue_per_elem_instance `{!noprolG Σ, !msqueueG Σ, !atomicG Σ} :
  queue_per_elem_spec Σ := {|
    spec_per_elem.new_queue_spec := new_msqueue_spec ;
    spec_per_elem.enqueue_spec   := enqueue_spec ;
    spec_per_elem.dequeue_spec   := dequeue_spec ;
    spec_per_elem.try_enq_spec   := try_enq_spec ;
    spec_per_elem.try_deq_spec   := try_deq_spec ;
  |}.
