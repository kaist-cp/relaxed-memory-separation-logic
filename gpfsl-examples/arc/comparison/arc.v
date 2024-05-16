From iris.bi Require Import fractional.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import excl csum frac auth agree.
From iris.base_logic.lib Require Import invariants.

From gpfsl.gps Require Import middleware protocols.
From gpfsl.logic Require Import view_invariants.
From lrust.lang Require Import notation new_delete arc_cmra.

From iris.prelude Require Import options.

(* Rust Arc has a maximum number of clones to prevent overflow. We currently
  don't support this. *)

Definition strong_count : val :=
  λ: ["l"], !ᵃᶜ"l".

Definition weak_count : val :=
  λ: ["l"], !ᵃᶜ("l" +ₗ #1).

Definition clone_arc : val :=
  rec: "clone" ["l"] :=
    let: "strong" := !ʳˡˣ"l" in
    (* fully relaxed CAS *)
    if: CAS "l" "strong" ("strong" + #1) Relaxed Relaxed Relaxed then #☠ else "clone" ["l"].

Definition clone_weak : val :=
  rec: "clone" ["l"] :=
    let: "weak" := !ʳˡˣ("l" +ₗ #1) in
    if: CAS ("l" +ₗ #1) "weak" ("weak" + #1) Relaxed Relaxed Relaxed then #☠ else "clone" ["l"].

(*  // the value usize::MAX acts as a sentinel for temporarily "locking" the
    // ability to upgrade weak pointers or downgrade strong ones; this is used
    // to avoid races in `make_mut` and `get_mut`.
    Her we use -1 for usize::MAX.
*)
Definition downgrade : val :=
  rec: "downgrade" ["l"] :=
    let: "weak" := !ʳˡˣ("l" +ₗ #1) in
    if: "weak" = #(-1) then
      (* -1 in weak indicates that somebody locked the counts; let's spin. *)
      "downgrade" ["l"]
    else
      (*
        // Unlike with Clone(), we need this to be an Acquire read to
        // synchronize with the write coming from `is_unique`, so that the
        // events prior to that write happen before this read.
      *)
      (* acquire CAS, i.e. relaxed fail read, acquire success read, relaxed write *)
      if: CAS ("l" +ₗ #1) "weak" ("weak" + #1) Relaxed AcqRel Relaxed then #☠
      else "downgrade" ["l"].

Definition upgrade : val :=
  rec: "upgrade" ["l"] :=
    let: "strong" := !ʳˡˣ"l" in
    if: "strong" = #0 then #false
    else
      if: CAS "l" "strong" ("strong" + #1) Relaxed Relaxed Relaxed then #true
      else "upgrade" ["l"].

Definition drop_weak : val :=
  rec: "drop" ["l"] :=
    (* This can ignore the lock because the lock is only held when there
       are no other weak refs in existence, so this code will never be called
       with the lock held. *)
    let: "weak" := !ʳˡˣ("l" +ₗ #1) in
    (* release CAS, i.e. relaxed fail read, relaxed success read, release write *)
    if: CAS ("l" +ₗ #1) "weak" ("weak" - #1) Relaxed Relaxed AcqRel
    then if: "weak" = #1 then FenceAcq ;; #true else #false
    else "drop" ["l"].

Definition drop_arc : val :=
  rec: "drop" ["l"] :=
    let: "strong" := !ʳˡˣ"l" in
    if: CAS "l" "strong" ("strong" - #1) Relaxed Relaxed AcqRel
    then if: "strong" = #1 then FenceAcq ;; #true else #false
    else "drop" ["l"].

Definition try_unwrap : val :=
  λ: ["l"],
    (* release CAS *)
    if: CAS "l" #1 #0 Relaxed Relaxed AcqRel
    then FenceAcq ;; #true
    else #false.

(* A bug was discovered where the read of strong was relaxed.
  It can be fixed by using an acquire read.
  See https://github.com/rust-lang/rust/issues/51780 *)
Definition is_unique : val :=
  λ: ["l"],
    (* Try to acquire the lock for the last ref by CASing weak count from 1 to -1. *)
    (* acquire CAS *)
    if: CAS ("l" +ₗ #1) #1 #(-1) Relaxed AcqRel Relaxed then
      let: "strong" := !ᵃᶜ"l" in
      let: "unique" := "strong" = #1 in
      "l" +ₗ #1 <-ʳᵉˡ #1;;
      "unique"
    else
      #false.

(* to be used in make_mut *)
(*// Note that we hold both a strong reference and a weak reference.
  // Thus, releasing our strong reference only will not, by itself, cause
  // the memory to be deallocated.
  //
  // Use Acquire to ensure that we see any writes to `weak` that happen
  // before release writes (i.e., decrements) to `strong`. Since we hold a
  // weak count, there's no chance the ArcInner itself could be
  // deallocated. *)
(* - Returns #2 to signal that there is another strong pointer,
    and trigger a deep copy and make a new Arc pointing to the new copy.
   - Returns #1 to signal that we have the last strong pointer and
   the main content, but there are more than 1 weak pointers left.
   So we will move the main content to a new Arc, and leave the job
   of dropping to old Arc to its remaining weak pointers.
   - Returns #0 to signal that we have collected both the last strong and weak pointer,
   so it's time to clean up everything. We reset "strong" back to 1 to unlock.
   The write "l" <- #1 seems to be good enough, but C/Rust
   uses a release write, may be because the strict distinction between atomics
   and non-atomics. (TODO: is a relaxed write enough?) *)

(* we use acquire read instead of relaxed read on weak: we do not know how to
  prove or disprove the relaxed read yet *)
Definition try_unwrap_full : val :=
  λ: ["l"],
    (* acquire CAS *)
    if: CAS "l" #1 #0 Relaxed AcqRel Relaxed then
      if: !ᵃᶜ("l" +ₗ #1) = #1 then "l" <- #1;; #0
      else #1
    else #2.

Section ArcInv.
  (* P1 is the thing that is shared by strong reference owners (in practice,
     this is the lifetime token), and P2 is the thing that is owned by the
     protocol when only weak references are left (in practice, P2 is the
     ownership of the underlying memory incl. deallocation). *)
  Context `{!noprolG Σ, !arcG Σ, !view_invG Σ}
          (P1 : Qp → vProp Σ) (P2 : vProp Σ) (N : namespace).
  Local Notation vProp := (vProp Σ).

  Definition SeenActs γ l (Mt: gset time) : vProp :=
    (∃ t v, GPS_Reader l t () v γ ∗ ⌜∀ t', t' ∈ Mt → t' ⊑ t⌝)%I.

  Definition WkResources lw ls t v γi γw γs γsw q Ut : vProp :=
    (* writer permission and remaining reader permission *)
    (view_tok γi (q/2) ∗ GPS_SWSharedReader lw t () v q γw ∗
    (* I have seen all upgrades by strong that I'm involved in --- γs *)
    WkUps γsw q Ut ∗ SeenActs γs ls Ut)%I.

  Definition weak_interp ls γi γs γsw : interpO Σ unitProtocol :=
    (λ pb lw γw t _ v, ∃ st, ⌜v = #(Z_of_arcweak_st st)⌝ ∗
       if pb
       (* Full interp *)
       then (* the weak state st, the move authority Mt, the upgrade authority Ut *)
            WeakAuth γsw st ∗
            match st return _ with
            | (None, None) => (* nothing *) True
            | (Some qs, None) => ⌜qs = 1%Qp⌝ ∗ (* some strongs, no weak *)
                (* weak resources are returned *)
                GPS_SWSharedWriter lw t () v γw ∗
                (∃ Ut, WkResources lw ls t v γi γw γs γsw 1%Qp Ut)
            | (None, Some (Cinl (q, n))) => (* no strong, n weaks *)
                (* remaining weak resources *)
                GPS_SWSharedWriter lw t () v γw ∗
                (∃ q' Ut, ⌜(q + q')%Qp = 1%Qp⌝ ∗
                              WkResources lw ls t v γi γw γs γsw q' Ut) ∗
                P2 ∗
                (* strong resources *)
                view_tok γi (1/2)%Qp ∗
                (∃ ts, GPS_SWWriter ls ts () #0 γs) ∗
                (∃ Mts, StrMoves γsw 1%Qp Mts) ∗
                (∃ Dts, StrDowns γsw 1%Qp Dts)
            | (Some qs, Some (Cinl (q, n))) => ⌜qs = 1%Qp⌝ ∗
                (* some strongs, n weaks *)
                GPS_SWSharedWriter lw t () v γw ∗
                (∃ q' Ut, ⌜(q + q')%Qp = 1%Qp⌝ ∗
                              WkResources lw ls t v γi γw γs γsw q' Ut)
            | (Some qs, Some (Cinr (_, agq))) => ⌜qs = 1%Qp⌝ ∗
                (* some strong arcs, no weak arcs, locked,
                   agown γsw (awk_n ((Some q, ε))) is the payload *)
                ∃ q, ⌜agq ≡ to_agree q⌝ ∗ StrWkTok γsw q
            | _ => False (* anything else is impossible *)
            end
       (* Read interp *)
       else ⌜0 < Z_of_arcweak_st st⌝ ∗ (* CASable values > 0 *)
            match st with
            | (Some _, None) | (None, Some (Cinl (_, 1%positive))) =>
                (* move from 1 *)
                ∃ t' : time, ⌜(t < t')%positive⌝ ∗ StrDownCert γsw t'
            | _ => True
            end
    )%I.

  Definition weak_noCAS γsw : interpCasO Σ unitProtocol :=
    (λ _ _ t _ v, ⌜v = #(-1)⌝ ∗ ∃ t' : time, ⌜(t < t')%positive⌝ ∗ StrDownCert γsw t')%I.

  Definition StrResources lw ls t v γi γs γw γsw q Mt Dt :=
    (* writer permission and remaining reader permission *)
    (view_tok γi (q/2) ∗ GPS_SWSharedReader ls t () v q γs ∗
    (* I have seen all my moves  --- γ *)
    StrMoves γsw q Mt ∗ SeenActs γs ls Mt ∗
    (* I have seen all downgrads by weak that I'm involved in --- γs *)
    StrDowns γsw q Dt ∗ SeenActs γw lw Dt ∗
    (* weak resources I need to keep to use weak *)
    StrWkTok γsw q)%I.

  Definition strong_interp lw γi γw γsw: interpO Σ unitProtocol :=
    (λ pb ls γs t _ v, ∃ st, ⌜v = #(Z_of_arcstrong_st st)⌝ ∗
      if pb
       (* Full interp *)
       then (* the strong state st *)
            StrongAuth γsw st ∗
            match st return _ with
            | None => (* nothing *) True
            | Some (q, n) => (* n strongs *)
                GPS_SWSharedWriter ls t () v γs ∗ ∃ q', ⌜(q + q')%Qp = 1%Qp⌝ ∗
                P1 q' ∗
                (∃ Mt Dt, StrResources lw ls t v γi γs γw γsw q' Mt Dt)
            end
       (* Read interp *)
       else match st with
            | None => False
            | Some (_, 1%positive) =>
                (* move from 1 *)
                ∃ t' : time, ⌜(t < t')%positive⌝ ∗ (StrMoveCert γsw t' ∨ WkUpCert γsw t')
            | _ => True
            end
    )%I.

  Definition strong_noCAS : interpCasO Σ unitProtocol :=
    (λ _ _ _ _ v, ⌜v = #0⌝)%I.

  Definition strong_arc t q l γi γs γw γsw : vProp :=
    (∃ v Mt Dt, StrongTok γsw q ∗ StrResources (l >> 1) l t v γi γs γw γsw q Mt Dt)%I.

  Definition weak_arc t q l γi γs γw γsw : vProp :=
    (∃ v Ut, WeakTok γsw q ∗ WkResources (l >> 1) l t v γi γw γs γsw q Ut)%I.

  Definition fake_arc l γi γs γw γsw :=
    (view_tok γi (1/2)%Qp ∗ (∃ ts, GPS_SWWriter l ts () #0 γs) ∗
    (∃ Mts, StrMoves γsw 1%Qp Mts ∗ SeenActs γs l Mts) ∗
    (∃ Dts, StrDowns γsw 1%Qp Dts ∗ SeenActs γw (l >> 1) Dts) ∗
    StrWkTok γsw 1%Qp)%I.

  Global Instance strong_arc_timeless t q l γi γs γw γsw : Timeless (strong_arc t q l γi γs γw γsw) := _.
  Global Instance weak_arc_timeless t q l γi γs γw γsw : Timeless (weak_arc t q l γi γs γw γsw) := _.
  Global Instance fake_arc_timeless l γi γs γw γsw : Timeless (fake_arc l γi γs γw γsw) := _.

  Definition strong_arc_acc l t γi γs γw γsw P E : vProp :=
    (□ (P ={E,↑histN}=∗ ∃ Vb q,
          (⊒Vb → ▷ strong_arc t q l γi γs γw γsw) ∗
          ((⊒Vb → ▷ strong_arc t q l γi γs γw γsw) ={↑histN,E}=∗ P)))%I.

  Definition weak_arc_acc l t γi γs γw γsw P E : vProp :=
    (□ (P ={E,↑histN}=∗ ∃ Vb q,
      (⊒Vb → ▷ weak_arc t q l γi γs γw γsw) ∗
      ((⊒Vb → ▷ weak_arc t q l γi γs γw γsw) ={↑histN,E}=∗ P)))%I.

  Definition arc_inv γi γs γw γsw (l : loc) : vProp :=
    (((∃ Mt, StrongMoveAuth γsw Mt) ∗
        (∃ Dt, StrongDownAuth γsw Dt) ∗ (∃ Ut, WeakUpAuth γsw Ut)) ∗
      GPS_INV (strong_interp (l >> 1) γi γw γsw) l strong_noCAS γs ∗
      GPS_INV (weak_interp l γi γs γsw) (l >> 1) (weak_noCAS γsw) γw)%I.

  Definition is_arc γi γs γw γsw l : vProp :=
    view_inv γi N (arc_inv γi γs γw γsw l).

  Global Instance is_arc_persistent γi γs γw γsw l : Persistent (is_arc γi γs γw γsw l) := _.

End ArcInv.

Global Typeclasses Opaque StrongTok WeakTok StrMoves StrDowns WkUps.

Section arc.
  (* P1 is the thing that is shared by strong reference owners (in practice,
     this is the lifetime token), and P2 is the thing that is owned by the
     protocol when only weak references are left (in practice, P2 is the
     ownership of the underlying memory incl. deallocation). *)
  Context `{!noprolG Σ, !arcG Σ, !view_invG Σ}
          (P1 : Qp → vProp Σ)
          (P2 : vProp Σ) (N : namespace).
  Local Notation vProp := (vProp Σ).
  Local Notation HP1 := (∀ q1 q2, P1 (q1 + q2)%Qp -∗ P1 q1 ∗ <obj> P1 q2).
  Local Notation HP2 := (∀ q1 q2, P1 q1 ∗ P1 q2 -∗ P1 (q1 + q2)%Qp).

  Global Instance arc_inv_ne n :
    Proper (pointwise_relation _ (dist n) ==> dist n ==>
                eq ==> eq ==> eq ==> eq ==> eq ==> dist n) arc_inv.
  Proof.
    repeat intro. subst.
    apply bi.sep_ne; [done|]. apply bi.sep_ne; apply GPS_INV_ne; [|done| |done].
    - move => b ?????. apply bi.exist_ne => st.
      apply bi.sep_ne; [done|]. destruct b; [|done]. apply bi.sep_ne; [done|].
      destruct st as [[]|]; [|done]. solve_proper.
    - move => b ?????. apply bi.exist_ne => st.
      apply bi.sep_ne; [done|]. destruct b; [|done]. apply bi.sep_ne; [done|].
      destruct st as [[|] [[[]| |]|]]; simpl; try done. solve_proper.
  Qed.

  Global Instance arc_inv_proper :
    Proper (pointwise_relation _ (≡) ==> (≡) ==>
                eq ==> eq ==> eq ==> eq ==> eq ==> (≡))
           arc_inv.
  Proof.
    repeat intro. subst.
    apply bi.sep_proper; [done|].
    apply bi.sep_proper; apply GPS_INV_proper; auto;
    move => b ?????; apply bi.exist_proper => ?; solve_proper.
  Qed.

  Global Instance is_arc_contractive n :
    Proper (pointwise_relation _ (dist_later n) ==> dist_later n ==>
                         eq ==> eq ==> eq ==> eq ==> eq ==> eq ==> dist n)
           is_arc.
  Proof.
    repeat intro. subst. constructor => ?.
    rewrite /is_arc. apply view_inv_contractive.
    dist_later_intro; by apply arc_inv_ne.
  Qed.

  Global Instance is_arc_proper :
    Proper (pointwise_relation _ (≡) ==> (≡) ==> eq
                ==> eq ==> eq ==> eq ==> eq ==> eq ==> (≡)) is_arc.
  Proof.
    repeat intro. subst.
    by apply view_inv_proper, arc_inv_proper.
  Qed.

  Local Instance strong_interp_read_persistent γi γw γsw l γs t s v :
    Persistent (strong_interp P1 (l >> 1) γi γw γsw false l γs t s v).
  Proof. apply bi.exist_persistent. intros [[? []]|]; simpl; by apply _. Qed.
  Local Instance weak_interp_read_persistent i γs γsw l γw t s v :
    Persistent (weak_interp P2 l i γs γsw false (l >> 1) γw t s v).
  Proof.
    intros. apply bi.exist_persistent.
    intros [[?|] [[[?[]]|?|]|]]; simpl; apply _.
  Qed.

  Lemma SeenActs_join γ l Mt Mt' :
    ⊢ (SeenActs γ l Mt ∗ SeenActs γ l Mt') ∗-∗ SeenActs γ l (Mt ∪ Mt').
  Proof.
    iSplit.
    - iIntros "[S1 S2]". iDestruct "S1" as (t1 v1) "[R1 MAX1]".
      iDestruct "S2" as (t2 v2) "[R2 MAX2]".
      iDestruct "MAX1" as %MAX1. iDestruct "MAX2" as %MAX2.
      case (decide (t1 ≤ t2)%positive) => [Le|/Pos.lt_nle /Pos.lt_le_incl Le].
      + iExists t2, v2. iFrame "R2". iPureIntro.
        move => ? /elem_of_union [/MAX1 -> //|/MAX2//].
      + iExists t1, v1. iFrame "R1". iPureIntro.
        move => ? /elem_of_union [/MAX1//|/MAX2 ->//].
    - iDestruct 1 as (t v) "[#R MAX]". iDestruct "MAX" as %MAX.
      iSplitL""; iExists t, v; iFrame "R"; iPureIntro; move => ? In;
        apply MAX, elem_of_union; [by left|by right].
  Qed.

  Lemma arc_inv_split Vb γi γs γw γsw l E:
    (⊒Vb → ▷ arc_inv P1 P2 γi γs γw γsw l)
    ={E}=∗ ((∃ Mt, StrongMoveAuth γsw Mt) ∗
            (∃ Dt, StrongDownAuth γsw Dt) ∗
            (∃ Ut, WeakUpAuth γsw Ut)) ∗
      (⊒Vb →
        ▷ GPS_INV (strong_interp P1 (l >> 1) γi γw γsw) l strong_noCAS γs) ∗
      (⊒Vb →
        ▷ GPS_INV (weak_interp P2 l γi γs γsw) (l >> 1) (weak_noCAS γsw) γw).
  Proof.
    rewrite -!view_join_unfold !view_join_later.
    iDestruct 1 as "((SMA & SDA & WUA) & $ & $)".
    iDestruct "SMA" as (Mt) ">SMA". iDestruct "SDA" as (Dt) ">SDA".
    iDestruct "WUA" as (Ut) ">WUA".
    iIntros "!>".
    iSplitL "SMA"; last iSplitL "SDA"; iExists _;
      rewrite view_join_embed; iFrame.
  Qed.

  Lemma arc_inv_join Vb γi γs γw γsw l :
    (∃ Mt, StrongMoveAuth γsw Mt) -∗ (∃ Dt, StrongDownAuth γsw Dt) -∗
      (∃ Ut, WeakUpAuth γsw Ut) -∗
      (⊒Vb →
        ▷ GPS_INV (strong_interp P1 (l >> 1) γi γw γsw) l strong_noCAS γs) -∗
      (⊒Vb →
        ▷ GPS_INV (weak_interp P2 l γi γs γsw) (l >> 1) (weak_noCAS γsw) γw) -∗
    (⊒Vb → ▷ arc_inv P1 P2 γi γs γw γsw l).
  Proof.
    iIntros "SMA SDA WUA IS IW #In". iFrame "SMA SDA WUA".
    iDestruct ("IS" with "In") as "$". by iDestruct ("IW" with "In") as "$".
  Qed.

  Lemma strong_arc_acc_open l t γi γs γw γsw P E :
    P -∗ strong_arc_acc l t γi γs γw γsw P E ={E,↑histN}=∗
      ∃ Vb q Mt Dt, (StrongTok γsw q ∗
      (⊒Vb → view_tok γi (q / 2)) ∗
      (∃ v, ⊒Vb → GPS_SWSharedReader l t ((): unitProtocol) v q γs) ∗
      StrMoves γsw q Mt ∗ StrDowns γsw q Dt ∗ StrWkTok γsw q) ∗
      (∀ Mt' Dt',
        StrongTok γsw q -∗
        (⊒Vb → view_tok γi (q / 2)) -∗
        (∃ v, ⊒Vb → GPS_SWSharedReader l t ((): unitProtocol) v q γs) -∗
        StrMoves γsw q (Mt ∪ Mt') -∗
        (if decide (Mt' = ∅) then True else SeenActs γs l Mt') -∗
        StrDowns γsw q (Dt ∪ Dt') -∗
        (if decide (Dt' = ∅) then True else SeenActs γw (l >> 1) Dt') -∗
        StrWkTok γsw q ={↑histN,E}=∗ P).
  Proof.
    iIntros "HP Hacc". iMod ("Hacc" with "HP") as (Vb q) "[Hown Hclose2]".
    iExists Vb, q. iMod (monPred_in_later_timeless with "Hown") as "Hown".
    rewrite monPred_in_exist'. iDestruct "Hown" as (v) "Hown".
    rewrite monPred_in_exist'. iDestruct "Hown" as (Mt) "Hown".
    rewrite monPred_in_exist'. iDestruct "Hown" as (Dt) "Hown".
    rewrite 7!monPred_in_sep'.
    iDestruct "Hown" as "(St & tok & SR & SM & SeenM & SD & SeenD & oW)".
    iExists Mt, Dt. iFrame "tok". iSplitR "Hclose2 SeenM SeenD".
    - iSplitL "St". { by rewrite monPred_in_embed' /StrongTok. }
      iSplitL "SR". { by iExists _. } iSplitL "SM".
      { by rewrite monPred_in_embed' /StrMoves. } iSplitL "SD".
      { by rewrite monPred_in_embed' /StrDowns. }
      by rewrite monPred_in_embed'.
    - iIntros "!>" (Mt' Dt') "St tok SR SM SeenM' SD SeenD' oW".
      iMod ("Hclose2" with "[-]") as "$"; [|done]. iIntros "#mb !>".
      iSpecialize ("tok" with "mb").
      iDestruct "SR" as (v') "SR". iSpecialize ("SR" with "mb").
      iExists _,_,_. iFrame "St tok SR SM SD oW".
      iSpecialize ("SeenM" with "mb"). iSpecialize ("SeenD" with "mb").
      iSplitL "SeenM SeenM'"; (case decide => [->|?];
        [by rewrite right_id_L| iApply SeenActs_join; by iFrame]).
  Qed.

  Lemma strong_arc_acc_open_no_change l t γi γs γw γsw P E :
    P -∗ strong_arc_acc l t γi γs γw γsw P E ={E,↑histN}=∗
      ∃ Vb q Mt Dt, (StrongTok γsw q ∗
      (⊒Vb → view_tok γi (q / 2)) ∗
      (∃ v, ⊒Vb → GPS_SWSharedReader l t ((): unitProtocol) v q γs) ∗
      StrMoves γsw q Mt ∗ StrDowns γsw q Dt ∗ StrWkTok γsw q) ∗
      (StrongTok γsw q -∗
        (⊒Vb → view_tok γi (q / 2)) -∗
        (∃ v, ⊒Vb → GPS_SWSharedReader l t ((): unitProtocol) v q γs) -∗
        StrMoves γsw q Mt -∗ StrDowns γsw q Dt -∗
        StrWkTok γsw q ={↑histN,E}=∗ P).
  Proof.
    iIntros "HP Hacc". iMod (strong_arc_acc_open with "HP Hacc")
                      as (Vs q Mt Dt) "[(St & tok & SR & SM & SD & oW) Hclose2]".
    iExists Vs, q, Mt, Dt. iFrame "St tok SR SM SD oW".
    iIntros "!> St tok SR SM SD oW".
    iApply ("Hclose2" $! ∅ ∅ with "St tok SR [SM] [//] [SD] [//] oW");
      by rewrite right_id_L.
  Qed.

  Lemma strong_arc_acc_open_2 l t γi γs γw γsw P E :
    P -∗ strong_arc_acc l t γi γs γw γsw P E ={E,↑histN}=∗
      ∃ Vb q Mt Dt, (StrongTok γsw q ∗
      (⊒Vb → view_tok γi (q / 2)) ∗
      (∃ v, ⊒Vb → GPS_SWSharedReader l t ((): unitProtocol) v q γs) ∗
      StrMoves γsw q Mt ∗ StrDowns γsw q Dt ∗ StrWkTok γsw q) ∗
      (∀ Mt' Dt',
         StrongTok γsw q -∗
         (⊒Vb → view_tok γi (q / 2)) -∗
        (∃ v, GPS_SWSharedReader l t ((): unitProtocol) v q γs) -∗
        StrMoves γsw q (Mt ∪ Mt') -∗
        (if decide (Mt' = ∅) then True else SeenActs γs l Mt') -∗
        StrDowns γsw q (Dt ∪ Dt') -∗
        (if decide (Dt' = ∅) then True else SeenActs γw (l >> 1) Dt') -∗
        StrWkTok γsw q ={↑histN,E}=∗ P).
  Proof.
    iIntros "HP Hacc". iMod (strong_arc_acc_open with "HP Hacc")
                        as (Vs q Mt Dt) "[(St & tok & SR & SM & SD & oW) Hclose2]".
    iExists Vs, q, Mt, Dt. iFrame "St tok SR SM SD oW".
    iIntros "!>" (Mt' Dt') "St tok SR SM SeenM SD SeenD oW".
    iApply ("Hclose2" $! Mt' Dt' with "St tok [SR] SM SeenM SD SeenD oW").
    iDestruct "SR" as (?) "SR". iExists _. by iIntros "_".
  Qed.

  Lemma strong_arc_acc_open_no_change_2 l t γi γs γw γsw P E :
    P -∗ strong_arc_acc l t γi γs γw γsw P E ={E,↑histN}=∗
      ∃ Vb q Mt Dt, (StrongTok γsw q ∗
      (⊒Vb → view_tok γi (q / 2)) ∗
      (∃ v, ⊒Vb → GPS_SWSharedReader l t ((): unitProtocol) v q γs) ∗
      StrMoves γsw q Mt ∗ StrDowns γsw q Dt ∗ StrWkTok γsw q) ∗
      (StrongTok γsw q -∗
        (⊒Vb → view_tok γi (q / 2)) -∗
        (∃ v, GPS_SWSharedReader l t ((): unitProtocol) v q γs) -∗
        StrMoves γsw q Mt -∗ StrDowns γsw q Dt -∗
        StrWkTok γsw q ={↑histN,E}=∗ P).
  Proof.
    iIntros "HP Hacc". iMod (strong_arc_acc_open_no_change with "HP Hacc")
                        as (Vs q Mt Dt) "[(St & tok & SR & SM & SD & oW) Hclose2]".
    iExists Vs, q, Mt, Dt. iFrame "St tok SR SM SD oW".
    iIntros "!> St tok SR SM SD oW". iApply ("Hclose2" with "St tok [SR] SM SD oW").
    iDestruct "SR" as (?) "SR". iExists _. by iIntros "_".
  Qed.

  Lemma weak_arc_acc_open l t γi γs γw γsw P E :
    P -∗ weak_arc_acc l t γi γs γw γsw P E ={E,↑histN}=∗
      ∃ Vb q Ut, (WeakTok γsw q ∗
        (⊒Vb → view_tok γi (q / 2)) ∗
        (∃ v, ⊒Vb →
                GPS_SWSharedReader (l >> 1) t ((): unitProtocol) v q γw) ∗
        WkUps γsw q Ut) ∗
      (∀ Ut', WeakTok γsw q -∗
        (⊒Vb → view_tok γi (q / 2)) -∗
        (∃ v, ⊒Vb →
                GPS_SWSharedReader (l >> 1) t ((): unitProtocol) v q γw) -∗
        WkUps γsw q (Ut ∪ Ut') -∗
        (if decide (Ut' = ∅) then True else SeenActs γs l Ut') ={↑histN,E}=∗ P).
  Proof.
    iIntros "HP Hacc". iMod ("Hacc" with "HP") as (Vb q) "[Hown Hclose2]".
    iExists Vb, q. iMod (monPred_in_later_timeless with "Hown") as "Hown".
    rewrite monPred_in_exist'. iDestruct "Hown" as (v) "Hown".
    rewrite monPred_in_exist'. iDestruct "Hown" as (Ut) "Hown". iExists Ut.
    rewrite 4!monPred_in_sep'. iDestruct "Hown" as "(Wt & $ & WR & WU & SeenU)".
    iSplitR "Hclose2 SeenU".
    - iSplitL "Wt". { by rewrite monPred_in_embed' /WeakTok. }
      iSplitL "WR". { by iExists _. } by rewrite monPred_in_embed' /WkUps.
    - iIntros "!>" (Ut') "Wt tok WR WU SeenU'".
      iMod ("Hclose2" with "[-]") as "$"; [|done]. iIntros "#mb !>".
      iDestruct "WR" as (v') "WR". iSpecialize ("WR" with "mb").
      iSpecialize ("tok" with "mb").
      iExists _,_. iFrame "Wt tok WR WU".
      iSpecialize ("SeenU" with "mb"). case decide => [->|?];
        [by rewrite right_id_L| iApply SeenActs_join; by iFrame].
  Qed.

  Lemma weak_arc_acc_open_no_change l t γi γs γw γsw P E :
    P -∗ weak_arc_acc l t γi γs γw γsw P E ={E,↑histN}=∗
      ∃ Vb q Ut, (WeakTok γsw q ∗
        (⊒Vb → view_tok γi (q / 2)) ∗
        (∃ v, ⊒Vb →
                GPS_SWSharedReader (l >> 1) t ((): unitProtocol) v q γw) ∗
        WkUps γsw q Ut) ∗
      (WeakTok γsw q -∗
        (⊒Vb → view_tok γi (q / 2)) -∗
        (∃ v, ⊒Vb →
              GPS_SWSharedReader (l >> 1) t ((): unitProtocol) v q γw) -∗
         WkUps γsw q Ut ={↑histN,E}=∗ P).
  Proof.
    iIntros "HP Hacc". iMod (weak_arc_acc_open with "HP Hacc")
                        as (Vs q Ut) "[(Wt & tok & WR & WU) Hclose2]".
    iExists Vs, q, Ut. iFrame "Wt tok WR WU".
    iIntros "!> Wt tok WR WU".
    iApply ("Hclose2" $! ∅ with "Wt tok WR [WU] [//]"); by rewrite right_id_L.
  Qed.

  Lemma weak_arc_acc_open_2 l t γi γs γw γsw P E :
    P -∗ weak_arc_acc l t γi γs γw γsw P E ={E,↑histN}=∗
      ∃ Vb q Ut, (WeakTok γsw q ∗
        (⊒Vb → view_tok γi (q / 2)) ∗
        (∃ v, ⊒Vb →
                GPS_SWSharedReader (l >> 1) t ((): unitProtocol) v q γw) ∗
        WkUps γsw q Ut) ∗
      (∀ Ut', WeakTok γsw q -∗
        (⊒Vb → view_tok γi (q / 2)) -∗
        (∃ v, GPS_SWSharedReader (l >> 1) t ((): unitProtocol) v q γw) -∗
        WkUps γsw q (Ut ∪ Ut') -∗
        (if decide (Ut' = ∅) then True else SeenActs γs l Ut') ={↑histN,E}=∗ P).
  Proof.
    iIntros "HP Hacc". iMod (weak_arc_acc_open with "HP Hacc")
                        as (Vs q Ut) "[(Wt & tok & WR & WU) Hclose2]".
    iExists Vs, q, Ut. iFrame "Wt tok WR WU".
    iIntros "!>" (Ut') "Wt tok WR WU SeenU".
    iApply ("Hclose2" $! Ut' with "Wt tok [WR] WU SeenU").
    iDestruct "WR" as (?) "WR". iExists _. by iIntros "_".
  Qed.

  Lemma weak_arc_acc_open_no_change_2 l t γi γs γw γsw P E :
    P -∗ weak_arc_acc l t γi γs γw γsw P E ={E,↑histN}=∗
      ∃ Vb q Ut, (WeakTok γsw q ∗
        (⊒Vb → view_tok γi (q / 2)) ∗
        (∃ v, ⊒Vb →
                GPS_SWSharedReader (l >> 1) t ((): unitProtocol) v q γw) ∗
        WkUps γsw q Ut) ∗
      (WeakTok γsw q -∗
        (⊒Vb → view_tok γi (q / 2)) -∗
        (∃ v, GPS_SWSharedReader (l >> 1) t ((): unitProtocol) v q γw) -∗
        WkUps γsw q Ut ={↑histN,E}=∗ P).
  Proof.
    iIntros "HP Hacc". iMod (weak_arc_acc_open_no_change with "HP Hacc")
                        as (Vs q Ut) "[(Wt & tok & WR & WU) Hclose2]".
    iExists Vs, q, Ut. iFrame "Wt tok WR WU".
    iIntros "!> Wt tok WR WU". iApply ("Hclose2" with "Wt tok [WR] WU").
    iDestruct "WR" as (?) "WR". iExists _. by iIntros "_".
  Qed.

  (* MAIN SPECS START HERE *)
  Lemma create_strong {HPn: HP1} E l :
    l ↦ #1 -∗ (l >> 1) ↦ #1 -∗ P1 1%Qp ={E}=∗
      ∃ γi γs γw γsw t q, is_arc P1 P2 N γi γs γw γsw l ∗ P1 q ∗
                     strong_arc t q l γi γs γw γsw .
  Proof.
    iIntros "Hl1 Hl2 HP1".
    iDestruct (HPn (1/2)%Qp (1/2)%Qp with "[HP1]") as "[HP1 HP1']";
      [by rewrite Qp.div_2|rewrite monPred_objectively_elim].
    set stS : strong_stUR := Some ((1/2)%Qp, xH).
    set stW : weak_stUR   := (Some 1%Qp, None).
    iAssert (|==> ∃ γ, StrongAuth γ stS ∗ StrongTok γ (1/2)%Qp ∗
                       WeakAuth γ stW ∗
                       StrongMoveAuth γ ∅ ∗ StrMoves γ 1%Qp ∅ ∗
                       StrongDownAuth γ ∅ ∗ StrDowns γ 1%Qp ∅ ∗
                       WeakUpAuth γ ∅ ∗ WkUps γ 1%Qp ∅ ∗
                       ⎡ own γ ((ε, ◯ ((Some 1%Qp, ε)), ε) : arcUR) ⎤)%I as ">Own".
    { do 9 setoid_rewrite <- embed_sep. do 9 setoid_rewrite <- own_op.
      iMod (own_alloc (A:=arcUR)) as (γ) "Own"; last by iExists γ.
      split; split; simpl.
      - rewrite !right_id. by apply auth_both_valid_discrete.
      - rewrite !left_id. by apply auth_both_valid_discrete.
      - split; split; simpl; rewrite !left_id !right_id.
        + by apply auth_both_valid_discrete.
        + by apply auth_auth_valid.
        + by apply auth_both_valid_discrete.
        + by apply auth_auth_valid.
      - split; simpl; rewrite !left_id !right_id.
        + by apply auth_both_valid_discrete.
        + by apply auth_auth_valid. }
    iDestruct "Own" as (γsw)
      "(SA & St & WA & SMA & [SM1 SM2] & SDA & [SD1 SD2] & WUA & WU & [S1 S2])".
    iMod (view_inv_alloc_frac N _ (1/2 + 1/2/2) (1/2/2)) as (γi) "[[tok2 tok1] VI]";
      first by rewrite -Qp.add_assoc 2!Qp.div_2.
    set Qs : time → time → gname → gname → vProp :=
      (λ ts tw γs γw,
        GPS_SWSharedReader l ts (() : unitProtocol) #1 (1/2)%Qp γs ∗
        GPS_Reader l ts (() : unitProtocol) #1 γs ∗
        GPS_Reader  (l >> 1) tw (() : unitProtocol) #1 γw)%I.
    iMod (GPS_SWRaw_Init_vs_strong_2 _ _
          (λ γw, strong_interp P1 (l >> 1) γi γw γsw)
          (λ γs, weak_interp P2 l γi γs γsw) true _ _ () () Qs
          with "Hl1 Hl2 [-HP1' S2 SM2 SD2 SMA SDA WUA St VI]")
          as (γs γw ts tw) "INV".
    { iIntros (ts tw γs γw) "Ws Ww". simpl.
      iDestruct (GPS_SWWriter_shared with "Ws") as "[Ws [Rs1 Rs2]]".
      iDestruct (GPS_SWWriter_shared with "Ww") as "[Ww [Rw1 Rw2]]".
      iDestruct (GPS_SWSharedReader_Reader with "Rs1") as "#R1".
      iDestruct (GPS_SWSharedReader_Reader with "Rw2") as "#R2".
      iModIntro. iSplitL "SA SM1 SD1 Ws Rs1 HP1 S1 tok1"; last iSplitR "Rs2".
      - iNext. iExists stS. iSplitL ""; [done|]. iFrame "SA Ws".
        iExists (1/2)%Qp. rewrite Qp.div_2. iSplitL ""; [done|]. iFrame "HP1".
        iExists ∅,∅. iFrame "tok1 Rs1 SM1 SD1 S1".
        iSplitL ""; iExists _, _; [by iFrame "R1"|by iFrame "R2"].
      - iNext. iExists stW.  iSplitL ""; [done|]. iFrame "WA". iSplitL ""; [done|].
        iFrame "Ww". iExists ∅. iFrame "tok2 Rw2 WU Rw1". iExists _,_. by iFrame "R1".
      - by iFrame "Rs2 R1 R2". }
    iExists γi, γs, γw, γsw, _, (1/2)%Qp. iFrame "HP1'".
    iDestruct ("INV" $! strong_noCAS (weak_noCAS γsw)) as "(Invs & Invw & Rs & #R1 & #R2)".
    iMod ("VI" $! (arc_inv P1 P2 γi γs γw γsw l) with "[SMA SDA WUA $Invs $Invw]")
      as "[$ tok]".
    { iNext. iSplitL "SMA"; [by iExists _|]. iSplitL "SDA"; by iExists _. }
    iModIntro. iExists _,∅,∅. iFrame "St tok Rs SM2 SD2 S2".
    iSplitL""; iExists _,_; [by iFrame "R1"|by iFrame "R2"].
  Qed.

  Lemma create_weak E l :
    l ↦ #0 -∗ (l >> 1) ↦ #1 -∗ P2 ={E}=∗ ∃ γi γs γw γsw t q,
        is_arc P1 P2 N γi γs γw γsw l ∗ weak_arc t q l γi γs γw γsw.
  Proof.
    iIntros "Hl1 Hl2 HP2".
    set stS : strong_stUR := None.
    set stW : weak_stUR   := (None, Some (Cinl ((1/2)%Qp, xH))).
    iAssert (|==> ∃ γ, StrongAuth γ stS ∗ WeakAuth γ stW ∗ WeakTok γ (1/2)%Qp ∗
                       StrongMoveAuth γ ∅ ∗ StrMoves γ 1%Qp ∅ ∗
                       StrongDownAuth γ ∅ ∗ StrDowns γ 1%Qp ∅ ∗
                       WeakUpAuth γ ∅ ∗ WkUps γ 1%Qp ∅)%I as ">Own".
    { do 8 setoid_rewrite <- embed_sep. do 8 setoid_rewrite <- own_op.
      iMod (own_alloc (A:=arcUR)) as (γ) "?"; last by iExists γ.
      split; split; simpl.
      - rewrite !right_id. by apply auth_auth_valid.
      - rewrite !left_id !right_id. by apply auth_both_valid_discrete.
      - split; split; simpl; rewrite !left_id !right_id.
        + by apply auth_both_valid_discrete.
        + by apply auth_auth_valid.
        + by apply auth_both_valid_discrete.
        + by apply auth_auth_valid.
      - split; simpl; rewrite !left_id ?right_id.
        + by apply auth_both_valid_discrete.
        + by apply auth_auth_valid. }
    iDestruct "Own" as (γsw) "(SA & WA & Wt & SMA & SM & SDA & SD & WUA & [WU1 WU2])".
    iMod (view_inv_alloc_frac N _ (1/2 + 1/2/2) (1/2/2)) as (γi) "[[tok2 tok1] VI]";
      first by rewrite -Qp.add_assoc 2!Qp.div_2.
    set Qs : time → time → gname → gname → vProp :=
      (λ ts tw γs γw,
        GPS_SWSharedReader (l >> 1) tw (() : unitProtocol) #1 (1 / 2)%Qp γw ∗
        GPS_Reader l ts (() : unitProtocol) #0 γs ∗
        GPS_Reader  (l >> 1) tw (() : unitProtocol) #1 γw)%I.
    iMod (GPS_SWRaw_Init_vs_strong_2 _ _
            (λ γw, strong_interp P1 (l >> 1) γi γw γsw)
            (λ γs, weak_interp P2 l γi γs γsw) true _ _ () () Qs
            with "Hl1 Hl2 [- SMA SDA WUA WU2 Wt VI]") as (γs γw ts tw) "INV".
    { iIntros (ts tw γs γw) "Ws Ww". simpl.
      iDestruct (GPS_SWWriter_shared with "Ww") as "[Ww [Rw1 Rw2]]".
      iDestruct (GPS_SWWriter_Reader with "Ws") as "#R1".
      iDestruct (GPS_SWSharedReader_Reader with "Rw2") as "#R2".
      iModIntro. iSplitL "SA"; last iSplitR "Rw2".
      - iNext. iExists stS. iSplitL ""; [done|]. by iFrame "SA".
      - iNext. iExists stW. iSplitL ""; [done|].
        iFrame "WA HP2 Ww". iSplitL "tok1 Rw1 WU1".
        + iExists (1/2)%Qp,∅. rewrite Qp.div_2. iSplitL ""; [done|].
          iFrame "tok1 Rw1 WU1". iExists _, _; by iFrame "R1".
        + iFrame "tok2". iSplitL "Ws"; [by iExists _|]. iSplitL "SM"; iExists _; by iFrame.
      - by iFrame "Rw2 R1 R2". }
    iExists γi, γs, γw, γsw, _, (1/2)%Qp.
    iDestruct ("INV" $! strong_noCAS (weak_noCAS γsw)) as "(Invs & Invw & Rw & #R1 & #R2)".
    iMod ("VI" $! (arc_inv P1 P2 γi γs γw γsw l) with "[SMA SDA WUA $Invs $Invw]")
      as "[$ tok]".
    { iNext. iSplitL "SMA"; [by iExists _|]. iSplitL "SDA"; by iExists _. }
    iModIntro. iExists _,∅. iFrame "Wt tok Rw WU2". iExists _,_; by iFrame "R1".
  Qed.

  Lemma strong_count_spec γi γs γw γsw l t v (P : vProp) tid :
    is_arc P1 P2 N γi γs γw γsw l -∗ strong_arc_acc l t γi γs γw γsw P (⊤ ∖ ↑N) -∗
    {{{ GPS_Reader l t () v γs ∗ P }}}
      strong_count [ #l] @ tid; ⊤
    {{{ (c : Z), RET #c; P ∗ ⌜0 < c⌝ }}}.
  Proof.
    iIntros "#INV #Hacc !# * [#RR HP] HΦ". iLöb as "IH". wp_rec.
    iMod (view_inv_acc_base_1 γi N with "INV") as "VI"; [done|].
    iMod (strong_arc_acc_open_no_change_2 with "HP Hacc")
      as (Vs q Mt Dt) "[(St & tok & SR & SM & SD & oW) Hclose2]".
    iSpecialize ("VI" $! Vs with "tok").
    iMod (fupd_mask_mono with "VI") as "[tok VI]"; [set_solver|].
    iDestruct "VI" as (Vb) "[VI Hclose1]".
    iMod (arc_inv_split with "VI") as "((SMA & MDU) & IS & IW)".
    iDestruct "SMA" as (Mt') "SMA".
    iDestruct (StrongMoveAuth_agree with "[$SMA $SM]") as %?. subst Mt'.
    iDestruct "SR" as (v0) "SR".
    iDestruct (GPS_SWSharedReader_Reader_join_subjectively _ _ _ _ _ _  q
        with "RR [SR]") as "[SR1 SR2]".
    { rewrite monPred_subjectively_unfold.
      iDestruct (monPred_in_view_elim with "SR") as (V') "SR". by iExists V'. }
    set R : time → unitProtocol → val → vProp :=
      (λ t' _ v', (∃ z : Z, ⌜v' = #z ∧ 0 < z⌝) ∗
            StrongTok γsw q ∗ StrongMoveAuth γsw Mt )%I.
    iApply (GPS_SWRaw_SharedReader_Read (strong_interp P1 (l >> 1) γi γw γsw) _
              strong_noCAS R with "[$SR1 $IS St SMA]"); [done|by right|..].
    { iIntros "!>" (t' [] v' [_ Ext']). rewrite /StrongTok. iIntros "!>". iSplit.
      - iIntros "#SI !>". iFrame "SI SMA". rewrite /StrongTok. iFrame "St".
        iDestruct "SI" as (st) "[% Eq]". subst v'. iExists (Z_of_arcstrong_st st).
        destruct st as [[]|]; simpl; [|done]. iPureIntro. split; [done|split].
      - iDestruct 1 as (st) "(Eq1 & SA & SI)". iDestruct "Eq1" as %?. subst v'.
        destruct st as [[q' n]|]; simpl.
        + iModIntro. iFrame "SMA". rewrite /StrongTok. iFrame "St".
          iSplitR""; [iExists (Some (q',n))|iExists (Z.pos n)].
          * iSplitL""; [done|]. by iFrame.
          * iPureIntro. split; [done|split].
        + iDestruct (StrongTok_Auth_agree with "[$SA St]") as %(?&?&EQ&?); [|done].
          rewrite /StrongTok. iFrame "St". }
    iIntros "!>" (t' [] v'). iDestruct 1 as "(_ & RR' & IS & Rs & St & SMA)".
    iDestruct "Rs" as (z) "[% %]". subst v'.
    iDestruct (GPS_SWSharedReaders_join with "SR2 RR'") as "SR". rewrite Qp.div_2.
    iSpecialize ("Hclose1" with "tok [SMA MDU IW IS]").
    { iDestruct "MDU" as "[SDA WUA]".
      iApply (arc_inv_join with "[SMA] SDA WUA IS IW"). by iExists _. }
    iMod (fupd_mask_mono with "Hclose1") as "[tok Hclose1]"; [set_solver|].
    iMod ("Hclose2" with "St tok [SR] SM SD oW") as "HP"; [by iExists _|].
    iModIntro. iMod "Hclose1". iModIntro. iApply ("HΦ"). by iFrame "HP".
  Qed.

  (* FIXME : in the case the weak count is locked, we can possibly
     return -1. This problem already exists in Rust. *)
  Lemma weak_count_spec γi γs γw γsw l t v ts (P : vProp) tid :
    is_arc P1 P2 N γi γs γw γsw l -∗
    strong_arc_acc l ts γi γs γw γsw P (⊤ ∖ ↑N) -∗
    GPS_Reader (l >> 1) t () v γw -∗
    {{{ P }}}
      weak_count [ #l] @ tid; ⊤
    {{{ (c : Z), RET #c; P ∗ ⌜-1 ≤ c⌝ }}}.
  Proof.
    iIntros "#INV #Hacc #RR !# * HP HΦ". iLöb as "IH". wp_rec. wp_op.
    iMod (view_inv_acc_base_1 γi N with "INV") as "VI"; [done|].
    iMod (strong_arc_acc_open_no_change with "HP Hacc")
      as (Vs q Mt Dt) "[(St & tok & SR & SM & SD & oW) Hclose2]".
    iSpecialize ("VI" $! Vs with "tok").
    iMod (fupd_mask_mono with "VI") as "[tok VI]"; [set_solver|].
    iDestruct "VI" as (Vb) "[VI Hclose1]".
    iMod (arc_inv_split with "VI") as "(MA & IS & IW)".

    set R : time → unitProtocol → val → vProp :=
      (λ _ _ v', ∃ z : Z, ⌜v' = #z ∧ -1 ≤ z⌝)%I.
    iApply (GPS_SWRaw_Read (weak_interp P2 l γi γs γsw) _
              (weak_noCAS γsw) R with "[$RR $IW]"); [done|by right|..].
    { iIntros "!>" (t' [] v' [_ Ext']) "!>". iSplit; last iSplit.
      - iIntros "#WI !>". iFrame "WI". iDestruct "WI" as (st) "[Eq1 Eq2]".
        iDestruct "Eq1" as %?. subst v'. iExists (Z_of_arcweak_st st).
        iPureIntro. split; [done|]. by apply weak_stUR_value.
      - iDestruct 1 as (st) "[Eq1 WI]". iDestruct "Eq1" as %?. subst v'.
        iModIntro. iSplitR "". { iExists _. by iFrame "WI". }
        iExists _. iPureIntro. split; [done|]. by apply weak_stUR_value.
      - iDestruct 1 as "[% $]". subst v'. iIntros "!> !%". split; [done|].
        by eexists. }
    iIntros "!>" (t' [] v'). iDestruct 1 as "(_ & _ & IW & Rs)".
    iDestruct "Rs" as (z) "Eq". iDestruct "Eq" as %[? Le]. subst v'.
    iSpecialize ("Hclose1" with "tok [MA IW IS]").
    { iDestruct "MA" as "[SMA [SDA WUA]]".
      by iApply (arc_inv_join with "SMA SDA WUA IS IW"). }
    iMod (fupd_mask_mono with "Hclose1") as "[tok Hclose1]"; [set_solver|].
    iMod ("Hclose2" with "St tok SR SM SD oW") as "HP".
    iModIntro. iMod "Hclose1". iModIntro. iApply ("HΦ"). by iFrame "HP".
  Qed.

  Lemma arc_strong_interp_comparable l γi γs γw γsw t s v (n: Z):
    strong_interp P1 (l >> 1) γi γw γsw true l γs t s v
    ∨ strong_interp P1 (l >> 1) γi γw γsw false l γs t s v
      -∗ ⌜∃ vl : lit, v = #vl ∧ lit_comparable n vl⌝.
  Proof.
    iIntros "[F|F]"; iDestruct "F" as (st ?) "_"; subst v;
    iExists _; iPureIntro; (split; [done|]); by constructor.
  Qed.

  Lemma arc_strong_interp_comparable_2 l γi γs γw γsw t s v (n: Z):
    strong_interp P1 (l >> 1) γi γw γsw true l γs t s v
    ∨ strong_interp P1 (l >> 1) γi γw γsw false l γs t s v
    ∨ strong_noCAS l γs t s v
      -∗ ⌜∃ vl : lit, v = #vl ∧ lit_comparable n vl⌝.
  Proof.
    iIntros "[F|[F|%]]";
    last (subst; iPureIntro; eexists; split; [done|by constructor]);
    iDestruct "F" as (st ?) "_"; subst;
    iExists _; iPureIntro; (split; [done|]); by constructor.
  Qed.

  Lemma clone_arc_spec {HPn: HP1} γi γs γw γsw l t v (P : vProp) tid :
    is_arc P1 P2 N γi γs γw γsw l -∗ strong_arc_acc l t γi γs γw γsw P (⊤ ∖ ↑N) -∗
    (∃ t' v', GPS_Reader (l >> 1) t' () v' γw) -∗
    GPS_Reader l t () v γs -∗
    {{{ P }}} clone_arc [ #l] @ tid; ⊤
    {{{ t' q', RET #☠; P ∗ strong_arc t' q' l γi γs γw γsw ∗ P1 q' }}}.
  Proof.
    iIntros "#INV #Hacc #WR #RR !# * HP HΦ". iLöb as "IH". wp_rec.
    (* read the value *)
    wp_bind (!ʳˡˣ_)%E.
    (* opening invariant *)
    iMod (view_inv_acc_base_1 γi N with "INV") as "VI"; [done|].
    iMod (strong_arc_acc_open_no_change_2 with "HP Hacc")
      as (Vs q Mt Dt) "[(St & tok & SR & SM & SD & oW) Hclose2]".
    iSpecialize ("VI" $! Vs with "tok").
    iMod (fupd_mask_mono with "VI") as "[tok VI]"; [set_solver|].
    iDestruct "VI" as (Vb) "[VI Hclose1]".
    iMod (arc_inv_split with "VI") as "(MA & IS & IW)".

    iDestruct "SR" as (v0) "SR".
    iDestruct (GPS_SWSharedReader_Reader_join_subjectively _ _ _ _ _ _  q
        with "RR [SR]") as "[SR1 SR2]".
    { rewrite monPred_subjectively_unfold.
      iDestruct (monPred_in_view_elim with "SR") as (V') "SR". by iExists V'. }
    set R : time → unitProtocol → val → vProp := (λ t' _ v', ∃ z : Z, ⌜v' = #z⌝)%I.
    (* actual read *)
    iApply (GPS_SWRaw_SharedReader_Read (strong_interp P1 (l >> 1) γi γw γsw) _
              strong_noCAS R with "[$SR1 $IS]"); [done|by left|..].
    { iIntros "!>" (t' [] v' [_ Ext']) "!>". iSplit.
      - iIntros "#SI !>". iFrame "SI". iDestruct "SI" as (st) "[Eq1 _]".
        iDestruct "Eq1" as %?. subst v'. by iExists _.
      - iDestruct 1 as (st) "[Eq1 SI]". iDestruct "Eq1" as %?. subst v'.
        iModIntro. iSplitR ""; [iExists _; by iFrame "SI"|by iExists _]. }
    iIntros "!>" (t' [] v'). iDestruct 1 as "(_ & SR1 & IS & Rs)".
    iDestruct "Rs" as (z) "%". subst v'.
    iDestruct (GPS_SWSharedReaders_join with "SR2 SR1") as "SR". rewrite Qp.div_2.

    (* closing invariant *)
    iSpecialize ("Hclose1" with "tok [MA IW IS]").
    { iDestruct "MA" as "[SMA [SDA WUA]]".
      by iApply (arc_inv_join with "SMA SDA WUA IS IW"). }
    iMod (fupd_mask_mono with "Hclose1") as "[tok Hclose1]"; [set_solver|].
    iMod ("Hclose2" with "St tok [SR] SM SD oW") as "HP"; [by iExists _|].
    iModIntro. iMod "Hclose1" as "_".

    iModIntro. wp_let. wp_op. clear Vs R v0 Mt Dt t' Vb q.
    (* now we can CAS *)
    wp_bind (CAS _ _ _ _ _ _).
    (* not really, just preparing *)
    (* opening invariant *)
    iMod (view_inv_acc_base_1 γi N with "INV") as "VI"; [done|].
    iMod (strong_arc_acc_open_2 with "HP Hacc")
      as (Vs q Mt Dt) "[(St & tok & SR & SM & SD & oW) Hclose2]".
    iSpecialize ("VI" $! Vs with "tok").
    iMod (fupd_mask_mono with "VI") as "[tok VI]"; [set_solver|].
    iDestruct "VI" as (Vb) "[VI Hclose1]".
    iMod (arc_inv_split with "VI") as "((SMA & MDU) & IS & IW)".

    iDestruct "SR" as (v0) "SR".
    iDestruct (GPS_SWSharedReader_Reader_join_subjectively _ _ _ _ _ _  q
        with "RR [SR]") as "[SR1 SR2]".
    { rewrite monPred_subjectively_unfold.
      iDestruct (monPred_in_view_elim with "SR") as (V') "SR". by iExists V'. }
    iDestruct "SMA" as (Mt') "SMA".
    iDestruct (StrongMoveAuth_agree with "[$SMA $SM]") as %?. subst Mt'.
    set Q: time → unitProtocol → vProp :=
      (λ t'' s'',
        let Mt' := if decide (Z.to_pos z = 1%positive) then (Mt ∪ {[t'']}) else Mt in
        StrongTok γsw q ∗ StrongMoveAuth γsw Mt' ∗ StrMoves γsw q Mt' ∗
        ∃ q'', StrongTok γsw q'' ∗ (<obj> P1 q'') ∗
          (<obj> view_tok γi (q''/2)) ∗
          GPS_SWSharedReader l t'' ((): unitProtocol) #(z+1) q'' γs ∗
          StrMoves γsw q'' Mt' ∗ ⌜∀ t' : time, t' ∈ Mt' → t' ⊑ t''⌝ ∗
          StrDowns γsw q'' ∅ ∗ agown γsw (awk_n ((Some q'', ε))))%I.
    set Q1: time → unitProtocol → vProp := (λ _ _, True)%I.
    set Q2: time → unitProtocol → vProp :=
      (λ tr sr, strong_interp P1 (l >> 1) γi γw γsw true l γs tr sr #z).
    set R: time → unitProtocol → lit → vProp :=
      (λ _ _ _, StrongTok γsw q ∗ StrongMoveAuth γsw Mt ∗ StrMoves γsw q Mt)%I.
    iMod (rel_True_intro tid) as "#rTrue".
    (* here comes the CAS *)
    iApply (GPS_SWRaw_SharedWriter_CAS_int_strong (strong_interp P1 (l >> 1) γi γw γsw)
            _ strong_noCAS false Relaxed Relaxed Relaxed z #(z+1) _ _ _ (q/2) _
            True%I Q Q1 Q2 R _ Vb _ (↑histN) with "[$SR1 $IS St SMA SM $rTrue]");
      [done|done|by left|by left|by left|..].
    { iSplitL "". { iIntros "!>!>" (??? _). by iApply arc_strong_interp_comparable. }
      rewrite /= -(bi.True_sep' (∀ _ (_ : unitProtocol), _)%I).
      iApply (rel_sep_objectively with "[$rTrue St SMA SM]").
      rewrite /StrongTok /StrMoves. iIntros "!>" (t' [] [_ Ext']). iSplit; last first.
      { iIntros (??) "!> !>". iSplit; iIntros "$ !>"; iFrame "SMA";
        rewrite /StrongTok /StrMoves; by iFrame. }
      iSplitL "". { by iIntros "!> $". } iIntros "_".
      iDestruct 1 as (st) "[>Eq [>SA SI]]".
      iDestruct (StrongTok_Auth_agree with "[$SA St]") as %(q'&n&EQ&Eq');
        [by rewrite /StrongTok|]. subst st. iDestruct "Eq" as %Eq.
      inversion Eq. subst z. clear Eq. iDestruct "SI" as "[$ SI]".
      iDestruct "SI" as (q'') "(>Eq'' & HP & SI)". iDestruct "Eq''" as %Eq''.
      iAssert (▷ (P1 (q''/2) ∗ <obj> P1 (q''/2)))%I with "[HP]" as "[HP1 HP2]".
      { iNext. iApply HPn. by rewrite Qp.div_2. }
      iDestruct "SI" as (Mt' Dt') "(>tok & R & SM' & RestS)". rewrite /StrMoves.
      iDestruct "SM'" as ">SM'".
      iDestruct (StrongMoveAuth_agree with "[$SMA SM']") as %?;
        [by rewrite /StrMoves|]. subst Mt'.
      iDestruct (view_tok_split_unit γi (q''/2/2) (q''/2/2) with "[tok]")
        as "[tok1 tok2]"; first by rewrite Qp.div_2.

      iModIntro. iExists (). iSplitL""; [done|]. iIntros (t'' Lt'') "W' _".
      set Mt' : gset time := if decide (n = 1%positive) then (Mt ∪ {[t'']}) else Mt.
      iAssert (|==> StrongMoveAuth γsw Mt' ∗ StrMoves γsw q Mt' ∗
                    StrMoves γsw q'' Mt' ∗
                    <obj> if decide (n = 1%positive)
                          then StrMoveCert γsw t'' else True)%I
              with "[SMA SM SM']" as ">(SMA & SM & [SM1 SM2] & Cert)".
      { case decide => Eq; last first.
        { rewrite /Mt' decide_False; [|done]. rewrite /StrMoves.
          iFrame; by iIntros "!> !>". }
        rewrite /Mt' (decide_True _ _ Eq). rewrite (decide_True _ _ Eq) in Eq'.
        iDestruct (StrMoves_fractional _ _ q with "[SM SM']") as "SM";
          [rewrite /StrMoves; by iFrame|]. subst q'. rewrite Eq''.
        iMod (StrMoves_update _ _ {[t'']} with "[$SMA $SM]") as "($ & SM & Cert)".
        iIntros. rewrite bi.sep_assoc -StrMoves_fractional Eq''. iFrame "SM".
        iIntros "!> !>". by iFrame "Cert". }
      iModIntro. iSplitL "Cert".
      { iIntros "!> _ !> !>". iExists (Some (q', n)). iSplit; [done|].
        destruct n; simpl; [done..|]. iExists t''. iFrame (Lt'').
        iDestruct (monPred_objectively_elim with "Cert") as "$". }
      iIntros "!> !>".
      iDestruct (GPS_SWSharedWriter_Reader_update with "W' R") as "[W' [R1 R2]]".
      iDestruct "RestS" as "(#SeenM & SD & #SeenD & [OS1 OS2])".
      iAssert (⌜∀ t' : time, t' ∈ Mt' → t' ⊑ t''⌝)%I with "[W']" as "#MAX".
      { iDestruct "SeenM" as (t4 v4) "[R4 MAX]". iDestruct "MAX" as %MAX'.
        iDestruct (GPS_SWSharedWriter_latest_time_1 with "W' R4") as %Le4.
        iPureIntro. have MAX2: ∀ t2 : time, t2 ∈ Mt → t2 ⊑ t'' by move =>? /MAX'->.
        rewrite /Mt'. case decide => ?; [|done].
         move => t5 /elem_of_union [/MAX2//|/elem_of_singleton -> //]. }
      iDestruct (GPS_SWSharedReader_Reader with "R1") as "#R''".
      iAssert (SeenActs γs l Mt')%I as "SeenM'". { iExists _,_. iFrame "R'' MAX". }
      iMod (StrongAuth_new_tok _ q' q'' _ Eq'' with "SA") as "[SA St']".
      iAssert (StrDowns γsw (q'' / 2) Dt' ∗ StrDowns γsw (q'' / 2) ∅)%I
        with "[SD]" as "[SD1 SD2]".
      { rewrite -(right_id_L ∅ union Dt') -{1}(Qp.div_2 q'').
        by iApply (StrDowns_forget with "SD"). }
      iModIntro. iSplitR "SA W' tok1 R1 SM1 OS1 SD1 HP1 SeenM'".
      - rewrite /Q Pos2Z.id. iFrame "SMA SM". iSplitL "St"; [by rewrite /StrongTok|].
        iExists _. by iFrame "St' tok2 R2 SM2 HP2 MAX SD2 OS2".
      - iExists (Some ((q' + q'' / 2)%Qp, (n + 1)%positive)). iSplitL ""; [done|].
        iFrame "SA W'". iExists (q''/2)%Qp.
        iSplitL "". { iPureIntro. by rewrite -Qp.add_assoc Qp.div_2. }
        iFrame "HP1". iExists Mt', Dt'. iFrame "tok1 R1 SM1 SeenM' SD1 SeenD OS1". }

    (* finally done with the CAS *)
    iIntros "!>" (b t' [] v') "(IS &%& [([%[%%]]&R'&Q) | ([%[_ %]] &R'&Rs&_)])".
    - subst b v'.
      iDestruct "Q" as "(St & SMA & SM & Q)". iDestruct "Q" as (q'') "Q".
      iDestruct "Q" as "(St'' & HP1 & tok'' & R'' & SM'' & %MAX'' & oW'' & SD'')".
      iDestruct (GPS_SWSharedReaders_join_subjectively _ _ _ _ _ _ _ _ q''
                  with "R' [R'']") as "[R' R'']". { by iApply acq_subjective. }
      iDestruct (GPS_SWSharedReader_Reader with "R'") as "#RR'".
      set Mt' := if decide (Z.to_pos z = 1%positive) then Mt ∪ {[t']} else Mt.
      iAssert (SeenActs γs l Mt')%I with "[]" as "#SeenM'".
      { iExists _, _. iFrame (MAX'') "RR'". }
      iDestruct (GPS_SWSharedReaders_join with "SR2 R'") as "SR".
      (* tedious removal of acq_mod *)
      rewrite Qp.div_2 2!acq_objectively_elim 2!monPred_objectively_elim.
      rewrite 7!acq_embed_elim.

      (* closing *)
      iSpecialize ("Hclose1" with "tok [SMA MDU IW IS]").
      { iClear "#". iDestruct "MDU" as "[SDA WUA]".
        iApply (arc_inv_join with "[SMA] SDA WUA IS IW"). by iExists _. }
      iMod (fupd_mask_mono with "Hclose1") as "[tok Hclose1]"; [set_solver|].

      iMod ("Hclose2" $! (if decide (Z.to_pos z = 1%positive) then {[t']} else ∅) ∅
        with "[St] tok [SR]  [SM] [] [SD] [] oW") as "HP";
        [by iExact "St"|by iExists _|..|by rewrite right_id_L|done|].
      { rewrite /Mt'. case decide => _; [done|by rewrite right_id_L]. }
      { destruct (decide (Z.to_pos _ = _)); [|done].
        iExists _,_. iFrame "RR'". iPureIntro. move => ? /elem_of_singleton -> //. }
      iModIntro. iMod "Hclose1" as "_". iModIntro.
      wp_case. iApply ("HΦ" with "[- $HP]"). iFrame "HP1".
      iExists _,_,∅. rewrite /StrongTok. iFrame "St'' tok'' R''".
      rewrite /StrMoves /StrDowns. iFrame "SM'' SeenM' oW'' SD''".
      iDestruct "WR" as (??) "WR". iExists _, _. by iFrame "WR".
    - subst b.
      iDestruct "Rs" as "(St & SMA & SM)". rewrite 3!acq_embed_elim.
      iDestruct (GPS_SWSharedReaders_join with "SR2 R'") as "SR". rewrite Qp.div_2.
      (* closing *)
      iSpecialize ("Hclose1" with "tok [SMA MDU IW IS]").
      { iDestruct "MDU" as "[SDA WUA]".
        iApply (arc_inv_join with "[SMA] SDA WUA IS IW"). by iExists _. }
      iMod (fupd_mask_mono with "Hclose1") as "[tok Hclose1]"; [set_solver|].

      iMod ("Hclose2" $! ∅ ∅ with "[St] tok [SR] [SM] [] [SD] [] oW") as "HP";
        [by iExact "St"|by iExists _| |done|by rewrite right_id_L|done|].
      { by rewrite right_id_L /StrMoves. }
      iModIntro. iMod "Hclose1" as "_". iModIntro.
      wp_case. iApply ("IH" with "HP HΦ").
  Qed.

  Lemma arc_weak_interp_comparable l γi γs γw γsw t s v (n: Z):
    weak_interp P2 l γi γs γsw true (l >> 1) γw t s v
    ∨ weak_interp P2 l γi γs γsw false (l >> 1) γw t s v
      -∗ ⌜∃ vl : lit, v = #vl ∧ lit_comparable n vl⌝.
  Proof.
    iIntros "[F|F]"; iDestruct "F" as (st ?) "_"; subst v;
    iExists _; iPureIntro; (split; [done|]); by constructor.
  Qed.

  Lemma arc_weak_interp_comparable_2 l γi γs γw γsw t s v (n: Z):
    weak_interp P2 l γi γs γsw true (l >> 1) γw t s v
    ∨ weak_interp P2 l γi γs γsw false (l >> 1) γw t s v
    ∨ weak_noCAS γsw (l >> 1) γw t s v
      -∗ ⌜∃ vl : lit, v = #vl ∧ lit_comparable n vl⌝.
  Proof.
    iIntros "[F|[F|[% ?]]]";
    last (subst; iPureIntro; eexists; split; [done|by constructor]);
    iDestruct "F" as (st ?) "_"; subst;
    iExists _; iPureIntro; (split; [done|]); by constructor.
  Qed.

  Lemma downgrade_spec γi γs γw γsw l t v ts (P : vProp) tid:
    is_arc P1 P2 N γi γs γw γsw l -∗ strong_arc_acc l ts γi γs γw γsw P (⊤ ∖ ↑N) -∗
    GPS_Reader (l >> 1) t () v γw -∗
    {{{ P }}} downgrade [ #l] @ tid; ⊤
    {{{ t' q', RET #☠; P ∗ weak_arc t' q' l γi γs γw γsw }}}.
  Proof.
    iIntros "#INV #Hacc #WR !# * HP HΦ". iLöb as "IH". wp_rec. wp_op.
    (* read the value *)
    wp_bind (!ʳˡˣ_)%E.
    (* opening invariant *)
    iMod (view_inv_acc_base_1 γi N with "INV") as "VI"; [done|].
    iMod (strong_arc_acc_open_no_change with "HP Hacc")
      as (Vs q Mt Dt) "[(St & tok & SR & SM & SD & oW) Hclose2]".
    iSpecialize ("VI" $! Vs with "tok").
    iMod (fupd_mask_mono with "VI") as "[tok VI]"; [set_solver|].
    iDestruct "VI" as (Vb) "[VI Hclose1]".
    iMod (arc_inv_split with "VI") as "(MA & IS & IW)".

    set R : time → unitProtocol → val → vProp :=
      (λ t' _ v', ∃ z : Z, ⌜v' = #z ∧ -1 ≤ z⌝)%I.
    iApply (GPS_SWRaw_Read (weak_interp P2 l γi γs γsw) _
              (weak_noCAS γsw) R with "[$WR $IW]"); [done|by left|..].
    { iIntros "!>" (t' [] v' [_ Ext']) "!>". iSplit; last iSplit.
      - iIntros "#WI !>". iFrame "WI". iDestruct "WI" as (st) "[Eq1 _]".
        iDestruct "Eq1" as %?. subst v'.
        iPureIntro. eexists. split; [done|]. by apply weak_stUR_value.
      - iDestruct 1 as (st) "[Eq1 WI]". iDestruct "Eq1" as %?. subst v'.
        iModIntro. iSplitR ""; [iExists _; by iFrame "WI"|].
        iPureIntro. eexists. split; [done|]. by apply weak_stUR_value.
      - iIntros "[% F]". subst v'. iModIntro. iFrame "F". iSplitL""; [done|].
        iPureIntro. by eexists.  }
    iIntros "!>" (t' [] v'). iDestruct 1 as "(_ & _ & IW & Rs)".
    iDestruct "Rs" as (z) "[% %Le1]". subst v'.

    (* closing invariant *)
    iSpecialize ("Hclose1" with "tok [MA IW IS]").
    { iDestruct "MA" as "[SMA [SDA WUA]]".
      by iApply (arc_inv_join with "SMA SDA WUA IS IW"). }
    iMod (fupd_mask_mono with "Hclose1") as "[tok Hclose1]"; [set_solver|].
    iMod ("Hclose2" with "St tok SR SM SD oW") as "HP".
    iModIntro. iMod "Hclose1" as "_".
    clear R t' Mt Dt Vb q Vs.

    iModIntro. wp_let. wp_op.
    case (decide (z = -1)) => Eq; [subst z|rewrite (bool_decide_false _ Eq)];
    wp_if; first by iApply ("IH" with "HP HΦ").
    wp_op. wp_op. wp_bind (CAS _ _ _ _ _ _).
    (* preparing to CAS *)
    (* opening invariant *)
    iMod (view_inv_acc_base_1 γi N with "INV") as "VI"; [done|].
    iMod (strong_arc_acc_open with "HP Hacc")
      as (Vs q Mt Dt) "[(St & tok & SR & SM & SD & oW) Hclose2]".
    iSpecialize ("VI" $! Vs with "tok").
    iMod (fupd_mask_mono with "VI") as "[tok VI]"; [set_solver|].
    iDestruct "VI" as (Vb) "[VI Hclose1]".
    iMod (arc_inv_split with "VI") as "((SMA & SDA & WUA) & IS & IW)".
    iDestruct "SDA" as (DtA) "SDA".

    set Q: time → unitProtocol → vProp :=
      (λ t'' s'',
        let Dt' := if decide (Z.to_pos z = 1%positive) then  {[t'']} else ∅ in
        StrongDownAuth γsw (DtA ∪ Dt') ∗ StrDowns γsw q (Dt ∪ Dt') ∗
        agown γsw (awk_n ((Some q, ε))) ∗
        ∃ q'', WeakTok γsw q'' ∗
                WkResources (l >> 1) l t'' #(z+1) γi γw γs γsw q'' ∅)%I.
    set Q1: time → unitProtocol → vProp := (λ _ _, True)%I.
    set Q2: time → unitProtocol → vProp :=
      (λ tr sr, weak_interp P2 l γi γs γsw true (l >> 1) γw tr sr #z).
    set R: time → unitProtocol → lit → vProp :=
      (λ _ _ _, StrongDownAuth γsw DtA ∗ StrDowns γsw q Dt ∗
                agown γsw (awk_n ((Some q, ε))))%I.
    iMod (rel_True_intro tid) as "#rTrue".
    (* here comes the CAS *)
    iApply (GPS_SWRaw_SharedWriter_CAS_int_weak (weak_interp P2 l γi γs γsw) _
            (weak_noCAS γsw) _ _ _ z #(z+1) _ _ _ _ True%I Q Q1 Q2 R _ Vb
            _ (↑histN) with "[$WR $IW SDA SD oW rTrue]");
      [done|done|by left|by right|by left|..].
    { simpl. iFrame "rTrue". iSplitL "".
      { iIntros "!>!>" (??? _). by iApply arc_weak_interp_comparable_2. }
      rewrite /= -(bi.True_sep' (∀ _ (_ : unitProtocol), _)%I).
      iApply (rel_sep_objectively with "[$rTrue SDA SD oW]"). rewrite /StrDowns.
      iIntros "!>" (t' [] [_ Ext']). iSplit; last first.
      { iIntros (??) "!> !>". iSplit; last iSplit;
          iIntros "$ !>"; iFrame "SDA oW"; by rewrite /StrDowns. }
      iSplitL "". { iIntros "_ [>%Eq1 ?]". by inversion Eq1. }
      iSplitL "". { by iIntros "!> $". } iIntros "_".
      iDestruct 1 as ([iS st]) "[>Eq [>WA WI]]".
      iDestruct "Eq" as %Eq'. inversion Eq'. subst z. clear Eq'.
      iDestruct (WeakAuth_strong with "[$WA $oW]") as %[qs ?]. subst iS.
      destruct st as [[[q' n]| | ]|]; [|done|done|].
      - iDestruct "WI" as "(>Eq & $ & WI)". iDestruct "Eq" as %?. subst qs.
        iDestruct "WI" as (q'' Ut') "(>Eq'' & [tok1 tok2] & R & WU & #SeenU)".
        iDestruct "Eq''" as %Eq''.
        iModIntro. iExists (). iSplitL""; [done|]. iIntros (t'' Lt'') "W'".
        iModIntro. iSplitL "".
        { iIntros "!> _ !> !>". iExists (Some 1%Qp, Some $ Cinl (q', n)).
          iSplit; [done|]. iSplit; [|done]. iPureIntro. simpl. lia. } iIntros "!> !>".
        iMod (WeakAuth_new_tok _ _ q' q'' _ Eq'' with "WA") as "[WA St']".
        iAssert (WkUps γsw (q'' / 2) Ut' ∗ WkUps γsw (q'' / 2) ∅)%I
          with "[WU]" as "[WU1 WU2]".
        { rewrite -(right_id_L ∅ union Ut') -{1}(Qp.div_2 q'').
          by iApply (WkUps_forget with "WU"). }
        iDestruct (GPS_SWSharedWriter_Reader_update with "W' R") as "[W' [R1 R2]]".
        iModIntro. iSplitR "WA W' tok1 R1 WU1 SeenU".
        + rewrite /Q Pos2Z.id decide_False; last by lia. rewrite !right_id_L.
          rewrite /StrDowns. iFrame "SDA SD oW".
          iExists (q''/2)%Qp. iFrame "St' tok2 R2 WU2".
          iDestruct "SeenU" as (t4 v4) "[Rs _]". iExists _, _. by iFrame "Rs".
        + iExists (Some 1%Qp, Some $ Cinl ((q' + q'' / 2)%Qp, (n + 1)%positive)).
          iSplitL ""; [done|]. iFrame "WA W'". iSplit; [done|].
          iExists (q''/2)%Qp, Ut'. iFrame "tok1 R1 WU1 SeenU".
          iPureIntro. by rewrite -Qp.add_assoc Qp.div_2.
      - iDestruct "WI" as "(>Eq & $ & WI)". iDestruct "Eq" as %?. subst qs.
        iDestruct "WI" as (Ut') "([tok1 tok2] & R & WU & #SeenU)".
        iModIntro. iExists (). iSplitL""; [done|]. iIntros (t'' Lt'') "W'".
        iMod (StrDowns_update _ DtA Dt {[t'']} q with "[$SDA SD]")
          as "(SDA & SD & Cert)"; [by rewrite /StrDowns|].
        iModIntro. iSplitL "Cert".
        { iIntros "!> _ !> !>". iExists (Some 1%Qp, None). do 2 (iSplit; [done|]).
          iExists t''. by iFrame (Lt'') "Cert". } iIntros "!> !>".
        iMod (WeakAuth_first_tok with "WA") as "[WA Wt']".
        iAssert (WkUps γsw (1 / 2) Ut' ∗ WkUps γsw (1 / 2) ∅)%I
          with "[WU]" as "[WU1 WU2]".
        { rewrite -(right_id_L ∅ union Ut') -{1}(Qp.div_2 1).
          by iApply (WkUps_forget with "WU"). }
        iDestruct (GPS_SWSharedWriter_Reader_update with "W' R") as "[W' [R1 R2]]".
        iModIntro. iSplitR "WA W' tok1 R1 WU1 SeenU".
        + rewrite /Q Pos2Z.id /=. iFrame "SDA SD oW".
          iExists (1/2)%Qp. iFrame "Wt' tok2 R2 WU2".
          iDestruct "SeenU" as (t4 v4) "[Rs _]". iExists _, _. by iFrame "Rs".
        + iExists (Some 1%Qp, Some $ Cinl ((1/2)%Qp, 1%positive)).
          iSplitL ""; [done|]. iFrame "WA W'". iSplitL""; [done|].
          iExists (1/2)%Qp, Ut'. iSplitL ""; [iPureIntro; by rewrite Qp.div_2|].
          iFrame "tok1 R1 WU1 SeenU". }
    iIntros "!>" (b t' [] v') "(IW &%& [([%[%%]]&R'&Q) | ([%[_ %]] &_&Rs&_)])".
    - subst b v'.
      iDestruct "Q" as "(SDA & SD & oW & WI)".
      iDestruct "WI" as (q'') "[Wt' WRs]".
      set Dt' := if decide (Z.to_pos z = 1%positive) then {[t']} else ∅.
      iAssert (SeenActs γw (l >> 1) Dt')%I with "[R']" as "#SeenD'".
      { iExists _, _. iFrame "R'". iPureIntro. rewrite /Dt'.
        case decide => ?; [|done]. move => ? /elem_of_singleton -> //. }

      (* closing *)
      iSpecialize ("Hclose1" with "tok [SMA SDA WUA IW IS]").
      { iApply (arc_inv_join with "SMA [SDA] WUA IS IW"). by iExists _. }
      iMod (fupd_mask_mono with "Hclose1") as "[tok Hclose1]"; [set_solver|].

      iMod ("Hclose2" $! ∅ Dt' with "St tok SR [SM] [] SD [] oW") as "HP";
        [by rewrite right_id_L|done|..].
      { rewrite /Dt'. by case_decide. }
      iModIntro. iMod "Hclose1" as "_". iModIntro.
      wp_case. iApply ("HΦ" with "[- $HP]").
      iExists _, ∅. iFrame "Wt' WRs".
    - subst b.
      iDestruct "Rs" as "(SDA & SD & oW)". rewrite 3!acq_embed_elim.
      (* closing *)
      iSpecialize ("Hclose1" with "tok [SMA SDA WUA IW IS]").
      { iApply (arc_inv_join with "SMA [SDA] WUA IS IW"). by iExists _. }
      iMod (fupd_mask_mono with "Hclose1") as "[tok Hclose1]"; [set_solver|].

      iMod ("Hclose2" $! ∅ ∅ with "St tok SR [SM] [] [SD] [] oW") as "HP";
        [by rewrite right_id_L|done|by rewrite right_id_L /StrDowns|done|].
      iModIntro. iMod "Hclose1" as "_". iModIntro.
      wp_case. iApply ("IH" with "HP HΦ").
  Qed.

  Lemma clone_weak_spec γi γs γw γsw l t v (P : vProp) tid :
    is_arc P1 P2 N γi γs γw γsw l -∗ weak_arc_acc l t γi γs γw γsw P (⊤ ∖ ↑N) -∗
    (∃ t' v', GPS_Reader l t' () v' γs) -∗
    GPS_Reader (l >> 1) t () v γw -∗
    {{{ P }}} clone_weak [ #l] @ tid; ⊤
    {{{ t' q', RET #☠; P ∗ weak_arc t' q' l γi γs γw γsw }}}.
  Proof.
    iIntros "#INV #Hacc #SR #WR !# * HP HΦ". iLöb as "IH". wp_rec. wp_op.
    (* read the value *)
    wp_bind (!ʳˡˣ_)%E.
    (* opening invariant *)
    iMod (view_inv_acc_base_1 γi N with "INV") as "VI"; [done|].
    iMod (weak_arc_acc_open_no_change with "HP Hacc")
      as (Vs q Ut) "[(Wt & tok & WRq & WU) Hclose2]".
    iSpecialize ("VI" $! Vs with "tok").
    iMod (fupd_mask_mono with "VI") as "[tok VI]"; [set_solver|].
    iDestruct "VI" as (Vb) "[VI Hclose1]".
    iMod (arc_inv_split with "VI") as "(MA & IS & IW)".

    set R : time → unitProtocol → val → vProp := (λ t' _ v', ∃ z : Z, ⌜v' = #z⌝)%I.
    iApply (GPS_SWRaw_Read (weak_interp P2 l γi γs γsw) _
              (weak_noCAS γsw) R with "[$WR $IW]"); [done|by left|..].
    { iIntros "!>" (t' [] v' [_ Ext']) "!>". iSplit; last iSplit.
      - iIntros "#WI !>". iFrame "WI". iDestruct "WI" as (st) "[Eq1 _]".
        iDestruct "Eq1" as %?. subst v'. by iExists _.
      - iDestruct 1 as (st) "[Eq1 WI]". iDestruct "Eq1" as %?. subst v'.
        iModIntro. iSplitR ""; [iExists _; by iFrame "WI"|by iExists _].
      - iIntros "[% F]". subst v'. iModIntro. iFrame "F". iSplitL""; [done|].
        iPureIntro. by eexists. }
    iIntros "!>" (t' [] v'). iDestruct 1 as "(_ & _ & IW & Rs)".
    iDestruct "Rs" as (z) "%". subst v'.

    (* closing *)
    iSpecialize ("Hclose1" with "tok [MA IW IS]").
    { iDestruct "MA" as "(SMA & SDA & WUA)".
      by iApply (arc_inv_join with "SMA SDA WUA IS IW"). }
    iMod (fupd_mask_mono with "Hclose1") as "[tok Hclose1]"; [set_solver|].
    iMod ("Hclose2" with "Wt tok WRq WU") as "HP".
    iModIntro. iMod "Hclose1" as "_". iModIntro.
    wp_let. wp_op. clear R Ut t' Vb Vs q.

    (* now we can CAS *)
    wp_op. wp_bind (CAS _ _ _ _ _ _).
    (* opening invariant *)
    iMod (view_inv_acc_base_1 γi N with "INV") as "VI"; [done|].
    iMod (weak_arc_acc_open_no_change_2 with "HP Hacc")
      as (Vs q Ut) "[(Wt & tok & WRq & WU) Hclose2]".
    iSpecialize ("VI" $! Vs with "tok").
    iMod (fupd_mask_mono with "VI") as "[tok VI]"; [set_solver|].
    iDestruct "VI" as (Vb) "[VI Hclose1]".
    iMod (arc_inv_split with "VI") as "((SMA & SDA & WUA) & IS & IW)".
    iDestruct "SDA" as (Dt) "SDA". iDestruct "WRq" as (v0) "WRq".
    iDestruct (GPS_SWSharedReader_Reader_join_subjectively _ _ _ _ _ _  q
        with "WR [WRq]") as "[WR1 WR2]".
    { rewrite monPred_subjectively_unfold.
      iDestruct (monPred_in_view_elim with "WRq") as (V') "?". by iExists V'. }

    set Q: time → unitProtocol → vProp :=
      (λ t'' s'',
        let Dt' := (if decide (Z.to_pos z = 1%positive) then {[t'']} else ∅) in
        StrongDownAuth γsw (Dt ∪ Dt') ∗ WeakTok γsw q ∗
        ∃ q'', WeakTok γsw q'' ∗
          (<obj> view_tok γi (q''/2)) ∗
          GPS_SWSharedReader (l >> 1) t'' ((): unitProtocol) #(z+1) q'' γw ∗
          WkUps γsw q'' ∅)%I.
    set Q1: time → unitProtocol → vProp := (λ _ _, True)%I.
    set Q2: time → unitProtocol → vProp :=
      (λ tr sr, weak_interp P2 l γi γs γsw true (l >> 1) γw tr sr #z).
    set R: time → unitProtocol → lit → vProp :=
      (λ _ _ _, WeakTok γsw q ∗ StrongDownAuth γsw Dt)%I.
    iMod (rel_True_intro tid) as "#rTrue".
    (* here comes the CAS *)
    iApply (GPS_SWRaw_SharedWriter_CAS_int_strong (weak_interp P2 l γi γs γsw) _
            (weak_noCAS γsw) false Relaxed Relaxed Relaxed z #(z+1) _ _ _ _ _
            True%I Q Q1 Q2 R _ Vb _ (↑histN) with "[$WR1 $IW Wt SDA $rTrue]");
      [done|done|by left|by left|by left|..].
    { iSplitL "". { iIntros "!>!>" (??? _). by iApply arc_weak_interp_comparable. }
      rewrite /= -(bi.True_sep' (∀ _ (_ : unitProtocol), _)%I).
      iApply (rel_sep_objectively with "[$rTrue Wt SDA]").
      rewrite /WeakTok. iIntros "!>" (t' [] [_ Ext']). iSplit; last first.
      { iIntros (??) "!> !>". iSplit; iIntros "$ !>";
          iFrame "SDA"; by rewrite /WeakTok. }
      iSplitL "". { by iIntros "!> $". } iIntros "_".
      iDestruct 1 as (st) "[>Eq [>WA WI]]".
      iDestruct (WeakTok_Auth_agree with "[$WA Wt]") as %(q'&n&iS&EQ&Eq');
        [by rewrite /WeakTok|]. subst st. iDestruct "Eq" as %Eq.
      inversion Eq. subst z. clear Eq. destruct iS as [iS|].
      - iDestruct "WI" as "(>iSI & $ & WI)". iDestruct "iSI" as %iSI.
        iDestruct "WI" as (q'' Ut') "(>Eq'' & tok & R & WU & SeenU)".
        iDestruct "Eq''" as %Eq''.
        iModIntro. iExists (). iSplitL""; [done|]. iIntros (t'' Lt'') "W' _".
        iModIntro. iSplitL "".
        { iIntros "!> _ !> !>". by iExists (Some iS, Some $ Cinl (q', n)). }
        iIntros "!> !>".
        iMod (WeakAuth_new_tok _ _ q' q'' _ Eq'' with "WA") as "[WA St']".
        iAssert (WkUps γsw (q'' / 2) Ut' ∗ WkUps γsw (q'' / 2) ∅)%I
          with "[WU]" as "[WU1 WU2]".
        { rewrite -(right_id_L ∅ union Ut') -{1}(Qp.div_2 q'').
          by iApply (WkUps_forget with "WU"). }
        iDestruct (GPS_SWSharedWriter_Reader_update with "W' R") as "[W' [R1 R2]]".
        iDestruct (view_tok_split_unit γi (q''/2/2) (q''/2/2) with "[tok]")
          as "[tok1 tok2]"; first by rewrite Qp.div_2.
        iModIntro. iSplitR "WA W' tok1 R1 WU1 SeenU".
        + rewrite /Q Pos2Z.id decide_False; last by lia. rewrite /WeakTok right_id_L.
          iFrame "Wt SDA". iExists _. iFrame "St' tok2 R2 WU2".
        + iExists (Some iS, Some $ Cinl ((q' + q'' / 2)%Qp, (n + 1)%positive)).
          iSplitL ""; [done|]. iFrame (iSI) "WA W'". iExists (q''/2)%Qp, Ut'.
          iFrame "tok1 R1 WU1 SeenU". iPureIntro. by rewrite -Qp.add_assoc Qp.div_2.
      - iDestruct "WI" as "($ & WI & HP2 & tokM & SW & SM & SD)".
        iDestruct "WI" as (q'' Ut') "(>Eq'' & tok & R & WU & #SeenU)".
        iDestruct "Eq''" as %Eq''. rewrite /StrDowns. iDestruct "SD" as (Dt') ">SD".
        iDestruct (StrongDownAuth_agree with "[$SDA SD]") as %?;
          [by rewrite /StrDowns|subst Dt'].
        iModIntro. iExists (). iSplitL""; [done|]. iIntros (t'' Lt'') "W' _".
        set Dt' : gset time := if decide (n = 1%positive) then {[t'']} else ∅.
        iAssert (|==> StrongDownAuth γsw (Dt ∪ Dt') ∗
                      StrDowns γsw 1%Qp (Dt ∪ Dt') ∗
                      <obj> if decide (n = 1%positive)
                            then StrDownCert γsw t'' else True)%I
                with "[SDA SD]" as ">(SDA & SD & Cert)".
        { rewrite /Dt'. case decide => ?; last first.
          { rewrite right_id_L /StrDowns. iFrame. by iIntros "!> !>". }
          iMod (StrDowns_update _ _ _ {[t'']} with "[$SDA SD]") as "($ & $ & Cert)".
          - by rewrite /StrDowns. - iIntros "!> !>". by iFrame "Cert". }
        iModIntro. iSplitL "Cert".
        { iIntros "!> _ !> !>". iExists (None, Some $ Cinl (q', n)).
          do 2 (iSplit; [done|]). destruct n; simpl; [done..|].
          iExists t''. by iDestruct (monPred_objectively_elim with "Cert") as "$". }
        iIntros "!> !>".
        iDestruct (GPS_SWSharedWriter_Reader_update with "W' R") as "[W' [R1 R2]]".
        iMod (WeakAuth_new_tok _ _ q' q'' _ Eq'' with "WA") as "[WA Wt']".
        iAssert (WkUps γsw (q'' / 2) Ut' ∗ WkUps γsw (q'' / 2) ∅)%I
          with "[WU]" as "[WU1 WU2]".
        { rewrite -(right_id_L ∅ union Ut') -{1}(Qp.div_2 q'').
          by iApply (WkUps_forget with "WU"). }
        iDestruct (view_tok_split_unit γi (q''/2/2) (q''/2/2) with "[tok]")
          as "[tok1 tok2]"; first by rewrite Qp.div_2.
        iModIntro. iSplitR "WA W' tok1 R1 WU1 HP2 tokM SW SM SD".
        + rewrite /Q Pos2Z.id /WeakTok. iFrame "SDA Wt".
          iFrame "Wt' tok2 R2 WU2".
        + iIntros "!>".
          iExists (None, Some $ Cinl ((q' + q'' / 2)%Qp, (n + 1)%positive)).
          iSplitL ""; [done|]. iFrame "WA W' HP2 SW SM".
          iSplitR "SD tokM"; [|iFrame].
          iExists (q'' / 2)%Qp, Ut'. iFrame "tok1 R1 WU1 SeenU".
          iPureIntro. by rewrite -Qp.add_assoc Qp.div_2. }

    (* finally done with the CAS *)
    iIntros "!>" (b t' [] v') "(IW &%& [([%[%%]]&R'&Q) | ([%[_ %]] &R'&Rs&_)])".
    - subst b v'.
      iDestruct "Q" as "(SDA & Wt & Q)". iDestruct "Q" as (q'') "Q".
      iDestruct "Q" as "(Wt'' & tok'' & R'' & WU'')".
      (* tedious removal of acq_mod *)
      rewrite 4!acq_embed_elim acq_objectively_elim monPred_objectively_elim.
      iDestruct (GPS_SWSharedReaders_join_subjectively _ _ _ _ _ _ _ _ q''
                  with "R' [R'']") as "[R' R'']". { by iApply acq_subjective. }
      iDestruct (GPS_SWSharedReader_Reader with "R'") as "#RR".
      iDestruct (GPS_SWSharedReaders_join with "WR2 R'") as "WRq". rewrite Qp.div_2.

      (* closing *)
      iSpecialize ("Hclose1" with "tok [SMA SDA WUA IW IS]").
      { iApply (arc_inv_join with "SMA [SDA] WUA IS IW"). by iExists _. }
      iMod (fupd_mask_mono with "Hclose1") as "[tok Hclose1]"; [set_solver|].
      iMod ("Hclose2" with "[Wt] tok [WRq] WU") as "HP";
        [by iExact "Wt"|by iExists _|].
      iModIntro. iMod "Hclose1" as "_". iModIntro.

      wp_case. iApply ("HΦ" with "[- $HP]"). iExists _, ∅.
      rewrite /WeakTok. iFrame "Wt'' tok'' R''". rewrite /WkUps.
      iFrame "WU''". iDestruct "SR" as (??) "SR". iExists _, _. by iFrame "SR".
    - subst b.
      iDestruct "Rs" as "(Wt & SDA)". rewrite 2!acq_embed_elim.
      iDestruct (GPS_SWSharedReaders_join with "WR2 R'") as "WRq".
      rewrite Qp.div_2.

      (* closing *)
      iSpecialize ("Hclose1" with "tok [SMA SDA WUA IW IS]").
      { iApply (arc_inv_join with "SMA [SDA] WUA IS IW"). by iExists _. }
      iMod (fupd_mask_mono with "Hclose1") as "[tok Hclose1]"; [set_solver|].
      iMod ("Hclose2" with "[Wt] tok [WRq] WU") as "HP";
        [by iExact "Wt"|by iExists _|].
      iModIntro. iMod "Hclose1" as "_". iModIntro.
      wp_case. iApply ("IH" with "HP HΦ").
  Qed.

  Lemma upgrade_spec {HPn: HP1} γi γs γw γsw l t v tw (P : vProp) tid :
    is_arc P1 P2 N γi γs γw γsw l -∗ weak_arc_acc l tw γi γs γw γsw P (⊤ ∖ ↑N) -∗
    (∃ t' v', GPS_Reader (l >> 1) t' () v' γw) -∗
    GPS_Reader l t () v γs -∗
    {{{ P }}} upgrade [ #l] @ tid; ⊤
    {{{ (b : bool) q, RET #b;
        P ∗ if b then ∃ ts, strong_arc ts q l γi γs γw γsw ∗ P1 q else True }}}.
  Proof.
    iIntros "#INV #Hacc #WRR #RR !# * HP HΦ". iLöb as "IH". wp_rec.
    (* read the value *)
    wp_bind (!ʳˡˣ_)%E.
    (* opening invariant *)
    iMod (view_inv_acc_base_1 γi N with "INV") as "VI"; [done|].
    iMod (weak_arc_acc_open_no_change with "HP Hacc")
      as (Vs q Ut) "[(Wt & tok & WRq & WU) Hclose2]".
    iSpecialize ("VI" $! Vs with "tok").
    iMod (fupd_mask_mono with "VI") as "[tok VI]"; [set_solver|].
    iDestruct "VI" as (Vb) "[VI Hclose1]".
    iMod (arc_inv_split with "VI") as "(MA & IS & IW)".

    set R : time → unitProtocol → val → vProp := (λ t' _ v', ∃ z : Z, ⌜v' = #z⌝)%I.
    iApply (GPS_SWRaw_Read (strong_interp P1 (l >> 1) γi γw γsw) _
              strong_noCAS R with "[$RR $IS]"); [done|by left|..].
    { iIntros "!>" (t' [] v' [_ Ext']) "!>". iSplit; last iSplit.
      - iIntros "#SI !>". iFrame "SI". iDestruct "SI" as (st) "[Eq1 _]".
        iDestruct "Eq1" as %?. subst v'. by iExists _.
      - iDestruct 1 as (st) "[Eq1 SI]". iDestruct "Eq1" as %?. subst v'.
        iModIntro. iSplitR ""; [iExists _; by iFrame "SI"|by iExists _].
      - iIntros "% !>". subst v'. iSplit; [done|]. by iExists _. }
    iIntros "!>" (t' [] v'). iDestruct 1 as "(_ &_& IS & Rs)".
    iDestruct "Rs" as (z) "%". subst v'.

    (* closing *)
    iSpecialize ("Hclose1" with "tok [MA IW IS]").
    { iDestruct "MA" as "(SMA & SDA & WUA)".
      by iApply (arc_inv_join with "SMA SDA WUA IS IW"). }
    iMod (fupd_mask_mono with "Hclose1") as "[tok Hclose1]"; [set_solver|].
    iMod ("Hclose2" with "Wt tok WRq WU") as "HP".
    iModIntro. iMod "Hclose1" as "_". iModIntro.
    wp_let. wp_op. clear R Ut t' Vb Vs q.

    case (decide (z = 0)) => NEq0; [subst z|rewrite (bool_decide_false _ NEq0)];
    wp_if; first by iApply ("HΦ" $! _ 1%Qp with "[$HP]").
    wp_op. wp_bind (CAS _ _ _ _ _ _).
    (* preparing to CAS *)
    (* opening invariant *)
    iMod (view_inv_acc_base_1 γi N with "INV") as "VI"; [done|].
    iMod (weak_arc_acc_open with "HP Hacc")
      as (Vs q Ut) "[(Wt & tok & WRq & WU) Hclose2]".
    iSpecialize ("VI" $! Vs with "tok").
    iMod (fupd_mask_mono with "VI") as "[tok VI]"; [set_solver|].
    iDestruct "VI" as (Vb) "[VI Hclose1]".
    iMod (arc_inv_split with "VI") as "((SMA & SDA & WUA) & IS & IW)".
    iDestruct "WUA" as (UtA) "WUA".

    set Q: time → unitProtocol → vProp :=
      (λ t'' s'',
        let Ut' := if decide (Z.to_pos z = 1%positive) then  {[t'']} else ∅ in
        WeakUpAuth γsw (UtA ∪ Ut') ∗ WkUps γsw q (Ut ∪ Ut') ∗
        ∃ q'' Mt'', StrongTok γsw q'' ∗ (<obj> P1 q'') ∗
          (<obj> view_tok γi (q''/2)) ∗
          GPS_SWSharedReader l t'' ((): unitProtocol) #(z+1) q'' γs ∗
          StrMoves γsw q'' Mt'' ∗ ⌜∀ t' : time, t' ∈ Mt'' → t' ⊑ t''⌝ ∗
          StrDowns γsw q'' ∅ ∗ StrWkTok γsw q'')%I.
    set Q1: time → unitProtocol → vProp := (λ _ _, True)%I.
    set Q2: time → unitProtocol → vProp :=
      (λ tr sr, strong_interp P1 (l >> 1) γi γw γsw true l γs tr sr #z).
    set R: time → unitProtocol → lit → vProp :=
      (λ _ _ _, WeakUpAuth γsw UtA ∗ WkUps γsw q Ut)%I.
    iMod (rel_True_intro tid) as "#rTrue".
    (* here comes the CAS *)
    iApply (GPS_SWRaw_SharedWriter_CAS_int_weak (strong_interp P1 (l >> 1) γi γw γsw) _
            strong_noCAS Relaxed Relaxed Relaxed z #(z+1) _ _ _ _
            True%I Q Q1 Q2 R _ Vb _ (↑histN) with "[$RR $IS WUA WU $rTrue]");
      [done|done|by left|by left|by left|..].
    { iSplitL "". { iIntros "!>!>" (??? _). by iApply arc_strong_interp_comparable_2. }
      rewrite /= -(bi.True_sep' (∀ _ (_ : unitProtocol), _)%I).
      iApply (rel_sep_objectively with "[$rTrue WUA WU]"). rewrite /WkUps.
      iIntros "!>" (t' [] [_ Ext']). iSplit; last first.
      { iIntros (??) "!> !>". iSplit; last iSplit; iIntros "$ !>";
                                iFrame "WUA"; by rewrite /WkUps. } iSplitL "".
      { iIntros "_ >%Eq". by inversion Eq. }
      iSplitL "". { by iIntros "!> $". } iIntros "_".
      iDestruct 1 as (st) "[>Eq [>SA SI]]". iDestruct "Eq" as %Eq.
      inversion Eq. subst z. clear Eq. destruct st as [[q' n]|]; [|done].
      iDestruct "SI" as "[$ SI]".
      iDestruct "SI" as (q'') "(>Eq'' & HP & SI)". iDestruct "Eq''" as %Eq''.
      iAssert (▷ (P1 (q''/2) ∗ <obj> P1 (q''/2)))%I with "[HP]" as "[HP1 HP2]".
      { iNext. iApply HPn. by rewrite Qp.div_2. }
      iModIntro. iExists (). iSplitL""; [done|]. iIntros (t'' Lt'') "W'".
      set Ut' : gset time := if decide (n = 1%positive) then {[t'']} else ∅.
      iMod (WkUps_update _ UtA Ut Ut' q with "[$WUA WU]")
          as "(WUA & WU & Cert)"; [by rewrite /WkUps|].
      iModIntro. iSplitL "Cert".
      { iIntros "!> _ !> !>". iExists (Some (q',n)). iSplit; [done|].
        destruct n; [done..|]. iExists t''. iFrame (Lt'') "Cert". }
      iIntros "!> !>".
      iMod (StrongAuth_new_tok _ q' q'' n Eq'' with "SA") as "[SA St']".
      iDestruct "SI" as (Mt' Dt')
        "(tok & SR & [SM1 SM2] & #SeenM & SD & #SeenD & [oW1 oW2])".
      iDestruct (GPS_SWSharedWriter_Reader_update with "W' SR") as "[W' [SR1 SR2]]".
      iAssert (StrDowns γsw (q'' / 2) Dt' ∗ StrDowns γsw (q'' / 2) ∅)%I
          with "[SD]" as "[SD1 SD2]".
      { rewrite -(right_id_L ∅ union Dt') -{1}(Qp.div_2 q'').
        by iApply (StrDowns_forget with "SD"). }
      iDestruct "SeenM" as (t4 v4) "[SR4 MAX4]".
      iDestruct (GPS_SWSharedWriter_latest_time_1 with "W' SR4") as %Ext4.
      iDestruct (view_tok_split_unit γi (q''/2/2) (q''/2/2) with "[tok]")
        as "[tok1 tok2]"; first by rewrite Qp.div_2.
      iModIntro. iSplitR "tok1 SM1 oW1 HP1 SA W' SR1 SD1".
      - rewrite /Q /=. iFrame "WUA WU".
        iExists (q''/2)%Qp, Mt'. iFrame "St' HP2 tok2 SR2 SM2 SD2 oW2".
        iDestruct "MAX4" as %MAX. iPureIntro. move => ? /MAX ->. by rewrite Ext4.
      - iExists (Some ((q' + q'' / 2)%Qp, (n + 1)%positive)).
        iSplitL ""; [done|]. iFrame "SA W'". iExists (q''/2)%Qp.
        iSplitL ""; [by rewrite -Qp.add_assoc Qp.div_2|].
        iFrame "HP1". iExists Mt', Dt'. iFrame "tok1 SR1 SM1 SD1 SeenD oW1".
        iExists _,_. by iFrame "SR4 MAX4". }

    (* finally done with the CAS *)
    iIntros "!>" (b t' [] v') "(IS &%& [([%[%%]]&#R'&Q) | ([%[_ %]] &R'&Rs&_)])".
    - subst b v'.
      iDestruct "Q" as "(WUA & WU & Q)".
      iDestruct "Q" as (q'' Mt'') "(St'' & HP1 & tok'' & R'' & SM'' & %MAX'' & SD'' & oW'')".
      (* tedious removal of acq_mod *)
      rewrite 6!acq_embed_elim 2!acq_objectively_elim.
      iDestruct (GPS_SWSharedReader_Reader_join_subjectively with "R' [R'']") as "R''".
      { by iApply acq_subjective. }
      set Ut' := if decide (Z.to_pos z = 1%positive) then {[t']} else ∅.
      iAssert (SeenActs γs l Ut')%I with "[]" as "#SeenU'".
      { iExists _, _. iFrame "R'". iPureIntro. rewrite /Ut'. case decide; [|done].
        move => ?? /elem_of_singleton => -> //. }
      iDestruct (GPS_SWSharedReader_Reader with "R''") as "#RR'".

      (* closing *)
      iSpecialize ("Hclose1" with "tok [SMA SDA WUA IW IS]").
      { iApply (arc_inv_join with "SMA SDA [WUA] IS IW"). by iExists _. }
      iMod (fupd_mask_mono with "Hclose1") as "[tok Hclose1]"; [set_solver|].
      iMod ("Hclose2" with "Wt tok WRq [WU] []") as "HP"; [by iExact "WU"|..].
      { rewrite /Ut'. by case_decide. }
      iModIntro. iMod "Hclose1" as "_". iModIntro.

      wp_case. iApply ("HΦ" with "[- $HP]").
      rewrite 2!monPred_objectively_elim. iFrame "HP1".
      iExists _,_,_, ∅. rewrite /StrongTok. iFrame "St'' tok'' R''".
      rewrite /StrMoves /StrDowns. iFrame "SM'' oW'' SD''".
      iDestruct "WRR" as (??) "WRR".
      iSplitL""; iExists _,_; [by iFrame (MAX'') "R'"|by iFrame "WRR"].
    - subst b.
      iDestruct "Rs" as "[WUA WU]". rewrite 2!acq_embed_elim.

      (* closing *)
      iSpecialize ("Hclose1" with "tok [SMA SDA WUA IW IS]").
      { iApply (arc_inv_join with "SMA SDA [WUA] IS IW"). by iExists _. }
      iMod (fupd_mask_mono with "Hclose1") as "[tok Hclose1]"; [set_solver|].
      iMod ("Hclose2" $! ∅ with "Wt tok WRq [WU] [//]") as "HP";
        [by rewrite right_id_L /WkUps|].
      iModIntro. iMod "Hclose1" as "_". iModIntro.

      wp_case. iApply ("IH" with "HP HΦ").
  Qed.

  Lemma drop_weak_spec γi γs γw γsw l q tid :
    histN ## N → is_arc P1 P2 N γi γs γw γsw l -∗
    {{{ (∃ tw, weak_arc tw q l γi γs γw γsw) }}} drop_weak [ #l] @ tid; ⊤
    {{{ (b : bool), RET #b ; if b then P2 ∗ l ↦ #0 ∗ (l >> 1) ↦ #0 else True }}}.
  Proof.
    iIntros (?) "#INV !# * HP HΦ". iLöb as "IH". wp_rec. wp_op.
    (* read the value *)
    wp_bind (!ʳˡˣ_)%E.
    iDestruct "HP" as (tw v Ut) "(Wt & tok & WR & WU & #SeenU)".
    (* opening invariant *)
    iMod (view_inv_acc_base γi N with "[$INV $tok]") as "[tok VI]"; [done|].
    iDestruct "VI" as (Vb) "[VI Hclose1]".
    iMod (arc_inv_split with "VI") as "(MA & IS & IW)".

    set R : time → unitProtocol → val → vProp := (λ t' _ v', ∃ z : Z, ⌜v' = #z⌝)%I.
    iApply (GPS_SWRaw_SharedReader_Read (weak_interp P2 l γi γs γsw) _
              (weak_noCAS γsw) R with "[$WR $IW]"); [solve_ndisj|by left|..].
    { iIntros "!>" (t' [] v' [_ Ext']) "!>". iSplit.
      - iIntros "#WI !>". iFrame "WI". iDestruct "WI" as (st) "[% _]".
        subst v'. by iExists _.
      - iDestruct 1 as (st) "[Eq1 WI]". iDestruct "Eq1" as %?. subst v'.
        iModIntro. iSplitR "". { iExists _. by iFrame "WI". } by iExists _. }
    iIntros "!>" (t' [] v'). iDestruct 1 as ([_ Ext']) "(WR & IW & Rs)".
    iDestruct "Rs" as (z) "%". subst v'.
    iMod ("Hclose1" with "tok [MA IW IS]") as "tok".
    { iDestruct "MA" as "(SMA & SDA & WUA)".
      by iApply (arc_inv_join with "SMA SDA WUA IS IW"). }
    clear Vb R. iModIntro. wp_let. wp_op. wp_op.

    wp_bind (CAS _ _ _ _ _ _).
    (* preparing to CAS *)
    iMod (view_inv_acc_base γi N with "[$INV $tok]") as "[tok VI]"; [done|].
    iDestruct "VI" as (Vb) "[VI Hclose1]".
    iMod (arc_inv_split with "VI") as "((SMA & SDA & WUA) & IS & IW)".

    set P : vProp :=
      (WeakTok γsw q ∗ WkUps γsw q Ut ∗ (∃ Dt, StrongDownAuth γsw Dt)
        ∗ if decide (z = 1) then True else view_tok γi (q / 2))%I.
    set P' : vProp :=
      (⊒Vb →
            ▷ GPS_INV (strong_interp P1 (l >> 1) γi γw γsw) l strong_noCAS γs)%I.
    set Q: time → unitProtocol → vProp :=
      (λ t'' _, (∃ Dt, StrongDownAuth γsw Dt) ∗
          if decide (Z.to_pos z = 1%positive)
          then GPS_SWSharedWriter (l >> 1) t'' ((): unitProtocol) #0 γw ∗
               GPS_SWSharedReader (l >> 1) t'' ((): unitProtocol) #0 1%Qp γw ∗
               (∃ q'', ⌜(q + q'')%Qp = 1%Qp⌝ ∗ view_tok γi (q''/2)) ∗
               (∃ Uts, WkUps γsw 1 Uts ∗ SeenActs γs l Uts) ∗
               P2 ∗ view_tok γi (1/2) ∗
               (∃ ts : time, GPS_SWWriter l ts ((): unitProtocol) #0 γs) ∗
               (∃ Mts, StrMoves γsw 1%Qp Mts) ∗
               (∃ Dts, StrDowns γsw 1 Dts)
          else True)%I.

    iAssert ((if decide (z = 1)
              then True else view_tok γi (q / 2)) ∗
              (if decide (z = 1)
              then view_tok γi (q / 2) else True))%I with "[tok]" as "[tok tokn]".
    { case decide => ?; by iFrame "tok". }

    (* here comes the CAS *)
    iApply (GPS_SWRaw_SharedWriter_CAS_int_view_strong (weak_interp P2 l γi γs γsw)
              _ (weak_noCAS γsw) true _ _ z #(z-1) _ _ _ _ _ P P' Q
              (λ _ _ _, True)%I _ Vb with "[$WR $IW $IS Wt WU SDA tok]");
      [solve_ndisj|by left|by left|..].
    { iSplitL "".  { iIntros "!>!>" (??? _). by iApply arc_weak_interp_comparable. }
      iSplitR "Wt WU SDA tok"; [|iSplitL""]; [..|by iFrame]; last first.
      { iIntros (????) "!> !>". by iSplit; iIntros "$". }
      iIntros (t1 [] [_ Ext1]) "!> (Wt & WU & SDA & tok)".
      iDestruct 1 as (st) "[Eq [WA WI]]".
      iDestruct (WeakTok_Auth_agree with "[$WA $Wt]") as %(q'&n&iS&EQ&Eq').
      subst st. iDestruct "Eq" as %Eq. inversion Eq. subst z. clear Eq.
      destruct iS as [iS|].
      - iDestruct "WI" as "(iSI & $ & WI)". iDestruct "iSI" as %?. subst iS.
        iDestruct "WI" as (q'' Ut') "(Eq'' & tok' & R & WU' & SeenU')".
        iDestruct "Eq''" as %Eq''.
        iModIntro. iExists (). iSplitL""; [done|]. iIntros (t'' Lt'') "W' R'".
        iModIntro. iSplitL "".
        { iIntros "!>". by iExists (Some 1%Qp, Some $ Cinl (q', n)). }
        iAssert (|==> if decide (n = 1%positive)
                      then WeakAuth γsw (Some 1%Qp, None)
                      else ∃ q'', ⌜q' = (q + q'')%Qp⌝ ∗
                           WeakAuth γsw (Some 1%Qp, Some (Cinl (q'', Pos.pred n))))%I
          with "[Wt WA]" as ">WA".
        { case decide => NEq.
          - subst n. simpl in Eq'. subst q'.
            by iApply (WeakAuth_drop_last with "[$WA $Wt]").
          - rewrite (decide_False _ _ NEq) in Eq'. destruct Eq' as [q3 Eq3].
            iExists q3. iFrame (Eq3). rewrite Eq3 Qp.add_comm.
            rewrite {1}(_: n = (1 + Pos.pred n)%positive);
              first by iApply (WeakAuth_drop with "[$WA $Wt]").
            by rewrite -Pplus_one_succ_l Pos.succ_pred. }
        iIntros "!>". iSplitL "SDA".
        { rewrite /Q decide_False.
          - by iFrame "SDA". - rewrite Z2Pos.inj_add; by lia. }
        iDestruct (GPS_SWSharedReaders_join with "R' R") as "R".
        iDestruct (GPS_SWSharedWriter_Reader_update with "W' R") as "[W' R]".
        iDestruct (WkUps_join with "[$WU $WU']") as "WU".
        iCombine "SeenU" "SeenU'" as "SeenU'".
        iDestruct (SeenActs_join with "SeenU'") as "SeenU'".
        rewrite decide_False; last lia.
        iCombine "tok" "tok'" as "tok". rewrite -Qp.div_add_distr.
        case (decide (n = 1%positive)) => nEq.
        + subst n. simpl in Eq'. subst q'. iExists (Some 1%Qp, None).
          iSplitL""; [done|]. iFrame "WA W'". iSplitL ""; [done|]. iExists _.
          rewrite Eq''. by iFrame "tok R WU SeenU'".
        + iDestruct "WA" as (q2 Eq2) "WA". subst q'.
          iExists (Some 1%Qp, Some $ Cinl (q2, Pos.pred n)). iSplitL"".
          { iPureIntro. f_equal. rewrite Z.add_simpl_r /=.
            by rewrite Z.add_1_r -Pos2Z.inj_succ Pos.succ_pred. }
          iFrame "WA W'". iSplitL ""; [done|]. iExists (q + q'')%Qp,_.
          iFrame "tok R WU SeenU'".
          iPureIntro. by rewrite Qp.add_assoc (Qp.add_comm q2).
      - iDestruct "WI" as "($ & WI & HP & tokS & SW & SM & SD)".
        iDestruct "WI" as (q'' Ut') "(Eq'' & tok' & R & WU' & SeenU')".
        iDestruct "Eq''" as %Eq''. rewrite /StrDowns.
        iDestruct "SD" as (Dt') "SD". iDestruct "SDA" as (Dt) "SDA".
        iDestruct (StrongDownAuth_agree with "[$SDA SD]") as %?;
          [by rewrite /StrDowns|subst Dt'].
        iModIntro. iExists (). iSplitL""; [done|]. iIntros (t'' Lt'') "W' R'".
        set Dt' : gset time := if decide (n = 1%positive) then (Dt ∪ {[t'']}) else Dt.
        iAssert (|==> StrongDownAuth γsw Dt' ∗ StrDowns γsw 1%Qp Dt' ∗
                      <obj> if decide (n = 1%positive)
                            then StrDownCert γsw t'' else True)%I
                with "[SDA SD]" as ">(SDA & SD & Cert)".
        { case decide => Eq; last first.
          { rewrite /StrDowns /Dt' decide_False; [|done]. iFrame "SDA SD".
            by iIntros "!> !>". }
          rewrite /Dt' Eq/=.
          iMod (StrDowns_update _ _ _ {[t'']} with "[$SDA SD]") as "($&$&Cert)";
            [by rewrite /StrDowns|]. iIntros "!> !>". by iFrame "Cert". }
        iModIntro. iSplitL "Cert".
        { iIntros "!> !>". iExists (None, Some $ Cinl (q',n)).
          do 2 (iSplit; [done|]). destruct n; [done..|]. iExists t''.
          by iDestruct (monPred_objectively_elim with "Cert") as "$". }
        iAssert (|==> if decide (n = 1%positive)
                      then WeakAuth γsw (None, None)
                      else ∃ q'', ⌜q' = (q + q'')%Qp⌝ ∗
                           WeakAuth γsw (None, Some (Cinl (q'', Pos.pred n))))%I
          with "[Wt WA]" as ">WA".
        { case decide => NEq.
          - subst n. simpl in Eq'. subst q'.
            by iApply (WeakAuth_drop_last with "[$WA $Wt]").
          - rewrite (decide_False _ _ NEq) in Eq'. destruct Eq' as [q3 Eq3].
            iExists q3. iFrame (Eq3). rewrite Eq3 Qp.add_comm.
            rewrite {1}(_: n = (1 + Pos.pred n)%positive);
              first by iApply (WeakAuth_drop with "[$WA $Wt]").
            by rewrite -Pplus_one_succ_l Pos.succ_pred. }
        iIntros "!>".
        iDestruct (GPS_SWSharedReaders_join with "R' R") as "R'".
        iDestruct (GPS_SWSharedWriter_Reader_update with "W' R'") as "[W' R']".
        iDestruct (WkUps_join with "[$WU $WU']") as "WU".
        iCombine "SeenU" "SeenU'" as "SeenU'".
        iDestruct (SeenActs_join with "SeenU'") as "SeenU'".
        case (decide (n = 1%positive)) => nEq.
        + subst n. simpl in Eq'. subst q'. iSplitR "WA"; last first.
          { iExists (None,None). by iFrame "WA". }
          iSplitL "SDA";  [by iExists _|]. simpl. rewrite Eq''.
          iDestruct (GPS_SWSharedReader_Reader with "R'") as "#RR".
          iFrame "W' R' HP SW SM".
          iSplitL "tok'"; by iFrame.
        + iSplitL "SDA". { rewrite /Q Pos2Z.id decide_False; [|done].
                           iSplitR ""; [by iExists _|done]. }
          rewrite decide_False; last first. { by destruct n; try lia. }
          iDestruct "WA" as (q2 Eq2) "WA".
          iExists (None, Some $ Cinl (q2, Pos.pred n)). iSplitL "".
          { iPureIntro. f_equal. by rewrite Z.sub_1_r -Pos2Z.inj_pred. }
          iFrame "WA W' HP SW SM". subst q'. iSplitR "SD tokS"; [|by iFrame].
          iExists (q + q'')%Qp, _.
          iCombine "tok" "tok'" as "tok". rewrite -Qp.div_add_distr.
          iFrame "R' tok WU SeenU'". by rewrite assoc_L (comm_L _ q2). }

    (* finally done with the CAS *)
    iIntros "!>" (b t2 [] v2) "(_ & [((%&%&%)&QI) | ((%&_&%)&IW&R'&_&P&IS)])";
      last first.
    { (* CAS fails *)
      subst b. iDestruct "P" as "(Wt & WU & SDA & tok)".
      iAssert (view_tok γi (q / 2)) with "[tokn tok]" as "tok".
      { case decide => ?; by iFrame. }
      iMod ("Hclose1" with "tok [SMA SDA WUA IW IS]") as "tok".
      { by iApply (arc_inv_join with "SMA SDA WUA IS IW"). }
      iModIntro. wp_case. iApply ("IH" with "[-HΦ] HΦ").
      iExists _, _, _. by iFrame  "Wt tok R' WU SeenU". }

    (* CAS succeeds *)
    subst b v2. iDestruct "QI" as (V') "(#InV' & P & IS & VS)".
    case (decide (z = 1)) => Eq; last first.
    { (* not the last drop *)
      iDestruct "P" as "(Wt & WU & SDA & tok)".
      rewrite bi.and_elim_r bi.and_elim_l decide_False; last done.
      iMod ("Hclose1" $! _ True%I with "tok [SMA SDA WUA VS IS Wt WU]") as "_".
      { iIntros "tok". iMod ("VS" with "[$Wt $WU SDA tok]") as "[IW Q]".
        { rewrite decide_False; last done. iFrame "tok".
          iDestruct "SDA" as (Dt) "SDA". by iExists Dt. }
        iDestruct "Q" as ([]) "(_&_&[[%Dt SDA] _])".
        iDestruct (acq_embed_elim with "SDA") as "SDA".
        iIntros "!>". iSplitR ""; last done. rewrite bi.later_sep monPred_in_sep'.
        iSplitR "IS IW"; last (rewrite bi.later_sep monPred_in_sep'; iFrame "IS IW").
        rewrite 2!bi.later_sep 2!monPred_in_sep'. iSplitL "SMA"; last iSplitL "SDA";
          rewrite bi.later_exist; setoid_rewrite <- embed_later.
        - rewrite -2!embed_exist monPred_in_embed'. iDestruct "SMA" as (Mt) "SMA".
          iExists Mt. by iFrame "SMA".
        - rewrite -embed_exist monPred_in_embed'. iExists _. iFrame "SDA".
        - rewrite -2!embed_exist monPred_in_embed'. iDestruct "WUA" as (Ut') "WUA".
          iExists Ut'. by iFrame "WUA". }
      iModIntro. wp_case. wp_op. rewrite (bool_decide_false _ Eq).
      wp_case. by iApply ("HΦ"). }

    iMod ("VS" with "P") as "(IW & QI)".
    iDestruct "QI" as ([]) "(_&_&[[%Dt' SDA] Q])".
    iDestruct (acq_embed_elim with "SDA") as "SDA".
    rewrite bi.and_elim_l.
    iMod ("Hclose1" with "tokn [SMA SDA WUA IW IS]") as "tok".
    { iApply (arc_inv_join with "SMA [SDA] WUA [IS] [IW]").
      - by iExists _.
      - iApply (monPred_in_elim with "InV' IS").
      - iApply (monPred_in_elim with "InV' IW"). }
    iClear "InV'". clear P P' Dt' V' Vb.

    iModIntro. wp_case. wp_op. subst z. wp_case.
    (* fence of the last drop *)
    wp_bind FenceAcq. iApply (wp_acq_fence with "Q"); [done|].

    (* TODO: we are getting more than we need here, but at least we got everything *)
    iIntros "!> (WW & WR & tok' & WU & P2 & tokh & SW & SM & SD)".
    iDestruct "WU" as (Uw) "[WU _]". iDestruct "SM" as (Ms) "SM".
    iDestruct "tok'" as (q'' Eq'') "tok'".
    iCombine "tok" "tok'" as "tok". rewrite -Qp.div_add_distr Eq''.
    iCombine "tokh" "tok" as "tok".

    iApply wp_fupd. iApply wp_hist_inv; [done|]. iIntros "#HINV". wp_let.

    (* open the invariant to deallocate *)
    iMod (view_inv_acc_base γi N with "[$INV $tok]") as "[tok VI]"; [done|].
    iDestruct "VI" as (Vb) "[VI Hclose1]".
    iMod (arc_inv_split with "VI") as "(MA & IS & IW)".
    iDestruct ("Hclose1" with "tok") as "[#InVb >_]".
    (* finish with the invariant *)

    iMod (GPS_SWRaw_SharedWriter_revert with "WW WR IW") as "[WW IW]".
    iDestruct "SW" as (ts) "SW".
    iSpecialize ("IS" with "InVb"). iSpecialize ("IW" with "InVb").

    iMod (GPS_SWWriter_dealloc (weak_interp P2 l γi γs γsw) _ _ true
             with "HINV IW WW") as "[Hw _]"; [done|].
    iMod (GPS_SWWriter_dealloc (strong_interp P1 (l >> 1) γi γw γsw) _ _ true
             with "HINV IS SW") as "[Hs _]"; [done|].

    iModIntro. iApply ("HΦ" with "[P2 Hw Hs]"). simpl. by iFrame "∗".
  Qed.

  Lemma drop_fake_spec γi γs γw γsw l tid :
    histN ## N → is_arc P1 P2 N γi γs γw γsw l -∗
    {{{ fake_arc l γi γs γw γsw ∗ P2 }}} drop_weak [ #l] @ tid; ⊤
    {{{ (b : bool), RET #b ; if b then P2 ∗ l ↦ #0 ∗ (l >> 1) ↦ #0 else True }}}.
  Proof.
    iIntros (?) "#INV !# * [HP HP2] HΦ". iLöb as "IH". wp_rec. wp_op.
    (* read the value *)
    wp_bind (!ʳˡˣ_)%E.
    iDestruct "HP" as "(tok & SW & SM & SD & oW)". iDestruct "SM" as (Mt) "[SM #SeenM]".
    iDestruct "SD" as (Dt) "[SD #SeenD]". iDestruct "SeenD" as (t1 v1) "[WR MAX]".
    iDestruct "MAX" as %MAX.
    (* opening invariant *)
    iMod (view_inv_acc_base γi N with "[$INV $tok]") as "[tok VI]"; [done|].
    iDestruct "VI" as (Vb) "[VI Hclose1]".
    iMod (arc_inv_split with "VI") as "(MA & IS & IW)".

    set R : time → unitProtocol → val → vProp :=
      (λ t' _ v', ∃ z : Z, ⌜v' = #z ∧ -1 ≤ z⌝)%I.
    iApply (GPS_SWRaw_Read (weak_interp P2 l γi γs γsw) _
              (weak_noCAS γsw) R with "[$WR $IW]"); [solve_ndisj|by left|..].
    { iIntros "!>" (t' [] v' [_ Ext']) "!>". iSplit; last iSplit.
      - iIntros "#WI !>". iFrame "WI". iDestruct "WI" as (st) "[Eq1 _]".
        iDestruct "Eq1" as %?. subst v'.
        iPureIntro. eexists. split; [done|]. by apply weak_stUR_value.
      - iDestruct 1 as (st) "[Eq1 WI]". iDestruct "Eq1" as %?. subst v'.
        iModIntro. iSplitR ""; [iExists _; by iFrame "WI"|].
        iPureIntro. eexists. split; [done|]. by apply weak_stUR_value.
      - iIntros "[% F]". subst v'. iModIntro. iFrame "F". iSplitL""; [done|].
        iPureIntro. by eexists. }
    iIntros "!>" (t' [] v'). iDestruct 1 as (_) "(_ & IW & Rs)".
    iDestruct "Rs" as (z) "[% %Le1]". subst v'.
    iMod ("Hclose1" with "tok [MA IW IS]") as "tok".
    { iDestruct "MA" as "(SMA & SDA & WUA)".
      by iApply (arc_inv_join with "SMA SDA WUA IS IW"). }

    clear Vb R. iModIntro. wp_let. wp_op. wp_op.
    wp_bind (CAS _ _ _ _ _ _).
    (* preparing to CAS *)
    (* opening invariant *)
    iMod (view_inv_acc_base γi N with "[$INV $tok]") as "[tok VI]"; [done|].
    iDestruct "VI" as (Vb) "[VI Hclose1]".
    iMod (arc_inv_split with "VI") as "((SMA & SDA & WUA) & IS & IW)".
    iDestruct "SDA" as (Dt') "SDA".
    iDestruct (StrongDownAuth_agree with "[$SDA $SD]") as %?. subst Dt'.

    set P : vProp :=
      (P2 ∗ (∃ ts, GPS_SWWriter l ts ((): unitProtocol) #0 γs) ∗
       StrMoves γsw 1 Mt ∗
       StrDowns γsw 1 Dt ∗
       agown γsw (awk_n ((Some 1%Qp, ε))) ∗
       StrongDownAuth γsw Dt ∗
       if decide (z = 1) then True else view_tok γi (1 / 2))%I.
    set P' : vProp :=
      (⊒Vb →
            ▷ GPS_INV (strong_interp P1 (l >> 1) γi γw γsw) l strong_noCAS γs)%I.
    set Q: time → unitProtocol → vProp :=
      (λ t'' _, (∃ Dt', StrongDownAuth γsw Dt') ∗
          if decide (Z.to_pos z = 1%positive)
          then GPS_SWSharedWriter (l >> 1) t'' ((): unitProtocol) #0 γw ∗
               GPS_SWSharedReader (l >> 1) t'' ((): unitProtocol) #0 1%Qp γw ∗
               view_tok γi (1/2) ∗
               (∃ Uts, WkUps γsw 1 Uts ∗ SeenActs γs l Uts) ∗
               P2 ∗
               (∃ ts : time, GPS_SWWriter l ts ((): unitProtocol) #0 γs) ∗
               (∃ Mts, StrMoves γsw 1%Qp Mts) ∗
               (∃ Dts, StrDowns γsw 1 Dts)
          else True)%I.

    iAssert ((if decide (z = 1)
              then True else view_tok γi (1 / 2)) ∗
              (if decide (z = 1)
              then view_tok γi (1 / 2) else True))%I with "[tok]" as "[tok tokn]".
    { case decide => ?; by iFrame "tok". }

    (* here comes the CAS *)
    iApply (GPS_SWRaw_SharedWriter_CAS_int_view_weak (weak_interp P2 l γi γs γsw) _
            (weak_noCAS γsw) _ _ z #(z-1) _ _ _ _ P P' Q (λ _ _ _, True)%I _ Vb
            with "[$WR $IW $IS SDA HP2 SW SM SD oW tok]");
      [solve_ndisj|by left|by left|..].
    { iSplitL "".  { iIntros "!>!>" (??? _). by iApply arc_weak_interp_comparable_2. }
      iSplitR "HP2 SW SM SD oW SDA tok"; [|iSplitL""]; [..|by iFrame]; last first.
      { iIntros (t2 [] [_ Ext2]). iSplit.
        - iIntros "(_&_&_&_&_&SDA&_) >[Eq NO]".
          iDestruct "NO" as (t3 Lt3) "Cert".
          iDestruct (StrongDownAuth_Cert_include with "[$SDA $Cert]")
            as %Le3%elem_of_subseteq_singleton%MAX. exfalso.
          apply (irreflexive_eq (R:=Pos.lt) t1 t1); [done|].
          eapply Pos.le_lt_trans; [exact Ext2|]. eapply Pos.lt_le_trans; [exact Lt3|done].
        - iIntros (??) "!> !>". iSplit; last iSplit; by iIntros "$ !>". }
      iIntros "!>" (t2 [] [_ Ext2]) "(HP2 & SW & SM & SD & oW & SDA & tok)".
      iDestruct 1 as (st) "[Eq [WA WI]]". iDestruct "Eq" as %Eq'.
      inversion Eq'. subst z. clear Eq'. destruct st as [iS st].
      iDestruct (WeakAuth_strong with "[$WA $oW]") as %[qs ?]. subst iS.
      destruct st as [[[q' n]|[]| ]|];
        [|iDestruct "WI" as "[? WI]"; iDestruct "WI" as (?) "[? WI]";
          by iDestruct (StrWkTok_exclusive with "[$oW $WI]") as %?
         |by iDestruct (WeakAuth_valid with "WA") as %?|].
      - (* n weak arcs left, put strong into weak *)
        iDestruct "WI" as "(Eqs & $ & WI)". iDestruct "Eqs" as %?. subst qs.
        iDestruct "WI" as (q'' Ut') "[Eq'' WR']". iDestruct "Eq''" as %Eq''.
        iModIntro. iExists (). iSplitL""; [done|]. iIntros (t'' Lt'') "W'".
        iModIntro. iSplitL "".
        { iIntros "!> !>". by iExists (Some 1%Qp, Some $ Cinl (q', n)). }
        iMod (WeakAuth_drop_strong with "[$WA $oW]") as "WA".
        iIntros "!>". iSplitL "SDA".
        { rewrite /Q /=. iSplitL "SDA"; [by iExists _|].
          rewrite decide_False; [done|by lia]. }
        rewrite (_: Z_of_arcweak_st (Some 1%Qp, Some (Cinl (q', n))) - 1 =
            Z.pos n); last first.
        { rewrite Z.sub_1_r -Pos2Z.inj_pred; [|lia].
          by rewrite /= -Pplus_one_succ_r Pos.pred_succ. }
        iExists (None, Some (Cinl (q',n))). iSplitL ""; [done|].
        iDestruct "WR'" as "(tok'' & R'' & WR')".
        iDestruct (GPS_SWSharedWriter_Reader_update with "W' R''") as "[W' R'']".
        rewrite decide_False; last by (simpl; lia).
        iFrame "WA W' HP2 SW".
        iSplitL "tok'' R'' WR'". { iExists q'',_. iFrame (Eq'') "tok'' R'' WR'". }
        iFrame.
      - (* no weak arcs left, take out everything *)
        simpl. iDestruct "WI" as "(Eqs & $ & WI)". iDestruct "Eqs" as %?. subst qs.
        iModIntro. iExists (). iSplitL""; [done|]. iIntros (t'' Lt'') "W'".
        iDestruct "WI" as (Ut') "(tok' & R' & WU & SeenU)".
        iMod (StrDowns_update _ _ _ {[t'']} with "[$SDA $SD]") as "(SDA & SD & Cert)".
        iModIntro. iSplitL "Cert".
        { iIntros "!> !>". iExists (Some 1%Qp, None). do 2 (iSplit; [done|]).
          iExists t''. by iFrame (Lt'') "Cert". }
        iMod (WeakAuth_drop_strong with "[$WA $oW]") as "WA".
        iIntros. iSplitR "WA"; last by (iExists (None,None); iFrame "WA").
        iSplitL "SDA"; [by iExists _|]. simpl.
        iDestruct (GPS_SWSharedWriter_Reader_update with "W' R'") as "[W' R']".
        iDestruct (GPS_SWSharedReader_Reader with "R'") as "#R5".
        iFrame "W' R' tok' HP2 SW".
        iSplitL "WU SeenU"; [iExists _; by iFrame "WU SeenU"|].
        iSplitL "SM"; by iExists _. }

    (* finally done with the CAS *)
    iIntros "!>" (b t2 [] v2) "(_ & [((%&%&%)&QI) | ((%&_&%)&IW&R'&_&P&IS)])";
      last first.
    { (* CAS fails *)
      subst b. iDestruct "P" as "(HP2 & SW & SM & SD & oW & SDA & tok)".
      iAssert (view_tok γi (1 / 2)) with "[tokn tok]" as "tok".
      { case decide => ?; by iFrame. }
      iMod ("Hclose1" with "tok [SMA SDA WUA IW IS]") as "tok".
      { iApply (arc_inv_join with "SMA [SDA] WUA IS IW"). by iExists _. }
      iModIntro. wp_case. iApply ("IH" with "[$tok $SW SD $oW R' SM] HP2 HΦ").
      iSplitL "SM". { iExists _. by iFrame "SM SeenM". }
      iExists _. iFrame "SD". iExists _,_. iFrame (MAX) "WR". }

    subst b v2. iDestruct "QI" as (V') "(#InV' & P & IS & VS)".
    case (decide (z = 1)) => Eq; last first.
    { (* not the last drop *)
      iDestruct "P" as "(HP2 & SW & SM & SD & oW & SDA & tok)".
      rewrite bi.and_elim_r bi.and_elim_l decide_False; last done.
      iMod ("Hclose1" $! _ True%I
              with "tok [SMA SDA WUA VS IS HP2 SW SM SD oW]") as "_".
      { iIntros "tok".
        iMod ("VS" with "[$HP2 $SW $SM $SD $oW $SDA tok]") as "[IW Q]".
        { rewrite decide_False; last done. iFrame "tok". }
        iDestruct "Q" as ([]) "(_&_&[[%Dt' SDA] _])".
        iDestruct (acq_embed_elim with "SDA") as "SDA".
        iIntros "!>". iSplitR ""; last done. rewrite bi.later_sep monPred_in_sep'.
        iSplitR "IS IW"; last (rewrite bi.later_sep monPred_in_sep'; iFrame "IS IW").
        rewrite 2!bi.later_sep 2!monPred_in_sep'. iSplitL "SMA"; last iSplitL "SDA";
          rewrite bi.later_exist; setoid_rewrite <- embed_later.
        - rewrite -2!embed_exist monPred_in_embed'. iDestruct "SMA" as (Mt') "SMA".
          iExists Mt'. by iFrame "SMA".
        - rewrite -embed_exist monPred_in_embed'. iExists _. iFrame "SDA".
        - rewrite -2!embed_exist monPred_in_embed'. iDestruct "WUA" as (Ut') "WUA".
          iExists Ut'. by iFrame "WUA". }

      iModIntro. wp_case. wp_op. rewrite (bool_decide_false _ Eq).
      wp_case. by iApply ("HΦ"). }

    iMod ("VS" with "P") as "(IW & QI)".
    iDestruct "QI" as ([]) "(_&_&[[%Dt' SDA] Q])".
    iDestruct (acq_embed_elim with "SDA") as "SDA".
    rewrite bi.and_elim_l.
    iMod ("Hclose1" with "tokn [SMA SDA WUA IW IS]") as "tok".
    { iApply (arc_inv_join with "SMA [SDA] WUA [IS] [IW]").
      - by iExists _.
      - iApply (monPred_in_elim with "InV' IS").
      - iApply (monPred_in_elim with "InV' IW"). }
    iClear "InV'". clear P P' Dt' V' Vb Q.

    iModIntro. wp_case. wp_op. subst z. wp_case.
    (* fence of the last drop *)
    wp_bind FenceAcq. iApply (wp_acq_fence with "Q"); [done|].

    (* TODO: we are getting more than we need here, but at least we got everything *)
    iIntros "!> (WW & WR' & tok' & WU & P2 & SW & SM & SD)".
    iDestruct "WU" as (Uw) "[WU _]". iDestruct "SM" as (Ms) "SM".
    iCombine "tok" "tok'" as "tok".

    iApply wp_fupd. iApply wp_hist_inv; [done|]. iIntros "#HINV". wp_let.
    (* open the invariant to deallocate *)
    iMod (view_inv_acc_base γi N with "[$INV $tok]") as "[tok VI]"; [done|].
    iDestruct "VI" as (Vb) "[VI Hclose1]".
    iMod (arc_inv_split with "VI") as "(MA & IS & IW)".
    iDestruct ("Hclose1" with "tok") as "[#InVb >_]".
    (* finish with the invariant *)

    iMod (GPS_SWRaw_SharedWriter_revert with "WW WR' IW") as "[WW IW]".
    iDestruct "SW" as (ts) "SW".
    iSpecialize ("IS" with "InVb"). iSpecialize ("IW" with "InVb").

    iMod (GPS_SWWriter_dealloc (weak_interp P2 l γi γs γsw) _ _ true
             with "HINV IW WW") as "[Hw _]"; [done|].
    iMod (GPS_SWWriter_dealloc (strong_interp P1 (l >> 1) γi γw γsw) _ _ true
             with "HINV IS SW") as "[Hs _]"; [done|].

    iModIntro. iApply ("HΦ" with "[P2 Hw Hs]"). simpl. by iFrame "∗".
  Qed.

  Lemma drop_arc_spec {HPn: HP2} γi γs γw γsw l q tid :
    histN ## N → is_arc P1 P2 N γi γs γw γsw l -∗
    {{{ (∃ ts, strong_arc ts q l γi γs γw γsw) ∗ P1 q }}}
      drop_arc [ #l] @ tid; ⊤
    {{{ (b : bool), RET #b ;
        if b then P1 1 ∗ fake_arc l γi γs γw γsw else True }}}.
  Proof.
    iIntros (?) "#INV !# * [HP HP1] HΦ". iLöb as "IH". wp_rec.
    (* read the value *)
    wp_bind (!ʳˡˣ_)%E.
    iDestruct "HP" as (t v Mt Dt) "(St & tok & SR & SM & #SeenM & SD & #SeenD & oW)".
    (* opening invariant *)
    iMod (view_inv_acc_base γi N with "[$INV $tok]") as "[tok VI]"; [done|].
    iDestruct "VI" as (Vb) "[VI Hclose1]".
    iMod (arc_inv_split with "VI") as "(MA & IS & IW)".

    set R : time → unitProtocol → val → vProp := (λ t' _ v', ∃ z : Z, ⌜v' = #z⌝)%I.
    iApply (GPS_SWRaw_SharedReader_Read (strong_interp P1 (l >> 1) γi γw γsw) _
              strong_noCAS R with "[$SR $IS]"); [solve_ndisj|by left|..].
    { iIntros "!>" (t' [] v' [_ Ext']) "!>". iSplit.
      - iIntros "#SI !>". iFrame "SI". iDestruct "SI" as (st) "[% _]".
        subst v'. by iExists _.
      - iDestruct 1 as (st) "[Eq1 SI]". iDestruct "Eq1" as %?. subst v'.
        iModIntro. iSplitR "". { iExists _. by iFrame "SI". } by iExists _. }
    iIntros "!>" (t' [] v'). iDestruct 1 as ([_ Ext']) "(SR & IS & Rs)".
    iDestruct "Rs" as (z) "%". subst v'.
    iMod ("Hclose1" with "tok [MA IW IS]") as "tok".
    { iDestruct "MA" as "(SMA & SDA & WUA)".
      by iApply (arc_inv_join with "SMA SDA WUA IS IW"). }
    clear Vb R. iModIntro. wp_let. wp_op.
    wp_bind (CAS _ _ _ _ _ _).
    (* preparing to CAS *)
    iMod (view_inv_acc_base γi N with "[$INV $tok]") as "[tok VI]"; [done|].
    iDestruct "VI" as (Vb) "[VI Hclose1]".
    iMod (arc_inv_split with "VI") as "((SMA & SDA & WUA) & IS & IW)".

    set P : vProp := (P1 q ∗ StrongTok γsw q ∗
                      StrMoves γsw q Mt ∗ StrDowns γsw q Dt ∗
                      agown γsw (awk_n ((Some q, ε))) ∗
                      (∃ Mt', StrongMoveAuth γsw Mt') ∗
                      if decide (z = 1) then True else view_tok γi (q / 2))%I.
    set P' : vProp :=
      (⊒Vb →
            ▷ GPS_INV (weak_interp P2 l γi γs γsw) (l >> 1) (weak_noCAS γsw) γw)%I.
    set Q: time → unitProtocol → vProp :=
      (λ t'' _, (∃ Mt', StrongMoveAuth γsw Mt') ∗
          if decide (Z.to_pos z = 1%positive)
          then GPS_SWSharedWriter l t'' ((): unitProtocol) #0 γs ∗
              P1 1%Qp ∗
              (∃ q'', ⌜(q + q'')%Qp = 1%Qp⌝ ∗ view_tok γi (q''/2)) ∗
              GPS_SWSharedReader l t'' ((): unitProtocol) #0 1%Qp γs ∗
              (∃ Mt', StrMoves γsw 1%Qp Mt' ∗ SeenActs γs l Mt') ∗
              (∃ Dt', StrDowns γsw 1%Qp Dt' ∗ SeenActs γw (l >> 1) Dt') ∗
              StrWkTok γsw 1%Qp
          else True)%I.

     iAssert ((if decide (z = 1)
              then True else view_tok γi (q / 2)) ∗
              (if decide (z = 1)
              then view_tok γi (q / 2) else True))%I with "[tok]" as "[tok tokn]".
    { case decide => ?; by iFrame "tok". }

    (* here comes the CAS *)
    iApply (GPS_SWRaw_SharedWriter_CAS_int_view_strong
            (strong_interp P1 (l >> 1) γi γw γsw) _
            strong_noCAS true _ _ z #(z-1) _ _ _ _ _ P P' Q (λ _ _ _, True)%I _ Vb
            with "[$SR $IS $IW St SM SD SMA HP1 oW tok]");
      [solve_ndisj|by left|by left|..].
    { iSplitL "". { iIntros "!>!>" (??? _). by iApply arc_strong_interp_comparable. }
      iSplitR "HP1 St SM SD oW SMA tok"; [|iSplitL""]; [..|by iFrame]; last first.
      { iIntros (????) "!> !>". by iSplit; iIntros "$". }
      iIntros "!>" (t1 [] [_ Ext1]) "(HP1 & St & SM & SD & oW & SMA & tok)".
      iDestruct 1 as (st) "[Eq [SA SI]]".
      iDestruct "Eq" as %Eq. inversion Eq. subst z. clear Eq.
      iDestruct (StrongTok_Auth_agree with "[$SA $St]") as %(q'&n&?&Eq'). subst st.
      iDestruct "SI" as "[$ SI]". iDestruct "SI" as (q'') "(Eq & HP2 & SI)".
      iDestruct "SI" as (Mt2 Dt2) "(tok' & SR' & SM' & #SeenM' & SD' & SeenD' & oW')".
      iDestruct "Eq" as %Eq''. rewrite {2}/StrMoves. iDestruct "SM'" as "SM'".
      iDestruct (StrMoves_agree with "[$SM SM']") as %?; [by rewrite /StrMoves|].
      subst Mt2. iDestruct (StrMoves_fractional with "[$SM SM']") as "SM";
          [by rewrite /StrMoves|]. iDestruct "SMA" as (Mt') "SMA".
      iDestruct (StrongMoveAuth_agree with "[$SMA $SM]") as %?. subst Mt'.
      iModIntro. iExists (). iSplitL""; [done|]. iIntros (t'' Lt'') "W' R'".
      set Mt' : gset time := if decide (n = 1%positive) then (Mt ∪ {[t'']}) else Mt.
      iAssert (|==> StrongMoveAuth γsw Mt' ∗ StrMoves γsw (q + q'') Mt' ∗
                    <obj> if decide (n = 1%positive)
                          then StrMoveCert γsw t'' else True)%I
              with "[SMA SM]" as ">(SMA & SM & Cert)".
      { case decide => Eq; last first.
        { rewrite /Mt' decide_False; [|done]. iFrame "SMA SM". by iIntros "!> !>". }
        rewrite /Mt' (decide_True _ _ Eq). rewrite (decide_True _ _ Eq) in Eq'.
        subst q. rewrite Eq''.
        iMod (StrMoves_update _ _ {[t'']} with "[$SMA $SM]") as "($ & $ & Cert)".
        iIntros "!> !>". by iFrame "Cert". }
      iModIntro. iSplitL "Cert".
      { iIntros "!> !>". iExists (Some (q',n)). iSplit; [done|].
        destruct n; [done..|]. iExists t''. iFrame (Lt'').
        iDestruct (monPred_objectively_elim with "Cert") as "$". }
      iAssert (|==> if decide (n = 1%positive)
                    then StrongAuth γsw None
                    else ∃ q'', ⌜q' = (q + q'')%Qp⌝ ∗
                         StrongAuth γsw (Some (q'', Pos.pred n)))%I
        with "[St SA]" as ">SA".
      { case decide => NEq.
        - subst n. simpl in Eq'. subst q'.
          by iApply (StrongAuth_drop_last with "[$SA $St]").
        - rewrite (decide_False _ _ NEq) in Eq'. destruct Eq' as [q3 Eq3].
          iExists q3. iFrame (Eq3). rewrite Eq3 Qp.add_comm.
          rewrite {1}(_: n = (1 + Pos.pred n)%positive);
            first by iApply (StrongAuth_drop with "[$SA $St]").
          by rewrite -Pplus_one_succ_l Pos.succ_pred. }
      iIntros "!>".
      iDestruct (GPS_SWSharedReaders_join with "R' SR'") as "R'".
      iDestruct (StrDowns_join with "[$SD $SD']") as "SD".
      iCombine "oW" "oW'" as "oW". iCombine "HP1" "HP2" as "HP".
      rewrite (bi.wand_entails _ _ (HPn _ _)).
      iCombine "SeenD" "SeenD'" as "SeenD'".
      iDestruct (SeenActs_join with "SeenD'") as "SeenD'".
      case (decide (n = 1%positive)) => nEq.
      - subst n. simpl in Eq'. subst q'. iSplitR "SA"; last first.
        { iExists None. by iFrame "SA". }
        iSplitL "SMA";  [by iExists _|]. simpl. rewrite Eq''.
        iDestruct "SeenM" as (t5 v5) "[#R5 MAX]". iDestruct "MAX" as %MAX.
        iDestruct (GPS_SWSharedWriter_latest_time_1 with "W' R5") as %Le5.
        iDestruct (GPS_SWSharedReader_Reader with "R'") as "#RR".
        iFrame "W' HP R' oW".
        iSplitL "tok'". { iExists _. by iFrame (Eq'') "tok'". } iSplitL "SM".
        { iExists _. iFrame "SM". iExists _, _. iFrame "RR". iPureIntro.
          move => ? /elem_of_union [/MAX ->//|/elem_of_singleton -> //]. }
        iExists _. by iFrame "SD SeenD'".
      - iSplitL "SMA". { rewrite /Q Pos2Z.id decide_False; [|done].
                         iSplitR ""; [by iExists _|done]. }
        iDestruct "SA" as (q2 Eq2) "SA".
        iExists (Some (q2, Pos.pred n)). iSplitL "".
        { iPureIntro. f_equal. by rewrite Z.sub_1_r -Pos2Z.inj_pred. }
        iFrame "SA W'". subst q'. iExists (q + q'')%Qp. iSplitL "".
        { by rewrite Qp.add_assoc (Qp.add_comm q2). } iFrame "HP".
        iExists _,_. iFrame "R' SM SD SeenD' oW".
        rewrite /Mt' (decide_False _ _ nEq). iFrame "SeenM'".
        rewrite decide_False; last first. { simpl. by destruct n; try lia. }
        rewrite Qp.div_add_distr. by iFrame "tok tok'". }

    (* finally done with the CAS *)
    iIntros "!>" (b t2 [] v2) "(_ & [((%&%&%)&QI) | ((%&_&%)&IS&R'&_&P&IW)])";
      last first.
    { (* CAS fails *)
      subst b. iDestruct "P" as "(HP1 & St & SM & SD & oW & SMA & tok)".
      iAssert (view_tok γi (q / 2)) with "[tokn tok]" as "tok".
      { case decide => ?; by iFrame. }
      iMod ("Hclose1" with "tok [SMA SDA WUA IW IS]") as "tok".
      { by iApply (arc_inv_join with "SMA SDA WUA IS IW"). }
      iModIntro. wp_case. iApply ("IH" with "[$St $tok SM SD $oW R'] HP1 HΦ").
      iExists _,_,_,_. by iFrame "R' SM SeenM SD SeenD". }

    subst b v2. iDestruct "QI" as (V') "(#InV' & P & IW & VS)".
    case (decide (z = 1)) => Eq; last first.
    { (* not the last drop *)
      iDestruct "P" as "(HP1 & St & SM & SD & oW & SMA & tok)".
      rewrite bi.and_elim_r bi.and_elim_l decide_False; last done.
      iMod ("Hclose1" $! _ True%I
              with "tok [SMA SDA WUA VS IW HP1 St SM SD oW]") as "_".
      { iIntros "tok".
         iMod ("VS" with "[$HP1 $St $SM $SD $oW SMA tok]") as "[IS Q]".
        { rewrite decide_False; last done. iFrame "tok".
          iDestruct "SMA" as (Mt1) "SMA". by iExists Mt1. }
        iDestruct "Q" as ([]) "(_&_&[[%Mt1 SMA] _])".
        iDestruct (acq_embed_elim with "SMA") as "SMA".
        iIntros "!>". iSplitR ""; last done. rewrite bi.later_sep monPred_in_sep'.
        iSplitR "IS IW"; last (rewrite bi.later_sep monPred_in_sep'; iFrame "IS IW").
        rewrite 2!bi.later_sep 2!monPred_in_sep'. iSplitL "SMA"; last iSplitL "SDA";
          rewrite bi.later_exist; setoid_rewrite <- embed_later.
        - rewrite -embed_exist monPred_in_embed'. iExists Mt1. by iFrame "SMA".
        - rewrite -2!embed_exist monPred_in_embed'. iDestruct "SDA" as (?) "SDA".
          iExists _. iFrame "SDA".
        - rewrite -2!embed_exist monPred_in_embed'. iDestruct "WUA" as (Ut') "WUA".
          iExists Ut'. by iFrame "WUA". }
      iModIntro. wp_case. wp_op. rewrite (bool_decide_false _ Eq).
      wp_case. by iApply ("HΦ"). }

    iMod ("VS" with "P") as "(IS & QI)".
    iDestruct "QI" as ([]) "(_&_&[[%Mt' SMA] Q])".
    iDestruct (acq_embed_elim with "SMA") as "SMA".
    rewrite bi.and_elim_l.
    iMod ("Hclose1" with "tokn [SMA SDA WUA IW IS]") as "tok".
    { iApply (arc_inv_join with "[SMA] SDA WUA [IS] [IW]").
      - by iExists _.
      - iApply (monPred_in_elim with "InV' IS").
      - iApply (monPred_in_elim with "InV' IW"). }
    iClear "InV'". clear P P' V' Vb Q Mt'.

    iModIntro. wp_case. wp_op. subst z. wp_case.
    (* fence of the last drop *)
    wp_bind FenceAcq. iApply (wp_acq_fence with "Q"); [done|].

    iIntros "!> (SW & HP & tok' & SR & SM & SD & oW)".
    iDestruct "SM" as (Mt2) "[SM SeenM']". iDestruct "SD" as (Dt2) "[SD SeenD']".
    iDestruct "tok'" as (q'' Eq'') "tok'".

    iApply wp_fupd. wp_let.
    (* open invariant to revert shared writer to strong writer *)
    iMod (view_inv_acc_base γi N with "[$INV $tok]") as "[tok VI]"; [done|].
    iDestruct "VI" as (Vb) "[VI Hclose1]".
    iMod (arc_inv_split with "VI") as "((SMA & SDA & WUA) & IS & IW)".

    iMod (GPS_SWRaw_SharedWriter_revert (strong_interp P1 (l >> 1) γi γw γsw)
            with "SW SR IS") as "[SW IS]".
    iMod ("Hclose1" with "tok [SMA SDA WUA IW IS]") as "tok".
    { by iApply (arc_inv_join with "SMA SDA WUA IS IW"). }

    iCombine "tok" "tok'" as "tok". rewrite -Qp.div_add_distr Eq''.
    iModIntro. iApply "HΦ". iFrame "HP tok". iSplitL "SW"; [by iExists _|].
    iSplitL "SM SeenM'"; [iExists _; by iFrame|].
    iSplitL "SD SeenD'"; [iExists _; by iFrame|]. by iFrame "oW".
  Qed.

  Lemma try_unwrap_spec {HPn: HP2} γi γs γw γsw l q tid :
    histN ## N → is_arc P1 P2 N γi γs γw γsw l -∗
    {{{ (∃ t, strong_arc t q l γi γs γw γsw) ∗ P1 q }}} try_unwrap [ #l] @ tid; ⊤
    {{{ (b : bool), RET #b ;
        if b then P1 1 ∗ fake_arc l γi γs γw γsw
        else (∃ t, strong_arc t q l γi γs γw γsw) ∗ P1 q }}}.
  Proof.
    iIntros (?) "#INV !# * [HP HP1] HΦ". wp_lam. wp_bind (CAS _ _ _ _ _ _).
    iDestruct "HP" as (t v Mt Dt) "(St & tok & SR & SM & #SeenM & SD & #SeenD & oW)".
    (* preparing to CAS *)
    iMod (view_inv_acc_base γi N with "[$INV $tok]") as "[tok VI]"; [done|].
    iDestruct "VI" as (Vb) "[VI Hclose1]".
    iMod (arc_inv_split with "VI") as "((SMA & SDA & WUA) & IS & IW)".

    set P : vProp := (P1 q ∗ StrongTok γsw q ∗
                      StrMoves γsw q Mt ∗ StrDowns γsw q Dt ∗
                      agown γsw (awk_n ((Some q, ε))))%I.
    set Q: time → unitProtocol → vProp :=
      (λ t'' _, (∃ Mt', StrongMoveAuth γsw Mt') ∗
          GPS_SWSharedWriter l t'' ((): unitProtocol) #0 γs ∗
          P1 1%Qp ∗
          (∃ q'', ⌜(q + q'')%Qp = 1%Qp⌝ ∗ view_tok γi (q''/2)) ∗
          GPS_SWSharedReader l t'' ((): unitProtocol) #0 1%Qp γs ∗
          (∃ Mt', StrMoves γsw 1%Qp Mt' ∗ SeenActs γs l Mt') ∗
          (∃ Dt', StrDowns γsw 1%Qp Dt' ∗ SeenActs γw (l >> 1) Dt') ∗
          StrWkTok γsw 1%Qp)%I.
    set Q1: time → unitProtocol → vProp :=  (λ _ _, True)%I.
    set Q2: time → unitProtocol → vProp :=
      (λ tr sr, strong_interp P1 (l >> 1) γi γw γsw true l γs tr sr #1).
    set R: time → unitProtocol → lit → vProp :=
      (λ _ _ _, (∃ Mt', StrongMoveAuth γsw Mt'))%I.

    (* here comes the CAS *)
    iApply (GPS_SWRaw_SharedWriter_CAS_int_strong (strong_interp P1 (l >> 1) γi γw γsw)
            _ strong_noCAS true _ _ _ 1 #0 _ _ _ _ _ P Q Q1 Q2 R _ Vb
            _ (↑histN) with "[$SR $IS St SM SD SMA HP1 oW]");
      [solve_ndisj|solve_ndisj|by left|by left|by right|..].
    { iSplitL "". { iIntros "!>!>" (??? _). by iApply arc_strong_interp_comparable. }
      iSplitR "HP1 St SM SD oW"; [|by iFrame]. simpl.
      iIntros (t1 [] [_ Ext1]). iSplit; last first.
      { iIntros (??) "!> !>". iSplit; iIntros "$ !>"; by iFrame "SMA". }
      iSplitL "". { by iIntros "!> $". }
      iIntros "(HP1 & St & SM & SD & oW)".
      iDestruct 1 as (st) "[>Eq [>SA SI]]".
      iDestruct "Eq" as %Eq. inversion Eq as [Eq1].
      destruct st as [[q' [n| |]]|]; [done|done| |done]. clear Eq Eq1.
      iDestruct (StrongTok_Auth_agree with "[$SA $St]") as %(q2&n&Eq2&Eq').
      inversion Eq2. subst q2 n. simpl in Eq'. subst q'. clear Eq2.
      iDestruct "SI" as "[$ SI]". iDestruct "SI" as (q'') "(>Eq & HP2 & SI)".
      iDestruct "SI" as (Mt2 Dt2) "(tok' & SR' & SM' & #SeenM' & SD' & SeenD' & oW')".
      iDestruct "Eq" as %Eq''. rewrite {2}/StrMoves. iDestruct "SM'" as ">SM'".
      iDestruct (StrMoves_agree with "[$SM SM']") as %?; [by rewrite /StrMoves|].
      subst Mt2. iDestruct (StrMoves_fractional with "[$SM SM']") as "SM";
          [by rewrite /StrMoves|]. iDestruct "SMA" as (Mt') "SMA".
      iDestruct (StrongMoveAuth_agree with "[$SMA $SM]") as %?. subst Mt'.
      iModIntro. iExists (). iSplitL""; [done|]. iIntros (t'' Lt'') "W' R'".
      set Mt' : gset time := (Mt ∪ {[t'']}).
      iAssert (|==> StrongMoveAuth γsw Mt' ∗ StrMoves γsw (q + q'') Mt' ∗
                    <obj> StrMoveCert γsw t'')%I
              with "[SMA SM]" as ">(SMA & SM & Cert)".
      { rewrite Eq''. iMod (StrMoves_update _ _ {[t'']} with "[$SMA $SM]")
          as "($ & $ & Cert)". iIntros "!> !>". by iFrame "Cert". }
      iModIntro. iSplitL "Cert".
      { iIntros "!> _ !> !>". iExists (Some (q,1%positive)). iSplitL ""; [done|].
        iExists t''. iFrame (Lt'').
        iDestruct (monPred_objectively_elim with "Cert") as "$". }
      iMod (StrongAuth_drop_last with "[$SA $St]") as "SA".
      iApply step_fupd_intro; [solve_ndisj|]. iIntros "!>".
      iDestruct (GPS_SWSharedReaders_join with "R' SR'") as "R'".
      iDestruct (StrDowns_join with "[$SD $SD']") as "SD".
      iCombine "oW" "oW'" as "oW". iCombine "HP1" "HP2" as "HP".
      rewrite (bi.wand_entails _ _ (HPn _ _)).
      iCombine "SeenD" "SeenD'" as "SeenD'".
      iDestruct (SeenActs_join with "SeenD'") as "SeenD'".
      iSplitR "SA"; last first. { iExists None. by iFrame "SA". }
      iSplitL "SMA";  [by iExists _|]. rewrite Eq''.
      iDestruct "SeenM" as (t5 v5) "[#R5 MAX]". iDestruct "MAX" as %MAX.
      iDestruct (GPS_SWSharedWriter_latest_time_1 with "W' R5") as %Le5.
      iDestruct (GPS_SWSharedReader_Reader with "R'") as "#RR".
      iFrame "W' HP R' oW ".
      iSplitL "tok'". { iExists _. by iFrame (Eq'') "tok'". } iSplitL "SM".
      { iExists _. iFrame "SM".
        iExists _, _. iFrame "RR".
        iPureIntro. move => ? /elem_of_union [/MAX ->//|/elem_of_singleton -> //]. }
      iExists _. by iFrame "SD SeenD'". }

    iIntros "!>" (b t2 [] v2) "(IS &%& [([%[%%]]&_&Q) | ([%[_ %]] &R'&Rs&P)])";
      last first.
    { (* CAS fails*)
      subst b. iDestruct "Rs" as (Mt') "SMA".
      iDestruct (acq_embed_elim with "SMA") as "SMA".
      iDestruct "P" as "(HP1 & St & SM & SD & oW)".
      iMod ("Hclose1" with "tok [SMA SDA WUA IW IS]") as "tok".
      { iApply (arc_inv_join with "[SMA] SDA WUA IS IW"). by iExists _. }
      iModIntro. wp_case. iApply "HΦ". iFrame "HP1".
      iExists _,_,_,_. by iFrame "St tok R' SM SeenM SD SeenD oW". }

    clear P Q1 Q2 R. subst b v2.
    iDestruct "Q" as "[[%Mt' SMA] Q]".
    iDestruct (acq_embed_elim with "SMA") as "SMA".
    iMod ("Hclose1" with "tok [SMA SDA WUA IW IS]") as "tok".
    { iApply (arc_inv_join with "[SMA] SDA WUA IS IW"). by iExists _. }
    clear Vb Q Mt'.

    iModIntro. wp_case. wp_bind FenceAcq. iApply (wp_acq_fence with "Q"); [done|].
    iIntros "!> (SW & HP & tok' & SR & SM & SD & oW)".
    iDestruct "SM" as (Mt2) "[SM SeenM']". iDestruct "SD" as (Dt2) "[SD SeenD']".
    iDestruct "tok'" as (q'' Eq'') "tok'".
    iCombine "tok" "tok'" as "tok". rewrite -Qp.div_add_distr Eq''.

    iApply wp_fupd. wp_let.
    (* open invariant to revert shared writer to strong writer *)
    iMod (view_inv_acc_base γi N with "[$INV $tok]") as "[tok VI]"; [done|].
    iDestruct "VI" as (Vb) "[VI Hclose1]".
    iMod (arc_inv_split with "VI") as "((SMA & SDA & WUA) & IS & IW)".

    iMod (GPS_SWRaw_SharedWriter_revert (strong_interp P1 (l >> 1) γi γw γsw)
            with "SW SR IS") as "[SW IS]".
    iMod ("Hclose1" with "tok [SMA SDA WUA IW IS]") as "tok".
    { by iApply (arc_inv_join with "SMA SDA WUA IS IW"). }

    iModIntro. iApply "HΦ". iFrame "HP tok". iSplitL "SW"; [by iExists _|].
    iSplitL "SM SeenM'"; [iExists _; by iFrame|].
    iSplitL "SD SeenD'"; [iExists _; by iFrame|]. by iFrame "oW".
  Qed.

  Lemma is_unique_spec {HPn: HP2} γi γs γw γsw l q tid :
    histN ## N → is_arc P1 P2 N γi γs γw γsw l -∗
    {{{ (∃ t, strong_arc t q l γi γs γw γsw) ∗ P1 q }}}
      is_unique [ #l] @ tid; ⊤
    {{{ (b : bool), RET #b ;
        if b then l ↦ #1 ∗ (l >> 1) ↦ #1 ∗ P1 1
        else (∃ t, strong_arc t q l γi γs γw γsw) ∗ P1 q }}}.
  Proof.
    iIntros (?) "#INV !# * [Hown HP1] HΦ". wp_rec. wp_bind (CAS _ _ _ _ _ _). wp_op.
    iDestruct "Hown" as (t v Mt Dt) "(St & tok & SR & SM & #SeenM & SD & #SeenD & oW)".
    (* preparing to CAS *)
    iMod (view_inv_acc_base γi N with "[$INV $tok]") as "[tok VI]"; [done|].
    iDestruct "VI" as (Vb) "[VI Hclose1]".
    iMod (arc_inv_split with "VI") as "((SMA & SDA & WUA) & IS & IW)".

    iDestruct "SeenD" as (t1 v1) "[WR MAX]". iDestruct "MAX" as %MAX.
    iDestruct "SDA" as (DtA) "SDA".
    set Q: time → unitProtocol → vProp :=
      (λ t'' s'',
        StrongDownAuth γsw (DtA ∪ {[t'']}) ∗ StrDowns γsw q (Dt ∪ {[t'']}) ∗
        ⌜∀ t' : time, t' ∈ (Dt ∪ {[t'']}) → t' ⊑ t''⌝ ∗
        agown γsw (awk_n ((Some (q/2)%Qp, ε))) ∗
        WkLock γsw (q / 2)%Qp ∗
        GPS_SWSharedWriter (l >> 1) t'' (() : unitProtocol) #(-1) γw ∗
        (∃ Ut, WkResources (l >> 1) l t'' #(-1) γi γw γs γsw 1%Qp Ut))%I.
    set Q1: time → unitProtocol → vProp := (λ _ _, True)%I.
    set Q2: time → unitProtocol → vProp :=
      (λ tr sr, weak_interp P2 l γi γs γsw true (l >> 1) γw tr sr #1).
    set R: time → unitProtocol → lit → vProp :=
      (λ _ _ _, StrongDownAuth γsw DtA ∗ StrDowns γsw q Dt ∗
                agown γsw (awk_n ((Some q, ε))))%I.
    iMod (rel_True_intro tid) as "#rTrue".
    (* here comes the CAS *)
    iApply (GPS_SWRaw_SharedWriter_CAS_int_weak (weak_interp P2 l γi γs γsw) _
            (weak_noCAS γsw) _ _ _ 1 #(-1) _ _ _ _ True%I Q Q1 Q2 R _ Vb
            _ (↑histN) with "[$WR $IW SDA SD oW rTrue]");
      [solve_ndisj|solve_ndisj|by left|by right|by left|..].
    { simpl. iFrame "rTrue".
      iSplitL "". { iIntros "!>!>" (??? _). by iApply arc_weak_interp_comparable_2. }
      rewrite /= -(bi.True_sep' (∀ _ (_ : unitProtocol), _)%I).
      iApply (rel_sep_objectively with "[$rTrue SDA SD oW]"). rewrite /StrDowns.
      iIntros "!>" (t' [] [_ Ext']). iSplit; last first.
      { iIntros (??) "!> !>". iSplit; last iSplit;
          iIntros "$ !>"; iFrame "SDA oW"; by rewrite /StrDowns. }
      iSplitL "". { iIntros "_ [>%Eq _]". by inversion Eq. }
      iSplitL "". { by iIntros "!> $". } iIntros "_".
      iDestruct 1 as ([iS st]) "[>%Eq' [>WA WI]]".
      iDestruct (WeakAuth_strong with "[$WA $oW]") as %[qs ?]. subst iS.
      destruct st as [[[q' n]| | ]|];
        [exfalso; inversion Eq'; lia|by exfalso|by exfalso|]. clear Eq'.
      iDestruct "WI" as "(>Eq & $ & WI)". iDestruct "Eq" as %?. subst qs.
      iDestruct "WI" as (Ut') "(tok & R & WU & #SeenU)".
      iModIntro. iExists (). iSplitL""; [done|]. iIntros (t'' Lt'') "W'".
      iMod (StrDowns_update _ DtA Dt {[t'']} q with "[$SDA SD]")
        as "(SDA & SD & Cert)"; [by rewrite /StrDowns|].
      iModIntro. iSplitL "Cert".
      { iIntros "!> _ !> !>". iExists (Some 1%Qp, None). do 2 (iSplit; [done|]).
        iExists t''. by iFrame (Lt'') "Cert". }
      iMod (WeakAuth_new_lock _ _ (q/2)%Qp with "WA") as "[WA WL]".
      iApply step_fupd_intro; [solve_ndisj|]. iNext.
      iDestruct "oW" as "[oW oW']". iSplitR "WA oW'"; last first.
      { iExists _. iFrame "WA". do 2 (iSplitL ""; [done|]). iExists _. by iFrame "oW'". }
      iFrame "SDA SD". iSplitL "".
      { iPureIntro. move => ? /elem_of_union [/MAX ->|/elem_of_singleton -> //].
        eapply Pos.lt_le_incl, Pos.le_lt_trans; [|apply Lt'']. done. }
      iDestruct (GPS_SWSharedWriter_Reader_update with "W' R") as "[W' R]".
      iFrame "oW WL W'". iExists _. by iFrame "R WU SeenU". }

    iIntros "!>" (b t' [] v') "(IW &_& [([%[%%]]&_&Q) | ([%[_ %]] &R'&Rs&_)])";
      last first.
    { (* CAS fail first *)
      subst b.
      iDestruct "Rs" as "(SDA & SD & oW)". rewrite 3!acq_embed_elim.
      clear Q Q1 Q2 R.
      iMod ("Hclose1" with "tok [SMA SDA WUA IW IS]") as "tok".
      { iApply (arc_inv_join with "SMA [SDA] WUA IS IW"). by iExists _. }
      iModIntro. wp_case. iApply "HΦ". iFrame "HP1". iExists _,_,_,_.
      iFrame "St tok SR SM SeenM". rewrite /StrDowns. iFrame "SD oW".
      iExists _,_. iFrame (MAX) "WR". }

    (* CAS success, we have all weak pointers! *)
    subst b v'. iDestruct "Q" as "(SDA & SD & %MAX1 & oW & WL & WW & WS)".
    iMod ("Hclose1" with "tok [SMA SDA WUA IW IS]") as "tok".
    { iApply (arc_inv_join with "SMA [SDA] WUA IS IW"). by iExists _. }

    clear Q Q1 Q2 R Vb DtA. iModIntro. wp_case. wp_bind (!ᵃᶜ _)%E.
    (* preparing to read *)
    iDestruct "SeenM" as (t4 v4) "[#SR4 MAX]". iDestruct "MAX" as %MAX4.
    iDestruct (GPS_SWSharedReader_Reader_update_max with "SR SR4") as "SR".
    iDestruct "WS" as (Ut) "(tokW & WR2 & WU & #SeenU)".
    iDestruct "SeenU" as (t5 v5) "[#SR5 MAX]". iDestruct "MAX" as %MAX5.
    iDestruct (GPS_SWSharedReader_Reader_update_max with "SR SR5") as "SR".

    (* opening invariant *)
    iMod (view_inv_acc_base_2 γi N with "[$INV $tok]") as "[tok VI]"; [done|].
    iDestruct "VI" as (Vb VR) "(VI & VR & #FR & Hclose1)".
    iMod (arc_inv_split with "VI") as "((SMA & SDA & WUA) & IS & IW)".
    iDestruct "SMA" as (Mt2) "SMA".
    iDestruct (StrongMoveAuth_agree with "[$SMA $SM]") as %?. subst Mt2.
    iDestruct "WUA" as (Ut') "WUA".
    iDestruct (WeakUpAuth_agree with "[$WUA $WU]") as %?. subst Ut'.
    set P : vProp :=
      (StrongTok γsw q ∗ StrMoves γsw q Mt ∗ P1 q ∗
       StrongMoveAuth γsw Mt ∗ WeakUpAuth γsw Ut ∗ view_tok γi (q / 2) ∗
       view_tok γi (1 / 2) ∗ VR)%I.
    set R : time → unitProtocol → vProp :=
      (λ t s, GPS_SWSharedReader l t s #1 1 γs ∗
          StrongMoveAuth γsw Mt ∗ WeakUpAuth γsw Ut ∗
          StrMoves γsw 1 Mt ∗ P1 1 ∗ view_tok γi 1%Qp ∗ VR)%I.
    set R' : time → unitProtocol → val → vProp :=
      (λ _ _ v'', ∃ z: Z, ⌜v'' = #z⌝)%I.
    iApply (GPS_SWRaw_SharedReader_Read_val_dealloc
              (strong_interp P1 (l >> 1) γi γw γsw) _ strong_noCAS P R R' #1
              with "[$SR $IS $St $SM $HP1 $SMA $WUA $tok $tokW $VR]");
              [solve_ndisj|..].
    { iIntros "!>" (t6 [] [_ Ext']). iSplit; last first.
      { iIntros  "!>" (v'). iSplit.
        - iIntros "#WI !>". iFrame "WI". iDestruct "WI" as (st) "[Eq1 _]".
          iExists _. by iFrame "Eq1".
        - iDestruct 1 as (st) "[#Eq1 WI]". iSplitR ""; [iExists _; by iFrame "WI"|].
          iExists _. by iFrame "Eq1". }
      iIntros "(St & SM & HP1 & SMA & WUA & tok & tokW & VR) SR". iSplit.
      - (* we read 1 here, we should be able to scrap the whole protocol *)
        iDestruct 1 as (st) "(Eq & SA & SI)".
        iDestruct "Eq" as %Eq. inversion Eq as [Eq1]. clear Eq.
        iDestruct (StrongTok_Auth_agree with "[$SA $St]") as %(q'&n&?&Eq'). subst st.
        iDestruct "SI" as "[$ SI]". iDestruct "SI" as (q'') "(Eq & HP2 & SI)".
        iDestruct "SI" as (Mt2 Dt2) "(tok' & SR' & SM' & #SeenM' & SD' & SeenD' & oW')".
        iDestruct "Eq" as %Eq''. simpl in Eq1.
        have ?: n = 1%positive by destruct n. subst n. simpl in Eq'. subst q'.
        iDestruct (GPS_SWSharedReaders_join with "SR' SR") as "SR'".
        iDestruct (StrMoves_agree with "[$SM $SM']") as %?. subst Mt2.
        iCombine "SM" "SM'" as "SM". iCombine "HP1" "HP2" as "HP".
        iCombine "tok" "tok'" as "tok".
        rewrite (bi.wand_entails _ _ (HPn _ _)) Qp.add_comm -Qp.div_add_distr Eq''.
        iCombine "tok" "tokW" as "tok". iDestruct ("FR" with "tok VR") as "#$".
        by iFrame "SR' SMA WUA SM HP tok VR".
      - (* it's impossible to read 1 with only F_read *)
        iDestruct 1 as (st) "(Eq & SI)".
        iDestruct "Eq" as %Eq. inversion Eq as [Eq1]. clear Eq.
        destruct st as [[q' []]|]; simpl in Eq1; [by exfalso..| |by exfalso].
        iDestruct "SI" as (t7 Ext7) "[Cert|Cert]".
        + iDestruct (StrongMoveAuth_Cert_include with "[$SMA $Cert]")
            as %Le7%elem_of_subseteq_singleton%MAX4. exfalso.
          apply (irreflexive_eq (R:=Pos.lt) t4 t4); [done|].
          eapply Pos.lt_le_trans; [|by apply Le7].
          eapply Pos.le_lt_trans; [|by apply Ext7].
          etrans; [|by apply Ext'].
          case decide; case decide; [done..| |]; clear; lia.
        + iDestruct (WeakUpAuth_Cert_include with "[$WUA $Cert]")
            as %Le7%elem_of_subseteq_singleton%MAX5. exfalso.
          apply (irreflexive_eq (R:=Pos.lt) t5 t5); [done|].
          eapply Pos.lt_le_trans; [|by apply Le7].
          eapply Pos.le_lt_trans; [|by apply Ext7].
          etrans; [|by apply Ext']. by case decide. }

    iIntros "!>" (t8 [] v8) "([_ Le] & Rs)". iDestruct "Le" as %Le.
    case (decide (v8 = #1)) => NEq.
    - subst v8. simpl.
      iDestruct "Rs" as "(str & WR' & SMA & WUA & SM & HP & tok & VR)".
      iDestruct ("Hclose1" with "VR tok") as "[#InVb >_]".
      iIntros "!>".
      iApply wp_hist_inv; [done|]. iIntros "#HINV".
      iMod (GPS_SWRaw_SharedWriter_revert with "WW WR2 IW") as "[WW IW]".
      iSpecialize ("IW" with "InVb").
      iMod (GPS_SWWriter_dealloc (weak_interp P2 l γi γs γsw) _ _ true
             with "HINV IW WW") as "[wk _]"; [done|].
      wp_let. wp_op. wp_let. wp_op. wp_bind (_ <-ʳᵉˡ _)%E.
      iApply (wp_write _ #(1) with "[wk]");
        [done|by iApply own_loc_na_own_loc|..].
      iIntros "!> wk". wp_let. iApply "HΦ". by iFrame "str wk HP".

    - iDestruct "Rs" as "((St & SM & HP & SMA & WUA & tok & tokW & VR) & Rs & SW & IS)".
      iMod ("Hclose1" with "VR tok [SMA SDA WUA IW IS]") as "tok".
      { iApply (arc_inv_join with "[SMA] SDA [WUA] IS IW"); by iExists _. }
      iModIntro. wp_let. iDestruct "Rs" as (z) "%". subst v8.
      wp_op. rewrite bool_decide_false; [|move =>?; exfalso; by subst z].
      iClear "FR". clear Vb R NEq P R'.

      wp_let. wp_op. wp_bind (_ <-ʳᵉˡ _)%E.
      (* bad luck, there are some other strong pointers.
        releasing the lock on the weak counter. Single-writers to the rescue! *)

      iMod (view_inv_acc_base γi N with "[$INV $tok]") as "[tok VI]"; [done|].
      iDestruct "VI" as (Vb) "[VI Hclose1]".
      iMod (arc_inv_split with "VI") as "((SMA & SDA & WUA) & IS & IW)".
      iMod (GPS_SWRaw_SharedWriter_revert with "WW WR2 IW") as "[WW IW]".
      iDestruct "SDA" as (DtA) "SDA".

      set Q : time → vProp :=
        (λ t'', StrongDownAuth γsw (DtA ∪ {[t'']}) ∗
                StrDowns γsw q ((Dt ∪ {[t']}) ∪ {[t'']}) ∗
                agown γsw (awk_n ((Some q, ε))))%I.
      iApply (GPS_SWRaw_SWWrite_rel (weak_interp P2 l γi γs γsw) _
              (weak_noCAS γsw) Q True%I
              (weak_interp P2 l γi γs γsw true (l>>1) γw t' tt #(-1)) _ tt tt
              _ #1 with "[$WW $IW WL WU SDA SD oW tokW]"); [done|solve_ndisj|..].
      { iSplitR ""; [|by iIntros "!> !> $"].
        iIntros (t'' Ext'') "!> W'". iDestruct 1 as ([iS st]) "(Eq & WA & WI)".
        iDestruct "Eq" as %Eq. inversion Eq as [Eq']. clear Eq.
        iDestruct (WeakAuth_strong with "[$WA $oW]") as %[qs ?]. subst iS.
        destruct st as [[[]|[? q'']| ]|]; [exfalso; by lia| |done|by exfalso].
        iMod (StrDowns_update _ _ _ {[t'']} with "[$SDA $SD]") as "(SDA & SD & Cert)".
        iModIntro. iSplitL "Cert".
        { iIntros "!> _ !>". iSplitL""; [done|]. iExists _. iFrame (Ext'') "Cert". }
        iDestruct "WI" as "[% WI]". subst qs. iDestruct "WI" as (q') "[Eq oW']".
        iDestruct (WeakAuth_lock_agree with "[$WA $WL]") as %Eq2.
        iMod (WeakAuth_unlock with "[$WA $WL]") as "WA".
        iDestruct "Eq" as %Eq''. rewrite -> Eq'' in Eq2. clear Eq''.
        apply Some_equiv_inj, Cinr_inj, pair_equiv_inj in Eq2 as
          [? Eq%to_agree_inj]. inversion Eq. subst q'.
        iCombine "oW" "oW'" as "oW". iModIntro. iSplitR "SDA SD oW"; [|by iFrame].
        iExists (Some 1%Qp, None). iSplitL""; [done|]. iFrame "WA".
        iSplitL""; [done|]. iDestruct (GPS_SWWriter_shared with "W'") as "[$ R']".
        iExists _. iFrame "tokW R' WU". iExists _,_. iFrame (MAX5) "SR5". }
      iIntros "!>" (t'') "(% & WW & IW & SDA & SD & oW)".
      iMod ("Hclose1" with "tok [SMA SDA WUA IW IS]") as "tok".
      { iApply (arc_inv_join with "SMA [SDA] WUA IS IW"); by iExists _. }
      iModIntro. wp_seq. iApply "HΦ". iFrame "HP".
      iExists _,_,_,_. iFrame "St tok SW SM SD oW". iSplitL "".
      + iExists _,_. iFrame (MAX4) "SR4".
      + iExists _,_. iFrame "WW".
        iPureIntro. move => ? /elem_of_union [/MAX1->|/elem_of_singleton -> //].
        by apply Pos.lt_le_incl.
  Qed.

  Lemma try_unwrap_full_spec {HPn : HP2} γi γs γw γsw l q tid :
    histN ## N → is_arc P1 P2 N γi γs γw γsw l -∗
    {{{ (∃ t, strong_arc t q l γi γs γw γsw) ∗ P1 q }}}
      try_unwrap_full [ #l] @ tid; ⊤
    {{{ (x : fin 3), RET #x ;
        match x : nat with
        (* No other reference : we get everything. *)
        | 0%nat => l ↦ #1 ∗ (l >> 1) ↦ #1 ∗ P1 1
        (* No other strong, but there are weaks : we get P1,
           plus the option to get a weak if we pay P2. *)
        | 1%nat => P1 1 ∗ fake_arc l γi γs γw γsw
        (* There are other strong : we get back what we gave at the first place. *)
        | _ (* 2 *) => (∃ t, strong_arc t q l γi γs γw γsw) ∗ P1 q
        end }}}.
  Proof.
    iIntros (?) "#INV !# * [HP HP1] HΦ". wp_lam. wp_bind (CAS _ _ _ _ _ _).
    (* preparing to CAS *)
    iDestruct "HP" as (t v Mt Dt) "(St & tok & SR & SM & #SeenM & SD & #SeenD & oW)".
    iMod (view_inv_acc_base γi N with "[$INV $tok]") as "[tok VI]"; [done|].
    iDestruct "VI" as (Vb) "[VI Hclose1]".
    iMod (arc_inv_split with "VI") as "((SMA & SDA & WUA) & IS & IW)".
    iDestruct "SMA" as (Mt') "SMA".
    iDestruct (StrongMoveAuth_agree with "[$SMA $SM]") as %?. subst Mt'.
    iDestruct "SeenM" as (t2 v2) "[#R MAX]". iDestruct "MAX" as %MAX.
    iDestruct (GPS_SWSharedReader_Reader_update_max with "SR R") as "SR".
    set Q: time → unitProtocol → vProp :=
      (λ t'' s'',
        StrongMoveAuth γsw (Mt ∪ {[t'']}) ∗
        StrMoves γsw 1%Qp (Mt ∪ {[t'']}) ∗
        ⌜∀ t' : time, t' ∈ (Mt ∪ {[t'']}) → t' ⊑ t''⌝ ∗
        GPS_SWSharedWriter l t'' ((): unitProtocol) #0 γs ∗
        ∃ q'', ⌜(q + q'')%Qp =1%Qp⌝ ∗ P1 q'' ∗ view_tok γi (q''/2) ∗
          GPS_SWSharedReader l t'' ((): unitProtocol) #0 q'' γs ∗
          (∃ Dt', StrDowns γsw q'' Dt' ∗ SeenActs γw (l >> 1) Dt') ∗
          agown γsw (awk_n ((Some q'', ε))))%I.
    set Q1: time → unitProtocol → vProp := (λ _ _, True)%I.
    set Q2: time → unitProtocol → vProp :=
      (λ tr sr, strong_interp P1 (l >> 1) γi γw γsw true l γs tr sr #1).
    set R: time → unitProtocol → lit → vProp :=
      (λ _ _ _, StrongTok γsw q ∗ StrongMoveAuth γsw Mt ∗ StrMoves γsw q Mt)%I.
    iMod (rel_True_intro tid) as "#rTrue".
    (* here comes the CAS *)
    iApply (GPS_SWRaw_SharedWriter_CAS_int_strong (strong_interp P1 (l >> 1) γi γw γsw) _
            strong_noCAS false _ _ _ 1 #0 _ _ _ q _
            True%I Q Q1 Q2 R _ Vb _ (↑histN) with "[$SR $IS St SMA SM rTrue]");
      [solve_ndisj|solve_ndisj|by left|by right|by left|..].
    { iSplitL "". { iIntros "!>!>" (??? _). by iApply arc_strong_interp_comparable. }
      iFrame "rTrue". rewrite /= -(bi.True_sep' (∀ _ (_ : unitProtocol), _)%I).
      iApply (rel_sep_objectively with "[$rTrue St SMA SM]").
      rewrite /StrongTok /StrMoves. iIntros "!>" (t' [] [_ Ext']). iSplit; last first.
      { iIntros (??) "!> !>". iSplit; iIntros "$ !>"; iFrame "SMA";
        rewrite /StrongTok /StrMoves; by iFrame. }
      iSplitL "". { by iIntros "!> $". } iIntros "_".
      iDestruct 1 as (st) "[>Eq [>SA SI]]".
      iDestruct (StrongTok_Auth_agree with "[$SA St]") as %(q'&n&EQ&Eq');
        [by rewrite /StrongTok|]. subst st. iDestruct "Eq" as %Eq.
      inversion Eq. subst n. simpl in Eq'. subst q'. clear Eq.
      iDestruct "SI" as "[$ SI]". iDestruct "SI" as (q'') "(>Eq'' & HP & SI)".
      iDestruct "Eq''" as %Eq''.
      iDestruct "SI" as (Mt' Dt') "(tok' & R & SM' & SeenM' & SD' & SeenD' & oW')".
      rewrite /StrMoves. iDestruct "SM'" as ">SM'".
      iDestruct (StrongMoveAuth_agree with "[$SMA SM']") as %?;
        [by rewrite /StrMoves|]. subst Mt'.
      iDestruct (StrMoves_fractional _ _ q q'' with "[SM SM']") as "SM";
        [rewrite /StrMoves; by iFrame "SM SM'"|]. rewrite Eq''.
      iModIntro. iExists (). iSplitL""; [done|]. iIntros (t'' Lt'') "W' _".
      iMod (StrMoves_update _ _ {[t'']} with "[$SMA $SM]") as "(SMA & SM & Cert)".
      iMod (StrongAuth_drop_last with "[$SA St]") as "SA"; [by rewrite /StrongTok|].
      iModIntro. iSplitL "Cert".
      { iIntros "!> _ !> !>". iExists (Some (q'', 1%positive)). iSplit; [done|].
        iExists t''. by iFrame (Lt'') "Cert". }
      iApply step_fupd_intro; [solve_ndisj|]. iIntros "!>".
      iSplitR "SA"; last first. { iExists None. by iFrame "SA". }
      iFrame "SMA SM". iSplitL "".
      { iPureIntro. move => ? /elem_of_union [/MAX ->|/elem_of_singleton ->//].
        eapply Pos.lt_le_incl, Pos.le_lt_trans; [|apply Lt''].
        etrans; [|apply Ext']. by case decide. }
      iDestruct (GPS_SWSharedWriter_Reader_update with "W' R") as "[$ R]".
      iExists q''. iFrame (Eq'') "HP tok' R oW'".
      iExists _. by iFrame "SD' SeenD'". }

    (* finally done with the CAS *)
    iIntros "!>" (b t' [] v') "(IS &_& [([% [% _]]&R'&Q) | ([% _] &R'&Rs&_)])";
      last first.
    { (* CAS failure case first *)
      subst b.
      iDestruct "Rs" as "(St & SMA & SM)". rewrite 3!acq_embed_elim.
      iMod ("Hclose1" with "tok [SMA SDA WUA IW IS]") as "tok".
      { iApply (arc_inv_join with "[SMA] SDA WUA IS IW"). by iExists _. }
      iModIntro. wp_case. iApply ("HΦ" $! 2%fin). simpl. iFrame "HP1".
      iExists _,_,_,_. rewrite /StrongTok. iFrame "St tok R'". rewrite /StrMoves.
      iFrame "SD SM SeenD oW". iExists _,_. iFrame (MAX) "R". }

    (* CAS success case *)
    subst b v'. iDestruct "Q" as "(SMA & SM & MAX & SW & Q)". clear Q Q1 Q2 R.
    iDestruct "Q" as (q'' Eq) "(HP2 & tok' & SR & SD' & oW')".
    iDestruct (GPS_SWSharedReaders_join with "R' SR") as "R'". rewrite Eq.
    iMod (GPS_SWRaw_SharedWriter_revert with "SW R' IS") as "[SW IS]".
    iMod ("Hclose1" with "tok [SMA SDA WUA IW IS]") as "tok".
    { iApply (arc_inv_join with "[SMA] SDA WUA IS IW"). by iExists _. }

    iCombine "HP1" "HP2" as "HP1". iCombine "oW" "oW'" as "oW".
    iDestruct "SD'" as (Dt') "[SD' SeenD']".
    iDestruct (StrDowns_join with "[$SD $SD']") as "SD".
    iCombine "SeenD" "SeenD'" as "SeenD'". iClear "SeenD".
    iDestruct (SeenActs_join with "SeenD'") as "SeenD".
    rewrite (bi.wand_entails _ _ (HPn _ _)) Eq.
    iAssert (SeenActs γs l (Mt ∪ {[t']}))%I with "[SW MAX]" as "#SeenM".
    { iExists _, _. iDestruct (GPS_SWWriter_Reader with "SW") as "$".
      by iFrame "MAX". } iClear "rTrue R MAX". clear Vb MAX t2 v2 t v.

    iModIntro. wp_case. wp_op. wp_bind (!ᵃᶜ_)%E.
    (* preparing to read *)
    iDestruct "SeenD" as (t v) "[#WR MAX]". iDestruct "MAX" as %MAX.
    iMod (view_inv_acc_base_2 γi N with "[$INV $tok]") as "[tok VI]"; [done|].
    iDestruct "VI" as (Vb VR) "(VI & VR & #FR & Hclose1)".
    iMod (arc_inv_split with "VI") as "((SMA & SDA & WUA) & IS & IW)".
    iDestruct "SDA" as (Dt2) "SDA".
    iDestruct (StrongDownAuth_agree with "[$SDA $SD]") as %?. subst Dt2.

    set P : vProp :=
      (StrongDownAuth γsw (Dt ∪ Dt') ∗
       view_tok γi (q / 2) ∗ view_tok γi (q'' / 2) ∗ VR)%I.
    set R : time → unitProtocol → vProp :=
      (λ _ _, view_tok γi 1%Qp ∗ VR)%I.
    set R' : time → unitProtocol → val → vProp :=
      (λ _ _ v'', (∃ z: Z, ⌜v'' = #z⌝) ∗ agown γsw (awk_n ((Some 1%Qp, ε))))%I.
    iApply (GPS_SWRaw_Reader_Read_val_dealloc (weak_interp P2 l γi γs γsw) _
              (weak_noCAS γsw) P R R' #1 with "[$WR $IW oW $SDA $tok $tok' $VR]");
           [solve_ndisj|..].
    { iIntros "!>" (t5 [] [_ Ext']). iSplit; last first.
      { iIntros "!>" (v'). iSplit; last iSplit.
        - iIntros "#WI !>". iFrame "WI oW". iDestruct "WI" as (st) "[Eq1 _]".
          iExists _. by iFrame "Eq1".
        - iDestruct 1 as (st) "[#Eq1 WI]". iFrame "oW".
          iSplitR ""; [iExists _; by iFrame "WI"|].
          iExists _. by iFrame "Eq1".
        - iIntros "[% F]". subst v'. iModIntro. iFrame "F oW".
          iSplitL""; [done|]. iPureIntro. by eexists.  }
      iIntros "(SDA & tok & tok' & VR)". iSplit; last iSplit.
      - iDestruct 1 as ([iS st] Eq') "[WA WI]". inversion Eq' as [Eq1]. clear Eq'.
        iDestruct (WeakAuth_strong with "[$WA $oW]") as %[qs ?]. subst iS.
        destruct st as [[[]| |]|].
        { exfalso. lia. } { by exfalso. } { by exfalso. }
        iDestruct "WI" as "(% & $ & WI)". iDestruct "WI" as (Ut) "(tokW&?&WU&?)".
        iCombine "tok" "tok'" as "tok". rewrite -Qp.div_add_distr Eq.
        iCombine "tok" "tokW" as "tok". iDestruct ("FR" with "tok VR") as "#$".
        iModIntro. by iFrame "tok VR".
      - iDestruct 1 as (st Eq') "[_ WI]". inversion Eq' as [Eq1]. clear Eq'.
        iAssert (∃ t6: time, ⌜(t5 < t6)%positive⌝ ∗ StrDownCert γsw t6)%I
          with "[WI]" as (t6 Lt6) "Cert".
        { destruct st as [[] [cs|]]; simpl in Eq1; [|done|..|done].
          - destruct cs as [[? c']| |]; [|done..]. by lia.
          - destruct cs as [[? c']| |]; [|done..]. by destruct c'. }
        iDestruct (StrongDownAuth_Cert_include with "[$SDA $Cert]")
          as %Lt%elem_of_subseteq_singleton%MAX.
        exfalso. apply (irreflexive_eq (R:=Pos.lt) t t); [done|].
        eapply Pos.lt_le_trans; [|apply Lt]. eapply Pos.le_lt_trans; [apply Ext'|done].
      - by iDestruct 1 as "[% _]". }

    iIntros "!>" (t2 [] v2) "([_ Le] & Rs)". iDestruct "Le" as %Le.
    case (decide (v2 = #1)) => NEq; last first.
    { simpl. iDestruct "Rs" as "((SDA & tok & tok' & VR) & Rs & WW & IW)".
      iMod ("Hclose1" with "VR tok [SMA SDA WUA IW IS]") as "tok".
      { iApply (arc_inv_join with "SMA [SDA] WUA IS IW"). by iExists _. }

      iDestruct "Rs" as "[Rs oW]". iDestruct "Rs" as (z) "%". subst v2.
      iModIntro. wp_op. rewrite bool_decide_false; [|move => ?; exfalso; by subst z].
      wp_case. iApply ("HΦ" $! 1%fin). simpl. iFrame "HP1".
      iCombine "tok" "tok'" as "tok". rewrite -Qp.div_add_distr Eq. iFrame "tok".
      iSplitL "SW"; [by iExists _|]. iSplitL "SM". { iExists _. iFrame "SM SeenM". }
      iFrame "oW". iExists _. iFrame "SD". iExists _, _. iFrame (MAX) "WR". }

    iDestruct "Rs" as "(wk & tok & VR)".
    iDestruct ("Hclose1" with "VR tok") as "[#InVb >_]".
    iModIntro. subst v2. wp_op. wp_case. wp_bind (_ <- _)%E.
    iApply wp_hist_inv; [done|]. iIntros "HInv".
    iSpecialize ("IS" with "InVb").
    iMod (GPS_SWWriter_dealloc (strong_interp P1 (l >> 1) γi γw γsw) _
              strong_noCAS true with "HInv IS SW") as "[str _]"; [done|..].
    wp_write. wp_seq. iApply ("HΦ" $! 0%fin). iFrame "str wk HP1".
  Qed.
End arc.

Global Typeclasses Opaque StrMoveCertS StrDownCertS WkUpCertS.
Global Typeclasses Opaque is_arc strong_arc weak_arc.
