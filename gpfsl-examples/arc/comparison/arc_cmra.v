From iris.base_logic.lib Require Import invariants.
From iris.proofmode Require Import tactics.
From iris.bi Require Import fractional.
From iris.algebra Require Import excl csum frac auth agree numbers.
From lrust.lang Require Import notation.
From gpfsl.gps Require Import middleware protocols.
From gpfsl.logic Require Import view_invariants.

From iris.prelude Require Import options.

(** The CMRAs we need. *)

(* This cmra tracks what the arc must have done by itself when it is the unique clone.

  Self here means that the cmra is updated when the caller moves its own counter,
  e.g. the strong arc modifying the strong counter, or the weak arc modifying
  the weak counter.
  For the strong counter, it tracks the actions: moving 1 to 0
  (the last release/drop), and 1 to 2 (the unique clone).
  For the weak counter, it tracks the self actions: moving 1 to -1 (locking),
  moving 1 to 0 (the last drop), and 1 to 2 (the unique clone).

  The authority should only be updated when having full fraction,
  i.e. the caller being unique. A persistent certificate is issued when the
  authority is updated. A fraction of the authority must have seen all certificates. *)
Definition move_selfUR :=
  prodUR (authUR (optionUR (prodR fracR (agreeR (latO (gset_Lat time))))))
        (authUR (latUR (gset_Lat time))).

(* This cmra tracks what the arc has asked the other to do, e.g., the weak arc
  asks the strong counter to increment when upgrading, or the strong arc asks
  the weak counter to increment when downgrading.

  The authority part is owned by the caller, and issue a certificate for
  the callee to store in its update. There can be multiple authorities,
  each is owned by one caller. A fraction of the authority can issue certificates,
  while only the full fraction authority is guaranteed to have seen all certificates. *)
Definition move_otherUR :=
  prodUR (authUR (optionUR (prodR fracR (latR (gset_Lat time)))))
        (authUR (latUR (gset_Lat time))).

(* This cmra tracks states of the weak counter:
  - (None, None) : no strong or weak arc, v = 0.
  - (None, Some Cinl (q,n)) : no strong arc, n weak arcs that use q permission,
    v = n.
  - (None, Some Cinr q) : no strong arc, no weak arc, the weak counter is locked
    with a payload of q from a strong arc, v = -1. This state is IMPOSSIBLE.
  - (Some 1, None) : some strong arcs, no weak arcs, v = 1.
  - (Some 1, Some Cinl (q,n)) : some strong arcs, n weak arcs that use q, v = S n.
  - (Some 1, Some Cinr q) : some strong arcs, no weak arc, the weak counter is
    locked with a payload of q from a strong arc, v = -1.
*)

Definition weak_stUR :=
  prodUR (optionUR fracR)
         (optionUR (csumR (prodR fracR positiveR) (prodR (exclR unitO) (agreeR fracO)))).

(* This cmra tracks states of the strong counter:
  - None: no strong arc, v = 0.
  - Some (q,n): n strong arcs that took out q, v = n. *)
Definition strong_stUR :=
  optionUR (prodR fracR positiveR).

(* The final cmra has 5 components
  (strong arc states, weak arc states),
  (strong arc self, strong arc downgrade),
  (weak arc upgrade) *)
Definition arcUR :=
  prodUR (prodUR (authUR strong_stUR) (authUR weak_stUR))
         (prodUR (prodUR move_selfUR move_otherUR) move_otherUR).

Class arcG Σ := {
  ArcStG : inG Σ arcUR;
  ArcPrt_gpsG : gpsG Σ unitProtocol;
  Arc_atomG : atomicG Σ;
  Arc_viewInvG : view_invG Σ;
}.
#[global] Existing Instances ArcStG ArcPrt_gpsG Arc_atomG Arc_viewInvG.

Definition arcΣ : gFunctors := #[GFunctor arcUR; gpsΣ unitProtocol; atomicΣ; view_invΣ].
Global Instance subG_arcΣ {Σ} : subG arcΣ Σ → arcG Σ.
Proof. solve_inG. Qed.

Definition Z_of_arcweak_st (st : weak_stUR) : Z :=
  match st with
  | (None, None) => 0
  | (Some _, None) => 1
  | (None, Some (Cinl (_, n))) => Zpos n
  | (Some _, Some (Cinl (_, n))) => Zpos n +1
  | (_, Some _) => -1
  end.

Definition Z_of_arcstrong_st (st : strong_stUR) : Z :=
  match st with
  | None => 0
  | Some (_, n) =>  Zpos n
  end.

Local Open Scope Z_scope.

Lemma strong_stUR_value st: 0 ≤ Z_of_arcstrong_st st.
Proof. destruct st as [[]|]; simpl; lia. Qed.

Lemma weak_stUR_value st: -1 ≤ Z_of_arcweak_st st.
Proof. destruct st as [[|] [[[]| |]|]]; simpl; lia. Qed.

Notation agown γ st := (⎡ own γ (st : arcUR) ⎤ : vProp _)%I.
Notation awk_n st   := ((ε, ◯ (st : weak_stUR)), ε).

Section ArcGhost.
  Context `{inG Σ arcUR}.
  Local Notation vProp := (vProp Σ).
  Implicit Types (Mt Ut Dt: gset time).

  Definition StrongAuth γ (st : strong_stUR) :=
    agown γ ((● st, ε), ε).
  Definition StrongTok γ q :=
    agown γ ((◯ Some (q, xH), ε), ε).
  Definition StrongMoveAuth γ Mt :=
    agown γ (ε, (((● Some (1%Qp, to_agree $ to_latT Mt), ● to_latT Mt) : move_selfUR, ε), ε)).
  Definition StrMoves γ (q: frac) Mt :=
    agown γ (ε, (((◯ Some (q, to_agree $ to_latT Mt), ε) : move_selfUR, ε), ε)).
  Definition StrongDownAuth γ Dt :=
    agown γ (ε, ((ε, (● Some (1%Qp, to_latT Dt), ● to_latT Dt) : move_otherUR), ε)).
  Definition StrDowns γ (q: frac) Dt :=
    agown γ (ε, ((ε, (◯ Some (q, to_latT Dt), ε) : move_otherUR), ε)).
  Definition StrMoveCertS γ Mt : vProp :=
    agown γ (ε, (((ε, ◯ to_latT Mt) : move_selfUR, ε), ε)).
  Definition StrDownCertS γ Mt : vProp :=
    agown γ (ε, ((ε, (ε, ◯ to_latT Mt) : move_otherUR), ε)).
  Definition StrMoveCert γ t := StrMoveCertS γ {[t : time]}.
  Definition StrDownCert γ t := StrDownCertS γ {[t : time]}.
  Definition StrWkTok γsw q := agown γsw (awk_n ((Some q, ε))).

  Definition WeakAuth γ (st : weak_stUR) :=
    agown γ ((ε, ● st), ε).
  Definition WeakTok γ q :=
    agown γ ((ε, ◯ (ε, Some (Cinl (q, xH)))), ε).
  Definition WeakUpAuth γ Ut :=
    agown γ (ε, (ε, (● Some (1%Qp, to_latT Ut), ● to_latT Ut) : move_otherUR)).
  Definition WkUps γ (q: frac) Ut :=
    agown γ (ε, (ε, (◯ Some (q, to_latT Ut), ε) : move_otherUR)).
  Definition WkUpCertS γ Mt :=
    agown γ (ε, (ε, (ε, ◯ to_latT Mt) : move_otherUR)).
  Definition WkUpCert γ t := WkUpCertS γ {[t : time]}.
  Definition WkLock γ q :=
    agown γ (ε, ◯ (ε, Some $ Cinr (Excl(), to_agree q)),ε) .

  Global Instance StrMoveCertS_persistent γ Mt : Persistent (StrMoveCertS γ Mt).
  Proof. apply embed_persistent, own_core_persistent, pair_core_id; by apply _. Qed.
  Global Instance StrDownCertS_persistent γ Mt : Persistent (StrDownCertS γ Mt).
  Proof. apply embed_persistent, own_core_persistent, pair_core_id; by apply _. Qed.
  Global Instance WkUpCertS_persistent γ Mt : Persistent (WkUpCertS γ Mt).
  Proof. apply embed_persistent, own_core_persistent, pair_core_id; by apply _. Qed.
  Global Instance StrMoves_fractional γ Mt : Fractional (λ q, StrMoves γ q Mt).
  Proof.
    rewrite /Fractional => p q. rewrite -embed_sep -own_op.
    apply embed_proper, own.own_proper.
    apply pair_proper; [done|]. do 3 (apply pair_proper; [|done]). simpl.
    by rewrite -auth_frag_op -Some_op -pair_op frac_op agree_idemp.
  Qed.
  Global Instance StrMoves_asfractional γ q Mt :
    AsFractional (StrMoves γ q Mt) (λ q, StrMoves γ q Mt) q.
  Proof. split; [done|apply _]. Qed.
  Global Instance StrDowns_fractional γ Dt : Fractional (λ q, StrDowns γ q Dt).
  Proof.
    rewrite /Fractional => p q. rewrite -embed_sep -own_op.
    apply embed_proper, own.own_proper.
    apply pair_proper; [done|]. apply pair_proper; [|done].
    rewrite /=. setoid_rewrite <-pair_op. apply pair_proper; [done|].
    rewrite -pair_op. apply pair_proper; [|done].
    by rewrite -auth_frag_op -Some_op -pair_op frac_op lat_op_join' lat_join_idem_L.
  Qed.
  Global Instance StrDowns_asfractional γ q Dt :
    AsFractional (StrDowns γ q Dt) (λ q, StrDowns γ q Dt) q.
  Proof. split; [done|apply _]. Qed.
  Global Instance WkUps_fractional γ Ut : Fractional (λ q, WkUps γ q Ut).
  Proof.
    rewrite /Fractional => p q. rewrite -embed_sep -own_op.
    apply embed_proper, own.own_proper.
    do 2 (apply pair_proper; [done|]).
    rewrite /=. setoid_rewrite <-pair_op. apply pair_proper; [|done].
    by rewrite -auth_frag_op -Some_op -pair_op frac_op lat_op_join' lat_join_idem_L.
  Qed.
  Global Instance WkUps_asfractional γ q Ut :
    AsFractional (WkUps γ q Ut) (λ q, WkUps γ q Ut) q.
  Proof. split; [done|apply _]. Qed.

  (* move_self *)
  Local Notation moveSAuth Mt
    := ((● Some (1%Qp, to_agree $ to_latT Mt), ● to_latT Mt) : move_selfUR).
  Local Notation moveSMain q Mt
    := ((◯ Some (q, to_agree $ to_latT Mt), ε) : move_selfUR).
  Local Notation certS Mt
    := ((ε, ◯ to_latT Mt) : move_selfUR).

  Lemma arc_ghost_move_self_main_valid Mt1 Mt2 q:
    ✓ (moveSAuth Mt1 ⋅ moveSMain q Mt2) → Mt2 = Mt1.
  Proof.
    rewrite -pair_op right_id.
    move => [/= /auth_both_valid_discrete [/Some_included
            [[_ /= /to_agree_inj /to_latT_inj /leibniz_equiv_iff //]|
              /prod_included[_ /to_agree_included /to_latT_inj /leibniz_equiv_iff //]]_]_].
  Qed.

  Lemma arc_ghost_move_self_cert_valid Mt1 Mt2:
    ✓ (moveSAuth Mt1 ⋅ certS Mt2) → Mt2 ⊆ Mt1.
  Proof. rewrite -pair_op => [[_ /auth_both_valid_discrete [/latT_included // _]]]. Qed.

  Lemma StrongMoveAuth_agree γ Mt q Mt':
    StrongMoveAuth γ Mt ∗ StrMoves γ q Mt' -∗ ⌜Mt = Mt'⌝.
  Proof.
    rewrite -embed_sep -own_op.
    iIntros "own". iDestruct (own_valid with "own") as %VALID. iPureIntro.
    move : VALID => [/=_ [/= ]]. rewrite -pair_op.
    move => [/= /arc_ghost_move_self_main_valid //].
  Qed.

  Lemma StrMoves_agree γ Mt Mt' q q':
    StrMoves γ q Mt ∗ StrMoves γ q' Mt' -∗ ⌜Mt = Mt'⌝.
  Proof.
    rewrite -embed_sep -own_op.
    iIntros "own". iDestruct (own_valid with "own") as %VAL. iPureIntro.
    move : VAL => [/=_ [/= [[VAL  _]_]_]]. move :VAL.
    rewrite /= -auth_frag_op -Some_op -pair_op auth_frag_valid.
    move => [_ /to_agree_op_inv /to_latT_inj /leibniz_equiv_iff // ].
  Qed.

  Lemma StrongMoveAuth_Cert_include γ Mt Mt':
    StrongMoveAuth γ Mt ∗ StrMoveCertS γ Mt' -∗ ⌜Mt' ⊆ Mt⌝.
  Proof.
    rewrite -embed_sep -own_op.
    iIntros "own". iDestruct (own_valid with "own") as %VALID. iPureIntro.
    move :VALID => [/= _ [/= ]]. rewrite -pair_op.
    move => [/= /arc_ghost_move_self_cert_valid //].
  Qed.

  Lemma StrMoves_update γ Mt Mt':
    StrongMoveAuth γ Mt ∗ StrMoves γ 1%Qp Mt ==∗
      StrongMoveAuth γ (Mt ∪ Mt') ∗ StrMoves γ 1%Qp (Mt ∪ Mt') ∗ StrMoveCertS γ Mt'.
  Proof.
    rewrite -3!embed_sep -3!own_op. iIntros "own".
    iMod (own_update with "own") as "$"; [|done].
    apply prod_update; simpl; [done|].
    apply prod_update; simpl; [|done].
    setoid_rewrite <-pair_op. rewrite /=.
    apply prod_update; simpl; [|done].
    rewrite /= -2!pair_op /= 2!right_id left_id.
    apply prod_update; simpl.
    - by apply auth_update, option_local_update, exclusive_local_update.
    - apply auth_update_alloc.
      rewrite -(right_id_L ε op (to_latT Mt')) -lat_op_join' cmra_comm.
      by apply op_local_update_discrete.
  Qed.

  (* move_other *)
  Local Notation moveOAuth Mt   := ((● Some (1%Qp, to_latT Mt), ● to_latT Mt) : move_otherUR).
  Local Notation moveOMain q Mt := ((◯ Some (q, to_latT Mt), ε) : move_otherUR).
  Local Notation certO Mt       := ((ε, ◯ to_latT Mt) : move_otherUR).

  Lemma arc_ghost_move_other_main_valid Mt1 Mt2:
    ✓ (moveOAuth Mt1 ⋅ moveOMain 1%Qp Mt2) → Mt2 = Mt1.
  Proof.
    rewrite -pair_op.
    move => [/= /auth_both_valid_discrete [/Some_included
              [[/= _ /to_latT_inj /leibniz_equiv_iff //]|
              /prod_included [/= /frac_included /= // _]]]].
  Qed.

  Lemma arc_ghost_move_other_cert_valid Mt1 Mt2:
    ✓ (moveOAuth Mt1 ⋅ certO Mt2) → Mt2 ⊆ Mt1.
  Proof.
    rewrite -pair_op right_id.
    move => [/= _ /auth_both_valid_discrete [/latT_included // ]].
  Qed.

  Lemma StrongDownAuth_agree γ Dt Dt':
    StrongDownAuth γ Dt ∗ StrDowns γ 1%Qp Dt' -∗ ⌜Dt = Dt'⌝.
  Proof.
    rewrite -embed_sep -own_op.
    iIntros "own". iDestruct (own_valid with "own") as %VALID. iPureIntro.
    move : VALID => [/=_ [/= [/= _ /arc_ghost_move_other_main_valid //]]].
  Qed.

  Lemma StrongDownAuth_Cert_include γ Dt Dt':
    StrongDownAuth γ Dt ∗ StrDownCertS γ Dt' -∗ ⌜Dt' ⊆ Dt⌝.
  Proof.
    rewrite -embed_sep -own_op.
    iIntros "own". iDestruct (own_valid with "own") as %VALID. iPureIntro.
    move :VALID => [/= _ [/= [/= _ /arc_ghost_move_other_cert_valid //]]].
  Qed.

  Lemma StrDowns_forget γ q q' Dt Dt':
    StrDowns γ (q + q')%Qp (Dt ∪ Dt') ≡
    (StrDowns γ q (Dt ∪ Dt') ∗ StrDowns γ q' Dt')%I.
  Proof.
    rewrite -embed_sep -own_op. apply embed_proper, own.own_proper.
    do 2 (apply pair_proper; [done|]; apply pair_proper; [|done]).
    simpl. rewrite -auth_frag_op -Some_op -pair_op -frac_op lat_op_join'.
    rewrite (lat_le_join_l_L (Dt ∪ Dt') Dt'); [done|solve_lat].
  Qed.

  Lemma WeakUpAuth_agree γ Ut Ut':
    WeakUpAuth γ Ut ∗ WkUps γ 1%Qp Ut' -∗ ⌜Ut = Ut'⌝.
  Proof.
    rewrite -embed_sep -own_op.
    iIntros "own". iDestruct (own_valid with "own") as %VALID. iPureIntro.
    move : VALID => [/=_ [/= _  /arc_ghost_move_other_main_valid //]].
  Qed.

  Lemma WeakUpAuth_Cert_include γ Ut Ut':
    WeakUpAuth γ Ut ∗ WkUpCertS γ Ut' -∗ ⌜Ut' ⊆ Ut⌝.
  Proof.
    rewrite -embed_sep -own_op.
    iIntros "own". iDestruct (own_valid with "own") as %VALID. iPureIntro.
    move :VALID => [/= _ [/= _ /arc_ghost_move_other_cert_valid //]].
  Qed.

  Lemma WkUps_forget γ q q' Ut Ut':
    WkUps γ (q + q')%Qp (Ut ∪ Ut') ≡
    (WkUps γ q (Ut ∪ Ut') ∗ WkUps γ q' Ut')%I.
  Proof.
    rewrite -embed_sep -own_op. apply embed_proper, own.own_proper.
    do 2 (apply pair_proper; [done|]). apply pair_proper; [|done]. simpl.
    rewrite -auth_frag_op -Some_op -pair_op -frac_op lat_op_join'.
    rewrite (lat_le_join_l_L (Ut ∪ Ut') Ut'); [done|solve_lat].
  Qed.

  Lemma StrDowns_join γ Dt Dt' q q' :
    StrDowns γ (q + q')%Qp (Dt ∪ Dt') ≡
    (StrDowns γ q Dt ∗ StrDowns γ q' Dt')%I.
  Proof.
    rewrite -embed_sep -own_op. apply embed_proper, own.own_proper.
    do 2 (apply pair_proper; [done|]; apply pair_proper; [|done]).
    simpl. by rewrite -auth_frag_op -Some_op -pair_op -frac_op lat_op_join'.
  Qed.

  Lemma StrDowns_update γ Dt1 Dt2 Dt' q :
    StrongDownAuth γ Dt1 ∗ StrDowns γ q Dt2 ==∗
      StrongDownAuth γ (Dt1 ⊔ Dt') ∗ StrDowns γ q (Dt2 ⊔ Dt') ∗ StrDownCertS γ Dt'.
  Proof.
    rewrite -3!embed_sep -3!own_op. iIntros "own".
    iMod (own_update with "own") as "$"; [|done].
    apply prod_update; simpl; [done|].
    apply prod_update; simpl; [|done].
    setoid_rewrite <-pair_op. rewrite /=.
    apply prod_update; simpl; [done|].
    rewrite /= -2!pair_op /= 2!right_id left_id. rewrite -2!lat_op_join'.
    apply prod_update; simpl.
    - apply auth_update, option_local_update, prod_local_update_2.
      rewrite (cmra_comm_L (to_latT Dt1)) (cmra_comm_L (to_latT Dt2)).
      by apply op_local_update_discrete.
    - apply auth_update_alloc.
      rewrite cmra_comm_L -{2}(right_id_L ε op (to_latT Dt')).
      by apply op_local_update_discrete.
  Qed.

  Lemma WkUps_join γ Ut Ut' q q' :
    WkUps γ (q + q')%Qp (Ut ∪ Ut') ≡
    (WkUps γ q Ut ∗ WkUps γ q' Ut')%I.
  Proof.
    rewrite -embed_sep -own_op. apply embed_proper, own.own_proper.
    by do 3 (apply pair_proper; simpl; [done|]).
  Qed.

  Lemma WkUps_full_exclusive γ q Ut' :
    (∃ Ut, WkUps γ 1%Qp Ut) -∗ WkUps γ q Ut' -∗ False.
  Proof.
    iDestruct 1 as (Ut) "WU". iIntros "WU'".
    iDestruct (WkUps_join with "[$WU $WU']") as "WU".
    iDestruct (@own_valid _ arcUR with "WU")
      as %[_ [_ [[VAL _]%auth_frag_valid_1 _]]].
    iPureIntro. simpl in VAL.
    have Lt: (1 < 1 + q)%Qp. { apply Qp.lt_sum. by eexists. }
    apply (irreflexive_eq (R:= Qp.lt) 1%Qp 1%Qp); [done|].
    eapply Qp.lt_le_trans; [apply Lt|done].
  Qed.

  Lemma WkUps_update γ Ut1 Ut2 Ut' q :
    WeakUpAuth γ Ut1 ∗ WkUps γ q Ut2 ==∗
      WeakUpAuth γ (Ut1 ⊔ Ut') ∗ WkUps γ q (Ut2 ⊔ Ut') ∗ WkUpCertS γ Ut'.
  Proof.
    rewrite -3!embed_sep -3!own_op. iIntros "own".
    iMod (own_update with "own") as "$"; [|done].
    apply prod_update; simpl; [done|].
    apply prod_update; simpl; [done|].
    apply prod_update; rewrite /=.
    - apply auth_update, option_local_update, prod_local_update_2.
      rewrite -2!lat_op_join' (cmra_comm_L (to_latT Ut1)) (cmra_comm_L (to_latT Ut2)).
      by apply op_local_update_discrete.
    - rewrite -lat_op_join' right_id left_id. apply auth_update_alloc.
      rewrite cmra_comm_L -{2}(right_id_L ε op (to_latT Ut')).
      by apply op_local_update_discrete.
  Qed.

  Lemma StrongTok_Auth_agree γ st q :
    StrongAuth γ st ∗ StrongTok γ q -∗
    ⌜∃ q' strong, st = Some (q', strong) ∧
        if decide (strong = xH) then q = q' else ∃ q'', q' = (q + q'')%Qp⌝.
  Proof.
    rewrite -embed_sep -own_op. iIntros "oA".
    iDestruct (own_valid with "oA")
      as %[[[[|INCL]%option_included _]%auth_both_valid_discrete _] _]; [done|].
    iPureIntro. destruct INCL as [q1 [[q' n] [Eq1 [Eq2 Eq3]]]].
    inversion Eq1. subst q1. exists q', n. split; [done|].
    destruct Eq3 as [[Eq3 Eq4]|[[q'' Le1] Le2%pos_included]%prod_included].
    - inversion Eq3. inversion Eq4. simpl in *. by subst.
    - simpl in *. rewrite decide_False.
      + exists q''. by rewrite Le1 frac_op.
      + move => ?. by subst n.
  Qed.

  Lemma WeakTok_Auth_agree γ st q :
    WeakAuth γ st ∗ WeakTok γ q -∗
    ⌜∃ q' weak isStr, st = (isStr, Some $ Cinl (q', weak)) ∧
        if decide (weak = xH) then q = q' else ∃ q'', q' = (q + q'')%Qp⌝.
  Proof.
    rewrite -embed_sep -own_op. iIntros "oA".
    iDestruct (own_valid with "oA")
      as %[[_ [[_ INCL]%prod_included VALID]%auth_both_valid_discrete] _].
    iPureIntro. destruct st as [st' st]. simpl in *.
    apply option_included in INCL as [|[q1 [qn [Eq1 [Eq2 Eq3]]]]]; [done|].
    subst st. inversion Eq1. subst q1. destruct Eq3 as [Eq3|INCL].
    - exists q, xH, st'. inversion Eq3 as [? ? Eq4| |]. subst.
       apply leibniz_equiv_iff in Eq4. by subst.
    - destruct VALID as [? ?]. simpl in *.
      apply csum_included in INCL as [?|[([??]&[q' weak]&Eq2&?&INCL)|(?&?&?&?)]];
        [by subst qn|..|done].
      subst qn. exists q', weak, st'. split; [done|]. inversion Eq2. subst.
      apply prod_included in INCL as [[q'' Eq] INCLs%pos_included]. simpl in *.
      rewrite decide_False.
      + exists q''. by rewrite Eq frac_op.
      + move => ?. by subst weak.
  Qed.

  Lemma StrongAuth_first_tok γ :
    StrongAuth γ None ==∗
    StrongAuth γ (Some ((1/2)%Qp, 1%positive)) ∗ StrongTok γ (1/2)%Qp.
  Proof.
    iIntros "own". rewrite -embed_sep -own_op.
    iMod (@own_update _ arcUR with "own") as "$"; [|done].
    apply prod_update; simpl; [|done].
    apply prod_update; simpl; [|done]. apply auth_update_alloc.
    rewrite /= -(right_id None op (Some _)). by apply: op_local_update_discrete.
  Qed.

  Lemma StrongAuth_new_tok γ (q q': frac) n (Hqq' : (q + q')%Qp = 1%Qp):
    StrongAuth γ (Some (q,n)) ==∗
    StrongAuth γ (Some ((q + q'/2)%Qp, (n + 1)%positive)) ∗
    StrongTok γ (q'/2)%Qp.
  Proof.
    iIntros "own". rewrite -embed_sep -own_op.
    iMod (@own_update _ arcUR with "own") as "$"; [|done].
    apply prod_update; simpl; [|done].
    apply prod_update; simpl; [|done]. apply auth_update_alloc.
    rewrite Pos.add_comm Qp.add_comm -pos_op_add /= -frac_op pair_op Some_op.
    rewrite -{2}(right_id None op (Some ((q' /2)%Qp, _))).
    apply op_local_update_discrete => _ /=. split; simpl; [|done].
    apply frac_valid. rewrite -Hqq' comm -{2}(Qp.div_2 q').
    apply Qp.add_le_mono_l. apply Qp.le_add_r.
  Qed.

  Lemma WeakAuth_first_tok γ iS :
    WeakAuth γ (iS, None) ==∗
    WeakAuth γ (iS, Some $ Cinl ((1/2)%Qp, 1%positive)) ∗ WeakTok γ (1/2)%Qp.
  Proof.
    iIntros "own". rewrite -embed_sep -own_op.
    iMod (@own_update _ arcUR with "own") as "$"; [|done].
    apply prod_update; simpl; [|done].
    apply prod_update; simpl; [done|]. apply auth_update_alloc.
    apply prod_local_update; simpl; [done|].
    rewrite /= -(right_id None op (Some _)). by apply op_local_update_discrete.
  Qed.

  Lemma WeakAuth_new_tok γ iS (q q': frac) n (Hqq' : (q + q')%Qp = 1%Qp):
    WeakAuth γ (iS, Some (Cinl (q, n))) ==∗
    WeakAuth γ (iS, Some (Cinl ((q + q'/2)%Qp, (n + 1)%positive))) ∗
    WeakTok γ (q'/2)%Qp.
  Proof.
    iIntros "own". rewrite -embed_sep -own_op.
    iMod (@own_update _ arcUR with "own") as "$"; [|done].
    apply prod_update; simpl; [|by rewrite right_id].
    apply prod_update; simpl; [done|]. apply auth_update_alloc.
    apply prod_local_update; simpl; [done|].
    rewrite Pos.add_comm Qp.add_comm -pos_op_add /=
            -frac_op pair_op Cinl_op Some_op.
    rewrite -{2}(right_id None op (Some $ Cinl ((q' /2)%Qp, _))).
    apply op_local_update_discrete => _ /=. split; simpl; [|done].
    apply frac_valid. rewrite -Hqq' comm -{2}(Qp.div_2 q').
    apply Qp.add_le_mono_l. apply Qp.le_add_r.
  Qed.

  Lemma StrongAuth_drop_last γ q:
    StrongAuth γ (Some (q,1%positive)) ∗ StrongTok γ q ==∗
    StrongAuth γ None.
  Proof.
    rewrite -embed_sep -own_op. iIntros "own".
    iMod (@own_update _ arcUR with "own") as "$"; [|done].
    apply prod_update; simpl; [|by rewrite right_id].
    apply prod_update; simpl; [|done].
    apply auth_update_dealloc. rewrite /= -(right_id None op (Some _)).
    apply: cancel_local_update_unit.
  Qed.

  Lemma StrongAuth_drop γ q q' n:
    StrongAuth γ (Some ((q + q')%Qp,(1 + n)%positive)) ∗ StrongTok γ q' ==∗
    StrongAuth γ (Some (q,n)).
  Proof.
    rewrite -embed_sep -own_op. iIntros "own".
    iMod (@own_update _ arcUR with "own") as "$"; [|done].
    apply prod_update; [|simpl; by rewrite right_id].
    apply prod_update; simpl; [|done].
    apply auth_update_dealloc.
    rewrite -frac_op -pos_op_add /= (cmra_comm_L q) pair_op Some_op.
    by apply (cancel_local_update_unit (Some _)), _.
  Qed.

  Lemma WeakAuth_drop_last γ iS q:
    WeakAuth γ (iS, Some $ Cinl (q,1%positive)) ∗ WeakTok γ q ==∗
    WeakAuth γ (iS, None).
  Proof.
    rewrite -embed_sep -own_op. iIntros "own".
    iMod (@own_update _ arcUR with "own") as "$"; [|done].
    apply prod_update; [|by rewrite /= right_id]. apply prod_update; simpl; [done|].
    apply auth_update_dealloc. apply prod_local_update; [done|].
    rewrite /= -(right_id None op (Some _)). apply: cancel_local_update_unit.
  Qed.

  Lemma WeakAuth_drop γ iS (q q': frac) n:
    WeakAuth γ (iS, Some (Cinl ((q + q')%Qp,(1 + n)%positive))) ∗
    WeakTok γ q' ==∗
    WeakAuth γ (iS, Some (Cinl (q,n))).
  Proof.
    rewrite -embed_sep -own_op. iIntros "own".
    iMod (@own_update _ arcUR with "own") as "$"; [|done].
    apply prod_update; [|simpl; by rewrite right_id]. apply prod_update; simpl; [done|].
    apply auth_update_dealloc. apply prod_local_update; [done|].
    rewrite -frac_op -pos_op_add /= (cmra_comm_L q) pair_op Cinl_op Some_op.
    by apply (cancel_local_update_unit (Some _)), _.
  Qed.

  Lemma WeakAuth_strong γ iS st q :
    WeakAuth γ (iS, st) ∗ agown γ (awk_n ((Some q, ε))) -∗ ∃ q', ⌜iS = Some q'⌝.
  Proof.
    rewrite -embed_sep -own_op. iIntros "own".
    iDestruct (own_valid with "own") as %[[_ [VAL _]%auth_both_valid_discrete] _].
    iPureIntro. move : VAL => /prod_included /= [/option_included [//|[?[? [?[??]]]]] _].
    subst iS. by eexists.
  Qed.

  Lemma WeakAuth_valid γ iS st :
    WeakAuth γ (iS, st) -∗ ⌜st ≠ Some CsumBot⌝.
  Proof.
    iIntros "own".
    iDestruct (@own_valid _ arcUR with "own") as %[[_ Hvl] _].
    iPureIntro. move : Hvl. rewrite auth_auth_valid => [[_ ?]].
    by destruct st as [[| |]|].
  Qed.

  Lemma WeakAuth_drop_strong γ st:
    WeakAuth γ (Some 1%Qp, st) ∗ agown γ (awk_n ((Some 1%Qp, ε))) ==∗
    WeakAuth γ (None, st).
  Proof.
    rewrite -embed_sep -own_op. iIntros "own".
    iMod (@own_update _ arcUR with "own") as "$"; [|done].
    apply prod_update; [|by rewrite /= right_id]. apply prod_update; simpl; [done|].
    apply auth_update_dealloc. apply prod_local_update; [|done].
    rewrite /= -{1}(right_id None op (Some _)).
    by apply (cancel_local_update_unit (Some _)), _.
  Qed.

  Lemma StrWkTok_exclusive γ q :
    agown γ (awk_n ((Some 1%Qp, ε))) ∗ agown γ (awk_n ((Some q, ε))) -∗ False.
  Proof.
    rewrite -embed_sep -own_op. iIntros "own".
    iDestruct (@own_valid _ arcUR with "own") as %[[_ VAL] _]. simpl in VAL.
    iPureIntro. move : VAL. rewrite -auth_frag_op -pair_op -Some_op frac_op.
    move => /auth_frag_valid /= [/= ? _].
    have Lt: (1 < 1 + q)%Qp. { apply Qp.lt_sum. by eexists. }
    apply (irreflexive_eq (R:= Qp.lt) 1%Qp 1%Qp); [done|].
    eapply Qp.lt_le_trans; [apply Lt|done].
  Qed.

  Lemma StrMoves_full_exclusive γ q Mt' :
    (∃ Mt, StrMoves γ 1%Qp Mt) -∗ StrMoves γ q Mt' -∗ False.
  Proof.
    iDestruct 1 as (Mt) "SM". iIntros "SM'".
    iDestruct (StrMoves_agree with "[$SM $SM']") as %?. subst Mt'.
    iDestruct (StrMoves_fractional with "[$SM $SM']") as "SM".
    iDestruct (@own_valid _ arcUR with "SM") as %[_ [[[[VAL _]%auth_frag_valid_1 _] _] _]].
    iPureIntro. simpl in VAL.
    have Lt: (1 < 1 + q)%Qp. { apply Qp.lt_sum. by eexists. }
    apply (irreflexive_eq (R:= Qp.lt) 1%Qp 1%Qp); [done|].
    eapply Qp.lt_le_trans; [apply Lt|done].
  Qed.

  Lemma WeakAuth_new_lock γ iS q:
    WeakAuth γ (iS, None) ==∗
    WeakAuth γ (iS, Some $ Cinr (Excl (), to_agree q)) ∗ WkLock γ q.
  Proof.
    rewrite -embed_sep -own_op. iIntros "own".
    iMod (@own_update _ arcUR with "own") as "$"; [|done].
    apply prod_update; [|by rewrite /= right_id]. apply prod_update; simpl; [done|].
    apply auth_update_alloc. apply prod_local_update; simpl; [done|].
    rewrite -(right_id None op (Some _)).
    by apply op_local_update_discrete.
  Qed.

  Lemma WeakAuth_lock_agree γ iS st q:
    WeakAuth γ (iS, st) ∗ WkLock γ q -∗
    ⌜st ≡ Some (Cinr (Excl tt, to_agree q))⌝.
  Proof.
    rewrite -embed_sep -own_op. iIntros "own".
    iDestruct (@own_valid _ arcUR with "own")
      as %[[_ [[_ [?|INCL]%option_included]%prod_included [_ VAL]]%auth_both_valid_discrete] _];
      [done|]. iPureIntro.
    destruct INCL as (x & y & Eq1 & Eq2 & INCL). simpl in *. inversion Eq1.
    subst x st. destruct INCL as [Eq|INCL].
    - inversion Eq as [|? b Eq2 |]. subst. by rewrite -Eq2.
    - apply csum_included in INCL as [?|[(?&?&?&?)|(?&[u v]&Eq&?&[IN1 IN2]%prod_included)]];
        [by subst y|done|..].
      subst. inversion Eq. clear Eq. subst.
      move : VAL => [VAL1 /to_agree_uninj [? VAL2]]. destruct u as [[]|]; [|done].
      simpl in *. move : IN2. rewrite -VAL2. move => /to_agree_included <- //.
  Qed.

  Lemma WeakAuth_unlock γ iS st q :
    WeakAuth γ (iS, st) ∗ WkLock γ q ==∗ WeakAuth γ (iS, None).
  Proof.
    iIntros "own". iDestruct (WeakAuth_lock_agree with "own") as %Eq.
    rewrite -embed_sep -own_op.
    iMod (@own_update _ arcUR with "own") as "$"; [|done].
    apply prod_update; [|by rewrite /= right_id]. apply prod_update; simpl; [done|].
    rewrite Eq. apply auth_update_dealloc. apply prod_local_update; [done|].
    rewrite /= -{1}(right_id None op (Some _)).
    apply (cancel_local_update_unit (Some _)), _.
  Qed.
End ArcGhost.
