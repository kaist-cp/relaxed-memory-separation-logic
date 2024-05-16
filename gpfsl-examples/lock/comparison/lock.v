From iris.proofmode Require Import tactics.
From iris.algebra Require Import excl.
From lrust.lang Require Import notation.
From gpfsl.gps Require Import middleware protocols.
From lrust.logic Require Import gps.
From lrust.lifetime Require Import at_borrow.

From iris.prelude Require Import options.

Definition mklock_unlocked : val := λ: ["l"], "l" <- #false.
Definition mklock_locked : val := λ: ["l"], "l" <- #true.
(* If the CAS fails, it's a relaxed-read.
   If the CAS succeeds, it's a acq-read and relaxed-write *)
Definition try_acquire : val := λ: ["l"], CAS "l" #false #true Relaxed AcqRel Relaxed.
Definition acquire : val :=
  rec: "acquire" ["l"] := if: try_acquire ["l"] then #☠ else "acquire" ["l"].
Definition release : val := λ: ["l"], "l" <-ʳᵉˡ #false.

Class lockG Σ := LockG {
  lock_gpsG : gpsG Σ unitProtocol;
  lock_atomG : atomicG Σ;
}.
#[global] Existing Instances lock_gpsG lock_atomG.

Definition lockΣ : gFunctors := #[gpsΣ unitProtocol; atomicΣ].

Global Instance subG_lockΣ {Σ} : subG lockΣ Σ → lockG Σ.
Proof. solve_inG. Qed.

Section proof.
  Context `{!noprolG Σ, !lftG Σ view_Lat lft_userE, !lockG Σ}.

  Implicit Types (l : loc).
  Local Notation vProp := (vProp Σ).

  Definition lock_interp (R : vProp) : interpO Σ unitProtocol :=
    (λ pb _ _ _ _ v, ∃ b : bool, ⌜v = #b⌝ ∗
                 if pb then (if b then True else R) else True)%I.

  Definition lock_proto N l γ κ (R : vProp): vProp :=
    (∃ R0, □ (R ↔ R0) ∗ ∃ t v, GPS_aPP N (lock_interp R0) l κ t () v γ)%I.

  Global Instance lock_proto_ne N l γ κ: NonExpansive (lock_proto N l γ κ).
  Proof. solve_proper. Qed.
  Global Instance lock_proto_persistent N l γ κ R:
    Persistent (lock_proto N l γ κ R) := _.

  Lemma lock_proto_lft_mono N l γ κ κ' R:
    κ' ⊑ κ -∗ lock_proto N l γ κ R -∗ lock_proto N l γ κ' R.
  Proof.
    iIntros "#Hincl". iDestruct 1 as (R0) "[#Eq Hproto]".
    iDestruct "Hproto" as (t v) "Hproto".
    iExists R0. iFrame "Eq". iExists t, v. by iApply GPS_aPP_lft_mono.
  Qed.

  Lemma lock_proto_iff N l γ κ R R' :
    □ (R ↔ R') -∗ lock_proto N l γ κ R -∗ lock_proto N l γ κ R'.
  Proof.
    iIntros "#Eq1". iDestruct 1 as (R0) "[#Eq2 PP]".
    iExists R0. iFrame "PP".
    iIntros "!#". iSplit; iIntros "?".
    - iApply "Eq2". by iApply "Eq1".
    - iApply "Eq1". by iApply "Eq2".
  Qed.

  Lemma lock_proto_iff_proper N l γ κ R R' :
    □ (R ↔ R') -∗ □ (lock_proto N l γ κ R ↔ lock_proto N l γ κ R').
  Proof.
    iIntros "#HR !#".
    iSplit; iIntros "Hlck"; iApply (lock_proto_iff with "[HR] Hlck"); [done|].
    iModIntro; iSplit; iIntros; by iApply "HR".
  Qed.

  Lemma lock_interp_comparable l γ t s v R:
    lock_interp R true l γ t s v ∨ lock_interp R false l γ t s v
    -∗ ⌜∃ vl : lit, v = #vl ∧ lit_comparable (Z_of_bool false) vl⌝.
  Proof.
    iDestruct 1 as "[F|F]"; iDestruct "F" as (b) "[% _]"; subst v; iExists b;
      iPureIntro; (split; [done|by constructor]).
  Qed.

  Lemma lock_interp_false l γ t s v R b:
    lock_interp R b l γ t s v -∗ □ lock_interp R false l γ t s v.
  Proof. iDestruct (1) as (b') "[#Eq _]". iExists b'. iFrame "Eq". Qed.

  (** The main proofs. *)
  Lemma lock_proto_create N l q κ (R : vProp) E
    (DISJ: N ## lftN) (SUB: ↑lftN ⊆ E) (histN_lft_userE : ↑histN ⊆ lft_userE):
    ⎡ lft_ctx ⎤ -∗ (q).[κ] -∗ ▷ ⎡ hist_inv ⎤ -∗
    &{κ}(∃ b: bool, l ↦ #b) -∗ ▷ R ={E}=∗
      (q).[κ] ∗ ∃ γ, lock_proto N l γ κ R.
  Proof.
    iIntros "#LFT Htok #HINV Hl R".
    iMod (bor_acc_cons with "LFT Hl Htok") as "[Hl Hclose]"; first done.
    iMod ("Hclose" $! (∃ v, l ↦ v ∗ ⌜∃ b: bool, v = #b⌝)%I with "[] [Hl]")
      as "[Hl Htok]".
    { iIntros "!>". iDestruct 1 as (v) "[Hl >Eq]". iDestruct "Eq" as (b) "%".
       subst v. by iExists _. }
    { iDestruct "Hl" as (b) "Hl". iExists _. iFrame. by iExists _. }
    iMod (GPS_aPP_Init N (lock_interp R) l κ () q (λ v, ⌜∃ b : bool, v = #b⌝)%I
          with "LFT Htok HINV Hl [R] []") as "[$ Hproto]"; [done|done|done|..].
    { iIntros (t γ v) "#Eqb". iDestruct "Eqb" as (b) "Eqb". iExists b.
      iFrame "Eqb". by destruct b. }
    { iIntros "!>" (??? v). iDestruct 1 as (b) "[? ?]". by iExists _. }
    iDestruct "Hproto" as (γ t v) "Hproto".
    iModIntro. iExists γ, R. iSplit; [|by iExists _, _].
    iIntros "!#". by iApply (bi.iff_refl True%I).
  Qed.

  (* At this point, it'd be really nice to have some sugar for symmetric
     accessors. *)
  Lemma try_acquire_spec N l γ κ R q tid E
    (DISJ: histN ## N) (SUB1: ↑N ⊆ E) (SUB2 :↑lftN ⊆ E) (SUB3: ↑histN ⊆ E) :
    ⎡ lft_ctx ⎤ -∗
    {{{ lock_proto N l γ κ R ∗ (q).[κ] }}} try_acquire [ #l ] @ tid; E
    {{{ b, RET #b; (if b is true then R else True) ∗ (q).[κ] }}}.
  Proof.
    iIntros "#LFT !#" (Φ) "[#Hproto Htok] HΦ". wp_rec.
    iDestruct "Hproto" as (R0) "[#Eq Hproto]".
    iDestruct "Hproto" as (t v) "PP".
    iMod (rel_True_intro tid) as "#rTrue".
    iApply (GPS_aPP_CAS_int_simple N (lock_interp R0) l κ q t () _
                (Z_of_bool false) #true _ _ _ γ True%I (λ _ _, R0)%I
                (λ t _, lock_interp R0 false l γ t () #false)
                (λ _ _, R0)%I (λ _ _ _, True)%I
      with "[$LFT $PP $Htok]");
      [done|done|solve_ndisj|done|by left|by right|by left|..].
    { iSplitL ""; [iNext; iModIntro..|].
      - iIntros (??? _). by iApply lock_interp_comparable.
      - simpl. iFrame "rTrue". rewrite /= -(bi.True_sep' (∀ _, _)%I).
        iApply (rel_sep_objectively with "[$rTrue]").
        iModIntro. iIntros (t' [] [_ Ext]). iSplit; last first.
        { iIntros "!>" (?) "? !>". by iSplit; iIntros "$". } iSplitL "".
        { iIntros "!>". iDestruct 1 as (b) "[>Eqb R]". iDestruct "Eqb" as %Eqb.
          destruct b; [by inversion Eqb|]. iFrame "R". by iExists _. }
        iIntros "_ R0". iExists (). iSplitL ""; [done|].
        iIntros "!>" (t'' Ext'') "PP' !>". iSplitL ""; [by iIntros "!> $"|].
        iIntros "!> !> !>". iFrame "R0". by iExists true. }
    iNext. iIntros (b t' v' s') "(Htok & _ & CASE)"; simpl.
    iApply ("HΦ" $! b with "[- $Htok]").
    iDestruct "CASE" as "[[[% _] [_ ?]]|[[% _]_]]"; subst b; [by iApply "Eq"|done].
  Qed.

  Lemma acquire_spec N l γ κ R q tid E
    (DISJ: histN ## N) (SUB1: ↑N ⊆ E) (SUB2 :↑lftN ⊆ E) (SUB3: ↑histN ⊆ E) :
    ⎡ lft_ctx ⎤ -∗
    {{{ lock_proto N l γ κ R ∗ (q).[κ] }}}
      acquire [ #l ] @ tid; E
    {{{ RET #☠; R ∗ (q).[κ] }}}.
  Proof.
    iIntros "#LFT !#" (Φ) "[#Hproto Htok] HΦ". iLöb as "IH". wp_rec.
    wp_apply (try_acquire_spec with "LFT [$Hproto $Htok]"); [done..|by etrans|].
    iIntros ([]).
    - iIntros "[HR Htok]". wp_if. iApply "HΦ"; iFrame.
    - iIntros "[_ Htok]". wp_if. iApply ("IH" with "Htok HΦ").
  Qed.

  Lemma release_spec N l γ κ R q tid E
    (DISJ: histN ## N) (SUB1: ↑N ⊆ E) (SUB2 :↑lftN ⊆ E) (SUB3: ↑histN ⊆ E) :
    ⎡ lft_ctx ⎤ -∗
    {{{ R ∗ lock_proto N l γ κ R ∗ (q).[κ] }}}
      release [ #l ] @ tid; E
    {{{ RET #☠; (q).[κ] }}}.
  Proof.
    iIntros "#LFT !#" (Φ) "(HR & #Hproto & Htok) HΦ". wp_let.
    iDestruct "Hproto" as (R0) "[#Eq Hproto]".
    iDestruct "Hproto" as (t v) "PP".
    iApply (GPS_aPP_Write N (lock_interp R0) l κ q _ t _ #(Z_of_bool false) _ ()
              with "[$LFT $Htok $PP HR]"); [by move => []|done..|by right| |].
    { simpl. iIntros "!>" (t' Ext') "PP' !>". iExists false.
      iSplit; [done|by iApply "Eq"]. }
    iIntros "!>" (t') "[PP' Htok]". by iApply "HΦ".
  Qed.
End proof.

Global Typeclasses Opaque lock_proto.
