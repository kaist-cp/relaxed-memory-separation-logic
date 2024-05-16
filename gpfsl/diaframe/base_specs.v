From gpfsl.base_logic Require Export weakestpre.
From gpfsl.logic Require Import lifting proofmode atomics invariants.
From diaframe Require Import proofmode_base lib.except_zero tele_utils.
From diaframe.symb_exec Require Import defs.
From gpfsl.base_logic Require Import na meta_data.

From gpfsl.diaframe Require Import vprop_weakestpre spec_notation vprop_weakestpre_logatom atom_spec_notation inv_hints.


Require Import iris.prelude.options.

#[local] Open Scope positive_scope.

Section base_specs.
  Context `{!noprolG Σ, !atomicG Σ}.

  #[global] Instance fork_spec e E:
    SolveSepSideCondition (↑histN ⊆ E) →
    SPEC ⟨E⟩ {{ ▷ ∀ tid', WP e @ tid'; ⊤ {{ _, True }}  }}
      Fork e
    {{ RET #☠; True }}.
  Proof.
    move => HE. iSteps as (tid) "H1". iApply (wp_fork with "H1"); done.
  Qed.

  #[global] Instance alloc_spec (n : Z) E :
    SolveSepSideCondition (↑ histN ⊆ E) →
    SPEC ⟨E⟩ {{ ⌜(0 < n)%Z⌝ }}
      Alloc #n
    {{ (l : loc), RET #l;
      ⎡ † l … Z.to_nat n ⎤ ∗ l ↦∗ repeat #☠ (Z.to_nat n) ∗
      ([∗ list] i ∈ seq 0 (Z.to_nat n), meta_token (l >> i) ⊤) }}.
  Proof.
    move => HE. iSteps.
    iApply wp_alloc; first apply HE; first lia; iSteps.
  Qed.

  #[global] Instance free_spec (n: Z) (l: loc) E:
    SolveSepSideCondition (↑histN ⊆ E) →
    SPEC ⟨E⟩ {{ ⌜(0 ≤ n)%Z⌝ ∗ ▷ ⎡†l…Z.to_nat n⎤ ∗ ▷ own_loc_vec l 1 (Z.to_nat n)}}
      Free #n #l
    {{ RET #☠; True }}.
  Proof.
    move => HE. iSteps as (tid Hn) "H1 H2". iApply (wp_free with "[$H1 $H2]"); done.
  Qed.

  #[global] Instance read_own_loc_na_spec (l: loc) q o v E:
    SolveSepSideCondition (↑histN ⊆ E) →
    SPEC [(l ↦{q} v)] ⟨E⟩ {{ True }}
      Read o #l
    {{ RET v; l ↦{q} v }} | 15.
  Proof.
    move => HE. iSteps as (tid) "H1". iApply (wp_read with "H1"); [done|]. iSteps.
  Qed.


  #[global] Instance read_own_loc_spec (l: loc) q o E:
    SolveSepSideCondition (Relaxed ⊑ o) →
    SolveSepSideCondition (↑histN ⊆ E) →
    SPEC [ (l ↦{q} ?) ] ⟨E⟩ {{ True }}
      Read o #l
    {{ (v: val), RET v; l ↦{q} ? }} | 20.
  Proof.
    move => Rx => HE. iSteps as (tid) "H1". iApply (wp_read_own with "H1"); try done. iSteps.
  Qed.

  #[global] Instance write_own_loc_spec E l v e :
    SolveSepSideCondition (↑histN ⊆ E) →
    IntoVal e v →
    SPEC [ l ↦ ? ] ⟨E⟩ {{ True }} #l <- e {{ RET #☠; l ↦ v }}.
  Proof. move => HE <-. iSteps. wp_write. iSteps. Qed.

  #[global] Instance write_own_loc_na_spec E l v v' e :
    SolveSepSideCondition (↑histN ⊆ E) →
    IntoVal e v' →
    SPEC [ l ↦ v ] ⟨E⟩ {{ True }} #l <- e {{ RET #☠; l ↦ v' }}.
  Proof. move => HE <-. iSteps. wp_write. iSteps. Qed.


  #[global] Instance AtomicSeen_concurrent_write_no_fence_spec E1 E2 l γ ζ' o v' e:
    SolveSepSideCondition (Relaxed ⊑ o) →
    IntoVal e v' →
    SPEC [ l sn⊒{γ} ζ' ] ⟨E1, E2⟩ ζ V Vb, {{ @{Vb} l at↦{γ} ζ ∗ ⊒V ∗ ⌜↑histN ⊆ E2⌝ }} Write o #l e {{ t' V' V'', RET #☠;
            ⌜fresh_max_time ζ' t'
            ∧ ζ !! t' = None
              ∧ V ⊑ V''
                ∧ V ≠ V''
                  ∧ ¬ V' ⊑ V
                    ∧ (if decide (AcqRel ⊑ o)
                      then V'' = V'
                      else V' ⊑ V'')⌝ ∗ ⊒V'' ∗
              (let ζ'' := <[t':=(v', V')]> ζ' in
                let ζn := <[t':=(v', V')]> ζ in
                @{V''} l sn⊒{γ} ζ'' ∗
                @{Vb ⊔ V''} l at↦{γ} ζn)
    }} | 200.
  Proof.
    rewrite /SolveSepSideCondition. move => RelaxedO <-.
    iSteps as (tid ζ V Vrel HE)"sn⊒ ⊒V l↦".

    iMod (rel_objectively_intro (⊒∅) tid with "[]") as "#rel_empty".
    { iApply objective_objectively. iApply monPred_in_bot. }

    wp_apply (AtomicSeen_concurrent_write _ _ _ _ _ _ ∅ _ _ _ with "[$sn⊒ $l↦ $⊒V]"); [done| solve_ndisj| by destruct (decide _)| ].
    destruct (decide _); iSteps.
  Qed.

  #[global] Instance AtomicSeen_CON_CAS_no_fence_spec E1 E2 l γ ζ' orf or ow (vr: lit) e (vw: val):
  SolveSepSideCondition (Relaxed ⊑ orf) →
  SolveSepSideCondition (Relaxed ⊑ or) →
  SolveSepSideCondition (Relaxed ⊑ ow) →
  IntoVal e vw →
  SPEC [ l sn⊒{γ} ζ' ] ⟨E1, E2⟩ ζ (V Vb: view),
    {{ ( @{Vb} l at↦{γ} ζ ∗
        ⌜ (∀ (t : positive) (v : val),
            no_earlier_time ζ' t
            → fst <$> ζ !! t = Some v
              → ∃ vl : lit, v = #vl ∧ lit_comparable vr vl) ⌝
        ∗ ⊒V ∗ ⌜↑histN ⊆ E2⌝ )
    }}
  CAS #l #vr e orf or ow
  {{ (b : bool) t' (v' : lit) (Vr V'': view) ζ'' ζn,
      RET #b;
  ( ⌜ζ' ⊆ ζ'' ⊆ ζn
    ∧ ζ'' !! t' = Some (#v', Vr)
      ∧ no_earlier_time ζ' t' ∧ V ⊑ V'' ⌝ ∗
      @{V''} l sn⊒{γ} ζ'' ∗ @{Vb ⊔ V''} l at↦{γ} ζn ∗
      ((* fail *)
      (⌜ b = false ∧ lit_neq vr v' ∧ ζn = ζ ⌝
        ∧ (if decide (AcqRel ⊑ orf)
          then ⌜Vr ⊑ V''⌝
          else emp))
      ∨
        (* success *)
        (⌜b = true ∧ v' = vr⌝
        ∧ (let tn := t' + 1 in
          ∃ Vw : view,
            ⌜ζ !! tn = None
              ∧ ζn = <[tn:=(vw, Vw)]> ζ
                ∧ ζ'' !! tn = Some (vw, Vw)
                  ∧ Vr ⊑ Vw
                    ∧ Vr ≠ Vw
                      ∧ ¬ V'' ⊑ Vr
                        ∧ V ≠ V''
                          ∧ (if decide (AcqRel ⊑ ow)
                            then
                              if decide (AcqRel ⊑ or)
                              then Vw = V''
                              else V'' ⊑ Vw
                            else True)⌝
            ∧ (if decide (AcqRel ⊑ ow)
                then @{Vw} l sn⊒{γ} ζ''
                else emp) ∗
            (if decide (AcqRel ⊑ or)
              then ⌜Vw ⊑ V''⌝
              else emp))))
      ∗ ⊒V'')
  }} | 200.
  Proof.
  rewrite /SolveSepSideCondition. move => Rx1 Rx2 Rx3 <-.
  iSteps as (tid ζ V Vb comp_val HE) "sn⊒ ⊒V l↦".

  iMod (rel_objectively_intro (⊒∅) tid with "[]") as "#rel_empty".
  { iApply objective_objectively. iApply monPred_in_bot. }

  wp_apply (AtomicSeen_CON_CAS _ _ _ _ _ _ _ _ with "[$sn⊒ $l↦ $⊒V]"); [done..| solve_ndisj | done |  |].
  { destruct (decide _); done. }
  iIntros (b t' v' Vr V'' ζ'' ζn) "H". iExists b, t', v', Vr, V'', ζ'', ζn.
  iDestruct "H" as "(%Ha & ? & ? & ? & case)". iFrame. do 2 (iSplitR; try done). iSteps; repeat destruct (decide _); done.
  Qed.


  Section logatom_test.
    Local Instance write_own_loc_spec_atomic E1 E2 l v e :
      IntoVal e v →
      SPEC [ l ↦ ? ] ⟨E1, E2⟩ {{ ⌜↑histN ⊆ E2⌝ }} #l <- e {{ RET #☠; l ↦ v }}.
    Proof. move => <-. iSteps. Qed.

    Local Instance write_own_loc_always_spec E1 E2 l v e :
      IntoVal e v →
      SPEC  ⟨E1, E2⟩ {{ l ↦ ? ∗ ⌜↑histN ⊆ E2⌝ }} #l <- e {{ RET #☠; l ↦ v }}.
    Proof. move => <-. iSteps. Qed.

    Lemma write_own_loc_na_logatom_spec E E' l v' e :
      IntoVal e v' →
      (↑histN ⊆ E) →
      SPEC ⟨E, E', ↑histN⟩ << l ↦ ? > > #l <- e << RET #☠; l ↦ v' > >.
    Proof.
      move => <- HE. do 4 iStep.
      (* TODO: assumption HE takes precedence and disrupts mask inference*)
      clear HE. iSteps.
    Qed.
  End logatom_test.
End base_specs.


#[global] Arguments sqsubseteq {_} {_} _ _ : simpl never.