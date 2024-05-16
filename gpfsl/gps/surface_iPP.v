From stdpp Require Import namespaces.
From iris.proofmode Require Import proofmode.

From gpfsl.gps Require Export middleware_PP.
From gpfsl.logic Require Import subj_invariants.

Require Import iris.prelude.options.

(** Persistent Plain Protocol *)

Implicit Types (l : loc) (t : time) (v : val) (E : coPset) (q: Qp) (γ : gname).
Section gps_iPP.
Context `{!noprolG Σ, !gpsG Σ Prtcl, !atomicG Σ} (N: namespace).
Local Notation vProp := (vProp Σ).

Implicit Types (IP : interpO Σ Prtcl) (s : pr_stateT Prtcl).

Definition GPS_iPP IP l t s v γ : vProp :=
  GPS_Reader l t s v γ ∗ subj_inv N (GPS_PPInv IP l γ).

Global Instance GPS_iPP_persistent IP l t s v γ :
  Persistent (GPS_iPP IP l t s v γ) := _.

Lemma GPS_iPP_own_loc_prim IP l t s v γ E E'
  (SUB: ↑N ⊆ E) (SUB': E' ⊆ E ∖ ↑N) :
  GPS_iPP IP l t s v γ ={E, E'}=∗ ∃ C, ▷ <subj> l p↦ C.
Proof.
  iIntros "[R1 Hshr]".
  iInv N as (Vb) "gpsI" "Close".
  iMod (fupd_mask_subseteq E') as "_"; [done|].
  iAssert (<subj> ▷ GPS_PPInv IP l γ)%I with "[gpsI]" as "gpsI".
  { rewrite monPred_subjectively_unfold. by iApply monPred_in_view_elim. }
  iIntros "!>".
  iDestruct (monPred_subjectively_mono _ _ (GPS_PPInv_own_loc_prim _ _ true _)
              with "gpsI") as (?) "own".
  rewrite -monPred_subjectively_later. by iExists _.
Qed.

Lemma GPS_iPP_agree IP l t1 t2 s1 s2 v1 v2 γ E (SUB: ↑N ⊆ E) :
  GPS_iPP IP l t1 s1 v1 γ -∗
  GPS_iPP IP l t2 s2 v2 γ ={E}=∗
  ⌜ (t1 ⊑ t2 → s1 ⊑ s2) ∧ (t2 ⊑ t1 → s2 ⊑ s1) ⌝.
Proof.
  iIntros "[R1 Hshr] [R2 _]".
  iInv N as (Vb) "gpsI" "Close".
  iMod (GPS_Readers_agree with "R1 R2 gpsI") as "[gpsI $]".
  by iMod ("Close" with "gpsI").
Qed.

Lemma GPS_iPP_Init IP l s v E:
  l ↦ v -∗ (∀ t γ, ▷ IP true l γ t s v) ={E}=∗
  ∃ γ t, GPS_iPP IP l t s v γ.
Proof.
  iIntros "Hl IP".
  iMod (GPS_PPRaw_Init_vs IP _ true _ s with "Hl IP") as (γ t) "[PP gpsI]".
  iExists γ, t. iMod (subj_inv_alloc N with "gpsI") as "$". by iFrame "PP".
Qed.

Lemma GPS_iPP_Init_write IP b l v s E tid :
  ↑histN ⊆ E →
  {{{ l ↦ ? ∗ (∀ t γ, ▷?b IP true l γ t s v) }}}
    #l <- v @ tid; E
  {{{ γ t, RET #☠; GPS_iPP IP l t s v γ }}}.
Proof.
  iIntros (? Φ) "own Post". iApply wp_fupd.
  iApply (GPS_PPRaw_Init IP l b with "own"); [done|].
  iNext. iIntros (γ t) "[PP gpsI]".
  iMod (subj_inv_alloc N _ (GPS_PPInv IP l γ) with "[gpsI]") as "gpsI".
  { destruct b; by iFrame. }
  iModIntro. iApply "Post". by iFrame.
Qed.

Lemma GPS_iPP_Read IP (R: time → Prtcl → val → vProp) o l t s v γ tid E
  (DISJ: histN ## N) (SUB1: ↑histN ⊆ E) (SUB2: ↑N ⊆ E)
  (RLX: o = Relaxed ∨ o = AcqRel) :
  {{{ GPS_iPP IP l t s v γ ∗
      (▷ ∀ t' s' v', ⌜s ⊑ s' ∧ t ⊑ t'⌝ -∗
         <obj> ((IP false l γ t' s' v' ={E ∖ ↑N}=∗
                    IP false l γ t' s' v' ∗ R t' s' v') ∧
                (IP true l γ t' s' v' ={E ∖ ↑N}=∗
                    IP true l γ t' s' v' ∗ R t' s' v'))) }}}
    Read o #l @ tid; E
  {{{ t' s' v', RET v'; ⌜s ⊑ s' ∧ t ⊑ t'⌝
      ∗ GPS_iPP IP l t' s' v' γ
      ∗ if (decide (AcqRel ⊑ o)) then R t' s' v'
                                 else ▽{tid} R t' s' v' }}}.
Proof.
  iIntros (Φ) "[#[Hlc Hshr] VS] Post".
  iInv N as (Vb) "gpsI" "Close".
  iApply (GPS_PPRaw_Read IP l R o t s v γ tid Vb with "[$Hlc $gpsI $VS]");
    [solve_ndisj|done|..].
  iIntros "!>" (t' s' v') "(Ext & Hlc' & gpsI & R)".
  iMod ("Close" with "gpsI") as "_".
  iApply ("Post" $! t' s' v' with "[$Ext $Hlc' $Hshr $R]").
Qed.

Lemma GPS_iPP_Write IP l o t s s' v v' γ tid E
  (DISJ: histN ## N) (SUB1: ↑histN ⊆ E) (SUB2: ↑N ⊆ E)
  (RLX: o = Relaxed ∨ o = AcqRel) (FIN: final_st s') :
  let VS : vProp := (∀ t' : time, ⌜(t < t')%positive⌝ -∗
                      GPS_Reader l t' s' v' γ ={E ∖ ↑N}=∗
                      IP true l γ t' s' v')%I in
  {{{ GPS_iPP IP l t s v γ
      ∗ ▷ if decide (AcqRel ⊑ o) then VS else △{tid} VS }}}
    Write o #l v' @ tid; E
  {{{ t', RET #☠; GPS_iPP IP l t' s' v' γ }}}.
Proof.
  iIntros (VS Φ) "[#[Hlc Hshr] VS] Post".
  iInv N as (Vb) "gpsI" "Close".
  iApply (GPS_PPRaw_Write IP l o t v v' s s' γ Vb tid
          with "[$Hlc $gpsI $VS]"); [done|solve_ndisj|done|..].
  iIntros "!>" (t') "(Hlc' & gpsI)".
  iMod ("Close" with "gpsI") as "_".
  iApply ("Post" $! t' with "[$Hlc' $Hshr]").
Qed.

Lemma GPS_iPP_CAS_int_simple
  IP orf or ow l v (vr: Z) (vw: val) t s P Q Q1 Q2 R γ tid E
  (DISJ: histN ## N) (SUB1: ↑histN ⊆ E) (SUB2: ↑N ⊆ E)
  (RLXF: orf = Relaxed ∨ orf = AcqRel)
  (RLXR: or = Relaxed ∨ or = AcqRel) (RLXW: ow = Relaxed ∨ ow = AcqRel) :
  let VSC : vProp :=
    (<obj> ∀ t' s' v', ⌜s ⊑ s' ∧ t ⊑ t'⌝ -∗
                  (IP true l γ t' s' v' ∨ IP false l γ t' s' v') -∗
                  ⌜∃ vl, v' = #vl ∧ lit_comparable vr vl⌝)%I in
  let VS : vProp :=
    (∀ t' s', ⌜s ⊑ s' ∧ t ⊑ t'⌝ -∗
      ((<obj> (▷ IP true l γ t' s' #vr ={E ∖ ↑N}=∗ ▷ Q1 t' s' ∗ ▷ Q2 t' s')) ∗
       (P -∗ ▷ Q2 t' s' ={E ∖ ↑N}=∗ ∃ s'', ⌜s' ⊑ s''⌝ ∗
          (∀ t , ⌜(t' < t)%positive⌝ -∗ ▷ (GPS_Reader l t s'' vw γ)
            ={E ∖ ↑N}=∗
              (<obj> (▷ Q1 t' s' ={E ∖ ↑N}=∗ ▷ IP false l γ t' s' #vr)) ∗
              |={E ∖ ↑N}▷=> Q t s'' ∗ ▷ IP true l γ t s'' vw)) ) ∧
      (▷ ∀ (v: lit), ⌜lit_neq vr v⌝ -∗
          <obj> ((IP false l γ t' s' #v
                      ={E ∖ ↑N}=∗ IP false l γ t' s' #v ∗ R t' s' v) ∧
                 (IP true l γ t' s' #v
                      ={E ∖ ↑N}=∗ IP true l γ t' s' #v ∗ R t' s' v))))%I in
  {{{ GPS_iPP IP l t s v γ
      ∗ ▷ VSC
      ∗ (if decide (AcqRel ⊑ ow) then VS else △{tid} VS)
      ∗ (if decide (AcqRel ⊑ ow) then P  else △{tid} P )  }}}
    CAS #l #vr vw orf or ow @ tid; E
  {{{ (b: bool) t' s' (v': lit), RET #b; ⌜s ⊑ s'⌝
      ∗ ( (⌜b = true  ∧ v' = LitInt vr ∧ (t < t')%positive⌝
            ∗ GPS_iPP IP l t' s' vw γ
            ∗ if decide (AcqRel ⊑ or) then Q t' s' else ▽{tid} Q t' s')
        ∨ (⌜b = false ∧ lit_neq vr v' ∧ (t ≤ t')%positive⌝
            ∗ GPS_iPP IP l t' s' #v' γ
            ∗ (if decide (AcqRel ⊑ orf) then R t' s' v' else ▽{tid} R t' s' v')
            ∗ (if decide (AcqRel ⊑ ow)  then P          else △{tid} P ))) }}}.
Proof.
  iIntros (VSC VS Φ) "(#[Hlc Hshr] & VS) Post".
  iInv N as (Vb) "gpsI" "Close".
  iApply (GPS_PPRaw_CAS_int IP l orf or ow v vr vw t s P Q Q1 Q2 R
          with "[$Hlc $gpsI $VS]"); [solve_ndisj|done..|].
  iIntros "!>" (b t' s' v') "(gpsI & Lt & CASE)".
  iMod ("Close" with "gpsI") as "_".
  iModIntro. iApply ("Post" $! b t' s' v').
  iFrame "Lt". iDestruct "CASE" as "[(Lt & PP & Q) | (Lt & PP & R & P)]".
  - iLeft. by iFrame.
  - iRight. by iFrame.
Qed.

Lemma GPS_iPP_CAS_live_loc
  IP orf or ow l v (lr: loc) (vw: val) t s P Q Q1 Q2 R γ tid
  E (El: loc → coPset)
  (DISJ: histN ## N) (SUB1: ↑histN ⊆ E) (SUB2: ↑N ⊆ E)
  (SUBl: ∀ l', ↑histN ⊆ El l')
  (RLXF: orf = Relaxed ∨ orf = AcqRel)
  (RLXR: or = Relaxed ∨ or = AcqRel) (RLXW: ow = Relaxed ∨ ow = AcqRel) :
  let VSC : vProp :=
    (<obj> ∀ t' s' v', ⌜s ⊑ s' ∧ t ⊑ t'⌝ -∗
                  (IP true l γ t' s' v' ∨ IP false l γ t' s' v') -∗
                  ⌜∃ vl, v' = #vl ∧ lit_comparable lr vl⌝)%I in
  let VS : vProp :=
    (∀ t' s', ⌜s ⊑ s' ∧ t ⊑ t'⌝ -∗
      ((<obj> ∀ l' : loc, ⌜l' ≠ lr⌝ -∗ ▷ IP true l γ t' s' #l' -∗
                      ▷ |={E ∖ ↑N, El l'}=> ∃ q' C', ▷ <subj> l' p↦{q'} C') ∗
       (<obj> (▷ IP true l γ t' s' #lr ={E ∖ ↑N}=∗ ▷ Q1 t' s' ∗ ▷ Q2 t' s')) ∗
       (P -∗ ▷ Q2 t' s' ={E ∖ ↑N}=∗ ∃ s'', ⌜s' ⊑ s''⌝ ∗
          (∀ t , ⌜(t' < t)%positive⌝ -∗ ▷ (GPS_Reader l t s'' vw γ)
            ={E ∖ ↑N}=∗
              (<obj> (▷ Q1 t' s' ={E ∖ ↑N}=∗ ▷ IP false l γ t' s' #lr)) ∗
              |={E ∖ ↑N}▷=> Q t s'' ∗ ▷ IP true l γ t s'' vw)) ) ∧
      (▷ ∀ (v: lit), ⌜lit_neq lr v⌝ -∗
          <obj> ((IP false l γ t' s' #v
                      ={E ∖ ↑N}=∗ IP false l γ t' s' #v ∗ R t' s' v) ∧
                 (IP true l γ t' s' #v
                      ={E ∖ ↑N}=∗ IP true l γ t' s' #v ∗ R t' s' v))))%I in
  {{{ GPS_iPP IP l t s v γ
      ∗ ▷ VSC
      ∗ (if decide (AcqRel ⊑ ow) then VS else △{tid} VS)
      ∗ (if decide (AcqRel ⊑ ow) then P  else △{tid} P )  }}}
    CAS #l #lr vw orf or ow @ tid; E
  {{{ (b: bool) t' s' (v': lit), RET #b; ⌜s ⊑ s'⌝
      ∗ ( (⌜b = true  ∧ v' = LitLoc lr ∧ (t < t')%positive⌝
            ∗ GPS_iPP IP l t' s' vw γ
            ∗ if decide (AcqRel ⊑ or) then Q t' s' else ▽{tid} Q t' s')
        ∨ (⌜b = false ∧ lit_neq lr v' ∧ (t ≤ t')%positive⌝
            ∗ GPS_iPP IP l t' s' #v' γ
            ∗ (if decide (AcqRel ⊑ orf) then R t' s' v' else ▽{tid} R t' s' v')
            ∗ (if decide (AcqRel ⊑ ow)  then P          else △{tid} P ))) }}}.
Proof.
  iIntros (VSC VS Φ) "(#[Hlc Hshr] & VS) Post".
  iInv N as (Vb) "gpsI" "Close".
  iApply (GPS_PPRaw_CAS_live_loc IP l orf or ow v lr vw t s
            P Q Q1 Q2 R _ _ _ _ El
            with "[$Hlc $gpsI VS]"); [done|solve_ndisj|done..|].
  iIntros "!>" (b t' s' v') "(gpsI & Lt & CASE)".
  iMod ("Close" with "gpsI") as "_".
  iModIntro. iApply ("Post" $! b t' s' v').
  iFrame "Lt". iDestruct "CASE" as "[(Lt & PP & Q) | (Lt & PP & R & P)]".
  - iLeft. by iFrame.
  - iRight. by iFrame.
Qed.

Lemma GPS_iPP_CAS_live_loc_simple
  IP orf or ow l v (lr: loc) (vw: val) t s P Q Q1 Q2 R γ tid E
  (DISJ: histN ## N) (SUB1: ↑histN ⊆ E) (SUB2: ↑N ⊆ E)
  (RLXF: orf = Relaxed ∨ orf = AcqRel)
  (RLXR: or = Relaxed ∨ or = AcqRel) (RLXW: ow = Relaxed ∨ ow = AcqRel) :
  let VSC : vProp :=
    (<obj> ∀ t' s' v', ⌜s ⊑ s' ∧ t ⊑ t'⌝ -∗
                  (IP true l γ t' s' v' ∨ IP false l γ t' s' v') -∗
                  ⌜∃ vl, v' = #vl ∧ lit_comparable lr vl⌝)%I in
  let VS : vProp :=
    (∀ t' s', ⌜s ⊑ s' ∧ t ⊑ t'⌝ -∗
      ((<obj> ∀ l' : loc, ⌜l' ≠ lr⌝ -∗ ▷ IP true l γ t' s' #l'
                ={E ∖ ↑N}=∗ ∃ q', ▷ l' ↦{q'} -) ∗
       (<obj> (▷ IP true l γ t' s' #lr ={E ∖ ↑N}=∗ ▷ Q1 t' s' ∗ ▷ Q2 t' s')) ∗
       (P -∗ ▷ Q2 t' s' ={E ∖ ↑N}=∗ ∃ s'', ⌜s' ⊑ s''⌝ ∗
          (∀ t , ⌜(t' < t)%positive⌝ -∗ ▷ (GPS_Reader l t s'' vw γ)
            ={E ∖ ↑N}=∗
              (<obj> (▷ Q1 t' s' ={E ∖ ↑N}=∗ ▷ IP false l γ t' s' #lr)) ∗
              |={E ∖ ↑N}▷=> Q t s'' ∗ ▷ IP true l γ t s'' vw)) ) ∧
      (▷ ∀ (v: lit), ⌜lit_neq lr v⌝ -∗
          <obj> ((IP false l γ t' s' #v
                      ={E ∖ ↑N}=∗ IP false l γ t' s' #v ∗ R t' s' v) ∧
                 (IP true l γ t' s' #v
                      ={E ∖ ↑N}=∗ IP true l γ t' s' #v ∗ R t' s' v))))%I in
  {{{ GPS_iPP IP l t s v γ
      ∗ ▷ VSC
      ∗ (if decide (AcqRel ⊑ ow) then VS else △{tid} VS)
      ∗ (if decide (AcqRel ⊑ ow) then P  else △{tid} P )  }}}
    CAS #l #lr vw orf or ow @ tid; E
  {{{ (b: bool) t' s' (v': lit), RET #b; ⌜s ⊑ s'⌝
      ∗ ( (⌜b = true  ∧ v' = LitLoc lr ∧ (t < t')%positive⌝
            ∗ GPS_iPP IP l t' s' vw γ
            ∗ if decide (AcqRel ⊑ or) then Q t' s' else ▽{tid} Q t' s')
        ∨ (⌜b = false ∧ lit_neq lr v' ∧ (t ≤ t')%positive⌝
            ∗ GPS_iPP IP l t' s' #v' γ
            ∗ (if decide (AcqRel ⊑ orf) then R t' s' v' else ▽{tid} R t' s' v')
            ∗ (if decide (AcqRel ⊑ ow)  then P          else △{tid} P ))) }}}.
Proof.
  iIntros (VSC VS Φ) "(#[Hlc Hshr] & VS) Post".
  iInv N as (Vb) "gpsI" "Close".
  iApply (GPS_PPRaw_CAS_live_loc_simple IP l orf or ow v lr vw t s
            P Q Q1 Q2 R
            with "[$Hlc $gpsI VS]"); [solve_ndisj|done..|].
  iIntros "!>" (b t' s' v') "(gpsI & Lt & CASE)".
  iMod ("Close" with "gpsI") as "_".
  iModIntro. iApply ("Post" $! b t' s' v').
  iFrame "Lt". iDestruct "CASE" as "[(Lt & PP & Q) | (Lt & PP & R & P)]".
  - iLeft. by iFrame.
  - iRight. by iFrame.
Qed.

Global Instance GPS_iPP_contractive l t s v γ :
  Contractive (λ IP, GPS_iPP IP l t s v γ).
Proof.
  move => n ???. apply bi.sep_ne; [done|]. apply subj_inv_contractive.
  dist_later_fin_intro. apply GPS_PPInv_ne; by eapply dist_later_S.
Qed.
Global Instance GPS_iPP_ne l t s v γ :
  NonExpansive (λ IP, GPS_iPP IP l t s v γ).
Proof. apply contractive_ne. by apply _. Qed.

End gps_iPP.

#[global] Instance: Params (@GPS_iPP) 6 := {}.
#[global] Typeclasses Opaque GPS_iPP.
