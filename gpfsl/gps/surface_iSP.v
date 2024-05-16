From iris.base_logic Require Import lib.invariants.
From iris.proofmode Require Import proofmode.

From gpfsl.gps Require Export middleware_SW.
From gpfsl.logic Require Import subj_invariants relacq.

Require Import iris.prelude.options.

(** Persistent Single-Writer protocols *)

Implicit Types (l : loc) (t : time) (v : val) (E : coPset) (q: Qp) (γ : gname).

Section gps_iSP.
Context `{!noprolG Σ, !gpsG Σ Prtcl, !atomicG Σ} (N: namespace).
Local Notation vProp := (vProp Σ).

Implicit Types (IP : interpO Σ Prtcl) (IPC: interpCasO Σ Prtcl)
               (s : pr_stateT Prtcl).

Definition GPS_iSP_Reader IP IPC l t s v γ : vProp :=
  (GPS_Reader l t s v γ ∗ subj_inv N (GPS_INV IP l IPC γ))%I.
Definition GPS_iSP_Writer IP IPC l t s v γ : vProp :=
  (GPS_SWWriter l t s v γ ∗ subj_inv N (GPS_INV IP l IPC γ))%I.
Definition GPS_iSP_SharedReader IP IPC l t s v q γ : vProp :=
  (GPS_SWSharedReader l t s v q γ ∗ subj_inv N (GPS_INV IP l IPC γ))%I.
Definition GPS_iSP_SharedWriter IP IPC l t s v γ : vProp :=
  (GPS_SWSharedWriter l t s v γ ∗ subj_inv N (GPS_INV IP l IPC γ))%I.

Lemma GPS_iSP_SWWriter_Reader IP IPC l t s v γ:
  GPS_iSP_Writer IP IPC l t s v γ -∗ GPS_iSP_Reader IP IPC l t s v γ.
Proof.
  iDestruct 1 as "[W $]". iDestruct (GPS_SWWriter_Reader with "W") as "$".
Qed.

Lemma GPS_iSP_SWWriter_latest IP IPC l tr sr vr tw sw vw γ E (SUB: ↑N ⊆ E) :
  GPS_SWWriter l tw sw vw γ -∗ GPS_iSP_Reader IP IPC l tr sr vr γ
  ={E}=∗ ⌜sr ⊑ sw ∧ tr ⊑ tw⌝ ∧ GPS_SWWriter l tw sw vw γ.
Proof.
  iIntros "W [R #Inv]".
  iInv N as (Vb) "gpsI" "Close".
  iMod (GPS_SWWriter_latest with "W R gpsI") as "($ & gpsI & $)".
  by iMod ("Close" with "gpsI") as "_".
Qed.

Lemma GPS_iSP_Init IP IPC l s v E:
  l ↦ v -∗ (∀ t γ, ▷ IP true l γ t s v) ={E}=∗
  ∃ γ t, GPS_iSP_Writer IP IPC l t s v γ.
Proof.
  iIntros "Hl IP".
  iMod (GPS_SWRaw_Init_vs IP _ IPC true s with "Hl IP") as (γ t) "[SW gpsI]".
  iExists γ, t. iMod (subj_inv_alloc N with "gpsI") as "$". by iFrame "SW".
Qed.

Lemma GPS_iSP_Init_strong IP IPC (Q: time → gname → vProp) l s v E:
  l ↦ v -∗
  (∀ t γ, GPS_SWWriter l t s v γ ={E}=∗ ▷ IP true l γ t s v ∗ Q t γ) ={E}=∗
  ∃ γ t, GPS_iSP_Reader IP IPC l t s v γ ∗ Q t γ.
Proof.
  iIntros "Hl IP".
  set Q' : time → gname → vProp :=
    (λ t γ, Q t γ ∗ GPS_Reader l t s v γ)%I.
  iMod (GPS_SWRaw_Init_vs_strong IP l IPC true v s Q' E with "Hl [IP]")
    as (γ t) "[gpsI [R Q]]".
  { iIntros (t γ) "SW". iDestruct (GPS_SWWriter_Reader with "SW") as "#$".
    by iApply ("IP" with "SW"). }
  iExists γ, t. iMod (subj_inv_alloc N with "gpsI") as "$". by iFrame.
Qed.

Lemma GPS_iSP_Init_strong_inv IP IPC (Q: time → gname → vProp) l s v E
  (SUB: ↑N ⊆ E) :
  l ↦ v -∗
  (∀ t γ, GPS_iSP_Writer IP IPC l t s v γ ={E ∖ ↑N}=∗ ▷ IP true l γ t s v ∗ Q t γ)
  ={E}=∗ ∃ γ t, GPS_iSP_Reader IP IPC l t s v γ ∗ Q t γ.
Proof.
  iIntros "Hl IP".
  set Q' : time → gname → vProp :=
    (λ t γ, Q t γ ∗ GPS_Reader l t s v γ)%I.
  iPoseProof (GPS_SWRaw_Init_vs_strong_open IP l IPC true v s
                (λ _ γ, subj_inv N (GPS_INV IP l IPC γ)) Q' (E ∖ ↑N)
                with "Hl [IP]") as "VS".
  { iIntros (t γ) "INV SW".
    iDestruct (GPS_SWWriter_Reader with "SW") as "#$".
    iApply ("IP" with "[$SW INV]").
    by iApply monPred_objectively_elim. }
  iMod (fupd_mask_mono with "VS") as (γ t) "VS"; [solve_ndisj|].
  iMod (fupd_mask_mono with "VS") as "F"; [solve_ndisj|].
  iExists γ, t.
  iMod (subj_inv_alloc_open N E (GPS_INV IP l IPC γ)) as "[#INV Close]"; [done|].
  iMod ("F" with "[]") as "(gpsI & $ & $)".
  { by iApply objective_objectively. }
  iFrame "INV". by iMod ("Close" with "gpsI") as "_".
Qed.

Lemma GPS_iSP_SWRead IP IPC R l o t s v γ tid E
  (DISJ: histN ## N) (SUB1: ↑histN ⊆ E) (SUB2: ↑N ⊆ E)
  (RLX: o = Relaxed ∨ o = AcqRel) :
  {{{ GPS_iSP_Writer IP IPC l t s v γ
      ∗ ▷ <obj> (IP true l γ t s v ={E ∖ ↑N}=∗ IP true l γ t s v ∗ R) }}}
    Read o #l @ tid; E
  {{{ RET v; GPS_iSP_Writer IP IPC l t s v γ ∗ R }}}.
Proof.
  iIntros (Φ) "[[Hlc #Hshr] VS] Post".
  iInv N as (Vb) "gpsI" "Close".
  iApply (GPS_SWRaw_SWRead IP l IPC R o with "[$Hlc $gpsI $VS]");
    [solve_ndisj|done|..].
  iIntros "!> (SW & gpsI & R)". iMod ("Close" with "gpsI") as "_".
  iApply "Post". by iFrame.
Qed.

Lemma GPS_iSP_Read' IP IPC (Q R: time → Prtcl → val → vProp) l o t s v γ tid E
  (DISJ: histN ## N) (SUB1: ↑histN ⊆ E) (SUB2: ↑N ⊆ E)
  (RLX: o = Relaxed ∨ o = AcqRel) :
  {{{ GPS_iSP_Reader IP IPC l t s v γ
      ∗ (▷ ∀ t' s' v', ⌜s ⊑ s' ∧ t ⊑ t'⌝ -∗
           <obj> ((IP false l γ t' s' v' ={E ∖ ↑N}=∗
                      IP false l γ t' s' v' ∗ R t' s' v') ∧
                  (IP true l γ t' s' v' ={E ∖ ↑N}=∗
                      IP true l γ t' s' v' ∗ R t' s' v') ∧
                  (IPC l γ t' s' v' ={E ∖ ↑N}=∗
                      IPC l γ t' s' v' ∗ R t' s' v')))
      ∗ (▷ ∀ t' s' v', ⌜s ⊑ s' ∧ t ⊑ t'⌝ -∗ R t' s' v' ={E ∖ ↑N}=∗ Q t' s' v') }}}
    Read o #l @ tid; E
  {{{ t' s' v', RET v'; ⌜s ⊑ s' ∧ t ⊑ t'⌝
      ∗ GPS_iSP_Reader IP IPC l t' s' v' γ
      ∗ if decide (AcqRel ⊑ o)%stdpp then Q t' s' v' else ▽{tid} Q t' s' v' }}}.
Proof.
  iIntros (Φ) "[#[Hlc Hshr] [VS VSQ]] Post".
  iInv N as (Vb) "gpsI" "Close".
  iApply (GPS_SWRaw_Read' IP l IPC Q R o t s v γ tid Vb
          with "[$Hlc $gpsI $VS $VSQ]"); [solve_ndisj|done|..].
  iIntros "!>" (t' s' v') "(Ext & Hlc' & gpsI & Q)".
  iMod ("Close" with "gpsI") as "_".
  iApply ("Post" $! t' s' v' with "[$Ext $Hlc' $Hshr $Q]").
Qed.

Lemma GPS_iSP_Read IP IPC (R: time → Prtcl → val → vProp) l o t s v γ tid E
  (DISJ: histN ## N) (SUB1: ↑histN ⊆ E) (SUB2: ↑N ⊆ E)
  (RLX: o = Relaxed ∨ o = AcqRel) :
  {{{ GPS_iSP_Reader IP IPC l t s v γ
      ∗ (▷ ∀ t' s' v', ⌜s ⊑ s' ∧ t ⊑ t'⌝ -∗
           <obj> ((IP false l γ t' s' v' ={E ∖ ↑N}=∗
                      IP false l γ t' s' v' ∗ R t' s' v') ∧
                  (IP true l γ t' s' v' ={E ∖ ↑N}=∗
                      IP true l γ t' s' v' ∗ R t' s' v') ∧
                  (IPC l γ t' s' v' ={E ∖ ↑N}=∗
                      IPC l γ t' s' v' ∗ R t' s' v'))) }}}
    Read o #l @ tid; E
  {{{ t' s' v', RET v'; ⌜s ⊑ s' ∧ t ⊑ t'⌝
      ∗ GPS_iSP_Reader IP IPC l t' s' v' γ
      ∗ if decide (AcqRel ⊑ o)%stdpp then R t' s' v' else ▽{tid} R t' s' v' }}}.
Proof.
  iIntros (Φ) "[#[Hlc Hshr] VS] Post".
  iInv N as (Vb) "gpsI" "Close".
  iApply (GPS_SWRaw_Read IP l IPC R o t s v γ tid Vb
          with "[$Hlc $gpsI $VS]"); [solve_ndisj|done|..].
  iIntros "!>" (t' s' v') "(Ext & Hlc' & gpsI & R)".
  iMod ("Close" with "gpsI") as "_".
  iApply ("Post" $! t' s' v' with "[$Ext $Hlc' $Hshr $R]").
Qed.

Lemma GPS_iSP_SWWrite IP IPC (R: vProp) l o t s s' v v' γ tid E
  (DISJ: histN ## N) (SUB1: ↑histN ⊆ E) (SUB2: ↑N ⊆ E)
  (RLX: o = Relaxed ∨ o = AcqRel) (Exts: s ⊑ s') :
  let WVS: vProp :=
  (∀ t', ⌜(t < t')%positive⌝ ={E ∖ ↑N}=∗ IP true l γ t' s' v')%I in
  {{{ GPS_iSP_Writer IP IPC l t s v γ
      ∗ ▷ (if decide (AcqRel ⊑ o)%stdpp then WVS else △{tid} WVS)
      ∗ ▷ <obj> (IP true l γ t s v ={E ∖ ↑N}=∗ IPC l γ t s v ∗ R) }}}
    Write o #l v' @ tid; E
  {{{ t', RET #☠; ⌜(t < t')%positive⌝ ∗ GPS_iSP_Writer IP IPC l t' s' v' γ
      ∗ R }}}.
Proof.
  iIntros (VS Φ) "([W #Hshr] & VS) Post".
  iInv N as (Vb) "gpsI" "Close".
  iApply (GPS_SWRaw_SWWrite IP l IPC R o t s s' v v' γ tid Vb
          with "[$W $gpsI $VS]"); [done|solve_ndisj|done|..].
  iIntros "!>" (t') "(Ext & W & gpsI & R)".
  iMod ("Close" with "gpsI") as "_".
  iApply ("Post" $! t' with "[$Ext $W $Hshr $R]").
Qed.

Lemma GPS_iSP_SWWrite_rel IP IPC l Q Q1 Q2 t s s' v v' γ tid E
  (DISJ: histN ## N) (SUB1: ↑histN ⊆ E) (SUB2: ↑N ⊆ E)
  (Exts: s ⊑ s') :
  let WVS: vProp :=
  (∀ t', ⌜(t < t')%positive⌝ -∗ GPS_iSP_Writer IP IPC l t' s' v' γ -∗ Q2
              ={E ∖ ↑N}=∗ (<obj> (Q1 ={E ∖ ↑N}=∗ IPC l γ t s v)) ∗
                     |={E ∖ ↑N}=> (IP true l γ t' s' v' ∗ Q t'))%I in
  {{{ GPS_iSP_Writer IP IPC l t s v γ
      ∗ ▷ WVS ∗ ▷ <obj> (IP true l γ t s v ={E ∖ ↑N}=∗ Q1 ∗ Q2) }}}
    #l <-ʳᵉˡ v' @ tid; E
  {{{ t', RET #☠; ⌜(t < t')%positive⌝ ∗ GPS_iSP_Reader IP IPC l t' s' v' γ ∗ Q t' }}}.
Proof.
  iIntros (VS Φ) "([W #Hshr] & VS1 & VS2) Post".
  iInv N as (Vb) "gpsI" "Close".
  iApply (GPS_SWRaw_SWWrite_rel IP l IPC Q Q1 Q2 t s s' v v' γ tid Vb
          with "[$W $gpsI VS1 $VS2]"); [done|solve_ndisj|..].
  { iIntros "!>" (t' Lt') "W".
    iApply "VS1"; [done|by iFrame "W Hshr"]. }
  iIntros "!>" (t') "(Ext & R' & gpsI & Q)".
  iMod ("Close" with "gpsI") as "_".
  iApply ("Post" $! t' with "[$Ext $R' $Hshr $Q]").
Qed.

Lemma GPS_iSP_SharedWriter_CAS_int_weak
  IP IPC l orf or ow (vr: Z) (vw: val) t s v γ P Q Q1 Q2 R E E' tid
  (DISJ: histN ## N) (SUB1: ↑histN ⊆ E) (SUB2: ↑N ⊆ E)
  (SUBE: E' ⊆ E ∖ ↑N) (RLXF: orf = Relaxed ∨ orf = AcqRel)
  (RLXR: or = Relaxed ∨ or = AcqRel) (RLXW: ow = Relaxed ∨ ow = AcqRel) :
  let VSC : vProp :=
    (<obj> ∀ t' s' v', ⌜s ⊑ s' ∧ t ⊑ t'⌝ -∗
            (IP true l γ t' s' v' ∨ IP false l γ t' s' v' ∨ IPC l γ t' s' v') -∗
            ⌜∃ vl, v' = #vl ∧ lit_comparable vr vl⌝)%I in
  let VS : vProp :=
    (∀ t' s', ⌜s ⊑ s' ∧ t ⊑ t'⌝ -∗
        (((P -∗ ▷ IPC l γ t' s' #vr ={E ∖ ↑N}=∗ False)) ∧
         ((<obj> (▷ IP true l γ t' s' #vr ={E ∖ ↑N}=∗ ▷ Q1 t' s' ∗ ▷ Q2 t' s')) ∗
         (P -∗ ▷ Q2 t' s' ={E ∖ ↑N}=∗ ▷ GPS_SWSharedWriter l t' s' #vr γ ∗
            ∃ s'', ⌜s' ⊑ s''⌝ ∗
              (∀ t'' , ⌜(t' < t'')%positive⌝ -∗
                  ▷ GPS_SWSharedWriter l t'' s'' vw γ ={E ∖ ↑N}=∗
                  (<obj> (▷ Q1 t' s' ={E ∖ ↑N}=∗ ▷ IP false l γ t' s' #vr)) ∗
                  |={E ∖ ↑N}[E']▷=> Q t'' s'' ∗ ▷ IP true l γ t'' s'' vw))) ) ∧
        ▷ (∀ (v: lit), ⌜lit_neq vr v⌝ -∗
        <obj> ((IP false l γ t' s' #v ={E ∖ ↑N}=∗ IP false l γ t' s' #v ∗ R t' s' v) ∧
               (IP true l γ t' s' #v ={E ∖ ↑N}=∗ IP true l γ t' s' #v ∗ R t' s' v) ∧
               (IPC l γ t' s' #v ={E ∖ ↑N}=∗ IPC l γ t' s' #v ∗ R t' s' v))))%I in
  {{{ GPS_iSP_Reader IP IPC l t s v γ
      ∗ (▷ VSC)
      ∗ (if decide (AcqRel ⊑ ow)%stdpp then VS else △{tid} VS)
      ∗ (if decide (AcqRel ⊑ ow)%stdpp then P  else △{tid} P) }}}
    CAS #l #vr vw orf or ow @ tid; E
  {{{ (b: bool) t' s' (v': lit), RET #b;
      ⌜s ⊑ s'⌝
      ∗ ( (⌜b = true  ∧ v' = LitInt vr ∧ (t < t')%positive⌝
            ∗ GPS_iSP_Reader IP IPC l t' s' vw γ
            ∗ if decide (AcqRel ⊑ or)%stdpp then Q t' s' else ▽{tid} Q t' s')
        ∨ (⌜b = false ∧ lit_neq vr v' ∧ (t ≤ t')%positive⌝
            ∗ GPS_iSP_Reader IP IPC l t' s' #v' γ
            ∗ (if decide (AcqRel ⊑ orf)%stdpp
               then R t' s' v' else ▽{tid} (R t' s' v'))
            ∗ (if decide (AcqRel ⊑ ow)%stdpp then P else △{tid} P) ) ) }}}.
Proof.
  iIntros (VSC VS Φ) "(#[Hlc Hshr] & VSC & VS & P) Post".
  iInv N as (Vb) "gpsI" "Close".
  iApply (GPS_SWRaw_SharedWriter_CAS_int_weak IP l IPC orf or ow vr vw t s v γ
            P Q Q1 Q2 R tid Vb with "[$Hlc $gpsI $VSC $VS $P]");
    [done|solve_ndisj|done|done|done|..].
  iIntros "!>" (b t' s' v') "(gpsI & Ext & CASE)".
  iMod ("Close" with "gpsI") as "_".
  iApply ("Post" $! b t' s' v' with "[-$Ext]").
  iDestruct "CASE" as "[?|?]"; [iLeft|iRight]; iFrame "Hshr ∗".
Qed.

Lemma GPS_iSP_SharedWriter_CAS_int_strong
  IP IPC l qs (dropR: bool) orf or ow (vr: Z) (vw: val) t s v γ
  P Q Q1 Q2 R E E' tid
  (DISJ: histN ## N) (SUB1:  ↑histN ⊆ E) (SUB2: ↑N ⊆ E)
  (SUBE: E' ⊆ E ∖ ↑N) (RLXF: orf = Relaxed ∨ orf = AcqRel)
  (RLXR: or = Relaxed ∨ or = AcqRel) (RLXW: ow = Relaxed ∨ ow = AcqRel) :
  let VSC : vProp :=
    (<obj> ∀ t' s' v', ⌜s ⊑ s' ∧ t ⊑ t'⌝ -∗
            (IP true l γ t' s' v' ∨ IP false l γ t' s' v') -∗
            ⌜∃ vl, v' = #vl ∧ lit_comparable vr vl⌝)%I in
  let VS : vProp :=
    (∀ t' s', ⌜s ⊑ s' ∧ t ⊑ t'⌝ -∗
      ((<obj> (▷ IP true l γ t' s' #vr ={E ∖ ↑N}=∗ ▷ Q1 t' s' ∗ ▷ Q2 t' s')) ∗
       (P -∗ ▷ Q2 t' s' ={E ∖ ↑N}=∗ ▷ GPS_SWSharedWriter l t' s' #vr γ ∗
          ∃ s'', ⌜s' ⊑ s''⌝ ∗
            (∀ t'' , ⌜(t' < t'')%positive⌝ -∗ ▷ GPS_SWSharedWriter l t'' s'' vw γ -∗
              (if dropR then ▷ GPS_SWSharedReader l t'' s'' vw qs γ else True) ={E ∖ ↑N}=∗
              (<obj> (▷ Q1 t' s' ={E ∖ ↑N}=∗ ▷ IP false l γ t' s' #vr)) ∗
              |={E ∖ ↑N}[E']▷=> Q t'' s'' ∗ ▷ IP true l γ t'' s'' vw)) ) ∧
      ▷ (∀ (v: lit), ⌜lit_neq vr v⌝ -∗
        <obj> ((IP false l γ t' s' #v ={E ∖ ↑N}=∗ IP false l γ t' s' #v ∗ R t' s' v) ∧
               (IP true l γ t' s' #v ={E ∖ ↑N}=∗ IP true l γ t' s' #v ∗ R t' s' v))))%I in
  {{{ GPS_iSP_SharedReader IP IPC l t s v qs γ
      ∗ (▷ VSC)
      ∗ (if decide (AcqRel ⊑ ow)%stdpp then VS else △{tid} VS)
      ∗ (if decide (AcqRel ⊑ ow)%stdpp then P  else △{tid} P) }}}
    CAS #l #vr vw orf or ow @ tid; E
  {{{ (b: bool) t' s' (v': lit), RET #b;
      ⌜s ⊑ s'⌝
      ∗ ( (⌜b = true  ∧ v' = LitInt vr ∧ (t < t')%positive⌝
            (* TODO: GPS_aSP_Reader here *)
            ∗ (if dropR then True else GPS_iSP_SharedReader IP IPC l t' s' vw qs γ)
            ∗ if decide (AcqRel ⊑ or)%stdpp then Q t' s' else ▽{tid} Q t' s')
        ∨ (⌜b = false ∧ lit_neq vr v' ∧ (t ≤ t')%positive⌝
            ∗ GPS_iSP_SharedReader IP IPC l t' s' #v' qs γ
            ∗ (if decide (AcqRel ⊑ orf)%stdpp then R t' s' v' else ▽{tid} (R t' s' v'))
            ∗ (if decide (AcqRel ⊑ ow)%stdpp then P else △{tid} P) ) ) }}}.
Proof.
  iIntros (VSC VS Φ) "([Hlc #Hshr] & VSC & VS & P) Post".
  iInv N as (Vb) "gpsI" "Close".
  iApply (GPS_SWRaw_SharedWriter_CAS_int_strong IP l IPC dropR orf or ow vr vw
            t s v qs γ P Q Q1 Q2 R tid Vb with "[$Hlc $gpsI $VS $VSC $P]");
    [done|solve_ndisj|done|done|done|..].
  iIntros "!>" (b t' s' v') "(gpsI & Ext & CASE)".
  iMod ("Close" with "gpsI") as "_".
  iApply ("Post" $! b t' s' v' with "[- $Ext]").
  iDestruct "CASE" as "[CASE|?]"; [iLeft|iRight]; last iFrame "Hshr ∗".
  iDestruct "CASE" as "($ & R & $)". destruct dropR; [done|]. by iFrame "R Hshr".
Qed.

Lemma GPS_iSP_SharedWriter_revert IP IPC l t t' s s' v v' γ E (SUB: ↑N ⊆ E) :
  GPS_iSP_SharedWriter IP IPC l t s v γ -∗
  GPS_SWSharedReader l t' s' v' 1%Qp γ ={E}=∗ GPS_iSP_Writer IP IPC l t s v γ.
Proof.
  iIntros "[W #Hshr] SR".
  iInv N as (Vb) "gpsI" "Close".
  iMod (GPS_SWRaw_SharedWriter_revert with "W SR gpsI") as "[$ gpsI]".
  iMod ("Close" with "gpsI") as "_". by iFrame "Hshr".
Qed.

Lemma GPS_iSP_Readers_agree IP IPC l t1 t2 s1 s2 v1 v2 γ E (SUB: ↑N ⊆ E) :
  GPS_iSP_Reader IP IPC l t1 s1 v1 γ -∗
  GPS_iSP_Reader IP IPC l t2 s2 v2 γ ={E}=∗
  ⌜(t1 ⊑ t2 → s1 ⊑ s2) ∧ (t2 ⊑ t1 → s2 ⊑ s1)⌝.
Proof.
  iIntros "[R1 Hshr] [R2 _]".
  iInv N as (Vb) "gpsI" "Close".
  iMod (GPS_Readers_agree with "R1 R2 gpsI") as "[gpsI $]".
  by iMod ("Close" with "gpsI").
Qed.

Global Instance GPS_iSP_Writer_contractive n l t s v γ :
  Proper (dist_later n ==> dist_later n ==> dist n)
         (λ IP IPC, GPS_iSP_Writer IP IPC l t s v γ).
Proof.
  move => ??????. apply bi.sep_ne; [done|]. apply subj_inv_contractive.
  dist_later_fin_intro. apply GPS_INV_ne; by eapply dist_later_S.
Qed.
Global Instance GPS_iSP_Writer_ne l t s v γ :
  NonExpansive2 (λ IP IPC, GPS_iSP_Writer IP IPC l t s v γ).
Proof.
  repeat intro. apply bi.sep_ne; [done|]. by apply subj_inv_ne, GPS_INV_ne.
Qed.
Global Instance GPS_iSP_Writer_proper :
  Proper ((≡) ==> (≡) ==> (=) ==> (=) ==> (=) ==> (=) ==> (=) ==> (≡))
         GPS_iSP_Writer.
Proof.
  repeat intro. subst.
  apply bi.sep_proper; [done|]. by apply subj_inv_proper, GPS_INV_proper.
Qed.

Global Instance GPS_iSP_Reader_contractive n l t s v γ :
  Proper (dist_later n ==> dist_later n ==> dist n)
         (λ IP IPC, GPS_iSP_Reader IP IPC l t s v γ).
Proof.
  move => ??????. apply bi.sep_ne; [done|]. apply subj_inv_contractive.
  dist_later_fin_intro. apply GPS_INV_ne; by eapply dist_later_S.
Qed.
Global Instance GPS_iSP_Reader_ne l t s v γ :
  NonExpansive2 (λ IP IPC, GPS_iSP_Reader IP IPC l t s v γ).
Proof.
  repeat intro. apply bi.sep_ne; [done|]. by apply subj_inv_ne, GPS_INV_ne.
Qed.
Global Instance GPS_iSP_Reader_proper :
  Proper ((≡) ==> (≡) ==> (=) ==> (=) ==> (=) ==> (=) ==> (=) ==> (≡))
         GPS_iSP_Reader.
Proof.
  repeat intro. subst.
  apply bi.sep_proper; [done|]. by apply subj_inv_proper, GPS_INV_proper.
Qed.

Global Instance GPS_iSP_SharedReader_contractive n l t s v q γ :
  Proper (dist_later n ==> dist_later n ==> dist n)
         (λ IP IPC, GPS_iSP_SharedReader IP IPC l t s v q γ).
Proof.
  move => ??????. apply bi.sep_ne; [done|]. apply subj_inv_contractive.
  dist_later_fin_intro. apply GPS_INV_ne; by eapply dist_later_S.
Qed.
Global Instance GPS_iSP_SharedReader_ne l t s v q γ :
  NonExpansive2 (λ IP IPC, GPS_iSP_SharedReader IP IPC l t s v q γ).
Proof.
  repeat intro. apply bi.sep_ne; [done|]. by apply subj_inv_ne, GPS_INV_ne.
Qed.
Global Instance GPS_iSP_SharedReader_proper :
  Proper ((≡) ==> (≡) ==> (=) ==> (=) ==> (=) ==> (=) ==> (=) ==> (=) ==> (≡))
         GPS_iSP_SharedReader.
Proof.
  repeat intro. subst.
  apply bi.sep_proper; [done|]. by apply subj_inv_proper, GPS_INV_proper.
Qed.

Global Instance GPS_iSP_SharedWriter_contractive n l t s v γ :
  Proper (dist_later n ==> dist_later n ==> dist n)
         (λ IP IPC, GPS_iSP_SharedWriter IP IPC l t s v γ).
Proof.
  move => ??????. apply bi.sep_ne; [done|]. apply subj_inv_contractive.
  dist_later_fin_intro. apply GPS_INV_ne; by eapply dist_later_S.
Qed.
Global Instance GPS_iSP_SharedWriter_ne l t s v γ :
  NonExpansive2 (λ IP IPC, GPS_iSP_SharedWriter IP IPC l t s v γ).
Proof.
  repeat intro. apply bi.sep_ne; [done|]. by apply subj_inv_ne, GPS_INV_ne.
Qed.
Global Instance GPS_iSP_SharedWriter_proper :
  Proper ((≡) ==> (≡) ==> (=) ==> (=) ==> (=) ==> (=) ==> (=) ==> (≡))
         GPS_iSP_SharedWriter.
Proof.
  repeat intro. subst.
  apply bi.sep_proper; [done|]. by apply subj_inv_proper, GPS_INV_proper.
Qed.

End gps_iSP.

Global Instance: Params (@GPS_iSP_Reader) 6 := {}.
Global Instance: Params (@GPS_iSP_Writer) 6 := {}.
Global Instance: Params (@GPS_iSP_SharedReader) 6 := {}.
Global Instance: Params (@GPS_iSP_SharedWriter) 6 := {}.
