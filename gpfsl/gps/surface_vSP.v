From iris.base_logic Require Import lib.invariants.
From iris.proofmode Require Import proofmode.

From gpfsl.gps Require Export middleware_SW.
From gpfsl.logic Require Import relacq.
From gpfsl.logic Require Export view_invariants.

Require Import iris.prelude.options.

(** Cancellable Single-Writer protocols *)

Implicit Types (l : loc) (t : time) (v : val) (E : coPset) (q: Qp) (γ : gname).

Section gps_vSP.
Context `{!noprolG Σ, !gpsG Σ Prtcl, !atomicG Σ, !view_invG Σ} (N: namespace).

Local Notation vProp := (vProp Σ).

Implicit Types (IP : interpO Σ Prtcl) (IPC: interpCasO Σ Prtcl)
               (s : pr_stateT Prtcl).

Definition GPS_vSP_Reader IP IPC l t s v γ γi : vProp :=
  (GPS_Reader l t s v γ ∗ view_inv γi N (GPS_INV IP l IPC γ))%I.
Definition GPS_vSP_Writer IP IPC l t s v γ γi: vProp :=
  (GPS_SWWriter l t s v γ ∗ view_inv γi N (GPS_INV IP l IPC γ))%I.
Definition GPS_vSP_SharedReader IP IPC l t s v q γ γi : vProp :=
  (GPS_SWSharedReader l t s v q γ ∗ view_inv γi N (GPS_INV IP l IPC γ))%I.
Definition GPS_vSP_SharedWriter IP IPC l t s v γ γi : vProp :=
  (GPS_SWSharedWriter l t s v γ ∗ view_inv γi N (GPS_INV IP l IPC γ))%I.

Lemma GPS_vSP_SWWriter_Reader IP IPC l t s v γ γi:
  GPS_vSP_Writer IP IPC l t s v γ γi -∗ GPS_vSP_Reader IP IPC l t s v γ γi.
Proof.
  iDestruct 1 as "[W $]". iDestruct (GPS_SWWriter_Reader with "W") as "$".
Qed.

Lemma GPS_vSP_Init
  (IP: gname → interpO Σ Prtcl) (IPC : gname → interpCasO Σ Prtcl) l s v E:
  l ↦ v -∗ (∀ γi t γ, ▷ IP γi true l γ t s v) ={E}=∗
  ∃ γi γ t, view_tok γi 1 ∗ GPS_vSP_Writer (IP γi) (IPC γi) l t s v γ γi.
Proof.
  iIntros "Hl IP".
  iMod (view_inv_alloc N _) as (γi) "VI".
  iMod (GPS_SWRaw_Init_vs (IP γi) _ (IPC γi) true s with "Hl IP") as (γ t) "[SW gpsI]".
  iMod ("VI" $! (GPS_INV (IP γi) l (IPC γi) γ) with "gpsI") as "[#Inv tok]".
  iIntros "!>". iExists γi, γ, t. by iFrame.
Qed.

Lemma GPS_vSP_SWWrite_rel IP IPC l q Q Q1 Q2 t s s' v v' γ γi tid E
  (Exts: s ⊑ s') (DISJ: histN ## N) (SUB1: ↑histN ⊆ E) (SUB2: ↑N ⊆ E):
  let WVS: vProp :=
  (∀ t', ⌜(t < t')%positive⌝ -∗ GPS_SWWriter l t' s' v' γ -∗ Q2 -∗ view_tok γi q
              ={E ∖ ↑N}=∗ (<obj> (Q1 ={E ∖ ↑N}=∗ IPC l γ t s v)) ∗
                     |={E ∖ ↑N}=> (IP true l γ t' s' v' ∗ Q t'))%I in
  {{{ view_tok γi q ∗ GPS_vSP_Writer IP IPC l t s v γ γi
      ∗ ▷ WVS ∗ ▷ <obj> (IP true l γ t s v ={E ∖ ↑N}=∗ Q1 ∗ Q2) }}}
    #l <-ʳᵉˡ v' @ tid; E
  {{{ t', RET #☠; ⌜(t < t')%positive⌝ ∗ GPS_vSP_Reader IP IPC l t' s' v' γ γi
      ∗ Q t' }}}.
Proof.
  iIntros (WVS Φ) "(Htok & [W #Inv] & WVS & IP) Post".
  iMod (view_inv_acc_base γi N with "[$Inv $Htok]") as "[Htok VI]"; [done|].
  iDestruct "VI" as (Vb) "[HInv Closed]".
  iApply (GPS_SWRaw_SWWrite_rel_view IP _ IPC Q Q1 Q2 (view_tok γi q)%I t s s'
           v v' γ tid Vb with "[$W $HInv $Htok $WVS $IP]"); [done|solve_ndisj|..].
  iIntros "!>" (t' V') "(Ext & R & In & tok & HInv)".
  rewrite bi.and_elim_r bi.and_elim_l.
  iMod ("Closed" $! _ (Q t') with "tok HInv") as "Q".
  by iApply ("Post" $! t' with "[$Ext $R $Q $Inv]").
Qed.

Lemma GPS_vSP_Read IP IPC (R: time → Prtcl → val → vProp) l o t s v q γ γi tid E
  (DISJ: histN ## N) (SUB1: ↑histN ⊆ E) (SUB2: ↑N ⊆ E)
  (RLX: o = Relaxed ∨ o = AcqRel) :
  {{{ view_tok γi q ∗ GPS_vSP_Reader IP IPC l t s v γ γi ∗
      (▷ ∀ t' s' v', ⌜s ⊑ s' ∧ t ⊑ t'⌝ -∗
          <obj> ((IP false l γ t' s' v' ={E ∖ ↑N}=∗
                    IP false l γ t' s' v' ∗ R t' s' v') ∧
                (IP true l γ t' s' v' ={E ∖ ↑N}=∗
                    IP true l γ t' s' v' ∗ R t' s' v') ∧
                (IPC l γ t' s' v' ={E ∖ ↑N}=∗
                    IPC l γ t' s' v' ∗ R t' s' v'))) }}}
    Read o #l @ tid; E
  {{{ t' s' v', RET v'; ⌜s ⊑ s' ∧ t ⊑ t'⌝
      ∗ view_tok γi q
      ∗ GPS_vSP_Reader IP IPC l t' s' v' γ γi
      ∗ if decide (AcqRel ⊑ o)%stdpp then R t' s' v' else ▽{tid} R t' s' v' }}}.
Proof.
  iIntros (Φ) "(Htok & #[Hlc Inv] & VS) Post".
  iMod (view_inv_acc_base γi N with "[$Inv $Htok]") as "[Htok VI]"; [done|].
  iDestruct "VI" as (Vb) "[gpsI Close]".
  iApply (GPS_SWRaw_Read IP l IPC R o t s v γ tid Vb
          with "[$Hlc $gpsI $VS]"); [solve_ndisj|done|..].
  iIntros "!>" (t' s' v') "(Ext & Hlc' & gpsI & R)".
  iMod ("Close" with "Htok gpsI") as "Htok".
  iApply ("Post" $! t' s' v' with "[$Htok $Ext $Hlc' $Inv $R]").
Qed.

Lemma GPS_vSP_SWRead_acq_dealloc IP IPC l P Q R q t s v vd γ γi tid E
  (DISJ: histN ## N) (SUB1: ↑histN ⊆ E) (SUB2: ↑N ⊆ E):
  let RVS: vProp :=
    (∀ t' s' v', ⌜s ⊑ s' ∧ t ⊑ t'⌝ -∗
      <obj> ((IP false l γ t' s' v' ={E ∖ ↑N}=∗ IP false l γ t' s' v' ∗ R t' s' v') ∧
            (IP true l γ t' s' v' ={E ∖ ↑N}=∗ IP true l γ t' s' v' ∗ R t' s' v') ∧
            (IPC l γ t' s' v' ={E ∖ ↑N}=∗ IPC l γ t' s' v' ∗ R t' s' v')))%I in
  let DVS: vProp :=
    (∀ t' s', ⌜s ⊑ s' ∧ t ⊑ t'⌝ -∗ P -∗ view_tok γi q -∗ R t' s' vd ={E ∖ ↑N}=∗
      view_tok γi 1 ∗ Q t' s')%I in
  {{{ view_tok γi q ∗ GPS_vSP_Reader IP IPC l t s v γ γi
      ∗ ▷ RVS ∗ ▷ DVS ∗ P }}}
    !ᵃᶜ#l @ tid; E
  {{{ t' s' v', RET v'; ⌜s ⊑ s' ∧ t ⊑ t'⌝ ∗
      GPS_vSP_Reader IP IPC l t' s' v' γ γi ∗
      if (decide (v' = vd)) then ▷ GPS_INV IP l IPC γ ∗ Q t' s'
      else view_tok γi q ∗ R t' s' v' ∗ P }}}.
Proof.
  iIntros (RVS DVS Φ) "(Htok & [R #Inv] & RVS & DVS & P) Post".
  iMod (view_inv_acc_base γi N with "[$Inv $Htok]") as "[Htok VI]"; [done|].
  iDestruct "VI" as (Vb) "[HInv Closed]".
  iApply (GPS_SWRaw_Read IP _ IPC R _ t s v _ _ Vb with "[$R $HInv $RVS]");
    [solve_ndisj|by right|..].
  iIntros "!>" (t' s' v') "(#Ext & R & HInv & HR)".
  case (decide (v' = vd)) as [Eq|NEq]; last first.
  - rewrite bi.and_elim_l. iMod ("Closed" with "Htok HInv") as "Htok".
    iIntros "!>". iApply ("Post" with "[$Ext $R $Inv HR Htok P]").
    rewrite (decide_False _ _ NEq). by iFrame.
  - subst v'. iMod ("DVS" $! t' s' with "Ext P Htok HR") as "[Htok Q]".
    rewrite bi.and_elim_r bi.and_elim_r.
    iDestruct ("Closed" with "Htok") as "[In >_]".
    iSpecialize ("HInv" with "In"). iModIntro.
    iApply ("Post" $! t' s' vd with "[$Ext $R $Inv HInv Q]").
    rewrite decide_True; [by iFrame|done].
Qed.

Lemma GPS_vSP_dealloc IP IPC l t s v γ γi E
  (SUB1: ↑histN ⊆ E) (SUB2: ↑N ⊆ E) :
  ⎡ hist_inv ⎤ -∗ view_tok γi 1 -∗
  GPS_vSP_Reader IP IPC l t s v γ γi ={E}=∗
  ∃ t s v, l ↦ v ∗ ▷ IP true l γ t s v.
Proof.
  iIntros "HINV Htok [? Inv]".
  iMod (view_inv_dealloc with "[$Inv $Htok]") as "Inv"; [done|].
  by iApply (GPS_INV_dealloc _ _ _ true with "HINV Inv").
Qed.

Global Instance GPS_vSP_Writer_contractive n l t s v γ γi :
  Proper (dist_later n ==> dist_later n ==> dist n)
         (λ IP IPC, GPS_vSP_Writer IP IPC l t s v γ γi).
Proof.
  move => ??????. apply bi.sep_ne; [done|]. apply view_inv_contractive.
  dist_later_fin_intro. apply GPS_INV_ne; by eapply dist_later_S.
Qed.
Global Instance GPS_vSP_Writer_ne IPC l t s v γ γi :
  NonExpansive2 (λ IP IPC, GPS_vSP_Writer IP IPC l t s v γ γi).
Proof.
  repeat intro. apply bi.sep_ne; [done|]. by apply view_inv_ne, GPS_INV_ne.
Qed.
Global Instance GPS_vSP_Writer_proper :
  Proper ((≡) ==> (≡) ==> (=) ==> (=) ==> (=) ==> (=) ==> (=) ==> (=) ==> (≡))
         GPS_vSP_Writer.
Proof.
  repeat intro. subst.
  apply bi.sep_proper; [done|]. by apply view_inv_proper, GPS_INV_proper.
Qed.

Global Instance GPS_vSP_Reader_contractive n l t s v γ γi :
  Proper (dist_later n ==> dist_later n ==> dist n)
         (λ IP IPC, GPS_vSP_Reader IP IPC l t s v γ γi).
Proof.
  move => ??????. apply bi.sep_ne; [done|]. apply view_inv_contractive.
  dist_later_fin_intro. apply GPS_INV_ne; by eapply dist_later_S.
Qed.
Global Instance GPS_vSP_Reader_ne l t s v γ γi :
  NonExpansive2 (λ IP IPC, GPS_vSP_Reader IP IPC l t s v γ γi).
Proof.
  repeat intro. apply bi.sep_ne; [done|]. by apply view_inv_ne, GPS_INV_ne.
Qed.
Global Instance GPS_vSP_Reader_proper :
  Proper ((≡) ==> (≡) ==> (=) ==> (=) ==> (=) ==> (=) ==> (=) ==> (=) ==> (≡))
         GPS_vSP_Reader.
Proof.
  repeat intro. subst.
  apply bi.sep_proper; [done|]. by apply view_inv_proper, GPS_INV_proper.
Qed.

Global Instance GPS_vSP_SharedReader_contractive n l t s v q γ γi :
  Proper (dist_later n ==> dist_later n ==> dist n)
         (λ IP IPC, GPS_vSP_SharedReader IP IPC l t s v q γ γi).
Proof.
  move => ??????. apply bi.sep_ne; [done|]. apply view_inv_contractive.
  dist_later_fin_intro. apply GPS_INV_ne; by eapply dist_later_S.
Qed.
Global Instance GPS_vSP_SharedReader_ne l t s v q γ γi :
  NonExpansive2 (λ IP IPC, GPS_vSP_SharedReader IP IPC l t s v q γ γi).
Proof.
  repeat intro. apply bi.sep_ne; [done|]. by apply view_inv_ne, GPS_INV_ne.
Qed.
Global Instance GPS_vSP_SharedReader_proper :
  Proper ((≡) ==> (≡) ==> (=) ==> (=) ==> (=) ==> (=) ==> (=) ==> (=) ==> (=) ==> (≡))
         GPS_vSP_SharedReader.
Proof.
  repeat intro. subst.
  apply bi.sep_proper; [done|]. by apply view_inv_proper, GPS_INV_proper.
Qed.

Global Instance GPS_vSP_SharedWriter_contractive n l t s v γ γi :
  Proper (dist_later n ==> dist_later n ==> dist n)
         (λ IP IPC, GPS_vSP_SharedWriter IP IPC l t s v γ γi).
Proof.
  move => ??????. apply bi.sep_ne; [done|]. apply view_inv_contractive.
  dist_later_fin_intro. apply GPS_INV_ne; by eapply dist_later_S.
Qed.
Global Instance GPS_vSP_SharedWriter_ne l t s v γ γi :
  NonExpansive2 (λ IP IPC, GPS_vSP_SharedWriter IP IPC l t s v γ γi).
Proof.
  repeat intro. apply bi.sep_ne; [done|]. by apply view_inv_ne, GPS_INV_ne.
Qed.
Global Instance GPS_vSP_SharedWriter_proper :
  Proper ((≡) ==> (≡) ==> (=) ==> (=) ==> (=) ==> (=) ==> (=) ==> (=) ==> (≡))
         GPS_vSP_SharedWriter.
Proof.
  repeat intro. subst.
  apply bi.sep_proper; [done|]. by apply view_inv_proper, GPS_INV_proper.
Qed.

End gps_vSP.

Global Instance: Params (@GPS_vSP_Reader) 7 := {}.
Global Instance: Params (@GPS_vSP_Writer) 7 := {}.
Global Instance: Params (@GPS_vSP_SharedReader) 7 := {}.
Global Instance: Params (@GPS_vSP_SharedWriter) 7 := {}.
