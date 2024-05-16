From iris.algebra Require Import gmap coPset auth excl functions lib.excl_auth.
From iris.base_logic.lib Require Import invariants.
From iris.proofmode Require Import proofmode.
From gpfsl.base_logic Require Export vprop.
From gpfsl.algebra Require Import lattice_cmra.

Require Import iris.prelude.options.

(* Non-atomic ("thread-local") invariants. *)

Definition na_inv_pool_name := gname.

Class na_invG Vw `{!LatBottom bot} Σ :=
  { na_inv_enable_inG : inG Σ (@discrete_funR positive (λ _, authUR (latUR Vw)));
    na_inv_disable_inG : inG Σ (excl_authR (latO Vw)) }.
Local Existing Instances na_inv_enable_inG na_inv_disable_inG.

Definition na_invΣ Vw `{!LatBottom bot} : gFunctors :=
  #[ GFunctor (constRF (@discrete_funR positive (λ _, authUR (latUR Vw))));
     GFunctor (constRF (excl_authR (latO Vw))) ].
Global Instance subG_na_invG Vw `{!LatBottom bot} Σ :
  subG (na_invΣ Vw) Σ → na_invG Vw Σ.
Proof. solve_inG. Qed.

Section defs.
  Context `{invGS Σ, !@na_invG Vw bot BOT Σ}.
  Notation vProp := (monPred (lat_bi_index Vw) (uPredI (iResUR Σ))).

  Definition to_ofe_funR (E : coPset) (Vs : positive → Vw) : discrete_funR _ :=
    λ i, if decide (i ∈ E) then ● to_latT (Vs i) else ε.

  Definition na_own (p : na_inv_pool_name) (E : coPset) : vProp :=
    (∃ Vs, ⎡own p (to_ofe_funR E Vs)⎤ ∗ ∀ i, ⊒(Vs i))%I.

  Definition na_inv (p : na_inv_pool_name) (N : namespace) (P : vProp) : vProp :=
    (∃ i V γ, ⌜i ∈ (↑N:coPset)⌝ ∗ ⊒V ∗
            ⎡inv N ((∃ V', P (V ⊔ V') ∗
                           own p (discrete_fun_singleton i (◯ to_latT V')) ∗
                           own γ (● None)) ∨
                    (∃ V', own p (discrete_fun_singleton i (● to_latT V')) ∗
                           own γ (●E (to_latT V'))))⎤)%I.
End defs.

#[global] Instance: Params (@na_inv) 8 := {}.
#[global] Instance: Params (@na_own) 6 := {}.
#[global] Typeclasses Opaque na_own na_inv.

Section proofs.
  Context `{invGS Σ, !@na_invG Vw bot BOT Σ}.
  Notation vProp := (monPred (lat_bi_index Vw) (uPredI (iResUR Σ))).

  Global Instance na_own_timeless p E : Timeless (na_own p E).
  Proof. rewrite /na_own. apply _. Qed.

  Global Instance na_inv_ne p N : NonExpansive (na_inv p N).
  Proof. rewrite /na_inv. solve_proper. Qed.
  Global Instance na_inv_proper p N : Proper ((≡) ==> (≡)) (na_inv p N).
  Proof. apply (ne_proper _). Qed.

  Global Instance na_inv_persistent p N (P : vProp) : Persistent (na_inv p N P).
  Proof. rewrite /na_inv; apply _. Qed.

  Lemma na_alloc : ⊢ |==> ∃ tid, na_own tid ⊤.
  Proof.
    rewrite /na_own. iDestruct (monPred_in_intro True%I with "[//]") as (V) "[HV _]".
    iMod (own_alloc (to_ofe_funR ⊤ (λ _, V))) as (p) "Own".
    { intro i. by rewrite /to_ofe_funR /= auth_auth_valid. }
    iExists _, _. by iFrame "HV ∗".
  Qed.

  Lemma na_own_disjoint tid E1 E2 : na_own tid E1 -∗ na_own tid E2 -∗ ⌜E1 ## E2⌝.
  Proof.
    rewrite /na_own. iIntros "H1 H2".
    iDestruct "H1" as (Vs1) "[H1 _]". iDestruct "H2" as (Vs2) "[H2 _]".
    iCombine "H1 H2" gives %Hv. iIntros "!%" (i Hi1 Hi2).
    specialize (Hv i).
    rewrite /to_ofe_funR /= discrete_fun_lookup_op !decide_True in Hv; auto.
    by destruct Hv.
  Qed.

  Lemma na_own_union tid E1 E2 :
    E1 ## E2 → na_own tid (E1 ∪ E2) ⊣⊢ na_own tid E1 ∗ na_own tid E2.
  Proof.
    intros DISJ. rewrite /na_own. iSplit.
    - iIntros "H". iDestruct "H" as (Vs) "[Hown #Hin]".
      rewrite -!(bi.exist_intro Vs). iFrame "Hin".
      rewrite -embed_sep -own_op 
        (_:to_ofe_funR (E1 ∪ E2) Vs ≡ to_ofe_funR E1 Vs ⋅ to_ofe_funR E2 Vs) //.
      intros i. rewrite discrete_fun_lookup_op /to_ofe_funR. specialize (DISJ i).
      do 3 destruct decide; try set_solver; by rewrite ?right_id ?left_id.
    - iIntros "[H1 H2]".
      iDestruct "H1" as (Vs1) "[H1 #Hin1]". iDestruct "H2" as (Vs2) "[H2 #Hin2]".
      iExists (λ i, if decide (i ∈ E1) then Vs1 i else Vs2 i). iSplitL.
      + iCombine "H1 H2" as "H".
        rewrite (_:to_ofe_funR E1 Vs1 ⋅ to_ofe_funR E2 Vs2 ≡ _) //.
        intros i. rewrite discrete_fun_lookup_op /to_ofe_funR. specialize (DISJ i).
        do 3 destruct decide; try set_solver; by rewrite ?right_id ?left_id.
      + iIntros (i). destruct decide; [iApply "Hin1"|iApply "Hin2"].
  Qed.

  Lemma na_own_acc E2 E1 tid :
    E2 ⊆ E1 → na_own tid E1 -∗ na_own tid E2 ∗ (na_own tid E2 -∗ na_own tid E1).
  Proof.
    intros HF. assert (E1 = E2 ∪ (E1 ∖ E2)) as -> by exact: union_difference_L.
    rewrite na_own_union; last by set_solver+. iIntros "[$ $]". auto.
  Qed.

  Lemma na_inv_alloc p E N (P : vProp) : ▷ P ={E}=∗ na_inv p N P.
  Proof.
    iIntros "HP".
    iDestruct (monPred_in_intro with "HP") as (V) "[#HV HP]".
    iMod (own_unit (@discrete_funUR positive (λ _, authUR (latUR Vw))) p) as "Hempty".
    iMod (own_alloc (● None)) as (γ) "Hdis"; [by apply auth_auth_valid|].
    destruct (fresh_inv_name ∅ N) as (i & _ & HiN). unfold na_inv.
    iExists i, V, γ. iFrame "# %". iMod (inv_alloc N with "[-]") as "$"; [|done].
    iLeft. iExists bot. iNext. iFrame. rewrite (_:ε ≡ _) //. intros i'.
    rewrite /discrete_fun_singleton /discrete_fun_insert. destruct decide=>//. by subst i.
  Qed.

  Lemma na_inv_acc p E F N (P : vProp) :
    ↑N ⊆ E → ↑N ⊆ F →
    na_inv p N P -∗ na_own p F ={E}=∗ ▷ P ∗ na_own p (F∖↑N) ∗
                       (▷ P ∗ na_own p (F∖↑N) ={E}=∗ na_own p F).
  Proof.
    rewrite /na_inv. iIntros (??) "#Hnainv Htoks".
    iDestruct "Hnainv" as (i V γ) "(% & HinV & Hinv)".
    rewrite [F as X in na_own p X](union_difference_L (↑N) F) //.
    rewrite [X in (X ∪ _)](union_difference_L {[i]} (↑N)) ?na_own_union; [|set_solver..].
    iDestruct "Htoks" as "[[Htoki $] $]". rewrite [_ p {[i]}]/na_own.
    iDestruct "Htoki" as (Vs) "[Hown #HinVs]".
    iInv N as "[HP|>Htoki]" "Hclose"; last first.
    { iDestruct "Htoki" as (V') "[Hown' _]".
      iCombine "Hown Hown'" gives %Hv. specialize (Hv i).
      rewrite /= discrete_fun_lookup_op discrete_fun_lookup_singleton /to_ofe_funR
        decide_True // in Hv; [by destruct Hv|set_solver-]. }
    iDestruct "HP" as (V') "(HP & >#HV' & >Hdis)".
    iCombine "Hown HV'" gives %Hv. specialize (Hv i).
    rewrite /= discrete_fun_lookup_op discrete_fun_lookup_singleton /to_ofe_funR
      decide_True in Hv; [|set_solver].
    apply auth_both_valid_discrete, proj1, latT_included in Hv. simpl in Hv. rewrite [in P _]Hv.
    iSpecialize ("HinVs" $! i). iCombine "HinV HinVs" as "Hin".
    iDestruct (monPred_in_intro with "Hin") as (V0) "[HV0 [% %]]".
    rewrite (lat_join_lub V (Vs i) V0) // -monPred_at_later.
    iDestruct (monPred_in_elim (▷ P)%I with "HV0 HP") as "$".
    iMod (own_update with "Hdis") as "[Hdis1 Hdis2]".
    { by apply auth_update_alloc, (alloc_option_local_update (Excl (to_latT (Vs i)))). }
    iMod ("Hclose" with "[Hown Hdis1]") as "_".
    { iNext. iRight. iExists (Vs i). rewrite (_:to_ofe_funR {[i]} Vs ≡ _); [by iFrame|].
      intros i'. rewrite /to_ofe_funR /discrete_fun_singleton /discrete_fun_insert.
      do 2 destruct decide; set_solver. }
    iIntros "!> [HP $]".
    iInv N as "[HP'|>Htoki]" "Hclose".
    { iDestruct "HP'" as (?) "(_ & _ & >Hdis1)".
      iCombine "Hdis1 Hdis2"
        gives %[Hv'%option_included _]%auth_both_valid_discrete. exfalso. naive_solver. }
    iDestruct "Htoki" as (Vi) "[Hown Hdis1]".
    iCombine "Hdis1 Hdis2" gives %EQVi%excl_auth_agree%(inj to_latT).
    (* FIXME : rewrite EQVi should work. *)
    assert (@discrete_fun_singleton _ _ (λ _, _) i (● to_latT Vi) ≡
            discrete_fun_singleton i (● to_latT (Vs i))) as -> by by f_equiv; rewrite EQVi.
    iMod (own_update_2 with "Hdis1 Hdis2") as "Hdis".
    { apply auth_update_dealloc, delete_option_local_update, _. }
    iCombine "HP Hin" as "H".
    iDestruct (monPred_in_intro with "H") as (V'') "(#HV'' & HP & % & %)".
    iMod (own_update with "Hown") as "[Hown1 Hown2]".
    { etrans.
      - by apply discrete_fun_singleton_update, auth_update_alloc,
          (op_local_update_discrete _ _ (to_latT V'')).
      - by rewrite -discrete_fun_singleton_op. }
    iMod ("Hclose" with "[-Hown1]") as "_".
    - iLeft. iExists V''. iFrame. iNext. iApply (own_proper with "Hown2").
      (* FIXME : idem *)
      f_equiv. by rewrite (right_id ε).
    - iExists (λ _, V''). iSplitL; last by auto.
      iApply (own_proper with "Hown1").
      intros i'. unfold discrete_fun_singleton, discrete_fun_insert, to_ofe_funR.
      destruct (decide (i = i')) as [<-|]=>/=; last first.
      { rewrite decide_False //. set_solver. }
      rewrite decide_True; [|set_solver]. rewrite lat_op_join'.
      do 2 f_equiv. solve_lat.
  Qed.
End proofs.
