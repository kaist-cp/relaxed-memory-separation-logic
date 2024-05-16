From iris.algebra Require Import auth excl lib.excl_auth.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import adequacy ownp.
From gpfsl.base_logic Require Import iwp.
From gpfsl.base_logic Require Import weakestpre.

Require Import iris.prelude.options.

Local Existing Instances
  histGpreS_hist histGpreS_freeable histGpreS_read histGpreS_na_view
  histGpreS_at_write histGpreS_tview
  hist_inG
  ownP_inG ownP_invG ownPPre_invG ownPPre_state_inG
  noprolG_ownpG
  .

Class noprolGpreS (Σ : gFunctors) : Set := NoprolG {
  noprolGpreS_ownPG : ownPGpreS nopro_lang Σ;
  noprolGpreS_histG : gen_heapGpreS loc (option cell) Σ;
  (* for ownership of block deallocations *)
  noprolGpreS_freeable : inG Σ (authR hist_freeableUR);
  (* for tracking read events *)
  noprolGpreS_read : inG Σ (authR hist_readUR);
  (* for tracking simple views *)
  noprolGpreS_na_view : inG Σ viewR;
  (* for tracking atomic write events *)
  noprolGpreS_at_write : inG Σ (authR hist_writesUR);
  (* for thread views *)
  noprolGpreS_tview : inG Σ (authR (latUR tview_Lat));
}.

Local Existing Instances
  noprolGpreS_ownPG noprolGpreS_histG noprolGpreS_freeable noprolGpreS_read
  noprolGpreS_na_view noprolGpreS_at_write noprolGpreS_tview.

Definition noprolΣ : gFunctors := #[
    ownPΣ nopro_lang ;
    gen_heapΣ loc (option cell);
    GFunctor (authR hist_freeableUR);
    GFunctor (authR hist_readUR);
    GFunctor viewR;
    GFunctor (authR hist_writesUR);
    GFunctor (authR (latUR tview_Lat))
  ].

Global Instance subG_noprolGpreS {Σ} : subG noprolΣ Σ → noprolGpreS Σ.
Proof. solve_inG. Qed.

Implicit Type (φ : val → Prop) (tid : thread_id).
Lemma noprol_adequacy Σ `{!noprolGpreS Σ} e (σ : state) 𝓥 φ :
  Wf σ →
  𝓥 ∈ σ.(mem) →
  (∀ `{noprolG Σ} tid, ⊢ WP e @ tid; ⊤ {{ v, ⌜φ v⌝ }}) →
  adequate NotStuck (e at 𝓥) σ (λ v _, φ v).
Proof.
  (* TODO: we cannot use [ownP_adequacy] because it fixes a state_interp. We
    have to embed [ownP_adequacy]'s proof here instead. *)
  intros WFσ H𝓥 Hwp; eapply (wp_adequacy _ _); iIntros (Hinv ?).
  set (M := mem_cut σ.(mem) σ.(na)).
  iMod (gen_heap_init (to_hist M)) as (HEAPG) "(Hist & hists & metas)".
  iMod (own_alloc (● (∅ : hist_freeableUR))) as (hist_freeable_name) "hf".
  { by apply auth_auth_valid. }
  iMod (own_alloc (● to_atr σ.(na))) as (hist_atread_name) "har".
  { by apply auth_auth_valid, to_atr_valid. }
  iMod (own_alloc (● to_atw σ.(na))) as (hist_atwrite_name) "haw".
  { by apply auth_auth_valid, to_atw_valid. }
  iMod (own_alloc (● to_nar σ.(na))) as (hist_naread_name) "hn".
  { by apply auth_auth_valid, to_nar_valid. }
  iMod (own_alloc (● to_latT σ.(sc))) as (hist_sc_name) "sc".
  { by apply auth_auth_valid. }
  iMod (own_alloc (● to_latT 𝓥.(acq) ⋅ ◯ to_latT 𝓥.(acq)))
    as (hist_gtime_name) "[hV1 hV2]".
  { by apply auth_both_valid_discrete. }
  iMod (own_alloc (●E σ ⋅ ◯E σ)) as (hist_phys_name) "[HAσ HNσ]".
  { by apply excl_auth_valid. }
  set HISTPREG := {| histGpreS_hist := HEAPG |}.
  set HISTG := HistGS Σ _ hist_freeable_name
                      hist_atwrite_name hist_atread_name hist_naread_name
                      hist_sc_name hist_gtime_name.
  set OWNPG := OwnPGS _ _ _ _ hist_phys_name.
  set NOPROLG := NoProLG _ _ _.
  iAssert (hist_ctx σ) with "[- hV2 HAσ HNσ]" as "CTX".
  { iExists _, _,_. iFrame. iPureIntro.
    split; [done|split; [done|split;[apply H𝓥|done]]]. }
  iExists (λ σ _, hist_interp σ), (λ _, True%I). iSplitR "hV2".
  - rewrite /hist_interp /=. iFrame "HAσ".
    iApply (invariants.inv_alloc histN). iNext. iExists _. rewrite /ownP. iFrame.
  - iMod (own_alloc (● to_latT 𝓥)) as (tid) "tid".
    { by apply auth_auth_valid. }
    iDestruct (Hwp _ tid) as "H".
    iSpecialize ("H" $! 𝓥.(cur)). rewrite wp_eq /wp_def /=.
    iModIntro. iApply (iwp_wand with "[-]").
    + iApply ("H" with "[//] tid"). rewrite seen_eq /seen_def. by iFrame.
    + by iIntros ([v 𝓥']) "/= [_ %]".
Qed.

Lemma noprol_adequacy' Σ `{!noprolGpreS Σ} e φ:
  (∀ `{noprolG Σ} tid, ⊢ WP e @ tid; ⊤ {{ v, ⌜φ v⌝ }}) →
  adequate NotStuck (e at init_tview) (mkGB ∅ ∅ ∅) (λ v _, φ v).
Proof.
  intros. eapply noprol_adequacy=>//. split=>//. split=> l /=.
  - destruct (memory_loc_not_elem_of_dom (VAL := val) l ∅) as [EQ _].
    rewrite EQ //. intros t m. naive_solver.
  - destruct (memory_loc_not_elem_of_dom (VAL := val) l ∅) as [EQ _].
    rewrite EQ //.
Qed.
