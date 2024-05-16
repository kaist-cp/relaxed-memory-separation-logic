From stdpp Require Import gmap.
From orc11 Require Export thread.

Require Import stdpp.options.

Section Wellformedness.
   Context `{!LocFacts loc} `{CVAL: Countable VAL} `{!Shift loc} `{!Allocator loc (memory loc VAL)}.

  Notation memory := (memory loc VAL).
  Notation message := (message loc VAL).
  Notation event := (event loc VAL).
  Notation global := (@global loc _ VAL).
  Notation config := (@config loc _ VAL).
  Notation val := (@val VAL).
  Notation view := (@view loc _).
  Notation threadView := (@threadView loc _).

  Implicit Type (𝑚: message) (M: memory) (𝓝: view) (𝓥: threadView)
                (l: loc) (G: global) (c: config).

  (** Wellformedness of program local step *)
  (* memory wf *)
  Lemma alloc_step_mem_wf 𝓥1 M1 l n 𝑚s 𝓥2 M2
    (ALLOC: alloc_step 𝓥1 M1 l n 𝑚s 𝓥2 M2) (WF: Wf M1) :
    Wf M2.
  Proof. inversion ALLOC. inversion MEMALL. by eapply wf_mem_list_addins. Qed.

  Lemma dealloc_step_mem_wf 𝓥1 M1 l n 𝑚s 𝓥2 M2
    (DEALLOC: dealloc_step 𝓥1 M1 l n 𝑚s 𝓥2 M2) (WF: Wf M1) :
    Wf M2.
  Proof. inversion DEALLOC. inversion MEMALL. by eapply wf_mem_list_addins. Qed.

  Lemma write_step_mem_wf 𝓥1 M1 𝑚 o V 𝓥2 M2
    (WRITE: write_step 𝓥1 M1 𝑚 o V 𝓥2 M2) (WF: Wf M1):
    Wf M2.
  Proof. inversion WRITE. by eapply memory_write_wf. Qed.

  Lemma machine_step_mem_wf 𝓥1 M1 𝓢1 ev ot 𝑚s 𝓥2 M2 𝓢2
    (STEP: machine_step 𝓥1 M1 𝓢1 ev ot 𝑚s 𝓥2 M2 𝓢2) (WF: Wf M1) :
    Wf M2.
  Proof.
    inversion STEP; simpl; subst; auto;
      [by eapply alloc_step_mem_wf|by eapply dealloc_step_mem_wf
      |by eapply write_step_mem_wf|by eapply write_step_mem_wf].
  Qed.

  (* threadView closed *)
  Lemma read_step_closed_tview 𝓥1 M tr 𝑚 o 𝓥2
    (READ: read_step 𝓥1 M tr 𝑚 o 𝓥2)
    (CLOSED: 𝓥1 ∈ M) (WF: Wf M) : 𝓥2 ∈ M.
  Proof.
    inversion READ. eapply read_helper_closed_tview; eauto.
    destruct (mrel (mbase 𝑚)) as [V|] eqn:HR; last done.
    have ?: Some V ∈ M by rewrite -HR; eapply WF. done.
  Qed.

  Lemma write_step_closed_tview 𝓥1 M1 𝑚 o V 𝓥2 M2
    (WRITE: write_step 𝓥1 M1 𝑚 o V 𝓥2 M2)
    (CLOSED: 𝓥1 ∈ M1) : 𝓥2 ∈ M2.
  Proof. inversion WRITE. eapply write_helper_closed_tview; eauto. Qed.

  Lemma alloc_step_closed_tview 𝓥1 M1 l n 𝑚s 𝓥2 M2
    (ALLOC: alloc_step 𝓥1 M1 l n 𝑚s 𝓥2 M2)
    (CLOSED: 𝓥1 ∈ M1) : 𝓥2 ∈ M2.
  Proof.
    inversion ALLOC. inversion MEMALL.
    eapply alloc_helper_mem_closed_tview; eauto. by apply AMES.
  Qed.

  Lemma dealloc_step_closed_tview 𝓥1 M1 l n 𝑚s 𝓥2 M2
    (DEALLOC: dealloc_step 𝓥1 M1 l n 𝑚s 𝓥2 M2)
    (CLOSED: 𝓥1 ∈ M1) : 𝓥2 ∈ M2.
  Proof.
    inversion DEALLOC. inversion MEMALL.
    eapply alloc_helper_mem_closed_tview; eauto. by apply DMES.
  Qed.

  Lemma acq_fence_step_closed_tview 𝓥 𝓥' M
    (ACQ: acq_fence_step 𝓥 𝓥') (CLOSED: 𝓥 ∈ M) : 𝓥' ∈ M.
  Proof. inversion ACQ. constructor; apply CLOSED. Qed.

  Lemma rel_fence_step_closed_tview 𝓥1 𝓥2 M
    (REL: rel_fence_step 𝓥1 𝓥2) (CLOSED: 𝓥1 ∈ M) : 𝓥2 ∈ M.
  Proof. inversion REL. constructor=>/=; apply CLOSED. Qed.

  Lemma sc_fence_step_closed_tview 𝓥1 𝓥2 M 𝓢 𝓢'
    (SC: sc_fence_step 𝓥1 𝓢 𝓢' 𝓥2) (CLOSED: 𝓥1 ∈ M) (CLOSED2: 𝓢 ∈ M): 𝓥2 ∈ M.
  Proof. inversion SC. eapply sc_fence_helper_closed_tview; eauto. Qed.

  Lemma machine_step_closed_tview 𝓥1 M1 𝓢1 ev ot 𝑚s 𝓥2 M2 𝓢2
    (STEP: machine_step 𝓥1 M1 𝓢1 ev ot 𝑚s 𝓥2 M2 𝓢2)
    (WF: Wf M1) (CLOSED: 𝓥1 ∈ M1) (CLOSED𝓢: 𝓢1 ∈ M1) :
    𝓥2 ∈ M2.
  Proof.
    inversion STEP; simpl; subst.
    - eapply alloc_step_closed_tview; eauto.
    - eapply dealloc_step_closed_tview; eauto.
    - eapply read_step_closed_tview; eauto; apply WF.
    - eapply write_step_closed_tview; eauto.
    - eapply write_step_closed_tview; eauto.
      eapply read_step_closed_tview; eauto; apply WF.
    - eapply acq_fence_step_closed_tview; eauto.
    - eapply rel_fence_step_closed_tview; eauto.
    - eapply sc_fence_step_closed_tview; eauto.
  Qed.

  (* sc closed *)
  Lemma alloc_step_closed_view 𝓥1 M1 l n 𝑚s 𝓥2 M2 (V: view)
    (ALLOC: alloc_step 𝓥1 M1 l n 𝑚s 𝓥2 M2)
    (CLOSED: V ∈ M1) : V ∈ M2.
  Proof.
    inversion ALLOC. inversion MEMALL.
    eapply closed_view_list_addins_mono; eauto.
  Qed.

  Lemma dealloc_step_closed_view 𝓥1 M1 l n 𝑚s 𝓥2 M2 (V: view)
    (DEALLOC: dealloc_step 𝓥1 M1 l n 𝑚s 𝓥2 M2)
    (CLOSED: V ∈ M1) : V ∈ M2.
  Proof.
    inversion DEALLOC. inversion MEMALL.
    eapply closed_view_list_addins_mono; eauto.
  Qed.

  Lemma write_step_closed_view 𝓥1 M1 𝑚 o R 𝓥2 M2 (V: view)
    (WRITE: write_step 𝓥1 M1 𝑚 o R 𝓥2 M2)
    (CLOSED: V ∈ M1) : V ∈ M2.
  Proof.
    inversion WRITE. eapply memory_write_closed_view; eauto; apply WF.
  Qed.

  Lemma machine_step_closed_view 𝓥1 M1 𝓢1 ev ot 𝑚s 𝓥2 M2 𝓢2 (V: view)
    (STEP: machine_step 𝓥1 M1 𝓢1 ev ot 𝑚s 𝓥2 M2 𝓢2)
    (CLOSED: V ∈ M1) (WF: Wf M1) :
    V ∈ M2.
  Proof.
    inversion STEP; simpl; subst; [| |done|..|done|done|done].
    - eapply alloc_step_closed_view; eauto.
    - eapply dealloc_step_closed_view; eauto.
    - eapply write_step_closed_view; eauto.
    - eapply write_step_closed_view; eauto.
  Qed.

  Lemma machine_step_view_join_update
    (𝓥 𝓥': threadView) (σ σ': global) ev (V: view) ot 𝑚s
    (STEP: machine_step 𝓥 σ.(mem) σ.(sc) ev ot 𝑚s 𝓥' σ'.(mem) σ'.(sc))
    (WF: Wf σ) (CLOSED: V ∈ σ.(mem)) (CLOSED2: 𝓥 ∈ σ.(mem)):
    V ⊔ 𝓥'.(acq) ∈ σ'.(mem).
  Proof.
    apply join_closed_view.
    - eapply machine_step_closed_view; eauto; apply WF.
    - eapply machine_step_closed_tview; eauto; apply WF.
  Qed.

  Lemma sc_fence_step_closed_sc 𝓥1 𝓥2 M 𝓢 𝓢'
    (SC: sc_fence_step 𝓥1 𝓢 𝓢' 𝓥2) (CLOSED: 𝓥1 ∈ M) (CLOSED2: 𝓢 ∈ M): 𝓢' ∈ M.
  Proof. inversion SC. eapply sc_fence_helper_closed_sc; eauto. Qed.

  Lemma machine_step_closed_sc 𝓥1 M1 𝓢1 ev ot 𝑚s 𝓥2 M2 𝓢2
    (STEP: machine_step 𝓥1 M1 𝓢1 ev ot 𝑚s 𝓥2 M2 𝓢2)
    (CLOSED: 𝓥1 ∈ M1) (CLOSED𝓢: 𝓢1 ∈ M1) : 𝓢2 ∈ M2.
  Proof.
    inversion STEP; subst; simpl; auto.
    - eapply alloc_step_closed_view; eauto.
    - eapply dealloc_step_closed_view; eauto.
    - eapply write_step_closed_view; eauto.
    - eapply write_step_closed_view; eauto.
    - eapply sc_fence_step_closed_sc; eauto.
  Qed.

  (* threadView sqsubseteq *)
  Lemma acq_fence_step_tview_sqsubseteq 𝓥 𝓥'
    (ACQ: acq_fence_step 𝓥 𝓥') : 𝓥 ⊑ 𝓥'.
  Proof. inversion ACQ. constructor; [done|done|by apply cur_acq|done]. Qed.

  Lemma rel_fence_step_tview_sqsubseteq 𝓥1 𝓥2
    (REL: rel_fence_step 𝓥1 𝓥2) : 𝓥1 ⊑ 𝓥2.
  Proof. inversion REL. constructor=>//=. apply frel_cur. Qed.

  Lemma sc_fence_helper_tview_sqsubseteq 𝓥 𝓥' 𝓢 𝓢'
    (SC: sc_fence_helper 𝓥 𝓢 𝓥' 𝓢') : 𝓥 ⊑ 𝓥'.
  Proof.
    inversion SC. have ?: 𝓥.(acq) ⊑ 𝓥.(acq) ⊔ 𝓢 by solve_lat.
    subst 𝓢'. constructor; by [|rewrite frel_cur cur_acq|rewrite cur_acq|].
  Qed.

  Lemma sc_fence_step_tview_sqsubseteq 𝓥1 𝓢1 𝓥2 𝓢2
    (SC: sc_fence_step 𝓥1 𝓢1 𝓢2 𝓥2) : 𝓥1 ⊑ 𝓥2.
  Proof. inversion SC. by eapply sc_fence_helper_tview_sqsubseteq. Qed.

  Lemma alloc_step_tview_sqsubseteq 𝓥1 M1 l n 𝑚s 𝓥2 M2
    (ALLOC: alloc_step 𝓥1 M1 l n 𝑚s 𝓥2 M2) : 𝓥1 ⊑ 𝓥2.
  Proof. inversion ALLOC. by eapply alloc_helper_tview_sqsubseteq. Qed.

  Lemma dealloc_step_tview_sqsubseteq 𝓥1 M1 l n 𝑚s 𝓥2 M2
    (DEALLOC: dealloc_step 𝓥1 M1 l n 𝑚s 𝓥2 M2): 𝓥1 ⊑ 𝓥2.
  Proof. inversion DEALLOC. by eapply alloc_helper_tview_sqsubseteq. Qed.

  Lemma read_step_tview_sqsubseteq 𝓥1 M1 tr 𝑚 o 𝓥2
    (READ: read_step 𝓥1 M1 tr 𝑚 o 𝓥2) : 𝓥1 ⊑ 𝓥2.
  Proof. inversion READ. by eapply read_helper_tview_sqsubseteq. Qed.

  Lemma write_step_tview_sqsubseteq 𝓥1 M1 𝑚 o V 𝓥2 M2
    (WRITE: write_step 𝓥1 M1 𝑚 o V 𝓥2 M2): 𝓥1 ⊑ 𝓥2.
  Proof. inversion WRITE. by eapply write_helper_tview_sqsubseteq. Qed.

  Lemma machine_step_tview_sqsubseteq  𝓥1 M1 𝓢1 ev ot 𝑚s 𝓥2 M2 𝓢2
    (STEP: machine_step 𝓥1 M1 𝓢1 ev ot 𝑚s 𝓥2 M2 𝓢2): 𝓥1 ⊑ 𝓥2.
  Proof.
    inversion STEP; subst.
    - by eapply alloc_step_tview_sqsubseteq.
    - by eapply dealloc_step_tview_sqsubseteq.
    - by eapply read_step_tview_sqsubseteq.
    - by eapply write_step_tview_sqsubseteq.
    - etrans; [by eapply read_step_tview_sqsubseteq|by eapply write_step_tview_sqsubseteq].
    - by apply acq_fence_step_tview_sqsubseteq.
    - by apply rel_fence_step_tview_sqsubseteq.
    - by eapply sc_fence_step_tview_sqsubseteq.
  Qed.

  (* na closed *)
  Lemma memory_write_closed_na_view
    (M1: memory) 𝑚 M2 o 𝓝 𝓝'
    (WRITE: memory_write M1 𝑚 M2)
    (DRF: drf_post_write 𝑚.(mloc) 𝑚.(mto) o 𝓝 𝓝')
    (CLOSED: 𝓝 ∈ M1) : 𝓝' ∈ M2.
  Proof.
    inversion DRF. case_decide; subst.
    - apply add_awrite_id_memory. by eapply memory_write_closed_view.
    - move => l t.
      case (decide (l = 𝑚.(mloc))) => [->|NEq].
      + rewrite /set_write_time /view_lookup_write lookup_partial_alter.
        move/fmap_Some => [[t'???]/= [/fmap_Some [? [? ?]] ->]]. simplify_eq.
        do 2 eexists. split; last by eapply memory_write_new. done.
      + rewrite /set_write_time /view_lookup_write lookup_partial_alter_ne //.
        move/fmap_Some => [[????]/= [? ->]].
        by eapply memory_write_closed_view, view_lookup_w.
  Qed.

  Lemma alloc_step_closed_na 𝓥1 M1 l n 𝑚s 𝓥2 M2 𝓝
    (ALLOC: alloc_step 𝓥1 M1 l n 𝑚s 𝓥2 M2) (CLOSED: 𝓝 ∈ M1):
    alloc_new_na 𝓝 𝑚s ∈ M2.
  Proof.
    inversion ALLOC. inversion MEMALL.
    eapply closed_na_view_list_addins; eauto.
  Qed.

  Lemma dealloc_step_closed_na 𝓥1 M1 l n 𝑚s 𝓥2 M2 𝓝1
    (DEALLOC: dealloc_step 𝓥1 M1 l n 𝑚s 𝓥2 M2) (CLOSED: 𝓝1 ∈ M1) :
    alloc_new_na 𝓝1 𝑚s ∈ M2.
  Proof.
    inversion DEALLOC. inversion MEMALL.
    eapply closed_na_view_list_addins; eauto.
  Qed.

  Lemma read_step_closed_na M1 tr l o 𝓝1 𝓝2
    (DRF: drf_post_read l o tr 𝓝1 𝓝2) (CLOSED: 𝓝1 ∈ M1): 𝓝2 ∈ M1.
  Proof.
    inversion DRF. case_decide; destruct POST; subst.
    - by apply add_aread_id_memory. - by apply add_nread_id_memory.
  Qed.

  Lemma write_step_closed_na 𝓥1 M1 𝑚 o V 𝓥2 M2 𝓝1 𝓝2
    (WRITE: write_step 𝓥1 M1 𝑚 o V 𝓥2 M2)
    (DRF: drf_post_write 𝑚.(mloc) 𝑚.(mto) o 𝓝1 𝓝2)
    (CLOSED: 𝓝1 ∈ M1) : 𝓝2 ∈ M2.
  Proof. inversion WRITE. eapply memory_write_closed_na_view; eauto. Qed.

  Lemma machine_step_closed_na 𝓥1 (σ1: global) ev ot 𝑚s 𝓥2 σ2
    (STEP: machine_step 𝓥1 σ1.(mem) σ1.(sc) ev ot 𝑚s 𝓥2 σ2.(mem) σ2.(sc))
    (DRF: drf_post σ1.(na) ev ot 𝑚s σ2.(na))
    (CLOSED: σ1.(na) ∈ σ1.(mem)) (WF: Wf σ1.(mem)):
    σ2.(na) ∈ σ2.(mem).
  Proof.
    inversion DRF; subst; inversion STEP; subst; [..|done|done|done]; clear DRF STEP.
    - by eapply write_step_closed_na.
    - by eapply read_step_closed_na.
    - inversion DRF0. destruct POST as [POST1 POST2].
      rewrite POST1. apply add_awrite_id_memory, add_aread_id_memory.
      eapply write_step_closed_view; eauto.
    - by eapply dealloc_step_closed_na.
    - by eapply alloc_step_closed_na.
  Qed.

  (* alloc_inv *)
  Lemma alloc_step_alloc_inv 𝓥1 M1 l n 𝑚s 𝓥2 M2
    (ALLOC: alloc_step 𝓥1 M1 l n 𝑚s 𝓥2 M2)
    (AINV: alloc_inv M1):
    alloc_inv M2.
  Proof. inversion ALLOC. by eapply memory_alloc_alloc_inv. Qed.

  Lemma dealloc_step_alloc_inv 𝓥1 M1 l n 𝑚s 𝓥2 M2
    (DEALLOC: dealloc_step 𝓥1 M1 l n 𝑚s 𝓥2 M2)
    (AINV: alloc_inv M1) :
    alloc_inv M2.
  Proof. inversion DEALLOC. by eapply memory_dealloc_alloc_inv. Qed.

  Lemma write_step_alloc_inv 𝓥1 M1 𝑚 o V 𝓥2 M2
    (WRITE: write_step 𝓥1 M1 𝑚 o V 𝓥2 M2)
    (AINV: alloc_inv M1) :
    alloc_inv M2.
  Proof. inversion WRITE. by eapply memory_write_alloc_inv. Qed.

  Lemma machine_step_alloc_inv 𝓥1 M1 𝓢1 ev ot 𝑚s 𝓥2 M2 𝓢2
    (STEP: machine_step 𝓥1 M1 𝓢1 ev ot 𝑚s 𝓥2 M2 𝓢2)
    (AINV: alloc_inv M1):
    alloc_inv M2.
  Proof.
    inversion STEP; auto; subst; auto;
      [by eapply alloc_step_alloc_inv|by eapply dealloc_step_alloc_inv
      |by eapply write_step_alloc_inv|by eapply write_step_alloc_inv].
  Qed.

  (* dealloc_na_agree *)
  Lemma memory_write_dealloc_na_mono M1 𝑚 M2 𝓝
    (WRITE: memory_write M1 𝑚 M2)
    (AGREE: dealloc_na_agree M1 𝓝) :
    dealloc_na_agree M2 𝓝.
  Proof.
    inversion_clear WRITE.
    move => l t m; case (decide ((l, t) = (mloc 𝑚, mto 𝑚))) => [Eq|NEq].
    - rewrite Eq (lookup_mem_addins_new _ _ _ MEM) => [[<-]]. by inversion ISVAL.
    - rewrite -(lookup_mem_addins_old_eq _ _ _ _ _ MEM NEq). by apply AGREE.
  Qed.

  Lemma mem_list_addins_dealloc_na 𝑚s M1 M2 𝓝
    (ADDINS: mem_list_addins 𝑚s M1 M2)
    (ND: ∀ 𝑚, 𝑚 ∈ 𝑚s → 𝓝 !!w 𝑚.(mloc) ⊑ Some 𝑚.(mto))
    (DISJ: mem_list_disj 𝑚s)
    (AGREE: dealloc_na_agree M1 𝓝) :
    dealloc_na_agree M2 (alloc_new_na 𝓝 𝑚s).
  Proof.
    revert M2 ADDINS.
    induction 𝑚s as [|𝑚 𝑚s IH] => M2 ADDINS; inversion ADDINS; subst; [done|].
    move => l t m /=.
    case (decide ((l, t) = (mloc 𝑚, mto 𝑚))) => [Eq|NEq].
    - rewrite Eq (lookup_mem_addins_new _ _ _ ADD) => [[<-]].
      inversion Eq. by rewrite /view_lookup_write lookup_insert.
    - rewrite -(lookup_mem_addins_old_eq _ _ _ _ _ ADD NEq).
      have IH2: dealloc_na_agree M3 (alloc_new_na 𝓝 𝑚s).
      { apply IH; [|by eapply mem_list_disj_cons|done].
        move => ??. apply ND. by right. }
      etrans; first by eapply IH2.
      rewrite /view_lookup_write.
      case (decide (l = 𝑚.(mloc))) => [Eql|NEql];
        [rewrite Eql lookup_insert| by rewrite lookup_insert_ne].
      rewrite alloc_new_na_lookup_old.
      + apply ND. by left.
      + by apply mem_list_disj_cons_rest.
  Qed.

  Lemma alloc_dealloc_na  𝓥1 M1 l n 𝑚s 𝓥2 M2 𝓝
    (ALLOC: alloc_step 𝓥1 M1 l n 𝑚s 𝓥2 M2)
    (AGREE: dealloc_na_agree M1 𝓝) (CLOSED: 𝓝 ∈ M1):
    dealloc_na_agree M2 (alloc_new_na 𝓝 𝑚s).
  Proof.
    inversion_clear ALLOC.
    have DISJ := memory_alloc_disjoint _ _ _ _ _ MEMALL.
    inversion_clear MEMALL.
    eapply (mem_list_addins_dealloc_na _ _ _ _ ADD); [|done|done].
    move => 𝑚 /elem_of_list_lookup [n' In𝑚].
    destruct (𝓝 !!w 𝑚.(mloc)) as [t|] eqn:H𝓝; last done.
    apply CLOSED in H𝓝 as [? [? [_ Eqt]]].
    have Lt: (n' < n)%nat by rewrite -LEN; eapply lookup_lt_Some. exfalso.
    apply (alloc_add_fresh _ _ _ ALLOC _ Lt), memory_loc_elem_of_dom.
    destruct (AMES _ _ In𝑚) as [Eql _]. rewrite -Eql.
    intros EQ. by rewrite memory_lookup_cell EQ in Eqt.
  Qed.

  Lemma dealloc_dealloc_na  𝓥1 M1 l n 𝑚s 𝓥2 M2 𝓝
    (DEALLOC: dealloc_step 𝓥1 M1 l n 𝑚s 𝓥2 M2)
    (AGREE: dealloc_na_agree M1 𝓝) (CLOSED: 𝓝 ∈ M1):
    dealloc_na_agree M2 (alloc_new_na 𝓝 𝑚s).
  Proof.
    inversion_clear DEALLOC.
    have DISJ := memory_dealloc_disjoint _ _ _ _ _ MEMALL.
    inversion MEMALL.
    eapply (mem_list_addins_dealloc_na _ _ _ _ ADD); [|done|done].
    move => 𝑚 In𝑚.
    destruct (𝓝 !!w 𝑚.(mloc)) as [t|] eqn:H𝓝; last done.
    apply CLOSED in H𝓝 as [? [t' [Le Eqt]]].
    transitivity (Some t')=>//. apply Pos.lt_le_incl.
    by apply (memory_dealloc_max _ _ _ _ _ MEMALL _ In𝑚 (mkMsg 𝑚.(mloc) t' _) Eqt).
  Qed.

  Lemma read_step_dealloc_na 𝓥1 M1 tr 𝑚 o 𝓥2 𝓝1 𝓝2
    (READ: read_step 𝓥1 M1 tr 𝑚 o 𝓥2)
    (DRF: drf_post_read 𝑚.(mloc) o tr 𝓝1 𝓝2)
    (AGREE: dealloc_na_agree M1 𝓝1) (CLOSED: 𝓝1 ∈ M1) :
    dealloc_na_agree M1 𝓝2.
  Proof.
    inversion READ. inversion DRF.
    case_decide; destruct POST; subst;
    move => ???; [rewrite add_aread_id_eqw|rewrite add_nread_id_eqw]; by apply AGREE.
  Qed.

  Lemma write_step_dealloc_na 𝓥1 M1 𝑚 o R M2 𝓥2 𝓝1 𝓝2
    (WRITE: write_step 𝓥1 M1 𝑚 o R 𝓥2 M2)
    (DRFPRE: drf_pre_write 𝑚.(mloc) 𝓝1 𝓥1 M1 o)
    (DRFP: drf_post_write 𝑚.(mloc) 𝑚.(mto) o 𝓝1 𝓝2)
    (CLOSED: 𝓝1 ∈ M1)
    (AGREE: dealloc_na_agree M1 𝓝1):
    dealloc_na_agree M2 𝓝2.
  Proof.
    inversion_clear WRITE. inversion_clear DRFPRE. inversion_clear DRFP.
    case_decide; simplify_eq.
    - subst. by eapply add_awrite_id_dealloc_agree, memory_write_dealloc_na_mono.
    - move => l t m Eqm EqV.
      etrans; first by eapply memory_write_dealloc_na_mono.
      rewrite /view_lookup_write /set_write_time.
      case (decide (l = 𝑚.(mloc))) => [->|NEq];
        [rewrite lookup_partial_alter|by rewrite lookup_partial_alter_ne].
      case H𝓝: (𝓝1 !! mloc 𝑚) => [[????]/=|]; last done.
      apply view_lookup_w in H𝓝.
      destruct (CLOSED _ _ H𝓝) as [mn [tn' [Le Eqmm]]].
      transitivity (Some tn')=>//. change (Some tn' ⊑ Some 𝑚.(mto)).
      destruct WriteNA as [LAST ?].
      etrans; first apply (LAST (mkMsg 𝑚.(mloc) tn' mn)); auto.
      apply strict_include. by inversion WVIEW.
  Qed.

  Lemma update_step_dealloc_na 𝓥1 M1 𝓢1 𝑚 tr vr vw or ow 𝓥2 M2 𝓢2 𝓝1 𝓝2
    (STEP: machine_step 𝓥1 M1 𝓢1 (Update 𝑚.(mloc) vr vw or ow) (Some tr) [𝑚] 𝓥2 M2 𝓢2)
    (DRFP: drf_post_update 𝑚.(mloc) tr 𝑚.(mto) 𝓝1 𝓝2)
    (AGREE: dealloc_na_agree M1 𝓝1)
    (CLOSED: 𝓝1 ∈ M1):
    dealloc_na_agree M2 𝓝2.
  Proof.
    inversion STEP; subst. inversion DRFP; subst.
    clear STEP DRFP.
    have Eq1 := (read_step_tview_sqsubseteq _ _ _ _ _ _ READ).
    destruct POST as [POST1 POST2]. subst 𝓝2.
    apply add_awrite_id_dealloc_agree, (memory_write_dealloc_na_mono M1 𝑚).
    { by inversion WRITE. }
    by apply add_aread_id_dealloc_agree.
  Qed.

  Lemma machine_step_dealloc_na (g1: global) 𝓥1 ev ot 𝑚s 𝓥2 g2
    (STEP: machine_step 𝓥1 g1.(mem) g1.(sc) ev ot 𝑚s 𝓥2 g2.(mem) g2.(sc))
    (DRF': drf_pre g1.(na) 𝓥1 g1.(mem) ev)
    (DRF: drf_post g1.(na) ev ot 𝑚s g2.(na))
    (AGREE: dealloc_na_agree g1.(mem) g1.(na))
    (CLOSED: g1.(na) ∈ g1.(mem)):
    dealloc_na_agree g2.(mem) g2.(na).
  Proof.
    inversion DRF; auto; subst; inversion DRF'; subst.
    - inversion STEP; subst. by eapply write_step_dealloc_na.
    - inversion STEP; subst. by eapply read_step_dealloc_na.
    - eapply update_step_dealloc_na; eauto.
    - inversion STEP; subst. by eapply dealloc_dealloc_na.
    - inversion STEP; subst. by eapply alloc_dealloc_na.
    - inversion STEP; by subst.
  Qed.

  Lemma write_step_global_wf 𝑚 o σ σ' (Vr: view) 𝓥 𝓥'
    (WRITE: write_step 𝓥 σ.(mem) 𝑚 o Vr 𝓥' σ'.(mem))
    (DRFPRE: drf_pre_write 𝑚.(mloc) σ.(na) 𝓥 σ.(mem) o)
    (DRFP: drf_post_write 𝑚.(mloc) 𝑚.(mto) o σ.(na) σ'.(na))
    (CLOSED: 𝓥 ∈ σ.(mem)) (WF: Wf σ) (EQSC: σ.(sc) = σ'.(sc)):
    Wf σ'.
  Proof.
    constructor.
    - eapply write_step_mem_wf; [by eauto|by apply WF].
    - eapply write_step_alloc_inv; [by eauto|by apply WF..].
    - eapply write_step_dealloc_na; eauto; [by apply WF..].
    - rewrite -EQSC. eapply write_step_closed_view; [eauto|by apply WF].
    - eapply write_step_closed_na; [by eauto|by eauto|by apply WF..].
  Qed.

  Lemma machine_step_global_wf 𝓥 (σ: global) ev ot 𝑚s 𝓥' σ'
    (STEP: machine_step 𝓥 σ.(mem) σ.(sc) ev ot 𝑚s 𝓥' σ'.(mem) σ'.(sc))
    (DRF': drf_pre σ.(na) 𝓥 σ.(mem) ev)
    (DRF: drf_post σ.(na) ev ot 𝑚s σ'.(na))
    (WF: Wf σ) (CLOSED: 𝓥 ∈ σ.(mem)) :
    Wf σ'.
  Proof.
    constructor.
    - eapply machine_step_mem_wf; eauto; apply WF.
    - eapply machine_step_alloc_inv; eauto; apply WF.
    - eapply machine_step_dealloc_na; eauto; apply WF.
    - eapply machine_step_closed_sc; eauto; apply WF.
    - eapply machine_step_closed_na; eauto; apply WF.
  Qed.

  Lemma machine_step_config_wf c1 ev ot 𝑚s c2
    (STEP: machine_step c1.(lc) c1.(gb).(mem) c1.(gb).(sc) ev ot 𝑚s
                        c2.(lc) c2.(gb).(mem) c2.(gb).(sc))
    (DRF': drf_pre c1.(gb).(na) c1.(lc) c1.(gb).(mem) ev)
    (DRF: drf_post c1.(gb).(na) ev ot 𝑚s c2.(gb).(na))
    (WF: Wf c1) :
    Wf c2.
  Proof.
    constructor.
    - eapply machine_step_global_wf; eauto; apply WF.
    - by eapply machine_step_closed_tview; eauto; apply WF.
  Qed.

End Wellformedness.


Section AllocSteps.
  Context `{!LocFacts loc} `{CVAL: Countable VAL} `{!Shift loc} `{!Allocator loc (memory loc VAL)}.

  Notation memory := (memory loc VAL).
  Notation message := (message loc VAL).
  Notation event := (event loc VAL).
  Notation machine_step := (@machine_step _ _ VAL _ _).
  Notation view := (@view loc _).

  Implicit Type (𝑚: message) (M: memory) (𝓝: view).

  (* Lifting lemmas to alloc step level *)
  Lemma alloc_step_mem_fresh  𝓥1 M1 l n 𝑚s 𝓥2 M2
     (ALLOC: alloc_step 𝓥1 M1 l n 𝑚s 𝓥2 M2):
    ∀ (n' : nat), (n' < n)%nat → l >> n' ∈ dom M2 ∖ dom M1.
  Proof. inversion ALLOC. by eapply memory_alloc_fresh. Qed.

  Lemma alloc_step_mem_fresh_2  𝓥1 M1 l n 𝑚s 𝓥2 M2
     (ALLOC: alloc_step 𝓥1 M1 l n 𝑚s 𝓥2 M2):
    ∀ 𝑚, 𝑚 ∈ 𝑚s → 𝑚.(mloc) ∉ dom M1.
  Proof. inversion ALLOC. by eapply memory_alloc_fresh_2. Qed.

  Lemma alloc_step_cell_list_lookup  𝓥1 M1 l n 𝑚s 𝓥2 M2
     (ALLOC: alloc_step 𝓥1 M1 l n 𝑚s 𝓥2 M2):
    ∀ (n': nat) C,
      (cell_list l n M2) !! n' = Some C
      ↔ ∃ 𝑚, 𝑚s !! n' = Some 𝑚 ∧ C = {[𝑚.(mto) := 𝑚.(mbase)]}.
  Proof. inversion ALLOC. by eapply memory_alloc_cell_list. Qed.

  Lemma alloc_step_cell_list_map 𝓥1 M1 l n 𝑚s 𝓥2 M2
      (ALLOC: alloc_step 𝓥1 M1 l n 𝑚s 𝓥2 M2):
    (cell_list l n M2) = fmap (λ 𝑚, {[𝑚.(mto) := 𝑚.(mbase)]}) 𝑚s.
  Proof. inversion ALLOC. by eapply memory_alloc_cell_list_map. Qed.

  Lemma alloc_step_mem_lookup 𝓥1 M1 l n 𝑚s 𝓥2 M2
      (ALLOC: alloc_step 𝓥1 M1 l n 𝑚s 𝓥2 M2):
    ∀ 𝑚, 𝑚 ∈ 𝑚s
    → M2 !!c 𝑚.(mloc) = {[𝑚.(mto) := 𝑚.(mbase)]}.
  Proof. inversion ALLOC. by eapply memory_alloc_lookup. Qed.

  Lemma alloc_step_mem_insert 𝓥1 M1 l n 𝑚s 𝓥2 M2
      (ALLOC: alloc_step 𝓥1 M1 l n 𝑚s 𝓥2 M2):
    M2 = alloc_new_mem M1 𝑚s.
  Proof. inversion ALLOC. by eapply memory_alloc_insert. Qed.

  Lemma alloc_step_disjoint 𝓥1 M1 l n 𝑚s 𝓥2 M2
      (ALLOC: alloc_step 𝓥1 M1 l n 𝑚s 𝓥2 M2):
    mem_list_disj 𝑚s.
  Proof. inversion ALLOC. by eapply memory_alloc_disjoint. Qed.

  Lemma alloc_step_loc_eq 𝓥1 M1 l n 𝑚s 𝓥2 M2
      (ALLOC: alloc_step 𝓥1 M1 l n 𝑚s 𝓥2 M2):
    ∀ (n': nat) 𝑚, 𝑚s !! n' = Some 𝑚 → 𝑚.(mloc) = l >> n'.
  Proof. inversion ALLOC. by eapply memory_alloc_loc_eq. Qed.

  Lemma alloc_step_AVal 𝓥1 M1 l n 𝑚s 𝓥2 M2
      (ALLOC: alloc_step 𝓥1 M1 l n 𝑚s 𝓥2 M2):
    ∀ (n': nat) 𝑚, 𝑚s !! n' = Some 𝑚 → 𝑚.(mbase).(mval) = AVal.
  Proof. inversion ALLOC. by eapply memory_alloc_AVal. Qed.

  Lemma alloc_step_view_None 𝓥1 M1 l n 𝑚s 𝓥2 M2
      (ALLOC: alloc_step 𝓥1 M1 l n 𝑚s 𝓥2 M2):
    ∀ (n': nat) 𝑚, 𝑚s !! n' = Some 𝑚 → 𝑚.(mbase).(mrel) = None.
  Proof. inversion ALLOC. by eapply memory_alloc_view_None. Qed.

  Lemma alloc_step_length 𝓥1 M1 l n 𝑚s 𝓥2 M2
      (ALLOC: alloc_step 𝓥1 M1 l n 𝑚s 𝓥2 M2):
    length 𝑚s = n.
  Proof. inversion ALLOC. by eapply memory_alloc_length. Qed.

  Lemma alloc_step_mem_cut 𝓥1 M1 l n 𝑚s 𝓥2 M2 𝓝
      (ALLOC: alloc_step 𝓥1 M1 l n 𝑚s 𝓥2 M2):
    mem_cut M2 (alloc_new_na 𝓝 𝑚s) = alloc_new_mem (mem_cut M1 𝓝) 𝑚s.
  Proof. inversion ALLOC. by eapply mem_cut_memory_alloc. Qed.

  Lemma dealloc_step_disjoint 𝓥1 M1 l n 𝑚s 𝓥2 M2
    (DEALLOC: dealloc_step 𝓥1 M1 l n 𝑚s 𝓥2 M2) :
      mem_list_disj 𝑚s.
  Proof. inversion DEALLOC. by eapply memory_dealloc_disjoint. Qed.

  Lemma dealloc_step_remove 𝓥1 M1 l n 𝑚s 𝓥2 M2
    (DEALLOC: dealloc_step 𝓥1 M1 l n 𝑚s 𝓥2 M2) :
    ∀ (n' : nat), (n' < n)%nat
    → l >> n' ∈ (dom M1 ∖ mem_deallocated M1) ∩ mem_deallocated M2.
  Proof. inversion DEALLOC. by eapply memory_dealloc_remove. Qed.

  Lemma dealloc_step_loc_eq 𝓥1 M1 l n 𝑚s 𝓥2 M2
      (DEALLOC: dealloc_step 𝓥1 M1 l n 𝑚s 𝓥2 M2):
    ∀ (n': nat) 𝑚, 𝑚s !! n' = Some 𝑚 → 𝑚.(mloc) = l >> n'.
  Proof. inversion DEALLOC. by eapply memory_dealloc_loc_eq. Qed.

  Lemma dealloc_step_AVal 𝓥1 M1 l n 𝑚s 𝓥2 M2
      (DEALLOC: dealloc_step 𝓥1 M1 l n 𝑚s 𝓥2 M2):
    ∀ (n': nat) 𝑚, 𝑚s !! n' = Some 𝑚 → 𝑚.(mbase).(mval) = DVal.
  Proof. inversion DEALLOC. by eapply memory_dealloc_DVal. Qed.

  Lemma dealloc_step_length 𝓥1 M1 l n 𝑚s 𝓥2 M2
      (DEALLOC: dealloc_step 𝓥1 M1 l n 𝑚s 𝓥2 M2):
    length 𝑚s = n.
  Proof. inversion DEALLOC. by eapply memory_dealloc_length. Qed.

  Lemma dealloc_step_mem_cut 𝓥1 M1 l n 𝑚s 𝓥2 M2 𝓝
      (DEALLOC: dealloc_step 𝓥1 M1 l n 𝑚s 𝓥2 M2):
    mem_cut M2 (alloc_new_na 𝓝 𝑚s) = alloc_new_mem (mem_cut M1 𝓝) 𝑚s.
  Proof. inversion DEALLOC. by eapply mem_cut_memory_dealloc. Qed.

  (** Progress for alloc *)
  Definition alloc_messages (n: nat) (l : loc) : list message :=
    fmap (λ (i: nat), mkMsg (l >> i) 1%positive (mkBMes AVal None)) (seq 0%nat n).

  Definition alloc_new_tview (𝑚s: list message) 𝓥1:=
    foldr (λ 𝑚 𝓥, write_tview 𝓥 NonAtomic 𝑚.(mloc) 𝑚.(mto)) 𝓥1 𝑚s.

  Lemma alloc_messages_cons n l :
    alloc_messages (S n) l =
       mkMsg (l >> 0) 1%positive (mkBMes AVal None) :: alloc_messages n (l >> 1).
  Proof.
    rewrite /alloc_messages /=. f_equal. simpl. apply list_eq => i.
    rewrite 2!list_lookup_fmap /=. case (decide (i < n)) => [Lt| Ge].
    - do 2 (rewrite lookup_seq_lt; last done). simpl.
      rewrite shift_nat_assoc. by f_equal.
    - apply Nat.nlt_ge in Ge.
      do 2 (rewrite lookup_seq_ge; last done). done.
  Qed.

  Lemma alloc_messages_shift_1 n l :
    ∀ 𝑚 , 𝑚 ∈ alloc_messages n (l >> 1) → l >> 0 ≠ mloc 𝑚.
  Proof.
    move => 𝑚 /elem_of_list_fmap [i [-> In]] /=.
    rewrite (shift_nat_assoc _ 1) => /(shift_nat_inj _ 0). lia.
  Qed.

  Lemma alloc_memory_progress n l M1
    (FRESH: alloc M1 n l):
    let 𝑚s := alloc_messages n l in
    memory_alloc n l 𝑚s M1 (alloc_new_mem M1 𝑚s).
  Proof.
    move => 𝑚s.
    constructor; last done.
    - by rewrite map_length seq_length.
    - move => n' 𝑚 Eq.
      rewrite /𝑚s /alloc_messages in Eq.
      apply list_lookup_fmap_inv in Eq as [i [Eq1 [Eq2 Lt]%lookup_seq]].
      simpl in Eq2. subst i.
      by rewrite Eq1 /=.
    - have FRESH' := alloc_add_fresh _ _ _ FRESH.
      rewrite /𝑚s. clear FRESH 𝑚s.
      revert l FRESH'.
      induction n as [|n IH] => l FRESH.
      + rewrite /alloc_messages /=. constructor.
      + rewrite alloc_messages_cons /=.
        have MA : mem_list_addins (alloc_messages n (l >> 1)) M1
                  (alloc_new_mem M1 (alloc_messages n (l >> 1))).
        { apply (IH (l >> 1)).
          move => n' Lt. rewrite (shift_nat_assoc _ 1). apply FRESH. by lia. }
        econstructor; [exact MA| |done..].
        econstructor. simpl.
        rewrite -(mem_list_addins_old _ _ _ _ MA).
        * rewrite (_ : _ !!c _ = ∅); first done.
          apply memory_loc_not_elem_of_dom, (FRESH 0). by lia.
        * apply alloc_messages_shift_1.
  Qed.

  Lemma alloc_tview_progress n l M1 𝓥1
    (HC: 𝓥1 ∈ M1)
    (FRESH: alloc M1 n l):
    let 𝑚s := alloc_messages n l in
    alloc_helper 𝑚s 𝓥1 (alloc_new_tview 𝑚s 𝓥1).
  Proof.
    move => 𝑚s. rewrite /𝑚s.
    have FRESH' := alloc_add_fresh _ _ _ FRESH.
    clear FRESH 𝑚s. revert l FRESH'.
    induction n as [|n IH] => l FRESH.
    - rewrite /alloc_messages /=. constructor.
    - rewrite alloc_messages_cons /=.
      set 𝓥' := alloc_new_tview (alloc_messages n (l >> 1)) 𝓥1.
      have MA : alloc_helper (alloc_messages n (l >> 1)) 𝓥1 𝓥'.
      { apply (IH (l >> 1)).
        move => n' Lt. rewrite (shift_nat_assoc _ 1). apply FRESH. by lia. }
      clear IH.
      have HRlx : 𝓥'.(cur) !! (l >> 0) = None. {
        rewrite -(alloc_helper_cur_old _ _ _ _ MA);
          last by apply alloc_messages_shift_1.
        apply (closed_view_memory_None _ M1); last apply HC.
        apply memory_loc_not_elem_of_dom, (FRESH 0). by lia. }
      have HRel : 𝓥'.(rel) !! (l >> 0) = None.
        { rewrite -(alloc_helper_rel_old _ _ _ _ MA);
            last by apply alloc_messages_shift_1.
          apply (not_elem_of_dom (D:=gset loc))=>/(rel_dom _ _) /elem_of_dom [[????] Eq].
          destruct (closed_tview_cur _ _ HC _ _ (view_lookup_w _ _ _ _ _ _ Eq))
            as [m [t' [_ Eqm]]].
          apply (FRESH 0); first by lia. rewrite memory_lookup_cell in Eqm.
          apply memory_loc_elem_of_dom=>EQ. by rewrite EQ in Eqm. }
      econstructor; [exact MA|]. simpl.
      erewrite ->threadView_eq; [econstructor|..]=>//=.
      by rewrite (view_lookup_w' _ _ _ HRlx); compute.
  Qed.

  Lemma alloc_progress 𝓥1 M1 𝓢1 l n
    (CLOSED: 𝓥1 ∈ M1)
    (ALLOC: alloc M1 (Pos.to_nat n) l):
    let 𝑚s := alloc_messages (Pos.to_nat n) l in
    let 𝓥2 := (alloc_new_tview 𝑚s 𝓥1) in
    let M2 := (alloc_new_mem M1 𝑚s) in
    machine_step 𝓥1 M1 𝓢1 (Alloc l n) None 𝑚s 𝓥2 M2 𝓢1.
  Proof.
    move => 𝑚s. eapply PStepA. constructor.
    - by apply alloc_memory_progress.
    - eapply alloc_tview_progress; eauto.
  Qed.

  (** Progress for dealloc *)
  Definition dealloc_messages (M: memory) (n: nat) (l : loc) : list message :=
    fmap (λ (i: nat),
            match cell_max (M !!c (l >> i)) with
            | Some (t,_) =>
                mkMsg (l >> i) (t+1)%positive (mkBMes DVal None)
            | _ =>
                mkMsg (l >> i) 1%positive (mkBMes DVal None)
            end)
         (seq 0%nat n).

  Definition dealloc_new_mem (M: memory) (𝑚s: list message) : memory :=
    foldr (λ 𝑚 M,
       <[𝑚.(mloc) := <[𝑚.(mto) := 𝑚.(mbase)]> (M !!c 𝑚.(mloc))]> M) M 𝑚s.

  Definition dealloc_new_tview (𝑚s: list message) 𝓥1:=
    foldr (λ 𝑚 𝓥, write_tview 𝓥 NonAtomic 𝑚.(mloc) 𝑚.(mto)) 𝓥1 𝑚s.

  Lemma dealloc_messages_cons M n l :
    dealloc_messages M (S n) l =
       (match (cell_max (M !!c (l >> 0))) with
        | Some (t,_) =>
            mkMsg (l >> 0) (t+1)%positive (mkBMes DVal None)
        | _ =>
            mkMsg (l >> 0) 1%positive (mkBMes DVal None)
        end) :: dealloc_messages M n (l >> 1).
  Proof.
    rewrite /dealloc_messages /=. f_equal. apply list_eq => i.
    rewrite 2!list_lookup_fmap /=. case (decide (i < n)) => [Lt| Ge].
    - do 2 (rewrite lookup_seq_lt; last done). simpl.
      rewrite shift_nat_assoc. by f_equal.
    - apply Nat.nlt_ge in Ge.
      do 2 (rewrite lookup_seq_ge; last done). done.
  Qed.

  Lemma dealloc_messages_shift_1 M n l :
    ∀ 𝑚 , 𝑚 ∈ dealloc_messages M n (l >> 1) → l >> 0 ≠ mloc 𝑚.
  Proof.
    move => 𝑚 /elem_of_list_fmap [i [-> In]] /=.
    case_match; first case_match; simpl;
    rewrite (shift_nat_assoc _ 1) => /(shift_nat_inj _ 0); lia.
  Qed.

  Lemma dealloc_messages_length M n l:
    length (dealloc_messages M n l) = n.
  Proof. by rewrite fmap_length seq_length. Qed.

  Lemma dealloc_messages_eq_loc M n l :
    ∀ (n': nat) 𝑚, (dealloc_messages M n l) !! n' = Some 𝑚 → 𝑚.(mloc) = l >> n'.
  Proof.
    move => n' 𝑚 Eq.
    have Lt: (n' < n)%nat.
    { apply lookup_lt_Some in Eq. move : Eq. by rewrite dealloc_messages_length. }
    move : Eq.
    rewrite list_lookup_fmap (lookup_seq_lt _ _ _ Lt) /= => [[<-]].
    by case_match; [case_match|].
  Qed.

  Lemma dealloc_messages_eq_loc_2 M n l :
    ∀ 𝑚, 𝑚 ∈ (dealloc_messages M n l) →
      ∃ n':nat, (dealloc_messages M n l) !! n' = Some 𝑚 ∧ (n' < n)%nat ∧ 𝑚.(mloc) = l >> n'.
  Proof.
    move => 𝑚 /elem_of_list_lookup [n' Eqn'].
    exists n'. split; [done|split]; last by eapply dealloc_messages_eq_loc.
     apply lookup_lt_Some in Eqn'. by rewrite dealloc_messages_length in Eqn'.
  Qed.

  Lemma dealloc_messages_max M n l :
    ∀ 𝑚, 𝑚 ∈ (dealloc_messages M n l) →
      ∀ 𝑚', 𝑚' ∈ M → mloc 𝑚' = mloc 𝑚 → (mto 𝑚' < mto 𝑚)%positive.
  Proof.
    move => 𝑚 /elem_of_list_fmap [i [-> In]] /= 𝑚' In' EQL.
    have EQLOC: 𝑚'.(mloc) = l >> i by case_match; [case_match|]. clear EQL.
    rewrite /elem_of /message_ElemOf memory_lookup_cell in In'.
    assert (∃ t0 m0, cell_max (M !!c mloc 𝑚') = Some (t0, m0)) as [t0 [m0 Eqm0]]
      by (eapply gmap_top_nonempty_2; eauto with typeclass_instances).
    rewrite -EQLOC. rewrite Eqm0.
    eapply Pos.le_lt_trans.
    - eapply (gmap_top_top _ _ _ _ Eqm0), elem_of_dom_2, In'.
    - simpl. lia.
  Qed.

  Lemma dealloc_memory_progress n l (M: memory)
    (NEMP: ∀ (n':nat), (n' < n)%nat → M !!c (l >> n') ≠ ∅)
    (DEALLOC: dealloc M n l) (AINV: alloc_inv M):
    let 𝑚s := dealloc_messages M n l in
    memory_dealloc n l 𝑚s M (dealloc_new_mem M 𝑚s).
  Proof.
    move => 𝑚s.
    have REMOVE:= dealloc_remove _ _ _ DEALLOC.
    constructor; last done.
    - by rewrite map_length seq_length.
    - move => n' 𝑚 Eq. rewrite /𝑚s /dealloc_messages in Eq.
      apply list_lookup_fmap_inv in Eq as [i [Eq1 [Eq2 Lt]%lookup_seq]].
      simpl in Eq2. subst i.
      move : (REMOVE _ Lt)
        => /elem_of_difference [/memory_loc_elem_of_dom Eqm NIN].
      assert (∃ t m, cell_max (M !!c (l >> n')) = Some (t, m)) as [t [m Eqmx]].
      { by apply gmap_top_nonempty; eauto. }
      rewrite Eqmx in Eq1. rewrite Eq1 /=.
      split; [done|split; [done|split; [done|split]]]; last first.
      { apply gmap_top_lookup in Eqmx; eauto with typeclass_instances.
        do 2 eexists. by rewrite memory_lookup_cell. }
      move => t' m' Eqm'. rewrite memory_lookup_cell in Eqm'.
      split.
      + move => EqD. apply NIN, mem_deallocated_correct2.
        apply cell_deallocated_correct2.
        exists t', m'. split; [done|split;[done|]].
        have MAX: cell_max (M !!c (l >> n')) = Some (t',m')
          by apply (alloc_inv_max_dealloc _ AINV).
        by apply (gmap_top_top _ _ _ _ MAX).
      + eapply Pos.le_lt_trans.
        * by apply (gmap_top_top _ _ _ _ Eqmx), (elem_of_dom_2 _ _ _ Eqm').
        * lia.
    - clear DEALLOC. revert l 𝑚s NEMP REMOVE.
      induction n as [|n IH] => l 𝑚s NEMP REMOVE; first by constructor.
      have MA : mem_list_addins (dealloc_messages M n (l >> 1)) M
                                (dealloc_new_mem M (dealloc_messages M n (l >> 1))).
      { apply (IH (l >> 1));
          [move => ??|move => ??]; rewrite (shift_nat_assoc _ 1);
          [apply NEMP|apply REMOVE]; by lia. } clear IH.
      rewrite /𝑚s dealloc_messages_cons.
      econstructor; [exact MA|..].
      + assert (∃ t0 m0, cell_max (M !!c (l >> 0)) = Some (t0, m0)) as [t0 [m0 Eqm0]].
        { apply gmap_top_nonempty; eauto with typeclass_instances.
          by apply (NEMP 0); lia. }
        have HL: M !!c (l >> 0)
          = dealloc_new_mem M (dealloc_messages M n (l >> 1)) !!c (l >> 0).
        { rewrite (mem_list_addins_old _ _ _ _ MA); first done.
          apply dealloc_messages_shift_1. }
        rewrite Eqm0. econstructor. rewrite -HL /=. constructor.
        destruct ((M !!c (l >> 0)) !! (t0 + 1)%positive) eqn: Eqt0; last done.
        have ? : ((t0 + 1)%positive ≤ t0)%positive.
        { by apply (gmap_top_top _ _ _ _ Eqm0), (elem_of_dom_2 _ _ _ Eqt0). }
        by lia.
      + by case_match; [case_match|].
      + by case_match; [case_match|].
  Qed.

  Lemma dealloc_tview_progress n l M1 𝓥1
    (HC: 𝓥1 ∈ M1)
    (DEALLOC: dealloc M1 n l):
    let 𝑚s := dealloc_messages M1 n l in
    alloc_helper 𝑚s 𝓥1 (dealloc_new_tview 𝑚s 𝓥1).
  Proof.
    move => 𝑚s. rewrite /𝑚s.
    have REMOVE := dealloc_remove _ _ _ DEALLOC.
    clear DEALLOC 𝑚s. revert l REMOVE.
    induction n as [|n IH] => l REMOVE; first by constructor.
    rewrite dealloc_messages_cons.
    set 𝓥' := dealloc_new_tview (dealloc_messages M1 n (l >> 1)) 𝓥1.
    have MA : alloc_helper (dealloc_messages M1 n (l >> 1)) 𝓥1 𝓥'.
    { apply (IH (l >> 1)) => n' Lt. rewrite (shift_nat_assoc _ 1).
      apply REMOVE. by lia. } clear IH.
    econstructor; [exact MA|].
    econstructor=>//. remember (mloc _) as l'.
    rewrite -(_: 𝓥1.(cur) !!w l' = 𝓥'.(cur) !!w l'); last first.
    { rewrite (view_lookup_w' _ _ _ (alloc_helper_cur_old _ _ _ l' MA _)); [done|].
      subst l'. by case_match; [case_match|]; apply dealloc_messages_shift_1. }
    subst l'.
    destruct (𝓥1.(cur) !! (l >> 0)) as [t0|] eqn:Ht0;
      last by (case_match; [case_match|]; rewrite /= (view_lookup_w' _ _ _ Ht0); compute).
    apply view_lookup_w' in Ht0.
    destruct (closed_tview_cur _ _ HC _ _ Ht0) as [mo [to [Leo Eqmo]]].
    rewrite memory_lookup_cell in Eqmo.
    assert (∃ tm mm, cell_max (M1 !!c (l >> 0)) = Some (tm, mm)) as [tm [mm Eqmm]].
    { by eapply gmap_top_nonempty_2; eauto with typeclass_instances. }
    rewrite Eqmm /= Ht0.
    eapply (strict_transitive_r _ (Some to)); first apply Leo.
    eapply (strict_transitive_r _ (Some tm)), total_not_strict, Pos.lt_nle; last lia.
    apply (gmap_top_top _ _ _ _ Eqmm), (elem_of_dom_2 _ _ _ Eqmo).
  Qed.

  Lemma dealloc_progress 𝓥1 M1 𝓢1 𝓝1 l n
    (DEALLOC: dealloc M1 (Pos.to_nat n) l)
    (NEMP: ∀ n', (n' < Pos.to_nat n)%nat → M1 !!c (l >> n') ≠ ∅)
    (DRFB: ∀ n', (n' < Pos.to_nat n)%nat → 𝓝1 !! (l >> n') ⊑ 𝓥1.(cur) !! (l >> n'))
    (DRFW: ∀ n', (n' < Pos.to_nat n)%nat →
            ∀ 𝑚', 𝑚' ∈ M1 → mloc 𝑚' = l >> n' →
              Some (mto 𝑚') ⊑ 𝓥1.(cur) !!w (l >> n'))
    (AINV: alloc_inv M1)
    (CLOSED: 𝓥1 ∈ M1) :
    drf_pre_dealloc l n 𝓥1 M1 𝓝1 ∧
    let 𝑚s := dealloc_messages M1 (Pos.to_nat n) l in
    let 𝓥2 := (dealloc_new_tview 𝑚s 𝓥1) in
    let M2 := (dealloc_new_mem M1 𝑚s) in
    machine_step 𝓥1 M1 𝓢1 (Dealloc l n) None 𝑚s 𝓥2 M2 𝓢1.
  Proof.
    split; first by constructor.
    move => 𝑚s 𝓥2 M2. apply PStepD. constructor.
    - by apply dealloc_memory_progress.
    - by apply dealloc_tview_progress.
   (* - constructor.
      + move => 𝑚 In𝑚. econstructor; eauto. simpl.
        destruct (dealloc_messages_eq_loc_2 _ _ _ _ In𝑚) as  [n' [Eq' [Lt' EqL]]].
        move => ? /(DRFW _ Lt') Lt EqL'. rewrite EqL' EqL in Lt. rewrite EqL.
        by apply Lt.
      + move => 𝑚 /dealloc_messages_eq_loc_2 [n' [Eq' [Lt' EqL]]].
        rewrite EqL. apply view_sqsubseteq. by apply DRFB.
      + move => 𝑚 /dealloc_messages_eq_loc_2 [n' [Eq' [Lt' EqL]]].
        rewrite EqL. apply view_sqsubseteq. by apply DRFB.
      + move => 𝑚 /dealloc_messages_eq_loc_2 [n' [Eq' [Lt' EqL]]].
        rewrite EqL. apply view_sqsubseteq. by apply DRFB. *)
  Qed.
End AllocSteps.

Section Steps.
  Context `{!LocFacts loc} `{CVAL: Countable VAL} `{!Shift loc} `{!Allocator loc (memory loc VAL)}.

  Notation memory := (memory loc VAL).
  Notation message := (message loc VAL).
  Notation event := (event loc VAL).
  Notation machine_step := (@machine_step _ _ VAL _ _).
  Notation view := (@view loc _).
  Notation threadView := (@threadView loc _).

  Implicit Types (M: memory) (𝑚: message).

  (* Lifting lemmas to step level *)
  Lemma write_step_addins_fresh 𝓥1 M1 𝑚 o V 𝓥2 M2
    (WRITE: write_step 𝓥1 M1 𝑚 o V 𝓥2 M2) (WF: Wf M1) :
    M1 !! (𝑚.(mloc), 𝑚.(mto)) = None.
  Proof.
    inversion_clear WRITE. by eapply memory_write_addins_fresh.
  Qed.

  Lemma write_step_addins_eq 𝓥1 M1 𝑚 o V 𝓥2 M2
    (WRITE: write_step 𝓥1 M1 𝑚 o V 𝓥2 M2) :
    M2 = <[mloc 𝑚:=<[mto 𝑚:=mbase 𝑚]> (M1 !!c mloc 𝑚)]> M1.
  Proof.
    inversion_clear WRITE. by eapply memory_write_addins_eq.
  Qed.

  (** Progress for read *)
  Definition read_new_tview (o : memOrder) l t tr (R: view) 𝓥 : threadView :=
    let V : view :=
        if decide (Relaxed ⊑ o)
        then {[l := [{ t, ∅, ∅, {[tr]} }] ]}
        else {[l := [{ t, ∅, {[tr]}, ∅ }] ]} in
    read_tview 𝓥 o R V.

  Lemma tview_closed_max (𝓥: threadView) M l tm mm
    (CLOSED: 𝓥 ∈ M) (MAX: cell_max (VAL:=VAL) (M !!c l) = Some (tm, mm)) :
      𝓥.(cur) !!w l ⊑ Some tm.
  Proof.
    destruct (𝓥.(cur) !!w l) as [ct|] eqn:Eqct; last done.
    destruct (closed_tview_cur _ _ CLOSED _ _ Eqct) as [mt [tt [Lett Eqmt]]].
    cbn. transitivity (Some tt)=>//.
    apply (gmap_top_top _ _ _ _ MAX), elem_of_dom.
    eexists. by rewrite -memory_lookup_cell.
  Qed.

  Lemma read_step_progress l o M1 𝓥1 𝓝1
    (CLOSED: 𝓥1 ∈ M1) (WFM: Wf M1)
    (AINV: alloc_inv M1) (ALLOC: allocated l M1)
    (NE: M1 !!c l ≠ ∅):
    (* basic na safe *)
    let otl := 𝓥1.(cur) !!w l in  𝓝1 !!w l ⊑ otl →
    (* read na safe *)
    (o = NonAtomic →
      (∀ 𝑚', 𝑚' ∈ M1 → 𝑚'.(mloc) = l → Some 𝑚'.(mto) ⊑ otl)
      ∧ 𝓝1 !!aw l ⊑ 𝓥1.(cur) !!aw l) →
    drf_pre_read l 𝓝1 𝓥1 M1 o ∧
    ∃ 𝑚 tr 𝓝2, 𝑚.(mloc) = l
     ∧ Wf 𝑚
     ∧ (∀ t': time, is_Some (M1 !! (l,t')) → t' ⊑ 𝑚.(mto))
     ∧ read_step 𝓥1 M1 tr 𝑚 o
                  (read_new_tview o l 𝑚.(mto) tr (default ∅ 𝑚.(mbase).(mrel)) 𝓥1)
     ∧ drf_post_read l o tr 𝓝1 𝓝2
     ∧ (* initialized *)
         ((∃ t m, M1 !! (l,t) = Some m ∧ (m.(mval) = AVal → Some t ⊏ otl)) →
            isval 𝑚.(mbase).(mval)).
  Proof.
    move => otl VLe PLN.
    split. { constructor; [done|]. case_decide; [done|apply PLN; by destruct o]. }
    destruct (gmap_top_nonempty (flip (⊑)) _ NE) as [tm [mm Eqmm]].
    have Lmm: M1 !! (l, tm) = Some mm.
    { rewrite memory_lookup_cell.
      eapply gmap_top_lookup, Eqmm; eauto with typeclass_instances. }
    have Ler: 𝓥1.(cur) !!w l ⊑ Some tm
    by apply (tview_closed_max _ M1 _ _ mm).
    have ?: otl ⊑ Some tm. { rewrite -Ler. by apply view_sqsubseteq. }
    set tr  := if decide (Relaxed ⊑ o)
               then fresh_aread_id 𝓝1 l else fresh_nread_id 𝓝1 l.
    set 𝓝2 := if decide (Relaxed ⊑ o)
               then add_aread_id 𝓝1 l tr else add_nread_id 𝓝1 l tr.
    exists (mkMsg l tm mm), tr, 𝓝2.
    have MAX: ∀ (t' : time) m', M1 !! (l, t') = Some m' → t' ⊑ tm.
    { move => ???.
      apply (gmap_top_top _ _ _ _ Eqmm), elem_of_dom.
      eexists. by rewrite -memory_lookup_cell. }
    split; [done|]. split; first by eapply msg_elem_wf_pre.
    split; last split; last split.
    - move => ? [? ?]. by eapply MAX.
    - constructor; [|done..]. simpl. constructor; [done|].
      destruct mm.(mrel) as [Vmm|] eqn:EqVmm; [|done].
      rewrite /= (_: Some tm = Vmm !!w l); [done|]. move : EqVmm.
      have WFm: Wf (mkMsg l tm mm) by eapply msg_elem_wf_pre.
      apply WFm.
    - constructor; simpl. by case_decide.
    - move => [ti [mi [Eqmi Lti]]] /=. rewrite memory_lookup_cell in Eqmi.
      destruct mm.(mval) eqn:Hmv; [|exfalso; by apply (ALLOC tm mm)|done].
      have CM: cell_min (M1 !!c l) = Some (tm, mm).
      { apply (alloc_inv_min_alloc _ AINV). by rewrite -memory_lookup_cell. }
      have ?: ti ∈ dom (M1 !!c l) by apply elem_of_dom; eexists.
      have ?: tm = ti.
      { apply : (anti_symm (⊑)).
        - by apply (gmap_top_top _ _ _ _ CM).
        - by eapply (gmap_top_top _ _ _ _ Eqmm). }
      subst ti. rewrite memory_lookup_cell in Lmm.
      rewrite Eqmi in Lmm. inversion Lmm. subst. specialize (Lti Hmv).
      edestruct (irreflexivity (⊏) otl). by eapply strict_transitive_r.
  Qed.

  Lemma read_progress 𝓥1 M1 𝓢1 𝓝1 l o
    (CLOSED: 𝓥1 ∈ M1) (WFM: Wf M1)
    (AINV: alloc_inv M1) (ALLOC: allocated l M1)
    (NE: M1 !!c l ≠ ∅):
    (* basic na safe *)
    let otl := 𝓥1.(cur) !!w l in  𝓝1 !!w l ⊑ otl →
    (* read na safe *)
    (o = NonAtomic →
      (∀ 𝑚', 𝑚' ∈ M1 → mloc 𝑚' = l → Some (mto 𝑚') ⊑ otl)
      ∧ 𝓝1 !!aw l ⊑ 𝓥1.(cur) !!aw l) →
    drf_pre_read l 𝓝1 𝓥1 M1 o ∧
    ∃ 𝓥2 𝓝2 tr v, machine_step 𝓥1 M1 𝓢1 (Read l v o) (Some tr) [] 𝓥2 M1 𝓢1
    ∧ drf_post_read l o tr 𝓝1 𝓝2
    ∧ (* initialized *)
      ((∃ t m, M1 !! (l,t) = Some m ∧ (m.(mval) = AVal → Some t ⊏ otl))
        → isval v).
  Proof.
    move => otl VLe PLN.
    destruct (read_step_progress _ _ _ _ _ CLOSED WFM AINV ALLOC NE VLe PLN)
      as [DRFPR [𝑚  [tr [𝓝2 [EQL [_ [_ [RS [DRF ISVAL]]]]]]]]].
    split; [done|].
    exists (read_new_tview o l 𝑚.(mto) tr (default ∅ 𝑚.(mbase).(mrel)) 𝓥1),
            𝓝2, tr, 𝑚.(mbase).(mval).
    subst l. split; [by eapply (PStepR _ _ _ 𝑚)|done].
  Qed.

  (** Progress for writes *)
  Definition write_new_na (o : memOrder) l t 𝓝 : view :=
    if decide (Relaxed ⊑ o) then add_awrite_id 𝓝  l t else set_write_time 𝓝 l t.

  Definition write_new_mview o l t Vr 𝓥 : option view :=
    let V : view :=
      if decide (Relaxed ⊑ o) then {[l := [{t, {[t]}, ∅,∅ }] ]}
      else {[l := [{t, ∅, ∅,∅ }] ]} in
    let Vra := if decide (AcqRel ⊑ o) then 𝓥.(cur) ⊔ V else V in
    let V'  := default ∅ (𝓥.(rel) !! l) ⊔ Vra in
      if decide (Relaxed ⊑ o) then Some (V' ⊔ 𝓥.(frel) ⊔ Vr) else None.

  Lemma write_new_mview_na_time o l t Vr 𝓥:
        𝓥 .(cur) !!w l ⊑ Some t → Vr !!w l ⊑ Some t →
    (default ∅ (write_new_mview o l t Vr 𝓥)) !!w l ⊑ Some t.
  Proof.
    rewrite /write_new_mview => Le1 Le2. case_match; [|done]. simpl.
    rewrite 3!view_lookup_w_join.
    apply lat_join_lub; [|done].
    apply lat_join_lub; [|rewrite -Le1; apply view_sqsubseteq, frel_cur].
    have ?: ({[l := [{ t, {[t]},∅,∅ }] ]} : view) !!w l ⊑ Some t.
    { rewrite (view_lookup_w  _ l t {[t]} ∅ ∅); [done|].
      by rewrite /= lookup_insert. }
    apply lat_join_lub; [|case decide => ? //].
    - have Lel := rel_cur 𝓥 l. destruct (𝓥.(rel) !! l); [|done].
      etrans; [apply view_sqsubseteq,Lel|done].
    - rewrite view_lookup_w_join. by apply lat_join_lub.
  Qed.

  Lemma write_new_mview_message_wf o (l : loc) t (v : val) (Vr: view) 𝓥:
    𝓥 .(cur) !!w l ⊑ Some t → Vr !!w l ⊑ Some t →
    Wf (mkMsg (VAL:=VAL) l t (mkBMes v (write_new_mview o l t Vr 𝓥))).
  Proof.
    move => Le1 Le2 V /= LE. apply : anti_symm.
    - rewrite (_ : V = default ∅ (Some V)); [|done]. rewrite -LE.
      by apply write_new_mview_na_time.
    - move : LE. rewrite /write_new_mview. case_match; last done.
      have ?: Some t ⊑ ({[l := [{ t, {[t]}, ∅, ∅ }] ]}: view) !!w l
        by rewrite view_lookup_w_insert.
      move => [<-].
      destruct (𝓥.(rel) !! l); case_match => /=;
      rewrite ?view_lookup_w_join; solve_lat.
  Qed.

  Lemma write_new_mview_closed o l (t : time) v (Vr: view) 𝓥 M1 C V'
    (MAX : ∀ t' : time, is_Some (M1 !! (l, t')) → (t' < t)%positive)
    (CLOSED: 𝓥 ∈ M1) (CLOSEDV: Vr ∈ M1):
    (write_new_mview o l t Vr 𝓥) ∈
      (<[l := (<[t := mkBMes (VAL:=VAL) v V']>C) ]>M1).
  Proof.
    rewrite /write_new_mview.
    set V  : time_ids → view := λ ws, {[l := [{ t,ws,∅,∅ }] ]}.
    set M2: memory := <[l := (<[t := mkBMes (VAL:=VAL) v V' ]>C) ]>M1.
    have INV: ∀ ws, V ws ∈ M2.
    { move => ? l1 t1 Eq1. apply view_lookup_w_singleton_Some in Eq1 as [??].
      subst l1 t1. eexists. exists t.
      split; [done|by rewrite lookup_mem_first_eq lookup_insert]. }
    have ?: 𝓥.(cur) ∈ M2.
    { move => l1 t1.
      case (decide (l1 = l)) => [->|?] Eqt1.
      - rewrite /M2. setoid_rewrite lookup_mem_first_eq.
        eexists. exists t. rewrite lookup_insert. split; last done.
        apply CLOSED in Eqt1 as [m2 [t2 [Le2 Eqt2]]].
        etrans; first exact Le2. apply Pos.lt_le_incl, MAX. by eexists.
      - apply CLOSED in Eqt1 as [m2 [t2 Eqt2]].
        exists m2, t2. by rewrite (lookup_mem_first_ne l l1) //. }
    have ?: 𝓥.(frel) ∈ M2 by rewrite frel_cur.
    have ?: Vr ∈ M2.
    { move => l1 t1.
      case (decide (l1 = l)) => [->|?] Eqt1.
      - rewrite /M2. setoid_rewrite lookup_mem_first_eq.
        eexists. exists t. rewrite lookup_insert. split; last done.
        apply CLOSEDV in Eqt1 as [m2 [t2 [Le2 Eqt2]]].
        etrans; first exact Le2. apply Pos.lt_le_incl, MAX. by eexists.
      - apply CLOSEDV in Eqt1 as [m2 [t2 Eqt2]].
        exists m2, t2. by rewrite (lookup_mem_first_ne l l1) //. }
    case_match; last done. destruct (𝓥.(rel) !! l) as [V0|] eqn:EQV.
    - have CLOSED0: V0 ∈ M1.
      { change (Some V0 ∈ M1). rewrite -EQV. apply CLOSED. }
      have ?: V0 ∈ M2.
      { move => l1 t1.
        case (decide (l1 = l)) => [->|?] Eqt1.
        - rewrite /M2. setoid_rewrite lookup_mem_first_eq.
          eexists. exists t. rewrite lookup_insert. split; last done.
          apply CLOSED0 in Eqt1 as [m2 [t2 [Le2 Eqt2]]].
          etrans; first exact Le2. apply Pos.lt_le_incl, MAX. by eexists.
        - apply CLOSED0 in Eqt1 as [m2 [t2 Eqt2]].
          exists m2, t2. by rewrite (lookup_mem_first_ne l l1). }
      case_match; simpl; repeat apply join_closed_view => //; apply INV.
    - case_match; simpl; repeat apply join_closed_view=>//; apply INV.
  Qed.

  Lemma memory_write_addins_progress 𝓥 l o t v (Vr: view) M1 m
    (CLOSED: 𝓥 ∈ M1) (CLOSEDV: Vr ∈ M1)
    (ALLOC: allocated l M1) (Eqm: M1 !! (l, t) = Some m)
    (MAX: ∀ t': time, is_Some (M1 !! (l,t')) → t' ⊑ t):
    let VR := write_new_mview o l (t+1)%positive Vr 𝓥 in
    let 𝑚 := mkMsg l (t+1)%positive (mkBMes (VVal v) VR) in
    ∃ M2, memory_write (VAL:=VAL) M1 𝑚 M2.
  Proof.
    move => VR 𝑚.
    exists (<[l := (<[(t+1)%positive := 𝑚.(mbase) ]>(M1 !!c l)) ]>M1).
    constructor; [..|done|done|].
    - econstructor; first eauto. constructor.
      destruct ((M1 !!c l) !! (t + 1)%positive) eqn: Eqt0; last done.
      have ? : ((t + 1)%positive ≤ t)%positive.
      { apply MAX. eexists. by rewrite memory_lookup_cell. } lia.
    - have Le: ∀ V, V ∈ M1 → V !!w l ⊑ Some (t + 1)%positive.
      { move => V CV.
        destruct (V !!w l) as [tv|] eqn: Eqtv; [|done].
        apply CV in Eqtv as [m' [to' [Le' Eq']]].
        change (tv ≤ (t + 1))%positive. etrans; [apply Le'|].
        etrans; [apply MAX; by eexists|]. lia. }
      eapply write_new_mview_message_wf; eauto. apply Le, CLOSED.
    - apply write_new_mview_closed; auto.
      move => ? /MAX Le. eapply Pos.le_lt_trans; first exact Le. lia.
    - exists t. split; first by eauto. simpl. lia.
  Qed.

  Lemma write_step_addins_progress l o v t m (Vr: view) M1 𝓥1 𝓝1
    (CLOSED: 𝓥1 ∈ M1)
    (AINV: alloc_inv M1) (ALLOC: allocated l M1)
    (Eqm: M1 !! (l, t) = Some m)
    (MAX: ∀ t': time, is_Some (M1 !! (l,t')) → t' ⊑ t)
    (CLOSEDV: Vr ∈ M1) (NAR: 𝓝1 !!nr l ⊑ 𝓥1.(cur) !!nr l) :
    (* na write safe *)
    let ot := 𝓥1.(cur) in 𝓝1 !!w l ⊑ ot !!w l →
    (o = NonAtomic →
      (∀ 𝑚', 𝑚' ∈ M1 → mloc 𝑚' = l → Some (mto 𝑚') ⊑ ot !!w l) ∧
      (𝓝1 !!aw l ⊑ 𝓥1.(cur) !!aw l) ∧
      (𝓝1 !!ar l ⊑ 𝓥1.(cur) !!ar l)) →
    drf_pre_write l 𝓝1 𝓥1 M1 o ∧
    let VR := write_new_mview o l (t+1)%positive Vr 𝓥1 in
    let 𝑚 := mkMsg l (t+1)%positive (mkBMes (VVal v) VR) in
    ∃ 𝓥2 M2,
      write_step 𝓥1 M1 𝑚 o Vr 𝓥2 M2 ∧ 𝑚.(mloc) = l ∧
      drf_post_write l (t + 1)%positive o 𝓝1 (write_new_na o l (t + 1)%positive 𝓝1).
  Proof.
    move => otl Vnaw Vna. split.
    { econstructor; [done..|]. case_match; [done|]. apply Vna. by destruct o. }
    move => NAW 𝑚.
    destruct (memory_write_addins_progress _ _ o t v _ _ _
                    CLOSED CLOSEDV ALLOC Eqm MAX) as [M2 WRITE].
    have Ler: 𝓥1.(cur) !!w l ⊑ Some t.
    { apply (tview_closed_max _ M1 _ _ m); [done|].
      rewrite memory_lookup_cell in Eqm.
      apply gmap_top_inv; eauto with typeclass_instances.
      move => ? /elem_of_dom [??].
      apply MAX. rewrite memory_lookup_cell. by eexists. }
    eexists. exists M2. split; last split; [|done|].
    - econstructor; [done|]. econstructor; eauto; simpl.
      eapply strict_transitive_r; first by eauto.
      apply total_not_strict, Pos.lt_nle. lia.
    - econstructor. rewrite /write_new_na. by case_match.
  Qed.

  Lemma write_addins_progress 𝓥1 M1 𝓢1 𝓝1 l o v
    (CLOSED: 𝓥1 ∈ M1)
    (AINV: alloc_inv M1) (ALLOC: allocated l M1)
    (NEMP: ∃ t, is_Some (M1 !! (l,t)))
    (* write na safe *) (Vler: 𝓝1 !!nr l ⊑ 𝓥1.(cur) !!nr l):
    let ot := 𝓥1.(cur) in 𝓝1 !!w l ⊑ ot !!w l →
    (o = NonAtomic →
      (∀ 𝑚', 𝑚' ∈ M1 → mloc 𝑚' = l → Some (mto 𝑚') ⊑ ot !!w l) ∧
      (𝓝1 !!aw l ⊑ ot !!aw l) ∧ (𝓝1 !!ar l ⊑ ot !!ar l)) →
    drf_pre_write l 𝓝1 𝓥1 M1 o ∧
    ∃ 𝑚 𝓥2 M2, machine_step 𝓥1 M1 𝓢1 (Write l v o) None [𝑚] 𝓥2 M2 𝓢1 ∧ 𝑚.(mloc) = l ∧
    drf_post_write l 𝑚.(mto) o 𝓝1 (write_new_na o l 𝑚.(mto) 𝓝1).
  Proof.
    move => otl Vlew Vna.
    destruct NEMP as [ts [ms Eqms]]. rewrite memory_lookup_cell in Eqms.
    destruct (gmap_top_nonempty_2 (flip (⊑)) _ _ _ Eqms) as [t [m Eqm]].
    assert (EqL := gmap_top_lookup _ _ _ _ Eqm). rewrite -memory_lookup_cell in EqL.
    set MAX:= gmap_top_top _ _ _ _ Eqm.
    destruct (write_step_addins_progress _ o v t _ ∅ _ _ 𝓝1
                                           CLOSED AINV ALLOC EqL)
      as [DRFPR [𝓥2 [M2 [WRITE [EQL DRF]]]]]; [..|done|done|done|done|].
    { move => t' [m' Eqt'].
      apply (gmap_top_top _ _ _ _ Eqm), (elem_of_dom (M:=gmap time)).
      rewrite -memory_lookup_cell. by eexists. }
    split; [done|].
    exists (mkMsg l (t + 1) (mkBMes (VVal v) (write_new_mview o l (t + 1) ∅ 𝓥1))).
    do 2 eexists. split; [|done].
    eapply (PStepW _ _ _ (mkMsg l _ (mkBMes (VVal v) _))); eauto.
  Qed.

  Lemma read_step_stronger_read 𝓥 (M: memory) tr 𝑚 or1 or2 :
    let 𝓥': memOrder → threadView :=
      λ o, read_new_tview o 𝑚.(mloc) 𝑚.(mto) tr (default ∅ 𝑚.(mbase).(mrel)) 𝓥 in
    Relaxed ⊑ or1 → read_step 𝓥 M tr 𝑚 or1 (𝓥' or1) → read_step 𝓥 M tr 𝑚 or2 (𝓥' or2).
  Proof.
    move => 𝓥' oLE. inversion 1; subst; simpl.
    constructor; [|done..]. inversion READ. simpl in *. by constructor.
  Qed.

  Lemma read_step_relaxed 𝓥 𝓥' (M: memory) 𝑚 tr or1 or2:
    Relaxed ⊑ or1 → read_step 𝓥 M tr 𝑚 or1 𝓥' →
      ∃ 𝓥2, read_step 𝓥 M tr 𝑚 or2 𝓥2.
  Proof.
    move => oLE. inversion 1. subst; simpl in *.
    inversion READ. subst; simpl in *.
    eexists. constructor; [|done..]. by constructor.
  Qed.

  (* We match updates with C/Rust CASes, which have success/failure modes,
    thus effectively correspond to 3 access modes: read failure mode orf,
    read success mode or, and write success mod ow.
    C11 requires that orf ⊑ or. This condition is removed in C17.
    Additionally, progress forbids non-atomic CASes. *)
  Lemma update_read_write_addins_progress 𝓥1 M1 𝓢1 𝓝1 l vr vw orf or ow
    (CLOSED: 𝓥1 ∈ M1)
    (AINV: alloc_inv M1) (WFM: Wf M1)
    (ALLOC: allocated l M1) (NE: M1 !!c l ≠ ∅)
    (RLX: Relaxed ⊑ orf) (RLX1: Relaxed ⊑ or) (RLX2: Relaxed ⊑ ow)
    (* basic na safe *) (VLer: 𝓝1 !!nr l ⊑ 𝓥1.(cur) !!nr l) :
    let ot := 𝓥1.(cur) in 𝓝1 !!w l ⊑ ot !!w l →
    (* initialized *)
    (∃ t m, M1 !! (l,t) = Some m ∧ (m.(mval) = AVal → Some t ⊏ ot !!w l) ) →
    drf_pre 𝓝1 𝓥1 M1 (Update l vr vw or ow) ∧
    ((∃ 𝓥2 M2 𝓝2 v tr,
        v ≠ vr ∧
        machine_step 𝓥1 M1 𝓢1 (Read l (VVal v) orf) (Some tr) [] 𝓥2 M2 𝓢1 ∧
        drf_post_read l orf tr 𝓝1 𝓝2)
    ∨ (∃ 𝓥2 M2 𝓝2 tr 𝑚,
        machine_step 𝓥1 M1 𝓢1 (Update l vr vw or ow) (Some tr) [𝑚] 𝓥2 M2 𝓢1 ∧ 𝑚.(mloc) = l ∧
        drf_post_update l tr 𝑚.(mto) 𝓝1 𝓝2)).
  Proof.
    move => otl VLe INIT. split.
    { constructor.
      - constructor; [done|by rewrite (decide_True _ _ RLX1)].
      - constructor; [done..|by rewrite (decide_True _ _ RLX2)]. }
    destruct (read_step_progress _ orf _ _ 𝓝1 CLOSED WFM AINV ALLOC NE VLe)
      as [DRFPR [𝑚 [tr [𝓝2 [EQL [WFm [MAx [RS [DRFPS ISVAL]]]]]]]]];
      [move => ?; by subst orf|].
    specialize (ISVAL INIT). inversion ISVAL as [vm Eqvm].
    set 𝓥2 : memOrder → threadView :=
          λ o, read_new_tview o l 𝑚.(mto) tr (default ∅ 𝑚.(mbase).(mrel)) 𝓥1.
    case (decide (vm = vr)) => ?; last first.
    { left. exists (𝓥2 orf), M1, 𝓝2, vm, tr. split; first done. subst l.
      rewrite Eqvm. split; [by eapply (PStepR _ _ _ 𝑚)|done]. }
    subst vm l.
    have IN: 𝑚 ∈ M1 by inversion RS; inversion READ.
    have RS':= read_step_stronger_read _ _ _ _ _ or RLX RS.
    have LE':= read_step_tview_sqsubseteq _ _ _ _ _ _ RS'.
    have ?: 𝓝2 = add_aread_id 𝓝1 𝑚.(mloc) tr. {
      clear - DRFPS RLX. inversion DRFPS. subst.
      rewrite decide_True in POST; [apply POST|done]. } subst 𝓝2.
    destruct (write_step_addins_progress 𝑚.(mloc) ow vw 𝑚.(mto) 𝑚.(mbase)
                 (default ∅ 𝑚.(mbase).(mrel))
                 M1 (𝓥2 or) (add_aread_id 𝓝1 𝑚.(mloc) tr))
      as [DRFWP [𝓥3 [M2 [WRITE DRFW]]]]; auto.
    - by apply (read_step_closed_tview _ _ _ _ _ _ RS').
    - have ?:= mem_wf_closed _ WFM _ _ _ IN.
      by destruct 𝑚.(mbase).(mrel).
    - rewrite add_aread_id_eqnr VLer. by apply view_sqsubseteq, LE'.
    - rewrite add_aread_id_eqw VLe. by apply view_sqsubseteq, LE'.
    - move => ?. by subst.
    - right. exists 𝓥3, M2. eexists. exists tr. eexists. split.
      + by eapply (PStepU _ _ _ _ (mkMsg _ (𝑚.(mto) + 1) (mkBMes _ _))); eauto.
      + constructor; simpl; [done|]. inversion DRFPS. inversion DRFW.
        subst. constructor. split; [done|].
        rewrite (decide_True _ _ RLX) in POST. by destruct POST.
  Qed.

  Lemma acq_fence_progress 𝓥1 M1 𝓢1:
    ∃ 𝓥2, machine_step 𝓥1 M1 𝓢1 (Fence AcqRel Relaxed) None [] 𝓥2 M1 𝓢1.
  Proof. eexists. do 2 constructor. Qed.

  Lemma rel_fence_progress 𝓥1 M1 𝓢1:
    ∃ 𝓥2, machine_step 𝓥1 M1 𝓢1 (Fence Relaxed AcqRel) None [] 𝓥2 M1 𝓢1.
  Proof. eexists. do 2 constructor. Qed.

  Lemma sc_fence_progress 𝓥1 M1 𝓢1:
    ∃ 𝓥2 𝓢2, machine_step 𝓥1 M1 𝓢1 (Fence SeqCst SeqCst) None [] 𝓥2 M1 𝓢2.
  Proof. do 2 eexists. constructor. constructor=>//=. Qed.

End Steps.
