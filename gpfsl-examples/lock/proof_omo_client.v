From iris.algebra Require Import excl_auth gset.
From iris.bi.lib Require Import fractional.
From iris.proofmode Require Import tactics.

From gpfsl.lang Require Import notation.
From gpfsl.logic Require Import new_delete logatom invariants proofmode.
From gpfsl.examples.lock Require Import spec_trylock_composition.
From gpfsl.examples.omo Require Import omo omo_preds append_only_loc.
From gpfsl.examples Require Import set_helper uniq_token.

Require Import iris.prelude.options.

Definition clN := nroot .@ "clN".

Section Client.
  Context `{!noprolG Σ,
            !uniqTokG Σ,
            !omoGeneralG Σ,
            !omoSpecificG Σ lock_event_type lock_state}.

  Implicit Types
    (E : history lock_event_type) (omo : omoT) (stlist : list lock_state)
    (s d : loc).

  Local Notation iProp := (iProp Σ).
  Local Notation vProp := (vProp Σ).
  Local Open Scope nat_scope.

  (** Assuming composable linearizability spec of spinlock *)
  Hypothesis lck : lock_spec Σ.

  Definition prog  : expr :=
    let: "l" := lck.(new_lock) [] in
    let: "res" := lck.(try_lock) ["l"] in (* Must succeed *)
    lck.(unlock) ["l"];;
    "res".

  Lemma client_lock_spec tid :
    {{{ True }}}
      prog @ tid; ⊤
    {{{ RET #true; True }}}.
  Proof using All.
    iIntros (Φ) "_ Post". rewrite /prog.
    iDestruct (view_at_intro emp with "[]") as (V1) "[#⊒V1 _]"; [done|].
    wp_apply (new_lock_spec lck (clN .@ "lck") _ _ emp%I with "[$⊒V1]"); [done|].
    iIntros (γg γs l V2 M1) "(#⊒V2 & M● & #⊒M1@V2 & _)".
    wp_pures.

    iAssert (▷ LockInv lck _ _ _ _ _ _ _)%I with "[M●]" as "M●"; [iFrame|].
    iDestruct (view_at_elim with "⊒V2 ⊒M1@V2") as "⊒M1".
    awp_apply (try_lock_spec lck with "⊒V2 ⊒M1"); [solve_ndisj|].
    iAaccIntro with "M●".
    { iIntros "M● !>". iFrame. }

    iIntros (b2 V3 ty2 omo2 stlist2 M2) "(#⊒V3 & M● & #⊒M2@V3 & _ & _ & CASE)".
    iDestruct (LockInv_OmoAuth_acc with "M●") as "[>M● Close]".
    iDestruct (OmoAuth_wf with "M●") as %[OMO_GOOD2 _].
    iDestruct ("Close" with "[M●]") as "M●"; [done|].

    (* Prove that `try_lock` succeeds *)
    destruct b2; last first.
    { iDestruct "CASE" as "[(-> & [%gen1 ->] & ->) _]". simpl in *.
      destruct gen1; last first.
      { eapply (lookup_omo_surjective _ _ _ 1) in OMO_GOOD2 as [eidx Heidx]; [|done].
        destruct eidx; simpl in Heidx; destruct gen; inversion Heidx. }
      eapply (omo_read_op_step _ _ _ 0 0 1) in OMO_GOOD2 as STEP; [|done..].
      by inversion STEP. }

    iDestruct "CASE" as "[(-> & -> & [%st2 ->]) _]". simpl in *.
    iModIntro. iIntros "[_ Locked]". wp_pures.

    iAssert (▷ LockInv lck _ _ _ _ _ _ _)%I with "[M●]" as "M●"; [iFrame|].
    have DISJ : clN .@ "lck" ## histN by solve_ndisj.
    awp_apply (unlock_spec lck _ DISJ _ _ _ _ _ emp%I with "⊒V2 ⊒M1 [] Locked"); [done|].
    iAaccIntro with "M●".
    { iIntros "M● !>". iFrame. }

    iIntros (V4 st3 M3) "(#⊒V4 & M● & #⊒M3@V4 & _)".
    iModIntro. iIntros "_". wp_pures. by iApply "Post".
  Qed.
End Client.
