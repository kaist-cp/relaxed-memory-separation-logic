From iris.proofmode Require Import proofmode.

From gpfsl.logic Require Import proofmode.
From gpfsl.logic Require Import new_delete.

From gpfsl.examples.stack Require Import spec_na code_na.

Require Import iris.prelude.options.

(** A stack that is built up by non-atomics. **)
Section defs.
Context `{!noprolG Σ} (P: lit → vProp Σ).
Local Notation vProp := (vProp Σ).

Local Notation next := 0%nat (only parsing).
Local Notation data := 1%nat (only parsing).

Definition NAStack'
  :  (loc -d> list lit -d> vPropO Σ) -d> loc -d> list lit -d> vPropO Σ
  := (fun F l A => ∃ (v': val), (l >> next) ↦ v' ∗
        match A with
        | nil     => ⌜v' = #0%Z⌝
        | v :: A' => ∃ l', ⌜v' = #(LitLoc l')⌝ ∗ ⎡ † l' … 2 ⎤ ∗
                      (l' >> data) ↦ #v ∗ P v ∗ ▷ F l' A'
        end)%I.

#[local] Instance NAStack'_contractive : Contractive NAStack'.
Proof.
  intros ? ? ? H ? A.
  apply bi.exist_ne => ?.
  apply bi.sep_ne; [done|].
  destruct A as [|v A]; [done|].
  apply bi.exist_ne => ?.
  repeat (apply bi.sep_ne; [done|]).
  f_contractive. by apply H.
Qed.

Definition NAStack_def := fixpoint NAStack'.
(* The stack resources contain freeable blocks, so that we can deallocate it. *)
Definition NAStack s A := (⎡ † s … 1 ⎤ ∗ NAStack_def s A)%I.
End defs.

Section proof.
Context `{!noprolG Σ} (P: lit → vProp Σ).
Local Notation vProp := (vProp Σ).

Implicit Types (s: loc) (A: list lit) (v: lit) (tid: thread_id).

Lemma new_stack_spec tid:
  {{{ True }}} new_stack [] @ tid; ⊤ {{{ (s: loc), RET #s; NAStack P s nil }}}.
Proof.
  iIntros (Φ) "_ Post".
  wp_lam.
  (* allocation *)
  wp_apply wp_new; [done..|].
  iIntros (s) "([H†|%] & Hs & Hm)"; [|done].
  wp_let.
  (* initialize head as 0 *)
  rewrite own_loc_na_vec_singleton. wp_write.
  (* finish *)
  iApply "Post".
  rewrite /NAStack /NAStack_def (fixpoint_unfold (NAStack' P) _ _).
  iFrame "H†".
  iExists #0. rewrite shift_0. by iFrame.
Qed.

Lemma push_spec s A v tid:
  {{{ NAStack P s A ∗ P v }}}
     push [ #s; #v] @ tid; ⊤
  {{{ RET #☠; NAStack P s (v :: A) }}}.
Proof.
  iIntros (Φ) "[[Hs† Stack] P] Post".
  wp_lam.
  (* allocate new node *)
  wp_apply wp_new; [done..|].
  iIntros (n) "([H†|%] & Hn & Hm)"; [|done].
  (* write data to new node *)
  wp_let. rewrite own_loc_na_vec_cons own_loc_na_vec_singleton.
  iDestruct "Hn" as "[Hn Hd]".
  wp_op. wp_write.
  (* read current head *)
  rewrite /NAStack_def (fixpoint_unfold (NAStack' P) _ _).
  iDestruct "Stack" as (h) "[oH oT]".
  rewrite shift_0. wp_read.
  wp_pures.
  (* let new node point to the current head *)
  rewrite shift_0. wp_write.
  (* update head to new node *)
  wp_write.
  (* finish *)
  iApply "Post".
  rewrite /NAStack /NAStack_def (fixpoint_unfold (NAStack' P) _ _).
  iFrame "Hs†".
  iExists #n. rewrite shift_0. iFrame "oH".
  iExists n. iSplit; [done|]. iFrame.

  iNext. rewrite (fixpoint_unfold (NAStack' P) _ _).
  iExists h. rewrite shift_0. by iFrame.
Qed.

Lemma pop_spec s A tid:
  {{{ NAStack P s A }}}
     pop [ #s] @ tid; ⊤
  {{{ (v: lit), RET #v;  match A with
                         | nil => ⌜v = 0⌝ ∗ NAStack P s A
                         | v' :: A' =>  ⌜v = v'⌝ ∗ NAStack P s A' ∗ P v
                         end }}}.
Proof.
  iIntros (Φ) "[Hs† Stack] Post".
  wp_lam.

  (* read current head *)
  rewrite {1}/NAStack_def (fixpoint_unfold (NAStack' P) _ _).
  iDestruct "Stack" as (h) "[oH oT]".
  rewrite shift_0. wp_read. wp_let.

  destruct A as [|v' A'].
  - (* empty stack, nothing to pop *)
    iDestruct "oT" as "%". subst h.
    wp_pures.
    iApply "Post". iSplit; [done|].
    rewrite /NAStack /NAStack_def (fixpoint_unfold (NAStack' P) _ _).
    iFrame "Hs†".
    iExists #0. rewrite shift_0. by iFrame.
  - (* popping v' *)
    iDestruct "oT" as (l') "(% & H† & od & P & oT)". subst h.
    wp_pures.
    (* read the data of the head element *)
    wp_read. wp_pures.
    (* read the next of the head element *)
    rewrite /NAStack (fixpoint_unfold (NAStack' P) _ _).
    iDestruct "oT" as (h') "[on oT]".
    wp_read. wp_let.
    (* update head with that next node *)
    wp_write.
    (* free the popped node *)
    wp_apply (wp_delete _ tid 2 _ [h'; #v'] with "[od on H†]"); [done|done|..].
    { rewrite own_loc_na_vec_cons own_loc_na_vec_singleton shift_0.
      by iFrame. }

    (* finish, with A' as the remaining stack *)
    iIntros "_".
    wp_seq. iApply "Post". iSplit; [done|]. iFrame "Hs† P".
    rewrite /NAStack_def (fixpoint_unfold (NAStack' P) _ _).
    iExists h'. rewrite shift_0. by iFrame.
Qed.

End proof.

Definition na_stack_instance `{!noprolG Σ} : na_stack_spec Σ :=
  {| spec_na.new_stack_spec := new_stack_spec;
     spec_na.push_spec      := push_spec;
     spec_na.pop_spec       := pop_spec |}.

#[global] Typeclasses Opaque NAStack.
