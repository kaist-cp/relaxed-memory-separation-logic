Require Import stdpp.namespaces.
Require Import iris.bi.telescopes.

From iris.proofmode Require Import proofmode.
Require Export iris.bi.lib.atomic.

Require Export gpfsl.base_logic.weakestpre.
Require Import gpfsl.logic.invariants.

Require Import iris.prelude.options.

Definition atomic_wp `{!noprolG Σ} {TA TB : tele}
  (e: expr) (* expression *)
  (tid : thread_id)
  (E : coPset) (* implementation masks *)
  (α: TA → vProp Σ) (* atomic pre-condition *)
  (β: TA → TB → vProp Σ) (* atomic post-condition *)
  (POST: TA → TB → vProp Σ) (* private post condition *)
  (f: TA → TB → val) (* Turn the return data into the return value *)
  : vProp Σ :=
    ∀ (Φ : val → vProp Σ),
      (* Fix the inner mask to the shared global namespace histN *)
      atomic_update (⊤∖E) (↑histN) α β (λ.. x y, POST x y -∗ Φ (f x y)) -∗
      WP e @ tid ; ⊤ {{ Φ }}.

Notation "'<<<' ∀ x1 .. xn , α '>>>' e @ tid ; E '<<<' ∃ y1 .. yn , β , 'RET' v , POST '>>>'" :=
  (atomic_wp (TA:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
             (TB:=TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
             e%E
             tid
             E
             (tele_app (TT:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. )) $
                       λ x1, .. (λ xn, α%I) ..)
             (tele_app (TT:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. )) $
                       λ x1, .. (λ xn,
                         tele_app (TT:=TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
                         (λ y1, .. (λ yn, β%I) .. )
                        ) .. )
             (tele_app (TT:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. )) $
                       λ x1, .. (λ xn,
                         tele_app (TT:=TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
                         (λ y1, .. (λ yn, POST%I) .. )
                       ) .. )
             (tele_app (TT:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. )) $
                       λ x1, .. (λ xn,
                         tele_app (TT:=TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
                         (λ y1, .. (λ yn, v%V) .. )
                        ) .. )
  )
  (at level 20, E, α, β, v at level 200, x1 binder, xn binder, y1 binder, yn binder,
   format "'[hv' '<<<'  ∀  x1  ..  xn ,  α  '>>>'  '/  ' e  @  tid ;  E  '/' '[    ' '<<<'  ∃  y1  ..  yn ,  β ,  '/' 'RET'  v ,  POST  '>>>' ']' ']'")
  : bi_scope.

Notation "'<<<' ∀ x1 .. xn , α '>>>' e @ tid ; E '<<<' β , 'RET' v , POST '>>>'" :=
  (atomic_wp (TA:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
             (TB:=TeleO)
             e%E
             tid
             E
             (tele_app (TT:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. )) $
                       λ x1, .. (λ xn, α%I) ..)
             (tele_app (TT:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. )) $
                       λ x1, .. (λ xn,
                         tele_app (TT:=TeleO) β%I
                        ) .. )
             (tele_app (TT:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. )) $
                       λ x1, .. (λ xn,
                         tele_app (TT:=TeleO) POST%I
                        ) .. )
             (tele_app (TT:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. )) $
                       λ x1, .. (λ xn,
                         tele_app (TT:=TeleO) v%V
                        ) .. )
  )
  (at level 20, α, β, v at level 200, x1 binder, xn binder,
   format "'[hv' '<<<'  ∀  x1  ..  xn ,  α  '>>>'  '/  ' e  @  tid ;  E  '/' '[    ' '<<<'  β ,  '/' 'RET'  v ,  POST  '>>>' ']' ']'")
  : bi_scope.

Notation "'<<<' α '>>>' e @ tid ; E '<<<' ∃ y1 .. yn , β , 'RET' v , POST '>>>'" :=
  (atomic_wp (TA:=TeleO)
             (TB:=TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
             e%E
             tid
             E
             (tele_app (TT:=TeleO) α%I)
             (tele_app (TT:=TeleO) $
                       tele_app (TT:=TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
                         (λ y1, .. (λ yn, β%I) .. ))
             (tele_app (TT:=TeleO) $
                       tele_app (TT:=TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
                         (λ y1, .. (λ yn, POST%I) .. ))
             (tele_app (TT:=TeleO) $
                       tele_app (TT:=TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
                         (λ y1, .. (λ yn, v%V) .. ))
  )
  (at level 20, E, α, β , v at level 200, y1 binder, yn binder,
   format "'[hv' '<<<'  α  '>>>'  '/  ' e  @  tid ;  E  '/' '[    ' '<<<'  ∃  y1  ..  yn ,  β ,  '/' 'RET'  v ,  POST  '>>>' ']' ']'")
  : bi_scope.

Notation "'<<<' α '>>>' e @ tid ; E '<<<' β , 'RET' v , POST '>>>'" :=
  (atomic_wp (TA:=TeleO)
             (TB:=TeleO)
             e%E
             tid
             E
             (tele_app (TT:=TeleO) α%I)
             (tele_app (TT:=TeleO) $ tele_app (TT:=TeleO) β%I)
             (tele_app (TT:=TeleO) $ tele_app (TT:=TeleO) POST%I)
             (tele_app (TT:=TeleO) $ tele_app (TT:=TeleO) v%V)
  )
  (at level 20, E, α, β, v at level 200,
   format "'[hv' '<<<'  α  '>>>'  '/  ' e  @  tid ;  E  '/' '[    ' '<<<'  β ,  '/' 'RET'  v ,  POST  '>>>' ']' ']'")
  : bi_scope.

(** Theory *)
Section lemmas.
  Context `{!noprolG Σ} {TA TB : tele}.
  Notation vProp := (vProp Σ).
  Implicit Types (α : TA → vProp) (β : TA → TB → vProp) (f : TA → TB → val).

  Lemma atomic_wp_mask_weaken e tid E1 E2 α β POST f :
    E1 ⊆ E2 → atomic_wp e tid E1 α β POST f -∗ atomic_wp e tid E2 α β POST f.
  Proof.
    iIntros (HE) "Hwp". iIntros (Φ) "AU". iApply "Hwp".
    iApply atomic_update_mask_weaken; last done. set_solver.
  Qed.

  (* Atomic triples imply sequential triples. *)
  Lemma atomic_wp_seq e tid E α β POST f
    (Sub: ↑histN ⊆ ⊤ ∖ E) :
    atomic_wp e tid E α β POST f -∗
    ∀ Φ, ∀.. x, α x -∗ (∀.. y, β x y -∗ POST x y -∗ Φ (f x y)) -∗ WP e @ tid; ⊤ {{ Φ }}.
  Proof.
    iIntros "Hwp" (Φ x) "Hα HΦ".
    iApply wp_frame_wand_l. iSplitL "HΦ"; first iAccu. iApply "Hwp".
    iAuIntro. iAaccIntro with "Hα"; first by eauto. iIntros (y) "Hβ !>".
    rewrite !tele_app_bind. iIntros "HP HΦ". by iApply ("HΦ" with "Hβ HP").
  Qed.

  (** This version matches the Texan triple, i.e., with a later in front of the
  [(∀.. y, β x y -∗ Φ (f x y))]. *)
  Lemma atomic_wp_seq_step e tid E α β POST f
    (Sub: ↑histN ⊆ ⊤ ∖ E) :
    TCEq (to_val e) None →
    atomic_wp e tid E α β POST f -∗
    ∀ Φ, ∀.. x, α x -∗ ▷ (∀.. y, β x y -∗ POST x y -∗ Φ (f x y)) -∗ WP e @ tid; ⊤ {{ Φ }}.
  Proof.
    iIntros (TCE) "H"; iIntros (Φ x) "Hα HΦ".
    iApply (wp_step_fupd _ _ ⊤ _ (∀.. y : TB, β x y -∗ POST x y -∗ Φ (f x y))%I
      with "[$HΦ //]"); [by rewrite ->TCEq_eq in TCE|done|].
    iApply (atomic_wp_seq with "H Hα"); [done..|].
    iIntros (y) "Hβ HP HΦ". by iApply ("HΦ" with "Hβ HP").
  Qed.

  (* Sequential triples with the inner mask for a physically atomic [e] are atomic. *)
  Lemma atomic_seq_wp_atomic e tid E α β POST f `{!Atomic e} :
    (∀ Φ, ∀.. x, α x -∗ (∀.. y, β x y -∗ POST x y -∗ Φ (f x y)) -∗
    WP e @ tid; ↑histN {{ Φ }}) -∗
    atomic_wp e tid E α β POST f.
  Proof.
    iIntros "Hwp" (Φ) "AU". iMod "AU" as (x) "[Hα [_ Hclose]]".
    iApply ("Hwp" with "Hα"). iIntros (y) "Hβ HP".
    iMod ("Hclose" with "Hβ") as "HΦ".
    rewrite ->!tele_app_bind. iApply ("HΦ" with "HP").
  Qed.

  (* Sequential triples with a persistent precondition and no initial quantifier
  are atomic. *)
  Lemma persistent_seq_wp_atomic e tid E
        (α : [tele] → vProp) (β POST : [tele] → TB → vProp)
        (f : [tele] → TB → val) {HP : Persistent (α [tele_arg])} :
    (∀ Φ, α [tele_arg] -∗ (∀.. y, β [tele_arg] y -∗ POST [tele_arg] y -∗ Φ (f [tele_arg] y)) -∗
    WP e @ tid; ⊤ {{ Φ }}) -∗
    atomic_wp e tid E α β POST f.
  Proof.
    simpl in HP. iIntros "Hwp" (Φ) "HΦ". iApply fupd_wp.
    iMod ("HΦ") as "[#Hα [Hclose _]]". iMod ("Hclose" with "Hα") as "HΦ".
    iApply wp_fupd. iApply ("Hwp" with "Hα"). iIntros "!>" (y) "Hβ POST".
    iMod ("HΦ") as "[_ [_ Hclose]]". iMod ("Hclose" with "Hβ") as "HΦ".
    rewrite !tele_app_bind. by iApply ("HΦ" with "POST").
  Qed.

  (* We can open invariants around atomic triples.
     (Just for demonstration purposes; we always use [iInv] in proofs.) *)
  Lemma wp_atomic_inv e tid E α β POST f N I `{!Objective I} :
    ↑N ⊆ E →
    atomic_wp e tid (E ∖ ↑N) (λ.. x, ▷ I ∗ α x) (λ.. x y, ▷ I ∗ β x y) POST f -∗
    inv N I -∗ atomic_wp e tid E α β POST f.
  Proof.
    intros ?. iIntros "Hwp #Hinv" (Φ) "AU". iApply "Hwp". iAuIntro.
    iInv N as "HI". iApply (aacc_aupd with "AU"); first solve_ndisj.
    iIntros (x) "Hα". iAaccIntro with "[HI Hα]"; rewrite ->!tele_app_bind; first by iFrame.
    - (* abort *)
      iIntros "[HI $]". by eauto with iFrame.
    - (* commit *)
      iIntros (y). rewrite ->!tele_app_bind. iIntros "[HI Hβ]". iRight.
      iExists y. rewrite ->!tele_app_bind. by eauto with iFrame.
  Qed.

End lemmas.
