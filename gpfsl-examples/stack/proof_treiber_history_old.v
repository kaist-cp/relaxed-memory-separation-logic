From gpfsl.examples Require Import sflib.

From iris.algebra Require Import auth gset gmap agree.
From iris.algebra Require Import lib.mono_list.
From iris.proofmode Require Import tactics.

From gpfsl.base_logic Require Import meta_data.
From gpfsl.examples.algebra Require Import mono_list_list.
From gpfsl.logic Require Import logatom atomics invariants.

From gpfsl.logic Require Import repeat_loop new_delete.
From gpfsl.examples Require Import map_seq loc_helper.
From gpfsl.examples.stack Require Import spec_history_old code_treiber.

Require Import iris.prelude.options.

(** Prove that Treiber stack satisfies the logically atomic, history-based
  specifications *)

#[local] Notation next := 0%nat (only parsing).
#[local] Notation data := 1%nat (only parsing).

#[local] Notation history := (history sevent).
#[local] Notation graph_event := (graph_event sevent).

Implicit Types
  (stk : stack_state) (node : event_id * Z * view * logView)
  (** mo of the head pointer, not including the initializing write. *)
  (mo : list (option loc * view))
  (** Event mo. This is used for deriving the linearization order [lin].
  Write event ([Push]/[Pop]) order coincides with xo and read-only events ([EmpPop])
  are associated with the write event that they read. The generation [O] refers
  to [esi], the list of empty pops that reads the head pointer init msg
  (non-atomic). The generation [S gen'] refers to [gen']-th element of [emo],
  which is a triple of a write event that created the generation, a list of
  associated empty pops, and the msg written by the write event (using CAS). *)
  (emo : list ((event_id * list event_id) * (option loc * view)))
  (esi : list event_id)
  (M : logView)
  (s n: loc) (tid: thread_id) (γh γe: gname).

Section emo.
Local Open Scope nat_scope.

(** Find the generation of [emo] started by a non-empty event [e]. *)
Definition emo_find emo e : option ((event_id * (list event_id)) * (option loc * view)) :=
  snd <$> (list_find (λ '((e', _), (_, _)), e' = e) emo).
Definition omsg_of_id emo e : option (option loc * view) := snd <$> emo_find emo e.
Definition oloc_of_id emo e : option loc := mjoin (fst <$> omsg_of_id emo e).

(** Index to an event in emo. [eidx] *)
Inductive emo_idx : Set :=
| emo_e (gen i' : nat) (* [i']-th empty pop at generation [gen] *)
| emo_ne (gen' : nat)  (* the non-empty event of generation [S gen'] *)
.

Definition gen_of eidx :=
  match eidx with
  | emo_e gen _ => gen
  | emo_ne gen' => (S gen')
  end.

Definition lookup_emo esi emo eidx : option event_id :=
  match eidx with
  | emo_e gen i' =>
      match gen with
      | O => esi !! i'
      | S gen' => emo.*1.*2 !! gen' ≫= (!!) i'
      end
  | emo_ne gen' => emo.*1.*1 !! gen'
  end.

(** "Lexicographic" order of emo index *)
Inductive emo_idx_le : ∀ (eidx1 eidx2 : emo_idx), Prop :=
| emo_idx_le_e_e_1 gen1 i1' gen2 i2'
    (LTgen : gen1 < gen2)
    : emo_idx_le (emo_e gen1 i1') (emo_e gen2 i2')
| emo_idx_le_e_e_2 gen i1' i2'
    (LEi' : i1' ≤ i2')
    : emo_idx_le (emo_e gen i1') (emo_e gen i2')
| emo_idx_le_e_ne_1 gen1 i1' gen2'
    (LTgen : gen1 < S gen2')
    : emo_idx_le (emo_e gen1 i1') (emo_ne gen2')
| emo_idx_le_e_ne_2 gen' i1'
    : emo_idx_le (emo_e (S gen') i1') (emo_ne gen')
| emo_idx_le_ne_e gen1' gen2 i2'
    (LTgen : S gen1' ≤ gen2)
    : emo_idx_le (emo_ne gen1') (emo_e gen2 i2')
| emo_idx_le_ne_ne gen1' gen2'
    (LEgen : gen1' ≤ gen2')
    : emo_idx_le (emo_ne gen1') (emo_ne gen2')
.

(** hb implies emo-before. *)
Definition hb_emo (E : history) esi emo :=
  ∀ eidx1 eidx2 e1 e2 eV2
    (EMO_eidx1 : lookup_emo esi emo eidx1 = Some e1)
    (EMO_eidx2 : lookup_emo esi emo eidx2 = Some e2)
    (EV2 : E !! e2 = Some eV2)
    (IN_LVIEW : e1 ∈ eV2.(ge_lview)),
    emo_idx_le eidx1 eidx2.

(** Linearization of [esi] and [emo]. [lin] *)
Definition lin_of_emo esi emo :=
  esi ++ concat ((λ '((e, es), _), e :: es) <$> emo).

Lemma lin_of_emo_singleton e es msg :
  lin_of_emo [] [(e, es, msg)] = [e] ++ es.
Proof.
  unfold lin_of_emo; by list_simplifier.
Qed.

Lemma lin_of_emo_app esi emo1 emo2 :
  lin_of_emo esi (emo1 ++ emo2) =
  (lin_of_emo esi emo1) ++ (lin_of_emo [] emo2).
Proof.
  unfold lin_of_emo; list_simplifier. by rewrite concat_app.
Qed.

(** Insert (append) empty pop to the generation [S gen'] of [emo]. *)
Definition emo_insert_e emo gen' e :=
  alter (λ '((e', es'), msg'), ((e', es'++[e]), msg')) gen' emo.

(** Convert an [eidx] into an index in [lin]. *)
Definition emo_idx_to_lin_idx esi emo eidx :=
  match eidx with
  | emo_e gen i' =>
      match gen with
      | O => i'
      | S gen' =>
          length esi
          + length (concat ((λ '((e, es), _), e :: es) <$> take gen' emo))
          + S i'
      end
  | emo_ne gen' =>
      length esi
      + length (concat ((λ '((e, es), _), e :: es) <$> take gen' emo))
  end
.

(** [esi] is well-formed. *)
Inductive esi_good (E : history) esi : Prop :=
| esi_good_intro
    (EMPPOPS : Forall (λ e', ∃ eV', E !! e' = Some eV' ∧ eV'.(ge_event) = EmpPop) esi)
    (EMPPOP_XO_SUB :
      esi `sublist_of` (seq 0 (length E)))
.

(** Each generation of [emo] is well-formed *)
Inductive emo_gen_good (E : history) e (es : list event_id) (on : option loc) V : Prop :=
| emo_gen_good_intro eV
    (EV : E !! e = Some eV)
    (NOT_EMPPOP : eV.(ge_event) ≠ EmpPop)
    (VIEW : V = eV.(ge_view).(dv_wrt))
    (EMPPOPS : Forall (λ e', ∃ eV',
      « EV' : E !! e' = Some eV' » ∧
      « EMPPOP : eV'.(ge_event) = EmpPop » ∧
      (* TODO: Does this hold in the presence of promises? Is there other
      relation (e.g. view) that we can use instead? *)
      « RW_XO : e < e' » ) es)
    (EMPPOP_EMPTY :
      (* Empty pops can be inserted only when the stack is empty *)
      ∀ (NE : es ≠ []),
        « INTERP_EMTPY : stack_interp E (filter (not_empty_pop E) (seq 0 e) ++ [e]) [] [] »)
    (EMPTYING_POP :
      (* The event that makes the stack empty writes null. *)
      stack_interp E (filter (not_empty_pop E) (seq 0 e) ++ [e]) [] []
      ↔ on = None)
    (EMPPOP_XO_SUB :
      (* The linearization order of the same-generation empty pops is xo. *)
      es `sublist_of` (seq 0 (length E)))
.

(** [esi] + [emo] is well-formed. *)
Inductive esi_emo_good (E : history) esi emo : Prop :=
| emo_good_intro
    (ESI_GOOD : esi_good E esi)
    (GEN_GOOD : Forall (λ '((e, es), (on, V)), emo_gen_good E e es on V) emo)
    (XO_AGREE : emo.*1.*1 = write_xo E)
    (HB_EMO : hb_emo E esi emo)
    (LIN_PERM : lin_of_emo esi emo ≡ₚ seq 0 (length E))
.

(* No [Inj] instance because it's partial *)
Definition emo_inj esi emo :=
  ∀ eidx1 eidx2 e
    (EMO_LOOKUP1 : lookup_emo esi emo eidx1 = Some e)
    (EMO_LOOKUP2 : lookup_emo esi emo eidx2 = Some e),
    eidx1 = eidx2.

Tactic Notation "destruct_eidx" ident(eidx) ident(EMO_LOOKUP) "as" ident(gen') ident(i') ident(e) ident(es) ident(msg) ident(GEN) ident(ES_i') ident(LEgen') ident(LEi') :=
  destruct eidx as [[|gen'] i'|gen']; simpl in *;
      [apply lookup_lt_Some in EMO_LOOKUP as LEi'
      |apply bind_Some in EMO_LOOKUP as [es [GEN ES_i']];
          apply list_lookup_fmap_inv in GEN as ([e ?] & [= <-] & GEN);
          apply list_lookup_fmap_inv in GEN as ([[? ?] msg] & [= <- <-] & GEN);
          apply lookup_lt_Some in GEN as LEgen';
          apply lookup_lt_Some in ES_i' as LEi'
      |apply list_lookup_fmap_inv in EMO_LOOKUP as ([? es] & [= <-] & GEN);
       apply list_lookup_fmap_inv in GEN as ([[? ?] msg] & [= <- <-] & GEN);
       apply lookup_lt_Some in GEN as LEgen'].


Section emo_lemmas.
#[global] Instance emo_idx_eqdec : EqDecision emo_idx.
Proof. solve_decision. Qed.

Lemma length_concat_fmap_take_plus_S (f : _ → list event_id) gen1' emo x N
    (GEN1 : emo !! gen1' = Some x) :
  length (concat (f <$> take (gen1' + S N) emo))
  = length (concat (f <$> take gen1' emo)) + (length (f x) + length (concat (f <$> take N (drop (S gen1') emo)))).
Proof.
  apply lookup_lt_Some in GEN1 as LEgen1'.
  rewrite -{1}(take_drop gen1' emo).
  rewrite take_add_app; last first. { rewrite take_length. lia. }
  rewrite fmap_app concat_app app_length.
  rewrite (drop_S _ _ _ GEN1). rewrite firstn_cons fmap_cons /=.
  rewrite app_length. done.
Qed.

Lemma emo_idx_to_lin_idx_inj esi emo eidx1 eidx2 e
    (EMO_LOOKUP1 : lookup_emo esi emo eidx1 = Some e)
    (EMO_LOOKUP2 : lookup_emo esi emo eidx2 = Some e)
    (EQlin : emo_idx_to_lin_idx esi emo eidx1 = emo_idx_to_lin_idx esi emo eidx2) :
  eidx1 = eidx2.
Proof.
  unfold emo_idx_to_lin_idx in *.
  set (f := λ '(e0, es, _), e0 :: es) in *.
  destruct_eidx eidx1 EMO_LOOKUP1 as gen1' i1' e1 es1 msg1 GEN1 ES_i1' LEgen1' LEi1';
    destruct_eidx eidx2 EMO_LOOKUP2 as gen2' i2' e2 es2 msg2 GEN2 ES_i2' LEgen2' LEi2'.
  - by simplify_eq.
  - lia.
  - lia.
  - lia.
  - case (decide (gen1' = gen2')) as [->|NEgen].
    { simplify_eq. by assert (i1' = i2') as -> by lia. }
    exfalso.
    wlog: gen1' gen2' i1' i2' e1 e2 es1 es2 msg1 msg2
          GEN1 GEN2 LEgen1' LEgen2' ES_i1' ES_i2' LEi1' LEi2' EQlin NEgen
          / gen1' < gen2'.
    { case (le_gt_dec gen1' gen2') => ? X.
      - eapply (X gen1' gen2' i1' i2'); (done || lia).
      - by eapply (X gen2' gen1' i2' i1'). }
    clear NEgen. intros LT.
    assert (∃ (N : nat), gen2' = gen1' + (S N)) as [N ->].
    { exists (gen2' - gen1' - 1). lia. } clear LT.
    have {}EQlin : length (concat (f <$> take gen1' emo)) + i1' = length (concat (f <$> take (gen1' + S N) emo)) + i2' by lia.
    erewrite length_concat_fmap_take_plus_S in EQlin; [|done]. simpl in EQlin.
    assert (i1' = S (length es1 + length (concat (f <$> take N (drop (S gen1') emo)))) + i2') as ->; lia.
  - (* symmetric to 8th case *) exfalso.
    have {}EQlin : length (concat (f <$> take gen1' emo)) + S i1' = length (concat (f <$> take gen2' emo)) by lia.
    have [LT|[EQ|GT]] : gen1' < gen2' ∨ gen1' = gen2' ∨ gen1' > gen2' by lia.
    + assert (∃ (N : nat), gen2' = gen1' + (S N)) as [N ->].
      { exists (gen2' - gen1' - 1). lia. } clear LT.
      erewrite length_concat_fmap_take_plus_S in EQlin; [|done]. simpl in EQlin.
      assert (i1' = length es1 + length (concat (f <$> take N (drop (S gen1') emo)))); lia.
    + subst. lia.
    + assert (∃ (N : nat), gen1' = gen2' + (S N)) as [N ->].
      { exists (gen1' - gen2' - 1). lia. } clear GT.
      erewrite length_concat_fmap_take_plus_S in EQlin; [|done]. simpl in EQlin.
      assert (i1' = length es2 + length (concat (f <$> take N (drop (S gen2') emo)))); lia.
  - lia.
  - (* symmetric to 6th case *) exfalso.
    have {}EQlin : length (concat (f <$> take gen2' emo)) + S i2' = length (concat (f <$> take gen1' emo)) by lia.
    have [LT|[EQ|GT]] : gen2' < gen1' ∨ gen2' = gen1' ∨ gen2' > gen1' by lia.
    + assert (∃ (N : nat), gen1' = gen2' + (S N)) as [N ->].
      { exists (gen1' - gen2' - 1). lia. } clear LT.
      erewrite length_concat_fmap_take_plus_S in EQlin; [|done]. simpl in EQlin.
      assert (i2' = length es2 + length (concat (f <$> take N (drop (S gen2') emo)))); lia.
    + subst. lia.
    + assert (∃ (N : nat), gen2' = gen1' + (S N)) as [N ->].
      { exists (gen2' - gen1' - 1). lia. } clear GT.
      erewrite length_concat_fmap_take_plus_S in EQlin; [|done]. simpl in EQlin.
      assert (i2' = length es1 + length (concat (f <$> take N (drop (S gen1') emo)))); lia.
  - case (decide (gen1' = gen2')) as [->|NEgen]; first by simplify_eq.
    exfalso.
    wlog: gen1' gen2' es1 es2 msg1 msg2 GEN1 GEN2 LEgen1' LEgen2' EQlin NEgen
          / gen1' < gen2'.
    { case (le_gt_dec gen1' gen2') => ? X.
      - eapply (X gen1' gen2'); (done || lia).
      - by eapply (X gen2' gen1'). }
    clear NEgen. intros LT.
    assert (∃ (N : nat), gen2' = gen1' + (S N)) as [N ->].
    { exists (gen2' - gen1' - 1). lia. } clear LT.
    erewrite length_concat_fmap_take_plus_S in EQlin; [|done]. simpl in EQlin. lia.
Qed.

Lemma lin_of_emo_split_esi esi emo :
  lin_of_emo esi emo = esi ++ lin_of_emo [] emo.
Proof. done. Qed.

Lemma lin_of_emo_add_emo_ne esi emo e es msg :
  lin_of_emo esi (emo ++ [(e, es, msg)]) = lin_of_emo esi emo ++ e :: es.
Proof.
  unfold lin_of_emo. list_simplifier. rewrite concat_app /=. list_simplifier. done.
Qed.

Lemma lookup_emo_app esi emo emo' eidx e
    (EMO_LOOKUP : lookup_emo esi emo eidx = Some e) :
 lookup_emo esi (emo ++ emo') eidx = Some e.
Proof.
  unfold lookup_emo in *. list_simplifier. repeat case_match.
  - done.
  - apply bind_Some in EMO_LOOKUP as [es [GEN ES_i']].
    have LT := GEN. apply lookup_lt_Some in LT.
    rewrite lookup_app_l; [|done]. rewrite GEN. done.
  - have LT := EMO_LOOKUP. apply lookup_lt_Some in LT.
    rewrite lookup_app_l; [|done]. rewrite EMO_LOOKUP. done.
Qed.

Lemma lookup_emo_inv_e esi emo gen i' e
    (EMO_LOOKUP : lookup_emo esi emo (emo_e gen i') = Some e) :
  ∃ es,
    « GEN : (esi :: emo.*1.*2) !! gen = Some es » ∧
    « ES_i' : es !! i' = Some e ».
Proof.
  unfold lookup_emo in *. case Egen: gen => [|gen']; subst.
  - by exists esi.
  - apply bind_Some in EMO_LOOKUP as [es [??]]. by exists es.
Qed.

Lemma lookup_emo_inv_ne esi emo gen' e
    (EMO_LOOKUP : lookup_emo esi emo (emo_ne gen') = Some e) :
  « GEN : emo.*1.*1 !! gen' = Some e ».
Proof. done. Qed.

Lemma emo_idx_to_lin_idx_emo_app esi emo emo' eidx e
    (EMO_LOOKUP : lookup_emo esi emo eidx = Some e) :
  emo_idx_to_lin_idx esi emo eidx = emo_idx_to_lin_idx esi (emo ++ emo') eidx.
Proof.
  unfold emo_idx_to_lin_idx. case Eeidx: eidx => [[|gen'] i'|gen'].
  - done.
  - subst. apply lookup_emo_inv_e in EMO_LOOKUP. des. simplify_list_eq.
    have LT : gen' < length emo.
    { apply lookup_lt_Some in GEN. by rewrite !fmap_length in GEN. }
    rewrite take_app_le; [done|lia].
  - subst. apply lookup_emo_inv_ne in EMO_LOOKUP as GEN. des.
    have LT : gen' < length emo.
    { apply lookup_lt_Some in GEN. by rewrite !fmap_length in GEN. }
    rewrite take_app_le; [done|lia].
Qed.

Lemma lin_of_emo_lookup_lookup_emo esi emo i e
    (NODUP : NoDup (lin_of_emo esi emo))
    (LIN_I : lin_of_emo esi emo !! i = Some e) :
  ∃ eidx,
    « IDX : i = emo_idx_to_lin_idx esi emo eidx » ∧
    « EMO_LOOKUP : lookup_emo esi emo eidx = Some e ».
Proof.
  revert i e NODUP LIN_I.
  induction emo as [|[[e' es] msg] emo] using rev_ind; intros.
  { exists (emo_e O i). unfold lin_of_emo in *. list_simplifier. done. }
  rewrite ->lin_of_emo_add_emo_ne,NoDup_app in NODUP. des.
  rewrite lin_of_emo_add_emo_ne in LIN_I.
  set len := length (lin_of_emo esi emo).
  have Hi : i < len ∨ i = len ∨ i > len by lia. des.
  - (* use [i] in IH to get a [eidx] and use it *)
    rewrite lookup_app_l in LIN_I; [|done].
    specialize (IHemo _ _ NODUP LIN_I). des.
    exists eidx. split; red.
    + by erewrite emo_idx_to_lin_idx_emo_app in IDX.
    + by eapply lookup_emo_app.
  - rewrite list_lookup_middle in LIN_I; [|done]. simplify_eq.
    exists (emo_ne (length emo)). list_simplifier. split; red.
    + subst len. by rewrite /lin_of_emo app_length.
    + by rewrite -!(fmap_length fst) lookup_app_1_eq.
  - rewrite ->lookup_app_r,lookup_cons in LIN_I; [|lia].
    case Esub: (i - len) => [|i']; [lia|]. rewrite -/len Esub in LIN_I.
    have {Esub}Hi : i = len + S i' by lia. subst.
    subst len. unfold lin_of_emo in *. rewrite app_length.
    exists (emo_e (S (length emo)) i'). split; red.
    + rewrite /emo_idx_to_lin_idx. list_simplifier. done.
    + unfold lookup_emo. list_simplifier.
      by rewrite -(fmap_length fst) -(fmap_length snd) lookup_app_1_eq.
Qed.

Lemma lookup_emo_lin_of_emo_lookup esi emo eidx e
    (EMO_LOOKUP : lookup_emo esi emo eidx = Some e) :
  lin_of_emo esi emo !! (emo_idx_to_lin_idx esi emo eidx) = Some e.
Proof.
  unfold lin_of_emo, emo_idx_to_lin_idx.
  set (f := λ '(e0, es, _), e0 :: es) in *.
  destruct eidx as [[|gen'] i'|gen']; simpl in *.
  - rewrite lookup_app_l; [done|]. by eapply lookup_lt_Some.
  - rewrite lookup_app_r; [|lia]. rewrite (_ : (∀ x a b, x + a + b - x = a + b)); [|lia].
    apply bind_Some in EMO_LOOKUP as [es [GEN ES_i']].
    apply list_lookup_fmap_inv in GEN as ([? ?] & [= <-] & GEN).
    apply list_lookup_fmap_inv in GEN as ([[? ?] [? ?]] & [= <- <-] & GEN).
    apply lookup_lt_Some in GEN as LEN.
    rewrite -{2}(take_drop gen' emo). rewrite fmap_app concat_app.
    rewrite lookup_app_r; [|lia]. rewrite (_ : ∀ x a, x + a - x = a); [|lia].
    rewrite (drop_S _ _ _ GEN). rewrite fmap_cons concat_cons /=.
    apply lookup_lt_Some in ES_i' as LEN'. rewrite lookup_app_l; [done|lia].
  - rewrite lookup_app_r; [|lia]. rewrite (_ : (∀ x a, x + a - x = a)); [|lia].
    apply list_lookup_fmap_inv in EMO_LOOKUP as ([? ?] & [= <-] & GEN).
    apply list_lookup_fmap_inv in GEN as ([[? ?] [? ?]] & [= <- <-] & GEN).
    apply lookup_lt_Some in GEN as LEN.
    rewrite -{2}(take_drop gen' emo). rewrite fmap_app concat_app.
    rewrite lookup_app_r; [|lia]. rewrite (_ : ∀ x, x - x = 0); [|lia].
    rewrite (drop_S _ _ _ GEN) //=.
Qed.

Lemma event_in_esi_emo (E : history) esi emo e
    (LIN_PERM : lin_of_emo esi emo ≡ₚ seq 0 (length E))
    (IS : is_Some (E !! e)) :
  ∃ eidx, lookup_emo esi emo eidx = Some e.
Proof.
  have NODUP : NoDup (lin_of_emo esi emo) by by eapply ord_nodup.
  move: IS => /lookup_lt_is_Some /lookup_xo => XO_LOOKUP.
  apply Permutation_sym,Permutation_inj in LIN_PERM as [_ (f & _ & LIN_PERM)].
  specialize (LIN_PERM e). rewrite LIN_PERM in XO_LOOKUP.
  specialize (lin_of_emo_lookup_lookup_emo _ _ _ _ NODUP XO_LOOKUP). i. des.
  by exists eidx.
Qed.

Lemma longer_take i1 i2 (lss : list (list event_id)) (LE: i1 ≤ i2):
    length (concat (take i1 lss))
  ≤ length (concat (take i2 lss)).
Proof.
  apply prefix_length.
  revert lss i2 LE. induction i1; intros; simpl.
  { apply prefix_nil. }
  destruct i2; first lia. destruct lss; first done; simpl.
  apply prefix_app, IHi1; lia.
Qed.

Lemma lin_idx_e_i'_mono esi emo gen i1' i2' (LEi' : i1' ≤ i2') :
  emo_idx_to_lin_idx esi emo (emo_e gen i1') ≤ emo_idx_to_lin_idx esi emo (emo_e gen i2').
Proof.
  unfold emo_idx_to_lin_idx.
  destruct gen; lia.
Qed.

Lemma lin_idx_ne_gen_mono esi emo gen1' gen2' (LEgen : gen1' ≤ gen2') :
  emo_idx_to_lin_idx esi emo (emo_ne gen1') ≤ emo_idx_to_lin_idx esi emo (emo_ne gen2').
Proof.
  simpl. do 2 rewrite fmap_take.
  by apply Nat.add_le_mono_l, longer_take.
Qed.

Lemma lin_idx_e_ne_gen_mono esi emo gen1 i1' gen2'
    (EMO_LOOKUP1 : is_Some (lookup_emo esi emo (emo_e gen1 i1')))
    (LTgen : gen1 < S gen2') :
  emo_idx_to_lin_idx esi emo (emo_e gen1 i1') < emo_idx_to_lin_idx esi emo (emo_ne gen2').
Proof.
  inversion EMO_LOOKUP1 as [e LOOKUP].
  apply lookup_emo_inv_e in LOOKUP as [es [LOOKUP1 LOOKUP2]].
  apply lookup_lt_Some in LOOKUP2; clear e.
  eapply Nat.lt_le_trans; last first.
  { apply lin_idx_ne_gen_mono. instantiate (1 := gen1); lia. }
  destruct gen1; simpl.
  { inversion LOOKUP1; lia. }
  rewrite <- Nat.add_assoc. apply Nat.add_lt_mono_l.
  do 2 rewrite fmap_take.
  simpl in LOOKUP1.
  do 2 rewrite list_lookup_fmap in LOOKUP1.
  destruct (emo !! gen1) eqn:EG; last inversion LOOKUP1.
  destruct p as [[ep esp] rest]. inversion LOOKUP1; subst.
  remember (λ '(y, _), let '(e, es0) := y in e :: es0) as f.
  assert ((f <$> emo) !! gen1 = Some (ep::es)).
  - rewrite list_lookup_fmap. rewrite EG.
    by list_simplifier.
  - apply take_S_r in H. rewrite H.
    rewrite concat_app /= app_nil_r app_length cons_length. lia.
Qed.

Lemma lin_idx_ne_e_gen_mono esi emo gen1' gen2 i2' (LEgen : S gen1' ≤ gen2) :
  emo_idx_to_lin_idx esi emo (emo_ne gen1') < emo_idx_to_lin_idx esi emo (emo_e gen2 i2').
Proof.
  destruct gen2; first lia; simpl.
  apply le_S_n in LEgen.
  rewrite <- Nat.add_assoc. apply Nat.add_lt_mono_l.
  do 2 rewrite fmap_take.
  eapply Nat.le_lt_trans.
  - apply longer_take, LEgen.
  - lia.
Qed.

Lemma lin_idx_e_gen_mono esi emo gen1 gen2 i1' i2'
    (EMO_LOOKUP1 : is_Some (lookup_emo esi emo (emo_e gen1 i1')))
    (LTgen : gen1 < gen2) :
  emo_idx_to_lin_idx esi emo (emo_e gen1 i1') < emo_idx_to_lin_idx esi emo (emo_e gen2 i2').
Proof.
  destruct gen2; first lia.
  eapply Nat.lt_le_trans.
  - by apply lin_idx_e_ne_gen_mono.
  - simpl; lia.
Qed.

Lemma not_empty_pop_lin E emo esi
  (ESI_GOOD: esi_good E esi)
  (GEN_GOOD: Forall
    (λ '(y, y0), let '(e, es) := y in let '(on, V) := y0 in
      emo_gen_good E e es on V) emo) :
  filter (not_empty_pop E) (lin_of_emo esi emo) = emo.*1.*1.
Proof.
  induction emo using rev_ind; intros; simpl.
  - destruct ESI_GOOD. clear -EMPPOPS.
    unfold lin_of_emo; list_simplifier.
    induction esi; [by rewrite filter_nil|].
    rewrite filter_cons.
    apply Forall_cons in EMPPOPS as [[eV [Ha EMP1]] EMP2].
    apply IHesi in EMP2; rewrite EMP2.
    destruct (decide (not_empty_pop E a)); auto.
    edestruct n; [apply Ha|done].
  - destruct x as [[e es] [on V]].
    do 2 rewrite fmap_app; simpl.
    rewrite lin_of_emo_add_emo_ne. rewrite filter_app.
    apply Forall_app in GEN_GOOD as [GENE GENX].
    apply IHemo in GENE; rewrite GENE.
    list_simplifier. destruct H.
    clear -EV NOT_EMPPOP EMPPOPS.
    rewrite filter_cons_True; last first.
    { intros ??. rewrite EV in EV0. by injection EV0 as ->. }
    clear -EMPPOPS.
    assert (filter (not_empty_pop E) es = []); last by rewrite H.
    induction es; [apply filter_nil|].
    apply Forall_cons in EMPPOPS as [[eV [Ea [EMP1 _]]] EMP2].
    apply IHes in EMP2. rewrite filter_cons.
    destruct (decide (not_empty_pop E a)); last done.
    edestruct n; [apply Ea|done].
Qed.

Lemma emo_ids_le_new (E : history) esi emo eidx e
    (EMO_LOOKUP : lookup_emo esi emo eidx = Some e)
    (ESI_EMO_GOOD : esi_emo_good E esi emo) :
  (e < length E)%nat.
Proof.
  destruct ESI_EMO_GOOD. destruct ESI_GOOD.
  have ? : Forall (λ e, e < length E)%nat (seq 0 (length E)).
  { apply Forall_seq. lia. }
  destruct eidx as [[|gen'] i'|gen']; simplify_list_eq.
  - have LE : Forall (λ e, e < length E)%nat esi by apply: Forall_sublist.
    move: LE. rewrite Forall_lookup => /(_ _ _ EMO_LOOKUP). lia.
  - apply bind_Some in EMO_LOOKUP as (es & GEN & ES_i').
    apply list_lookup_fmap_inv in GEN as ([? ?] & [= <-] & GEN).
    apply list_lookup_fmap_inv in GEN as ([[? ?] [? ?]] & [= <- <-] & GEN).
    rewrite ->Forall_lookup in GEN_GOOD. destruct (GEN_GOOD _ _ GEN).
    have LE : Forall (λ e, e < length E)%nat es by apply: Forall_sublist.
    move: LE. rewrite Forall_lookup => /(_ _ _ ES_i'). lia.
  - have LE : Forall (λ e, e < length E)%nat (write_xo E) by apply: Forall_filter.
    rewrite XO_AGREE in EMO_LOOKUP.
    move: LE. rewrite Forall_lookup => /(_ _ _ EMO_LOOKUP). lia.
Qed.

Lemma lookup_emo_old_esi esi emo eidx e e0
    (EMO_LOOKUP : lookup_emo (esi ++ [e0]) emo eidx = Some e)
    (NEedix : eidx ≠ emo_e O (length esi)) :
  lookup_emo esi emo eidx = Some e.
Proof.
  destruct eidx as [[|gen'] i'|gen']; simplify_list_eq; [|done|done].
  have LEi' : (i' < length esi)%nat.
  { apply lookup_lt_Some in EMO_LOOKUP. rewrite app_length /= in EMO_LOOKUP.
    have ? : i' ≠ length esi by intros ->. lia. }
  by rewrite lookup_app_l in EMO_LOOKUP.
Qed.

Lemma emo_insert_e_11 emo gen' e :
  (emo_insert_e emo gen' e).*1.*1 = emo.*1.*1.
Proof.
  rewrite /emo_insert_e.
  rewrite (list_alter_fmap fst
             (λ '(e', es', msg'), (e', es' ++ [e], msg'))
             (λ '(e', es'), (e', es' ++ [e]))
             emo gen'); last first.
  { induction emo; [done|]. constructor; [|done]. destruct a. destruct p. by simpl. }
  rewrite (list_alter_fmap fst
             (λ '(e', es'), (e', es' ++ [e]))
             id
             emo.*1 gen').
  { by rewrite list_alter_id. }
  induction emo.*1; [done|]. constructor; [|done]. destruct a. by simpl.
Qed.

Lemma emo_insert_e_12 emo gen' e :
  (emo_insert_e emo gen' e).*1.*2 = alter (λ es' : list event_id, es' ++ [e]) gen' emo.*1.*2.
Proof.
  rewrite /emo_insert_e.
  rewrite (list_alter_fmap fst
             (λ '(e', es', msg'), (e', es' ++ [e], msg'))
             (λ '(e', es'), (e', es' ++ [e]))
             emo gen'); last first.
  { induction emo; [done|]. constructor; [|done]. destruct a. destruct p. by simpl. }
  rewrite (list_alter_fmap snd
             (λ '(e', es'), (e', es' ++ [e]))
             (λ es', es' ++ [e])
             emo.*1 gen'); [done|].
  induction emo.*1; [done|]. constructor; [|done]. destruct a. by simpl.
Qed.

Lemma emo_insert_e_2 emo gen' e :
  (emo_insert_e emo gen' e).*2 = emo.*2.
Proof.
  rewrite /emo_insert_e.
  rewrite (list_alter_fmap snd
             (λ '(e', es', msg'), (e', es' ++ [e], msg'))
             id
             emo gen'); [by rewrite list_alter_id|].
  induction emo; [done|]. constructor; [|done]. destruct a. destruct p. by simpl.
Qed.

Lemma lookup_emo_old_emo_e esi emo eidx gen0' es e e0
    (EMO_LOOKUP : lookup_emo esi (emo_insert_e emo gen0' e0) eidx = Some e)
    (GEN0 : emo.*1.*2 !! gen0' = Some es)
    (NEedix : eidx ≠ emo_e (S gen0') (length es)) :
  lookup_emo esi emo eidx = Some e.
Proof.
  destruct eidx as [[|gen'] i'|gen']; simplify_list_eq; [done|..];
    case (decide (gen' = gen0')) as [->|NE].
  - rewrite emo_insert_e_12 in EMO_LOOKUP.
    rewrite list_lookup_alter GEN0 /= in EMO_LOOKUP.
    have ? : i' ≠ length es by intros ->.
    rewrite lookup_app_1_ne in EMO_LOOKUP; [|done].
    apply bind_Some. by exists es.
  - rewrite emo_insert_e_12 in EMO_LOOKUP.
    rewrite list_lookup_alter_ne in EMO_LOOKUP; done.
  - by rewrite emo_insert_e_11 in EMO_LOOKUP.
  - by rewrite emo_insert_e_11 in EMO_LOOKUP.
Qed.

Lemma lookup_emo_old_emo_ne esi emo eidx e0 e msg0
    (EMO_LOOKUP : lookup_emo esi (emo ++ [(e0, [], msg0)]) eidx = Some e)
    (NEedix : eidx ≠ emo_ne (length emo)) :
  lookup_emo esi emo eidx = Some e.
Proof.
  rewrite -(fmap_length fst) -(fmap_length snd) in NEedix.
  destruct eidx as [[|gen'] i'|gen']; simplify_list_eq; [done|..];
    case (decide (gen' = (length emo.*1.*2))) as [->|NE].
  - rewrite lookup_app_1_eq /= in EMO_LOOKUP. done.
  - rewrite lookup_app_1_ne in EMO_LOOKUP; done.
  - rewrite fmap_length -(fmap_length fst) in EMO_LOOKUP. simplify_eq.
  - rewrite fmap_length -(fmap_length fst) in NE.
    rewrite lookup_app_1_ne in EMO_LOOKUP; done.
Qed.

Lemma lookup_emo_new_ne (E : history) esi emo eidx (e := length E) msg
    (EMO_LOOKUP : lookup_emo esi (emo ++ [(e, [], msg)]) eidx = Some e)
    (ESI_EMO_GOOD : esi_emo_good E esi emo) :
  eidx = emo_ne (length emo).
Proof.
  case (decide (eidx = emo_ne (length emo))) as [->|NE]; [done|]. exfalso.
  apply lookup_emo_old_emo_ne in EMO_LOOKUP; [|done].
  eapply (emo_ids_le_new E) in EMO_LOOKUP; [lia|done].
Qed.

Lemma sub_esi_emo_lookup esi1 esi2 emo1 emo2 eidx e
    (Subesi : esi1 ⊑ esi2)
    (Subne : emo1.*1.*1 ⊑ emo2.*1.*1)
    (Subess : emo1.*1.*2 `prefixes_of` emo2.*1.*2) :
  lookup_emo esi1 emo1 eidx = Some e → lookup_emo esi2 emo2 eidx = Some e.
Proof.
  case eidx as [[|gen'] i'|gen'] => /= EMO_LOOKUP.
  - by eapply prefix_lookup_Some.
  - apply bind_Some in EMO_LOOKUP as (es1 & GEN1 & ES1_i').
    have [es2 GEN2] : ∃ es2, emo2.*1.*2 !! gen' = Some es2.
    { clear -Subne GEN1.
      have [e {}GEN1] : ∃ e, emo1.*1 !! gen' = Some (e, es1).
      { apply list_lookup_fmap_inv in GEN1 as ([e ?] & [= <-] & GEN). by exists e. }
      apply (f_equal (fmap fst)) in GEN1. rewrite -list_lookup_fmap /= in GEN1.
      have GEN2 := prefix_lookup_Some _ _ _ _ GEN1 Subne.
      have [es2 {}GEN2] : ∃ es2, emo2.*1 !! gen' = Some (e, es2).
      { apply list_lookup_fmap_inv in GEN2 as ([? es] & [= <-] & GEN). by exists es. }
      apply (f_equal (fmap snd)) in GEN2. rewrite -list_lookup_fmap /= in GEN2.
      by exists es2. }
    specialize (Subess gen'). rewrite GEN1 GEN2 /= in Subess.
    have ES2_i' := prefix_lookup_Some _ _ _ _ ES1_i' Subess.
    apply bind_Some. by exists es2.
  - by eapply prefix_lookup_Some.
Qed.

Lemma emo_insert_e_12_prefixes emo gen' e :
  emo.*1.*2 `prefixes_of` (emo_insert_e emo gen' e).*1.*2.
Proof.
  rewrite emo_insert_e_12. intros i.
  case (decide (i = gen')) as [EQ|NE]; case Ei: (emo.*1.*2 !! i); simplify_eq.
  + rewrite list_lookup_alter Ei /=. by apply prefix_app_r.
  + rewrite list_lookup_alter Ei /=. done.
  + rewrite list_lookup_alter_ne; [|done]. rewrite Ei //=.
  + rewrite list_lookup_alter_ne; [|done]. rewrite Ei //=.
Qed.

Lemma emo_insert_ne_12_prefixes emo e msg :
  emo.*1.*2 `prefixes_of` (emo ++ [(e, [], msg)]).*1.*2.
Proof.
  rewrite !fmap_app /=. intros i.
  case Ei: (emo.*1.*2 !! i); simplify_eq.
  + apply lookup_lt_Some in Ei as Hi. rewrite lookup_app_l; [|done]. by rewrite Ei /=.
  + simpl. by case_match.
Qed.

Lemma lin_perm_emo_inj (E : history) esi emo
    (LIN_PERM : lin_of_emo esi emo ≡ₚ seq 0 (length E)) :
  emo_inj esi emo.
Proof.
  intros ?????.
  (* another way: Using [NoDup (lin_of_emo _ _)]... Is that easier? *)
  apply lookup_emo_lin_of_emo_lookup in EMO_LOOKUP1 as LIN1, EMO_LOOKUP2 as LIN2.
  apply Permutation_inj in LIN_PERM as [_ (f & INJ_f & LIN_PERM)].
  rewrite ->LIN_PERM in LIN1,LIN2.
  apply lookup_lt_Some in LIN1 as LT1, LIN2 as LT2.
  rewrite seq_length in LT1,LT2.
  rewrite ->lookup_xo in LIN1,LIN2; [|done..].
  rewrite -LIN1 in LIN2. injection LIN2 as EQ%(inj f).
  by eapply emo_idx_to_lin_idx_inj in EQ.
Qed.

Lemma emo_inj_esi_insert E esi emo
    (INJ : emo_inj esi emo)
    (ESI_EMO_GOOD : esi_emo_good E esi emo) :
  emo_inj (esi ++ [length E]) emo.
Proof.
  intros ???.
  case (decide (eidx1 = emo_e O (length esi))) => [->|NE1]; simpl;
    [rewrite lookup_app_1_eq; intros [= <-]
    |intros HL1%lookup_emo_old_esi; [|done]];
    (case (decide (eidx2 = emo_e O (length esi))) => [->|NE2]; simpl;
      [rewrite lookup_app_1_eq; (intros [= <-] || intros _)
      |intros HL2%lookup_emo_old_esi; [|done]]).
  - done.
  - exfalso. eapply (emo_ids_le_new E) in HL2; [lia|done].
  - exfalso. eapply (emo_ids_le_new E) in HL1; [lia|done].
  - by eapply INJ.
Qed.

Lemma emo_inj_emo_insert_e E esi emo gen' o es msg
    (INJ : emo_inj esi emo)
    (GEN : emo !! gen' = Some (o, es, msg))
    (ESI_EMO_GOOD : esi_emo_good E esi emo) :
  emo_inj esi (emo_insert_e emo gen' (length E)).
Proof.
  intros ???.
  have GEN12 : emo.*1.*2 !! gen' = Some es.
  { apply (f_equal (fmap fst)), (f_equal (fmap snd)) in GEN.
    rewrite -!list_lookup_fmap // in GEN. }
  case (decide (eidx1 = emo_e (S gen') (length es))) => [->|NE1]; simpl;
    [rewrite emo_insert_e_12 list_lookup_alter GEN12 /= lookup_app_1_eq; intros [= <-]
    |intros HL1%(lookup_emo_old_emo_e _ _ _ _ es); [|done..]];
    (case (decide (eidx2 = emo_e (S gen') (length es))) => [->|NE2]; simpl;
      [rewrite emo_insert_e_12 list_lookup_alter GEN12 /= lookup_app_1_eq; (intros [= <-] || intros _)
      |intros HL2%(lookup_emo_old_emo_e _ _ _ _ es); [|done..]]).
  - done.
  - exfalso. eapply (emo_ids_le_new E) in HL2; [lia|done].
  - exfalso. eapply (emo_ids_le_new E) in HL1; [lia|done].
  - by eapply INJ.
Qed.

Lemma emo_inj_emo_insert_ne E esi emo msg
    (INJ : emo_inj esi emo)
    (ESI_EMO_GOOD : esi_emo_good E esi emo) :
  emo_inj esi (emo ++ [(length E, [], msg)]).
Proof.
  intros ???.
  case (decide (eidx1 = emo_ne (length emo.*1.*1))) => [->|NE1]; simpl;
    [rewrite !fmap_app /= lookup_app_1_eq; intros [= <-]
    |rewrite !fmap_length in NE1; intros HL1%lookup_emo_old_emo_ne; [|done]];
    (case (decide (eidx2 = emo_ne (length emo.*1.*1))) => [->|NE2]; simpl;
      [rewrite !fmap_app /= lookup_app_1_eq; (intros [= <-] || intros _)
      |rewrite !fmap_length in NE2; intros HL2%lookup_emo_old_emo_ne; [|done]]).
  - done.
  - exfalso. eapply (emo_ids_le_new E) in HL2; [lia|done].
  - exfalso. eapply (emo_ids_le_new E) in HL1; [lia|done].
  - by eapply INJ.
Qed.

Lemma max_gen esi emo eidx e
    (EMO_LOOKUP : lookup_emo esi emo eidx = Some e) :
  gen_of eidx ≤ length emo.
Proof.
  destruct_eidx eidx EMO_LOOKUP as gen' i' e' es msg GEN ES_i' LEgen' LEi'; lia.
Qed.

Lemma esi_good_mono E1 E2 esi (ESI_GOOD : esi_good E1 esi) (SubE : E1 ⊑ E2) :
  esi_good E2 esi.
Proof.
  destruct ESI_GOOD. rewrite ->Forall_lookup in EMPPOPS.
  constructor.
  - rewrite Forall_lookup => i' e ES_i'.
    specialize (EMPPOPS _ _ ES_i') as [eV [EV' ?]].
    exists eV. split; [|done]. by eapply prefix_lookup_Some.
  - destruct SubE as [E ->]. rewrite app_length /= seq_app.
    apply sublist_inserts_r, EMPPOP_XO_SUB.
Qed.

Lemma emo_gen_good_mono E1 E2 e es on V
    (GEN_GOOD : emo_gen_good E1 e es on V)
    (SubE : E1 ⊑ E2) :
  emo_gen_good E2 e es on V.
Proof.
  destruct GEN_GOOD.
  apply lookup_lt_Some in EV as LT.
  rewrite (write_xo_stable _ E2) in EMPPOP_EMPTY EMPTYING_POP; [|lia|done].
  econstructor.
  - by eapply prefix_lookup_Some.
  - done.
  - done.
  - rewrite ->Forall_lookup in EMPPOPS |- *. intros ? ? ES_i'.
    specialize (EMPPOPS _ _ ES_i'). des.
    exists eV'. unfold NW. split_and!; [by eapply prefix_lookup_Some|done..].
  - intros ES. specialize (EMPPOP_EMPTY ES). unnw.
    by apply (stack_interp_mono_prefix E1).
  - split; last first.
    { move=> /EMPTYING_POP; by apply stack_interp_mono_prefix. }
    intros INTERP. apply EMPTYING_POP.
    apply (stack_interp_mono E2); [|done].
    rewrite Forall_lookup => i e' In eV' EV2'.
    have ? : e' ≤ e.
    { rewrite lookup_app in In. case_match eqn:Heqo; simplify_list_eq; [|lia].
      apply list_filter_lookup_Some_inv in Heqo as [? [In _]].
      apply lookup_seq in In. lia. }
    apply (prefix_lookup_inv E1 E2); [done| |done].
    apply lookup_lt_is_Some_2. lia.
  - destruct SubE as [E ->]. rewrite app_length seq_app.
    apply sublist_inserts_r, EMPPOP_XO_SUB.
Qed.

Lemma stack_interp_esi E esi
    (EMPPOPS : Forall (λ e', ∃ eV',
      E !! e' = Some eV' ∧ eV'.(ge_event) = EmpPop) esi) :
  stack_interp E esi [] [].
Proof.
  induction esi using rev_ind; first constructor.
  apply Forall_app in EMPPOPS; des.
  apply IHesi in EMPPOPS.
  apply stack_interp_app; exists []; split; auto.
  rewrite -> Forall_singleton in EMPPOPS0; des.
  apply (stack_interp_snoc _ x eV' _ [] _ [] _); auto.
  - constructor.
  - apply (stack_run_EmpPop _ _ []); auto.
Qed.

Lemma stack_interp_esi_nil E esi emo stk
    (EMPPOPS : Forall (λ e', ∃ eV',
      E !! e' = Some eV' ∧ eV'.(ge_event) = EmpPop) esi) :
  stack_interp E (lin_of_emo esi emo) [] stk
  ↔ stack_interp E (lin_of_emo [] emo) [] stk.
Proof.
  split; intros.
  - rewrite lin_of_emo_split_esi in H.
    apply stack_interp_app in H; des.
    eapply (stack_interp_functional _ _ _ [] _) in H;
      [by subst|by apply stack_interp_esi].
  - rewrite lin_of_emo_split_esi.
    apply stack_interp_app.
    exists []; split;
      [by apply stack_interp_esi|auto].
Qed.

Lemma lin_of_emo_insert_e esi emo g e
    (Hg : g < length emo) :
  lin_of_emo esi (emo_insert_e emo g e) =
    lin_of_emo esi (take (S g) emo) ++
    [e] ++ lin_of_emo [] (drop (S g) emo).
Proof.
  apply lookup_lt_is_Some_2 in Hg.
  inv Hg.
  unfold emo_insert_e. rewrite (alter_take_drop _ _ _ x); auto.
  rewrite (take_S_r _ _ x); auto.
  do 3 rewrite lin_of_emo_app. rewrite <- app_assoc.
  destruct x as [[e' es'] msg'].
  unfold lin_of_emo; by list_simplifier.
Qed.

Lemma lin_perm_add_esi esi emo e
    (LIN_PERM: lin_of_emo esi emo ≡ₚ seq 0 e):
  lin_of_emo (esi ++ [e]) emo ≡ₚ seq 0 (e + 1).
Proof.
  rewrite seq_app /=. rewrite lin_of_emo_split_esi.
  rewrite -(assoc app esi) (comm app [e]) (assoc app esi).
  by apply Permutation_app.
Qed.

Lemma lin_perm_add_emo_ne esi emo e msg
    (LIN_PERM: lin_of_emo esi emo ≡ₚ seq 0 e):
  lin_of_emo esi (emo ++ [(e, [], msg)]) ≡ₚ seq 0 (e + 1).
Proof.
  rewrite seq_app /=. rewrite lin_of_emo_add_emo_ne. by apply Permutation_app.
Qed.

Lemma lin_perm_add_emo_e esi emo gen' x e
    (GEN : emo !! gen' = Some x)
    (LIN_PERM: lin_of_emo esi emo ≡ₚ seq 0 e) :
  lin_of_emo esi (emo_insert_e emo gen' e) ≡ₚ seq 0 (e + 1).
Proof.
  rewrite lin_of_emo_insert_e; [|by apply lookup_lt_Some in GEN].
  rewrite (comm app [e]) (assoc app _ _ [e]).
  rewrite seq_app /=. apply Permutation_app; [|done].
  by rewrite -lin_of_emo_app take_drop.
Qed.

Lemma hb_emo_add_ne E esi emo msg eV
    (ESI_EMO_GOOD : esi_emo_good E esi emo)
    (EWF : history_wf E)
    (HB_EMO : hb_emo E esi emo) :
  hb_emo (E ++ [eV]) esi (emo ++ [(length E, [], msg)]).
Proof.
  unfold hb_emo. intros.
  set gen' := length emo.*1.*1.
  set eidx := emo_ne gen'.
  case (decide (eidx = eidx1)) as [<-|NE1]; case (decide (eidx = eidx2)) as [<-|NE2].
   -- (* this ∈ this.lview *)
      by apply emo_idx_le_ne_ne.
   -- (* this ∈ old.lview: old can't contain this *)
      exfalso. rewrite /= !fmap_app /= in EMO_eidx1.
      apply lookup_last_Some_2 in EMO_eidx1 as ->.
      eapply lookup_emo_old_emo_ne in EMO_eidx2;
        [|subst eidx gen'; rewrite !fmap_length in NE2; done].
      exploit (emo_ids_le_new E esi emo eidx2 e2); [done..|]. intro.
      rewrite lookup_app_l in EV2; [|done].
      move: (hwf_logview_closed _ EWF _ _ EV2 _ IN_LVIEW) => /lookup_lt_is_Some. lia.
   -- (* old ∈ this.lview *)
      rewrite /= !fmap_app /= in EMO_eidx2.
      apply lookup_last_Some_2 in EMO_eidx2 as ->.
      apply lookup_last_Some_2 in EV2 as ->.
      eapply lookup_emo_old_emo_ne in EMO_eidx1;
        [|subst eidx gen'; rewrite !fmap_length in NE1; done].
      have MAXgen : (gen_of eidx1 ≤ gen')%nat.
      { subst gen'. rewrite !fmap_length. by eapply max_gen. }
      destruct eidx1 as [gen1 i1'|gen1']; intros; simpl in *.
      ++ apply emo_idx_le_e_ne_1. lia.
      ++ apply emo_idx_le_ne_ne. lia.
   -- (* old ∈ old.lview *)
      eapply lookup_emo_old_emo_ne in EMO_eidx1,EMO_eidx2;
        [|subst eidx gen'; rewrite !fmap_length in NE1,NE2; done..].
      exploit (emo_ids_le_new E esi emo eidx2 e2); [done..|]. intros.
      rewrite lookup_app_l in EV2; [|done].
      by eapply (HB_EMO eidx1 eidx2).
Qed.

Lemma xo_agree_cut E emo i x
    (XO_AGREE : emo.*1.*1 = write_xo E)
    (LOOKUP : emo !! i = Some x) :
  take i (write_xo E) = filter (not_empty_pop E) (seq 0 x.1.1).
Proof.
  assert (emo.*1.*1 !! i = Some x.1.1).
  { by rewrite !list_lookup_fmap LOOKUP. }
  rewrite XO_AGREE in H. by apply take_filter_seq.
Qed.
End emo_lemmas.

Section emo_ghost.

Definition esiR : cmra := mono_listR (leibnizO event_id).
Definition emo_neR : cmra := mono_listR (leibnizO event_id).
Definition emo_eR : cmra := mono_list_listR (leibnizO event_id).
Definition emoR : cmra := prodR (prodR esiR emo_neR) emo_eR.

Definition emo_auth esi emo : emoR :=
  ( ●ML (esi : listO (leibnizO _)),
    ●ML (emo.*1.*1 : listO (leibnizO _)),
    ●MLL (emo.*1.*2 : listO (listO (leibnizO _)))).
Definition emo_lb esi emo : emoR :=
  ( ◯ML (esi : listO (leibnizO _)),
    ◯ML (emo.*1.*1 : listO (leibnizO _)),
    ◯MLL (emo.*1.*2 : listO (listO (leibnizO _)))).

Section rules.
Context `{!inG Σ emoR}.

Lemma emo_auth_lb_valid γ esi1 esi2 emo1 emo2 :
  own γ (emo_auth esi1 emo1) -∗
  own γ (emo_lb esi2 emo2) -∗
  ⌜ esi2 `prefix_of` esi1 ∧
    emo2.*1.*1 `prefix_of` emo1.*1.*1 ∧
    emo2.*1.*2 `prefixes_of` emo1.*1.*2 ⌝.
Proof.
  iIntros "Hauth Hlb".
  by iDestruct (own_valid_2 with "Hauth Hlb")
    as %[[?%mono_list_both_valid_L ?%mono_list_both_valid_L] ?%mono_list_list_both_valid_L].
Qed.

Lemma emo_lb_own_get γ esi emo :
  own γ (emo_auth esi emo) -∗ own γ (emo_lb esi emo).
Proof.
  intros. apply own_mono. rewrite !prod_included. simpl. split_and!.
  - apply mono_list_included.
  - apply mono_list_included.
  - apply mono_list_list_included.
Qed.

Lemma emo_own_alloc esi emo :
  ⊢ |==> ∃ γ, own γ (emo_auth esi emo) ∗ own γ (emo_lb esi emo).
Proof.
  setoid_rewrite <- own_op. apply own_alloc. rewrite !pair_valid /=. split_and!.
  - apply mono_list_both_valid. exists []. by rewrite app_nil_r.
  - apply mono_list_both_valid. exists []. by rewrite app_nil_r.
  - apply mono_list_list_both_valid. intros i.
    case Eess: (emo.*1.*2 !! i); simpl; [|done].
    exists []. by rewrite app_nil_r.
Qed.
Lemma emo_auth_own_update {γ esi emo} esi' emo' :
  esi `prefix_of` esi' →
  emo.*1.*1 `prefix_of` emo'.*1.*1 →
  emo.*1.*2 `prefixes_of` emo'.*1.*2 →
  own γ (emo_auth esi emo) ==∗ own γ (emo_auth esi' emo') ∗ own γ (emo_lb esi' emo').
Proof.
  iIntros (???) "Hauth".
  iAssert (own γ (emo_auth esi' emo')) with "[> Hauth]" as "Hauth".
  { iApply (own_update with "Hauth"). apply prod_update; [apply prod_update|].
    - by apply mono_list_update.
    - by apply mono_list_update.
    - by apply mono_list_list_update. }
  iModIntro. iSplit; [done|]. by iApply emo_lb_own_get.
Qed.

Lemma emo_auth_own_update_esi {γ esi emo} e :
  own γ (emo_auth esi emo) ==∗
  own γ (emo_auth (esi ++ [e]) emo) ∗ own γ (emo_lb (esi ++ [e]) emo).
Proof. apply emo_auth_own_update; [|done..]. by apply prefix_app_r. Qed.

Lemma emo_auth_own_update_emo_ne {γ esi emo} e msg :
  own γ (emo_auth esi emo) ==∗
  own γ (emo_auth esi (emo ++ [(e, [], msg)])) ∗ own γ (emo_lb esi (emo ++ [(e, [], msg)])).
Proof.
  apply emo_auth_own_update; [done|..].
  - rewrite !fmap_app /=. by apply prefix_app_r.
  - apply emo_insert_ne_12_prefixes.
Qed.

Lemma emo_auth_own_update_emo_e {γ esi emo} gen' e :
  own γ (emo_auth esi emo) ==∗
  own γ (emo_auth esi (emo_insert_e emo gen' e)) ∗
  own γ (emo_lb esi (emo_insert_e emo gen' e)).
Proof.
  apply emo_auth_own_update; [done|..].
  - by rewrite emo_insert_e_11.
  - apply emo_insert_e_12_prefixes.
Qed.

End rules.
End emo_ghost.
End emo.

(** * Ghost state construction *)

Class tstackG Σ := TStackG {
  tstk_graphG : inG Σ (historyR sevent) ;
  tstk_emoG : inG Σ emoR ;
}.

Definition tstackΣ : gFunctors := #[GFunctor (historyR sevent); GFunctor emoR].

Global Instance subG_tstackΣ {Σ} : subG tstackΣ Σ → tstackG Σ.
Proof. solve_inG. Qed.

(** * The invariant and local assertions *)
Section Interp.
Context `{!noprolG Σ, !tstackG Σ, !atomicG Σ}.
Local Existing Instances tstk_graphG tstk_emoG.

#[local] Notation iProp := (iProp Σ).
#[local] Notation vProp := (vProp Σ).
Local Open Scope nat_scope.

(** Physical resources of the node at loc [n] with a possible next node at [on'] *)
Definition StackNode n (on' : option loc) (v : Z) : vProp :=
  (∃ q, (n >> next) ↦{q} #(oloc_to_lit on')) ∗
  (n >> data) ↦ #v
  (* ∗ ⎡ † n … 2 ⎤ *)
  .

(** [StackNode] for each nodes in having values in [vs]. *)
Fixpoint StackNodes (on : option loc) (vs : list Z) : vProp :=
  match (on, vs) with
  | (None, []) => True
  | (Some n, v :: vs') =>
      ∃ on', StackNode n on' v ∗ StackNodes on' vs'
  | _ => False
  end.

#[global] Instance StackNodes_timeless on vs : Timeless (StackNodes on vs).
Proof. elim: vs on => [|v vs' IH] [n|]; apply _. Qed.

(** There's a node for each head ptr msgs. Used for [!("h" +ₗ #next)] in pop. *)
Definition AllLinks mo : vProp :=
  [∗ list] onV ∈ mo,
    if onV.1 is Some n
    then (∃ q on', @{onV.2} (n >> next) ↦{q} #(oloc_to_lit on'))
    else emp.

#[global] Instance AllLinks_objective mo : Objective (AllLinks mo).
Proof. apply big_sepL_objective => _ [[n|] V]; apply _. Qed.

#[global] Instance AllLinks_timeless mo : Timeless (AllLinks mo).
Proof. apply big_sepL_timeless => _ [[n|] V]; apply _. Qed.

Definition toHeadHist (start : time) mo : absHist :=
  map_seqP start ((λ olv, (#(oloc_to_lit olv.1), olv.2)) <$> mo).

(** For each event in the logical view, there is a corresponding message (that
is written or read by the event) in the snapshot [ζ]. *)
Definition seen_msgs esi emo (ζ : absHist) ti M : Prop :=
  ∀ e eidx
    (SEEN : e ∈ M)
    (EMO_LOOKUP : lookup_emo esi emo eidx = Some e),
    is_Some (ζ !! Pos.of_nat (Pos.to_nat ti + gen_of eidx)).

Definition SeenMsgs γh s esi emo ti M : vProp :=
  ∃ ζ, s sn⊒{γh} ζ ∗ ⌜seen_msgs esi emo ζ ti M⌝.

(** Collection of [SeenMsgs] at each event. Transferred to a thread when it
runs an event that synchronizes with these events. *)
Definition SeenMsgsAll γh s (E : history) esi emo ti : vProp :=
  ∀ e eidx eV
    (EV : E !! e = Some eV)
    (EMO_LOOKUP : lookup_emo esi emo eidx = Some e) ,
    @{eV.(ge_view).(dv_comm)} SeenMsgs γh s esi emo ti eV.(ge_lview).

(** The top view is larger than commit views of pushes (release write) *)
Definition top_view_released (E : history) Vt : Prop :=
  ∀ e eV v (EV : E !! e = Some eV) (PUSH : eV.(ge_event) = Push v),
    eV.(ge_view).(dv_comm) ⊑ Vt.

(** [seen_logview] at each event. TODO: move to history.v? *)
Definition seen_logview_all (E : history) : Prop :=
  ∀ e eV (EV : E !! e = Some eV),
    seen_logview E eV.(ge_lview) eV.(ge_view).(dv_comm).

(** ** Top-level predicates & invariant *)

Definition StackInv γg s E : vProp :=
  ∃ (γh γe : gname) ti esi emo stk (ont : option loc) Vt Vi,
  meta s nroot (γh,γe,ti) ∗

  (* Logical states *)
  history_master γg 1 E ∗
  ⎡own γe (emo_auth esi emo)⎤ ∗

  (* Physical resources *)
  (* head *)
  (∃ Vb, @{Vb} s at↦{γh} (toHeadHist ti ((None, Vi) :: emo.*2))) ∗(* ⎡ † s … 1 ⎤ *)
  (* physical stack *)
  @{Vt} StackNodes ont stk.*1.*1.*2 ∗
  (* all nodes, including the popped ones *)
  AllLinks emo.*2 ∗

  SeenMsgsAll γh s E esi emo ti ∗

  ⌜ « LAST_MSG : last ((None, Vi) :: emo.*2) = Some (ont, Vt) » ∧
    « TOP_SEEN_PUSH : top_view_released E Vt » ∧
    « SEEN_ALL : seen_logview_all E » ∧
    « HB_XO : hb_ord E (seq 0 (length E)) » ∧
    « ESI_EMO_GOOD : esi_emo_good E esi emo » ∧
    « XO_INTERP : stack_interp E (write_xo E) [] stk » ⌝
  .

#[global] Instance StackInv_objective γg s E : Objective (StackInv γg s E) := _.
#[global] Instance StackInv_timeless γg s E : Timeless (StackInv γg s E) := _.

Definition StackLocal (_ : namespace) γg s E M : vProp :=
  ∃ (γh γe : gname) ti esi emo,
  meta s nroot (γh,γe,ti) ∗

  (* Local snapshot of the history *)
  history_snap γg E M ∗
  ⎡own γe (emo_lb esi emo)⎤ ∗

  (* "I have seen all the messages in the head pointer that corresponds to
  events in my logView". *)
  SeenMsgs γh s esi emo ti M ∗

  ⌜ lin_of_emo esi emo ≡ₚ seq 0 (length E) ⌝
  .

#[global] Instance StackLocal_persistent N γg s E M :
  Persistent (StackLocal N γg s E M) := _.

(** ** The main linearization lemma *)
Lemma interp_lin_induction E emo stk i
    (GEN_GOOD : Forall (λ '((e, es), (on, V)), emo_gen_good E e es on V) emo)
    (XO_AGREE : emo.*1.*1 = write_xo E)
    (EMO_11_INTERP : stack_interp E (take i emo).*1.*1 [] stk) :
  stack_interp E (lin_of_emo [] (take i emo)) [] stk.
Proof.
  revert stk EMO_11_INTERP.
  induction i; intros; auto.
  destruct (le_lt_dec (length emo) i) as [Hi|Hi].
  - assert (length emo <= S i) as HSi by lia.
    apply take_ge in Hi; apply take_ge in HSi.
    rewrite HSi; rewrite HSi in EMO_11_INTERP.
    rewrite Hi in IHi. by apply IHi.
  - apply lookup_lt_is_Some in Hi as Hx; destruct Hx as [[[e es] [on V]] Hx].
    eapply xo_agree_cut in XO_AGREE as HXO; last apply Hx. simpl in HXO.
    apply take_S_r in Hx as Htake.
    rewrite Htake fmap_app fmap_app in EMO_11_INTERP; rewrite Htake.
    rewrite lin_of_emo_app lin_of_emo_singleton.
    rewrite fmap_cons fmap_nil fmap_cons fmap_nil /= in EMO_11_INTERP.
    apply stack_interp_app in EMO_11_INTERP as EMO_MID; des.
    apply IHi in EMO_MID as EMO_MID_LIN; des.
    apply stack_interp_app; exists midstk; split; auto.
    apply stack_interp_app; exists stk; split; auto.
    (* if es = [], nothing more to do *)
    destruct es; [constructor|].
    (* if es ≠ [], prove stk = [] *)
    rewrite -> Forall_lookup in GEN_GOOD.
    specialize (GEN_GOOD _ _ Hx) as []. unnw.
    specialize (EMPPOP_EMPTY ltac:(done)).
    rewrite -HXO -XO_AGREE in EMPPOP_EMPTY.
    rewrite fmap_take fmap_take in EMO_11_INTERP.
    specialize (stack_interp_functional _ _ _ _ _ EMO_11_INTERP EMPPOP_EMPTY) as ->.
    apply stack_interp_esi. apply (Forall_impl _ _ _ EMPPOPS).
    naive_solver.
Qed.

Lemma stack_linearization E emo esi stk
    (SEEN_ALL : seen_logview_all E)
    (HB_XO : hb_ord E (seq 0 (length E)))
    (ESI_EMO_GOOD : esi_emo_good E esi emo)
    (XO_INTERP : stack_interp E (write_xo E) [] stk) :
  StackLinearizability E.
Proof.
  destruct ESI_EMO_GOOD.
  constructor 1 with (seq 0 (length E)) (lin_of_emo esi emo) stk.
  - done.
  - done.
  - unfold write_xo in XO_AGREE. rewrite <- XO_AGREE. by apply not_empty_pop_lin.
  - done.
  - unfold hb_ord. intros.
    have [eV1 EV1] : ∃ eV1, E !! e1 = Some eV1 by eapply ord_idx_event.
    have E1' : seq 0 (length E) !! e1 = Some e1 by by eapply lookup_xo, lookup_lt_Some.
    have E2' : seq 0 (length E) !! e2 = Some e2 by by eapply lookup_xo, lookup_lt_Some.
    have NODUP : NoDup (lin_of_emo esi emo) by eapply ord_nodup.
    exploit (lin_of_emo_lookup_lookup_emo esi emo i1); [done..|].
    intros (eidx1 & -> & EMO_LOOKUP1).
    exploit (lin_of_emo_lookup_lookup_emo esi emo i2); [done..|].
    intros (eidx2 & -> & EMO_LOOKUP2).
    exploit (HB_EMO eidx1 eidx2); [done..|]. intros LE_EIDX. des.

    destruct eidx1 as [gen1 i1'|gen1']; destruct eidx2 as [gen2 i2'|gen2'].
    + (* emppop, emppop *) inv LE_EIDX.
      * by apply Nat.lt_le_incl,lin_idx_e_gen_mono.
      * simplify_eq. apply lin_idx_e_i'_mono. done.
    + (* emppop, _ *) inv LE_EIDX.
      * (* gen1 < S gen2' *)
        exploit (lin_idx_e_ne_gen_mono esi emo gen1 i1' gen2'); [done..|lia].
      * (* gen1 = S gen2' *) exfalso. rename gen2' into gen'.
        exploit (lookup_emo_inv_e esi emo (S gen')); [done..|].
        intros (es & GEN1 & ES_i1').
        exploit (lookup_emo_inv_ne esi emo gen'); [done..|]. intros GEN2.
        des. simplify_list_eq.
        exploit (HB_XO e1 e2); [done..|]. (* this contradicts RW_XO *)
        (* Reconstruct the generation of interest. *)
        have GEN : emo.*1 !! gen' = Some (e2, es).
        { apply list_lookup_fmap_inv in GEN1,EMO_LOOKUP2.
          destruct GEN1 as ([? ?] & -> & GEN1).
          destruct EMO_LOOKUP2 as ([? ?] & -> & EMO_LOOKUP2).
          by simplify_eq/=. }
        apply list_lookup_fmap_inv in GEN.
        destruct GEN as ([[? ?] [? ?]] & [= <- <-] & GEN).
        rewrite ->Forall_lookup in GEN_GOOD. destruct (GEN_GOOD _ _ GEN).
        rewrite ->Forall_lookup in EMPPOPS.
        specialize (EMPPOPS _ _ ES_i1'). des.
        clear -RW_XO HB_XO. lia.
    + (* _, emppop *)
      inv LE_EIDX. by apply Nat.lt_le_incl,lin_idx_ne_e_gen_mono.
    + (* _, _ *)
      des. inv LE_EIDX.
      exploit (HB_XO e1 e2); [done..|]. intros LEe.
      apply lin_idx_ne_gen_mono. done.
  - done.
  - (* INTERP_LIN *)
    rewrite lin_of_emo_split_esi.
    apply stack_interp_app; exists []; split.
    { apply stack_interp_esi. by inv ESI_GOOD. }
    rewrite <- XO_AGREE in XO_INTERP.
    assert (emo = take (length emo) emo).
    { symmetry. by apply take_ge. }
    rewrite H; rewrite H in XO_INTERP.
    by apply interp_lin_induction.
Qed.

(** ** Properties of assertions *)
Section assertion_props.
Lemma toHeadHist_lookup_Some ti mo t v V :
  toHeadHist ti mo !! t = Some (v, V) ↔
  (ti ≤ t)%positive
  ∧ ∃ on, v = #(oloc_to_lit on)
  ∧ mo !! (Pos.to_nat t - Pos.to_nat ti)%nat = Some (on, V).
Proof.
  rewrite lookup_map_seqP_Some. f_equiv.
  rewrite list_lookup_fmap fmap_Some. split.
  - intros ([] & ? & ?). simplify_eq. naive_solver.
  - intros (on & -> & ?). exists (on, V). naive_solver.
Qed.

Lemma toHeadHist_lookup_None ti mo t :
  (toHeadHist ti mo) !! t = None ↔
  (t < ti)%positive ∨ (ti +p (length mo) ≤ t)%positive.
Proof. by rewrite lookup_map_seqP_None fmap_length. Qed.

Lemma toHeadHist_lookup_Some_is_comparable_nullable_loc mo ti t v V (on : option loc) :
  toHeadHist ti mo !! t = Some (v, V) →
  ∃ vl : lit, v = #vl ∧ lit_comparable (oloc_to_lit on) vl.
Proof.
  rewrite toHeadHist_lookup_Some. intros (? & on' & -> & _).
  exists (oloc_to_lit on'). split; [done|].
  destruct on, on'; constructor.
Qed.

Lemma seen_msgs_absHist_mono esi emo ζ1 ζ2 ti M :
  ζ1 ⊆ ζ2 → seen_msgs esi emo ζ1 ti M → seen_msgs esi emo ζ2 ti M.
Proof.
  intros Subζ SM e eidx SEEN EMO_LOOKUP.
  destruct (SM _ _ SEEN EMO_LOOKUP) as [msg Eqt].
  exists msg. by eapply lookup_weaken.
Qed.

Lemma seen_msgs_esi_emo_mono esi1 esi2 emo1 emo2 ζ ti M :
  (∀ e eidx, e ∈ M → lookup_emo esi2 emo2 eidx = Some e → lookup_emo esi1 emo1 eidx = Some e) →
  esi1 ⊑ esi2 → emo1.*1.*1 ⊑ emo2.*1.*1 → emo1.*1.*2 `prefixes_of` emo2.*1.*2 →
  seen_msgs esi1 emo1 ζ ti M → seen_msgs esi2 emo2 ζ ti M.
Proof. intros In ??? SM ????. by apply (SM _ _ SEEN),In. Qed.

Lemma seen_msgs_mono esi1 esi2 emo1 emo2 ζ1 ζ2 ti M
    (INJ : emo_inj esi2 emo2)
    (IN_EMO : set_Forall (λ e, ∃ eidx, lookup_emo esi1 emo1 eidx = Some e) M)
    (Subesi : esi1 ⊑ esi2)
    (Subne : emo1.*1.*1 ⊑ emo2.*1.*1)
    (Subess : emo1.*1.*2 `prefixes_of` emo2.*1.*2)
    (Subζ : ζ1 ⊆ ζ2)
    (SM : seen_msgs esi1 emo1 ζ1 ti M) :
  seen_msgs esi2 emo2 ζ2 ti M.
Proof.
  eapply (seen_msgs_absHist_mono _ _ _ _ _ _ Subζ).
  revert SM. eapply seen_msgs_esi_emo_mono; [|done..].
  intros e eidx2 In EMO_LOOKUP2.
  specialize (IN_EMO e In) as [eidx1 EMO_LOOKUP1].
  exploit (INJ eidx1 eidx2); [|done|by intros ->].
  by eapply sub_esi_emo_lookup.
Qed.

Lemma seen_msgs_union esi emo ζ ti M1 M2 :
  seen_msgs esi emo ζ ti M1 → seen_msgs esi emo ζ ti M2 → seen_msgs esi emo ζ ti (M1 ∪ M2).
Proof. by intros SM1 SM2 e n [Ine|Ine]%elem_of_union; [apply SM1|apply SM2]. Qed.

Lemma SeenMsgs_mono esi1 esi2 emo1 emo2 ti M γh s
    (INJ : emo_inj esi2 emo2)
    (IN_EMO : set_Forall (λ e, ∃ eidx, lookup_emo esi1 emo1 eidx = Some e) M)
    (Subesi : esi1 ⊑ esi2)
    (Subne : emo1.*1.*1 ⊑ emo2.*1.*1)
    (Subess : emo1.*1.*2 `prefixes_of` emo2.*1.*2) :
  SeenMsgs γh s esi1 emo1 ti M ⊢ SeenMsgs γh s esi2 emo2 ti M.
Proof.
  iDestruct 1 as (ζ) "[sn⊒ %SM]".
  iExists ζ. iFrame. iPureIntro. revert SM. by eapply seen_msgs_mono.
Qed.

Lemma AllLinks_node_next_access mo n Vn :
  (Some n, Vn) ∈ mo →
  AllLinks mo -∗ AllLinks mo ∗ ∃ q on, @{Vn} (n >> 0) ↦{q} #(oloc_to_lit on).
Proof.
  iIntros ([i Inn]%elem_of_list_lookup) "AllLinks".
  rewrite {1}/AllLinks (big_sepL_lookup_acc _ _ _ _ Inn) /=.
  iDestruct "AllLinks" as "[n↦ Close]".
  iDestruct "n↦" as (q on') "[n↦1 n↦2]". iSplitL "n↦1 Close".
  - iApply "Close". eauto with iFrame.
  - eauto with iFrame.
Qed.

Lemma AllLinks_node_access_prim ti Vi mo t (l' : loc) :
  fst <$> toHeadHist ti ((None, Vi) :: mo) !! t = Some #l' →
  AllLinks mo ⊢ ∃ (q' : Qp) (C' : cell), ▷ <subj> l' p↦{q'} C'.
Proof.
  intros ([] & Eq' & (? & on & Eq & Eq2)%toHeadHist_lookup_Some)%lookup_fmap_Some'.
  simpl in Eq'. subst v.
  assert (on = Some l') as ->.
  { clear -Eq. destruct on; by inversion Eq. } clear Eq.
  apply elem_of_list_lookup_2 in Eq2 as [[=]|Eq2]%elem_of_cons.
  rewrite (AllLinks_node_next_access _ _ _ Eq2).
  iIntros "[As En]". iDestruct "En" as (q' on) "En". iExists _.
  by rewrite (shift_0 l') own_loc_na_view_at_own_loc_prim_subjectively.
Qed.

Lemma toHeadHist_insert ti mo t on V :
  (Pos.to_nat t - Pos.to_nat ti)%nat = length mo →
  (1 ≤ length mo)%nat →
  <[t := (#(oloc_to_lit on), V)]>(toHeadHist ti mo) =
  toHeadHist ti (mo ++ [(on, V)]).
Proof.
  intros Eq ?. apply map_eq.
  intros i. case (decide (i = t)) => [->|?].
  - rewrite lookup_insert. symmetry.
    apply toHeadHist_lookup_Some. split; [lia|].
    rewrite Eq !lookup_app_r // Nat.sub_diag /=. naive_solver.
  - rewrite lookup_insert_ne; [|done].
    destruct (toHeadHist ti mo !! i) as [[vi Vi]|] eqn:Eqi; rewrite Eqi; symmetry.
    + apply toHeadHist_lookup_Some in Eqi as (Letn & on' & -> & Eq1).
      apply toHeadHist_lookup_Some. split; [done|].
      exists on'. split; [done|]. by apply (lookup_app_l_Some _ _ _ _ Eq1).
    + apply toHeadHist_lookup_None.
      apply toHeadHist_lookup_None in Eqi as [?|Eqi]; [by left|right].
      rewrite app_length /=. move : Eqi.
      rewrite Nat.add_1_r pos_add_succ_r_2.
      rewrite (_: ti +p length mo = t); [lia|]. rewrite -Eq /pos_add_nat; lia.
Qed.

Lemma seen_logview_all_add E eV
    (WF : history_wf E)
    (SEEN_LVIEW : seen_logview (E ++ [eV]) eV.(ge_lview) eV.(ge_view).(dv_comm))
    (SEEN_ALL : seen_logview_all E) :
  seen_logview_all (E ++ [eV]).
Proof.
  intros ???. case (decide (e = length E)) as [->|NE].
  - by apply lookup_last_Some_2 in EV as ->.
  - rewrite lookup_app_1_ne in EV; [|done].
    move: (SEEN_ALL _ _ EV). apply seen_logview_mono. by eexists.
Qed.

End assertion_props.

End Interp.

(** * Proofs *)
Section proof.
Context `{!noprolG Σ, !tstackG Σ, !atomicG Σ}.
Local Existing Instances tstk_graphG tstk_emoG.

#[local] Notation iProp := (iProp Σ).
#[local] Notation vProp := (vProp Σ).

Lemma StackInv_StackLinearizability_instance :
  ∀ γg s E, StackInv γg s E ⊢ ⌜ StackLinearizability E ⌝.
Proof.
  intros. iDestruct 1 as (?????????) "(_ & _ & _ & _ & _ & _ & _ & %Props)".
  des. iPureIntro. by eapply stack_linearization.
Qed.

Lemma StackInv_history_master_acc_instance :
  ∀ γg s E, StackInv γg s E ⊢
    history_master γg 1 E ∗
    (history_master γg 1 E -∗ StackInv γg s E).
Proof.
  intros. iDestruct 1 as (?????????) "(? & $ & ?)". iIntros "$". eauto 11 with iFrame.
Qed.

Lemma StackInv_history_snap_instance :
  ∀ γg s E E' M',
    StackInv γg s E -∗ history_snap γg E' M' -∗ ⌜ E' ⊑ E ⌝.
Proof.
  intros. iDestruct 1 as (?????????) "(? & E & ?)". iIntros "E'".
  by iDestruct (history_master_snap_included with "E E'") as %?.
Qed.

Lemma StackLocal_history_snap_instance :
  ∀ N γg s E M, StackLocal N γg s E M ⊢ history_snap γg E M.
Proof. intros. iDestruct 1 as (?????) "(_ & $ & _)". Qed.

Lemma new_stack_spec :
  new_stack_spec' new_tstack StackLocal StackInv.
Proof.
  iIntros (N tid Φ) "_ Post".
  wp_lam.
  (* allocate head *)
  wp_apply wp_new; [done..|].
  iIntros (s) "([H†|%] & Hs & Hms & _)"; [|done].
  wp_let.
  (* initialize head as null, and create protocol *)
  rewrite own_loc_na_vec_singleton.
  iApply wp_fupd.
  wp_write.
  iMod (AtomicPtsTo_CON_from_na with "Hs") as (γh ti V0) "(#⊒V0 & #sn⊒ & at↦)".

  iMod history_master_alloc_empty as (γg) "[E● #E◯]".
  iMod (emo_own_alloc [] []) as (γe) "[M● #M◯]".
  iMod (meta_set _ _ (γh,γe,ti) nroot with "Hms") as "#Hms"; [done|].
  iApply ("Post" $! γg). iModIntro.
  iSplitL "".
  - iExists γh,γe,ti,[],[]. rewrite shift_0.
    iFrame "Hms E◯ M◯". iSplit; last iSplit.
    + iApply SeenLogview_empty.
    + iExists _. iFrame "sn⊒". done.
    + done.
  - iExists γh,γe,ti. iExists [],[],[],None,V0,V0. rewrite shift_0.
    iFrame "Hms E● M●". iSplit; last iSplit; last iSplit; last iSplit.
    + iDestruct (view_at_intro with "at↦") as (Vb) "[? ?]". by iExists Vb.
    + done.
    + rewrite /AllLinks //=.
    + by iIntros (?????).
    + iPureIntro. unnw. split_and!; [done..|constructor].
Qed.

Local Tactic Notation "simplify_meta" "with" constr(Hs) :=
  iDestruct (meta_agree with Hs) as %[[-> ->]%pair_inj ->]%pair_inj.

Lemma atom_try_push_internal :
  ∀ N (DISJ: N ## histN) s tid γg E0 M V (v : Z) (Posv: 0 < v) (n : loc),
  (* E1 is a snapshot of the history, locally observed by M *)
  ⊒V -∗ StackLocal N γg s E0 M -∗
  (n >> next) ↦ - -∗ (n >> data) ↦ #v -∗
  (* PUBLIC PRE *)
  <<< ∀ E, ▷ StackInv γg s E >>>
    try_push_internal [ #s ; #n] @ tid; ↑N
  <<< ∃ (b : bool) V' E' (psId : event_id) ps Vpush M',
      (* PUBLIC POST *)
      ▷ StackInv γg s E' ∗
      ⊒V' ∗ @{V'} StackLocal N γg s E' M' ∗
      (⌜ (* FAIL_RACE case *)
        b = false ∧ E' = E ∧ M' = M ⌝ ∗
        (n >> next) ↦ - ∗ (n >> data) ↦ #v
      ∨
      ⌜ b = true ∧
        Vpush.(dv_in) = V ∧ Vpush.(dv_comm) = V' ∧
        (* Vpush ⊑ V' ∧ *) (* << only works if push is also acquiring *)
        (* ps is a new push event with which E' strictly extends E *)
        is_push ps v ∧
        psId = length E ∧
        E' = E ++ [mkGraphEvent ps Vpush M'] ∧
        M' = {[psId]} ∪ M ⌝),
      (* RETURN VALUE AT COMMITTING POINT *)
      RET #b, emp >>>
  .
Proof.
  intros. iIntros "#⊒V #StackLocal n↦ d↦" (Φ) "AU".
  iDestruct "StackLocal" as (?? ti esi0 emo0) "(MS & E◯0 & M◯0 & (%ζh0 & sn⊒0 & %SM0) & %LIN_PERM0)".

  wp_lam. wp_bind (!ʳˡˣ _)%E.

  (* Inv access #1 *)
  iMod "AU" as (E1) "[>StackInv [Abort1 _]]".
  iDestruct "StackInv" as (??? esi1 emo1 stk1 ont1 Vt1 Vi1)
    "(MS' & E●1 & M●1 & (%Vb1 & at↦1) & StackNodes1 & AllLinks1 & #SeenMsgsAll1 & %Props1)".
  simplify_meta with "MS' MS".
  (* get snapshot of E1 *)
  iDestruct (history_master_snap with "E●1") as "#E◯1".
  iDestruct (history_master_snap_included with "E●1 E◯0") as %SubE01.
  iDestruct (emo_auth_lb_valid with "M●1 M◯0") as %(Subesi01 & Subne01 & Subess01).
  (* read *)
  wp_apply (AtomicSeen_relaxed_read with "[$sn⊒0 $at↦1 $⊒V]"); first solve_ndisj.

  iIntros (th1 vh1 Vh1 V1 ζh1) "(Subζ & #⊒V1 & _ & #sn⊒1 & at↦1') {sn⊒0 ⊒V}".
  iDestruct "Subζ" as %([Subemo0ζh1 Subζh1emo1] & Eqth1 & MAXth1 & LeVV1).

  (* Close Inv #1 *)
  iMod ("Abort1" with "[- n↦ d↦]") as "AU".
  { iExists _,_,_. iExists esi1,emo1,stk1,ont1,Vt1,Vi1.
    iNext. iFrame "∗"; eauto with iFrame. } clear Props1.

  (* check what we just read *)
  move: (lookup_weaken _ _ _ _ Eqth1 Subζh1emo1) => /toHeadHist_lookup_Some.
  intros (Letith1 & on1 & -> & Eqemo1).

  iPoseProof "E◯0" as "[_ PSV]".
  iDestruct (SeenLogview_closed with "PSV") as %SubME0.
  have SubMemo0 : set_Forall (λ e, ∃ eidx, lookup_emo esi0 emo0 eidx = Some e) M.
  { intros ??. eapply event_in_esi_emo; [done|]. by apply SubME0. }

  (* set n's link to what we read from Head *)
  iModIntro. wp_let. wp_op.
  iDestruct "n↦" as (vn) "n↦". wp_write. clear vn Vb1.

  (* Inv access #2 *)
  iMod "AU" as (E2) "[>StackInv [_ Commit2]]".
  iDestruct "StackInv" as (??? esi2 emo2 stk2 ont2 Vt2 Vi2)
    "(MS' & E●2 & M●2 & (%Vb2 & at↦2) & StackNodes2 & AllLinks2 & #SeenMsgsAll2 & %Props2)".
  simplify_meta with "MS' MS".

  have Injemo2 : emo_inj esi2 emo2.
  { apply (lin_perm_emo_inj E2). des. by destruct ESI_EMO_GOOD. }

  iDestruct (history_master_wf with "E●2") as %EWF2.
  iDestruct (history_master_snap_included with "E●2 E◯0") as %SubE02. clear SubE01.
  iDestruct (emo_auth_lb_valid with "M●2 M◯0") as %(Subesi02 & Subne02 & Subess02).
  clear Subesi01 Subne01 Subess01.
  have SubME2 : set_in_bound M E2 by apply (set_in_bound_mono _ E0).
  have SubMemo2 : set_Forall (λ e, ∃ eidx, lookup_emo esi2 emo2 eidx = Some e) M.
  { clear -SubMemo0 Subesi02 Subne02 Subess02.
    apply (set_Forall_impl _ _ _ SubMemo0).
    intros ? [eV ?]. exists eV. by eapply sub_esi_emo_lookup. }

  iCombine "n↦ d↦" as "n↦d↦". iCombine "n↦d↦ PSV" as "CHUNK".
  iDestruct (view_at_intro_incl with "CHUNK ⊒V1")
    as (V1') "(#⊒V1' & %LeV1V1' & [n↦d↦ #PSVA])".

  iDestruct (view_at_elim with "⊒V1 sn⊒1") as "sn⊒1'".
  iDestruct (AtomicPtsTo_AtomicSeen_latest_1 with "at↦2 sn⊒1'") as %Subζh1emo2.

  (* CAS with possible pointer comparison *)
  wp_apply (AtomicSeen_CON_CAS _ _ _ _ _ _ _ (oloc_to_lit on1) #n _ ∅
              with "[$sn⊒1' $at↦2 $⊒V1']"); [done|done|done|solve_ndisj|..]; [|done|].
  { intros t' v' NE. rewrite lookup_fmap_Some'.
    intros ([] & <- & ?). by eapply toHeadHist_lookup_Some_is_comparable_nullable_loc. }

  iIntros (b2 tr2 vr2 Vr2 V2 ζh2 ζn2) "(F & #⊒V2 & #sn⊒2 & at↦2 & CASE)".
  iDestruct "F" as %([Subζh1ζh2 Subζh2ζn2] & Eqtr2 & MAXtr2 & LeV1V2).

  iDestruct "CASE" as "[[F ⊒Vr2]|[F sVw2]]".
  { (* fail CAS *)
    iDestruct "F" as %(-> & NEq & ->).
    iDestruct (history_master_snap with "E●2") as "#E◯2".
    iDestruct (emo_lb_own_get with "M●2") as "#M◯2".

    have bLeVV : bool_decide (V ⊑ V) by eapply bool_decide_unpack; eauto.
    set Vps := mkDView V V V bLeVV.
    iMod ("Commit2" $! false V2 E2 dummy_eid dummy_sevt Vps M with "[-]") as "HΦ".
    { iSplitR "n↦d↦"; last iSplitR; last iSplitR.
      - iExists _,_,_. iExists esi2,emo2,stk2,ont2,Vt2,Vi2.
        iNext. iFrame "∗"; eauto with iFrame.
      - done.
      - iExists _,_,_,esi2,emo2. iFrame "MS M◯2". iSplit; last iSplit.
        + iDestruct "E◯2" as "[$ ?]".
          iApply (view_at_mono with "PSVA"); [done|].
          by apply SeenLogview_map_mono.
        + iExists ζh2. iFrame "#". iPureIntro.
          apply (seen_msgs_mono esi0 _ emo0 _ ζh0); [done..|by etrans|done].
        + iPureIntro. des. by destruct ESI_EMO_GOOD.
      - iLeft. iSplit; [done|].
        iDestruct (view_at_elim with "⊒V1' n↦d↦") as "[n↦ $]". by iExists _. }
    by iApply "HΦ". }

  (* successful CAS *)
  iDestruct "F" as %[-> ->].
  iDestruct "sVw2" as (Vw2 (FRt & Eqζn2 & Eqt'' & LeVr2Vw2 & SLeVr2Vw2 & NLeV2Ve2 & NEqV1'V2 & LeV2Vw2)) "#[_ ⊒Vw2]".
  iDestruct "n↦d↦" as "[n↦ d↦]".

  assert (Eqt2 := lookup_weaken _ _ _ _ Eqtr2 Subζh2ζn2).
  rewrite Eqζn2 lookup_insert_ne in Eqt2; last by (clear; lia).
  apply toHeadHist_lookup_Some in Eqt2 as (Letitr2 & on2 & Eqon2 & Eqn2).
  assert (on2 = on1) as ->. { clear -Eqon2. by simplify_eq. } clear Eqon2.

  assert (EqL: (Pos.to_nat tr2 - Pos.to_nat ti)%nat = length emo2.*2).
  { assert (LtL := lookup_lt_Some _ _ _ Eqn2).
    clear -FRt Letitr2 LtL.
    apply toHeadHist_lookup_None in FRt as [?|Let']; first (exfalso; lia).
    apply : (anti_symm (le)).
    - clear -LtL. rewrite cons_length /= in LtL. lia.
    - clear LtL. rewrite cons_length /= /pos_add_nat in Let'; lia. }
  rewrite EqL in Eqn2.

  assert (ont2 = on1 ∧ Vt2 = Vr2) as [-> ->].
  { clear -Eqn2 Props2. des.
    move: Eqn2. rewrite lookup_last_cons LAST_MSG => [=] //. }

  have LeVV2 : V ⊑ V2. { clear -LeVV1 LeV1V1' LeV1V2. solve_lat. }
  have bLeVV2 : bool_decide (V ⊑ V2) by eapply bool_decide_unpack; eauto.
  set Vps := mkDView V V2 Vw2 bLeVV2.

  set psId := length E2.
  set M' := {[psId]} ∪ M.
  set egV' := mkGraphEvent (Push v) Vps M'.
  set E2' := E2 ++ [egV'].
  set stk2' := (psId, v, V2, M') :: stk2.
  set emo2' := emo2 ++ [((psId, []), (Some n, Vw2))].

  have NInps : psId ∉ M. { move => /SubME2 /lookup_lt_is_Some. lia. }
  have SubE22' : E2 ⊑ E2' by apply prefix_app_r.
  have Subne22' : emo2.*1.*1 ⊑ emo2'.*1.*1.
  { subst emo2'. rewrite !fmap_app /=. by apply prefix_app_r. }
  have Subne02' : emo0.*1.*1 ⊑ emo2'.*1.*1 by etrans.
  have Subess22' : emo2.*1.*2 `prefixes_of` emo2'.*1.*2.
  { apply emo_insert_ne_12_prefixes. }
  have Subess02' : emo0.*1.*2 `prefixes_of` emo2'.*1.*2 by etrans.
  have Injemo2' : emo_inj esi2 emo2' by des; by apply (emo_inj_emo_insert_ne E2).
  have LeVV' : V ⊑ Vw2. { clear -LeVV2 LeV2Vw2. solve_lat. }

  iAssert (@{Vps.(dv_comm)} SeenLogview E2' M')%I with "[]" as "#PSV2'".
  { rewrite -SeenLogview_insert'. iSplitL; [|done].
    erewrite SeenLogview_map_mono; [iFrame "PSVA"|done..]. }
  iAssert ⌜seen_logview E2' M' Vps.(dv_comm)⌝%I with "[]" as %PSV2'.
  { rewrite view_at_eq /view_at_def /=. iDestruct "PSV2'" as %?. done. }

  iAssert (@{Vw2} SeenEvent E2' psId egV')%I with "[]" as "#SYE".
  { iSplit; last iSplit; [..|by iPureIntro].
    - iPureIntro. by rewrite lookup_app_1_eq.
    - rewrite /= view_at_view_at. iApply "PSV2'". }

  iCombine "n↦ d↦" as "n↦d↦".

  iAssert (AllLinks emo2'.*2 ∗ @{Vw2} StackNodes (Some n) stk2'.*1.*1.*2)%I
    with "[AllLinks2 StackNodes2 n↦d↦]" as "[AllLinks2' StackNodes2']".
  { iDestruct (view_at_mono_2 _ Vw2 with "n↦d↦") as "[[n↦1 n↦2] d↦]";
      [solve_lat|]. iSplitL "AllLinks2 n↦1".
    - rewrite {2}/AllLinks fmap_app /=. rewrite big_sepL_app /=. eauto with iFrame.
    - rewrite fmap_cons /=. rewrite {2}/StackNodes /= -/StackNodes.
      iExists on1. iSplitL "n↦2 d↦".
      + rewrite /StackNode. iSplitL "n↦2"; first iExists _; iFrame.
      + iApply (view_at_mono_2 _ _ _ LeVr2Vw2 with "StackNodes2"). }

  have SM2' : seen_msgs esi2 emo2' ζh2 ti M'.
  { intros ????. des.
    case (decide (eidx = (emo_ne (length emo2.*1.*1)))) as [->|NEeidx].
    - subst emo2'. simpl in *. rewrite !fmap_app /= in EMO_LOOKUP.
      apply lookup_last_Some_2 in EMO_LOOKUP as ->.
      rewrite !fmap_length -(fmap_length snd). rewrite -EqL.
      rewrite (_ : Pos.of_nat (Pos.to_nat ti + S (Pos.to_nat tr2 - Pos.to_nat ti)) = tr2 + 1)%positive; [done|lia].
    - case (decide (e = psId)) as [->|NEe].
      { exfalso. rewrite !fmap_length in NEeidx.
        apply lookup_emo_old_emo_ne in EMO_LOOKUP; [|done].
        eapply emo_ids_le_new in EMO_LOOKUP; [|done]. subst psId. lia. }
      apply (seen_msgs_mono _ esi2 _ emo2' _ ζh2) in SM0; [|done| |done..|by etrans].
      + exploit (SM0 e eidx); [|done..]. set_solver +SEEN NEe.
      + intros ? ?. eapply event_in_esi_emo; [done|]. by apply SubME0. }

  have LIN_PERM2' : lin_of_emo esi2 emo2' ≡ₚ seq 0 (length E2').
  { rewrite app_length. apply lin_perm_add_emo_ne. des. by destruct ESI_EMO_GOOD. }

  iMod (history_master_update _ _ E2' with "E●2") as "[E●2' #E◯2']";
    [done|by apply (history_wf_add E2 egV' M)|].
  iMod (emo_auth_own_update_emo_ne psId with "M●2") as "[M●2' #M◯2']".

  iMod ("Commit2" $! true V2 E2' psId (Push v) Vps M' with "[-]") as "HΦ".
  { des. destruct ESI_EMO_GOOD.
    iSplitL; last iSplitL; last iSplitL.
    - iExists _,_,_. iExists esi2,emo2',stk2',(Some n),Vw2,Vi2.
      iFrame "∗". iNext. iSplitL; last iSplitL.
      { (* at↦ *) subst ζn2. rewrite (toHeadHist_insert _ _ _ (Some n)).
        - subst emo2'. rewrite !fmap_app /=. eauto with iFrame.
        - clear -Letitr2 EqL. rewrite cons_length /=. lia.
        - clear. rewrite cons_length /=. lia. }
      { (* SeenMsgsAll γh s E2' esi2 emo2' ti *) iIntros (???? EMO_LOOKUP).
        (* TODO: Suspicious repetition of the same case analysis in SM2' proof. *)
        case (decide (eidx = emo_ne (length emo2.*1.*1))) as [->|NEeidx].
        - subst emo2'. rewrite /= !fmap_app /= in EMO_LOOKUP.
          apply lookup_last_Some_2 in EMO_LOOKUP as ->.
          apply lookup_last_Some_2 in EV as ->. subst egV'. simpl.
          iExists ζh2. iFrame (SM2') "sn⊒2".
        - rewrite !fmap_length in NEeidx.
          apply lookup_emo_old_emo_ne in EMO_LOOKUP; [|done].
          apply (emo_ids_le_new E2) in EMO_LOOKUP as OLD; [|done].
          rewrite lookup_app_l in EV; [|done].
          iSpecialize ("SeenMsgsAll2" $! _ _ _ EV EMO_LOOKUP).
          rewrite (SeenMsgs_mono _ esi2 emo2 emo2'); [done|done| |done|done|done].
          intros ? IN_LVIEW. eapply (event_in_esi_emo E2); [done|].
          by specialize (hwf_logview_closed _ EWF2 _ _ EV _ IN_LVIEW). }
      iPureIntro. des. split_and!; red.
      + (* LAST_MSG *) by rewrite last_cons fmap_last last_snoc.
      + (* TOP_SEEN_PUSH *) intros ?????. case (decide (e = length E2)) as [->|NE].
        * apply lookup_last_Some_2 in EV as ->. by simpl.
        * rewrite lookup_app_1_ne in EV; [|done].
          specialize (TOP_SEEN_PUSH _ _ _ EV PUSH). solve_lat.
      + (* SEEN_ALL *) by apply seen_logview_all_add.
      + (* HB_XO *) by apply hb_xo_add.
      + constructor. (* ESI_EMO_GOOD *)
        * by apply (esi_good_mono E2).
        * rewrite ->Forall_lookup in GEN_GOOD |- *. intros gen' [[e es] [on V']] GEN'.
          case (decide (gen' = length emo2)) as [->|NE].
          -- apply lookup_last_Some_2 in GEN' as [= -> -> -> ->].
             econstructor; [by rewrite lookup_app_1_eq|done..| |apply sublist_nil_l].
             (* EMPTYING_POP *)
             clear -XO_INTERP. split; [|done].
             intros [stk [INTERP PUSH]]%stack_interp_app_inv. exfalso.
             inv PUSH. rewrite -(app_nil_l [psId]) in ORD. apply app_inj_tail in ORD as [<- <-].
             apply lookup_last_Some_2 in EVENT as ->.
             inv RUN; done.
          -- rewrite lookup_app_1_ne in GEN'; [|done].
             specialize (GEN_GOOD _ _ GEN'). simpl in GEN_GOOD.
             by apply (emo_gen_good_mono E2).
        * (* XO_AGREE *)
          unfold emo2', E2'. rewrite !fmap_app /=.
          rewrite write_xo_snoc_ne; [|done]. by apply app_inv_tail_iff.
        * (* HB_EMO *) by apply hb_emo_add_ne.
        * (* LIN_PERM *) done.
      + (* XO_INTERP *) eapply (stack_interp_snoc _ psId _ _ (write_xo E2)).
        * by apply (stack_interp_mono_prefix E2).
        * by apply write_xo_snoc_ne.
        * apply lookup_app_1_eq.
        * by constructor.
    - done.
    - iExists _,_,_,esi2,emo2'. iFrame (LIN_PERM2') "MS E◯2' M◯2' PSV2'".
      iExists ζh2. iFrame "sn⊒2". done.
    - by iRight. }

  by iApply "HΦ".
Qed.

Lemma atom_try_push :
  try_push_spec' try_push StackLocal StackInv.
Proof.
  intros N DISJ s tid γg E0 M V v Posv. iIntros "#⊒V #Es" (Φ) "AU".

  wp_lam.
  (* allocate node *)
  wp_apply wp_new; [done..|].
  iIntros (n) "([H†|%] & n↦ & Hmn)"; [|done].

  (* initialize n's data as v *)
  rewrite own_loc_na_vec_cons own_loc_na_vec_singleton.
  iDestruct "n↦" as "[n↦ d↦]".
  wp_let. wp_op. wp_write.

  awp_apply (atom_try_push_internal with "⊒V Es [n↦] d↦"); [eauto..|].
  { rewrite shift_0. by iExists _. }

  iApply (aacc_aupd with "AU"); [done|].
  iIntros (E) "QI".
  iAaccIntro with "QI"; first by eauto with iFrame.
  iIntros (b V' E' psId ps Vps M') "(QI & ⊒V' & Local & CASE) !>". iRight.
  iExists b, V', E', psId, ps, Vps, M'. iFrame "QI ⊒V' Local".
  iDestruct "CASE" as "[(F & n↦ & d↦)|F]".
  - iDestruct "F" as %(-> & -> & ->). iSplit. { by iLeft. }
    iIntros "HΦ !> _". wp_if.
    (* cleaning up *)
    iDestruct "n↦" as (v') "n↦".
    wp_apply (wp_delete _ tid 2 _ [ v'; #v] with "[H† n↦ d↦]"); [done|done|..].
    { rewrite own_loc_na_vec_cons own_loc_na_vec_singleton.
      rewrite shift_0. iFrame "n↦ d↦". iLeft. by iFrame. }
    iIntros "_". wp_seq. by iApply "HΦ".
  - iSplit. { by iRight. } iDestruct "F" as %[-> F].
    iIntros "HΦ !> _". wp_if. by iApply "HΦ".
Qed.

Lemma atom_push_internal :
  ∀ N (DISJ: N ## histN) s tid γg E0 M V (v : Z) (Posv: 0 < v) (n : loc),
  (* E1 is a snapshot of the history, locally observed by M *)
  ⊒V -∗ StackLocal N γg s E0 M -∗
  (n >> next) ↦ - -∗ (n >> data) ↦ #v -∗
  (* PUBLIC PRE *)
  <<< ∀ E, ▷ StackInv γg s E >>>
    push_internal [ #s ; #n] @ tid; ↑N
  <<< ∃ V' E' (psId : event_id) ps Vpush M',
      (* PUBLIC POST *)
      ▷ StackInv γg s E' ∗
      ⊒V' ∗ @{V'} StackLocal N γg s E' M' ∗
      ⌜ Vpush.(dv_in) = V ∧ Vpush.(dv_comm) = V' ∧
        (* Vpush ⊑ V' ∧ *) (* << only works if push is also acquiring *)
        (* ps is a new push event with which G' strictly extends G *)
        is_push ps v ∧
        psId = length E ∧
        E' = E ++ [mkGraphEvent ps Vpush M'] ∧
        M' = {[psId]} ∪ M ⌝,
      (* RETURN VALUE AT COMMITTING POINT *)
      RET #☠, emp >>>
  .
Proof.
  intros. iIntros "#⊒V #Es n↦ Hd" (Φ) "AU".
  iLöb as "IH".

  wp_rec.
  awp_apply (atom_try_push_internal with "⊒V Es n↦ Hd"); [done..|].
  iApply (aacc_aupd with "AU"); [done|].
  iIntros (E) "QI".
  iAaccIntro with "QI"; first by eauto with iFrame.
  iIntros (b V' E' psId ps Vps M') "(QI & ⊒V' & Local & CASE) !>".
  iDestruct "CASE" as "[(F & n↦ & Hd)|F]".
  - iDestruct "F" as %(-> & -> & ->).
    iLeft. iFrame "QI". iIntros "AU !> _".
    wp_if. by iApply ("IH" with "n↦ Hd AU").
  - iRight.
    iExists V', E', psId, ps, Vps, M'.
    iFrame "QI ⊒V' Local". iDestruct "F" as %[-> F]. iSplit; [done|].
    iIntros "HΦ !> _". wp_if. by iApply "HΦ".
Qed.

Lemma atom_push :
  push_spec' push StackLocal StackInv.
Proof.
  intros N DISJ s tid γg E0 M V v Posv. iIntros "⊒V Es" (Φ) "AU".
  wp_lam.
  (* allocate node *)
  wp_apply wp_new; [done..|].
  iIntros (n) "([H†|%] & n↦ & Hmn)"; [|done].

  (* initialize n's data as v *)
  rewrite own_loc_na_vec_cons own_loc_na_vec_singleton.
  iDestruct "n↦" as "[n↦ Hd]".
  wp_let. wp_op. wp_write.

  wp_apply (atom_push_internal with "⊒V Es [n↦] Hd AU"); [eauto..|].
  rewrite shift_0. by iExists _.
Qed.

Lemma atom_try_pop :
  try_pop_spec' try_pop StackLocal StackInv.
Proof.
  intros N DISJ s tid γg E0 M V. iIntros "#⊒V #StackLocal" (Φ) "AU".
  iDestruct "StackLocal" as (?? ti esi0 emo0) "(MS & E◯0 & M◯0 & (%ζh0 & sn⊒0 & %SM0) & %LIN_PERM0)".

  wp_lam. wp_bind (!ᵃᶜ _)%E.

  (* Inv access #1 *)
  iMod "AU" as (E1) "[>StackInv Acc1]".
  iDestruct "StackInv" as (??? esi1 emo1 stk1 ont1 Vt1 Vi1)
    "(MS' & E●1 & M●1 & (%Vb1 & at↦1) & StackNodes1 & AllLinks1 & #SeenMsgsAll1 & %Props1)".
  simplify_meta with "MS' MS".
  (* get snapshot of E1 *)
  iDestruct (history_master_snap with "E●1") as "#E◯1".
  (* initial snapshot is included in E1 *)
  iPoseProof "E◯0" as "E◯0'". iDestruct "E◯0'" as "[_ PSV]".
  iDestruct (SeenLogview_closed with "PSV") as %SubME0.
  have SubMemo0 : set_Forall (λ e, ∃ eidx, lookup_emo esi0 emo0 eidx = Some e) M.
  { intros ??. eapply event_in_esi_emo; [done|]. by apply SubME0. }
  iCombine "sn⊒0 PSV" as "PSV'".
  iDestruct (view_at_intro_incl with "PSV' ⊒V") as (V0) "(⊒V0 & %LeVV0 & sn⊒0' & PSV0)".
  iClear "PSV'".
  iDestruct (history_master_snap_included with "E●1 E◯0") as %SubE01.
  iDestruct (emo_auth_lb_valid with "M●1 M◯0") as %(Subesi01 & Subne01 & Subess01).

  (* read *)
  wp_apply (AtomicSeen_acquire_read with "[$sn⊒0 $at↦1 $⊒V0]"); first solve_ndisj.
  iIntros (th1 vh1 Vh1 V1 ζh1) "(Subζ & #⊒V1 & #sn⊒1 & at↦1')".
  iDestruct "Subζ" as %([Subemo0ζh1 Subζh1emo1] & Eqth1 & MAXth1 & LeV0Vh1V1).
  have {LeV0Vh1V1}[LeV0V1 LeVh1V1] : V0 ⊑ V1 ∧ Vh1 ⊑ V1 by clear -LeV0Vh1V1; solve_lat.

  (* check what we just read *)
  move: (lookup_weaken _ _ _ _ Eqth1 Subζh1emo1) => /toHeadHist_lookup_Some.
  intros (Letith1 & on1 & -> & Eqemo1).

  have Injemo1 : emo_inj esi1 emo1.
  { apply (lin_perm_emo_inj E1). des. by destruct ESI_EMO_GOOD. }

  destruct on1 as [n1|]; last first.
  { (* EMPTY POP. The commit point is the read. *)
    iDestruct (history_master_wf with "E●1") as %EWF1.
    have SubM1 : set_in_bound M E1 by apply (set_in_bound_mono _ E0).

    have LeVV1: V ⊑ V1 by solve_lat.
    have bLeVV1 : bool_decide (V ⊑ V1) by eapply bool_decide_unpack; eauto.
    set Vpp := mkDView V V1 ∅ bLeVV1.

    set ppId := length E1.
    set M' := {[ppId]} ∪ M.
    set egV' := mkGraphEvent EmpPop Vpp M'.
    set E1' := E1 ++ [egV'].
    set stk1' := stk1.
    have NInpp : ppId ∉ M. { move => /SubM1 /lookup_lt_is_Some. lia. }
    have SubE11' : E1 ⊑ E1' by apply prefix_app_r.

    iMod (history_master_update _ _ E1' with "E●1") as "[E●1' #E◯1']".
    { by apply prefix_app_r. }
    { by apply (history_wf_add E1 egV' M). }

    iAssert (@{Vpp.(dv_comm)} SeenLogview E1' M')%I with "[]" as "#PSV1'".
    { rewrite -SeenLogview_insert'. iSplitL; [|done].
      iApply (view_at_mono with "PSV0"); [done|]. by apply SeenLogview_map_mono. }
    iAssert ⌜seen_logview E1' M' Vpp.(dv_comm)⌝%I with "[]" as %PSV1'.
    { rewrite view_at_eq /view_at_def /=. iDestruct "PSV1'" as %?. done. }

    set gen := (Pos.to_nat th1 - Pos.to_nat ti)%nat.
    have MAXgen : ∀ e0 eidx0, e0 ∈ M → lookup_emo esi1 emo1 eidx0 = Some e0 → (gen_of eidx0 ≤ gen)%nat.
    { intros ?? SEEN EMO_LOOKUP.
      apply (seen_msgs_mono _ esi1 _ emo1 _ ζh0) in SM0; [|done..|by etrans|done].
      specialize (SM0 e0 eidx0 SEEN EMO_LOOKUP).
      specialize (MAXth1 _ SM0). clear-MAXth1.
      rewrite /sqsubseteq /lat_sqsubseteq /= in MAXth1. lia. }

    (* pure props of StackInv common to both cases *)
    have TOP_SEEN_PUSH1' : top_view_released E1' Vt1.
    { des. intros ?????. case (decide (e = length E1)) as [->|NE].
      - apply lookup_last_Some_2 in EV as ->. by simpl.
      - rewrite lookup_app_1_ne in EV; [|done].
        specialize (TOP_SEEN_PUSH _ _ _ EV PUSH). solve_lat. }
    have SEEN_ALL1' : seen_logview_all E1'.
    { des. by apply seen_logview_all_add. }
    have HB_XO1' : hb_ord E1' (seq 0 (length E1')).
    { des. by apply hb_xo_add. }
    have XO_INTERP1' : stack_interp E1' (write_xo E1') [] stk1'.
    { des. apply (stack_interp_mono_prefix E1); [done|by rewrite write_xo_snoc_e]. }

    case Egen: gen => [|gen'].
    - subst gen. rewrite ->Egen in *.
      des. destruct ESI_EMO_GOOD.
      set esi1' := esi1 ++ [ppId].
      have Subesi11' : esi1 ⊑ esi1' by apply prefix_app_r.
      have Injemo1' : emo_inj esi1' emo1 by apply (emo_inj_esi_insert E1).
      have SM1' : seen_msgs esi1' emo1 ζh1 ti M'.
      { intros ????. des.
        case (decide (eidx = (emo_e O (length esi1)))) as [->|NEeidx].
        - subst esi1'. simpl in *.
          apply lookup_last_Some_2 in EMO_LOOKUP as ->.
          rewrite (_ : Pos.of_nat (Pos.to_nat ti + 0) = th1); [done|lia].
        - case (decide (e = ppId)) as [->|NEe].
          { exfalso. apply lookup_emo_old_esi in EMO_LOOKUP; [|done].
            eapply emo_ids_le_new in EMO_LOOKUP; [|done]. subst ppId. lia. }
          apply (seen_msgs_mono _ esi1' _ emo1 _ ζh1) in SM0; [|done|done| |done|done|by etrans].
          + exploit (SM0 e eidx); [|done..]. set_solver +SEEN NEe.
          + by trans esi1. }
      have LIN_PERM1' : lin_of_emo esi1' emo1 ≡ₚ seq 0 (length E1').
      { rewrite app_length. by apply lin_perm_add_esi. }

      iMod (emo_auth_own_update_esi ppId with "M●1") as "[M●1' #M◯1']".

      (* commit *)
      iDestruct "Acc1" as "[_ Commit1]".
      iMod ("Commit1" $! EMPTY V1 E1' dummy_eid ppId dummy_sevt EmpPop Vpp M' with "[-]") as "HΦ"; last first.
      { iModIntro. wp_let. wp_op. wp_if. by iApply "HΦ". }

      iFrame "⊒V1". rewrite (bi.sep_assoc (▷ StackInv _ _ _)%I).
      iSplitL; last iSplitL; [|done|by iRight; iLeft].

      iSplitL.
      + iExists _,_,_. iExists esi1',emo1,stk1',ont1,Vt1,Vi1.
        iFrame "∗". iSplitL; last iSplitL; first by eauto with iFrame.
        { (* SeenMsgsAll γh s E1' esi1' emo1 ti. *)
          iNext. iIntros (???? EMO_LOOKUP).
          case (decide (eidx = emo_e O (length esi1))) as [->|NEeidx].
          - simpl in EMO_LOOKUP.
            apply lookup_last_Some_2 in EMO_LOOKUP as ->.
            apply lookup_last_Some_2 in EV as ->. subst egV'. simpl.
            iExists ζh1. iFrame (SM1') "sn⊒1".
          - apply lookup_emo_old_esi in EMO_LOOKUP; [|done].
            apply (emo_ids_le_new E1) in EMO_LOOKUP as OLD; [|done].
            rewrite lookup_app_l in EV; [|done].
            iSpecialize ("SeenMsgsAll1" $! _ _ _ EV EMO_LOOKUP).
            rewrite (SeenMsgs_mono _ esi1' emo1 emo1); [done|done| |done|done|done].
            (* set_Forall (λ e0, ∃ eidx0, lookup_emo esi1 emo1 eidx0 = Some e0) eV.(ge_lview) *)
            intros ? IN_LVIEW. eapply (event_in_esi_emo E1); [done|].
            by specialize (hwf_logview_closed _ EWF1 _ _ EV _ IN_LVIEW). }
        iPureIntro. split_and!; red.
        * (* LAST_MSG *) done.
        * (* TOP_SEEN_PUSH *) done.
        * (* SEEN_ALL *) done.
        * (* HB_XO *) done.
        * (* ESI_EMO_GOOD *) constructor.
          -- apply (esi_good_mono _ E1') in ESI_GOOD as ESI_GOOD'; [|done].
             destruct ESI_GOOD,ESI_GOOD'. constructor.
             ++ apply Forall_app. split; [done|]. simpl. apply Forall_singleton.
                eexists. split; [apply lookup_app_1_eq|done].
             ++ rewrite app_length seq_app /=. by apply sublist_app.
          -- apply (Forall_impl _ _ _ GEN_GOOD). intros [[? ?] [? ?]] GOOD.
             by apply (emo_gen_good_mono _ _ _ _ _ _ GOOD).
          -- (* XO_AGREE *) by rewrite write_xo_snoc_e.
          -- unfold hb_emo. intros.
             set eidx := emo_e O (length esi1).
             case (decide (eidx = eidx1)) as [<-|NE1]; case (decide (eidx = eidx2)) as [<-|NE2].
             ++ (* this ∈ this.lview *)
                by apply emo_idx_le_e_e_2.
             ++ (* this ∈ old.lview: old can't contain this *)
                exfalso.
                apply lookup_last_Some_2 in EMO_eidx1 as ->.
                eapply lookup_emo_old_esi in EMO_eidx2; [|done..].
                exploit (emo_ids_le_new E1 esi1 emo1 eidx2 e2); [done..|]. intro.
                rewrite lookup_app_l in EV2; [|done].
                move: (hwf_logview_closed _ EWF1 _ _ EV2 _ IN_LVIEW) => /lookup_lt_is_Some.
                lia.
             ++ (* old ∈ this.lview *) simplify_list_eq.
                apply lookup_last_Some_2 in EMO_eidx2 as ->.
                apply lookup_last_Some_2 in EV2 as ->.
                apply lookup_emo_old_esi in EMO_eidx1; [|done].
                hexploit (MAXgen e1 eidx1).
                ** suff NEe : e1 ≠ ppId by set_solver +IN_LVIEW NEe.
                   exploit (emo_ids_le_new E1 esi1 emo1 eidx1 e1); [done|done|lia].
                ** done.
                ** destruct eidx1 as [[|gen1'] i1'|gen1']; simpl; intros; [|lia..].
                   apply lookup_lt_Some in EMO_eidx1. apply emo_idx_le_e_e_2. lia.
             ++ (* old ∈ old.lview *)
                eapply lookup_emo_old_esi in EMO_eidx1,EMO_eidx2; [|done..].
                exploit (emo_ids_le_new E1 esi1 emo1 eidx2 e2); [done|done|]. intros.
                rewrite lookup_app_l in EV2; [|done].
                by eapply (HB_EMO eidx1 eidx2).
          -- (* LIN_PERM *) done.
        * (* XO_INTERP *) done.
      + iExists _,_,_,esi1',emo1. iFrame (LIN_PERM1') "MS E◯1' M◯1' PSV1'".
        iExists ζh1. iFrame (SM1') "sn⊒1".
    - subst gen. rewrite ->Egen in *.
      des. destruct ESI_EMO_GOOD.
      have [o [es GEN]] : ∃ o es, emo1 !! gen' = Some (o, es, (None, Vh1)).
      { clear -Eqemo1. apply list_lookup_fmap_inv in Eqemo1.
        destruct Eqemo1 as ([[o es] [? ?]] & [= <- <-] & ?).
        by exists o,es. }
      set emo1' := emo_insert_e emo1 gen' ppId.
      have GEN' : emo1' !! gen' = Some (o, es ++ [ppId], (None, Vh1)).
      { clear -GEN. subst emo1'. rewrite /emo_insert_e.
        rewrite list_lookup_alter. rewrite GEN. done. }
      have GEN'12 : emo1'.*1.*2 !! gen' = Some (es ++ [ppId]).
      { apply (f_equal (fmap fst)), (f_equal (fmap snd)) in GEN'.
        rewrite -!list_lookup_fmap // in GEN'. }
      have GEN12 : emo1.*1.*2 !! gen' = Some es.
      { apply (f_equal (fmap fst)), (f_equal (fmap snd)) in GEN.
        rewrite -!list_lookup_fmap // in GEN. }
      have Injemo1' : emo_inj esi1 emo1' by eapply (emo_inj_emo_insert_e E1).
      have Subne11' : emo1.*1.*1 ⊑ emo1'.*1.*1 by rewrite emo_insert_e_11.
      have Subess11' : emo1.*1.*2 `prefixes_of` emo1'.*1.*2 by apply emo_insert_e_12_prefixes.
      have SM1' : seen_msgs esi1 emo1' ζh1 ti M'.
      { intros ????.
        case (decide (eidx = (emo_e (S gen') (length es)))) as [->|NEeidx].
        - subst emo1'. rewrite /= GEN'12 /= in EMO_LOOKUP.
          apply lookup_last_Some_2 in EMO_LOOKUP as ->. simpl.
          rewrite (_ : Pos.of_nat (Pos.to_nat ti + S gen') = th1); [done|lia].
        - case (decide (e = ppId)) as [->|NEe].
          { exfalso. eapply lookup_emo_old_emo_e in EMO_LOOKUP; [|done..].
            eapply emo_ids_le_new in EMO_LOOKUP; [|done]. subst ppId. lia. }
          apply (seen_msgs_mono _ esi1 _ emo1' _ ζh1) in SM0; [|done|done|done|by etrans..].
          exploit (SM0 e eidx); [|done..]. set_solver +SEEN NEe. }
      have LIN_PERM1' : lin_of_emo esi1 emo1' ≡ₚ seq 0 (length E1').
      { rewrite app_length. by eapply lin_perm_add_emo_e. }

      iMod (emo_auth_own_update_emo_e gen' ppId with "M●1") as "[M●1' #M◯1']".

      (* commit *)
      iDestruct "Acc1" as "[_ Commit1]".
      iMod ("Commit1" $! EMPTY V1 E1' dummy_eid ppId dummy_sevt EmpPop Vpp M' with "[-]") as "HΦ"; last first.
      { iModIntro. wp_let. wp_op. wp_if. by iApply "HΦ". }

      iFrame "⊒V1". rewrite (bi.sep_assoc (▷ StackInv _ _ _)%I).
      iSplitL; last iSplitL; [|done|by iRight; iLeft].

      iSplitL.
      + iExists _,_,_. iExists esi1,emo1',stk1',ont1,Vt1,Vi1.
        rewrite (_ : emo1.*2 = emo1'.*2); last by rewrite emo_insert_e_2.
        iFrame "∗". iSplitL; last iSplitL; first by eauto with iFrame.
        { (* SeenMsgsAll γh s E1' esi1 emo1' ti *)
          iNext. iIntros (???? EMO_LOOKUP).
          case (decide (eidx = emo_e (S gen') (length es))) as [->|NEeidx].
          - simpl in EMO_LOOKUP. rewrite GEN'12 /= in EMO_LOOKUP.
            apply lookup_last_Some_2 in EMO_LOOKUP as ->.
            apply lookup_last_Some_2 in EV as ->. subst egV'. simpl.
            iExists ζh1. iFrame (SM1') "sn⊒1".
          - eapply lookup_emo_old_emo_e in EMO_LOOKUP; [|done..].
            apply (emo_ids_le_new E1) in EMO_LOOKUP as OLD; [|done].
            rewrite lookup_app_l in EV; [|done].
            iSpecialize ("SeenMsgsAll1" $! _ _ _ EV EMO_LOOKUP).
            rewrite (SeenMsgs_mono _ esi1 emo1 emo1'); [done|done| |done|done|done].
            intros ? IN_LVIEW. eapply (event_in_esi_emo E1); [done|].
            by specialize (hwf_logview_closed _ EWF1 _ _ EV _ IN_LVIEW). }
        iPureIntro. split_and!; red.
        * (* LAST_MSG *) by rewrite emo_insert_e_2.
        * (* TOP_SEEN_PUSH *) done.
        * (* SEEN_ALL *) done.
        * (* HB_XO *) done.
        * (* ESI_EMO_GOOD *)
          constructor.
          -- by apply (esi_good_mono E1).
          -- rewrite ->Forall_lookup in GEN_GOOD |- *. intros gen0' [[e0 es0] [on0 Vn0]] GEN0'.
             case (decide (gen0' = gen')) as [->|NE].
             ++ rewrite GEN' in GEN0'. injection GEN0' as [= <- <- <- <-].
                specialize (GEN_GOOD _ _ GEN). simpl in GEN_GOOD.
                apply (emo_gen_good_mono _ E1') in GEN_GOOD as GEN_GOOD'; [|done].
                destruct GEN_GOOD, GEN_GOOD'.
                apply lookup_lt_Some in EV as LTo.
                econstructor; [done|done|done|..].
                ** apply Forall_app. split; [done|]. apply Forall_singleton. unnw.
                   eexists. split_and!; [by apply lookup_app_1_eq|done|lia].
                ** intros _. unfold NW.
                   destruct EMPTYING_POP as [_ INTERP_EMPTY]. specialize (INTERP_EMPTY eq_refl).
                   rewrite -(write_xo_stable E1); [|lia|done].
                   by apply (stack_interp_mono_prefix E1).
                ** done.
                ** rewrite app_length seq_app /=. by apply sublist_app.
             ++ rewrite /emo_insert_e list_lookup_alter_ne in GEN0'; [|done].
                specialize (GEN_GOOD _ _ GEN0'). simpl in GEN_GOOD.
                by apply (emo_gen_good_mono E1).
          -- (* XO_AGREE *) rewrite emo_insert_e_11. by rewrite write_xo_snoc_e.
          -- unfold hb_emo. intros.
             set eidx := emo_e (S gen') (length es).
             case (decide (eidx = eidx1)) as [<-|NE1]; case (decide (eidx = eidx2)) as [<-|NE2].
             ++ (* this ∈ this.lview *)
                by apply emo_idx_le_e_e_2.
             ++ (* this ∈ old.lview: old can't contain this *)
                exfalso.
                apply bind_Some in EMO_eidx1 as (es' & GEN'' & ES_i'). simplify_eq.
                apply lookup_last_Some_2 in ES_i' as ->.
                eapply lookup_emo_old_emo_e in EMO_eidx2; [|done..].
                exploit (emo_ids_le_new E1 esi1 emo1 eidx2 e2); [done..|]. intro.
                rewrite lookup_app_l in EV2; [|done].
                move: (hwf_logview_closed _ EWF1 _ _ EV2 _ IN_LVIEW) => /lookup_lt_is_Some.
                lia.
             ++ (* old ∈ this.lview *)
                apply bind_Some in EMO_eidx2 as (es' & GEN'' & ES_i'). simplify_eq.
                apply lookup_last_Some_2 in ES_i' as ->.
                apply lookup_last_Some_2 in EV2 as ->.
                eapply lookup_emo_old_emo_e in EMO_eidx1; [|done|done].
                hexploit (MAXgen e1 eidx1).
                ** suff NEe : e1 ≠ ppId by set_solver +IN_LVIEW NEe.
                   exploit (emo_ids_le_new E1 esi1 emo1 eidx1 e1); [done|done|lia].
                ** done.
                ** destruct eidx1 as [[|gen1'] i1'|gen1']; simpl; intros.
                   --- apply lookup_lt_Some in EMO_eidx1. apply emo_idx_le_e_e_1. lia.
                   --- case (decide (gen1' = gen')) as [->|NEgen].
                       +++ apply bind_Some in EMO_eidx1 as (? & ? & ES_i1'). simplify_eq.
                           apply lookup_lt_Some in ES_i1'. apply emo_idx_le_e_e_2. lia.
                       +++ apply emo_idx_le_e_e_1. lia.
                   --- by apply emo_idx_le_ne_e.
             ++ (* old ∈ old.lview *)
                eapply lookup_emo_old_emo_e in EMO_eidx1,EMO_eidx2; [|done..].
                exploit (emo_ids_le_new E1 esi1 emo1 eidx2 e2); [done..|]. intros.
                rewrite lookup_app_l in EV2; [|done]. by eapply (HB_EMO eidx1 eidx2).
          -- (* LIN_PERM *) done.
        * (* XO_INTERP *) done.
      + iExists _,_,_,esi1,emo1'. iFrame (LIN_PERM1') "MS E◯1' M◯1' PSV1'".
        iExists ζh1. iFrame (SM1') "sn⊒1". }

  (* Possibly non-empty, do not commit yet. *)
  (* Leak a fraction of `n1 >> next` to read after closing the inv. *)
  rewrite (AllLinks_node_next_access _ n1 Vh1); last first.
  { move: Eqemo1.
    case E: (Pos.to_nat th1 - Pos.to_nat ti)%nat; simpl; intros; simplify_eq.
    by eapply elem_of_list_lookup_2. }
  iDestruct "AllLinks1" as "[AllLinks1 n1↦]".

  (* Close Inv #1 *)
  iDestruct "Acc1" as "[Abort1 _]".
  iMod ("Abort1" with "[-n1↦]") as "AU".
  { iExists _,_,_. iExists esi1,emo1,stk1,ont1,Vt1,Vi1.
    iNext. iFrame "∗"; eauto with iFrame. } clear Props1.

  iModIntro. simpl. wp_let. wp_op. wp_if. wp_op.

  (* read `n1 >> next` non-atomically *)
  iDestruct "n1↦" as (q onn) "n1↦".
  iDestruct (view_at_elim with "[] n1↦") as "n1↦".
  { iApply (monPred_in_mono with "⊒V1"). simpl. solve_lat. }
  wp_read. wp_let.

  wp_bind (casᵃᶜ(_,_,_))%E. clear Vb1.
  (* Inv access #2 *)
  iMod "AU" as (E2) "[>StackInv [_ Commit2]]".
  iDestruct "StackInv" as (??? esi2 emo2 stk2 ont2 Vt2 Vi2)
    "(MS' & E●2 & M●2 & (%Vb2 & at↦2) & StackNodes2 & AllLinks2 & #SeenMsgsAll2 & %Props2)".
  simplify_meta with "MS' MS".

  have Injemo2 : emo_inj esi2 emo2.
  { apply (lin_perm_emo_inj E2). des. by destruct ESI_EMO_GOOD. }

  iDestruct (history_master_wf with "E●2") as %EWF2.
  iDestruct (history_master_snap_included with "E●2 E◯1") as %SubE12.
  have SubE02 : E0 ⊑ E2 by etrans.
  have SubME2: set_in_bound M E2 by apply (set_in_bound_mono _ E0).
  iDestruct (emo_auth_lb_valid with "M●2 M◯0") as %(Subesi02 & Subne02 & Subess02).
  clear Subesi01 Subne01 Subess01.

  iMod (rel_objectively_intro (⊒∅) tid with "[]") as "⊒∅".
  { iApply objective_objectively. iApply monPred_in_bot. }

  iDestruct (view_at_elim with "⊒V1 sn⊒1") as "sn⊒1'".
  set Pr : vProp := ((n1 >> next) ↦{q} #(oloc_to_lit onn) ∗ AllLinks emo2.*2)%I.
  wp_apply (AtomicSeen_CON_CAS_live_loc _ _ _ _ _ _ _ n1 #(oloc_to_lit onn) _ ∅
              with "[$sn⊒1' $at↦2 $⊒V1 ⊒∅]"); [done|done|done|solve_ndisj|..]; [|done|].
  { intros t v NE. rewrite lookup_fmap_Some'.
    intros ([] & <- & ?).
    by eapply (toHeadHist_lookup_Some_is_comparable_nullable_loc _ _ _ _ _ (Some n1)). }

  iIntros (b2 tr2 vr2 Vr2 V2 ζh2 ζn2) "(F & #⊒V2 & #sn⊒2 & at↦2' & CASE)".
  iDestruct "F" as %([Subζh1ζh2 Subζh2ζn2] & Eqtr2 & MAXtr2 & LeV1V2). clear Pr.

  have LeVV2 : V ⊑ V2. { clear -LeVV0 LeV0V1 LeV1V2. solve_lat. }
  have bLeVV2 : bool_decide (V ⊑ V2) by eapply bool_decide_unpack; eauto.

  iDestruct "CASE" as "[[(%&%&%) HV2]|([%%] & CASE)]".
  { (* FAIL_RACE case *)
    (* COMMIT with no change *)
    subst b2 ζn2.
    (* take a snapshot *)
    iDestruct (history_master_snap with "E●2") as "#E◯2".
    iDestruct (emo_lb_own_get with "M●2") as "#M◯2".

    set Vpp := mkDView V V2 V2 bLeVV2.

    iMod ("Commit2" $! FAIL_RACE V2 E2 dummy_eid dummy_eid
                      dummy_sevt dummy_sevt Vpp M with "[-]") as "HΦ".
    { iSplitL; last iSplitL; last iSplitL.
      - iExists _,_,_. iExists esi2,emo2,stk2,ont2,Vt2,Vi2. eauto 10 with iFrame.
      - done.
      - iExists _,_,_,esi2,emo2. iFrame "MS M◯2". iSplit; last iSplit.
        + (* history_snap γg E2 M *)
          iDestruct "E◯2" as "[$ ?]".
          iApply (view_at_mono with "PSV0"); [solve_lat|].
          by apply SeenLogview_map_mono.
        + iExists ζh2. iFrame "#". iPureIntro. (* seen_msgs esi2 emo2 ζh2 ti M *)
          apply (seen_msgs_mono esi0 _ emo0 _ ζh0); [done..|by etrans|done].
        + des. by destruct ESI_EMO_GOOD.
      - iSplit; first done. by iLeft. }
    iModIntro. wp_if. by iApply "HΦ". }

  subst b2 vr2.
  iDestruct "CASE" as (Vw2 (FRt & Eqζn2 & Eqt2 & LeVr2Vw2 & _)) "[_ %LeV2V2]".
  have LeVr2V2: Vr2 ⊑ V2 by etrans.

  (* The top message is what the CAS read *)
  have Eqtr2': toHeadHist ti ((None, Vi2) :: emo2.*2) !! tr2 = Some (#n1, Vr2).
  { eapply lookup_weaken in Eqtr2; [|apply Subζh2ζn2].
    rewrite Eqζn2 lookup_insert_ne in Eqtr2; [done|lia]. }

  apply toHeadHist_lookup_Some in Eqtr2' as (Letitr2 & on2 & Eqon2 & Eqn2).
  assert (on2 = Some n1) as ->.
  { clear -Eqon2. destruct on2; by simplify_eq. } clear Eqon2.

  assert (EqL: (Pos.to_nat tr2 - Pos.to_nat ti)%nat = length emo2.*2).
  { assert (LtL := lookup_lt_Some _ _ _ Eqn2). clear -FRt Letitr2 LtL.
    apply toHeadHist_lookup_None in FRt as [?|Let']; first (exfalso; lia).
    apply : (anti_symm (le)).
    - clear -LtL. rewrite cons_length /= in LtL. lia.
    - clear LtL. rewrite cons_length /= /pos_add_nat in Let'; lia. }
  rewrite EqL in Eqn2.

  assert (ont2 = Some n1 ∧ Vt2 = Vr2) as [-> ->].
  { des. rewrite lookup_last_cons LAST_MSG in Eqn2. by injection Eqn2. }

  assert (∃ stk2' node, stk2 = node :: stk2') as (stk2' & node & ->).
  { des. destruct ESI_EMO_GOOD.
    (* Get the info about the last non-empty event whose msg we read. *)
    have XO_INTERP' := XO_INTERP. inv XO_INTERP'.
    { exfalso. rewrite -{}H0 in XO_AGREE. do 2 apply fmap_nil_inv in XO_AGREE.
      subst emo2. simpl in Eqn2. done. }
    have {}LAST_MSG : last emo2.*2 = Some (Some n1, Vr2).
    { rewrite last_cons in LAST_MSG. by case_match. }
    have LAST : length emo2 = length (write_xo E2).
    { apply (f_equal length) in XO_AGREE. by rewrite !fmap_length in XO_AGREE. }
    have [es GEN] : ∃ es, emo2 !! (Nat.pred (length emo2)) = Some (e, es, (Some n1, Vr2)).
    { clear -LAST_MSG LAST XO_AGREE ORD EVENT.
      rewrite last_lookup fmap_length in LAST_MSG.
      apply list_lookup_fmap_inv in LAST_MSG as ([[? es] [? ?]] & [= <- <-] & LAST_MSG).
      rewrite ORD in XO_AGREE.
      apply (f_equal ((!!) (Nat.pred (length emo2)))) in XO_AGREE.
      rewrite !list_lookup_fmap LAST_MSG /= in XO_AGREE.
      apply (f_equal length) in ORD. rewrite -LAST in ORD. rewrite ORD in XO_AGREE.
      rewrite app_length /= -Nat.add_pred_r /= in XO_AGREE; [|lia].
      rewrite Nat.add_0_r lookup_app_1_eq in XO_AGREE. injection XO_AGREE as ->.
      by exists es. }
    rewrite ->Forall_lookup in GEN_GOOD. destruct (GEN_GOOD _ _ GEN).

    inv RUN.
    + (* The last non-emtpy event was push *) by eexists _,_.
    + (* The last non-empty event was pop
      - If the stack is still non-empty after the last pop: use that stack.
      - If the stack become empty after the last pop: The pop that makes the
        stack empty writes null, but the msg we read is not null; contradiction *)
      case Estk2: stk2; last by eexists _,_. exfalso. subst stk2.
      apply filter_seq_inv_snoc in ORD as Hord'. subst ord'.
      rewrite ORD in XO_INTERP. by apply EMPTYING_POP in XO_INTERP.
    + (* The last (non-empty) event was empty pop: contradiction. *)
      exfalso. clear -ORD EVENT EMPPOP. assert (e ∈ ord' ++ [e]) by set_solver-.
      rewrite <- ORD in H. apply elem_of_list_filter in H as [H _].
      by apply H in EVENT. }

  (* Get the node to pop. *)
  rewrite !fmap_cons /StackNodes.
  iDestruct "StackNodes2" as (onn') "[Node StackNodes2']". fold StackNodes.
  iDestruct "Node" as "[n↦ d↦]".

  iAssert ⌜stk2' = [] ↔ onn' = None⌝%I with "[StackNodes2']" as %EMPTYING_WRITE.
  { unfold iff. iSplit.
    - iIntros (->). simpl. case_match; [|done]. by iDestruct "StackNodes2'" as %?.
    - iIntros (->). case Estk2': (stk2'.*1.*1.*2).
      + do 3 apply fmap_nil_inv in Estk2'. done.
      + by iDestruct "StackNodes2'" as %?. }

  iAssert (⊒Vr2)%I with "[]" as "#⊒Vr2". { by iApply (monPred_in_mono with  "⊒V2"). }

  iAssert (⌜onn' = onn⌝)%I with "[n↦ n1↦]" as %->.
  { clear. iDestruct (view_at_elim with "⊒Vr2 n↦") as (?) "n↦".
    by iDestruct (own_loc_na_agree with "n1↦ n↦") as %[=[=->%oloc_to_lit_inj]]. }

  set psId := node.1.1.1.
  set ppId := length E2.
  set M' := M ∪ ({[ppId]} ∪ node.2).
  set Vpp := mkDView V V2 Vw2 bLeVV2.
  set v := node.1.1.2.
  set pp := mkGraphEvent (Pop v) Vpp M'.
  set E2' := E2 ++ [pp].
  set emo2' := emo2 ++ [((ppId, []), (onn, Vw2))].

  have SubE22' : E2 ⊑ E2' by apply prefix_app_r.
  have Injemo2' : emo_inj esi2 emo2' by des; by apply (emo_inj_emo_insert_ne E2).
  have Subne22' : emo2.*1.*1 ⊑ emo2'.*1.*1.
  { subst emo2'. rewrite !fmap_app /=. by apply prefix_app_r. }
  have Subess22' : emo2.*1.*2 `prefixes_of` emo2'.*1.*2.
  { apply emo_insert_ne_12_prefixes. }
  exploit (stack_node_pushed_inv E2 node (write_xo E2) [] stk2').
  { des. done. }
  { by eapply NoDup_filter,ord_nodup. }
  unfold NW. intros (pseV & IDps & EVps & VALps & NZps & LVIEWps & VIEWps).
  have SubAcqRel : pseV.(ge_view).(dv_comm) ⊑ V2.
  { des. specialize (TOP_SEEN_PUSH _ _ _ EVps VALps). by trans Vr2. }

  exploit (event_in_esi_emo E2 esi2 emo2 psId); [by des; destruct ESI_EMO_GOOD|done|].
  intros [pseidx EMO_LOOKUPps].

  have RUNpp : stack_run ppId pp (node :: stk2') stk2'.
  { des. destruct node as [[[? ?] ?] ?].
    subst pp Vpp. simplify_eq/=. (* NOTE: these are necessary for unification *)
    eapply stack_run_Pop; simpl; [done..|].
    specialize (hwf_logview_event _ EWF2 _ _ EVps). set_solver-. }

  (* Leak the new head node (if any) *)
  rewrite (_ : ∀ on vs, StackNodes on vs -∗ StackNodes on vs ∗
    if on is Some n
    then ∃ q onn, (n >> next) ↦{q} #(oloc_to_lit onn)
    else emp); last first.
  { clear. iIntros (??) "StackNodes". rewrite {1}/StackNodes.
    case on as [n|]; simpl; last by iFrame.
    case vs as [|v vs']; simpl; first done.
    iDestruct "StackNodes" as (?) "[Node StackNodes']".
    iDestruct "Node" as "[(% & n↦1 & n↦2) d↦]".
    iSplitR "n↦1"; eauto with iFrame. }
  iDestruct "StackNodes2'" as "[StackNodes2' onn↦]".
  iAssert (AllLinks emo2'.*2)%I with "[onn↦ AllLinks2]" as "AllLinks2'".
  { subst emo2'. rewrite fmap_app /=. rewrite /AllLinks big_sepL_app big_sepL_singleton /=.
    iFrame "AllLinks2". case onn as [nn|]; last done.
    iDestruct "onn↦" as (??) "onn↦". iExists _,_. by iFrame. }

  iAssert (@{Vpp.(dv_comm)} SeenLogview E2' M')%I with "[]" as "#PSV2'".
  { rewrite -SeenLogview_union' -SeenLogview_insert'.
    iSplitL; last iSplitL; [..|done].
    - iApply (view_at_mono with "PSV0").
      + by trans V1.
      + apply SeenLogview_map_mono; [..|done]. by trans E2.
    - unfold SeenLogview. simpl. rewrite view_at_eq /view_at_def /=. iPureIntro.
      des. move: (SEEN_ALL _ _ EVps). rewrite LVIEWps.
      by apply seen_logview_view_mono. }
  iAssert ⌜seen_logview E2' M' Vpp.(dv_comm)⌝%I with "[]" as %PSV2'.
  { rewrite view_at_eq /view_at_def /=. iDestruct "PSV2'" as %?. done. }

  iDestruct ("SeenMsgsAll2" $! psId _ _ EVps EMO_LOOKUPps) as (ζhps) "[sn⊒ps %SMps]".
  iDestruct (AtomicSeen_union_equiv with "sn⊒2 sn⊒ps") as %Eqζ.

  have SM2' : seen_msgs esi2 emo2' (ζh2 ∪ ζhps) ti M'.
  { des. destruct ESI_EMO_GOOD.
    have ? : seen_msgs esi2 emo2' (ζh2 ∪ ζhps) ti M.
    { move: SM0. apply seen_msgs_mono; [done|done|done|by etrans|by etrans|].
      apply map_union_subseteq_l'. by etrans. }
    have SMps' : seen_msgs esi2 emo2' (ζh2 ∪ ζhps) ti pseV.(ge_lview).
    { move: SMps. apply seen_msgs_mono; [done| |done|done|done|].
      - intros ? IN_LVIEW. eapply (event_in_esi_emo E2); [done|].
        by specialize (hwf_logview_closed _ EWF2 _ _ EVps _ IN_LVIEW).
      - rewrite Eqζ. apply map_union_subseteq_l. }
    rewrite LVIEWps in SMps'.
    apply seen_msgs_union; [done|]. apply seen_msgs_union; [|done].
    intros ?? ->%elem_of_singleton ?.
    exploit (lookup_emo_new_ne E2 esi2 emo2); [done|done|].
    intros ->. simpl.
    assert (Pos.of_nat (Pos.to_nat ti + S (length emo2)) = tr2 + 1)%positive as ->.
    { rewrite fmap_length in EqL. lia. }
    apply lookup_union_is_Some. by left. }

  iAssert (@{V2} s sn⊒{γh} (ζh2 ∪ ζhps))%I as "sn⊒2'".
  { rewrite -AtomicSeen_join'. iFrame "sn⊒2".
    des. specialize (TOP_SEEN_PUSH _ _ _ EVps VALps). iFrame "sn⊒ps". }

  iAssert (@{V2} SeenMsgs γh s esi2 emo2' ti M')%I with "[at↦2']" as "#SM2'".
  { iExists (ζh2 ∪ ζhps). iFrame (SM2') "sn⊒2'". }

  have LIN_PERM2' : lin_of_emo esi2 emo2' ≡ₚ seq 0 (length E2').
  { rewrite app_length. apply lin_perm_add_emo_ne. des. by destruct ESI_EMO_GOOD. }

  iMod (history_master_update _ _ E2' with "E●2") as "[E●2' #E◯2']".
  { done. }
  { apply (history_wf_add_sync E2 _ _ pp M EWF2 EVps); [done|].
    subst pp. simpl. rewrite LVIEWps. done. }
  iMod (emo_auth_own_update_emo_ne ppId with "M●2") as "[M●2' #M◯2']".

  iMod ("Commit2" $! v V2 E2' psId ppId (Push v) (Pop v) Vpp M'
        with "[- d↦]") as "HΦ".
  { des. destruct ESI_EMO_GOOD.
    have ORD_NODUP : NoDup (filter (not_empty_pop E2) (seq 0 (length E2)))
      by apply NoDup_filter, NoDup_seq.
    iSplitL; last iSplitL; last iSplitL; last iSplitL.
    - iExists _,_,_. iExists esi2,emo2',stk2',onn,Vw2,Vi2.
      iFrame "∗". iSplitL; last iSplitL.
      { (* at↦ *) subst ζn2. rewrite (toHeadHist_insert _ _ _ onn).
        - subst emo2'. rewrite !fmap_app /=. eauto with iFrame.
        - clear -Letitr2 EqL. rewrite cons_length /=. lia.
        - clear. rewrite cons_length /=. lia. }
      { (* SeenMsgsAll γh s E2' esi2 emo2' ti *) iNext. iIntros (???? EMO_LOOKUP).
        case (decide (eidx = emo_ne (length emo2.*1.*1))) as [->|NEeidx].
        - subst emo2'. rewrite /= !fmap_app /= in EMO_LOOKUP.
          apply lookup_last_Some_2 in EMO_LOOKUP as ->.
          apply lookup_last_Some_2 in EV as ->. subst pp. simpl.
          iFrame "SM2'".
        - rewrite !fmap_length in NEeidx.
          apply lookup_emo_old_emo_ne in EMO_LOOKUP; [|done].
          apply (emo_ids_le_new E2) in EMO_LOOKUP as OLD; [|done].
          rewrite lookup_app_l in EV; [|done].
          iSpecialize ("SeenMsgsAll2" $! _ _ _ EV EMO_LOOKUP).
          rewrite (SeenMsgs_mono _ esi2 emo2 emo2'); [done|done| |done|done|done].
          intros ? IN_LVIEW. eapply (event_in_esi_emo E2); [done|].
          by specialize (hwf_logview_closed _ EWF2 _ _ EV _ IN_LVIEW). }
      iPureIntro. split_and!; red.
      + (* LAST_MSG *) by rewrite last_cons fmap_last last_snoc.
      + (* TOP_SEEN_PUSH *) intros ?????. case (decide (e = length E2)) as [->|NE].
        * apply lookup_last_Some_2 in EV as ->. by simpl.
        * rewrite lookup_app_1_ne in EV; [|done].
          specialize (TOP_SEEN_PUSH _ _ _ EV PUSH). solve_lat.
      + (* SEEN_ALL *) by apply seen_logview_all_add.
      + (* HB_XO *) by apply hb_xo_add.
      + constructor. (* ESI_EMO_GOOD *)
        * by apply (esi_good_mono E2).
        * rewrite ->Forall_lookup in GEN_GOOD |- *. intros gen' [[e es] [on V']] GEN'.
          case (decide (gen' = length emo2)) as [->|NE].
          -- apply lookup_last_Some_2 in GEN' as [= -> -> -> ->].
             econstructor; [by rewrite lookup_app_1_eq|done..| |apply sublist_nil_l].
             (* EMPTYING_POP *)
             rewrite /write_xo in XO_INTERP.
             rewrite (write_xo_stable _ E2') in XO_INTERP; [|done..].
             apply (stack_interp_mono_prefix _ E2') in XO_INTERP; [|done]. split.
             ++ intros INTERP. inv INTERP. { by apply nil_snoc in H0. }
                apply app_inj_tail in ORD as [<- <-].
                apply lookup_last_Some_2 in EVENT as ->. inv RUN; [|done].
                specialize (stack_interp_functional _ _ _ _ _ INTERP' XO_INTERP) as [= ? <-].
                by apply EMPTYING_WRITE.
             ++ intros ->%EMPTYING_WRITE0.
                econstructor; [done|done|apply lookup_app_1_eq|done].
          -- rewrite lookup_app_1_ne in GEN'; [|done].
             specialize (GEN_GOOD _ _ GEN'). simpl in GEN_GOOD.
             by apply (emo_gen_good_mono E2).
        * (* XO_AGREE *)
          unfold emo2', E2'. rewrite !fmap_app /=.
          rewrite write_xo_snoc_ne; [|done]. by apply app_inv_tail_iff.
        * (* HB_EMO *) by apply hb_emo_add_ne.
        * (* LIN_PERM *) done.
      + (* XO_INTERP *) eapply (stack_interp_snoc _ ppId _ _ (write_xo E2)).
        * by apply (stack_interp_mono_prefix E2).
        * by apply write_xo_snoc_ne.
        * apply lookup_app_1_eq.
        * done.
    - done.
    - iExists _,_,_,esi2,emo2'. iFrame (LIN_PERM2') "MS E◯2' M◯2' PSV2' SM2'".
    - done.
    - iPureIntro. right; right. subst. split_and!; try done.
      + by apply lookup_lt_is_Some.
      + exists pseV. split_and!; [done..|].
        subst M'. rewrite -LVIEWps /=. set_solver-. }

  (* finish CAS successful case *)
  iIntros "!>". wp_if. wp_op.
  iDestruct (view_at_elim with "⊒Vr2 d↦") as "d↦".
  wp_read. by iApply "HΦ". (* leaking data field *)
Qed.

Lemma atom_pop :
  pop_spec' pop StackLocal StackInv.
Proof.
  intros N DISJ s tid γg E1 M V. iIntros "#⊒V #Es" (Φ) "AU".
  iLöb as "IH" forall "#".

  wp_rec. awp_apply (atom_try_pop with "⊒V Es"); [eauto..|].
  iApply (aacc_aupd with "AU"); [done|].
  iIntros (E) "QI". iAaccIntro with "QI"; first by eauto with iFrame.
  iIntros (v V' E' psId ppId ps pp Vpp M') "(QI & ⊒V' & Local & F & CASE) !>".
  iDestruct "CASE" as "[CASE|[CASE|CASE]]".
  - iLeft. iDestruct "CASE" as %(-> & -> & ->).
    iFrame "QI". iIntros  "AU !> _".
    wp_let. wp_op. wp_if. by iApply ("IH" with "AU ⊒V Es").
  - iRight. iClear "IH". iDestruct "CASE" as %[? ?].
    iExists v, V', E', psId, ppId, ps, pp. iExists Vpp, M'.
    iFrame "QI ⊒V' Local F". iSplitL.
    + by iLeft.
    + iIntros "H !> _". subst v. wp_let. wp_op. wp_if. by iApply "H".
  - iRight. iClear "IH". iDestruct "CASE" as %[? ?].
    iExists v, V', E', psId, ppId, ps, pp. iExists Vpp, M'.
    iFrame "QI ⊒V' Local F". iSplitL.
    + by iRight.
    + iIntros "H !> _". wp_let. wp_op. rewrite bool_decide_false; [|lia].
      wp_if. by iApply "H".
Qed.
End proof.

Definition treiber_stack_impl `{!noprolG Σ, !tstackG Σ, !atomicG Σ}
  : stack_spec Σ := {|
    spec_history_old.StackInv_Objective := StackInv_objective ;
    spec_history_old.StackInv_StackLinearizability := StackInv_StackLinearizability_instance ;
    spec_history_old.StackInv_history_master_acc := StackInv_history_master_acc_instance ;
    spec_history_old.StackInv_history_snap := StackInv_history_snap_instance ;

    spec_history_old.StackLocal_history_snap := StackLocal_history_snap_instance ;
    spec_history_old.StackLocal_Persistent := StackLocal_persistent ;
    spec_history_old.new_stack_spec := new_stack_spec;
    spec_history_old.try_push_spec := atom_try_push ;
    spec_history_old.push_spec := atom_push ;
    spec_history_old.try_pop_spec := atom_try_pop ;
    spec_history_old.pop_spec := atom_pop ;
  |}.
