From iris.algebra Require Import gmap gset excl auth frac agree.
From iris.algebra.lib Require Import dfrac_agree.
From iris.base_logic.lib Require Import own gen_heap.

From gpfsl.lang Require Import lang.
From gpfsl.algebra Require Import lattice_cmra.

Require Import iris.prelude.options.

Canonical Structure cellO := (leibnizO cell).

(** Cmra to manage block deallocation *)
(* This is needed to present the ownership of a block, which can only be used
  to deallocate the block altogether.
  There's no separation deallocation of elements of the block. *)
Definition hist_freeableUR : ucmra :=
  gmapUR location.block (prodR fracR (gmapR Z (exclR unitO))).

(** Cmra to manage racing reads *)
(* We need fracR to also split these sets for fractional ownership of locations. *)
(* Set of read events, which can only grow, so we use [fracLatR]. *)
Definition hist_readUR : ucmra := gmapUR loc (fracLatR (gset_Lat time_id)).
(* Set of atomic write events, cannot be changed without a full fraction. *)
Definition hist_writesUR : ucmra := gmapUR loc (dfrac_agreeR (gsetO time_id)).

(** Cmra to manage views, which include thread-local simple views and SC views. *)
Definition viewR := authR (latUR view_Lat).

(** A singleton type that collect all Cmra structures we need *)
Class histGpreS Σ := {
  (* for a map of location histories. We use [gen_heap] for this.
    [option] is used to denote deallocation: once the location is deallocated,
    then it is None, otherwise it is (Some C). *)
  histGpreS_hist : gen_heapGS loc (option cell) Σ;
  (* for ownership of block deallocations *)
  histGpreS_freeable : inG Σ (authR hist_freeableUR);
  (* for tracking read events *)
  histGpreS_read : inG Σ (authR hist_readUR);
  (* for tracking simple views *)
  histGpreS_na_view : inG Σ viewR;
  (* for tracking atomic write events *)
  histGpreS_at_write : inG Σ (authR hist_writesUR);
  (* for thread views *)
  histGpreS_tview : inG Σ (authR (latUR tview_Lat));
}.

(** The singleton type we will need, which also collects the global ghost names. *)
Class histGS Σ := HistGS {
  hist_inG : histGpreS Σ ;

  hist_freeable_name : gname;
  hist_atwrite_name : gname;
  hist_atread_name : gname;
  hist_naread_name : gname;
  hist_sc_name : gname;
  hist_gtime_name : gname;
}.

Implicit Type l : loc.
Implicit Type M : memory.
Implicit Type C : cell.
Implicit Type 𝓝 : view.

(** From base structure to CMRA *)

Definition to_atw 𝓝 : hist_writesUR :=
  fmap (λ ts, to_frac_agree 1 ts.(tawrite)) 𝓝.

Definition to_nar 𝓝 : hist_readUR :=
  fmap (λ ts, (1%Qp, to_latT ts.(tnread))) 𝓝.

Definition to_atr 𝓝 : hist_readUR :=
  fmap (λ ts, (1%Qp, to_latT ts.(taread))) 𝓝.

(* TODO move to_hist to elsewhere *)
Definition to_hist M : gmap loc (option cell) :=
  fmap (λ C, (if bool_decide (cell_deallocated C) then None else Some C))
       (gmap_curry M).

(* Insert into memory *)
Lemma memory_uncurry_insert_nonempty M l C (NE: C ≠ ∅) :
  gmap_curry (<[l:=C]> M) = <[l := C]> (gmap_curry M).
Proof.
  rewrite {1}/insert /memory_cell_insert. apply map_eq=>l'.
  generalize (lookup_gmap_curry M l'),
     (lookup_gmap_curry (gmap_uncurry (<[l:=C]> (gmap_curry M))) l').
  setoid_rewrite lookup_gmap_uncurry. destruct (decide (l = l')) as [<-|].
  - rewrite !lookup_insert=>_ /=. destruct lookup=>/=.
    + move=>?. f_equal. by apply map_eq.
    + apply map_choose in NE as (t & ? & EQ)=>/(_ t). by rewrite EQ.
  - generalize (lookup_gmap_curry_None M l'),
       (lookup_gmap_curry_None (gmap_uncurry (<[l:=C]> (gmap_curry M))) l').
    setoid_rewrite lookup_gmap_uncurry. rewrite lookup_insert_ne //.
    (do 2 case:(_ !! l'))=>[??|?|?|] //= HN1 HN2 HS1 HS2.
    + f_equal. apply map_eq, HS2.
    + setoid_rewrite <-HS1 in HN1. naive_solver.
    + naive_solver.
Qed.

(** Insert as an update to the ghost version of history *)
(* Alloc *)
Lemma to_hist_insert_alloc M l C
  (ALLOC: ¬ cell_deallocated C) (NE: C ≠ ∅):
  to_hist (<[l:=C]> M) = <[l:= Some C]> (to_hist M).
Proof.
  rewrite /to_hist {1}/insert /memory_cell_insert.
    rewrite (_: Some C = if (bool_decide (cell_deallocated C)) then None else Some C);
    last by rewrite bool_decide_false.
  rewrite -(fmap_insert _ _ _ C). f_equal. by apply memory_uncurry_insert_nonempty.
Qed.
(* Dealloc *)
Lemma to_hist_insert_dealloc M l C
  (DEALLOC: cell_deallocated C) :
  to_hist (<[l:=C]> M) = <[l:= None]> (to_hist M).
Proof.
  rewrite /to_hist {1}/insert /memory_cell_insert.
  rewrite {2}(_: None = if (bool_decide (cell_deallocated C)) then None else Some C);
    last by rewrite bool_decide_true.
  rewrite -(fmap_insert _ _ _ C). f_equal. apply memory_uncurry_insert_nonempty.
  move => EM. rewrite EM in DEALLOC. apply DEALLOC.
Qed.

(** Lookup from the ghost version of history *)
Lemma to_hist_lookup_None M l:
  M !!c l = ∅ → to_hist M !! l = None.
Proof.
  rewrite lookup_fmap /memory_cell_lookup.
  destruct (gmap_curry M !! l) as [?|] eqn:Eq; [|done].
  move => ?. exfalso. by apply (gmap_curry_non_empty _ _ _ Eq).
Qed.

Lemma to_hist_lookup_Some M C l:
  to_hist M !! l = Some (Some C) →
  M !!c l = C ∧ ¬ cell_deallocated C ∧ C ≠ ∅.
Proof.
  rewrite lookup_fmap /=.
  destruct (gmap_curry M !! l) eqn:Eq; last by inversion 1.
  simpl. case_bool_decide; inversion 1; subst.
  rewrite /memory_cell_lookup Eq. repeat split; [done|].
  by apply (gmap_curry_non_empty _ _ _ Eq).
Qed.

(** Properties of [to_atw]---ghost version of atomic write event sets. *)
Lemma to_atw_insert 𝓝 l t ws rsa rsn :
  to_atw (<[l:=[{ t,ws,rsn,rsa }]]> 𝓝) = <[l:= to_frac_agree 1 ws]> (to_atw 𝓝).
Proof. by rewrite /to_atw fmap_insert. Qed.

Lemma to_atw_set_write_time 𝓝 l t :
  to_atw (set_write_time 𝓝 l t) ≡ to_atw 𝓝.
Proof.
  move => l'. rewrite 2!lookup_fmap.
  case (decide (l' = l)) => [->|?].
  - rewrite lookup_partial_alter /=.
    by rewrite -2!lookup_fmap -map_fmap_compose lookup_fmap.
  - by rewrite lookup_partial_alter_ne.
Qed.

Lemma to_atw_add_aread_id 𝓝 l t :
  to_atw (add_aread_id 𝓝 l t) ≡ (to_atw 𝓝).
Proof.
  move => l'. rewrite 2!lookup_fmap.
  case (decide (l' = l)) => [->|?].
  - rewrite lookup_partial_alter /=.
    by rewrite -2!lookup_fmap -map_fmap_compose lookup_fmap.
  - by rewrite lookup_partial_alter_ne.
Qed.

Lemma to_atw_add_nread_id 𝓝 l t :
  to_atw (add_nread_id 𝓝 l t) ≡ (to_atw 𝓝).
Proof.
  move => l'. rewrite 2!lookup_fmap.
  case (decide (l' = l)) => [->|?].
  - rewrite lookup_partial_alter /=.
    by rewrite -2!lookup_fmap -map_fmap_compose lookup_fmap.
  - by rewrite lookup_partial_alter_ne.
Qed.

Lemma to_atw_add_awrite_id 𝓝 l t ws :
  𝓝 !!aw l = Some ws →
  to_atw (add_awrite_id 𝓝 l t) ≡ <[l := to_frac_agree 1 (ws ∪ {[t]})]> (to_atw 𝓝).
Proof.
  move => Eql l'. rewrite lookup_fmap.
  case (decide (l' = l)) => [->|?].
  - rewrite lookup_insert lookup_partial_alter /=.
    rewrite -2!lookup_fmap -map_fmap_compose lookup_fmap.
    destruct (view_lookup_of_awp _ _ _ Eql) as [p [Eq1 Eq2]].
    by rewrite Eq2 /= Eq1 union_comm_L.
  - rewrite lookup_insert_ne; [|done].
    rewrite lookup_partial_alter_ne; [|done]. by rewrite lookup_fmap.
Qed.

Lemma to_atw_lookup_None 𝓝 l:
  𝓝 !! l = None ↔ to_atw 𝓝 !! l = None.
Proof.
  rewrite lookup_fmap. split; first by move => ->.
  destruct (𝓝 !! l) as [[]|] eqn:Eql; [|done]. by rewrite Eql.
Qed.

Lemma to_atw_lookup_Some 𝓝 l p:
  𝓝 !! l = Some p → to_atw 𝓝 !! l = Some (to_frac_agree 1 p.(tawrite)).
Proof. rewrite lookup_fmap => -> //. Qed.

Lemma to_atw_lookup_r_Some 𝓝 l rs:
  𝓝 !!aw l = Some rs → to_atw 𝓝 !! l = Some (to_frac_agree 1 rs).
Proof.
  move => Eql. destruct (view_lookup_of_awp _ _ _ Eql) as [p [Eq1 Eq2]].
  rewrite -Eq1. by apply to_atw_lookup_Some.
Qed.

Lemma to_atw_valid 𝓝: ✓ to_atw 𝓝.
Proof. intros l. rewrite lookup_fmap. case (_ !! l) => //. Qed.

(** Properties of [to_nar]---ghost version of non-atomic read event sets. *)
Lemma to_nar_insert 𝓝 l t ws rsa rsn :
  to_nar (<[l:=[{ t,ws,rsn,rsa }]]> 𝓝) = <[l:= (1%Qp, to_latT rsn)]> (to_nar 𝓝).
Proof.
  apply leibniz_equiv => l'. rewrite lookup_fmap.
  case (decide (l' = l)) => [->|?].
  - by rewrite 2!lookup_insert /=.
  - do 2 (rewrite lookup_insert_ne; [|done]). by rewrite lookup_fmap.
Qed.

Lemma to_nar_set_write_time 𝓝 l t :
  to_nar (set_write_time 𝓝 l t) = to_nar 𝓝.
Proof.
  apply leibniz_equiv => l'. rewrite 2!lookup_fmap.
  case (decide (l' = l)) => [->|?].
  - rewrite lookup_partial_alter /=.
    by rewrite -2!lookup_fmap -map_fmap_compose lookup_fmap.
  - by rewrite lookup_partial_alter_ne.
Qed.

Lemma to_nar_add_awrite_id 𝓝 l t :
  to_nar (add_awrite_id 𝓝 l t) = to_nar 𝓝.
Proof.
  apply leibniz_equiv => l'. rewrite 2!lookup_fmap.
  case (decide (l' = l)) => [->|?].
  - rewrite lookup_partial_alter /=.
    by rewrite -2!lookup_fmap -map_fmap_compose lookup_fmap.
  - by rewrite lookup_partial_alter_ne.
Qed.

Lemma to_nar_add_aread_id 𝓝 l t :
  to_nar (add_aread_id 𝓝 l t) = to_nar 𝓝.
Proof.
  apply leibniz_equiv => l'.
  rewrite 2!lookup_fmap.
  case (decide (l' = l)) => [->|?].
  - rewrite lookup_partial_alter /=.
    by rewrite -2!lookup_fmap -map_fmap_compose lookup_fmap.
  - by rewrite lookup_partial_alter_ne.
Qed.

Lemma to_nar_add_nread_id 𝓝 l t rs :
  𝓝 !!nr l = Some rs →
  to_nar (add_nread_id 𝓝 l t) = <[l := (1%Qp, to_latT (rs ∪ {[t]}))]> (to_nar 𝓝).
Proof.
  move => Eql. apply leibniz_equiv => l'.
  rewrite lookup_fmap.
  case (decide (l' = l)) => [->|?].
  - rewrite lookup_insert lookup_partial_alter /=.
    rewrite -2!lookup_fmap -map_fmap_compose lookup_fmap.
    destruct (view_lookup_of_nrp _ _ _ Eql) as [p [Eq1 Eq2]].
    by rewrite Eq2 /= Eq1 union_comm_L.
  - rewrite lookup_insert_ne; [|done].
    rewrite lookup_partial_alter_ne; [|done]. by rewrite lookup_fmap.
Qed.

Lemma to_nar_lookup_None 𝓝 l:
  𝓝 !! l = None ↔ to_nar 𝓝 !! l = None.
Proof.
  rewrite lookup_fmap. split; first by move => ->.
  destruct (𝓝 !! l) as [[]|] eqn:Eql; [|done]. by rewrite Eql.
Qed.

Lemma to_nar_lookup_Some 𝓝 l p:
  𝓝 !! l = Some p → to_nar 𝓝 !! l = Some (1%Qp, to_latT p.(tnread)).
Proof. rewrite lookup_fmap => -> //. Qed.

Lemma to_nar_lookup_r_Some 𝓝 l rs:
  𝓝 !!nr l = Some rs → to_nar 𝓝 !! l = Some (1%Qp, to_latT rs).
Proof.
  move => Eql. destruct (view_lookup_of_nrp _ _ _ Eql) as [p [Eq1 Eq2]].
  rewrite -Eq1. by apply to_nar_lookup_Some.
Qed.

Lemma to_nar_valid 𝓝: ✓ to_nar 𝓝.
Proof. intros l. rewrite lookup_fmap. case (_ !! l) => //. Qed.

(** Properties of [to_atr]---ghost version of atomic read event sets. *)
Lemma to_atr_insert 𝓝 l t ws rsa rsn :
  to_atr (<[l:=[{ t,ws,rsn,rsa }]]> 𝓝) = <[l:= (1%Qp, to_latT rsa)]> (to_atr 𝓝).
Proof.
  apply leibniz_equiv => l'. rewrite lookup_fmap.
  case (decide (l' = l)) => [->|?].
  - by rewrite 2!lookup_insert /=.
  - do 2 (rewrite lookup_insert_ne; [|done]). by rewrite lookup_fmap.
Qed.

Lemma to_atr_set_write_time 𝓝 l t :
  to_atr (set_write_time 𝓝 l t) = to_atr 𝓝.
Proof.
  apply leibniz_equiv => l'. rewrite 2!lookup_fmap.
  case (decide (l' = l)) => [->|?].
  - rewrite lookup_partial_alter /=.
    by rewrite -2!lookup_fmap -map_fmap_compose lookup_fmap.
  - by rewrite lookup_partial_alter_ne.
Qed.

Lemma to_atr_add_nread_id 𝓝 l t :
  to_atr (add_nread_id 𝓝 l t) = to_atr 𝓝.
Proof.
  apply leibniz_equiv => l'. rewrite 2!lookup_fmap.
  case (decide (l' = l)) => [->|?].
  - rewrite lookup_partial_alter /=.
    by rewrite -2!lookup_fmap -map_fmap_compose lookup_fmap.
  - by rewrite lookup_partial_alter_ne.
Qed.

Lemma to_atr_add_awrite_id 𝓝 l t :
  to_atr (add_awrite_id 𝓝 l t) = to_atr 𝓝.
Proof.
  apply leibniz_equiv => l'. rewrite 2!lookup_fmap.
  case (decide (l' = l)) => [->|?].
  - rewrite lookup_partial_alter /=.
    by rewrite -2!lookup_fmap -map_fmap_compose lookup_fmap.
  - by rewrite lookup_partial_alter_ne.
Qed.

Lemma to_atr_add_aread_id 𝓝 l t rs :
  𝓝 !!ar l = Some rs →
  to_atr (add_aread_id 𝓝 l t) = <[l := (1%Qp, to_latT (rs ∪ {[t]}))]> (to_atr 𝓝).
Proof.
  move => Eql. apply leibniz_equiv => l'. rewrite lookup_fmap.
  case (decide (l' = l)) => [->|?].
  - rewrite lookup_insert lookup_partial_alter /=.
    rewrite -2!lookup_fmap -map_fmap_compose lookup_fmap.
    destruct (view_lookup_of_arp _ _ _ Eql) as [p [Eq1 Eq2]].
    by rewrite Eq2 /= Eq1 union_comm_L.
  - rewrite lookup_insert_ne; [|done].
    rewrite lookup_partial_alter_ne; [|done]. by rewrite lookup_fmap.
Qed.

Lemma to_atr_lookup_None 𝓝 l:
  𝓝 !! l = None ↔ to_atr 𝓝 !! l = None.
Proof.
  rewrite lookup_fmap. split; first by move => ->.
  destruct (𝓝 !! l) as [[]|] eqn:Eql; [|done]. by rewrite Eql.
Qed.

Lemma to_atr_lookup_Some 𝓝 l p:
  𝓝 !! l = Some p → to_atr 𝓝 !! l = Some (1%Qp, to_latT p.(taread)).
Proof. rewrite lookup_fmap => -> //. Qed.

Lemma to_atr_lookup_r_Some 𝓝 l rs:
  𝓝 !!ar l = Some rs → to_atr 𝓝 !! l = Some (1%Qp, to_latT rs).
Proof.
  move => Eql. destruct (view_lookup_of_arp _ _ _ Eql) as [p [Eq1 Eq2]].
  rewrite -Eq1. by apply to_atr_lookup_Some.
Qed.

Lemma to_atr_valid 𝓝: ✓ to_atr 𝓝.
Proof. intros l. rewrite lookup_fmap. case (_ !! l) => //. Qed.

Lemma add_aread_awrite_comm 𝓝 (l: loc) tr tw:
  add_awrite_id (add_aread_id 𝓝 l tr) l tw =
  add_aread_id (add_awrite_id 𝓝 l tw) l tr.
Proof.
  apply leibniz_equiv => l'.
  case (decide (l' = l)) => [->|?].
  - rewrite 4!lookup_partial_alter /=.
    by rewrite -4!lookup_fmap -2!map_fmap_compose.
  - by do 4 (rewrite lookup_partial_alter_ne; [|done]).
Qed.
