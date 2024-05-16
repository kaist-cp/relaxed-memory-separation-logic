From iris.algebra Require Import cmra auth lib.frac_auth.
From iris.base_logic.lib Require Import own.
From orc11 Require Export base.

Require Import iris.prelude.options.

Section lat.
Context {Lat : latticeT}.

(* We box the type to avoid ambiguous instances. *)
Record latT := to_latT { of_latT :> Lat }.
Instance latT_equiv : Equiv latT := λ x y, of_latT x ≡ y.
Instance latT_equiv_equivalence : @Equivalence latT (≡).
Proof. split; repeat intros []; apply lat_equiv_equivalence. Qed.

Canonical Structure latO := discreteO latT.

Instance lat_valid : Valid latT := λ _, True.
Instance lat_pcore : PCore latT := Some.
Instance lat_op : Op latT := λ x y, to_latT (of_latT x ⊔ y).

Definition lat_ra_mixin : RAMixin latT.
Proof.
  split; try apply _; try done.
  - intros ???. by apply lat_join_proper.
  - intros ????[=<-]. eauto.
  - intros ???. by apply (assoc (@join Lat _)).
  - intros ??. by apply (comm (@join Lat _)).
  - intros ??[=<-]. apply lat_join_idem.
  - intros ????[=<-]. eauto.
Qed.

Canonical Structure latR := discreteR latT lat_ra_mixin.

Global Instance latR_cmra_discrete : CmraDiscrete latR.
Proof. apply discrete_cmra_discrete. Qed.

Instance latR_unit `{!LatBottom bot} : Unit latT := to_latT bot.
Lemma latT_ucmra_mixin `{!LatBottom bot} : UcmraMixin latT.
Proof. split; (try apply _)=>// -[x]. apply: (left_id bot). Qed.
Canonical Structure latUR `{!LatBottom bot} : ucmra :=
  Ucmra latT latT_ucmra_mixin.
End lat.

Add Printing Constructor latT.
Arguments latT : clear implicits.
Arguments latO : clear implicits.
Arguments latR : clear implicits.
Arguments latUR _ {_ _}.

Section lat_prop.
Context {Lat : latticeT}.
Notation latT :=  (latT Lat).
Notation latO :=  (latO Lat).
Notation latR :=  (latR Lat).

Global Instance of_latT_inj : Inj (≡) (≡) (@of_latT Lat).
Proof. by intros ?. Qed.
Global Instance to_latT_inj : Inj (≡) (≡) (@to_latT Lat).
Proof. by intros ?. Qed.

Lemma of_to_latT (x : Lat) : of_latT (to_latT x) = x.
Proof. done. Qed.
Lemma to_of_latT (x : latT) : to_latT (of_latT x) = x.
Proof. by destruct x. Qed.

Global Instance of_latT_Proper : Proper ((≡) ==> (≡)) (@of_latT Lat).
Proof. solve_proper. Qed.
Global Instance to_latT_Proper : Proper ((≡) ==> (≡)) (@to_latT Lat).
Proof. solve_proper. Qed.

Lemma lat_op_join (x y : latT) : x ⋅ y = to_latT (of_latT x ⊔ y).
Proof. done. Qed.
Lemma lat_op_join' (x y : Lat) : to_latT x ⋅ to_latT y = to_latT (x ⊔ y).
Proof. done. Qed.

Global Instance latT_core_id (x : latT) : CoreId x.
Proof. by unfold CoreId. Qed.

Lemma latT_equiv_iff (x y : latT) : x ≡ y ↔ of_latT x ≡ of_latT y.
Proof. done. Qed.
Global Instance latT_leinbniz : LeibnizEquiv Lat → LeibnizEquiv latT.
Proof. by intros ?[x][y]->%(leibniz_equiv (A := Lat) x y). Qed.

Lemma latT_included (x y : latT) : x ≼ y ↔ of_latT x ⊑ of_latT y.
Proof.
  split=>[[z ->]|?]; [solve_lat|].
  exists y. rewrite lat_op_join latT_equiv_iff. solve_lat.
Qed.

Lemma latT_absorb (x y : latT):
  x ⋅ y ≡ x ↔ y ≼ x.
Proof.
  split; first by move => <-; apply : cmra_included_r.
  move => /latT_included ?.
  rewrite lat_op_join lat_le_join_l; [by rewrite to_of_latT|done].
Qed.

Lemma latT_local_unit_update `{!LatBottom bot} (x x' y : @latUR Lat _ _)
  (Ext: of_latT x ⊑ of_latT x'):
  (x, y) ~l~> (x', x').
Proof.
  apply local_update_unital_discrete => z Val Eq. split; [done|].
  symmetry. apply latT_absorb. etrans; last by apply latT_included, Ext.
  rewrite Eq. apply : cmra_included_r.
Qed.

Lemma latT_local_update (x x' y: Lat) :
  (to_latT x, to_latT x') ~l~> (to_latT (x ⊔ y), to_latT (x' ⊔ y)).
Proof.
  rewrite -2!lat_op_join' (cmra_comm (to_latT x)) (cmra_comm (to_latT x')).
  by apply op_local_update_discrete.
Qed.

Global Instance latR_cmra_total : CmraTotal latR.
Proof. intros ?. eauto. Qed.
End lat_prop.

Section lat_auth.
  Context `{LatBottom LAT} `{inG Σ (authR (latUR LAT))}.

  Lemma own_lat_auth_update γ (V V': LAT) (Ext: V ⊑ V'):
    own γ (● (to_latT V)) ==∗ own γ (● (to_latT V')) ∗ own γ (◯ (to_latT V')).
  Proof.
    rewrite -own_op.
    by apply own_update, auth_update_alloc, latT_local_unit_update.
  Qed.

  Lemma own_lat_auth_update_fork γ (V: LAT):
    own γ (● (to_latT V)) ==∗ own γ (● (to_latT V)) ∗ own γ (◯ (to_latT V)).
  Proof. by apply own_lat_auth_update. Qed.

  Lemma own_lat_auth_update_join γ (V1 V2: LAT):
     own γ (● (to_latT V1)) ==∗ own γ (● to_latT (V1 ⊔ V2)) ∗ own γ (◯ to_latT (V1 ⊔ V2)).
  Proof. apply own_lat_auth_update. solve_lat. Qed.

  Lemma own_lat_auth_downclosed γ (V1 V2: LAT) (Le : V2 ⊑ V1) :
    own γ (◯ (to_latT V1)) ⊢ own γ (◯ (to_latT V2)).
  Proof. by apply own_mono, auth_frag_mono, latT_included. Qed.

  Lemma own_lat_auth_max γ (V1 V2: LAT) :
    own γ (● (to_latT V1)) ⊢ own γ (◯ (to_latT V2)) -∗ ⌜V2 ⊑ V1⌝.
  Proof.
    apply bi.wand_intro_r.
    rewrite -own_op own_valid uPred.discrete_valid auth_both_valid_discrete
            latT_included.
    by apply bi.pure_mono=>-[? _].
  Qed.
End lat_auth.

From Coq.QArith Require Import Qcanon.

Lemma frac_prod_max {A : cmra} (q: frac) (a b : A) :
  ✓ (q, a) → (1%Qp, b) ≼ (q, a) → False.
Proof.
  move => [/= /frac_valid Le ?] /prod_included [/frac_included Lt _].
  by eapply (irreflexivity Qp.lt q), Qp.le_lt_trans.
Qed.

(* TODO: many of these can be generalized for (prodR fracR A) *)
Notation fracLatR LAT := (prodR fracR (latR LAT)).

Section lat_frac_prop.
Context {Lat : latticeT}.
Notation latT :=  (latT Lat).

Lemma frac_lat_included (q q': frac) (x x': latT) :
  (q, x) ≼ (q', x') ↔ (q < q')%Qp ∧ of_latT x ⊑ of_latT x'.
Proof. by rewrite prod_included frac_included latT_included. Qed.

Lemma frac_lat_op (q q': frac) (x x': Lat) :
  (q, to_latT x) ⋅ (q', to_latT x') = ((q+q')%Qp, to_latT (x ⊔ x')).
Proof. by rewrite -pair_op frac_op lat_op_join'. Qed.

Lemma frac_lat_op_join (q q': frac) (x x': Lat) :
  (q, to_latT (x ⊔ x')) ⋅ (q', to_latT x') ≡ ((q+q')%Qp, to_latT (x ⊔ x')).
Proof. rewrite -pair_op frac_op lat_op_join' (lat_le_join_l (x ⊔ x') x'); [done|solve_lat]. Qed.

Lemma frac_lat_op_join_L `{!LeibnizEquiv Lat} (q q': frac) (x x': Lat) :
  (q, to_latT (x ⊔ x')) ⋅ (q', to_latT x') = ((q+q')%Qp, to_latT (x ⊔ x')).
Proof. rewrite -pair_op frac_op lat_op_join' (lat_le_join_l_L (x ⊔ x') x'); [done|solve_lat]. Qed.

Lemma frac_lat_local_update (q q': frac) (x x' y: Lat) :
  ((q, to_latT x), (q', to_latT x')) ~l~> ((q, to_latT (x ⊔ y)), (q', to_latT (x' ⊔ y))).
Proof. by apply prod_local_update_2, latT_local_update. Qed.

End lat_frac_prop.
