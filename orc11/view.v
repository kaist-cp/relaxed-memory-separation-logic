From orc11 Require Export location.

Require Import stdpp.options.

Notation time := (positive) (only parsing).
Notation time_id := (positive) (only parsing).
Notation time_ids := (gset time_id) (only parsing).

Record timeInfo : Type := mkTimeInfo {
  twrite : time;
  tawrite: time_ids;
  tnread : time_ids;
  taread : time_ids;
}.

Notation "[{ t , wa , rn , ra }]" :=
  (mkTimeInfo t wa rn ra)
    (at level 20, format "[{  t , wa , rn , ra  }]",
     t at level 21, wa at level 21, rn at level 21, ra at level 21) : stdpp_scope.

Global Instance timeInfo_dec_eq : EqDecision timeInfo.
Proof. solve_decision. Qed.

Section timeInfoCountable.
  Definition _ti_tuple : Type := time * time_ids * time_ids * time_ids.
  Definition _ti_to_tuple (ti: timeInfo) : _ti_tuple :=
    (twrite ti, tawrite ti, tnread ti, taread ti).
  Definition _tuple_to_ti (ti: _ti_tuple) : timeInfo :=
    match ti with
    | (t, wa, rn, ra) => ([{ t, wa, rn, ra }])
    end.
End timeInfoCountable.

Global Instance timeInfo_countable : Countable timeInfo.
Proof.
  refine (inj_countable _ti_to_tuple (Some ∘ _tuple_to_ti) _); by intros [].
Qed.

Global Instance timeInfo_sqsubseteq : SqSubsetEq timeInfo :=
  λ i1 i2, i1.(twrite) ⊑ i2.(twrite) ∧ i1.(tawrite) ⊑ i2.(tawrite) ∧
           i1.(tnread) ⊑ i2.(tnread) ∧ i1.(taread) ⊑ i2.(taread).

Global Instance timeInfo_inhabited : Inhabited timeInfo := populate ([{ 1, ∅, ∅, ∅ }]).

Program Canonical Structure timeInfo_Lat : latticeT :=
  Make_Lat timeInfo eq timeInfo_sqsubseteq
  (λ i1 i2, [{ i1.(twrite) ⊔ i2.(twrite), i1.(tawrite) ⊔ i2.(tawrite),
               i1.(tnread) ⊔ i2.(tnread), i1.(taread) ⊔ i2.(taread) }])
  (λ i1 i2, [{ i1.(twrite) ⊓ i2.(twrite), i1.(tawrite) ⊓ i2.(tawrite),
               i1.(tnread) ⊓ i2.(tnread), i1.(taread) ⊓ i2.(taread) }])
  (populate ([{ 1, ∅, ∅, ∅ }])) _ _ _ _ _ _ _ _ _ _ _ _.
Next Obligation.
  constructor; first done. move => ??? [?[?[??]]] [?[?[??]]]. repeat split; by etrans.
Qed.
Next Obligation.
  move => [????] [????] [?[?[??]]] [?[?[??]]]. f_equal; by apply : anti_symm.
Qed.
Next Obligation. intros [] []. repeat split; simpl; solve_lat. Qed.
Next Obligation. intros [] []. repeat split; simpl; solve_lat. Qed.
Next Obligation.
  move => [????] [????] [????] [?[?[??]]] [?[?[??]]]. repeat split; solve_lat.
Qed.
Next Obligation. intros [] []. repeat split; simpl; solve_lat. Qed.
Next Obligation. intros [] []. repeat split; simpl; solve_lat. Qed.
Next Obligation.
  move => [????] [????] [????] [?[?[??]]] [?[?[??]]]. repeat split; solve_lat.
Qed.

Global Instance timeInfo_sqsubseteq_dec : RelDecision (A:=timeInfo) (⊑).
Proof. solve_decision. Qed.

Global Instance timeInfo_leibniz_eq : LeibnizEquiv timeInfo.
Proof. move => ?? //. Qed.

Section View.
  Context `{!LocFacts loc}.

  Definition view := gmap loc timeInfo.
  (* this is not canonical, as it overlaps [gmap_Lat].
    This is to avoid TC divergence in lambda-rust-weak. *)
  Canonical Structure view_Lat := gmap_Lat loc timeInfo_Lat.

  Implicit Type (V: view).

  Definition view_lookup_write: Lookup loc time view
    := fun l V => fmap twrite (V !! l).
  Definition view_lookup_awrite: Lookup loc time_ids view
    := fun l V => fmap tawrite (V !! l).
  Definition view_lookup_nread: Lookup loc time_ids view
    := fun l V => fmap tnread (V !! l).
  Definition view_lookup_aread: Lookup loc time_ids view
    := fun l V => fmap taread (V !! l).

  Global Instance default_view_bot : Proper ((⊑) ==> (⊑)) (default (∅: view)).
  Proof. apply from_option_bot_proper. solve_proper. Qed.
End View.
Arguments view {_ _}.
Arguments view_Lat {_ _}.


Notation "V !!w i" := (view_lookup_write i V) (at level 20) : stdpp_scope.
Notation "V !!aw i" := (view_lookup_awrite i V) (at level 20) : stdpp_scope.
Notation "V !!ar i" := (view_lookup_aread i V) (at level 20) : stdpp_scope.
Notation "V !!nr i" := (view_lookup_nread i V) (at level 20) : stdpp_scope.

Section ViewLookup.
Context `{!LocFacts loc}.
Implicit Types (l : loc) (t: time).

Lemma view_lookup_w' V l o:
  V !! l = o → V !!w l = twrite <$> o.
Proof. destruct o; [rewrite fmap_Some|rewrite fmap_None]; eauto. Qed.

Lemma view_lookup_w V l t wsa rsn rsa :
  V !! l = Some ([{ t, wsa, rsn , rsa }]) → V !!w l = Some t.
Proof. rewrite fmap_Some. eauto. Qed.

Lemma view_lookup_aw' V l o:
  V !! l = o → V !!aw l = tawrite <$> o.
Proof. destruct o; [rewrite fmap_Some|rewrite fmap_None]; eauto. Qed.

Lemma view_lookup_aw V l t wsa rsn rsa :
  V !! l = Some ([{ t, wsa, rsn , rsa }]) → V !!aw l = Some wsa.
Proof. rewrite fmap_Some. eauto. Qed.

Lemma view_lookup_nr' V l o:
  V !! l = o → V !!nr l = tnread <$> o.
Proof. destruct o; [rewrite fmap_Some|rewrite fmap_None]; eauto. Qed.

Lemma view_lookup_nr V l t wsa rsn rsa :
  V !! l = Some ([{ t, wsa, rsn, rsa }]) → V !!nr l = Some rsn.
Proof. rewrite fmap_Some. eauto. Qed.

Lemma view_lookup_ar' V l o:
  V !! l = o → V !!ar l = taread <$> o.
Proof. destruct o; [rewrite fmap_Some|rewrite fmap_None]; eauto. Qed.

Lemma view_lookup_ar V l t wsa rsn rsa :
  V !! l = Some  ([{ t, wsa, rsn, rsa }]) → V !!ar l = Some rsa.
Proof. rewrite fmap_Some. eauto. Qed.


Lemma view_lookup_wp V l p :
  V !! l = Some p → V !!w l = Some p.(twrite).
Proof. rewrite fmap_Some. eauto. Qed.

Lemma view_lookup_awp V l p :
  V !! l = Some p → V !!aw l = Some p.(tawrite).
Proof. rewrite fmap_Some. eauto. Qed.

Lemma view_lookup_nrp V l p :
  V !! l = Some p → V !!nr l = Some p.(tnread).
Proof. rewrite fmap_Some. eauto. Qed.

Lemma view_lookup_arp V l p :
  V !! l = Some p → V !!ar l = Some p.(taread).
Proof. rewrite fmap_Some. eauto. Qed.

Lemma view_lookup_of_wp V l t :
  V !!w l = Some t → ∃ p, p.(twrite) = t ∧ V !! l = Some p.
Proof. rewrite fmap_Some. move => [? [-> ->]]. eauto. Qed.

Lemma view_lookup_of_awp V l ws :
  V !!aw l = Some ws → ∃ p, p.(tawrite) = ws ∧ V !! l = Some p.
Proof. rewrite fmap_Some. move => [? [-> ->]]. eauto. Qed.

Lemma view_lookup_of_nrp V l rs :
  V !!nr l = Some rs → ∃ p, p.(tnread) = rs ∧ V !! l = Some p.
Proof. rewrite fmap_Some. move => [? [-> ->]]. eauto. Qed.

Lemma view_lookup_of_arp V l rs :
  V !!ar l = Some rs → ∃ p, p.(taread) = rs ∧ V !! l = Some p.
Proof. rewrite fmap_Some. move => [? [-> ->]]. eauto. Qed.

Lemma view_lookup_of V l t wsa rsa rsn:
  V !!w l = Some t → V !!aw l = Some wsa →
  V !!nr l = Some rsn → V !!ar l = Some rsa → V !! l = Some ([{ t, wsa, rsn, rsa }]).
Proof.
  move/(view_lookup_of_wp _ _ _) => [[????] /= [-> ?]].
  move/(view_lookup_of_awp _ _ _) => [[????] /= [-> ?]].
  move/(view_lookup_of_nrp _ _ _) => [[????] /= [-> ?]].
  move/(view_lookup_of_arp _ _ _) => [[????] /= [-> ?]].
  by simplify_map_eq.
Qed.

Lemma view_lookup_w_join V1 V2 l:
  (V1 ⊔ V2) !!w l = V1 !!w l ⊔ V2 !!w l.
Proof.
  rewrite /view_lookup_write /= lookup_join.
  destruct (V1 !! l) as [[]|] eqn:Eq1; destruct (V2 !! l) as [[]|] eqn:Eq2;
    rewrite ?Eq1 ?Eq2; done.
Qed.

Lemma view_lookup_aw_join V1 V2 l:
  (V1 ⊔ V2) !!aw l = V1 !!aw l ⊔ V2 !!aw l.
Proof.
  rewrite /view_lookup_awrite /= lookup_join.
  destruct (V1 !! l) as [[]|] eqn:Eq1; destruct (V2 !! l) as [[]|] eqn:Eq2;
    rewrite ?Eq1 ?Eq2; done.
Qed.

Lemma view_lookup_nr_join V1 V2 l:
  (V1 ⊔ V2) !!nr l = V1 !!nr l ⊔ V2 !!nr l.
Proof.
  rewrite /view_lookup_nread /= lookup_join.
  destruct (V1 !! l) as [[]|] eqn:Eq1; destruct (V2 !! l) as [[]|] eqn:Eq2;
    rewrite Eq1 Eq2; simpl; done.
Qed.

Lemma view_lookup_ar_join V1 V2 l:
  (V1 ⊔ V2) !!ar l = V1 !!ar l ⊔ V2 !!ar l.
Proof.
  rewrite /view_lookup_aread /= lookup_join.
  destruct (V1 !! l) as [[]|] eqn:Eq1; destruct (V2 !! l) as [[]|] eqn:Eq2;
    rewrite Eq1 Eq2; simpl; done.
Qed.

Lemma view_lookup_w_insert V l p :
  <[l := p]> V !!w l = Some p.(twrite).
Proof. by rewrite /view_lookup_write lookup_insert. Qed.

Lemma view_lookup_aw_insert V l p :
  <[l := p]> V !!aw l = Some p.(tawrite).
Proof. by rewrite /view_lookup_awrite lookup_insert. Qed.

Lemma view_lookup_nr_insert V l p :
  <[l := p]> V !!nr l = Some p.(tnread).
Proof. by rewrite /view_lookup_nread lookup_insert. Qed.

Lemma view_lookup_ar_insert V l p :
  <[l := p]> V !!ar l = Some p.(taread).
Proof. by rewrite /view_lookup_aread lookup_insert. Qed.

Lemma view_lookup_w_insert_ne V l l' p :
  l ≠ l' → <[l := p]> V !!w l' = V !!w l'.
Proof. move => ?. by rewrite /view_lookup_write lookup_insert_ne. Qed.

Lemma view_lookup_aw_insert_ne V l l' p :
  l ≠ l' → <[l := p]> V !!aw l' = V !!aw l'.
Proof. move => ?. by rewrite /view_lookup_awrite lookup_insert_ne. Qed.

Lemma view_lookup_nr_insert_ne V l l' p :
  l ≠ l' → <[l := p]> V !!nr l' = V !!nr l'.
Proof. move => ?. by rewrite /view_lookup_nread lookup_insert_ne. Qed.

Lemma view_lookup_ar_insert_ne V l l' p :
  l ≠ l' → <[l := p]> V !!ar l' = V !!ar l'.
Proof. move => ?. by rewrite /view_lookup_aread lookup_insert_ne. Qed.

Lemma view_lookup_w_singleton_Some l p l' t:
  {[l := p]} !!w l' = Some t → l' = l ∧ t = p.(twrite).
Proof.
  rewrite /view_lookup_write. case (decide (l' = l)) => ?; [subst l'|].
  - by rewrite lookup_insert => [[<-]].
  - by rewrite lookup_insert_ne.
Qed.

Lemma view_lookup_aw_singleton_Some l p l' rs:
  {[l := p]} !!aw l' = Some rs → l' = l ∧ rs = p.(tawrite).
Proof.
  rewrite /view_lookup_awrite. case (decide (l' = l)) => ?; [subst l'|].
  - by rewrite lookup_insert => [[<-]].
  - by rewrite lookup_insert_ne.
Qed.

Lemma view_lookup_nr_singleton_Some l p l' rs:
  {[l := p]} !!nr l' = Some rs → l' = l ∧ rs = p.(tnread).
Proof.
  rewrite /view_lookup_nread. case (decide (l' = l)) => ?; [subst l'|].
  - by rewrite lookup_insert => [[<-]].
  - by rewrite lookup_insert_ne.
Qed.

Lemma view_lookup_ar_singleton_Some l p l' rs:
  {[l := p]} !!ar l' = Some rs → l' = l ∧ rs = p.(taread).
Proof.
  rewrite /view_lookup_aread. case (decide (l' = l)) => ?; [subst l'|].
  - by rewrite lookup_insert => [[<-]].
  - by rewrite lookup_insert_ne.
Qed.


Lemma view_lookup_w_singleton_None l p l':
  {[l := p]} !!w l' = None → l' ≠ l.
Proof.
  rewrite /view_lookup_write. case (decide (l' = l)) => [?|//]. subst l'.
  by rewrite lookup_insert.
Qed.

Lemma view_lookup_aw_singleton_None l p l':
  {[l := p]} !!aw l' = None → l' ≠ l.
Proof.
  rewrite /view_lookup_awrite. case (decide (l' = l)) => [?|//]. subst l'.
  by rewrite lookup_insert.
Qed.

Lemma view_lookup_nr_singleton_None l p l':
  {[l := p]} !!nr l' = None → l' ≠ l.
Proof.
  rewrite /view_lookup_nread. case (decide (l' = l)) => [?|//]. subst l'.
  by rewrite lookup_insert.
Qed.

Lemma view_lookup_ar_singleton_None l p l':
  {[l := p]} !!ar l' = None → l' ≠ l.
Proof.
  rewrite /view_lookup_aread. case (decide (l' = l)) => [?|//]. subst l'.
  by rewrite lookup_insert.
Qed.

End ViewLookup.

Tactic Notation "simplify_view":= repeat
  match goal with
  | H : ?V !! ?l = ?o |- context P [ ?V !!w ?l ] =>
    let o' := eval cbn in (twrite <$> o) in
    let g := (context P [o']) in
    cut g; first (rewrite (view_lookup_w' V l o H); exact id)
  | H : ?V !! ?l = ?o |- context P [ ?V !!aw ?l ] =>
    let o' := eval cbn in (tawrite <$> o) in
    let g := (context P [o']) in
    cut g; first (rewrite (view_lookup_aw' V l o H); exact id)
  | H : ?V !! ?l = ?o |- context P [ ?V !!ar ?l ] =>
    let o' := eval cbn in (taread <$> o) in
    let g := (context P [o']) in
    cut g; first (rewrite (view_lookup_ar' V l o H); exact id)
  | H : ?V !! ?l = ?o |- context P [ ?V !!nr ?l ] =>
    let o' := eval cbn in (tnread <$> o) in
    let g := (context P [o']) in
    cut g; first (rewrite (view_lookup_nr' V l o H); exact id)
  end.


Lemma view_sqsubseteq `{!LocFacts loc} (V1 V2 : view) (l : loc) :
  V1 !! l ⊑ V2 !! l ↔
  V1 !!w l ⊑ V2 !!w l ∧ V1 !!aw l ⊑ V2 !!aw l ∧
  V1 !!nr l ⊑ V2 !!nr l ∧ V1 !!ar l ⊑ V2 !!ar l.
Proof.
  rewrite {1}/sqsubseteq /lat_sqsubseteq /= /option_sqsubseteq.
  split.
  - destruct (V1 !! l) as [[]|] eqn:Eq1;
    destruct (V2 !! l) as [[]|] eqn:Eq2;
    simplify_view; cbn; try done.
  - destruct (V1 !! l) as [[]|] eqn:Eq1;
    destruct (V2 !! l) as [[]|] eqn:Eq2;
    simplify_view; cbn; try done. intuition.
Qed.


Global Instance twrite_sqsubseteq_proper: Proper (sqsubseteq ==> sqsubseteq) twrite.
Proof. solve_proper. Qed.

Global Instance tawrite_sqsubseteq_proper: Proper (sqsubseteq ==> sqsubseteq) tawrite.
Proof. by intros [][] [?[?[]]]. Qed.

Global Instance tnread_sqsubseteq_proper: Proper (sqsubseteq ==> sqsubseteq) tnread.
Proof. by intros [][] [?[?[]]]. Qed.

Global Instance taread_sqsubseteq_proper: Proper (sqsubseteq ==> sqsubseteq) taread.
Proof. by intros [][] [?[?[]]]. Qed.
