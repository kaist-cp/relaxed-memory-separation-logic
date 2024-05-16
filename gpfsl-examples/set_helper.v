From stdpp Require Import sets gmap.

Require Import iris.prelude.options.

Section set_seq.
  Context {A : Type}.

  Definition to_set (E : list A) : gset nat := set_seq O (length E).

  Lemma to_set_empty E : to_set E = ∅ ↔ E = [].
  Proof. unfold to_set. destruct E; [done|simpl; set_solver]. Qed.

  (* TODO ugly proof *)
  Lemma to_set_singleton E e : to_set E = {[e]} ↔ e = O ∧ length E = 1%nat.
  Proof.
    unfold to_set. split.
    - destruct E as [|e' E].
      + simpl; set_solver.
      + rewrite cons_length, set_seq_S_end_union_L. destruct E; simpl.
        * rewrite (right_id_L _ _). set_solver.
        * intros Eqe.
          assert (Eq1 : S (length E) ∈ ({[e]} : gset _)).
          { rewrite <-Eqe. set_solver-. }
          assert (Eq2 : O ∈ ({[e]} : gset _)).
          { rewrite <-Eqe. set_solver-. }
          set_solver.
    - intros [-> ->]. by rewrite set_seq_S_end_union_L, (right_id_L _ _).
  Qed.

  Lemma to_set_append E e : to_set (E ++ [e]) = {[ length E ]} ∪ to_set E.
  Proof.
    unfold to_set. by rewrite app_length, Nat.add_1_r, set_seq_S_end_union_L.
  Qed.
End set_seq.
