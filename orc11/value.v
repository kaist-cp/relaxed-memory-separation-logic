From orc11 Require Export base.

Require Import stdpp.options.

Section Val.

  Context `{Countable VAL}.
  Inductive val  := | AVal | DVal | VVal (v : VAL).

  Inductive isval : ∀ (v : val), Prop := val_is_val v : isval (VVal v).

  Lemma NEqADVal : AVal ≠ DVal. Proof. congruence. Qed.

  Global Instance val_dec_eq : EqDecision val.
  Proof using All. solve_decision. Qed.

  Global Instance val_inhabited : Inhabited val := populate AVal.

  Section ValCount.
    Definition _val_to_sum (v : val): _ :=
      match v with
      | AVal => inl ()
      | DVal => inr (inl ())
      | VVal v => inr (inr v)
      end.
    Definition _sum_to_val s : val :=
      match s with
      | inl () => AVal
      | inr (inl ()) => DVal
      | inr (inr v) => VVal v
      end.
  End ValCount.

  Global Instance val_countable : Countable val.
  Proof. refine (inj_countable _val_to_sum (Some ∘ _sum_to_val) _); by intros []. Qed.
End Val.
