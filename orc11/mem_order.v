From orc11 Require Export base.

Require Import stdpp.options.

Inductive memOrder := | NonAtomic | Relaxed | AcqRel | SeqCst .

Definition memOrder_le : relation memOrder :=
  λ o1 o2,
    match o1, o2 with
    | NonAtomic, _ => True
    | _, NonAtomic => False

    | Relaxed, _ => True
    | _, Relaxed => False

    | AcqRel, _ => True
    | _, AcqRel => False

    | SeqCst, SeqCst => True
    end.

Global Instance memOrder_dec : EqDecision memOrder.
Proof. solve_decision. Defined.

Global Instance memOrder_countable : Countable memOrder.
Proof.
  refine(inj_countable'
    (λ v, match v with
          | NonAtomic => 0 | Relaxed => 1 | AcqRel => 2 | SeqCst => 3
          end)
    (λ x, match x with
          | 0 => NonAtomic | 1 => Relaxed | 2 => AcqRel | _ => SeqCst
          end) _); by intros [].
Qed.

Global Instance memOrder_le_dec : RelDecision memOrder_le.
Proof. move => [] []; firstorder. Defined.

Program Canonical Structure memOrder_Lat :=
  Make_Lat memOrder (=) memOrder_le
     (λ o1 o2, if (decide (memOrder_le o1 o2)) then o2 else o1)
     (λ o1 o2, if (decide (memOrder_le o1 o2)) then o1 else o2)
     _ _ _ _ _ _ _ _ _ _ _ _ _.
Next Obligation. repeat constructor. Qed.
Next Obligation. split; [move=>[]//|move=>[][]//[]//]. Qed.
Next Obligation. move=>[][]//. Qed.
Next Obligation. move=>[][]//. Qed.
Next Obligation. move=>[][]//. Qed.
Next Obligation. move=>[][][]//. Qed.
Next Obligation. move=>[][]//. Qed.
Next Obligation. move=>[][]//. Qed.
Next Obligation. move=>[][][]//. Qed.
