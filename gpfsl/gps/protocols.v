From orc11 Require Export base.

Record protocolT : Type := {
  pr_stateT     :> Type;
  pr_inhab      : Inhabited pr_stateT;
  pr_eqdec      : EqDecision pr_stateT;
  pr_count      : Countable pr_stateT;
  pr_steps      : SqSubsetEq pr_stateT;
  pr_steps_pre  : PreOrder (⊑@{pr_stateT});
}.

Global Existing Instances pr_inhab pr_eqdec pr_count pr_steps pr_steps_pre.

Definition unitProtocol : protocolT := Build_protocolT unit _ _ _ (λ _ _, True) _.
Definition boolProtocol : protocolT :=  Build_protocolT bool _ _ _ bool_le _.
Definition natProtocol : protocolT :=  Build_protocolT nat _ _ _ le _.

Definition gsetProtocol (K: Type) `{Countable K} : protocolT :=
  Build_protocolT (gset K) _ _ _ (⊆) _.

Definition listProtocol (A: Type) `{Countable A} : protocolT :=
  Build_protocolT (list A) _ _ _ prefix _.
