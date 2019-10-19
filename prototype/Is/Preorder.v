From Maniunfold.Has Require Export
  EquivalenceRelation OrderRelation.
From Maniunfold.Is Require Export
  Proper Reflexive Transitive.

Class IsPreorder {A : Type} {has_eqv : HasEqv A}
  (has_ord : HasOrd A) : Prop := {
  ord_is_proper :> IsProper (eqv ==> eqv ==> flip impl) ord;
  ord_is_reflexive :> IsReflexive ord;
  ord_is_transitive :> IsTransitive ord;
}.

Section Context.

Context {A : Type} `{is_preorder : IsPreorder A}.

Global Instance ord_pre_order : PreOrder ord | 0 := {}.

End Context.
