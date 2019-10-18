From Maniunfold.Has Require Export
  Relation EquivalenceRelation.

Delimit Scope order_relation_scope with order_relation.

Open Scope order_relation_scope.

Class HasOrd (A : Type) : Type := ord : A -> A -> Prop.

Typeclasses Transparent HasOrd.

Notation "x '<=' y" := (ord x y) : order_relation_scope.

Notation "x '<' y" := (x <= y /\ x =/= y) : order_relation_scope.

Global Instance ord_has_rel {A : Type} {has_ord : HasOrd A} : HasRel A := ord.
