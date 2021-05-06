From Maniunfold.Has Require Export
  OrderRelation StrictOrderRelation.

Class HasOrdRelPack (A : Type) `(HasOrdRel A) `(HasStrictOrdRel A) : Type :=
  ord_rel_pack : unit.

#[export] Hint Transparent HasOrdRelPack : typeclass_instances.
