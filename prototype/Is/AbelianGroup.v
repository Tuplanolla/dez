From Maniunfold.Has Require Import EquivalenceRelation
  GroupOperation GroupIdentity GroupInverse.
From Maniunfold.Is Require Import Group Identifiable.

Class IsAbelianGroup (A : Type) {has_eqv : HasEqv A}
  {has_opr : HasOpr A} {has_idn : HasIdn A} {has_inv : HasInv A} : Prop := {
  opr_is_group :> IsGroup A;
  opr_is_identifiable :> IsIdentifiable A;
}.
