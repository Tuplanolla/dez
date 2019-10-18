From Maniunfold.Has Require Export
  EquivalenceRelation GroupOperation GroupIdentity GroupInverse.
From Maniunfold.Is Require Export
  Group Commutative.

Class IsAbelianGroup {A : Type} {has_eqv : HasEqv A}
  (has_opr : HasOpr A) (has_idn : HasIdn A) (has_inv : HasInv A) : Prop := {
  abelian_group_opr_idn_inv_is_group :> IsGroup opr idn inv;
  abelian_group_opr_is_commutative :> IsCommutative opr;
}.
