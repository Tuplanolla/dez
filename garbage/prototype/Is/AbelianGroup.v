From DEZ.Has Require Export
  EquivalenceRelation GroupOperation GroupIdentity GroupInverse.
From DEZ.Is Require Export
  Group Commutative.

Class IsAbelianGroup {A : Type} {has_eqv : HasEqv A}
  (has_opr : HasOpr A) (has_idn : HasIdn A) (has_inv : HasInv A) : Prop := {
  opr_idn_inv_is_group :> IsGroup opr idn inv;
  opr_is_commutative :> IsCommutative opr;
}.
