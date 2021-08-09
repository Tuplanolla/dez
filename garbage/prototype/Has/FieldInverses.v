From DEZ.Has Require Export
  GroupOperation GroupIdentity GroupInverse FieldOperations FieldIdentities.

Class HasNeg (A : Type) : Type := neg : A -> A.
Class HasRecip (A : Type) : Type := recip : A -> A.

Typeclasses Transparent HasNeg HasRecip.

Global Instance neg_has_inv {A : Type} {has_neg : HasNeg A} : HasInv A := neg.
Global Instance recip_has_inv {A : Type} {has_recip : HasRecip A} : HasInv A := recip.
