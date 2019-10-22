From Maniunfold.Has Require Export
  Endomorphism GroupOperation GroupIdentity.

Class HasInv (A : Type) : Type := inv : A -> A.

Typeclasses Transparent HasInv.

Global Instance inv_has_endo {A : Type} {has_inv : HasInv A} : HasEndo A := inv.
