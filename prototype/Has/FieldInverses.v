From Maniunfold.Has Require Import GroupOperation GroupIdentity GroupInverse
  FieldOperations FieldIdentities.

Class HasNeg (A : Type) : Type := neg : A -> A.
Class HasRecip (A : Type) : Type := recip : A -> A.

Typeclasses Transparent HasNeg HasRecip.

Notation "'-' x" := (neg x) : field_scope.
Notation "x '-' y" := (add x (neg y)) : field_scope.
Notation "'/' x" := (recip x) : field_scope.
Notation "x '/' y" := (mul x (recip y)) : field_scope.

Instance neg_has_inv {A : Type} {has_neg : HasNeg A} : HasInv A := neg.
Instance recip_has_inv {A : Type} {has_recip : HasRecip A} : HasInv A := recip.
