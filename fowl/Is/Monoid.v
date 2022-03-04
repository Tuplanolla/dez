(** * Monoidal Structure *)

From DEZ.Is Require Export
  Semigroup Unital.

(** ** Monoid *)

Class IsMon (A : Type) (X : A -> A -> Prop)
  (x : A) (k : A -> A -> A) : Prop := {
  mon_is_semigrp :> IsSemigrp X k;
  mon_is_unl :> IsUnl X x k;
}.

Section Context.

Context (A : Type) (X : A -> A -> Prop)
  (x : A) (k : A -> A -> A) `{!IsMon X x k}.

#[local] Instance mon_is_assoc : IsAssoc X k.
Proof. typeclasses eauto. Qed.

End Context.
