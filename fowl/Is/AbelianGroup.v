(** * Abelian Group Structure *)

From DEZ.Has Require Export
  NullaryOperation UnaryOperation BinaryOperation.
From DEZ.Is Require Export
  Commutative Group Distributive.
From DEZ.ShouldHave Require Import
  AdditiveNotations.

(** ** Abelian Group *)
(** ** Commutative Group *)

Class IsAbGrp (A : Type) (X : A -> A -> Prop)
  (x : A) (f : A -> A) (k : A -> A -> A) : Prop := {
  is_comm :> IsComm R k;
  is_grp :> IsGrp R x f k;
}.

Section Context.

Context (A : Type) (X : A -> A -> Prop)
  (x : A) (f : A -> A) (k : A -> A -> A)
  `(!IsAbGrp R x f k).

#[local] Instance is_distr : IsDistr R f k k.
Proof.
  intros y z.
  setoid_rewrite (comm y z).
  apply (antidistr z y). Qed.

End Context.

#[export] Hint Resolve is_distr : typeclass_instances.
