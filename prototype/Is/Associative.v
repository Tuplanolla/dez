From Maniunfold.Has Require Export
  EquivalenceRelation GroupOperation.
From Maniunfold.Is Require Export
  Setoid.

Import AdditiveNotations.

Class IsAssociative {A : Type} {has_eqv : HasEqv A}
  (has_opr : HasOpr A) : Prop := {
  associative_eqv_is_setoid :> IsSetoid eqv;
  associative : forall x y z : A, x + (y + z) == (x + y) + z;
}.

(** TODO Heterogeneous predicates as superclasses
    of the corresponding homogeneous classes.
    Perhaps generalize multiplication and scalar multiplication
    to homogeneous and chiral multiplication. *)

(*
Class IsBiassociative {A : Type} {has_eqv : HasEqv A}
  (has_lopr : HasLOpr A) (has_ropr : HasROpr A) : Prop := {
  biassociative_is_setoid :> IsSetoid eqv;
  biassociative : forall x y z : A, x <+ (y +> z) == (x <+ y) +> z;
}.
*)
