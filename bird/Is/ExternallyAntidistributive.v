From Maniunfold.Has Require Export
  BinaryRelation BinaryOperation UnaryOperation.
From Maniunfold.ShouldHave Require Import
  BinaryRelationNotations AdditiveNotations.

(** TODO The following is the most general type.
    It is probably more general than we want for "externality".

<<
forall (e : F -> F -> Prop) (f : A -> B -> C) (g : D -> E -> F)
  (h : C -> F) (k : B -> D) (m : A -> E) (x : A) (y : B),
  e (h (f x y)) (g (k y) (m x))
>>
*)

Class IsExtAntidistr {A : Type} {has_bin_rel : HasBinRel A}
  (has_bin_op : HasBinOp A) (has_un_op : HasUnOp A) : Prop :=
  ext_antidistr : forall x y : A, T- (x T+ y) ~~ T- y T+ T- x.
