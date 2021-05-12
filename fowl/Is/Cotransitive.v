(* bad *)
From Maniunfold.Has Require Export
  OneSortedBinaryRelation.
From Maniunfold.ShouldHave Require Import
  OneSortedBinaryRelationNotations.

Class IsCotrans (A : Type) `(HasBinRel A) : Prop :=
  cotrans : forall x y z : A, x ~~ y -> x ~~ z \/ y ~~ z.
