(* bad *)
From Maniunfold.Has Require Export
  OneSorted.BinaryRelation.
From Maniunfold.ShouldHave Require Import
  OneSorted.BinaryRelationNotations.

Class IsCotrans (A : Type) `(HasBinRel A) : Prop :=
  cotrans : forall x y z : A, x ~~ y -> x ~~ z \/ y ~~ z.
