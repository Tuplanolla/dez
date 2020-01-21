From Coq Require Export
  Setoid Morphisms.
From Maniunfold.Has Require Export
  BinaryRelation.
From Maniunfold.ShouldHave Require Import
  BinaryRelationNotations.

Class IsTrans {A : Type} (has_bin_rel : HasBinRel A) : Prop :=
  trans : forall x y z : A, x ~~ y -> y ~~ z -> x ~~ z.

Section Context.

Context {A : Type} `{is_trans : IsTrans A}.

Global Instance bin_rel_transitive : Transitive bin_rel | 0.
Proof. intros x y z. apply trans. Qed.

End Context.
