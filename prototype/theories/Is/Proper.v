From Coq Require Export
  Setoid Morphisms.
From Maniunfold.Has Require Export
  BinaryRelation Unit.
From Maniunfold.ShouldHave Require Import
  BinaryRelationNotations.

Class IsProper {A : Type}
  (has_bin_rel : HasBinRel A) (has_un : HasUn A) : Prop :=
  proper : un ~~ un.

Section Context.

Context {A : Type} `{is_proper : IsProper A}.

Global Instance bin_rel_un_proper : Proper bin_rel un | 0 := proper.

End Context.
