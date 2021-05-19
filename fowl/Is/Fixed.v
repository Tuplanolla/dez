From Maniunfold.Has Require Export
  Endofunction Point.

Class IsFixed (A : Type) `(HasPt A) `(HasEndo A) : Prop :=
  fixed : fn pt = pt.
