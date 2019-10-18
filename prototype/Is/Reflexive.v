From Coq Require Export
  Setoid.
From Maniunfold.Has Require Export
  Relation.

Class IsReflexive {A : Type} (has_rel : HasRel A) : Prop :=
  reflexive : forall x : A, x ~ x.

Section Context.

Context {A : Type} `{is_reflexive : IsReflexive A}.

Global Instance reflexive_is_reflexive : Reflexive rel | 0 := reflexive.

End Context.
