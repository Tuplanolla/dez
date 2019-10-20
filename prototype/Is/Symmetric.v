From Coq Require Export
  Setoid.
From Maniunfold.Has Require Export
  Relation.

(** TODO This definition is not quite as nice as that for commutativity,
    since `->` is not a symmetric relation,
    but we can trivially generalize to `<->`. *)

Class IsSymmetric {A : Type} (has_rel : HasRel A) : Prop :=
  symmetric : forall x y : A, x ~ y -> y ~ x.

Section Context.

Context {A : Type} `{is_symmetric : IsSymmetric A}.

Global Instance rel_symmetric : Symmetric rel | 0 := symmetric.

End Context.
