(** * Basic Logic *)

From Maniunfold Require Export
  Init.

Lemma f_nequal (A B : Type) (f : A -> B) (x y : A) (fxy : f x <> f y) : x <> y.
Proof. auto using f_equal. Qed.
