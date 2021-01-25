(** * Basic logic. *)

From Maniunfold Require Import
  Init.

Lemma f_nequal (A B : Type) (f : A -> B) (x y : A) (fxy : f x <> f y) : x <> y.
Proof. auto using f_equal. Qed.
