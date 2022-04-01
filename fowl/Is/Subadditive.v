(** * Subadditivity *)

From DEZ Require Export
  Init.

(** ** Subadditive Form *)
(** ** Triangle Inequality *)

Class IsSubaddForm (A B : Type) (X : A -> A -> Prop)
  (k : A -> A -> A) (s : B -> B -> A) : Prop :=
  subadd_form (a b c : B) : X (s a c) (k (s a b) (s b c)).
