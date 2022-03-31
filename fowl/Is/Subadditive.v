(** * Subadditivity *)

From DEZ Require Export
  Init.

(** ** Subadditive Binary Relation *)
(** ** Triangle Inequality *)

Class IsSubadd (A B : Type) (X : A -> A -> Prop)
  (k : A -> A -> A) (s : B -> B -> A) : Prop :=
  subadd (a b c : B) : X (s a c) (k (s a b) (s b c)).
