(** * Coherence *)

From DEZ Require Export
  Init.

(** ** Coherent Equality Relation, Order Relation and Strict Order Relation *)

(** This has the same shape as [Z.le_lteq] and [Z.lt_eq_cases]. *)

Class IsCohRels (A : Type) (Xeq Xle Xlt : A -> A -> Prop) : Prop :=
  coh_rels (x y : A) : Xle x y <-> Xlt x y \/ Xeq x y.
