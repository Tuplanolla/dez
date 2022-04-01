(** * Coherence *)

From DEZ Require Export
  Init.

(** ** Coherent Equality Relation,
    Order Relation and Strict Order Relation *)

Class IsCohRels (A : Type) (Xeq Xle Xlt : A -> A -> Prop) : Prop :=
  coh_rels (x y : A) : Xle x y <-> Xeq x y \/ Xlt x y.

(** This has the same shape as [Z.le_neq]. *)

Class IsCohRels' (A : Type) (Xeq Xle Xlt : A -> A -> Prop) : Prop :=
  coh_rels' (x y : A) : Xlt x y <-> Xle x y /\ ~ Xeq x y.
