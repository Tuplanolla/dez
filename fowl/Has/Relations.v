(** * Relations *)

From DEZ Require Export
  Init.

(** ** Nullary Relation *)

Class HasNullRel (A : Type) : Type := null_rel : Prop.

#[export] Typeclasses Transparent HasNullRel.

(** * Unary Relation *)

Class HasUnRel (A : Type) : Type := un_rel (x : A) : Prop.

#[export] Typeclasses Transparent HasUnRel.

(** * Binary Relations *)

Class HasBinRel (A : Type) : Type := bin_rel (x y : A) : Prop.

#[export] Typeclasses Transparent HasBinRel.
