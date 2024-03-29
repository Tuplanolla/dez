(** * Categorical Operations *)

From DEZ.Has Require Export
  CategoricalRelations.
From DEZ.Supports Require Import
  CategoricalRelationNotations.

(** ** Identity Morphism *)

Class HasIdHom (A : Type) {X : HasHom A} : Type :=
  id_hom (x : A) : x --> x.

Arguments HasIdHom _ {_}.

#[export] Typeclasses Transparent HasIdHom.

(** ** Inverse Morphism *)

Class HasInvHom (A : Type) {X : HasHom A} : Type :=
  inv_hom (x y : A) (a : x --> y) : y --> x.

Arguments HasInvHom _ {_}.

#[export] Typeclasses Transparent HasInvHom.

(** ** Composed Morphism *)

Class HasCompHom (A : Type) {X : HasHom A} : Type :=
  comp_hom (x y z : A) (a : y --> z) (b : x --> y) : x --> z.

Arguments HasCompHom _ {_}.

#[export] Typeclasses Transparent HasCompHom.
