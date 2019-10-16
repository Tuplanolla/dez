(** This module is a bit awkward,
    because it tries to be compatible with the standard library morphisms. *)

From Coq Require Export
  Morphisms.
From Maniunfold.Has Require Export
  Relation.

Delimit Scope signature_scope with signature.

Open Scope signature_scope.

(** We use the standard library morphisms directly, because
    - they come with many useful instances and
    - they have better performance characteristics for type inference. *)

(* Class IsProper {A : Type} (has_rel : HasRel A) (x : A) : Prop :=
  proper : x ~ x. *)

Notation "'IsProper'" := Proper.
Notation "'proper'" := proper_prf.
