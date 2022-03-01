(** * Properness and Respectfulness *)

From DEZ Require Export
  Init.

(** ** Proper Relation *)
(** ** Respectful Morphism *)

Fail Fail Class IsProper (A : Type) (X : A -> A -> Prop) : Prop :=
  proper (x : A) : X x x.

Arguments proper_prf {_ _} _ {_}.

Notation IsProper := Proper.
Notation proper := proper_prf.
