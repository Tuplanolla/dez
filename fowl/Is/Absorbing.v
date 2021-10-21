(** * Absorptivity *)

From DEZ Require Export
  Init.

Module Superclass.

Class IsAbsorbElemL3 (A0 A1 B : Type) (X : B -> A0 -> Prop)
  (x : A0) (k : A0 -> A1 -> B) : Prop :=
  absorb_elem_l (y : A1) : X (k x y) x.

Class IsAbsorbElemR3 (A0 A1 B : Type) (X : B -> A0 -> Prop)
  (x : A0) (k : A1 -> A0 -> B) : Prop :=
  absorb_elem_r (y : A1) : X (k y x) x.

End Superclass.

(** ** Left Absorbing Element of a Binary Operation *)

Class IsAbsorbElemL (A : Type) (X : A -> A -> Prop)
  (x : A) (k : A -> A -> A) : Prop :=
  absorb_elem_l (y : A) : X (k x y) x.

(** ** Right Absorbing Element of a Binary Operation *)

Class IsAbsorbElemR (A : Type) (X : A -> A -> Prop)
  (x : A) (k : A -> A -> A) : Prop :=
  absorb_elem_r (y : A) : X (k y x) x.

(** ** Absorbing Element of a Binary Operation *)

Class IsAbsorbElemLR (A : Type) (X : A -> A -> Prop)
  (x : A) (k : A -> A -> A) : Prop := {
  is_absorb_elem_l :> IsAbsorbElemL X x k;
  is_absorb_elem_r :> IsAbsorbElemR X x k;
}.

(** TODO Unary absorptivity is just a fixed point of a unary operation! *)
