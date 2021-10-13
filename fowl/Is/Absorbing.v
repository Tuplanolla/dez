(** * Absorptivity *)

From DEZ Require Export
  Init.

(** ** Left Absorbing Element of a Binary Operation *)

Class IsAbsorbElemL (A : Type) (R : A -> A -> Prop)
  (x : A) (k : A -> A -> A) : Prop :=
  absorb_elem_l (y : A) : R (k x y) x.

(** ** Right Absorbing Element of a Binary Operation *)

Class IsAbsorbElemR (A : Type) (R : A -> A -> Prop)
  (x : A) (k : A -> A -> A) : Prop :=
  absorb_elem_r (y : A) : R (k y x) x.

(** ** Absorbing Element of a Binary Operation *)

Class IsAbsorbElemLR (A : Type) (R : A -> A -> Prop)
  (x : A) (k : A -> A -> A) : Prop := {
  is_absorb_elem_l :> IsAbsorbElemL R x k;
  is_absorb_elem_r :> IsAbsorbElemR R x k;
}.

(** TODO Unary absorptivity is just a fixed point of a unary operation! *)
