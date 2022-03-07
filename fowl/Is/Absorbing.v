(** * Absorptivity *)

From DEZ Require Export
  Init.

(** TODO This terminology is chirally confusing. *)

(** ** Left Absorbing Element of Right Action *)
(** ** Left Annihilating Element of Right Action *)

Class IsAbsorbElemActL (A B : Type) (X : B -> B -> Prop)
  (a : B) (ar : B -> A -> B) : Prop :=
  absorb_elem_act_l (x : A) : X (ar a x) a.

(** ** Right Absorbing Element of Left Action *)
(** ** Right Annihilating Element of Left Action *)

Class IsAbsorbElemActR (A B : Type) (X : B -> B -> Prop)
  (a : B) (al : A -> B -> B) : Prop :=
  absorb_elem_act_r (x : A) : X (al x a) a.

(** ** Left Absorbing Element of Binary Operation *)
(** ** Left Annihilating Element of Binary Operation *)

Class IsAbsorbElemL (A : Type) (X : A -> A -> Prop)
  (x : A) (k : A -> A -> A) : Prop :=
  absorb_elem_l (y : A) : X (k x y) x.

(** ** Right Absorbing Element of Binary Operation *)
(** ** Right Annihilating Element of Binary Operation *)

Class IsAbsorbElemR (A : Type) (X : A -> A -> Prop)
  (x : A) (k : A -> A -> A) : Prop :=
  absorb_elem_r (y : A) : X (k y x) x.

(** ** Absorbing Element of Binary Operation *)

Class IsAbsorbElem (A : Type) (X : A -> A -> Prop)
  (x : A) (k : A -> A -> A) : Prop := {
  absorb_elem_is_absorb_elem_l :> IsAbsorbElemL X x k;
  absorb_elem_is_absorb_elem_r :> IsAbsorbElemR X x k;
}.

(** TODO Unary absorptivity is just a fixed point of a unary operation! *)
