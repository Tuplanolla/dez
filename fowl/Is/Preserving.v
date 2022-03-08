(** * Preservation *)

From DEZ.Is Require Export
  Distributive.

(** ** Function Preserving Nullary Operation *)

Class IsNullPres (A B : Type) (X : B -> B -> Prop)
  (x : A) (y : B) (f : A -> B) : Prop :=
  null_pres : X (f x) y.
  (* >: IsFixed *)

(** ** Function Preserving Unary Operation *)

Class IsUnPres (A B : Type) (X : B -> B -> Prop)
  (f : A -> A) (g : B -> B) (h : A -> B) : Prop :=
  un_pres (x : A) : X (h (f x)) (g (h x)).
  (* =: IsComm *)

(** ** Function Preserving Binary Operation *)

Class IsBinPres (A B : Type) (X : B -> B -> Prop)
  (k : A -> A -> A) (m : B -> B -> B) (f : A -> B) : Prop :=
  bin_pres (x y : A) : X (f (k x y)) (m (f x) (f y)).
  (* <: IsDistrFns *)
