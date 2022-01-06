(* * Preservation of Properties *)

From DEZ Require Export
  Init.

(** ** Homomorphism Preserving Nullary Operations *)

Class IsNullPres (A B : Type) (X : B -> B -> Prop)
  (x : A) (y : B) (h : A -> B) : Prop :=
  null_pres : X (h x) y.

Class IsNullPres' (A B C : Type) (X : B -> C -> Prop)
  (x : A) (y : C) (h : A -> B) : Prop :=
  null_pres' : X (h x) y.

#[global] Instance is_null_pres (A B : Type) (X : B -> B -> Prop)
  (x : A) (y : B) (h : A -> B) `(!IsNullPres' X x y h) : IsNullPres X x y h.
Proof. apply null_pres'. Qed.

(** ** Homomorphism Preserving Unary Operations *)

Class IsUnPres (A B : Type) (X : B -> B -> Prop)
  (f : A -> A) (g : B -> B) (h : A -> B) : Prop :=
  un_pres (x : A) : X (h (f x)) (g (h x)).

(** ** Homomorphism Preserving Binary Operations *)

Class IsBinPres (A B : Type) (X : B -> B -> Prop)
  (k : A -> A -> A) (m : B -> B -> B) (h : A -> B) : Prop :=
  bin_pres (x y : A) : X (h (k x y)) (m (h x) (h y)).
