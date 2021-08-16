(** * Associativity and Compatibility *)

From DEZ Require Export
  Init.

(** ** Associative Binary Functions *)

Class IsAssoc7 (A0 A1 A2 B0 B1 C0 C1 : Type) (R : C0 -> C1 -> Prop)
  (k : A0 -> A1 -> B0) (m : A1 -> A2 -> B1)
  (n : A0 -> B1 -> C0) (p : B0 -> A2 -> C1) : Prop :=
  assoc (x : A0) (y : A1) (z : A2) : R (n x (m y z)) (p (k x y) z).

(** ** Left Action Compatible with a Binary Operation *)

Class IsCompatL (A B : Type) (R : B -> B -> Prop)
  (k : A -> A -> A) (m : A -> B -> B) : Prop :=
  l_is_assoc_7 :> IsAssoc7 R m m m k.

(** ** Right Action Compatible with a Binary Operation *)

Class IsCompatR (A B : Type) (R : B -> B -> Prop)
  (k : A -> A -> A) (m : B -> A -> B) : Prop :=
  r_is_assoc_7 :> IsAssoc7 R m k m m.

(** ** Associative Actions *)

Class IsAssoc3 (A B C : Type) (R : B -> B -> Prop)
  (k : A -> B -> B) (m : B -> C -> B) : Prop :=
  is_assoc_7 :> IsAssoc7 R k m m k.

(** ** Associative Binary Operation *)

(** This has the same shape as [mul_assoc]. *)

Class IsAssoc (A : Type) (R : A -> A -> Prop) (k : A -> A -> A) : Prop :=
  is_assoc_3 :> IsAssoc3 R k k.
