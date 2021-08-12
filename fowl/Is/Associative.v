(** * Associativity and Compatibility *)

From DEZ Require Export
  Init.

(** ** Associative Binary Functions *)

Class IsAssoc4 (A B C D E F G : Type) (R : F -> G -> Prop)
  (k : A -> D -> F) (m : B -> C -> D)
  (n : E -> C -> G) (p : A -> B -> E) : Prop :=
  assoc (x : A) (y : B) (z : C) : R (k x (m y z)) (n (p x y) z).

(** ** Left Action Compatible with a Binary Operation *)

Class IsCompatL (A B : Type) (R : B -> B -> Prop)
  (k : A -> A -> A) (m : A -> B -> B) : Prop :=
  l_is_assoc_4 :> IsAssoc4 R m m m k.

(** ** Right Action Compatible with a Binary Operation *)

Class IsCompatR (A B : Type) (R : B -> B -> Prop)
  (k : A -> A -> A) (m : B -> A -> B) : Prop :=
  r_is_assoc_4 :> IsAssoc4 R m k m m.

(** ** Associative Actions *)

Class IsAssoc2 (A B C : Type) (R : B -> B -> Prop)
  (k : A -> B -> B) (m : B -> C -> B) : Prop :=
  is_assoc_4 :> IsAssoc4 R k m m k.

(** ** Associative Binary Operation *)

(** This has the same shape as [mul_assoc]. *)

Class IsAssoc (A : Type) (R : A -> A -> Prop) (k : A -> A -> A) : Prop :=
  is_assoc_2 :> IsAssoc2 R k k.
