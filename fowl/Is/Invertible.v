(** * Invertibility *)

From DEZ Require Export
  Init.

(** ** Left Inverse of a Binary Function *)

Class IsInvL (A B C : Type) (x : A) (f : C -> B) (k : B -> C -> A) : Prop :=
  inv_l (y : C) : k (f y) y = x.

(** ** Right Inverse of a Binary Function *)

Class IsInvR (A B C : Type) (x : A) (f : C -> B) (k : C -> B -> A) : Prop :=
  inv_r (y : C) : k y (f y) = x.

(** ** Inverse of a Torsion *)

Class IsInvLR2 (A B C : Type)
  (x : A) (f : C -> B) (k : B -> C -> A) (m : C -> B -> A) : Prop := {
  is_inv_l :> IsInvL x f k;
  is_inv_r :> IsInvR x f m;
}.

(** ** Inverse of a Binary Operation *)

Class IsInvLR (A : Type) (x : A) (f : A -> A) (k : A -> A -> A) : Prop :=
  is_inv_l_r_2 :> IsInvLR2 x f k k.
