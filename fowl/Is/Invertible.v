(** * Invertibility *)

From DEZ Require Export
  Init.

(** ** Left Inverse of a Binary Function *)

Class IsInvL (A B C D : Type) (R : D -> B -> Prop)
  (x : B) (f : A -> C) (k : C -> A -> D) : Prop :=
  inv_l (y : A) : R (k (f y) y) x.

(** ** Right Inverse of a Binary Function *)

Class IsInvR (A B C D : Type) (R : D -> B -> Prop)
  (x : B) (f : A -> C) (k : A -> C -> D) : Prop :=
  inv_r (y : A) : R (k y (f y)) x.

(** ** Inverse of a Torsion *)

Class IsInvLR2 (A B C : Type) (R : B -> B -> Prop)
  (x : B) (f : A -> C) (k : C -> A -> B) (m : A -> C -> B) : Prop := {
  is_inv_l :> IsInvL R x f k;
  is_inv_r :> IsInvR R x f m;
}.

(** ** Inverse of a Binary Operation *)

Class IsInvLR (A : Type) (R : A -> A -> Prop)
  (x : A) (f : A -> A) (k : A -> A -> A) : Prop :=
  is_inv_l_r_2 :> IsInvLR2 R x f k k.
