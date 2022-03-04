(** * Distributivity *)

From DEZ.Has Require Export
  Operations ArithmeticOperations.
From DEZ.Supports Require
  AdditiveNotations ArithmeticNotations.

Class IsDistr7 (A0 A1 B0 B1 B2 C0 C1 : Type) (X : C0 -> C1 -> Prop)
  (f : A0 -> B0) (g : A1 -> B1) (h : B2 -> C0)
  (k : A0 -> A1 -> B2) (m : B0 -> B1 -> C1) : Prop :=
  distr' (x : A0) (y : A1) : X (h (k x y)) (m (f x) (g y)).

Class IsDistr3 (A B : Type) (X : B -> B -> Prop)
  (f : A -> B) (k : A -> A -> A) (m : B -> B -> B) : Prop :=
  is_distr_7 :> IsDistr7 X f f f k m.

Class Proper'' (A B : Type) (X : A -> A -> Prop) (S : B -> B -> Prop)
  (f g : A -> B) : Prop :=
  is_distr_7'' :> IsDistr7 impl f g id X S.

Class IsInj' (A B : Type) (f : A -> B) : Prop :=
  is_distr_7' :> IsDistr7 (flip impl) f f id _=_ _=_.

Section Context.

Import AdditiveNotations.

Class IsDistr2 (A B : Type) (X : B -> B -> Prop) (f : A -> B)
  (Hk : HasBinOp A) (Hm : HasBinOp B) : Prop :=
  distr2 (x y : A) : X (f (x + y)) (f x + f y).

(** This has the same shape as [opp_add_distr]. *)

Class IsDistr (A : Type) (X : A -> A -> Prop) (f : A -> A)
  (Hk : HasBinOp A) : Prop :=
  distr (x y : A) : X (f (x + y)) (f x + f y).

Class IsAntidistr2 (A B : Type) (X : B -> B -> Prop) (f : A -> B)
  (Hk : HasBinOp A) (Hm : HasBinOp B) : Prop :=
  antidistr2 (x y : A) : X (f (x + y)) (f y + f x).

Class IsAntidistr (A : Type) (X : A -> A -> Prop) (f : A -> A)
  (Hk : HasBinOp A) : Prop :=
  antidistr (x y : A) : X (f (x + y)) (f y + f x).

End Context.

Section Context.

Import ArithmeticNotations.

(** This has the same shape as [mul_add_distr_l]. *)

Class IsDistrL (A : Type) (X : A -> A -> Prop)
  (Hk : HasMul A) (Hm : HasAdd A) : Prop :=
  distr_l (x y z : A) : X (x * (y + z)) (x * y + x * z).

(** This has the same shape as [mul_add_distr_r]. *)

Class IsDistrR (A : Type) (X : A -> A -> Prop)
  (Hk : HasMul A) (Hm : HasAdd A) : Prop :=
  distr_r (x y z : A) : X ((x + y) * z) (x * z + y * z).

Class IsDistrLR (A : Type) (X : A -> A -> Prop)
  (Hk : HasMul A) (Hm : HasAdd A) : Prop := {
  is_distr_l :> IsDistrL X _*_ _+_;
  is_distr_r :> IsDistrR X _*_ _+_;
}.

End Context.
