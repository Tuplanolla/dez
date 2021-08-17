(** * Distributivity *)

From DEZ.Has Require Export
  BinaryOperation Addition Multiplication.
From DEZ.ShouldHave Require
  AdditiveNotations ArithmeticNotations.

Class IsDistr7 (A0 A1 B0 B1 B2 C0 C1 : Type) (R : C0 -> C1 -> Prop)
  (f : A0 -> B0) (g : A1 -> B1) (h : B2 -> C0)
  (k : A0 -> A1 -> B2) (m : B0 -> B1 -> C1) : Prop :=
  distr' (x : A0) (y : A1) : R (h (k x y)) (m (f x) (g y)).

Class IsDistr2 (A B : Type) (R : B -> B -> Prop)
  (f : A -> B) (k : A -> A -> A) (m : B -> B -> B) : Prop :=
  is_distr_7 :> IsDistr7 R f f f k m.

Class Proper'' (A B : Type) (R : A -> A -> Prop) (S : B -> B -> Prop)
  (f g : A -> B) : Prop :=
  is_distr_7'' :> IsDistr7 impl f g id R S.

Class IsInj' (A B : Type) (f : A -> B) : Prop :=
  is_distr_7' :> IsDistr7 (flip impl) f f id _=_ _=_.

Section Context.

Import AdditiveNotations.

(** This has the same shape as [opp_add_distr]. *)

Class IsDistr (A B : Type) (f : A -> B)
  (Hk : HasBinOp A) (Hm : HasBinOp B) : Prop :=
  distr (x y : A) : f (x + y) = f x + f y.

Class IsAntidistr (A B : Type) (f : A -> B)
  (Hk : HasBinOp A) (Hm : HasBinOp B) : Prop :=
  antidistr (x y : A) : f (x + y) = f y + f x.

End Context.

Section Context.

Import ArithmeticNotations.

(** This has the same shape as [mul_add_distr_l]. *)

Class IsDistrL (A : Type) (Hk : HasMul A) (Hm : HasAdd A) : Prop :=
  distr_l (x y z : A) : x * (y + z) = x * y + x * z.

(** This has the same shape as [mul_add_distr_r]. *)

Class IsDistrR (A : Type) (Hk : HasMul A) (Hm : HasAdd A) : Prop :=
  distr_r (x y z : A) : (x + y) * z = x * z + y * z.

Class IsDistrLR (A : Type) (Hk : HasMul A) (Hm : HasAdd A) : Prop := {
  is_distr_l :> IsDistrL _*_ _+_;
  is_distr_r :> IsDistrR _*_ _+_;
}.

End Context.
