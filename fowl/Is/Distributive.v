(** * Distributivity *)

From DEZ.Has Require Export
  BinaryOperation Addition Multiplication.
From DEZ.ShouldHave Require
  AdditiveNotations ArithmeticNotations.

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
