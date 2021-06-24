(** * Distributivity of a Function and a Unary Operation and a Binary Operation over a Binary Operation *)

From Maniunfold.Has Require Export
  Negation Addition Multiplication.
From Maniunfold.ShouldHave Require Import
  ArithmeticNotations.

(** This has the same shape as [opp_add_distr]. *)

Class IsDistrUnOp (A : Type) (Hf : HasNeg A) (Hk : HasAdd A) : Prop :=
  distr_un_op (x y : A) : - (x + y) = (- x) + (- y).

Class IsDistrFn (A B : Type) (f : A -> B)
  (Hk : HasAdd A) (Hm : HasAdd B) : Prop :=
  distr_fn (x y : A) : f (x + y) = f x + f y.

Class IsAntidistrUnOp (A : Type) (Hf : HasNeg A) (Hk : HasAdd A) : Prop :=
  antidistr_un_op (x y : A) : - (x + y) = (- y) + (- x).

Class IsAntidistrFn (A B : Type) (f : A -> B)
  (Hk : HasAdd A) (Hm : HasAdd B) : Prop :=
  antidistr_fn (x y : A) : f (x + y) = f y + f x.

(** This has the same shape as [mul_add_distr_l]. *)

Class IsDistrL (A : Type) (Hk : HasMul A) (Hm : HasAdd A) : Prop :=
  distr_l (x y z : A) : x * (y + z) = x * y + x * z.

(** This has the same shape as [mul_add_distr_r]. *)

Class IsDistrR (A : Type) (Hk : HasMul A) (Hm : HasAdd A) : Prop :=
  distr_r (x y z : A) : (x + y) * z = x * z + y * z.

Class IsDistr (A : Type) (Hk : HasMul A) (Hm : HasAdd A) : Prop := {
  is_distr_l :> IsDistrL _*_ _+_;
  is_distr_r :> IsDistrR _*_ _+_;
}.

Section Context.

Context (A : Type) (Hf : HasNeg A) (Hk : HasAdd A).

#[local] Instance is_distr_fn `(!IsDistrUnOp -_ _+_) :
  IsDistrFn -_ _+_ _+_.
Proof. intros x y. apply distr_un_op. Qed.

#[local] Instance is_antidistr_fn `(!IsAntidistrUnOp -_ _+_) :
  IsAntidistrFn -_ _+_ _+_.
Proof. intros x y. apply antidistr_un_op. Qed.

End Context.

#[export] Hint Resolve is_distr_fn is_antidistr_fn : typeclass_instances.
