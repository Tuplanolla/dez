From Maniunfold.Has Require Export
  BinaryOperation NullaryOperation.
From Maniunfold.Is Require Export
  OneSorted.CommutativeRing TwoSorted.LeftModule TwoSorted.LeftBilinear.
From Maniunfold.ShouldHave Require Import
  OneSorted.ArithmeticNotations TwoSorted.MultiplicativeNotations.

(** This is a nonunital nonassociative left algebra over a commutative ring;
    the magma of algebralikes. *)

(** TODO Should probably use a homogeneous bimodule here,
    because chiral algebras are heresy. *)

Class IsLAlg (A B : Type)
  (A_has_add : HasAdd A) (A_has_zero : HasZero A) (A_has_neg : HasNeg A)
  (A_has_mul : HasMul A) (A_has_one : HasOne A)
  (B_has_add : HasAdd B) (B_has_zero : HasZero B) (B_has_neg : HasNeg B)
  (B_has_bin_op : HasBinOp B) (A_B_has_l_act : HasLAct A B) : Prop := {
  add_zero_neg_mul_one_is_comm_ring :>
    IsCommRing (A := A) add zero neg mul one;
  add_zero_neg_mul_one_add_zero_neg_l_act_is_l_mod :>
    IsLMod A B add zero neg mul one add zero neg l_act;
  add_zero_neg_mul_one_add_zero_neg_l_act_r_act_bin_op_is_bilin_op :>
    IsBilinOp A B add zero neg mul one
    add zero neg l_act (flip l_act) bin_op;
}.

(** This is a nonunital associative left algebra over a commutative ring;
    the semigroup of algebralikes. *)

Class IsAssocLAlg (A B : Type)
  (A_has_add : HasAdd A) (A_has_zero : HasZero A) (A_has_neg : HasNeg A)
  (A_has_mul : HasMul A) (A_has_one : HasOne A)
  (B_has_add : HasAdd B) (B_has_zero : HasZero B) (B_has_neg : HasNeg B)
  (B_has_bin_op : HasBinOp B) (A_B_has_l_act : HasLAct A B) : Prop := {
  add_zero_neg_mul_one_add_zero_neg_mul_one_l_act_is_l_alg :>
    IsLAlg A B add zero neg mul one add zero neg bin_op l_act;
  (** TODO Them [prop]s. *)
  prop_0 : forall (a b : A) (x : B), a L* (b L* x) = (a * b) L* x;
}.

(** This is a associative unital left algebra over a commutative ring;
    the monoid of algebralikes. *)

Class IsAssocUnlLAlg (A B : Type)
  (A_has_add : HasAdd A) (A_has_zero : HasZero A) (A_has_neg : HasNeg A)
  (A_has_mul : HasMul A) (A_has_one : HasOne A)
  (B_has_add : HasAdd B) (B_has_zero : HasZero B) (B_has_neg : HasNeg B)
  (B_has_bin_op : HasBinOp B) (B_has_null_op : HasNullOp B)
  (A_B_has_l_act : HasLAct A B) : Prop := {
  add_zero_neg_mul_one_add_zero_neg_mul_one_l_act_is_assoc_l_alg :>
    IsAssocLAlg A B add zero neg mul one add zero neg bin_op l_act;
  (** TODO Them [prop]s. *)
  prop_1 : forall (a : A) (x y : B), a L* (x + y) = a L* x + a L* y;
  prop_2 : forall (a b : A) (x : B), (a + b) L* x = a L* x + b L* x;
  prop_3 : forall (x : B), 1 L* x = x;
  (** TODO This thing. *)
  unitality_thing : forall (x : B), bin_fn null_op x = x;
}.
