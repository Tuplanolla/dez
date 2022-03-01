(** * Deflationarity *)

From DEZ.Has Require Export
  OrderRelations BinaryOperation.
From DEZ.Supports Require Import
  OrderNotations AdditiveNotations.

Class IsDeflGen (A B : Type) (X : B -> A -> Prop) (f : A -> B) : Prop :=
  defl_gen (x : A) : X (f x) x.

Class IsDeflGenL (A B C : Type) (X : C -> B -> Prop)
  (k : A -> B -> C) : Prop :=
  defl_gen_l (x : A) (y : B) : X (k x y) y.

Class IsDeflGenR (A B C : Type) (X : C -> A -> Prop)
  (k : A -> B -> C) : Prop :=
  defl_gen_r (x : A) (y : B) : X (k x y) x.

(** ** Deflationary Function *)
(** ** Regressive Function *)

Class IsDefl (A : Type) (HR : HasOrdRel A) (f : A -> A) : Prop :=
  defl (x : A) : f x <= x.

Class IsDeflBinOpL (A : Type) (HR : HasOrdRel A) (Hk : HasBinOp A) : Prop :=
  defl_bin_op_l (x y : A) : x + y <= y.

Class IsDeflBinOpR (A : Type) (HR : HasOrdRel A) (Hk : HasBinOp A) : Prop :=
  defl_bin_op_r (x y : A) : x + y <= x.
