(* * Commutativity of a Binary Operation and a Torsion *)

From Maniunfold.Has Require Export
  BinaryOperation Torsion.
From Maniunfold.ShouldHave Require Import
  MultiplicativeNotations.

(** This has the same shape as [mul_comm]. *)

Class IsComm (A : Type) (Hk : HasBinOp A) : Prop :=
  comm (x y : A) : x * y = y * x.

Section Context.

#[local] Open Scope left_torsion_scope.

Class IsCommTorL (A B : Type) (Hl : HasTorL A B) : Prop :=
  comm_tor_l (x y : B) : y / x = x / y.

End Context.

Section Context.

#[local] Open Scope right_torsion_scope.

Class IsCommTorR (A B : Type) (Hr : HasTorR A B) : Prop :=
  comm_tor_r (x y : B) : y / x = x / y.

End Context.
