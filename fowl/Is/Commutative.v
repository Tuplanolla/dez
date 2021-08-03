(* * Commutativity of a Binary Operation and a Torsion *)

From Coq Require Import
  Logic.FunctionalExtensionality.
From Maniunfold.Has Require Export
  UnaryOperation BinaryOperation Torsion.
From Maniunfold.ShouldHave Require Import
  MultiplicativeNotations.

(** This has the same shape as [mul_opp_l]. *)

Class IsCommL (A : Type) (Hf : HasUnOp A) (Hk : HasBinOp A) : Prop :=
  comm_l (x y : A) : (/ x) * y = / (x * y).

(** This has the same shape as [mul_opp_r]. *)

Class IsCommR (A : Type) (Hf : HasUnOp A) (Hk : HasBinOp A) : Prop :=
  comm_r (x y : A) : x * (/ y) = / (x * y).

Class IsCommLR (A : Type) (Hf : HasUnOp A) (Hk : HasBinOp A) : Prop := {
  is_comm_l :> IsCommL /_ _*_;
  is_comm_r :> IsCommR /_ _*_;
}.

(** This has the same shape as [mul_comm]. *)

Class IsCommBinOp (A : Type) (Hk : HasBinOp A) : Prop :=
  comm_bin_op (x y : A) : x * y = y * x.

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

Class IsComm (A : Type) (f g : A -> A) : Prop :=
  comm (x : A) : f (g x) = g (f x).

Section Context.

Context (A : Type) (Hf : HasUnOp A) (Hk : HasBinOp A).

(** Chiral commutativity is just commutativity of partial applications. *)

#[local] Instance comm_r_is_inj `(!IsCommR /_ _*_)
  (x : A) : IsComm /_ (_*_ x).
Proof.
  intros y.
  rewrite comm_r.
  reflexivity. Qed.

#[local] Instance comm_l_is_inj `(!IsCommL /_ _*_)
  (y : A) : IsComm /_ (flip _*_ y).
Proof.
  intros x.
  unfold flip.
  rewrite comm_l.
  reflexivity. Qed.

End Context.
