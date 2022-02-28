(** * Arithmetic Actions *)

From DEZ.Has Require Export
  AlgebraicActions.

(** ** Left Scalar Multiplication *)

Class HasSMulL (A B : Type) : Type := s_mul_l (x : A) (a : B) : B.

#[export] Typeclasses Transparent HasSMulL.

(** ** Right Scalar Multiplication *)

Class HasSMulR (A B : Type) : Type := s_mul_r (a : B) (x : A) : B.

#[export] Typeclasses Transparent HasSMulR.

Module Subclass.

Section Context.

Context (A B : Type).

(** A left scalar multiplication is a left action. *)

#[export] Instance s_mul_l_has_act_l
  {al : HasSMulL A B} : HasActL A B := s_mul_l.

(** A right scalar multiplication is a right action. *)

#[export] Instance s_mul_r_has_act_r
  {ar : HasSMulR A B} : HasActR A B := s_mul_r.

End Context.

End Subclass.
