(** * Scalar Multiplication *)

From DEZ.Has Require Export
  Action.

Class HasSMulL (A B : Type) : Type := s_mul_l (a : A) (x : B) : B.
Class HasSMulR (A B : Type) : Type := s_mul_r (x : B) (a : A) : B.

Typeclasses Transparent HasSMulL HasSMulR.

Module Subclass.

Section Context.

Context (A B : Type).

(** Scalar multiplication is an action of scalars on vectors. *)

#[local] Instance has_act_l (Hl : HasSMulL A B) : HasActL A B := s_mul_l.
#[local] Instance has_act_r (Hr : HasSMulR A B) : HasActR A B := s_mul_r.

End Context.

#[export] Hint Resolve has_act_l has_act_r : typeclass_instances.

End Subclass.
