(** * Semiring Structure *)

From DEZ.Is Require Export
  Monoid Commutative Distributive Absorbing.

(** ** Noncommutative Nonunital Semiring *)

Class IsSemirng (A : Type) (X : A -> A -> Prop)
  (x : A) (k : A -> A -> A) (m : A -> A -> A) : Prop := {
  semirng_add_is_mon :> IsMon X x k;
  semirng_add_is_comm_bin_op :> IsCommBinOp X k;
  semirng_mul_is_semigrp :> IsSemigrp X m;
  semirng_is_distr :> IsDistr X m k;
  semirng_is_absorb_elem :> IsAbsorbElem X x m;
}.

(** ** Noncommutative Unital Semiring *)

Class IsSemiring (A : Type) (X : A -> A -> Prop)
  (x : A) (k : A -> A -> A) (y : A) (m : A -> A -> A) : Prop := {
  semiring_add_is_mon :> IsMon X x k;
  semiring_add_is_comm_bin_op :> IsCommBinOp X k;
  semiring_mul_is_mon :> IsMon X y m;
  semiring_is_distr :> IsDistr X m k;
  semiring_is_absorb_elem :> IsAbsorbElem X x m;
}.

Section Context.

Context (A : Type) (X : A -> A -> Prop)
  (x : A) (k : A -> A -> A) (y : A) (m : A -> A -> A)
  `{!IsSemiring X x k y m}.

(** Removing the unit element
    from a unital semiring yields a nonunital semiring. *)

#[export] Instance semiring_is_semirng : IsSemirng X x k m.
Proof. esplit; typeclasses eauto. Qed.

End Context.
