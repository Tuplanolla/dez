(** * Group Structure *)

From DEZ.Has Require Export
  EquivalenceRelation Addition Zero Multiplication One.
From DEZ.Is Require Export
  Monoid Commutative Distributive Absorbing Truncated.
From DEZ.ShouldHave Require Import
  EquivalenceRelationNotations ArithmeticNotations.

(** ** Semiring *)

Class IsSemiring (A : Type) (R : HasEqRel A)
  (x : HasZero A) (k : HasAdd A) (y : HasOne A) (m : HasMul A) : Prop := {
  add_is_mon :> IsMon _==_ 0 _+_;
  add_is_comm :> IsComm _==_ _+_;
  mul_is_mon :> IsMon _==_ 1 _*_;
  is_distr_l_r :> IsDistrLR _*_ _+_;
  is_absorb_elem_l_r :> IsAbsorbElemLR _==_ 0 _*_;
  (** TODO Relocate these. *)
  is_proper :> Proper (R ==> R ==> R) k;
  is_proper' :> Proper (R ==> R ==> R) m;
}.

Class IsContrGen (A : Type) (R : A -> A -> Prop) : Prop :=
  contr_gen : exists x : A, forall y : A, R x y.

Section Context.

Context (A : Type) `(IsSemiring A).

Ltac notations :=
  change R with _==_ in *;
  change x with 0 in *;
  change k with _+_ in *;
  change y with 1 in *;
  change m with _*_ in *.

#[local] Instance is_contr (a : 0 == 1) : IsContrGen R.
Proof.
  hnf.
  notations.
  exists 0.
  intros z.
  Fail pose proof f_equal (_*_ z) a as b.
  assert (b : z * 0 == z * 1).
  { apply is_proper'; easy. }
  setoid_rewrite (unl_r z) in b.
  setoid_rewrite (absorb_elem_r z) in b.
  setoid_rewrite b.
  reflexivity. Qed.

End Context.

#[export] Hint Resolve is_contr : typeclass_instances.
