From Coq Require Import
  Morphisms NArith.
From Maniunfold.Is Require Import
  Setoid Monoid.
From Maniunfold.ShouldHave Require Import
  BinaryRelationNotations EquivalenceRelationNotations AdditiveNotations.

Module Equivalence.

Instance N_has_eq_rel : HasEqRel N := N.eq.

Instance N_is_reflexive : IsReflexive N.eq := {}.
Proof. intros x. reflexivity. Qed.

Instance N_is_symmetric : IsSymmetric N.eq := {}.
Proof. intros x y p. symmetry; auto. Qed.

Instance N_is_transitive : IsTransitive N.eq := {}.
Proof. intros x y z p q. transitivity y; auto. Qed.

Instance N_is_setoid : IsSetoid N.eq := {}.

End Equivalence.

Module Additive.

Instance N_has_bi_op : HasBiOp N := N.add.

Instance N_is_associative : IsAssociative bi_op := {}.
Proof. intros x y z. apply N.add_assoc. Qed.

Instance N_is_semigroup : IsSemigroup N.add := {}.
Proof. cbv -[N.add]. apply N.add_wd. Qed.

Instance N_has_un : HasUn N := N.zero.

Instance N_is_left_unital : IsLeftUnital N.add N.zero := {}.
Proof. intros x. apply N.add_0_l. Qed.

Instance N_is_right_unital : IsRightUnital N.add N.zero := {}.
Proof. intros x. apply N.add_0_r. Qed.

Instance N_is_unital : IsUnital N.add N.zero := {}.

Instance N_is_monoid : IsMonoid N.add N.zero := {}.

End Additive.

Module Multiplicative.

(* etc *)

End Multiplicative.
