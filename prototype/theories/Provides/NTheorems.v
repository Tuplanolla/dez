From Coq Require Import
  Morphisms NArith.
From Maniunfold.Is Require Import
  Equivalence Monoid.
From Maniunfold.ShouldHave Require Import
  BinaryRelationNotations EquivalenceRelationNotations AdditiveNotations.

Module Equivalence.

Instance N_has_eq_rel : HasEqRel N := N.eq.

Instance N_is_reflexive : IsReflEq N.eq := {}.
Proof. intros x. reflexivity. Qed.

Instance N_is_symmetric : IsSymEq N.eq := {}.
Proof. intros x y p. symmetry; auto. Qed.

Instance N_is_transitive : IsTransEq N.eq := {}.
Proof. intros x y z p q. transitivity y; auto. Qed.

Instance N_is_setoid : IsEq N.eq := {}.

End Equivalence.

Module Additive.

Instance N_has_bin_op : HasBinOp N := N.add.

Instance N_is_associative : IsAssoc bin_op := {}.
Proof. intros x y z. apply N.add_assoc. Qed.

Instance N_is_semigroup : IsSGrp N.add := {}.
Proof. cbv -[N.add]. apply N.add_wd. Qed.

Instance N_has_un : HasUn N := N.zero.

Instance N_is_left_unital : IsLUn N.add N.zero := {}.
Proof. intros x. apply N.add_0_l. Qed.

Instance N_is_right_unital : IsRUn N.add N.zero := {}.
Proof. intros x. apply N.add_0_r. Qed.

Instance N_is_unital : IsUn N.add N.zero := {}.

Instance N_is_monoid : IsMon N.add N.zero := {}.

End Additive.

Module Multiplicative.

(* etc *)

End Multiplicative.
