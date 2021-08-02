(* bad *)
From Coq Require Import
  Logic.Eqdep_dec.
From Maniunfold Require Export
  TypeclassTactics.
From Maniunfold.Has Require Export
  Addition Zero Negation Multiplication
  One.
From Maniunfold.Is Require Export
  OneSortedAbelianGroup Distributive Monoid
  OneSortedAbsorbing OneSortedSignedAbsorbing OneSortedBinaryCommutative
  OneSortedBinaryCrossing OneSortedBinarySplitCancellative
  OneSortedDegenerate OneSortedSemiring OneSortedGradedRing
  Unital.
From Maniunfold.ShouldHave Require Import
  OneSortedAdditiveNotations
  OneSortedArithmeticNotations.
From Maniunfold.ShouldHave Require
  OneSortedGradedAdditiveNotations OneSortedGradedArithmeticNotations.

(** Ring, abelian group distributing over a monoid. *)

Class IsRing (A : Type)
  (Hk : HasAdd A) (Hx : HasZero A) (Hf : HasNeg A)
  (Hm : HasMul A) (Hy : HasOne A) : Prop := {
  add_zero_neg_is_ab_grp :> IsAbGrp add zero neg;
  mul_one_is_mon :> IsMon one mul;
  mul_add_is_distr :> IsDistrLR mul add;
}.

Section Context.

Context (A : Type) `(IsRing A).

Import Addition.Subclass Zero.Subclass Negation.Subclass
  Multiplication.Subclass One.Subclass.

Ltac conversions := typeclasses
  convert bin_op into add and null_op into zero and un_op into neg or
  convert bin_op into mul and null_op into one.

(** TODO Decide whether this is a good or a bad feature
    of operational subclasses (hypothesis: bad). *)

Theorem zero_mul_l_absorb (x : A) : 0 * x = 0.
Proof with conversions.
  apply (l_cancel (0 * x) 0 (1 * x))...
  pose proof unl_bin_op_r (Hk := add) as ea'...
  pose proof unl_bin_op_r (Hk := mul) as em'...
  pose proof unl_bin_op_r (Hk := add) as ea.
  pose proof unl_bin_op_r (Hk := mul) as em.
  pose proof unl_bin_op_r as ex.
  specialize (ex : forall x : A, x * 1 = x).
  specialize (ex : forall x : A, x + 0 = x).
  Fail rewrite (ex (1 * x)).
  rewrite (unl_bin_op_r (1 * x)).
  rewrite <- (distr_r 1 0 x).
  rewrite (unl_bin_op_r 1).
  reflexivity. Qed.

Global Instance zero_mul_is_l_absorb : IsLAbsorb zero mul.
Proof. exact @zero_mul_l_absorb. Qed.

Theorem zero_mul_r_absorb (x : A) : x * 0 = 0.
Proof with conversions.
  apply (l_cancel (x * 0) 0 (x * 1))...
  rewrite (unl_bin_op_r (x * 1)).
  rewrite <- (distr_l x 1 0).
  rewrite (unl_bin_op_r 1).
  reflexivity. Qed.

Global Instance zero_mul_is_r_absorb : IsRAbsorb zero mul.
Proof. exact @zero_mul_r_absorb. Qed.

Global Instance zero_mul_is_absorb : IsAbsorb zero mul.
Proof. split; typeclasses eauto. Qed.

Global Instance zero_neg_is_un_absorb : IsUnAbsorb zero neg.
Proof with conversions.
  hnf...
  apply (l_cancel (- 0) 0 0)...
  rewrite (inv_r 0)...
  rewrite (unl_bin_op_r 0).
  reflexivity. Qed.

Theorem neg_mul_one_l_sgn_absorb (x : A) : (- 1) * x = - x.
Proof with conversions.
  apply (l_cancel ((- 1) * x) (- x) (1 * x))...
  rewrite <- (distr_r 1 (- 1) x).
  rewrite (inv_r 1)...
  rewrite (l_absorb x).
  rewrite (unl_bin_op_l x).
  rewrite (inv_r x)...
  reflexivity. Qed.

Global Instance neg_mul_one_is_l_sgn_absorb : IsLSgnAbsorb neg mul one.
Proof. exact @neg_mul_one_l_sgn_absorb. Qed.

Theorem neg_mul_one_r_sgn_absorb (x : A) : x * (- 1) = - x.
Proof with conversions.
  apply (l_cancel (x * (- 1)) (- x) (x * 1))...
  rewrite <- (distr_l x 1 (- 1)).
  rewrite (inv_r 1)...
  rewrite (r_absorb x).
  rewrite (unl_bin_op_r x).
  rewrite (inv_r x)...
  reflexivity. Qed.

Global Instance neg_mul_one_is_r_sgn_absorb : IsRSgnAbsorb neg mul one.
Proof. exact @neg_mul_one_r_sgn_absorb. Qed.

Global Instance neg_mul_one_is_sgn_absorb : IsSgnAbsorb neg mul one.
Proof. split; typeclasses eauto. Qed.

Theorem neg_mul_l_bin_comm (x y : A) : - (x * y) = x * (- y).
Proof with conversions.
  rewrite <- (r_sgn_absorb (x * y)).
  rewrite <- (assoc x y (- 1))...
  rewrite r_sgn_absorb.
  reflexivity. Qed.

Global Instance neg_mul_is_l_bin_comm : IsLBinComm neg mul.
Proof. exact @neg_mul_l_bin_comm. Qed.

Theorem neg_mul_r_bin_comm (x y : A) : - (x * y) = (- x) * y.
Proof with conversions.
  rewrite <- (l_sgn_absorb (x * y)).
  rewrite (assoc (- 1) x y)...
  rewrite l_sgn_absorb.
  reflexivity. Qed.

Global Instance neg_mul_is_r_bin_comm : IsRBinComm neg mul.
Proof. exact @neg_mul_r_bin_comm. Qed.

Global Instance neg_mul_is_bin_comm : IsBinComm neg mul.
Proof. split; typeclasses eauto. Qed.

Theorem neg_mul_bin_crs (x y : A) : (- x) * y = x * (- y).
Proof with conversions.
  rewrite <- (l_bin_comm x y).
  rewrite <- (r_bin_comm x y).
  reflexivity. Qed.

Global Instance neg_mul_is_bin_crs : IsBinCrs neg mul.
Proof. exact @neg_mul_bin_crs. Qed.

Theorem neg_mul_bin_spt_cancel (x y : A) : (- x) * (- y) = x * y.
Proof with conversions.
  rewrite <- (r_bin_comm x (- y)).
  rewrite <- (l_bin_comm x y).
  rewrite (invol (x * y)).
  reflexivity. Qed.

Global Instance neg_mul_is_bin_spt_cancel : IsBinSptCancel neg mul.
Proof. exact @neg_mul_bin_spt_cancel. Qed.

Global Instance add_zero_mul_one_is_semiring : IsSemiring add zero mul one.
Proof. split; typeclasses eauto. Qed.

Theorem one_zero_degen (x : A) (e : 1 = 0) : x = 0.
Proof with conversions.
  pose proof distr_l x 0 1 as e'.
  rewrite unl_bin_op_l in e'. rewrite unl_bin_op_r in e' at 1. rewrite e in e'.
  repeat rewrite r_absorb in e'. rewrite unl_bin_op_r in e'. apply e'. Qed.

Global Instance one_zero_is_degen : IsDegen zero one.
Proof. exact @one_zero_degen. Qed.

(** TODO Clean up. *)

Theorem mul_l_cancel (a : forall x y : A, x * y = 0 -> x = 0 \/ y = 0)
  (x y z : A) (e : z * x = z * y) (f : z <> 0) : x = y.
Proof with conversions.
  assert (e' : z * x + - (z * y) = 0).
  { rewrite e.
    rewrite (inv_r (z * y))...
    reflexivity. }
  rewrite l_bin_comm in e'.
  rewrite <- distr_l in e'.
  apply a in e'.
  destruct e' as [e' | e'].
  - congruence.
  - apply (r_cancel x y (- y))...
    rewrite e'.
    rewrite (inv_r y)...
    reflexivity. Qed.

Import OneSortedGradedArithmeticNotations.
Import OneSortedGradedAdditiveNotations.

Local Instance unit_has_bin_op : HasBinOp unit := fun x y : unit => tt.

Local Instance bin_op_is_assoc : IsAssoc (bin_op (A := unit)).
Proof. intros x y z. repeat match goal with t : unit |- _ => destruct t end.
  reflexivity. Qed.

Local Instance unit_has_null_op : HasNullOp unit := tt.

Local Instance bin_op_null_op_is_unl_l : IsUnlBinOpL null_op bin_op.
Proof. intros x. repeat match goal with t : unit |- _ => destruct t end.
  reflexivity. Qed.

Local Instance bin_op_null_op_is_unl_r : IsUnlBinOpR null_op bin_op.
Proof. intros x. repeat match goal with t : unit |- _ => destruct t end.
  reflexivity. Qed.

Local Instance const_has_add (i : unit) : HasAdd A := add.

Local Instance const_has_zero (i : unit) : HasZero A := zero.

Local Instance const_has_neg (i : unit) : HasNeg A := neg.

Local Instance const_has_grd_mul : HasGrdMul (A := unit) (const A) bin_op :=
  fun (i j : unit) (x y : A) => mul x y.

Local Instance const_has_grd_one : HasGrdOne (A := unit) (const A) null_op :=
  one.

(** Every ring is a trivially graded ring. *)

Local Instance ring_is_grd_ring :
  IsGrdRing (A := unit) (P := const A) bin_op null_op
  const_has_add const_has_zero const_has_neg
  const_has_grd_mul const_has_grd_one.
Proof. repeat split. all: try typeclasses eauto.
  all: hnf; intros.
  all: repeat match goal with t : unit |- _ => destruct t end.
  all: auto; try typeclasses eauto.
  - apply distr_l.
  - apply distr_r.
  - esplit. intros [] [] [] x y z.
    rewrite <- eq_rect_eq_dec; try decide equality.
    apply assoc.
  - esplit. intros [] x.
    rewrite <- eq_rect_eq_dec; try decide equality.
    apply unl_bin_op_l.
  - esplit. intros [] x.
    rewrite <- eq_rect_eq_dec; try decide equality.
    apply unl_bin_op_r. Admitted.

End Context.
