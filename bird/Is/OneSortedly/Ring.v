From Maniunfold.Has Require Export
  EquivalenceRelation Addition Negation Multiplication.
From Maniunfold.Is Require Export
  Commutative Group Monoid Distributive Absorbing Semiring.
From Maniunfold.ShouldHave Require Import
  EquivalenceRelationNotations ArithmeticNotations.

Class IsRing {A : Type} {has_eq_rel : HasEqRel A}
  (has_add : HasAdd A) (has_zero : HasZero A) (has_neg : HasNeg A)
  (has_mul : HasMul A) (has_one : HasOne A) : Prop := {
  add_is_comm :> IsComm add;
  add_zero_neg_is_grp :> IsGrp add zero neg;
  add_mul_is_distr :> IsDistr add mul;
  mul_one_is_mon :> IsMon mul one;
}.

Section Context.

Context {A : Type} `{is_ring : IsRing A}.

Theorem zero_mul_l_absorb : forall x : A,
  0 * x == 0.
Proof.
  intros x.
  apply (l_cancel (0 * x) 0 (1 * x)).
  (** TODO Specialize lemmas. *)
  replace bin_op with add by reflexivity.
  rewrite (r_unl (1 * x)).
  rewrite <- (r_distr 1 0 x).
  rewrite (r_unl 1).
  reflexivity. Qed.

Global Instance zero_mul_is_l_absorb : IsLAbsorb zero mul.
Proof. intros x. apply zero_mul_l_absorb. Qed.

Theorem zero_mul_r_absorb : forall x : A,
  x * 0 == 0.
Proof.
  intros x.
  apply (l_cancel (x * 0) 0 (x * 1)).
  (** TODO Specialize lemmas. *)
  replace bin_op with add by reflexivity.
  rewrite (r_unl (x * 1)).
  rewrite <- (l_distr x 1 0).
  rewrite (r_unl 1).
  reflexivity. Qed.

Global Instance zero_mul_is_r_absorb : IsRAbsorb zero mul.
Proof. intros x. apply zero_mul_r_absorb. Qed.

Global Instance zero_mul_is_absorb : IsAbsorb zero mul.
Proof. constructor; typeclasses eauto. Qed.

(** TODO Name these properties. *)

(** TODO Could we avoid this,
    if we replaced the operational classes
    in [l_cancel] or [r_inv] with bare types?
    Even if that worked in this case,
    would it stop implicit generalization from working properly?
    Investigate!

    Yes, we could avoid it, and no, we would not break implicit generalization,
    but we would lose the ability to use notations
    when defining predicative classes,
    because notations are tied to operational classes.

    Clearly, there is a conflict between
    nice specialization versus nice notation.
    So, could we make a compromise,
    where implicit arguments are operative classes,
    but explicit ones are bare types? *)

Corollary add_l_cancel : forall x y z : A,
  z + x == z + y -> x == y.
Proof. intros x y z. apply l_cancel. Qed.

Corollary add_r_inv : forall x : A,
  x + - x == 0.
Proof. intros x. apply r_inv. Qed.

Theorem l_Unnamed_thm : forall x : A,
  - (1) * x == - x.
Proof.
  intros x.
  apply (add_l_cancel (- (1) * x) (- x) x).
  Fail progress
    replace bin_op with add by reflexivity.
  rewrite (r_inv (has_un := zero) x).
  Fail progress
    replace (@un A (@Zero.A_has_un A has_zero)) with 0 by reflexivity.
  rewrite <- (l_unl x) at 1.
  replace (bin_op un) with (mul 1) by reflexivity.
  rewrite <- (r_distr 1 (- (1)) x).
  rewrite (r_inv 1).
  replace (@un A (@Zero.A_has_un A has_zero)) with 0 by reflexivity.
  rewrite (l_absorb x).
  reflexivity. Qed.

(** Hold up! This might work. *)

Create HintDb group.
Hint Unfold bin_op un un_op : group.
Hint Unfold Addition.A_has_bin_op Zero.A_has_un Negation.A_has_un_op : group.
Hint Unfold Multiplication.A_has_bin_op One.A_has_un Reciprocation.A_has_un_op : group.

Theorem r_Unnamed_thm : forall x : A, x * - (1) == - x.
Proof with autounfold with group.
  intros x.
  apply (l_cancel (x * - (1)) (- x) x)...
  rewrite (r_inv x)...
  rewrite <- (r_unl x) at 1...
  rewrite <- (l_distr x)...
  rewrite (r_inv 1)...
  rewrite (r_absorb x)...
  reflexivity. Qed.

Goal forall x y : A, - (x * y) == - x * y.
Proof with autounfold with group.
  intros x y.
  rewrite <- (l_Unnamed_thm (x * y)).
  rewrite (assoc (- (1)) x y)...
  (** It does not work. *)
  change has_mul with mul.
  rewrite l_Unnamed_thm.
  reflexivity. Qed.

Goal forall x y : A, - (x * y) == x * - y.
Proof.
  intros x y.
  rewrite <- (r_Unnamed_thm (x * y)).
  rewrite <- (assoc x y (- (1))).
  rewrite r_Unnamed_thm.
  reflexivity. Qed.

Goal 0 == 1 -> forall x y : A, x == y.
Proof.
  intros H x y.
  rewrite <- (l_unl x).
  rewrite <- (l_unl y).
  replace (bin_op un) with (mul 1) by reflexivity.
  rewrite <- H.
  rewrite (l_absorb x).
  rewrite (l_absorb y).
  reflexivity. Qed.

Global Instance add_zero_mul_one_is_sring : IsSring add zero mul one.
Proof. constructor; typeclasses eauto. Qed.

End Context.
