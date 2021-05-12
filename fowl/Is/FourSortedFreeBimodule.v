(* bad *)
From Coq Require Import
  Lists.List Logic.ProofIrrelevance NArith.NArith.
From Maniunfold.Has Require Export
  OneSortedEnumeration OneSortedCardinality TwoSortedIsomorphism
  OneSortedAddition OneSortedZero OneSortedNegation
  OneSortedMultiplication OneSortedOne
  TwoSortedLeftAction TwoSortedRightAction.
From Maniunfold.Is Require Export
  OneSortedFinite TwoSortedIsomorphism
  ThreeSortedBimodule.
From Maniunfold.Offers Require Export
  TwoSortedIsomorphismMappings.

Local Open Scope N_scope.

(** This is a free bimodule with a finite dimension.
    The basis is carried by [A],
    the underlying rings are by [B] and [C] and
    the bimodule itself by [D]. *)

(** TODO Rename [X] into [A] and shift. *)

Class HasBasis (X A : Type) : Type := basis : X -> A.

Typeclasses Transparent HasBasis.

(** TODO Find a way to clean these properties up by refactoring stuff. *)

Definition sum (A : Type) `(HasAdd A) `(HasZero A) : list A -> A :=
  fold_right add zero.

Arguments sum {_ _ _} _.

(** TODO See if freeness is a good standalone property. *)

Class IsFourFreeBimod (X A B C : Type)
  `(HasEnum X) `(HasBasis X C)
  `(HasAdd A) `(HasZero A) `(HasNeg A)
  `(HasMul A) `(HasOne A)
  `(HasAdd B) `(HasZero B) `(HasNeg B)
  `(HasMul B) `(HasOne B)
  `(HasAdd C) `(HasZero C) `(HasNeg C)
  `(HasLAct A C) `(HasRAct B C) : Prop := {
  X_is_b_fin :> IsBFin enum;
  A_B_C_add_zero_neg_mul_one_add_zero_neg_mul_one_add_zero_neg_l_act_r_act_is_three_bimod
    :> IsThreeBimod
    add zero neg mul one add zero neg mul one add zero neg l_act r_act;
  (** The folded summation must be associative and commutative
      in order to keep the basis independent of the enumeration.
      Luckily, in this case, it already is. *)
  (* x = a0 L* e0 + a1 L* e1 + ... + an L* en *)
  l_gen_set : forall x : C, exists f : X -> A,
    x = sum (map (prod_uncurry l_act) (combine (map f enum) (map basis enum)));
  (* 0 = a0 L* e0 + a1 L* e1 + ... + an L* en ->
     0 = a0 /\ 0 = a1 /\ ... /\ 0 = an *)
  l_lin_indep : forall f : X -> A,
    zero = sum (map (prod_uncurry l_act) (combine (map f enum) (map basis enum))) ->
    Forall (eq zero) (map f enum);
  (** TODO Repeat for the other chirality. *)
}.

(** TODO But... why? *)
