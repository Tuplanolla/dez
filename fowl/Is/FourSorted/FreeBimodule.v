(* bad *)
From Coq Require Import
  Lists.List Logic.ProofIrrelevance NArith.NArith.
From Maniunfold.Has Require Export
  OneSorted.Enumeration OneSorted.Cardinality TwoSorted.Isomorphism
  OneSorted.Addition OneSorted.Zero OneSorted.Negation
  OneSorted.Multiplication OneSorted.One
  TwoSorted.LeftAction TwoSorted.RightAction.
From Maniunfold.Is Require Export
  OneSorted.Finite TwoSorted.Isomorphism
  ThreeSorted.Bimodule.
From Maniunfold.Offers Require Export
  TwoSorted.IsomorphismMappings.

Local Open Scope N_scope.

(** This is a free bimodule with a finite dimension.
    The basis is carried by [A],
    the underlying rings are by [B] and [C] and
    the bimodule itself by [D]. *)

(** TODO Rename [X] into [A] and shift. *)

Class HasBasis (X A : Type) : Type := basis : X -> A.

Typeclasses Transparent HasBasis.

(** TODO Find a way to clean these properties up by refactoring stuff. *)

Definition sum {A : Type}
  {A_has_add : HasAdd A} {A_has_zero : HasZero A} : list A -> A :=
  fold_right add zero.

(** TODO See if freeness is a good standalone property. *)

Class IsFourFreeBimod (X A B C : Type)
  {X_has_enum : HasEnum X} (X_C_has_basis : HasBasis X C)
  (A_has_add : HasAdd A) (A_has_zero : HasZero A) (A_has_neg : HasNeg A)
  (A_has_mul : HasMul A) (A_has_one : HasOne A)
  (B_has_add : HasAdd B) (B_has_zero : HasZero B) (B_has_neg : HasNeg B)
  (B_has_mul : HasMul B) (B_has_one : HasOne B)
  (C_has_add : HasAdd C) (C_has_zero : HasZero C) (C_has_neg : HasNeg C)
  (A_C_has_l_act : HasLAct A C) (B_C_has_r_act : HasRAct B C) : Prop := {
  X_is_b_fin :> IsBFin X;
  A_B_C_add_zero_neg_mul_one_add_zero_neg_mul_one_add_zero_neg_l_act_r_act_is_three_bimod
    :> IsThreeBimod A B C
    add zero neg mul one add zero neg mul one add zero neg l_act r_act;
  (** The folded summation must be associative and commutative
      in order to keep the basis independent of the enumeration.
      Luckily, in this case, it already is. *)
  (* x = a0 L* e0 + a1 L* e1 + ... + an L* en *)
  l_gen_set : forall x : C, exists f : X -> A,
    x = sum (map (prod_curry l_act) (combine (map f enum) (map basis enum)));
  (* 0 = a0 L* e0 + a1 L* e1 + ... + an L* en ->
     0 = a0 /\ 0 = a1 /\ ... /\ 0 = an *)
  l_lin_indep : forall f : X -> A,
    zero = sum (map (prod_curry l_act) (combine (map f enum) (map basis enum))) ->
    Forall (eq zero) (map f enum);
  (** TODO Repeat for the other chirality. *)
}.

(** TODO But... why? *)
