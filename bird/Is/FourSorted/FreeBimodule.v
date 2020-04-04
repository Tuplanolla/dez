(* bad *)
From Coq Require Import
  Lists.List Logic.ProofIrrelevance NArith.NArith.
From Maniunfold.Has Require Export
  OneSorted.Cardinality TwoSorted.Isomorphism
  OneSorted.Addition OneSorted.Zero OneSorted.Negation
  OneSorted.Multiplication OneSorted.One
  TwoSorted.LeftAction TwoSorted.RightAction.
From Maniunfold.Is Require Export
  OneSorted.Finite TwoSorted.Isomorphism
  ThreeSorted.Bimodule.
From Maniunfold.Offers Require Export
  OneSorted.Enumeration TwoSorted.IsomorphismMappings.

Local Open Scope N_scope.

(** This is a free bimodule with a finite dimension.
    The basis is carried by [A],
    the underlying rings are by [B] and [C] and
    the bimodule itself by [D]. *)

(** TODO Rename [X] into [A] and shift. *)

Class HasBasis (X A : Type) : Type := basis : X -> A.

Typeclasses Transparent HasBasis.

Definition curry {A B C : Type} (f : A * B -> C) (x : A) (y : B) : C :=
  f (x, y).

Definition uncurry {A B C : Type} (f : A -> B -> C) (xy : A * B) : C :=
  f (fst xy) (snd xy).

(** TODO See if freeness is a good standalone property. *)

Class IsFourFreeBimod (X A B C : Type)
  {X_has_card : HasCard X} {X_has_iso : HasIso X {n : N | n < card X}}
  (X_C_has_basis : HasBasis X C)
  (A_has_add : HasAdd A) (A_has_zero : HasZero A) (A_has_neg : HasNeg A)
  (A_has_mul : HasMul A) (A_has_one : HasOne A)
  (B_has_add : HasAdd B) (B_has_zero : HasZero B) (B_has_neg : HasNeg B)
  (B_has_mul : HasMul B) (B_has_one : HasOne B)
  (C_has_add : HasAdd C) (C_has_zero : HasZero C) (C_has_neg : HasNeg C)
  (A_C_has_l_act : HasLAct A C) (B_C_has_r_act : HasRAct B C) : Prop := {
  X_is_fin :> IsFin X;
  A_B_C_add_zero_neg_mul_one_add_zero_neg_mul_one_add_zero_neg_l_act_r_act_is_three_bimod
    :> IsThreeBimod A B C
    add zero neg mul one add zero neg mul one add zero neg l_act r_act;
  (** TODO Find a way to clean these properties up by refactoring stuff. *)
  l_gen_set : forall x : C, exists f : X -> A,
    x = fold_right add zero
    (map (uncurry l_act) (combine (map f enum) (map basis enum)));
  l_lin_indep : forall f : X -> A,
    zero = fold_right add zero
    (map (uncurry l_act) (combine (map f enum) (map basis enum))) ->
    Forall (fun a : A => zero = a) (map f enum);
  (** TODO Repeat for the other chirality. *)
}.

(** TODO But... why? *)
