From Maniunfold.Has Require Export
  Addition Zero Negation
  Multiplication One
  Action ThreeSortedBinaryFunction.
From Maniunfold.Is Require Export
  TwoSortedLeftModule TwoSortedRightModule
  ThreeSortedBimodule ThreeSortedBiadditive FiveSortedBihomogeneous.

(** Bilinear mapping from a left module and a right module into a bimodule,
    where each module is defined over a noncommutative ring.
    The rings are carried by [A] and [B],
    the left module by [C], the right module by [D] and the bimodule by [E]. *)

Class IsBilinMap (A B C D E : Type)
  `(HasAdd A) `(HasZero A) `(HasNeg A)
  `(HasMul A) `(HasOne A)
  `(HasAdd B) `(HasZero B) `(HasNeg B)
  `(HasMul B) `(HasOne B)
  `(HasAdd C) `(HasZero C) `(HasNeg C)
  `(HasAdd D) `(HasZero D) `(HasNeg D)
  `(HasAdd E) `(HasZero E) `(HasNeg E)
  `(HasActL A C) `(HasActR B D)
  `(HasActL A E) `(HasActR B E)
  `(HasBinFn C D E) : Prop := {
  A_C_add_zero_neg_mul_one_add_zero_neg_act_l_is_l_mod :>
    IsLMod add zero neg mul one add zero neg (act_l (A := A) (B := C));
  B_D_add_zero_neg_mul_one_add_zero_neg_act_r_is_r_mod :>
    IsRMod add zero neg mul one add zero neg (act_r (A := B) (B := D));
  A_B_E_add_zero_neg_mul_one_add_zero_neg_mul_one_add_zero_neg_act_l_act_r_is_three_bimod
    :> IsThreeBimod
    add zero neg mul one add zero neg mul one add zero neg act_l act_r;
  C_D_E_add_add_add_bin_fn_is_biaddve :>
    IsBiaddve (add (A := C)) (add (A := D)) (add (A := E)) bin_fn;
  A_B_C_D_E_act_l_act_r_act_l_act_r_bin_fn_is_bihomogen :>
    IsBihomogen act_l act_r act_l act_r bin_fn;
}.

(** TODO Get rid of this once it has been addressed. *)

(** And now, a curious digression into a common mistake in literature. *)

From Coq Require Import
  Logic.ProofIrrelevance.
From Maniunfold.Is Require Export
  TwoSortedUnital Isomorphism
  TwoSortedLeftDistributive ThreeSortedBicompatible
  Ring.
From Maniunfold.ShouldHave Require Import
  OneSortedArithmeticNotations TwoSortedMultiplicativeNotations.

Section Context.

(* BothBihomogeneous *)
Class IsBBihomogen (A B C D E : Type)
  `(HasActL A C) `(HasActR B D)
  `(HasActL A E) `(HasActR B E)
  `(HasBinFn C D E) : Prop :=
  b_bihomogen : forall (a : A) (x : C) (y : D) (b : B),
    bin_fn (a * x)%l_mod (y * b)%r_mod = ((a * bin_fn x y)%l_mod * b)%r_mod.

Definition bihomogen_has_iso {A B C D E : Type}
  `{HasActL A C} `{HasActR B D}
  `{HasActL A E} `{HasActR B E}
  `{HasBinFn C D E}
  (** These classes are not equivalent unless the actions are unital.
      Otherwise [IsBBihomogen] is weaker than [IsBihomogen]. *)
  `{HasNullOp A} `{HasNullOp B}
  `{!@IsTwoUnlL A C act_l null_op}
  `{!@IsTwoUnlL A E act_l null_op}
  `{!@IsTwoUnlR B D act_r null_op}
  `{!@IsTwoUnlR B E act_r null_op} :
  (@IsBihomogen A B C D E act_l act_r act_l act_r bin_fn ->
  @IsBBihomogen A B C D E act_l act_r act_l act_r bin_fn) *
  (@IsBBihomogen A B C D E act_l act_r act_l act_r bin_fn ->
  @IsBihomogen A B C D E act_l act_r act_l act_r bin_fn).
Proof.
  split.
  - intros ? a b x y.
    rewrite r_bihomogen. rewrite l_bihomogen.
    reflexivity.
  - intros ?. split.
    + intros a b x.
      rewrite <- (two_unl_r x).
      rewrite b_bihomogen.
      rewrite (two_unl_r x).
      rewrite (two_unl_r (a * bin_fn b x)%l_mod).
      reflexivity.
    + intros x y a.
      rewrite <- (two_unl_l x).
      rewrite b_bihomogen.
      rewrite (two_unl_l x).
      rewrite (two_unl_l (bin_fn x y)).
      reflexivity. Defined.

(** Life with proof irrelevance is dull. *)

Local Instance bihomogen_is_iso_l_r {A B C D E : Type}
  `{HasActL A C} `{HasActR B D}
  `{HasActL A E} `{HasActR B E}
  `{HasBinFn C D E}
  `{HasNullOp A} `{HasNullOp B}
  `{!@IsTwoUnlL A C act_l null_op}
  `{!@IsTwoUnlL A E act_l null_op}
  `{!@IsTwoUnlR B D act_r null_op}
  `{!@IsTwoUnlR B E act_r null_op} :
  IsIsoLR (fst bihomogen_has_iso) (snd bihomogen_has_iso).
Proof.
  split.
  - intros x. apply proof_irrelevance.
  - intros x. apply proof_irrelevance. Defined.

End Context.
