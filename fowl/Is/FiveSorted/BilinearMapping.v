From Maniunfold.Has Require Export
  OneSorted.Addition OneSorted.Zero OneSorted.Negation
  OneSorted.Multiplication OneSorted.One
  TwoSorted.LeftAction TwoSorted.RightAction ThreeSorted.BinaryFunction.
From Maniunfold.Is Require Export
  TwoSorted.LeftModule TwoSorted.RightModule
  ThreeSorted.Bimodule ThreeSorted.Biadditive FiveSorted.Bihomogeneous.

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
  `(HasLAct A C) `(HasRAct B D)
  `(HasLAct A E) `(HasRAct B E)
  `(HasBinFn C D E) : Prop := {
  A_C_add_zero_neg_mul_one_add_zero_neg_l_act_is_l_mod :>
    IsLMod A C add zero neg mul one add zero neg l_act;
  B_D_add_zero_neg_mul_one_add_zero_neg_r_act_is_r_mod :>
    IsRMod B D add zero neg mul one add zero neg r_act;
  A_B_E_add_zero_neg_mul_one_add_zero_neg_mul_one_add_zero_neg_l_act_r_act_is_three_bimod
    :> IsThreeBimod A B E
    add zero neg mul one add zero neg mul one add zero neg l_act r_act;
  C_D_E_add_add_add_bin_fn_is_biaddve :> IsBiaddve C D E add add add bin_fn;
  A_B_C_D_E_l_act_r_act_l_act_r_act_bin_fn_is_bihomogen :>
    IsBihomogen A B C D E l_act r_act l_act r_act bin_fn;
}.

(** TODO Get rid of this once it has been addressed. *)

(** And now, a curious digression into a common mistake in literature. *)

From Coq Require Import
  Logic.ProofIrrelevance.
From Maniunfold.Is Require Export
  TwoSorted.Unital TwoSorted.Isomorphism
  TwoSorted.LeftDistributive ThreeSorted.Bicompatible
  OneSorted.CommutativeRing.
From Maniunfold.ShouldHave Require Import
  OneSorted.ArithmeticNotations TwoSorted.MultiplicativeNotations.

Section Context.

(* BothBihomogeneous *)
Class IsBBihomogen (A B C D E : Type)
  `(HasLAct A C) `(HasRAct B D)
  `(HasLAct A E) `(HasRAct B E)
  `(HasBinFn C D E) : Prop :=
  b_bihomogen : forall (a : A) (x : C) (y : D) (b : B),
    bin_fn (a * x)%l_mod (y * b)%r_mod = ((a * bin_fn x y)%l_mod * b)%r_mod.

Local Instance bihomogen_has_iso {A B C D E : Type}
  `{HasLAct A C} `{HasRAct B D}
  `{HasLAct A E} `{HasRAct B E}
  `{HasBinFn C D E}
  (** These classes are not equivalent unless the actions are unital.
      Otherwise [IsBBihomogen] is weaker than [IsBihomogen]. *)
  `{HasNullOp A} `{HasNullOp B}
  `{!IsTwoLUnl A C l_act null_op}
  `{!IsTwoLUnl A E l_act null_op}
  `{!IsTwoRUnl B D r_act null_op}
  `{!IsTwoRUnl B E r_act null_op} :
  HasIso (IsBihomogen A B C D E l_act r_act l_act r_act bin_fn)
  (IsBBihomogen A B C D E l_act r_act l_act r_act bin_fn).
Proof.
  split.
  - intros ? a b x y.
    rewrite r_bihomogen. rewrite l_bihomogen.
    reflexivity.
  - intros ?. split.
    + intros a b x.
      rewrite <- (two_r_unl x).
      rewrite b_bihomogen.
      rewrite (two_r_unl x).
      rewrite (two_r_unl (a * bin_fn b x)%l_mod).
      reflexivity.
    + intros x y a.
      rewrite <- (two_l_unl x).
      rewrite b_bihomogen.
      rewrite (two_l_unl x).
      rewrite (two_l_unl (bin_fn x y)).
      reflexivity. Defined.

(** Life with proof irrelevance is dull. *)

Local Instance bihomogen_is_iso {A B C D E : Type}
  `{HasLAct A C} `{HasRAct B D}
  `{HasLAct A E} `{HasRAct B E}
  `{HasBinFn C D E}
  `{HasNullOp A} `{HasNullOp B}
  `{!IsTwoLUnl A C l_act null_op}
  `{!IsTwoLUnl A E l_act null_op}
  `{!IsTwoRUnl B D r_act null_op}
  `{!IsTwoRUnl B E r_act null_op} :
  IsIso (IsBihomogen A B C D E l_act r_act l_act r_act bin_fn)
  (IsBBihomogen A B C D E l_act r_act l_act r_act bin_fn) bihomogen_has_iso.
Proof.
  split.
  - intros x. apply proof_irrelevance.
  - intros x. apply proof_irrelevance. Defined.

End Context.
