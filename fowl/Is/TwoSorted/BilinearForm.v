From Maniunfold.Has Require Export
  OneSorted.Addition OneSorted.Zero OneSorted.Negation
  OneSorted.Multiplication OneSorted.One
  TwoSorted.LeftAction TwoSorted.RightAction ThreeSorted.BinaryFunction.
From Maniunfold.Is Require Export
  FiveSorted.BilinearMapping.

(** Bilinear form on a bimodule over a noncommutative ring.
    The scalars are carried by [A] and the vectors by [B]. *)

Class IsBilinForm (A B : Type)
  `(HasAdd A) `(HasZero A) `(HasNeg A)
  `(HasMul A) `(HasOne A)
  `(HasAdd B) `(HasZero B) `(HasNeg B)
  `(HasLAct A B) `(HasRAct A B)
  `(HasBinFn B B A) : Prop :=
  A_A_B_B_A_add_zero_neg_mul_one_add_zero_neg_mul_one_add_zero_neg_add_zero_neg_add_zero_neg_l_act_r_act_l_act_r_act_bin_fn_is_bilin_map
    :> IsBilinMap A A B B A add zero neg mul one add zero neg mul one
    add zero neg add zero neg add zero neg l_act r_act l_act r_act bin_fn.
