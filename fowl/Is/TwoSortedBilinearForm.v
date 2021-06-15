From Maniunfold.Has Require Export
  Addition Zero Negation
  Multiplication One
  Action ThreeSortedBinaryFunction.
From Maniunfold.Is Require Export
  FiveSortedBilinearMapping.

(** Bilinear form on a bimodule over a noncommutative ring.
    The scalars are carried by [A] and the vectors by [B]. *)

(** TODO This is the wrong specialization due to the [add]s. *)

Class IsBilinForm (A B : Type)
  `(HasAdd A) `(HasZero A) `(HasNeg A)
  `(HasMul A) `(HasOne A)
  `(HasAdd B) `(HasZero B) `(HasNeg B)
  (l : HasActL A B) (r : HasActR A B)
  (f : B -> B -> A) : Prop :=
  A_A_B_B_A_add_zero_neg_mul_one_add_zero_neg_mul_one_add_zero_neg_add_zero_neg_add_zero_neg_act_l_act_r_act_l_act_r_bin_fn_is_bilin_map
    :> @IsBilinMap A A B B A add zero neg mul one add zero neg mul one
    add zero neg add zero neg add zero neg
    l r add add f.
