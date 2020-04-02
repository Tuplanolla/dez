(* good *)
From Maniunfold.Has Require Export
  OneSorted.Addition OneSorted.Zero OneSorted.Negation
  OneSorted.Multiplication OneSorted.One
  TwoSorted.BinaryForm TwoSorted.LeftAction TwoSorted.RightAction.
From Maniunfold.Is Require Export
  FiveSorted.BilinearMapping.

(** This is a bilinear form.
    The scalars are carried by [A] and the vectors by [B].
    We call the form just that, for the lack of a better name. *)

Class IsBilinForm (A B : Type)
  (A_has_add : HasAdd A) (A_has_zero : HasZero A) (A_has_neg : HasNeg A)
  (A_has_mul : HasMul A) (A_has_one : HasOne A)
  (B_has_add : HasAdd B) (B_has_zero : HasZero B) (B_has_neg : HasNeg B)
  (A_B_has_bin_form : HasBinForm A B)
  (A_B_has_l_act : HasLAct A B) (A_B_has_r_act : HasRAct A B) : Prop :=
  A_A_B_B_A_add_zero_neg_mul_one_add_zero_neg_mul_one_add_zero_neg_add_zero_neg_add_zero_neg_bin_form_l_act_r_act_l_act_r_act_is_bilin_map
    :> IsBilinMap A A B B A add zero neg mul one add zero neg mul one
    add zero neg add zero neg add zero neg bin_form l_act r_act l_act r_act.
