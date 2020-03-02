From Maniunfold.Has Require Export
  EquivalenceRelation BinaryOperation Unit.
From Maniunfold.Is Require Export
  LeftUnital RightUnital.

Class IsUnl2 {A B : Type} {has_eq_rel : HasEqRel B}
  (has_l_un : HasLUn A) (has_r_un : HasRUn A)
  (has_l_act : HasLAct A B) (has_r_act : HasRAct A B) : Prop := {
  l_un_l_act_is_l_unl_2 :> IsLUnl2 l_un l_act;
  r_un_r_act_is_r_unl_2 :> IsRUnl2 r_un r_act;
}.
