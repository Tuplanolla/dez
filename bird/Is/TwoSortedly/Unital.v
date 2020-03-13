From Maniunfold.Has Require Export
  EquivalenceRelation BinaryOperation Unit.
From Maniunfold.Is Require Export
  LeftUnital RightUnital.

Class IsTwoUnl {A B : Type}
  (has_l_un : HasLUn A) (has_r_un : HasRUn A)
  (has_l_act : HasLAct A B) (has_r_act : HasRAct A B) : Prop := {
  l_un_l_act_is_two_l_unl_ :> IsTwoLUnl l_un l_act;
  r_un_r_act_is_two_r_unl_ :> IsTwoRUnl r_un r_act;
}.
