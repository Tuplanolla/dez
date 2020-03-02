From Maniunfold.Has Require Export
  EquivalenceRelation LeftAction RightAction
  LeftUnit RightUnit LeftFunction RightFunction.
From Maniunfold.Is Require Export
  LeftExternallyInvertible RightExternallyInvertible.

Class IsExtInv {A B : Type} {has_eq_rel : HasEqRel B}
  (has_l_un : HasLUn B) (has_r_un : HasRUn B)
  (has_l_fn : HasLFn B A) (has_r_fn : HasRFn B A)
  (has_l_act : HasLAct A B) (has_r_act : HasRAct A B) : Prop := {
  l_act_l_un_l_fn_is_l_ext_inv :> IsLExtInv l_un l_fn l_act;
  r_act_r_un_r_fn_is_r_ext_inv :> IsRExtInv r_act r_un r_fn;
}.
