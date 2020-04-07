From Maniunfold.Has Require Export
  TwoSorted.LeftAction TwoSorted.RightAction
  TwoSorted.LeftTorsion TwoSorted.RightTorsion.

(** Binary operation, dyadic operation.
    Commonly found in semigroups. *)

Class HasBinOp (A : Type) : Type := bin_op : A -> A -> A.

Typeclasses Transparent HasBinOp.

(** TODO Check these superclasses.
    Will give the following error if omitted.

<<
File "./Is/TwoSorted/BilinearForm.v", line 13, characters 0-620:
Error:
Unable to satisfy the following constraints:
In environment:
IsBilinForm : forall A B : Type,
              HasAdd A -> HasZero A -> HasNeg A -> HasMul A -> HasOne A ->
              HasAdd B -> HasZero B -> HasNeg B ->
              HasBinForm A B -> HasLAct A B -> HasRAct A B -> Prop
A : Type
B : Type
A_has_add : HasAdd A
A_has_zero : HasZero A
A_has_neg : HasNeg A
A_has_mul : HasMul A
A_has_one : HasOne A
B_has_add : HasAdd B
B_has_zero : HasZero B
B_has_neg : HasNeg B
A_B_has_bin_form : HasBinForm A B
A_B_has_l_act : HasLAct A B
A_B_has_r_act : HasRAct A B

?HasLAct : "HasLAct A A"
>> *)

Section Context.

Context {A : Type} `{A_has_bin_op : HasBinOp A}.

Global Instance A_A_has_l_act : HasLAct A A := bin_op.
Global Instance A_A_has_r_act : HasRAct A A := bin_op.
Global Instance A_A_has_l_tor : HasLTor A A := bin_op.
Global Instance A_A_has_r_tor : HasRTor A A := bin_op.

End Context.
