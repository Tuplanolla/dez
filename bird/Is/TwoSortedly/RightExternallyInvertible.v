From Maniunfold.Has Require Export
  BinaryRelation RightAction RightUnit RightFunction.
From Maniunfold.Is Require Export
  RightInternallyInvertible.
From Maniunfold.ShouldHave Require Import
  BinaryRelationNotations AdditiveNotations.

Class IsRExtInv {A B : Type} {has_bin_rel : HasBinRel B}
  (has_r_act : HasRAct A B) (has_r_un : HasRUn B)
  (has_r_fn : HasRFn B A) : Prop :=
  r_ext_inv : forall x : B, x R+ R- x ~~ R0.

Section Context.

Context {A : Type} `{is_r_ext_inv : IsRExtInv A}.

Global Instance r_act_r_un_r_fn_is_r_int_inv :
  IsRIntInv r_act r_un r_fn.
Proof. intros x. apply r_ext_inv. Qed.

End Context.
