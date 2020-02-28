From Maniunfold.Has Require Export
  BinaryRelation LeftAction LeftUnit LeftFunction.
From Maniunfold.Is Require Export
  LeftInternallyInvertible.
From Maniunfold.ShouldHave Require Import
  BinaryRelationNotations AdditiveNotations.

Class IsLExtInv {A B : Type} {has_bin_rel : HasBinRel B}
  (has_l_act : HasLAct A B) (has_l_un : HasLUn B)
  (has_l_fn : HasLFn B A) : Prop :=
  l_ext_inv : forall x : B, L- x L+ x ~~ L0.

Section Context.

Context {A : Type} `{is_l_ext_inv : IsLExtInv A}.

Global Instance l_act_l_un_l_fn_is_l_int_inv :
  IsLIntInv l_act l_un l_fn.
Proof. intros x. apply l_ext_inv. Qed.

End Context.
