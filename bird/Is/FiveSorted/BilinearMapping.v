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
  (A_has_add : HasAdd A) (A_has_zero : HasZero A) (A_has_neg : HasNeg A)
  (A_has_mul : HasMul A) (A_has_one : HasOne A)
  (B_has_add : HasAdd B) (B_has_zero : HasZero B) (B_has_neg : HasNeg B)
  (B_has_mul : HasMul B) (B_has_one : HasOne B)
  (C_has_add : HasAdd C) (C_has_zero : HasZero C) (C_has_neg : HasNeg C)
  (D_has_add : HasAdd D) (D_has_zero : HasZero D) (D_has_neg : HasNeg D)
  (E_has_add : HasAdd E) (E_has_zero : HasZero E) (E_has_neg : HasNeg E)
  (A_C_has_l_act : HasLAct A C) (B_D_has_r_act : HasRAct B D)
  (A_E_has_l_act : HasLAct A E) (B_E_has_r_act : HasRAct B E)
  (C_D_E_has_bin_fn : HasBinFn C D E) : Prop := {
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
  TwoSorted.LeftDistributive ThreeSorted.Bicompatible TwoSorted.LeftLinear
  OneSorted.CommutativeRing.
From Maniunfold.ShouldHave Require Import
  OneSorted.ArithmeticNotations TwoSorted.MultiplicativeNotations.

Section Context.

(* BothBihomogeneous *)
Class IsBBihomogen (A B C D E : Type)
  (A_C_has_l_act : HasLAct A C) (B_D_has_r_act : HasRAct B D)
  (A_E_has_l_act : HasLAct A E) (B_E_has_r_act : HasRAct B E)
  (C_D_E_has_bin_fn : HasBinFn C D E) : Prop :=
  b_bihomogen : forall (a : A) (x : C) (y : D) (b : B),
    bin_fn (a * x)%l_act (y * b)%r_act = ((a * bin_fn x y)%l_act * b)%r_act.

Local Instance bihomogen_has_iso {A B C D E : Type}
  {A_C_has_l_act : HasLAct A C} {B_D_has_r_act : HasRAct B D}
  {A_E_has_l_act : HasLAct A E} {B_E_has_r_act : HasRAct B E}
  {C_D_E_has_bin_fn : HasBinFn C D E}
  (** These classes are not equivalent unless the actions are unital.
      Otherwise [IsBBihomogen] is weaker than [IsBihomogen]. *)
  {A_has_null_op : HasNullOp A} {B_has_null_op : HasNullOp B}
  {A_C_null_op_l_act_is_two_l_unl : IsTwoLUnl A C null_op l_act}
  {A_E_null_op_l_act_is_two_l_unl : IsTwoLUnl A E null_op l_act}
  {B_D_null_op_r_act_is_two_r_unl : IsTwoRUnl B D null_op r_act}
  {B_E_null_op_r_act_is_two_r_unl : IsTwoRUnl B E null_op r_act} :
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
      rewrite (two_r_unl (a * bin_fn b x)%l_act).
      reflexivity.
    + intros x y a.
      rewrite <- (two_l_unl x).
      rewrite b_bihomogen.
      rewrite (two_l_unl x).
      rewrite (two_l_unl (bin_fn x y)).
      reflexivity. Defined.

(** Life with proof irrelevance is dull. *)

Local Instance bihomogen_is_iso {A B C D E : Type}
  {A_C_has_l_act : HasLAct A C} {B_D_has_r_act : HasRAct B D}
  {A_E_has_l_act : HasLAct A E} {B_E_has_r_act : HasRAct B E}
  {C_D_E_has_bin_fn : HasBinFn C D E}
  {A_has_null_op : HasNullOp A} {B_has_null_op : HasNullOp B}
  {A_C_null_op_l_act_is_two_l_unl : IsTwoLUnl A C null_op l_act}
  {A_E_null_op_l_act_is_two_l_unl : IsTwoLUnl A E null_op l_act}
  {B_D_null_op_r_act_is_two_r_unl : IsTwoRUnl B D null_op r_act}
  {B_E_null_op_r_act_is_two_r_unl : IsTwoRUnl B E null_op r_act} :
  IsIso _ _ bihomogen_has_iso.
Proof.
  split.
  - intros x. apply proof_irrelevance.
  - intros x. apply proof_irrelevance. Qed.

End Context.
