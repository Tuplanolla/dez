From Coq Require Import
  Logic.ProofIrrelevance.
From Maniunfold.Has Require Export
  OneSorted.UnaryOperation OneSorted.Addition TwoSorted.LeftAction
  OneSorted.Addition OneSorted.Zero OneSorted.Negation
  OneSorted.Multiplication OneSorted.One
  ThreeSorted.BinaryFunction.
From Maniunfold.Is Require Export
  TwoSorted.LeftDistributive ThreeSorted.Bicompatible TwoSorted.LeftLinear
  OneSorted.CommutativeRing TwoSorted.LeftModule TwoSorted.RightModule
  ThreeSorted.Bimodule
  TwoSorted.Unital TwoSorted.Isomorphism.
From Maniunfold.ShouldHave Require Import
  OneSorted.ArithmeticNotations TwoSorted.MultiplicativeNotations.

(* BothBihomogeneous *)
Class IsBBihomogen (A B C D E : Type)
  (A_C_has_l_act : HasLAct A C) (B_D_has_r_act : HasRAct B D)
  (A_E_has_l_act : HasLAct A E) (B_E_has_r_act : HasRAct B E)
  (C_D_E_has_bin_fn : HasBinFn C D E) : Prop :=
  b_bihomogen : forall (a : A) (b : B) (x : C) (y : D),
    bin_fn (a L* x) (y R* b) = a L* bin_fn x y R* b.

(* LeftBihomogeneous *)
Class IsLBihomogen (A B C D : Type)
  (A_B_has_l_act : HasLAct A B) (A_D_has_l_act : HasLAct A D)
  (B_C_D_has_bin_fn : HasBinFn B C D) : Prop :=
  l_bihomogen : forall (a : A) (x : B) (y : C),
    bin_fn (a L* x) y = a L* bin_fn x y.

(* RightBihomogeneous *)
Class IsRBihomogen (A B C D : Type)
  (A_C_has_r_act : HasRAct A C) (A_D_has_r_act : HasRAct A D)
  (B_C_D_has_bin_fn : HasBinFn B C D) : Prop :=
  r_bihomogen : forall (a : A) (x : B) (y : C),
    bin_fn x (y R* a) = bin_fn x y R* a.

(* Bihomogeneous *)
Class IsBihomogen (A B C D E : Type)
  (A_C_has_l_act : HasLAct A C) (B_D_has_r_act : HasRAct B D)
  (A_E_has_l_act : HasLAct A E) (B_E_has_r_act : HasRAct B E)
  (C_D_E_has_bin_fn : HasBinFn C D E) : Prop := {
  A_C_D_E_l_act_l_act_bin_fn_is_l_bihomogen :>
    IsLBihomogen A C D E l_act l_act bin_fn;
  B_C_D_E_r_act_r_act_bin_fn_is_r_bihomogen :>
    IsRBihomogen B C D E r_act r_act bin_fn;
}.

(* LeftBiadditive *)
Class IsLBiaddve (A B C : Type)
  (A_has_add : HasAdd A) (C_has_add : HasAdd C)
  (A_B_C_has_bin_fn : HasBinFn A B C) : Prop :=
  l_biaddve : forall (x y : A) (z : B),
    bin_fn (x + y) z = bin_fn x z + bin_fn y z.

(* RightBiadditive *)
Class IsRBiaddve (A B C : Type)
  (B_has_add : HasAdd B) (C_has_add : HasAdd C)
  (A_B_C_has_bin_fn : HasBinFn A B C) : Prop :=
  r_biaddve : forall (x : A) (y z : B),
    bin_fn x (y + z) = bin_fn x y + bin_fn x z.

(* Biadditive *)
Class IsBiaddve (A B C : Type)
  (A_has_add : HasAdd A) (B_has_add : HasAdd B) (C_has_add : HasAdd C)
  (A_B_C_has_bin_fn : HasBinFn A B C) : Prop := {
  l_act_l_act_fn_is_l_biaddve :>
    IsLBiaddve A B C add add bin_fn;
  r_act_r_act_fn_is_r_biaddve :>
    IsRBiaddve A B C add add bin_fn;
}.

(** Here, [A] and [B] are rings, [C] and [D] are domain modules over each and
    [E] is the range bimodule over both. *)

(* BilinearMap *)
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
  A_C_etc_is_l_mod :> IsLMod A C add zero neg mul one add zero neg l_act;
  B_D_etc_is_r_mod :> IsRMod B D add zero neg mul one add zero neg r_act;
  A_B_E_etc_is_bimod :> IsBimod A B E
    add zero neg mul one add zero neg mul one add zero neg l_act r_act;
  etc_bin_fn_is_bihomogen :> IsBihomogen A B C D E
    l_act r_act l_act r_act bin_fn;
  add_add_add_bin_fn_is_biaddve :> IsBiaddve C D E add add add bin_fn;
}.

Class IsBilinOp (A B : Type)
  (A_has_add : HasAdd A) (A_has_zero : HasZero A) (A_has_neg : HasNeg A)
  (A_has_mul : HasMul A) (A_has_one : HasOne A)
  (B_has_add : HasAdd B) (B_has_zero : HasZero B) (B_has_neg : HasNeg B)
  (A_B_has_l_act : HasLAct A B) (A_B_has_r_act : HasRAct A B)
  (B_has_bin_op : HasBinOp B) : Prop :=
  A_A_B_B_B_add_zero_neg_mul_one_add_zero_neg_mul_one_add_zero_neg_add_zero_neg_add_zero_neg_l_act_r_act_l_act_r_act_bin_fn_is_bilin_map
    :> IsBilinMap A A B B B
    add zero neg mul one add zero neg mul one
    add zero neg add zero neg add zero neg l_act r_act l_act r_act bin_fn.

(** TODO Bilinear forms are symmetric bilinear maps, so why not say so. *)

(*
Class IsLBilin' (A B : Type)
  (A_has_add : HasAdd A) (B_has_add : HasAdd B)
  (A_B_has_l_act : HasLAct A B) : Prop := {
  add_is_l_lin :> forall y : _, IsLLin add (fun x => x + y) l_act;
  flip_add_is_l_lin :> forall x : _, IsLLin add (fun y => x + y) l_act;
}.
*)

Global Instance bihomogen_has_iso {A B C D E : Type}
  {A_C_has_l_act : HasLAct A C} {B_D_has_r_act : HasRAct B D}
  {A_E_has_l_act : HasLAct A E} {B_E_has_r_act : HasRAct B E}
  {C_D_E_has_bin_fn : HasBinFn C D E}
  (** These classes are not equivalent unless the actions are unital. *)
  {A_has_l_null_op : HasLNullOp A} {A_has_r_null_op : HasRNullOp A}
  {B_has_l_null_op : HasLNullOp B} {B_has_r_null_op : HasRNullOp B}
  {A_C_l_null_op_l_act_is_two_l_unl : IsTwoLUnl A C l_null_op l_act}
  {A_E_l_null_op_l_act_is_two_l_unl : IsTwoLUnl A E l_null_op l_act}
  {B_D_l_null_op_r_act_is_two_r_unl : IsTwoRUnl B D r_null_op r_act}
  {B_E_l_null_op_r_act_is_two_r_unl : IsTwoRUnl B E r_null_op r_act} :
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
      rewrite (two_r_unl (a L* bin_fn b x)).
      reflexivity.
    + intros a x y.
      rewrite <- (two_l_unl x).
      rewrite b_bihomogen.
      rewrite (two_l_unl x).
      rewrite (two_l_unl (bin_fn x y)).
      reflexivity. Defined.

(** Life with proof irrelevance is dull. *)

Global Instance bihomogen_is_iso {A B C D E : Type}
  {A_C_has_l_act : HasLAct A C} {B_D_has_r_act : HasRAct B D}
  {A_E_has_l_act : HasLAct A E} {B_E_has_r_act : HasRAct B E}
  {C_D_E_has_bin_fn : HasBinFn C D E}
  (** These classes are not equivalent unless the actions are unital. *)
  {A_has_l_null_op : HasLNullOp A} {A_has_r_null_op : HasRNullOp A}
  {B_has_l_null_op : HasLNullOp B} {B_has_r_null_op : HasRNullOp B}
  {A_C_l_null_op_l_act_is_two_l_unl : IsTwoLUnl A C l_null_op l_act}
  {A_E_l_null_op_l_act_is_two_l_unl : IsTwoLUnl A E l_null_op l_act}
  {B_D_l_null_op_r_act_is_two_r_unl : IsTwoRUnl B D r_null_op r_act}
  {B_E_l_null_op_r_act_is_two_r_unl : IsTwoRUnl B E r_null_op r_act} :
  IsIso _ _ bihomogen_has_iso.
Proof.
  split.
  - intros x. apply proof_irrelevance.
  - intros x. apply proof_irrelevance. Qed.

(** TODO Figure out which formulation is better.

<<
IsBilin iff
- IsLin (fun x => x + y)
- IsLin (fun y => x + y).
IsBilin iff
- IsTwoLDistr add l_act
- IsBicompat add l_act
- IsBicompat l_act add.
>> *)
