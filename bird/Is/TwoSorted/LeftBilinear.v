From Maniunfold.Has Require Export
  OneSorted.UnaryOperation OneSorted.Addition TwoSorted.LeftAction
  OneSorted.Addition OneSorted.Zero OneSorted.Negation
  OneSorted.Multiplication OneSorted.One
  ThreeSorted.BinaryFunction.
From Maniunfold.Is Require Export
  TwoSorted.LeftDistributive ThreeSorted.Bicompatible TwoSorted.LeftLinear
  OneSorted.CommutativeRing TwoSorted.LeftModule TwoSorted.RightModule
  ThreeSorted.Bimodule.
From Maniunfold.ShouldHave Require Import
  OneSorted.ArithmeticNotations TwoSorted.MultiplicativeNotations.

(** TODO Check this and find a justification for the higher-sortedness. *)

Class IsLBilin {A B : Type}
  (A_has_add : HasAdd A) (B_has_add : HasAdd B)
  (A_B_has_l_act : HasLAct A B) : Prop := {
  add_add_l_act_is_two_l_distr :> IsTwoLDistr add add l_act;
  add_l_act_is_bicompat :> IsBicompat add l_act;
  l_act_add_is_bicompat :> IsBicompat l_act add;
}.

(** TODO This is a more verbatim translation of literature. *)

Class IsBilinMapComm {A B C D : Type}
  (A_has_add : HasAdd A) (A_has_zero : HasZero A) (A_has_neg : HasNeg A)
  (A_has_mul : HasMul A) (A_has_one : HasOne A)
  (B_has_add : HasAdd B) (B_has_zero : HasZero B) (B_has_neg : HasNeg B)
  (A_B_has_l_act : HasLAct A B)
  (C_has_add : HasAdd C) (C_has_zero : HasZero C) (C_has_neg : HasNeg C)
  (A_C_has_l_act : HasLAct A C)
  (D_has_add : HasAdd D) (D_has_zero : HasZero D) (D_has_neg : HasNeg D)
  (A_D_has_l_act : HasLAct A D) : Prop := {
  A_add_zero_neg_mul_one_is_comm_ring :>
    IsCommRing (A := A) add zero neg mul one;
  A_B_add_zero_neg_mul_one_add_zero_neg_l_act_is_l_mod :>
    IsLMod (A := A) (B := B) add zero neg mul one add zero neg l_act;
  A_C_add_zero_neg_mul_one_add_zero_neg_l_act_is_l_mod :>
    IsLMod (A := A) (B := C) add zero neg mul one add zero neg l_act;
  A_D_add_zero_neg_mul_one_add_zero_neg_l_act_is_l_mod :>
    IsLMod (A := A) (B := D) add zero neg mul one add zero neg l_act;
  (** Linearity goes here. *)
}.

(* LeftBihomogeneous *)
Class IsLBihomogen {A B C D : Type}
  (A_B_has_l_act : HasLAct A B) (A_D_has_l_act : HasLAct A D)
  (B_C_D_has_bin_fn : HasBinFn B C D) : Prop :=
  l_bihomogen : forall a x y,
    bin_fn (a L* x) y = a L* bin_fn x y.

(* RightBihomogeneous *)
Class IsRBihomogen {A B C D : Type}
  (A_C_has_r_act : HasRAct A C) (A_D_has_r_act : HasRAct A D)
  (B_C_D_has_bin_fn : HasBinFn B C D) : Prop :=
  r_bihomogen : forall a x y,
    bin_fn x (y R* a) = bin_fn x y R* a.

(* Bihomogeneous *)
Class IsBihomogen {A B C D : Type}
  (A_B_has_l_act : HasLAct A B) (A_C_has_r_act : HasRAct A C)
  (A_D_has_l_act : HasLAct A D) (A_D_has_r_act : HasRAct A D)
  (B_C_D_has_bin_fn : HasBinFn B C D) : Prop :=
  bihomogen : forall a b x y,
    bin_fn (a L* x) (y R* b) = a L* bin_fn x y R* b.

(* LeftBiadditive *)
Class IsLBiadditive {A B C : Type}
  (A_has_add : HasAdd A) (C_has_add : HasAdd C)
  (A_B_C_has_bin_fn : HasBinFn A B C) : Prop :=
  l_biadditive : forall x y z, bin_fn (x + y) z = bin_fn x z + bin_fn y z.

(* RightBiadditive *)
Class IsRBiadditive {A B C : Type}
  (B_has_add : HasAdd B) (C_has_add : HasAdd C)
  (A_B_C_has_bin_fn : HasBinFn A B C) : Prop :=
  r_biadditive : forall x y z, bin_fn x (y + z) = bin_fn x y + bin_fn x z.

(* BilinearMap *)
Class IsBilinMap {A B C D E : Type}
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
  A_C_etc_is_l_mod :>
    IsLMod (A := A) (B := C) add zero neg mul one add zero neg l_act;
  B_D_etc_is_r_mod :>
    IsRMod (A := B) (B := D) add zero neg mul one add zero neg r_act;
  A_B_E_etc_is_bimod :> IsBimod (A := A) (B := B) (C := E)
    add zero neg mul one add zero neg mul one add zero neg l_act r_act;
  l_act_l_act_fn_is_l_bihomogen :>
    IsLBihomogen l_act l_act bin_fn;
  r_act_r_act_fn_is_r_bihomogen :>
    IsRBihomogen r_act r_act bin_fn;
  add_add_fn_is_l_biadditive :>
    IsLBiadditive add add bin_fn;
  add_add_fn_is_r_biadditive :>
    IsRBiadditive add add bin_fn;
}.

(** TODO Bilinear forms are symmetric bilinear maps, so why not say so. *)

(*
Class IsLBilin' {A B : Type}
  (A_has_add : HasAdd A) (B_has_add : HasAdd B)
  (A_B_has_l_act : HasLAct A B) : Prop := {
  add_is_l_lin :> forall y : _, IsLLin add (fun x => x + y) l_act;
  flip_add_is_l_lin :> forall x : _, IsLLin add (fun y => x + y) l_act;
}.
*)

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
