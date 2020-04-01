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

(** TODO Check this and find a justification for the higher-sortedness. *)

Class IsLBilin {A B : Type}
  (A_has_add : HasAdd A) (B_has_add : HasAdd B)
  (A_B_has_l_act : HasLAct A B) : Prop := {
  add_add_l_act_is_two_l_distr :> IsTwoLDistr add add l_act;
  add_l_act_is_bicompat :> IsBicompat add l_act;
  l_act_add_is_bicompat :> IsBicompat l_act add;
}.

(* BothBihomogeneous *)
Class IsBBihomogen {A B C D : Type}
  (A_B_has_l_act : HasLAct A B) (A_C_has_r_act : HasRAct A C)
  (A_D_has_l_act : HasLAct A D) (A_D_has_r_act : HasRAct A D)
  (B_C_D_has_bin_fn : HasBinFn B C D) : Prop :=
  b_bihomogen : forall (a b : A) (x : B) (y : C),
    bin_fn (a L* x) (y R* b) = a L* bin_fn x y R* b.

(* LeftBihomogeneous *)
Class IsLBihomogen {A B C D : Type}
  (A_B_has_l_act : HasLAct A B) (A_D_has_l_act : HasLAct A D)
  (B_C_D_has_bin_fn : HasBinFn B C D) : Prop :=
  l_bihomogen : forall (a : A) (x : B) (y : C),
    bin_fn (a L* x) y = a L* bin_fn x y.

(* RightBihomogeneous *)
Class IsRBihomogen {A B C D : Type}
  (A_C_has_r_act : HasRAct A C) (A_D_has_r_act : HasRAct A D)
  (B_C_D_has_bin_fn : HasBinFn B C D) : Prop :=
  r_bihomogen : forall (a : A) (x : B) (y : C),
    bin_fn x (y R* a) = bin_fn x y R* a.

(* Bihomogeneous *)
Class IsBihomogen {A B C D : Type}
  (A_B_has_l_act : HasLAct A B) (A_C_has_r_act : HasRAct A C)
  (A_D_has_l_act : HasLAct A D) (A_D_has_r_act : HasRAct A D)
  (B_C_D_has_bin_fn : HasBinFn B C D) : Prop := {
  l_act_l_act_fn_is_l_bihomogen :>
    IsLBihomogen (A := A) (B := B) (C := C) (D := D) l_act l_act bin_fn;
  r_act_r_act_fn_is_r_bihomogen :>
    IsRBihomogen (A := A) (B := B) (C := C) (D := D) r_act r_act bin_fn;
}.

(* LeftBiadditive *)
Class IsLBiaddve {A B C : Type}
  (A_has_add : HasAdd A) (C_has_add : HasAdd C)
  (A_B_C_has_bin_fn : HasBinFn A B C) : Prop :=
  l_biaddve : forall (x y : A) (z : B),
    bin_fn (x + y) z = bin_fn x z + bin_fn y z.

(* RightBiadditive *)
Class IsRBiaddve {A B C : Type}
  (B_has_add : HasAdd B) (C_has_add : HasAdd C)
  (A_B_C_has_bin_fn : HasBinFn A B C) : Prop :=
  r_biaddve : forall (x : A) (y z : B),
    bin_fn x (y + z) = bin_fn x y + bin_fn x z.

(* Biadditive *)
Class IsBiaddve {A B C : Type}
  (A_has_add : HasAdd A) (B_has_add : HasAdd B) (C_has_add : HasAdd C)
  (A_B_C_has_bin_fn : HasBinFn A B C) : Prop := {
  l_act_l_act_fn_is_l_biaddve :>
    IsLBiaddve (A := A) (B := B) (C := C) add add bin_fn;
  r_act_r_act_fn_is_r_biaddve :>
    IsRBiaddve (A := A) (B := B) (C := C) add add bin_fn;
}.

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
  etc_bin_fn_is_bihomogen :>
    IsBihomogen l_act r_act l_act r_act bin_fn;
  add_add_add_bin_fn_is_biaddve :> IsBiaddve add add add bin_fn;
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

Global Instance bihomogen_has_iso {A B C D : Type}
  {A_B_has_l_act : HasLAct A B} {A_C_has_r_act : HasRAct A C}
  {A_D_has_l_act : HasLAct A D} {A_D_has_r_act : HasRAct A D}
  {B_C_D_has_bin_fn : HasBinFn B C D}
  (** These classes are not equivalent unless the actions are unital. *)
  {A_has_l_null_op : HasLNullOp A} {A_has_r_null_op : HasRNullOp A}
  {A_B_l_null_op_l_act_is_two_l_unl :
    IsTwoLUnl (A := A) (B := B) l_null_op l_act}
  {A_D_l_null_op_l_act_is_two_l_unl :
    IsTwoLUnl (A := A) (B := D) l_null_op l_act}
  {A_C_l_null_op_r_act_is_two_r_unl :
    IsTwoRUnl (A := A) (B := C) r_null_op r_act}
  {A_D_l_null_op_r_act_is_two_r_unl :
    IsTwoRUnl (A := A) (B := D) r_null_op r_act} :
  HasIso (IsBihomogen l_act r_act l_act r_act bin_fn)
  (IsBBihomogen l_act r_act l_act r_act bin_fn).
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

Global Instance bihomogen_is_iso {A B C D : Type}
  {A_B_has_l_act : HasLAct A B} {A_C_has_r_act : HasRAct A C}
  {A_D_has_l_act : HasLAct A D} {A_D_has_r_act : HasRAct A D}
  {B_C_D_has_bin_fn : HasBinFn B C D}
  (** These classes are not equivalent unless the actions are unital. *)
  {A_has_l_null_op : HasLNullOp A} {A_has_r_null_op : HasRNullOp A}
  {A_B_l_null_op_l_act_is_two_l_unl :
    IsTwoLUnl (A := A) (B := B) l_null_op l_act}
  {A_D_l_null_op_l_act_is_two_l_unl :
    IsTwoLUnl (A := A) (B := D) l_null_op l_act}
  {A_C_l_null_op_r_act_is_two_r_unl :
    IsTwoRUnl (A := A) (B := C) r_null_op r_act}
  {A_D_l_null_op_r_act_is_two_r_unl :
    IsTwoRUnl (A := A) (B := D) r_null_op r_act} : IsIso bihomogen_has_iso.
Proof.
  constructor.
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
