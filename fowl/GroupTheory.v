From Coq Require Import
  Lists.List ZArith.ZArith Lia.
From DEZ.Has Require Export
  Relations Operations Decisions.
From DEZ.Is Require Export
  Monoid Invertible Proper Injective Preserving.
From DEZ.Provides Require Export
  FreeTheorems.
From DEZ.ShouldHave Require Import
  EquivalenceNotations AdditiveNotations.

Import ListNotations.

#[local] Open Scope sig_scope.

Module Group.

Class IsGrp (A : Type) (X : A -> A -> Prop)
  (x : A) (f : A -> A) (k : A -> A -> A) : Prop := {
  is_mon :> IsMon X x k;
  is_inv_l_r :> IsInvLR X x f k;
  is_proper :> IsProper (X ==> X) f;
}.

Class IsComm (A : Type) (X : A -> A -> Prop) (k : A -> A -> A) : Prop :=
  comm (x y : A) : X (k x y) (k y x).

Class IsAbGrp (A : Type) (X : A -> A -> Prop)
  (x : A) (f : A -> A) (k : A -> A -> A) : Prop := {
  is_grp :> IsGrp X x f k;
  is_comm :> IsComm X k;
}.

Section Context.

Context (A : Type)
  (X : A -> A -> Prop) (x : A) (f : A -> A) (k : A -> A -> A)
  `{!IsGrp X x f k}.

#[local] Instance has_eq_rel : HasEqRel A := X.
#[local] Instance has_null_op : HasNullOp A := x.
#[local] Instance has_un_op : HasUnOp A := f.
#[local] Instance has_bin_op : HasBinOp A := k.

Ltac note := progress (
  try change X with (eq_rel (A := A)) in *;
  try change x with (null_op (A := A)) in *;
  try change f with (un_op (A := A)) in *;
  try change k with (bin_op (A := A)) in *).

#[export] Instance is_inj : IsInj X f.
Proof.
  note. intros y z a.
  rewrite <- (unl_l z). rewrite <- (inv_r y).
  rewrite a. rewrite <- (assoc y (- z) z).
  rewrite (inv_l z). rewrite (unl_r y).
  reflexivity. Qed.

End Context.

Class IsGrpHom (A B : Type)
  (X : A -> A -> Prop) (x : A) (f : A -> A) (k : A -> A -> A)
  (Y : B -> B -> Prop) (y : B) (g : B -> B) (m : B -> B -> B)
  (h : A -> B) : Prop := {
  dom_is_grp :> IsGrp X x f k;
  codom_is_grp :> IsGrp Y y g m;
  hom_is_bin_pres :> IsBinPres Y k m h;
  hom_is_proper :> IsProper (X ==> Y) h;
}.

Class IsGrpActL (A B : Type)
  (X : A -> A -> Prop) (x : A) (f : A -> A) (k : A -> A -> A)
  (Y : B -> B -> Prop) (a : A -> B -> B) : Prop := {
  act_is_grp :> IsGrp X x f k;
  act_is_unl_l :> IsUnlL Y x a;
  act_is_assoc :> IsCompatL Y k a;
  act_is_proper :> IsProper (X ==> Y ==> Y) a;
}.

End Group.

Module Groups.

Export Group.

Ltac ecrush :=
  repeat (try typeclasses eauto; esplit);
  hnf in *; repeat match goal with
  | |- exists _ : unit, _ => exists tt
  | |- forall _ : unit, _ => intros ?
  | x : unit |- _ => destruct x
  end; eauto with zarith.

Module Free.

Section Context.

Context (A : Type) {e : HasEqDec A}.

Equations wfb_def (a b : bool * A) : bool :=
  wfb_def (i, x) (j, y) := decide (~ (i <> j /\ x = y)).

Equations wfb (s : list (bool * A)) : bool :=
  wfb s := decide (Forall (prod_uncurry wfb_def) (combine s (skipn 1 s))).

Equations free : Type :=
  free := {s : list (bool * A) | wfb s}.

Lemma free_iff (x y : free) : x = y <-> proj1_sig x = proj1_sig y.
Proof.
  destruct x as [s a], y as [t b]. unfold proj1_sig. split.
  - intros c. inversion c as [d]. subst t. reflexivity.
  - intros d. subst t. f_equal. apply uip. Qed.

Equations null : free :=
  null := ([]; _).
Next Obligation. ecrush. Qed.

Equations un (x : free) : free :=
  un (s; _) := (map (prod_bimap negb id) (rev s); _).
Next Obligation. Admitted.

Equations bin_fix (s t : list (bool * A)) :
  list (bool * A) * list (bool * A) by struct t :=
  bin_fix [] t := ([], t);
  bin_fix s [] := (s, []);
  bin_fix (a :: s) (b :: t) with wfb_def a b :=
    | true => (a :: s, b :: t)
    | false => bin_fix s t.

Equations bin (x y : free) : free :=
  bin (s; _) (t; _) with bin_fix (rev s) t :=
    | (u, v) => (app (rev u) v; _).
Next Obligation. Admitted.

#[export] Instance has_eq_rel : HasEqRel free := eq.
#[export] Instance has_null_op : HasNullOp free := null.
#[export] Instance has_un_op : HasUnOp free := un.
#[export] Instance has_bin_op : HasBinOp free := bin.

#[export] Instance is_grp : IsGrp eq null un bin.
Proof. Admitted.

End Context.

Arguments free _ {_}.

End Free.

Module BinaryIntegers.

Module Additive.

#[export] Instance has_eq_rel : HasEqRel Z := eq.
#[export] Instance has_null_op : HasNullOp Z := Z.zero.
#[export] Instance has_un_op : HasUnOp Z := Z.opp.
#[export] Instance has_bin_op : HasBinOp Z := Z.add.

#[export] Instance is_grp : IsGrp eq Z.zero Z.opp Z.add.
Proof. ecrush. Qed.

End Additive.

End BinaryIntegers.

Section Context.

Context (A : Type)
  {X : HasEqRel A} {x : HasNullOp A} {f : HasUnOp A} {k : HasBinOp A}
  `{!IsGrp X x f k}.

Equations rep (n : Z) (y : A) : A :=
  rep Z0 y := 0;
  rep (Zpos n) y := Pos.iter_op _+_ n y;
  rep (Zneg n) y := - Pos.iter_op _+_ n y.

End Context.

Section Context.

Context (A : Type)
  (X : A -> A -> Prop) (x : A) (f : A -> A) (k : A -> A -> A)
  `{!IsGrp X x f k}.

#[local] Instance has_eq_rel : HasEqRel A := X.
#[local] Instance has_null_op : HasNullOp A := x.
#[local] Instance has_un_op : HasUnOp A := f.
#[local] Instance has_bin_op : HasBinOp A := k.

#[local] Instance is_grp_hom (y : A) :
  IsGrpHom eq Z.zero Z.opp Z.add X x f k (flip rep y).
Proof. Admitted.

End Context.

Module Trivial.

Equations tt1 (x : unit) : unit :=
  tt1 _ := tt.

Equations tt2 (x y : unit) : unit :=
  tt2 _ _ := tt.

#[export] Instance has_eq_rel : HasEqRel unit := eq.
#[export] Instance has_null_op : HasNullOp unit := tt.
#[export] Instance has_un_op : HasUnOp unit := tt1.
#[export] Instance has_bin_op : HasBinOp unit := tt2.

#[export] Instance is_grp : IsGrp eq tt tt1 tt2.
Proof. ecrush. Qed.

End Trivial.

Module Initial.

Export Free BinaryIntegers.Additive.

Section Context.

Context (A : Type) {e : HasEqDec A} (f : A -> Z).

Equations eval_Z_add_def (a : bool * A) : Z :=
  eval_Z_add_def (false, x) := f x;
  eval_Z_add_def (true, x) := - f x.

Equations eval_Z_add (x : free A) : Z :=
  eval_Z_add (s; _) := fold_right _+_ 0 (map eval_Z_add_def s).

#[local] Instance is_grp_hom :
  IsGrpHom eq null un bin eq Z.zero Z.opp Z.add eval_Z_add.
Proof. Admitted.

End Context.

End Initial.

Module Terminal.

Export Trivial.

Section Context.

Context (A : Type)
  (X : A -> A -> Prop) (x : A) (f : A -> A) (k : A -> A -> A)
  `{!IsGrp X x f k}.

#[local] Instance is_grp_hom : IsGrpHom X x f k eq tt tt1 tt2 (const tt).
Proof. ecrush. Qed.

End Context.

End Terminal.

End Groups.

From Coq Require Import Extraction ExtrOcamlBasic ExtrOcamlZBigInt.

Extraction "groupTheory.ml" Groups.
