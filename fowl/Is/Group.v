(** * Group Structure *)

From DEZ.Has Require Export
  EquivalenceRelation NullaryOperation UnaryOperation BinaryOperation Action.
From DEZ.Is Require Export
  Monoid Invertible Proper
  Fixed Involutive Injective Cancellative Distributive Preserving.
From DEZ.Supports Require Import
  AdditiveNotations EquivalenceNotations.

(** ** Group *)

Class IsGrp (A : Type) (X : A -> A -> Prop)
  (x : A) (f : A -> A) (k : A -> A -> A) : Prop := {
  grp_is_mon :> IsMon X x k;
  grp_is_inv :> IsInv X x f k;
  grp_is_proper :> IsProper (X ==> X) f;
}.

Section Context.

Context (A : Type) (X : A -> A -> Prop)
  (x : A) (f : A -> A) (k : A -> A -> A) `{!IsGrp X x f k}.

#[local] Instance has_equiv_rel : HasEquivRel A := X.
#[local] Instance has_null_op : HasNullOp A := x.
#[local] Instance has_un_op : HasUnOp A := f.
#[local] Instance has_bin_op : HasBinOp A := k.

Ltac note := progress (
  try change X with (equiv_rel (A := A)) in *;
  try change x with (null_op (A := A)) in *;
  try change f with (un_op (A := A)) in *;
  try change k with (bin_op (A := A)) in *).

#[export] Instance grp_is_fixed : IsFixed X x f.
Proof.
  note. unfold IsFixed, IsFixed2.
  setoid_rewrite <- (unl_r (- x)).
  setoid_rewrite (inv_l x).
  reflexivity. Qed.

#[export] Instance grp_is_invol : IsInvol X f.
Proof.
  note. intros y.
  setoid_rewrite <- (unl_r (- (- y))).
  setoid_rewrite <- (inv_l y).
  setoid_rewrite (assoc (- (- y)) (- y) y).
  setoid_rewrite (inv_l (- y)).
  setoid_rewrite (unl_l y).
  reflexivity. Qed.

#[export] Instance grp_is_inj : IsInj X f.
Proof.
  note. intros y z a.
  setoid_rewrite <- (unl_l z).
  setoid_rewrite <- (inv_r y).
  setoid_rewrite a.
  setoid_rewrite <- (assoc y (- z) z).
  setoid_rewrite (inv_l z).
  setoid_rewrite (unl_r y).
  reflexivity. Qed.

#[export] Instance grp_is_cancel_l : IsCancelL X k.
Proof.
  note. intros y z w a.
  setoid_rewrite <- (unl_l y).
  setoid_rewrite <- (inv_l w).
  setoid_rewrite <- (assoc (- w) w y).
  setoid_rewrite a.
  setoid_rewrite (assoc (- w) w z).
  setoid_rewrite (inv_l w).
  setoid_rewrite (unl_l z).
  reflexivity. Qed.

#[export] Instance grp_is_cancel_r : IsCancelR X k.
Proof.
  note. intros y z w a.
  setoid_rewrite <- (unl_r y).
  setoid_rewrite <- (inv_r w).
  setoid_rewrite (assoc y w (- w)).
  setoid_rewrite a.
  setoid_rewrite <- (assoc z w (- w)).
  setoid_rewrite (inv_r w).
  setoid_rewrite (unl_r z).
  reflexivity. Qed.

#[export] Instance grp_is_cancel : IsCancel X k.
Proof. esplit; typeclasses eauto. Qed.

#[export] Instance grp_is_antidistr : IsAntidistr X f k k.
Proof.
  note. intros y z.
  apply (cancel_l (- (y + z)) ((- z) + (- y)) (y + z)).
  setoid_rewrite (inv_r (y + z)).
  setoid_rewrite (assoc (y + z) (- z) (- y)).
  setoid_rewrite <- (assoc y z (- z)).
  setoid_rewrite (inv_r z).
  setoid_rewrite (unl_r y).
  setoid_rewrite (inv_r y).
  reflexivity. Qed.

End Context.

From Coq Require Import
  ZArith.ZArith.

Section Context.

Context (A : Type)
  {X : HasEquivRel A} {x : HasNullOp A} {f : HasUnOp A} {k : HasBinOp A}
  `{!IsGrp X x f k}.

Equations rep (n : Z) (y : A) : A :=
  rep Z0 y := 0;
  rep (Zpos n) y := Pos.iter_op _+_ n y;
  rep (Zneg n) y := - Pos.iter_op _+_ n y.

End Context.

(** ** Group Homomorphism *)

Class IsGrpHom (A B : Type)
  (X : A -> A -> Prop) (x : A) (f : A -> A) (k : A -> A -> A)
  (Y : B -> B -> Prop) (y : B) (g : B -> B) (m : B -> B -> B)
  (h : A -> B) : Prop := {
  grp_hom_dom_is_grp :> IsGrp X x f k;
  grp_hom_codom_is_grp :> IsGrp Y y g m;
  grp_hom_is_bin_pres :> IsBinPres Y k m h;
  grp_hom_is_proper :> IsProper (X ==> Y) h;
}.

Section Context.

Context (A B : Type)
  (X : A -> A -> Prop) (x : A) (f : A -> A) (k : A -> A -> A)
  (Y : B -> B -> Prop) (y : B) (g : B -> B) (m : B -> B -> B)
  (h : A -> B) `{!IsGrpHom X x f k Y y g m h}.

#[local] Instance dom_has_equiv_rel : HasEquivRel A := X.
#[local] Instance dom_has_null_op : HasNullOp A := x.
#[local] Instance dom_has_un_op : HasUnOp A := f.
#[local] Instance dom_has_bin_op : HasBinOp A := k.
#[local] Instance codom_has_equiv_rel : HasEquivRel B := Y.
#[local] Instance codom_has_null_op : HasNullOp B := y.
#[local] Instance codom_has_un_op : HasUnOp B := g.
#[local] Instance codom_has_bin_op : HasBinOp B := m.

Ltac note := progress (
  try change X with (equiv_rel (A := A)) in *;
  try change x with (null_op (A := A)) in *;
  try change f with (un_op (A := A)) in *;
  try change k with (bin_op (A := A)) in *;
  try change Y with (equiv_rel (A := B)) in *;
  try change y with (null_op (A := B)) in *;
  try change g with (un_op (A := B)) in *;
  try change m with (bin_op (A := B)) in *).

#[export] Instance grp_hom_is_null_pres : IsNullPres Y x y h.
Proof.
  unfold IsNullPres. note.
  pose proof bin_pres 0 0 as a.
  setoid_rewrite <- (unl_r (h (0 + 0))) in a.
  setoid_rewrite (unl_l 0) in a.
  apply cancel_l in a.
  setoid_rewrite <- a.
  reflexivity. Qed.

#[export] Instance grp_hom_is_un_pres : IsUnPres Y f g h.
Proof.
  note. intros z.
  pose proof bin_pres z (- z) as a.
  setoid_rewrite (inv_r z) in a.
  eapply cancel_l with (h z).
  setoid_rewrite <- a.
  setoid_rewrite inv_r.
  apply null_pres. Qed.

End Context.

(** ** Left Group Action *)

Class IsGrpActL (A B : Type)
  (X : A -> A -> Prop) (x : A) (f : A -> A) (k : A -> A -> A)
  (Y : B -> B -> Prop) (al : A -> B -> B) : Prop := {
  grp_act_l_is_grp :> IsGrp X x f k;
  grp_act_l_is_unl_l :> IsUnlL Y x al;
  grp_act_l_is_assoc :> IsCompatL Y k al;
  grp_act_l_is_proper :> IsProper (X ==> Y ==> Y) al;
}.
