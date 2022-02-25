(** * Group Structure *)

From DEZ.Has Require Export
  EquivalenceRelation NullaryOperation UnaryOperation BinaryOperation Action.
From DEZ.Is Require Export
  Monoid Invertible Proper
  Fixed Involutive Injective Cancellative Distributive Preserving.
From DEZ.ShouldHave Require Import
  EquivalenceNotations AdditiveNotations.

(** ** Group *)

Class IsGrp (A : Type) (X : A -> A -> Prop)
  (x : A) (f : A -> A) (k : A -> A -> A) : Prop := {
  is_mon :> IsMon X x k;
  is_inv_l_r :> IsInvLR X x f k;
  is_proper :> IsProper (X ==> X) f;
}.

Section Context.

Context (A : Type) (X : A -> A -> Prop)
  (x : A) (f : A -> A) (k : A -> A -> A)
  `{!IsGrp X x f k}.

#[local] Instance has_equiv_rel : HasEquivRel A := X.
#[local] Instance has_null_op : HasNullOp A := x.
#[local] Instance has_un_op : HasUnOp A := f.
#[local] Instance has_bin_op : HasBinOp A := k.

Ltac note := progress (
  try change X with (equiv_rel (A := A)) in *;
  try change x with (null_op (A := A)) in *;
  try change f with (un_op (A := A)) in *;
  try change k with (bin_op (A := A)) in *).

#[local] Instance is_fixed : IsFixed X x f.
Proof.
  note.
  unfold IsFixed, IsFixed2.
  setoid_rewrite <- (unl_r (- x)).
  setoid_rewrite (inv_l x).
  reflexivity. Qed.

#[local] Instance is_invol : IsInvol X f.
Proof.
  note.
  intros y.
  setoid_rewrite <- (unl_r (- (- y))).
  setoid_rewrite <- (inv_l y).
  setoid_rewrite (assoc (- (- y)) (- y) y).
  setoid_rewrite (inv_l (- y)).
  setoid_rewrite (unl_l y).
  reflexivity. Qed.

#[local] Instance is_inj : IsInj X f.
Proof.
  note.
  intros y z a.
  setoid_rewrite <- (unl_l z).
  setoid_rewrite <- (inv_r y).
  setoid_rewrite a.
  setoid_rewrite <- (assoc y (- z) z).
  setoid_rewrite (inv_l z).
  setoid_rewrite (unl_r y).
  reflexivity. Qed.

#[local] Instance is_cancel_l : IsCancelL X k.
Proof.
  note.
  intros y z w a.
  setoid_rewrite <- (unl_l y).
  setoid_rewrite <- (inv_l w).
  setoid_rewrite <- (assoc (- w) w y).
  setoid_rewrite a.
  setoid_rewrite (assoc (- w) w z).
  setoid_rewrite (inv_l w).
  setoid_rewrite (unl_l z).
  reflexivity. Qed.

#[local] Instance is_cancel_r : IsCancelR X k.
Proof.
  note.
  intros y z w a.
  setoid_rewrite <- (unl_r y).
  setoid_rewrite <- (inv_r w).
  setoid_rewrite (assoc y w (- w)).
  setoid_rewrite a.
  setoid_rewrite <- (assoc z w (- w)).
  setoid_rewrite (inv_r w).
  setoid_rewrite (unl_r z).
  reflexivity. Qed.

#[local] Instance is_cancel_l_r : IsCancelLR X k.
Proof. esplit; typeclasses eauto. Qed.

#[local] Instance is_antidistr : IsAntidistr X f k k.
Proof.
  note.
  intros y z.
  apply (cancel_l (- (y + z)) ((- z) + (- y)) (y + z)).
  setoid_rewrite (inv_r (y + z)).
  setoid_rewrite (assoc (y + z) (- z) (- y)).
  setoid_rewrite <- (assoc y z (- z)).
  setoid_rewrite (inv_r z).
  setoid_rewrite (unl_r y).
  setoid_rewrite (inv_r y).
  reflexivity. Qed.

End Context.

#[export] Hint Resolve is_fixed is_invol is_inj
  is_cancel_l is_cancel_r is_cancel_l_r is_antidistr : typeclass_instances.

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
  dom_is_grp :> IsGrp X x f k;
  codom_is_grp :> IsGrp Y y g m;
  hom_is_bin_pres :> IsBinPres Y k m h;
  hom_is_proper :> IsProper (X ==> Y) h;
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

#[local] Instance hom_is_null_pres : IsNullPres Y x y h.
Proof.
  unfold IsNullPres.
  note.
  pose proof bin_pres 0 0 as a.
  setoid_rewrite <- (unl_r (h (0 + 0))) in a.
  setoid_rewrite (unl_l 0) in a.
  apply cancel_l in a.
  setoid_rewrite <- a.
  reflexivity. Qed.

#[local] Instance hom_is_un_pres : IsUnPres Y f g h.
Proof.
  note.
  intros z.
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
  (Y : B -> B -> Prop) (a : A -> B -> B) : Prop := {
  is_grp :> IsGrp X x f k;
  act_is_unl_l :> IsUnlL Y x a;
  act_is_assoc :> IsCompatL Y k a;
  act_is_proper :> IsProper (X ==> Y ==> Y) a;
}.

(** Now, let us make a mess! *)

From DEZ.Has Require Import
  Decisions.
From DEZ.Is Require Import
  Extensional.
From Coq Require Import
  Extraction Lists.List ZArith.ZArith.

Module Mess.

(** This alternative definition is closer to the one in abstract algebra. *)

Module Existential.

#[local] Reserved Notation "'f'".

Class IsGrp (A : Type) (X : A -> A -> Prop)
  (x : A) (k : A -> A -> A) : Type := {
  is_mon :> IsMon X x k;
  inv_l_r (y : A) : {z : A | X (k z y) x /\ X (k y z) x}
    where "'f'" := (fun x : A => proj1_sig (inv_l_r x));
  is_proper :> IsProper (X ==> X) f;
}.

End Existential.

(** The definitions are equivalent. *)

Section Context.

Lemma choice (A B : Type) (X : A -> B -> Prop) :
  (forall x : A, {y : B | X x y}) -> {f : A -> B | forall x : A, X x (f x)}.
Proof.
  intro Hs. exists (fun x : A => proj1_sig (Hs x)).
  intros x. destruct (Hs x) as [y HX]. cbn. apply HX. Defined.

Lemma cochoice (A B : Type) (X : A -> B -> Prop) :
  {f : A -> B | forall x : A, X x (f x)} -> forall x : A, {y : B | X x y}.
Proof.
  intros [f HX]. intros x. exists (f x). cbn. apply (HX x). Defined.

Lemma choiceT (A B : Type) (X : A -> B -> Type) :
  (forall x : A, {y : B & X x y}) -> {f : A -> B & forall x : A, X x (f x)}.
Proof.
  intro Hs. exists (fun x : A => projT1 (Hs x)).
  intros x. destruct (Hs x) as [y HX]. cbn. apply HX. Defined.

Lemma cochoiceT (A B : Type) (X : A -> B -> Type) :
  {f : A -> B & forall x : A, X x (f x)} -> forall x : A, {y : B & X x y}.
Proof.
  intros [f HX]. intros x. exists (f x). cbn. apply (HX x). Defined.

Lemma sectT `(!IsFunExtDep) (A B : Type) (X : A -> B -> Type)
  (a : forall x : A, {y : B & X x y}) : cochoiceT _ (choiceT a) = a.
Proof.
  unfold choiceT, cochoiceT. apply fun_ext_dep. intros x.
  destruct (a x) as [y b]. f_equal. Defined.

Lemma retrT `(!IsFunExtDep) (A B : Type) (X : A -> B -> Type)
  (a : {f : A -> B & forall x : A, X x (f x)}) : choiceT (cochoiceT _ a) = a.
Proof.
  unfold choiceT, cochoiceT. destruct a as [f b]. f_equal. Defined.

Context (A : Type) (X : A -> A -> Prop)
  (x : A) (k : A -> A -> A).

Lemma herbrandize : {f : A -> A | IsGrp X x f k} -> Existential.IsGrp X x k.
Proof.
  intros [f ?]. esplit. all: shelve. Unshelve.
  - intros y. exists (f y). split.
    + apply inv_l.
    + apply inv_r.
  - typeclasses eauto.
  - intros y z a. cbv. apply is_proper. apply a. Defined.

Lemma skolemize : Existential.IsGrp X x k -> {f : A -> A | IsGrp X x f k}.
Proof.
  intros ?.
  set (f (y : A) := proj1_sig (Existential.inv_l_r y)).
  set (g (y : A) := proj2_sig (Existential.inv_l_r y)).
  exists f. esplit.
  - typeclasses eauto.
  - split.
    + intros y. destruct (g y) as [l r]. apply l.
    + intros y. destruct (g y) as [l r]. apply r.
  - typeclasses eauto. Defined.

End Context.

End Mess.
