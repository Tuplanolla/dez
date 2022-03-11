(** * Group Structure *)

From DEZ.Has Require Export
  EquivalenceRelations Operations Actions.
From DEZ.Is Require Export
  Monoid Invertible Proper
  Fixed Involutive Injective Cancellative Antidistributive
  Preserving Unital Compatible Associative.
From DEZ.Supports Require Import
  EquivalenceNotations AdditiveNotations.

#[local] Open Scope core_scope.

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

(** Zero is a fixed point of negation. *)

#[export] Instance grp_is_fixed : IsFixed X x f.
Proof.
  hnf. note.
  setoid_rewrite <- (unl_r (- x)).
  setoid_rewrite (inv_l x).
  reflexivity. Qed.

(** Negation is an involution. *)

#[export] Instance grp_is_invol : IsInvol X f.
Proof.
  note. intros y.
  setoid_rewrite <- (unl_r (- (- y))).
  setoid_rewrite <- (inv_l y).
  setoid_rewrite (assoc (- (- y)) (- y) y).
  setoid_rewrite (inv_l (- y)).
  setoid_rewrite (unl_l y).
  reflexivity. Qed.

(** Negation is injective. *)

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

(** Addition is left-cancellative. *)

#[local] Instance grp_is_cancel_l : IsCancelL X k.
Proof.
  note. intros y z w a.
  setoid_rewrite <- (unl_l z).
  setoid_rewrite <- (inv_l y).
  setoid_rewrite <- (assoc (- y) y z).
  setoid_rewrite a.
  setoid_rewrite (assoc (- y) y w).
  setoid_rewrite (inv_l y).
  setoid_rewrite (unl_l w).
  reflexivity. Qed.

(** Addition is right-cancellative. *)

#[local] Instance grp_is_cancel_r : IsCancelR X k.
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

(** Addition is cancellative. *)

#[export] Instance grp_is_cancel : IsCancel X k.
Proof. esplit; typeclasses eauto. Qed.

(** Negation antidistributes over addition. *)

#[export] Instance grp_is_antidistr_un_op : IsAntidistrUnOp X f k.
Proof.
  note. intros y z.
  eapply (cancel_l (y + z) (- (y + z)) ((- z) + (- y))).
  setoid_rewrite (inv_r (y + z)).
  setoid_rewrite (assoc (y + z) (- z) (- y)).
  setoid_rewrite <- (assoc y z (- z)).
  setoid_rewrite (inv_r z).
  setoid_rewrite (unl_r y).
  setoid_rewrite (inv_r y).
  reflexivity. Qed.

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

(** Homomorphisms preserve zero. *)

#[export] Instance grp_hom_is_null_pres : IsNullPres Y x y h.
Proof.
  hnf. note.
  pose proof bin_pres 0 0 as a.
  setoid_rewrite <- (unl_r (h (0 + 0))) in a.
  setoid_rewrite (unl_l 0) in a.
  apply cancel_l in a.
  setoid_rewrite <- a.
  reflexivity. Qed.

(** Homomorphisms preserve negation. *)

#[export] Instance grp_hom_is_un_pres : IsUnPres Y f g h.
Proof.
  note. intros z.
  pose proof bin_pres z (- z) as a.
  setoid_rewrite (inv_r z) in a.
  apply cancel_l with (h z).
  setoid_rewrite <- a.
  setoid_rewrite inv_r.
  apply null_pres. Qed.

End Context.

Section Context.

Context (A : Type)
  (X : A -> A -> Prop) (x : A) (f : A -> A) (k : A -> A -> A)
  `{!IsGrp X x f k}.

(** The identity function is a group homomorphism. *)

#[export] Instance id_is_grp_hom : IsGrpHom X x f k X x f k id.
Proof.
  split.
  - typeclasses eauto.
  - typeclasses eauto.
  - intros y z. unfold id. reflexivity.
  - typeclasses eauto. Qed.

End Context.

(** ** Left Group Action *)

Class IsGrpActL (A B : Type)
  (X : A -> A -> Prop) (x : A) (f : A -> A) (k : A -> A -> A)
  (Y : B -> B -> Prop) (al : A -> B -> B) : Prop := {
  grp_act_l_is_grp :> IsGrp X x f k;
  grp_act_l_is_unl_act_l :> IsUnlActL Y x al;
  grp_act_l_is_compat_act_l :> IsCompatActL Y k al;
  grp_act_l_is_proper :> IsProper (X ==> Y ==> Y) al;
}.

Section Context.

Context (A : Type)
  (X : A -> A -> Prop) (x : A) (f : A -> A) (k : A -> A -> A)
  `{!IsGrp X x f k}.

(** Addition is a left group action. *)

#[export] Instance bin_op_is_grp_act_l : IsGrpActL X x f k X k.
Proof.
  split.
  - typeclasses eauto.
  - enough (IsUnlL X x k) by assumption. typeclasses eauto.
  - enough (IsAssoc X k) by assumption. typeclasses eauto.
  - typeclasses eauto. Qed.

End Context.
