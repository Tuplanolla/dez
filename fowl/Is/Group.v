(** * Group Structure *)

From DEZ.Has Require Export
  EquivalenceRelations Operations.
From DEZ.Is Require Export
  Monoid Invertible Proper
  Fixed Involutive Injective Cancellative Antidistributive
  Preserving Unital Compatible.
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

#[local] Instance grp_has_equiv_rel : HasEquivRel A := X.
#[local] Instance grp_has_null_op : HasNullOp A := x.
#[local] Instance grp_has_un_op : HasUnOp A := f.
#[local] Instance grp_has_bin_op : HasBinOp A := k.

Ltac note := progress (
  try change X with (equiv_rel (A := A)) in *;
  try change x with (null_op (A := A)) in *;
  try change f with (un_op (A := A)) in *;
  try change k with (bin_op (A := A)) in *).

(** Zero is a fixed point of negation. *)

#[export] Instance grp_is_fixed : IsFixed X x f.
Proof with note.
  hnf...
  rewrite <- (unl_elem_r (- x)).
  rewrite (inv_l x).
  reflexivity. Qed.

(** Negation is an involution. *)

#[export] Instance grp_is_invol : IsInvol X f.
Proof with note.
  intros y...
  rewrite <- (unl_elem_r (- (- y))).
  rewrite <- (inv_l y).
  rewrite (assoc (- (- y)) (- y) y).
  rewrite (inv_l (- y)).
  rewrite (unl_elem_l y).
  reflexivity. Qed.

(** Negation is injective. *)

#[export] Instance grp_is_inj : IsInj X f.
Proof with note.
  intros y z a...
  rewrite <- (unl_elem_l z).
  rewrite <- (inv_r y).
  rewrite a.
  rewrite <- (assoc y (- z) z).
  rewrite (inv_l z).
  rewrite (unl_elem_r y).
  reflexivity. Qed.

(** Addition is left-cancellative. *)

#[local] Instance grp_is_cancel_l : IsCancelL X k.
Proof with note.
  intros y z w a...
  rewrite <- (unl_elem_l z).
  rewrite <- (inv_l y).
  rewrite <- (assoc (- y) y z).
  rewrite a.
  rewrite (assoc (- y) y w).
  rewrite (inv_l y).
  rewrite (unl_elem_l w).
  reflexivity. Qed.

(** Addition is right-cancellative. *)

#[local] Instance grp_is_cancel_r : IsCancelR X k.
Proof with note.
  intros y z w a...
  rewrite <- (unl_elem_r y).
  rewrite <- (inv_r w).
  rewrite (assoc y w (- w)).
  rewrite a.
  rewrite <- (assoc z w (- w)).
  rewrite (inv_r w).
  rewrite (unl_elem_r z).
  reflexivity. Qed.

(** Addition is cancellative. *)

#[export] Instance grp_is_cancel : IsCancel X k.
Proof. esplit; typeclasses eauto. Qed.

(** Negation antidistributes over addition. *)

#[export] Instance grp_is_antidistr_un_op : IsAntidistrUnOp X f k.
Proof with note.
  intros y z...
  apply (cancel_l (y + z) (- (y + z)) ((- z) + (- y)))...
  rewrite (inv_r (y + z)).
  rewrite (assoc (y + z) (- z) (- y)).
  rewrite <- (assoc y z (- z)).
  rewrite (inv_r z).
  rewrite (unl_elem_r y).
  rewrite (inv_r y).
  reflexivity. Qed.

End Context.

(** ** Group Homomorphism *)

Class IsGrpHom (A B : Type)
  (X : A -> A -> Prop) (x : A) (f : A -> A) (k : A -> A -> A)
  (Y : B -> B -> Prop) (y : B) (g : B -> B) (m : B -> B -> B)
  (h : A -> B) `{!IsGrp X x f k} `{!IsGrp Y y g m} : Prop := {
  grp_hom_dom_is_grp : IsGrp X x f k;
  grp_hom_codom_is_grp : IsGrp Y y g m;
  grp_hom_is_bin_pres :> IsBinPres Y k m h;
  grp_hom_is_proper :> IsProper (X ==> Y) h;
}.

Section Context.

Context (A B : Type)
  (X : A -> A -> Prop) (x : A) (f : A -> A) (k : A -> A -> A)
  (Y : B -> B -> Prop) (y : B) (g : B -> B) (m : B -> B -> B)
  (h : A -> B) `{!IsGrp X x f k} `{!IsGrp Y y g m} `{!IsGrpHom h}.

#[local] Instance grp_hom_dom_has_equiv_rel : HasEquivRel A := X.
#[local] Instance grp_hom_dom_has_null_op : HasNullOp A := x.
#[local] Instance grp_hom_dom_has_un_op : HasUnOp A := f.
#[local] Instance grp_hom_dom_has_bin_op : HasBinOp A := k.
#[local] Instance grp_hom_codom_has_equiv_rel : HasEquivRel B := Y.
#[local] Instance grp_hom_codom_has_null_op : HasNullOp B := y.
#[local] Instance grp_hom_codom_has_un_op : HasUnOp B := g.
#[local] Instance grp_hom_codom_has_bin_op : HasBinOp B := m.

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
Proof with note.
  hnf...
  apply (cancel_l (h 0) (h 0) 0).
  rewrite <- (bin_pres 0 0).
  rewrite (unl_elem_l 0).
  rewrite (unl_elem_r (h 0)).
  reflexivity. Qed.

(** Homomorphisms preserve negation. *)

#[export] Instance grp_hom_is_un_pres : IsUnPres Y f g h.
Proof with note.
  intros z...
  apply (cancel_l (h z) (h (- z)) (- h z)).
  rewrite <- (bin_pres z (- z)).
  rewrite (inv_r z).
  rewrite (inv_r (h z)).
  apply null_pres. Qed.

End Context.

Section Context.

Context (A : Type) (X : A -> A -> Prop)
  (x : A) (f : A -> A) (k : A -> A -> A) `{!IsGrp X x f k}.

(** Identity is a group homomorphism. *)

#[export] Instance id_is_grp_hom : IsGrpHom id.
Proof.
  split.
  - typeclasses eauto.
  - typeclasses eauto.
  - enough (IsDistrUnOp X id k) by assumption. typeclasses eauto.
  - typeclasses eauto. Qed.

End Context.

(** ** Left Group Action *)

Class IsGrpActL (A B : Type)
  (X : A -> A -> Prop) (x : A) (f : A -> A) (k : A -> A -> A)
  (Y : B -> B -> Prop) (al : A -> B -> B) `{!IsGrp X x f k} : Prop := {
  grp_act_l_is_grp : IsGrp X x f k;
  grp_act_l_is_unl_elem_act_l :> IsUnlElemActL Y x al;
  grp_act_l_is_compat_ext_act_l :> IsCompatExtActL Y k al;
  grp_act_l_is_proper :> IsProper (X ==> Y ==> Y) al;
}.

Section Context.

Context (A : Type) (X : A -> A -> Prop)
  (x : A) (f : A -> A) (k : A -> A -> A) `{!IsGrp X x f k}.

(** Identity is a left group action. *)

#[export] Instance id_is_grp_act_l : IsGrpActL X (flip const).
Proof.
  split.
  - typeclasses eauto.
  - enough (IsUnlElemL X x (flip const)) by assumption.
    intros y. unfold flip, const. reflexivity.
  - enough (IsAssoc X (flip const)) by assumption.
    intros y z w. unfold flip, const. reflexivity.
  - typeclasses eauto. Qed.

(** Addition is a left group action. *)

#[export] Instance bin_op_is_grp_act_l : IsGrpActL X k.
Proof.
  split.
  - typeclasses eauto.
  - enough (IsUnlElemL X x k) by assumption. typeclasses eauto.
  - enough (IsAssoc X k) by assumption. typeclasses eauto.
  - typeclasses eauto. Qed.

End Context.
