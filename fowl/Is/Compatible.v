(** * Compatibility *)

From DEZ Require Export
  Init.

(** ** Compatible Binary Functions *)

Class IsCompatBinFns (A0 A1 A2 B0 B1 C : Type) (X : C -> C -> Prop)
  (k : A0 -> A1 -> B0) (m : A1 -> A2 -> B1)
  (n : A0 -> B1 -> C) (p : B0 -> A2 -> C) : Prop :=
  compat_bin_fns (x : A0) (y : A1) (z : A2) : X (n x (m y z)) (p (k x y) z).

(** ** Left Action Compatible with an External Binary Operation *)

Class IsCompatExtActL (A B : Type) (X : B -> B -> Prop)
  (k : A -> A -> A) (al : A -> B -> B) : Prop :=
  compat_ext_act_l (x y : A) (a : B) : X (al x (al y a)) (al (k x y) a).

Section Context.

Context (A B : Type) (X : B -> B -> Prop)
  (k : A -> A -> A) (al : A -> B -> B).

(** Compatibility of a left action with a binary operation
    is a special case of their compatibility as binary functions. *)

#[export] Instance compat_ext_act_l_is_compat_bin_fns
  `{!IsCompatExtActL X k al} : IsCompatBinFns X k al al al.
Proof. auto. Qed.

#[local] Instance compat_bin_fns_is_compat_ext_act_l
  `{!IsCompatBinFns X k al al al} : IsCompatExtActL X k al.
Proof. auto. Qed.

End Context.

(** ** Right Action Compatible with an Exteral Binary Operation *)

Class IsCompatExtActR (A B : Type) (X : B -> B -> Prop)
  (k : A -> A -> A) (ar : B -> A -> B) : Prop :=
  compat_ext_act_r (a : B) (x y : A) : X (ar a (k x y)) (ar (ar a x) y).

Section Context.

Context (A B : Type) (X : B -> B -> Prop)
  (k : A -> A -> A) (ar : B -> A -> B).

(** Compatibility of a right action with a binary operation
    is a special case of their compatibility as binary functions. *)

#[export] Instance compat_ext_act_r_is_compat_bin_fns
  `{!IsCompatExtActR X k ar} : IsCompatBinFns X ar k ar ar.
Proof. auto. Qed.

#[local] Instance compat_bin_fns_is_compat_ext_act_r
  `{!IsCompatBinFns X ar k ar ar} : IsCompatExtActR X k ar.
Proof. auto. Qed.

End Context.

Section Context.

Context (A B : Type) (X : B -> B -> Prop)
  (k : A -> A -> A) (al : A -> B -> B).

(** Compatibility of a left action with a binary operation
    is a special case of the compatibility of their flipped versions. *)

#[local] Instance compat_ext_act_l_is_compat_ext_act_r_flip
  `{!IsCompatExtActL X k al} : IsCompatExtActR (flip X) (flip k) (flip al).
Proof. intros a y x. unfold flip in *. eauto. Qed.

#[local] Instance compat_ext_act_r_flip_is_compat_ext_act_l
  `{!IsCompatExtActR (flip X) (flip k) (flip al)} : IsCompatExtActL X k al.
Proof. intros x y a. unfold flip in *. eauto. Qed.

End Context.

(** ** Left Action Compatible with an Internal Binary Operation *)

Class IsCompatIntActL (A B : Type) (X : B -> B -> Prop)
  (k : B -> B -> B) (al : A -> B -> B) : Prop :=
  compat_int_act_l (x : A) (a b : B) : X (al x (k a b)) (k (al x a) b).

Section Context.

Context (A B : Type) (X : B -> B -> Prop)
  (k : B -> B -> B) (al : A -> B -> B).

(** Compatibility of a left action with a binary operation
    is a special case of their compatibility as binary functions. *)

#[export] Instance compat_int_act_l_is_compat_bin_fns
  `{!IsCompatIntActL X k al} : IsCompatBinFns X al k al k.
Proof. auto. Qed.

#[local] Instance compat_bin_fns_is_compat_int_act_l
  `{!IsCompatBinFns X al k al k} : IsCompatIntActL X k al.
Proof. auto. Qed.

End Context.

(** ** Right Action Compatible with an Internal Binary Operation *)

Class IsCompatIntActR (A B : Type) (X : B -> B -> Prop)
  (k : B -> B -> B) (ar : B -> A -> B) : Prop :=
  compat_int_act_r (a b : B) (x : A) : X (k a (ar b x)) (ar (k a b) x).

Section Context.

Context (A B : Type) (X : B -> B -> Prop)
  (k : B -> B -> B) (ar : B -> A -> B).

(** Compatibility of a right action with a binary operation
    is a special case of their compatibility as binary functions. *)

#[export] Instance compat_int_act_r_is_compat_bin_fns
  `{!IsCompatIntActR X k ar} : IsCompatBinFns X k ar k ar.
Proof. auto. Qed.

#[local] Instance compat_bin_fns_is_compat_int_act_r
  `{!IsCompatBinFns X k ar k ar} : IsCompatIntActR X k ar.
Proof. auto. Qed.

End Context.

Section Context.

Context (A B : Type) (X : B -> B -> Prop)
  (k : B -> B -> B) (al : A -> B -> B).

(** Compatibility of a left action with a binary operation
    is a special case of the compatibility of their flipped versions. *)

#[local] Instance compat_int_act_l_is_compat_int_act_r_flip
  `{!IsCompatIntActL X k al} : IsCompatIntActR (flip X) (flip k) (flip al).
Proof. intros a y x. unfold flip in *. eauto. Qed.

#[local] Instance compat_int_act_r_flip_is_compat_int_act_l
  `{!IsCompatIntActR (flip X) (flip k) (flip al)} : IsCompatIntActL X k al.
Proof. intros x y a. unfold flip in *. eauto. Qed.

End Context.

(** ** Compatible Actions *)

Class IsCompatActs (A B C : Type) (X : C -> C -> Prop)
  (al : A -> C -> C) (ar : C -> B -> C) : Prop :=
  compat_acts (x : A) (a : C) (y : B) : X (al x (ar a y)) (ar (al x a) y).

Section Context.

Context (A B C : Type) (X : C -> C -> Prop)
  (al : A -> C -> C) (ar : C -> B -> C).

(** Compatibility of actions is a special case
    of their compatibility as binary functions. *)

#[export] Instance compat_acts_is_compat_bin_fns
  `{!IsCompatActs X al ar} : IsCompatBinFns X al ar al ar.
Proof. auto. Qed.

#[local] Instance compat_bin_fns_is_compat_acts
  `{!IsCompatBinFns X al ar al ar} : IsCompatActs X al ar.
Proof. auto. Qed.

End Context.
