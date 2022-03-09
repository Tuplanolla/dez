(** * Compatibility *)

From DEZ Require Export
  Init.

(** ** Compatible Binary Functions *)

Class IsCompatBinFns (A0 A1 A2 B0 B1 C : Type) (X : C -> C -> Prop)
  (k : A0 -> A1 -> B0) (m : A1 -> A2 -> B1)
  (n : A0 -> B1 -> C) (p : B0 -> A2 -> C) : Prop :=
  compat_bin_fns (x : A0) (y : A1) (z : A2) : X (n x (m y z)) (p (k x y) z).

(** ** Compatible Left Action with a Binary Operation *)

Class IsCompatActL (A B : Type) (X : B -> B -> Prop)
  (k : A -> A -> A) (al : A -> B -> B) : Prop :=
  compat_act_l (x y : A) (a : B) : X (al x (al y a)) (al (k x y) a).

Section Context.

Context (A B : Type) (X : B -> B -> Prop)
  (k : A -> A -> A) (al : A -> B -> B).

(** Compatibility of a left action with a binary operation
    is a special case of the compatibility of binary functions. *)

#[export] Instance compat_act_l_is_compat_bin_fns
  `{!IsCompatActL X k al} : IsCompatBinFns X k al al al.
Proof. auto. Qed.

#[local] Instance compat_bin_fns_is_compat_act_l
  `{!IsCompatBinFns X k al al al} : IsCompatActL X k al.
Proof. auto. Qed.

End Context.

(** ** Compatible Right Action with a Binary Operation *)

Class IsCompatActR (A B : Type) (X : B -> B -> Prop)
  (k : A -> A -> A) (ar : B -> A -> B) : Prop :=
  compat_act_r (a : B) (x y : A) : X (ar a (k x y)) (ar (ar a x) y).

Section Context.

Context (A B : Type) (X : B -> B -> Prop)
  (k : A -> A -> A) (ar : B -> A -> B).

(** Compatibility of a right action with a binary operation
    is a special case of the compatibility of binary functions. *)

#[export] Instance compat_act_r_is_compat_bin_fns
  `{!IsCompatActR X k ar} : IsCompatBinFns X ar k ar ar.
Proof. auto. Qed.

#[local] Instance compat_bin_fns_is_compat_act_r
  `{!IsCompatBinFns X ar k ar ar} : IsCompatActR X k ar.
Proof. auto. Qed.

End Context.

(** ** Compatible Actions *)

Class IsCompatActs (A B C : Type) (X : C -> C -> Prop)
  (al : A -> C -> C) (ar : C -> B -> C) : Prop :=
  compat_acts (x : A) (a : C) (y : B) : X (al x (ar a y)) (ar (al x a) y).

Section Context.

Context (A B C : Type) (X : C -> C -> Prop)
  (al : A -> C -> C) (ar : C -> B -> C).

(** Compatibility of actions is a special case
    of the compatibility of binary functions. *)

#[export] Instance compat_acts_is_compat_bin_fns
  `{!IsCompatActs X al ar} : IsCompatBinFns X al ar al ar.
Proof. auto. Qed.

#[local] Instance compat_bin_fns_is_compat_acts
  `{!IsCompatBinFns X al ar al ar} : IsCompatActs X al ar.
Proof. auto. Qed.

End Context.
