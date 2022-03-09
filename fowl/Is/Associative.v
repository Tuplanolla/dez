(** * Associativity *)

From DEZ.Is Require Export
  Compatible.

(** ** Associative Binary Operation *)

(** This has the same shape as [Z.mul_assoc]. *)

Class IsAssoc (A : Type) (X : A -> A -> Prop) (k : A -> A -> A) : Prop :=
  assoc (x y z : A) : X (k x (k y z)) (k (k x y) z).

Section Context.

Context (A : Type) (X : A -> A -> Prop) (k : A -> A -> A).

(** Associativity is a special case
    of the compatibility of binary functions. *)

#[export] Instance assoc_is_compat_bin_fns
  `{!IsAssoc X k} : IsCompatBinFns X k k k k.
Proof. auto. Qed.

#[local] Instance compat_bin_fns_is_assoc
  `{!IsCompatBinFns X k k k k} : IsAssoc X k.
Proof. auto. Qed.

End Context.
