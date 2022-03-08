(** * Associativity *)

From DEZ.Is Require Export
  Compatible.

(** ** Associative Binary Operation *)

(** This has the same shape as [Z.mul_assoc]. *)

Class IsAssoc (A : Type) (X : A -> A -> Prop) (k : A -> A -> A) : Prop :=
  assoc (x y z : A) : X (k x (k y z)) (k (k x y) z).

Section Context.

Context (A : Type) (X : A -> A -> Prop) (k : A -> A -> A).

(** Compatibility of a binary operation with itself
    implies its associativity. *)

#[export] Instance compat_acts_is_assoc
  `{!IsCompatActs X k k} : IsAssoc X k.
Proof. auto. Qed.

(** Associativity of a binary operation
    implies its compatibility with itself. *)

#[local] Instance assoc_is_compat_acts
  `{!IsAssoc X k} : IsCompatActs X k k.
Proof. auto. Qed.

End Context.
