(** * Idempotency *)

From DEZ Require Export
  Init.

(** ** Idempotent Element of a Unary Operation *)

Class IsIdemElemUnOp (A : Type) (X : A -> A -> Prop)
  (x : A) (f : A -> A) : Prop :=
  idem_elem_un_op : X (f (f x)) (f x).

(** ** Idempotent Unary Operation *)

Class IsIdemUnOp (A : Type) (X : A -> A -> Prop)
  (f : A -> A) : Prop :=
  idem_un_op (x : A) : X (f (f x)) (f x).

Section Context.

Context (A : Type) (X : A -> A -> Prop)
  (f : A -> A).

(** An element of an idempotent unary operation
    is an idempotent element of a unary operation. *)

#[export] Instance idem_un_op_is_idem_elem_un_op
  `{!IsIdemUnOp X f} (x : A) : IsIdemElemUnOp X x f.
Proof. apply idem_un_op. Qed.

End Context.

(** ** Idempotent Element of a Binary Operation *)

Class IsIdemElemBinOp (A : Type) (X : A -> A -> Prop)
  (x : A) (k : A -> A -> A) : Prop :=
  idem_elem_bin_op : X (k x x) x.

(** ** Idempotent Binary Operation *)

Class IsIdemBinOp (A : Type) (X : A -> A -> Prop)
  (k : A -> A -> A) : Prop :=
  idem_bin_op (x : A) : X (k x x) x.

Section Context.

Context (A : Type) (X : A -> A -> Prop)
  (k : A -> A -> A).

(** An element of an idempotent binary operation
    is an idempotent element of a binary operation. *)

#[export] Instance idem_bin_op_is_idem_elem_bin_op
  `{!IsIdemBinOp X k} (x : A) : IsIdemElemBinOp X x k.
Proof. apply idem_bin_op. Qed.

#[local] Instance idem_elem_bin_op_is_idem_bin_op
  `{!forall x : A, IsIdemElemBinOp X x k} : IsIdemBinOp X k.
Proof. intros x. apply idem_elem_bin_op. Qed.

End Context.

Section Context.

Context (A : Type) (X : A -> A -> Prop)
  (f : A -> A).

(** An idempotent unary operation
    is an idempotent element of the endofunction monoid. *)

#[export] Instance idem_un_op_is_idem_elem_bin_op_compose
  `{!IsIdemUnOp X f} : IsIdemElemBinOp (pointwise_relation _ X) f _o_.
Proof. intros x. unfold compose. apply idem_un_op. Qed.

#[local] Instance idem_elem_bin_op_compose_is_idem_un_op
  `{!IsIdemElemBinOp (pointwise_relation _ X) f _o_} : IsIdemUnOp X f.
Proof.
  intros x.
  change (f (f x)) with ((f o f) x).
  pose proof idem_elem_bin_op x as a.
  apply a. Qed.

End Context.
