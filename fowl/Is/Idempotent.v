(** * Idempotency *)

From DEZ.Is Require Export
  Extensional.

(** ** Idempotent Unary Operation *)

Class IsIdemUnOp (A : Type) (X : A -> A -> Prop) (f : A -> A) : Prop :=
  idem_un_op (x : A) : X (f (f x)) (f x).

(** ** Idempotent Binary Operation *)

Class IsIdemBinOp (A : Type) (X : A -> A -> Prop) (k : A -> A -> A) : Prop :=
  idem_bin_op (x : A) : X (k x x) x.

(** TODO This is just fixed point! *)

(** ** Idempotent Element of a Unary Operation *)

Class IsIdemElemUnOp (A : Type) (X : A -> A -> Prop)
  (x : A) (f : A -> A) : Prop :=
  idem_elem_un_op : X (f x) x.

Section Context.

Context (A : Type) (X : A -> A -> Prop) (f : A -> A).

(** For an idempotent unary operation,
    every element in the codomain is an idempotent element. *)

#[export] Instance idem_un_op_is_idem_elem_un_op
  `{!IsIdemUnOp X f} (x : A) : IsIdemElemUnOp X (f x) f.
Proof. apply idem_un_op. Qed.

End Context.

(** ** Idempotent Element of a Binary Operation *)

Class IsIdemElemBinOp (A : Type) (X : A -> A -> Prop)
  (x : A) (k : A -> A -> A) : Prop :=
  idem_elem_bin_op : X (k x x) x.

Section Context.

Context (A : Type) (X : A -> A -> Prop) (k : A -> A -> A).

(** For an idempotent binary operation,
    every element is an idempotent element. *)

#[export] Instance idem_bin_op_is_idem_elem_bin_op
  `{!IsIdemBinOp X k} (x : A) : IsIdemElemBinOp X x k.
Proof. apply idem_bin_op. Qed.

End Context.

Section Context.

Context `{IsFunExt} (A : Type) (f : A -> A).

(** Idempotent functions are idempotent elements of the endofunction monoid. *)

#[export] Instance idem_un_op_is_idem_elem_compose
  `{!IsIdemUnOp _=_ f} : IsIdemElemBinOp _=_ f _o_.
Proof.
  apply fun_ext.
  intros x.
  unfold compose.
  setoid_rewrite idem_un_op.
  reflexivity. Qed.

End Context.
