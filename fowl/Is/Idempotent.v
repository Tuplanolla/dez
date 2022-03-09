(** * Idempotency *)

From DEZ.Is Require Export
  Extensional.

(** ** Idempotent Unary Operation *)

Class IsIdemUnOp (A : Type) (X : A -> A -> Prop) (f : A -> A) : Prop :=
  idem_un_op (x : A) : X (f (f x)) (f x).

(** ** Idempotent Binary Operation *)

Class IsIdemBinOp (A : Type) (X : A -> A -> Prop) (k : A -> A -> A) : Prop :=
  idem_bin_op (x : A) : X (k x x) x.

(** ** Idempotent Element of Binary Operation *)

Class IsIdemElem (A : Type) (X : A -> A -> Prop)
  (x : A) (k : A -> A -> A) : Prop :=
  idem_elem : X (k x x) x.

Section Context.

Context (A : Type) (X : A -> A -> Prop) (k : A -> A -> A).

(** For an idempotent binary operation,
    every element is an idempotent element. *)

#[export] Instance idem_bin_op_is_idem_elem
  `{!IsIdemBinOp X k} (x : A) : IsIdemElem X x k.
Proof. apply idem_bin_op. Qed.

End Context.

Section Context.

Context `{IsFunExt} (A : Type) (f : A -> A).

(** Idempotent functions are idempotent elements of the endofunction monoid. *)

#[export] Instance idem_un_op_is_idem_elem_compose
  `{!IsIdemUnOp _=_ f} : IsIdemElem _=_ f _o_.
Proof.
  apply fun_ext.
  intros x.
  unfold compose.
  setoid_rewrite idem_un_op.
  reflexivity. Qed.

End Context.
