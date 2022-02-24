(** * Arithmetic Operations *)

From DEZ.Has Require Export
  Operation.

(** ** Zero *)

Class HasZero (A : Type) : Type := zero : A.

#[export] Typeclasses Transparent HasZero.

(** ** Negation *)

Class HasNeg (A : Type) : Type := neg (x : A) : A.

#[export] Typeclasses Transparent HasNeg.

(** ** Addition *)

Class HasAdd (A : Type) : Type := add (x y : A) : A.

#[export] Typeclasses Transparent HasAdd.

(** ** One *)

Class HasOne (A : Type) : Type := one : A.

#[export] Typeclasses Transparent HasOne.

(** ** Reciprocal *)

Class HasRecip (A : Type) : Type := recip (x : A) : A.

#[export] Typeclasses Transparent HasRecip.

(** ** Multiplication *)

Class HasMul (A : Type) : Type := mul (x y : A) : A.

#[export] Typeclasses Transparent HasMul.

Module Subclass.

Section Context.

Context (A : Type).

(** Zero is a nullary operation. *)

#[export] Instance zero_has_null_op {x : HasZero A} : HasNullOp A := zero.

(** Negation is a unary operation. *)

#[export] Instance neg_has_un_op {f : HasNeg A} : HasUnOp A := neg.

(** Addition is a binary operation. *)

#[export] Instance add_has_bin_op {k : HasAdd A} : HasBinOp A := add.

(** One is a nullary operation. *)

#[export] Instance one_has_null_op {x : HasOne A} : HasNullOp A := one.

(** Reciprocal is a unary operation. *)

#[export] Instance recip_has_un_op {f : HasRecip A} : HasUnOp A := recip.

(** Multiplication is a binary operation. *)

#[export] Instance mul_has_bin_op {k : HasMul A} : HasBinOp A := mul.

End Context.

End Subclass.
