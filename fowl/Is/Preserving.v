(** * Preservation *)

From DEZ.Is Require Export
  Fixed Commutative Distributive.

(** ** Function Preserving a Nullary Operation *)

Class IsNullPres (A B : Type) (X : B -> B -> Prop)
  (x : A) (y : B) (f : A -> B) : Prop :=
  null_pres : X (f x) y.

Section Context.

Context (A : Type) (X : A -> A -> Prop)
  (x : A) (f : A -> A).

(** Preservation of a nullary operation
    is a special case of the fixed point property. *)

#[export] Instance fixed_is_null_pres
  `{!IsFixed X x f} : IsNullPres X x x f.
Proof. auto. Qed.

#[local] Instance null_pres_is_fixed
  `{!IsNullPres X x x f} : IsFixed X x f.
Proof. auto. Qed.

End Context.

(** ** Function Preserving a Unary Operation *)

Class IsUnPres (A B : Type) (X : B -> B -> Prop)
  (f : A -> A) (g : B -> B) (h : A -> B) : Prop :=
  un_pres (x : A) : X (h (f x)) (g (h x)).

Section Context.

Context (A : Type) (X : A -> A -> Prop)
  (f g : A -> A).

(** Preservation of a unary operation
    is a special case of the commutative property. *)

#[export] Instance comm_un_ops_is_un_pres
  `{!IsCommUnOps X f g} : IsUnPres X g g f.
Proof. auto. Qed.

#[local] Instance un_pres_is_comm_un_ops
  `{!IsUnPres X g g f} : IsCommUnOps X f g.
Proof. auto. Qed.

End Context.

(** ** Function Preserving a Binary Operation *)

Class IsBinPres (A B : Type) (X : B -> B -> Prop)
  (k : A -> A -> A) (m : B -> B -> B) (f : A -> B) : Prop :=
  bin_pres (x y : A) : X (f (k x y)) (m (f x) (f y)).

Section Context.

Context (A B : Type) (X : B -> B -> Prop)
  (f : A -> B) (k : A -> A -> A) (m : B -> B -> B).

(** Preservation of a binary operation
    is a special case of the distributive property. *)

#[export] Instance distr_un_fn_is_bin_pres
  `{!IsDistrUnFn X f k m} : IsBinPres X k m f.
Proof. auto. Qed.

#[local] Instance bin_pres_is_distr_un_fn
  `{!IsBinPres X k m f} : IsDistrUnFn X f k m.
Proof. auto. Qed.

End Context.
