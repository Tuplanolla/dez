(** * Monotonic *)

(** Strict monotonicity with respect to an order relation is just
    monotonicity with respect to the corresponding strict order relation,
    which is why we do not define it separately. *)

From DEZ.Has Require Export
  EquivalenceRelations OrderRelations Operations.
From DEZ.Is Require Export
  Coherent Proper Preorder.
From DEZ.Provides Require Import
  TypeclassTactics.
From DEZ.Supports Require Import
  EquivalenceNotations OrderNotations AdditiveNotations.

(** ** Monotonic Unary Function *)

Fail Fail Class IsMonoUnFn (A B : Type)
  (X : A -> A -> Prop) (Y : B -> B -> Prop)
  (f : A -> B) : Prop :=
  mono_un_fn (x y : A) (a : X x y) : Y (f x) (f y).

Fail Arguments mono_un_fn {_ _ _ _} _ {_} _ _ _.

Notation IsMonoUnFn X Y := (IsProper (X ==> Y)) (only parsing).
Notation mono_un_fn := proper (only parsing).

(** ** Monotonic Unary Operation *)

Fail Fail Class IsMonoUnOp (A : Type) (X : A -> A -> Prop)
  (f : A -> A) : Prop :=
  mono_un_op (x y : A) (a : X x y) : X (f x) (f y).

Fail Arguments mono_un_op {_ _} _ {_} _ _ _.

Notation IsMonoUnOp X := (IsProper (X ==> X)) (only parsing).
Notation mono_un_op := proper (only parsing).

(** ** Left-Monotonic Binary Function *)

Class IsMonoBinFnL (A0 A1 B : Type) (X : A1 -> A1 -> Prop) (Y : B -> B -> Prop)
  (k : A0 -> A1 -> B) : Prop :=
  mono_bin_fn_l (x y : A1) (z : A0) (a : X x y) : Y (k z x) (k z y).

(** ** Right-Monotonic Binary Function *)

Class IsMonoBinFnR (A0 A1 B : Type) (X : A0 -> A0 -> Prop) (Y : B -> B -> Prop)
  (k : A0 -> A1 -> B) : Prop :=
  mono_bin_fn_r (x y : A0) (z : A1) (a : X x y) : Y (k x z) (k y z).

(** ** Left-Right-Monotonic Binary Function *)

Fail Fail Class IsMonoBinFnLR (A0 A1 B : Type)
  (X0 : A0 -> A0 -> Prop) (X1 : A1 -> A1 -> Prop) (Y : B -> B -> Prop)
  (k : A0 -> A1 -> B) : Prop :=
  mono_bin_fn_l_r (x0 y0 : A0) (a0 : X0 x0 y0) (x1 y1 : A1) (a1 : X1 x1 y1) :
  Y (k x0 x1) (k y0 y1).

Fail Arguments mono_bin_fn_l_r {_ _ _ _ _ _} _ {_} _ _ _ _ _ _.

Notation IsMonoBinFnLR X0 X1 Y := (IsProper (X0 ==> X1 ==> Y)) (only parsing).
Notation mono_bin_fn_l_r := proper (only parsing).

Section Context.

Context (A0 A1 B : Type)
  (X0 : A0 -> A0 -> Prop) (X1 : A1 -> A1 -> Prop) (Y : B -> B -> Prop)
  (k : A0 -> A1 -> B) `{!IsPreord X0} `{!IsPreord X1} `{!IsPreord Y}.

#[local] Instance mono_bin_fn_dom_l_has_ord_rel : HasOrdRel A0 := X0.
#[local] Instance mono_bin_fn_dom_r_has_ord_rel : HasOrdRel A1 := X1.
#[local] Instance mono_bin_fn_codom_has_ord_rel : HasOrdRel B := Y.

Ltac note := progress (
  denote X0 with (ord_rel (A := A0));
  denote X1 with (ord_rel (A := A1));
  denote Y with (ord_rel (A := B))).

(** A left- and right-monotonic binary function is left-right-monotonic. *)

#[local] Instance mono_bin_fn_is_mono_bin_fn_l_r
  `{!IsMonoBinFnL X1 Y k} `{!IsMonoBinFnR X0 Y k} : IsMonoBinFnLR X0 X1 Y k.
Proof with note.
  intros x0 y0 a0 x1 y1 a1...
  transitivity (k x0 y1).
  - apply mono_bin_fn_l. apply a1.
  - apply mono_bin_fn_r. apply a0. Qed.

(** A monotonic binary function is left-monotonic. *)

#[local] Instance mono_bin_fn_l_r_is_mono_bin_fn_l
  `{!IsMonoBinFnLR X0 X1 Y k} : IsMonoBinFnL X1 Y k.
Proof with note.
  intros x y z a...
  pose proof mono_bin_fn_l_r k as b. apply b.
  - reflexivity.
  - apply a. Qed.

(** A monotonic binary function is right-monotonic. *)

#[local] Instance mono_bin_fn_l_r_is_mono_bin_fn_r
  `{!IsMonoBinFnLR X0 X1 Y k} : IsMonoBinFnR X0 Y k.
Proof with note.
  intros x y z a...
  pose proof mono_bin_fn_l_r k as b. apply b.
  - apply a.
  - reflexivity. Qed.

End Context.

(** ** Left-Monotonic Binary Operation *)

(** This has the same shape as [Z.add_le_mono_l]. *)

Class IsMonoBinOpL (A : Type) (X : A -> A -> Prop)
  (k : A -> A -> A) : Prop :=
  mono_bin_op_l (x y z : A) (a : X x y) : X (k z x) (k z y).

Section Context.

Context (A : Type) (X : A -> A -> Prop)
  (k : A -> A -> A).

(** Left-monotonicity of a binary operation is a special case
    of its left-monotonicity as a binary function. *)

#[export] Instance mono_bin_op_l_is_mono_bin_fn_l
  `{!IsMonoBinOpL X k} : IsMonoBinFnL X X k.
Proof. auto. Qed.

#[local] Instance mono_bin_fn_l_is_mono_bin_op_l
  `{!IsMonoBinFnL X X k} : IsMonoBinOpL X k.
Proof. auto. Qed.

End Context.

(** ** Right-Monotonic Binary Operation *)

(** This has the same shape as [Z.add_le_mono_r]. *)

Class IsMonoBinOpR (A : Type) (X : A -> A -> Prop)
  (k : A -> A -> A) : Prop :=
  mono_bin_op_r (x y z : A) (a : X x y) : X (k x z) (k y z).

Section Context.

Context (A : Type) (X : A -> A -> Prop)
  (k : A -> A -> A).

(** Right-monotonicity of a binary operation is a special case
    of its right-monotonicity as a binary function. *)

#[export] Instance mono_bin_op_r_is_mono_bin_fn_r
  `{!IsMonoBinOpR X k} : IsMonoBinFnR X X k.
Proof. auto. Qed.

#[local] Instance mono_bin_fn_r_is_mono_bin_op_r
  `{!IsMonoBinFnR X X k} : IsMonoBinOpR X k.
Proof. auto. Qed.

End Context.

(** ** Monotonic Binary Operation *)

Class IsMonoBinOp (A : Type) (X : A -> A -> Prop)
  (k : A -> A -> A) : Prop := {
  mono_bin_op_is_mono_bin_op_l :> IsMonoBinOpL X k;
  mono_bin_op_is_mono_bin_op_r :> IsMonoBinOpR X k;
}.

(** ** Left-Right-Monotonic Binary Operation *)

Fail Fail Class IsMonoBinOpLR (A : Type) (X : A -> A -> Prop)
  (k : A -> A -> A) : Prop :=
  mono_bin_op_l_r (x0 y0 : A) (a0 : X x0 y0) (x1 y1 : A) (a1 : X x1 y1) :
  X (k x0 x1) (k y0 y1).

Fail Arguments mono_bin_op_l_r {_ _} _ {_} _ _ _ _ _ _.

Notation IsMonoBinOpLR X := (IsProper (X ==> X ==> X)) (only parsing).
Notation mono_bin_op_l_r := proper (only parsing).

Section Context.

Context (A : Type) (X : A -> A -> Prop)
  (k : A -> A -> A) `{!IsPreord X}.

#[local] Instance mono_bin_fn_has_ord_rel : HasOrdRel A := X.

Ltac note := progress (
  denote X with (ord_rel (A := A))).

(** Monotonicity of a binary operation is equivalent
    to its left-right-monotonicity. *)

#[local] Instance mono_bin_op_is_mono_bin_op_l_r
  `{!IsMonoBinOp X k} : IsMonoBinOpLR X k.
Proof. eapply mono_bin_fn_is_mono_bin_fn_l_r; typeclasses eauto. Qed.

#[local] Instance mono_bin_op_l_r_is_mono_bin_op
  `{!IsMonoBinOpLR X k} : IsMonoBinOp X k.
Proof.
  esplit.
  - eapply mono_bin_fn_l_is_mono_bin_op_l.
    eapply mono_bin_fn_l_r_is_mono_bin_fn_l; typeclasses eauto.
  - eapply mono_bin_fn_r_is_mono_bin_op_r.
    eapply mono_bin_fn_l_r_is_mono_bin_fn_r; typeclasses eauto. Qed.

End Context.

Section Context.

Context (A B : Type)
  (Xeq Xle Xlt : A -> A -> Prop) (Yeq Yle Ylt : B -> B -> Prop)
  (f : A -> B) `{!IsCohRels Xeq Xle Xlt} `{!IsCohRels Yeq Yle Ylt}
  `{!IsProper (Xeq ==> Yeq) f}.

#[local] Instance mono_un_fn_dom_has_equiv_rel : HasEquivRel A := Xeq.
#[local] Instance mono_un_fn_dom_has_ord_rel : HasOrdRel A := Xle.
#[local] Instance mono_un_fn_dom_has_str_ord_rel : HasStrOrdRel A := Xlt.
#[local] Instance mono_un_fn_codom_has_equiv_rel : HasEquivRel B := Yeq.
#[local] Instance mono_un_fn_codom_has_ord_rel : HasOrdRel B := Yle.
#[local] Instance mono_un_fn_codom_has_str_ord_rel : HasStrOrdRel B := Ylt.

Ltac note := progress (
  denote Xeq with (equiv_rel (A := A));
  denote Xle with (ord_rel (A := A));
  denote Xlt with (str_ord_rel (A := A));
  denote Yeq with (equiv_rel (A := B));
  denote Yle with (ord_rel (A := B));
  denote Ylt with (str_ord_rel (A := B))).

(** A strictly monotonic function is monotonic. *)

#[export] Instance mono_un_fn_is_mono_un_fn
  `{!IsMonoUnFn Xlt Ylt f} : IsMonoUnFn Xle Yle f.
Proof with note.
  intros x y ale...
  pose proof coh_rels x y as a.
  pose proof coh_rels (f x) (f y) as b.
  intuition. Qed.

End Context.
