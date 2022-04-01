(** * Monotonic *)

From DEZ.Has Require Export
  EquivalenceRelations OrderRelations Operations.
From DEZ.Is Require Export
  Coherent Proper Preorder.
From DEZ.Supports Require Import
  EquivalenceNotations OrderNotations AdditiveNotations.

(** ** Monotonic Unary Function *)

(** Strict monotonicity with respect to an order relation is just
    monotonicity with respect to the corresponding strict order relation,
    which is why we do not define it separately. *)

Fail Fail Class IsMonoUnFn (A B : Type)
  (X : A -> A -> Prop) (Y : B -> B -> Prop)
  (f : A -> B) : Prop :=
  mono_un_fn (x y : A) (a : X x y) : Y (f x) (f y).

Fail Arguments mono_un_fn {_ _ _ _} _ {_} _ _ _.

Notation IsMonoUnFn X Y := (Proper (X ==> Y)) (only parsing).
Notation mono_un_fn := proper_prf (only parsing).

(** ** Monotonic Unary Operation *)

Fail Fail Class IsMonoUnOp (A : Type) (X : A -> A -> Prop)
  (f : A -> A) : Prop :=
  mono_un_op (x y : A) (a : X x y) : X (f x) (f y).

Fail Arguments mono_un_op {_ _} _ {_} _ _ _.

Notation IsMonoUnOp X := (Proper (X ==> X)) (only parsing).
Notation mono_un_op := proper_prf (only parsing).

(** ** Left-Monotonic Binary Function *)

Class IsMonoBinFnL (A0 A1 B : Type) (X : A1 -> A1 -> Prop) (Y : B -> B -> Prop)
  (k : A0 -> A1 -> B) : Prop :=
  mono_bin_fn_l (x y : A1) (z : A0) (a : X x y) : Y (k z x) (k z y).

(** ** Right-Monotonic Binary Function *)

Class IsMonoBinFnR (A0 A1 B : Type) (X : A0 -> A0 -> Prop) (Y : B -> B -> Prop)
  (k : A0 -> A1 -> B) : Prop :=
  mono_bin_fn_r (x y : A0) (z : A1) (a : X x y) : Y (k x z) (k y z).

(** ** Monotonic Binary Function *)

Fail Fail Class IsMonoBinFnLR (A0 A1 B : Type)
  (X0 : A0 -> A0 -> Prop) (X1 : A1 -> A1 -> Prop) (Y : B -> B -> Prop)
  (k : A0 -> A1 -> B) : Prop :=
  mono_bin_fn_l_r (x0 y0 : A0) (a0 : X0 x0 y0) (x1 y1 : A1) (a1 : X1 x1 y1) :
  Y (k x0 x1) (k y0 y1).

Fail Arguments mono_bin_fn_l_r {_ _ _ _ _ _} _ {_} _ _ _ _ _ _.

Notation IsMonoBinFnLR X0 X1 Y := (Proper (X0 ==> X1 ==> Y)) (only parsing).
Notation mono_bin_fn_l_r := proper_prf (only parsing).

Section Context.

Context (A0 A1 B : Type)
  (X0 : A0 -> A0 -> Prop) (X1 : A1 -> A1 -> Prop) (Y : B -> B -> Prop)
  (k : A0 -> A1 -> B) `{!IsPreord X0} `{!IsPreord X1} `{!IsPreord Y}.

#[local] Instance mono_bin_fn_dom_l_has_ord_rel : HasOrdRel A0 := X0.
#[local] Instance mono_bin_fn_dom_r_has_ord_rel : HasOrdRel A1 := X1.
#[local] Instance mono_bin_fn_codom_has_ord_rel : HasOrdRel B := Y.

Ltac note := progress (
  try change X0 with (ord_rel (A := A0)) in *;
  try change X1 with (ord_rel (A := A1)) in *;
  try change Y with (ord_rel (A := B)) in *).

(** Every left- and right-monotonic binary function is monotonic. *)

#[local] Instance mono_bin_fn_is_mono_bin_fn_l_r
  `{!IsMonoBinFnL X1 Y k} `{!IsMonoBinFnR X0 Y k} : IsMonoBinFnLR X0 X1 Y k.
Proof with note.
  intros x0 y0 a0 x1 y1 a1...
  transitivity (k x0 y1).
  - apply mono_bin_fn_l. apply a1.
  - apply mono_bin_fn_r. apply a0. Qed.

(** Every monotonic binary function is left-monotonic. *)

#[export] Instance mono_bin_fn_l_r_is_mono_bin_fn_l
  `{!IsMonoBinFnLR X0 X1 Y k} : IsMonoBinFnL X1 Y k.
Proof with note.
  intros x y z a...
  pose proof mono_bin_fn_l_r k as b. apply b.
  - reflexivity.
  - apply a. Qed.

(** Every monotonic binary function is right-monotonic. *)

#[export] Instance mono_bin_fn_l_r_is_mono_bin_fn_r
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

(** ** Right-Monotonic Binary Operation *)

(** This has the same shape as [Z.add_le_mono_r]. *)

Class IsMonoBinOpR (A : Type) (X : A -> A -> Prop)
  (k : A -> A -> A) : Prop :=
  mono_bin_op_r (x y z : A) (a : X x y) : X (k x z) (k y z).

(** ** Monotonic Binary Operation *)

Fail Fail Class IsMonoBinOpLR (A : Type) (X : A -> A -> Prop)
  (k : A -> A -> A) : Prop :=
  mono_bin_op_l_r (x0 y0 : A) (a0 : X x0 y0) (x1 y1 : A) (a1 : X x1 y1) :
  X (k x0 x1) (k y0 y1).

Fail Arguments mono_bin_op_l_r {_ _} _ {_} _ _ _ _ _ _.

Notation IsMonoBinOpLR X := (Proper (X ==> X ==> X)) (only parsing).
Notation mono_bin_op_l_r := proper_prf (only parsing).

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
  try change Xeq with (equiv_rel (A := A)) in *;
  try change Xle with (ord_rel (A := A)) in *;
  try change Xlt with (str_ord_rel (A := A)) in *;
  try change Yeq with (equiv_rel (A := B)) in *;
  try change Yle with (ord_rel (A := B)) in *;
  try change Ylt with (str_ord_rel (A := B)) in *).

(** Every strictly monotonic function is monotonic. *)

#[export] Instance mono_un_fn_is_mono_un_fn
  `{!IsMonoUnFn Xlt Ylt f} : IsMonoUnFn Xle Yle f.
Proof with note.
  intros x y ale...
  pose proof coh_rels x y as a.
  pose proof coh_rels (f x) (f y) as b.
  intuition. Qed.

End Context.
