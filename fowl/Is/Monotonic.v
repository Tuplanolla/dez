(** * Monotonic *)

From DEZ.Has Require Export
  Decisions Operations OrderRelations.
From DEZ.Is Require Export
  Coherent Preorder Proper.
From DEZ.Supports Require Import
  AdditiveNotations EquivalenceNotations OrderNotations.

#[local] Existing Instance dec_decidable.

(** ** Monotonic Function *)

Fail Fail Class IsMono (A B : Type) (X : A -> A -> Prop) (Y : B -> B -> Prop)
  (f : A -> B) : Prop :=
  mono (x y : A) (a : X x y) : Y (f x) (f y).

Notation IsMono X Y := (Proper (X ==> Y)) (only parsing).
Notation mono := proper_prf (only parsing).

(** ** Strictly Monotonic Function *)

(** Strict monotonicity with respect to an order relation is just
    monotonicity with respect to the corresponding strict order relation. *)

Notation IsStrMono X Y := (Proper (X ==> Y)) (only parsing).
Notation str_mono := proper_prf (only parsing).

Section Context.

Context (A B : Type) (Xeq : A -> A -> Prop) (Yeq : B -> B -> Prop)
  (Xle Xlt : A -> A -> Prop) (Yle Ylt : B -> B -> Prop)
  (d : forall x y : A, {Xeq x y} + {~ Xeq x y}) (f : A -> B)
  `{!IsCohRels Xeq Xle Xlt} `{!IsCohRels Yeq Yle Ylt}
  `{!IsProper (Xle ==> Yle) f}. (** Nonsense! *)

#[local] Instance str_mono_dom_has_equiv_rel : HasEquivRel A := Xeq.
#[local] Instance str_mono_dom_has_ord_rel : HasOrdRel A := Xle.
#[local] Instance str_mono_dom_has_str_ord_rel : HasStrOrdRel A := Xlt.
#[local] Instance str_mono_codom_has_equiv_rel : HasEquivRel B := Yeq.
#[local] Instance str_mono_codom_has_ord_rel : HasOrdRel B := Yle.
#[local] Instance str_mono_codom_has_str_ord_rel : HasStrOrdRel B := Ylt.
#[local] Instance str_mono_dom_has_equiv_dec : HasEquivDec A := d.

Ltac note := progress (
  try change Xeq with (equiv_rel (A := A)) in *;
  try change Xle with (ord_rel (A := A)) in *;
  try change Xlt with (str_ord_rel (A := A)) in *;
  try change Yeq with (equiv_rel (A := B)) in *;
  try change Yle with (ord_rel (A := B)) in *;
  try change Ylt with (str_ord_rel (A := B)) in *;
  try change d with (equiv_dec (A := A)) in *).

(** Every discrete strictly monotonic function is monotonic. *)

#[export] Instance str_mono_is_mono
  `{!IsStrMono Xlt Ylt f} : IsMono Xle Yle f.
Proof with note.
  intros x y ale...
  decide (x == y) as [aeq | aeq].
  - f_equiv. apply ale.
  - pose proof proj2 (coh_rels x y) (conj ale aeq) as alt.
    pose proof str_mono f x y alt as blt.
    pose proof proj1 (proj1 (coh_rels (f x) (f y)) blt) as ble.
    apply ble. Qed.

End Context.

(** ** Monotonic Unary Operation *)

Fail Fail Class IsMonoUnOp (A : Type) (X : A -> A -> Prop)
  (f : A -> A) : Prop :=
  mono_un_op (x y : A) (a : X x y) : X (f x) (f y).

Notation IsMonoUnOp X := (Proper (X ==> X)) (only parsing).
Notation mono_un_op := proper_prf (only parsing).

(** ** Strictly Monotonic Unary Operation *)

Notation IsStrMonoUnOp X := (Proper (X ==> X)) (only parsing).
Notation str_mono_un_op := proper_prf (only parsing).

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

(** ** Monotonic Binary Function *)

Fail Fail Class IsMonoBinFn (A0 A1 B : Type)
  (X0 : A0 -> A0 -> Prop) (X1 : A1 -> A1 -> Prop) (Y : B -> B -> Prop)
  (k : A0 -> A1 -> B) : Prop :=
  mono_bin_fn (x0 y0 : A0) (a0 : X0 x0 y0) (x1 y1 : A1) (a1 : X1 x1 y1) :
  Y (k x0 x1) (k y0 y1).

Notation IsMonoBinFn X Y W := (Proper (X ==> Y ==> W)) (only parsing).
Notation mono_bin_fn := proper_prf (only parsing).

(** ** Monotonic Binary Operation *)

Notation IsMonoBinOp X := (Proper (X ==> X ==> X)) (only parsing).
Notation mono_bin_op := proper_prf (only parsing).

(** ** Strictly Monotonic Binary Operation *)

Notation IsStrMonoBinOp X := (Proper (X ==> X ==> X)) (only parsing).
Notation str_mono_bin_op := proper_prf (only parsing).

Section Context.

Context (A : Type) (X : A -> A -> Prop)
  (k : A -> A -> A) `{!IsPreord X}.

#[local] Instance mono_bin_op_has_equiv_rel : HasOrdRel A := X.
#[local] Instance mono_bin_op_has_bin_op : HasBinOp A := k.

Ltac note := progress (
  try change X with (ord_rel (A := A)) in *;
  try change k with (bin_op (A := A)) in *).

(** Every left- and right-monotonic binary operation is monotonic. *)

#[local] Instance is_mono_bin_op
  `{!IsMonoBinOpL X k} `{!IsMonoBinOpR X k} : IsMonoBinOp X k.
Proof with note.
  intros x0 y0 a0 x1 y1 a1...
  transitivity (x0 + y1).
  - apply mono_bin_op_l. apply a1.
  - apply mono_bin_op_r. apply a0. Qed.

(** Every monotonic binary operation is left-monotonic. *)

#[export] Instance is_mono_bin_op_l
  `{!IsMonoBinOp X k} : IsMonoBinOpL X k.
Proof with note.
  intros x y z a...
  pose proof mono_bin_op _+_ as b. apply b.
  - reflexivity.
  - apply a. Qed.

(** Every monotonic binary operation is right-monotonic. *)

#[export] Instance is_mono_bin_op_r
  `{!IsMonoBinOp X k} : IsMonoBinOpR X k.
Proof with note.
  intros x y z a...
  pose proof mono_bin_op _+_ as b. apply b.
  - apply a.
  - reflexivity. Qed.

End Context.
