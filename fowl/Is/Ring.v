(** * Ring Structure *)

From DEZ.Has Require Export
  EquivalenceRelations ArithmeticOperations.
From DEZ.Is Require Export
  Group Commutative Monoid Distributive
  Absorbing Semiring Preserving Proper.
From DEZ.Supports Require Import
  EquivalenceNotations ArithmeticNotations.

(** ** Ring *)

Class IsRing (A : Type) (X : A -> A -> Prop)
  (x : A) (f : A -> A) (k : A -> A -> A)
  (y : A) (m : A -> A -> A) : Prop := {
  ring_add_is_grp :> IsGrp X x f k;
  ring_add_is_comm_bin_op :> IsCommBinOp X k;
  ring_mul_is_mon :> IsMon X y m;
  ring_is_distr :> IsDistr X m k;
}.

(** TODO Clean up. *)

Section Context.

Context (A : Type) (X : A -> A -> Prop)
  (x : A) (f : A -> A) (k : A -> A -> A)
  (y : A) (m : A -> A -> A) `{!IsRing X x f k y m}.

(** Declare the underlying equivalence relation as an equivalence relation and
    the underlying operations as operations. *)

#[local] Instance has_equiv_rel : HasEquivRel A := X.
#[local] Instance has_zero : HasZero A := x.
#[local] Instance has_neg : HasNeg A := f.
#[local] Instance has_add : HasAdd A := k.
#[local] Instance has_one : HasOne A := y.
#[local] Instance has_mul : HasMul A := m.

Ltac note := progress (
  try change X with (equiv_rel (A := A)) in *;
  try change x with (zero (A := A)) in *;
  try change f with (neg (A := A)) in *;
  try change k with (add (A := A)) in *;
  try change y with (one (A := A)) in *;
  try change m with (mul (A := A)) in *).

#[local] Instance ring_is_absorb_elem_l : IsAbsorbElemL X x m.
Proof.
  note. intros z.
  apply (cancel_r (0 * z) 0 (1 * z)).
  setoid_rewrite <- (distr_r 0 1 z).
  setoid_rewrite (unl_elem_l 1).
  setoid_rewrite (unl_elem_l z).
  reflexivity. Qed.

#[local] Instance ring_is_absorb_elem_r : IsAbsorbElemR X x m.
Proof.
  note. intros z.
  apply (cancel_r (z * 0) 0 (z * 1)).
  setoid_rewrite <- (distr_l z 0 1).
  setoid_rewrite (unl_elem_l 1).
  setoid_rewrite (unl_elem_r z).
  reflexivity. Qed.

#[export] Instance ring_is_absorb_elem : IsAbsorbElem X x m.
Proof. esplit; typeclasses eauto. Qed.

#[export] Instance ring_is_semiring : IsSemiring X x k y m.
Proof. esplit; typeclasses eauto. Qed.

#[local] Instance ring_is_comm_l : IsCommL X m f.
Proof.
  note. intros z w.
  apply (cancel_l (z * w) ((- z) * w) (- (z * w))).
  setoid_rewrite <- (distr_r z (- z) w).
  setoid_rewrite (inv_r z).
  setoid_rewrite (absorb_elem_l w).
  setoid_rewrite (inv_r (z * w)).
  reflexivity. Qed.

#[local] Instance ring_is_comm_r : IsCommR X m f.
Proof.
  note. intros z w.
  apply (cancel_l (z * w) (z * (- w)) (- (z * w))).
  setoid_rewrite <- (distr_l z w (- w)).
  setoid_rewrite (inv_r w).
  setoid_rewrite (absorb_elem_r z).
  setoid_rewrite (inv_r (z * w)).
  reflexivity. Qed.

#[export] Instance ring_is_comm : IsComm X m f.
Proof. esplit; typeclasses eauto. Qed.

(* X (k (f x) y) (k x (f y)) *)

Lemma comm_l_r (z w : A) : (- z) * w == z * (- w).
Proof.
  note.
  setoid_rewrite (comm_l z w).
  setoid_rewrite (comm_r z w).
  reflexivity. Qed.

(* X (k (f x) (f y)) (k x y) *)

Lemma involutivity_thing (z w : A) : (- z) * (- w) == z * w.
Proof.
  note.
  setoid_rewrite (comm_r (- z) w).
  setoid_rewrite (comm_l z w).
  setoid_rewrite (invol (z * w)).
  reflexivity. Qed.

(** TODO What? *)

#[local] Notation "'-' '1'" := (- (1)) (format "'-'  '1'").

(* X (k (f x) y) (f y) *)

Lemma neg_mul_one_l_sgn_absorb (z : A) : (- 1) * z == - z.
Proof.
  note.
  setoid_rewrite (comm_l 1 z).
  setoid_rewrite (unl_elem_l z).
  reflexivity. Qed.

(* X (k y (f x)) (f y) *)

Lemma neg_mul_one_r_sgn_absorb (z : A) : z * (- 1) == - z.
Proof.
  setoid_rewrite (comm_r z 1).
  setoid_rewrite (unl_elem_r z).
  reflexivity. Qed.

(* Instance integral_domain_thing
  (a : forall z w : A, z * w == 0 -> z == 0 \/ w == 0) :
  IsNonzeroCancelL _==_ 0 _*_.
Proof with subclass.
  intros z w v g e.
  subclass.
  assert (e' : v * z + - (v * w) == 0).
  { setoid_rewrite e.
    setoid_rewrite (inv_r (v * w)).
    reflexivity. }
  setoid_rewrite <- comm_l in e'.
  setoid_rewrite <- distr_l in e'.
  apply a in e'.
  destruct e' as [e' | e'].
  - congruence.
  - apply (cancel_r z w (- w))...
    setoid_rewrite e'.
    setoid_rewrite (inv_r w).
    reflexivity. Qed. *)

End Context.

(** ** Ring Homomorphism *)

Class IsRingHom (A B : Type)
  (X : A -> A -> Prop) (x : A) (f : A -> A) (k : A -> A -> A)
  (y : A) (m : A -> A -> A)
  (Y : B -> B -> Prop) (z : B) (g : B -> B) (n : B -> B -> B)
  (w : B) (p : B -> B -> B)
  (h : A -> B) `{!IsRing X x f k y m} `{!IsRing Y z g n w p} : Prop := {
  ring_hom_dom_is_grp : IsRing X x f k y m;
  ring_hom_codom_is_grp : IsRing Y z g n w p;
  ring_hom_add_is_bin_pres :> IsBinPres Y k n h;
  ring_hom_mul_is_bin_pres :> IsBinPres Y m p h;
  ring_hom_mul_is_null_pres :> IsNullPres Y y w h;
  ring_hom_is_proper :> IsProper (X ==> Y) h;
}.
