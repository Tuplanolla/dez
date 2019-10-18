From Coq Require Import
  NArith.
From Maniunfold Require Export
  Init.
From Maniunfold.Is Require Import
  Setoid TotalOrder Ring FinitelyEnumerable.
From Maniunfold.Justifies Require Import
  NTheorems.

Definition F (p : positive) : Set := {n : N | (n < Npos p)%N}.

Module Equivalence.

Definition F_eqv {p : positive} (x y : F p) : Prop :=
  proj1_sig x = proj1_sig y.

Instance F_has_eqv {p : positive} : HasEqv (F p) := F_eqv.

(** TODO This implicit argument plumbing is annoying. *)

Instance F_is_reflexive {p : positive} : IsReflexive (F_eqv (p := p)) := {}.
Proof. intros [x ?]. apply (@N.eq_refl x). Qed.

Instance F_is_symmetric {p : positive} : IsSymmetric (F_eqv (p := p)) := {}.
Proof. intros [x ?] [y ?] ?. apply (@N.eq_sym x y); auto. Qed.

Instance F_is_transitive {p : positive} : IsTransitive (F_eqv (p := p)) := {}.
Proof. intros [x ?] [y ?] [z ?] ? ?. apply (@N.eq_trans x y z); auto. Qed.

Instance F_is_setoid {p : positive} : IsSetoid (F_eqv (p := p)) := {}.

End Equivalence.

(** TODO Remove these. *)

Instance N_lt_has_eqv {p n : N} : HasEqv (p < n)%N := fun x y : (p < n)%N =>
  True.

Lemma proj1_eqv : forall {p : positive}
  {x : N} {px : (x < Npos p)%N} {y : N} {qy : (y < Npos p)%N},
  let P (n : N) := (n < Npos p)%N in
  exist P x px == exist P y qy -> x == y.
Proof. intros ? ? ? ? ? ? ?; auto. Qed.

Lemma proj2_eqv : forall {p : positive}
  {x : N} {px qx : (x < Npos p)%N},
  let P (n : N) := (n < Npos p)%N in
  exist P x px == exist P x qx -> px == qx.
Proof. intros ? ? ? ? ?; constructor. Qed.

Module Order.

Definition F_ord {p : positive} (x y : F p) : Prop :=
  proj1_sig x <= proj1_sig y.

Instance F_has_ord {p : positive} : HasOrd (F p) := F_ord.

(** TODO Remove this. *)

Ltac simp := cbv [eqv Equivalence.F_has_eqv Equivalence.F_eqv
  rel ord_has_rel ord F_has_ord F_ord] in *; cbn in *.

Instance F_is_antisymmetric {p : positive} : IsAntisymmetric (F_ord (p := p)) := {}.
Proof. intros [x ?] [y ?] ? ?. apply (N.le_antisymm x y); auto. Qed.

Instance F_is_transitive {p : positive} : IsTransitive (F_ord (p := p)) := {}.
Proof. intros [x ?] [y ?] [z ?] ? ?. apply (N.le_trans x y z); auto. Qed.

Instance F_is_connex {p : positive} : IsConnex (F_ord (p := p)) := {}.
Proof. intros [x ?] [y ?]. apply (N.le_ge_cases x y). Qed.

Instance F_is_total_order {p : positive} : IsTotalOrder (F_ord (p := p)) := {}.
Proof. intros [x ?] [y ?] ? [z ?] [w ?] ? ?. simp. subst. auto. Qed.

End Order.

Definition F_has_opr_transparent_part {p : positive} (x y : F p) : N :=
  ((proj1_sig x + proj1_sig y) mod Npos p)%N.

Definition F_has_opr_opaque_part : forall {p : positive} {x y : F p},
  (F_has_opr_transparent_part x y < Npos p)%N.
Proof. intros p x y. apply N.mod_lt. intros H. inversion H. Qed.

Instance F_has_opr {p : positive} : HasOpr (F p) := fun x y : F p =>
  exist _ (F_has_opr_transparent_part x y) F_has_opr_opaque_part.

Instance F_is_associative {p : positive} : IsAssociative (F_has_opr (p := p)) := {}.
Proof. Admitted.

(** TODO Treat [Proper] like a predicative class as well. *)

Definition N_seq (p : positive) : list N :=
  List.map N.of_nat (List.seq O (Pos.to_nat p)).

Axiom violence : False.

Definition F_seq {p : positive} : list (F p).
Proof.
  induction p as [| q xs] using Pos.peano_rec.
  - apply cons.
    + hnf. exists 0%N. apply N.lt_0_1.
    + apply nil.
  - apply cons.
    + hnf. exists (Npos q). exfalso; apply violence.
    + eapply List.map. 2: apply xs.
      * intros [x ?]. hnf. exists x. exfalso; apply violence. Defined.

Instance F_has_enum {p : positive} : HasEnum (F p) := F_seq.

(* Compute List.map (@proj1_sig _ _) (enum : list (F 6%positive)). *)

Instance F_is_finite {p : positive} : IsFinite (F p) := {}.
Proof.
  - intros x. apply List.Exists_exists. exists x. split.
    + exfalso; apply violence.
    + reflexivity.
  - exfalso; apply violence. Qed.
