(** * Simplicial Complexes *)

From Coq Require Import
  Lists.List Sets.Ensembles Sets.Powerset_facts QArith.QArith.
From DEZ.Is Require Export
  Equivalence.

Arguments Ensembles.Empty_set {_}.
Arguments Ensembles.In {_} _ _.
Arguments Included {_} _ _.
Arguments Singleton {_} _.
Arguments Union {_} _ _.
Arguments Same_set {_} _ _.

(** ** Abstract Simplicial Complex *)

(** We deviate slightly from the standard definition.
    Instead of requiring that every subset of the set of faces is nonempty,
    we require that the empty set is a face in every complex. *)

Class IsAbsSimpComp (A : Type) (F : Ensemble (Ensemble A)) : Prop := {
  abs_simp_comp_nonempty : Ensembles.In F Ensembles.Empty_set;
  abs_simp_comp_cumulative (P S : Ensemble A) (C : Included P S)
    (E : Ensembles.In F S) : Ensembles.In F P;
}.

Inductive IsIm (A B : Type) (X : B -> B -> Prop) (P : Ensemble A)
  (f : A -> B) : Ensemble B :=
  IsIm_intro (x : A) (J : In P x) (y : B) (a : X y (f x)) :
  Ensembles.In (IsIm X P f) y.

(** ** Simplicial Complex *)

Class IsSimpComp (A B : Type)
  (F : Ensemble (Ensemble A)) (X : B -> B -> Prop)
  (K : Ensemble B -> Ensemble B -> Ensemble B -> Prop)
  (f : A -> B) : Prop := {
  simp_comp_is_equiv :> IsEquiv X;
  simp_comp_is_abs_simp_comp :> IsAbsSimpComp F;
  simp_comp_coherent (P S : Ensemble A)
    (EP : Ensembles.In F P) (ES : Ensembles.In F S)
    (T : Ensemble B) (ET : K (IsIm X P f) (IsIm X S f) T) :
    exists V : Ensemble A, Ensembles.In F V ->
    Included V P /\ Included V S;
}.

Module Example.

Import ListNotations.

#[local] Open Scope nat_scope.

Equations Ensemble_of_list (A : Type) (a : list A) : Ensemble A :=
  Ensemble_of_list [] := Ensembles.Empty_set;
  Ensemble_of_list (x :: b) := Union (Singleton x) (Ensemble_of_list b).

Definition P0 : Ensemble nat := Ensemble_of_list [].
Definition P1 : Ensemble nat := Ensemble_of_list [6].
Definition P2 : Ensemble nat := Ensemble_of_list [7].
Definition P3 : Ensemble nat := Ensemble_of_list [8].
Definition P4 : Ensemble nat := Ensemble_of_list [9].
Definition P5 : Ensemble nat := Ensemble_of_list [11].
Definition P6 : Ensemble nat := Ensemble_of_list [6; 7].
Definition P7 : Ensemble nat := Ensemble_of_list [6; 8].
Definition P8 : Ensemble nat := Ensemble_of_list [7; 8].
Definition P9 : Ensemble nat := Ensemble_of_list [8; 9].
Definition P10 : Ensemble nat := Ensemble_of_list [6; 7; 8].

Equations F : Ensemble (Ensemble nat) :=
  F P := Exists (Same_set P) [P0; P1; P2; P3; P4; P5; P6; P7; P8; P9; P10].

#[local] Instance is_abs_simp_comp : IsAbsSimpComp F.
Proof.
  unfold F.
  split.
  { left. split. apply Included_Empty. apply Included_Empty. }
  (* unfold P0, P1, P2, P3, P4, P5, P6, P7, P8, P9, P10. *)
  (* unfold Ensemble_of_list. *)
  intros S T C E. inversion E as [V a X | V a X]; subst.
  - destruct X as [C0 C1]. hnf. left.
    split. eapply Inclusion_is_transitive; eauto.
    unfold P0. unfold Ensemble_of_list. apply Included_Empty.
  - hnf. right. inversion X; subst.
    admit.
Admitted.

Equations Q2eq (x y : Q * Q) : Prop :=
  Q2eq (x0, x1) (y0, y1) := Qeq x0 y0 /\ Qeq x1 y1.

#[local] Existing Instances
  QOrderedType.Q_as_OT.eq_refl
  QOrderedType.Q_as_OT.eq_sym
  QOrderedType.Q_as_OT.eq_trans.

#[local] Instance Q2eq_is_refl : IsRefl Q2eq.
Proof. intros [x0 x1]. split; reflexivity. Qed.

#[local] Instance Q2eq_is_sym : IsSym Q2eq.
Proof.
  intros [x0 x1] [y0 y1] [a0 a1].
  split; symmetry; assumption.
Qed.

#[local] Instance Q2eq_is_trans : IsTrans Q2eq.
Proof.
  intros [x0 x1] [y0 y1] [z0 z1] [a0 a1] [b0 b1].
  split; etransitivity; eassumption.
Qed.

#[local] Instance Q2eq_is_equiv : IsEquiv Q2eq.
Proof. split; typeclasses eauto. Qed.

Equations K_dec (x y : list (Q * Q)) : list (list (Q * Q)) :=
  K_dec x y := (** Tricky! *) [].

Equations K (x y z : Ensemble (Q * Q)) : Prop :=
  K x y z := (** Tricky! *) False.

#[local] Open Scope Q_scope.

Equations f (n : nat) : Q * Q :=
  f 6 := (8.5, 161);
  f 7 := (143, 169);
  f 8 := (157.5, 8.5);
  f 9 := (255.5, 24);
  f 11 := (31, 260);
  f _ := (0, 0).

#[local] Instance is_simp_comp : IsSimpComp F Q2eq K f.
Proof.
  split.
  - typeclasses eauto.
  - typeclasses eauto.
  - intros P S EP ES T ET. inversion ET.
Qed.

End Example.
