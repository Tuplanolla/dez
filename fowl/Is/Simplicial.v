(** * Simplicial Complexes *)

From Coq Require Import
  Lists.List Reals.Reals Sets.Ensembles Sets.Powerset_facts.
From DEZ Require Export
  Init.
From Topology Require Import
  Homeomorphisms.

(** ** Topological Manifold *)

(** TODO See this issue.

    https://github.com/coq-community/topology/issues/29 *)

Fail Class IsTopManifold (A : (* Indexed *) Type) (M : TopologicalSpace)
  (n : nat) (f : A -> homeomorphism (_ : M -> R ^ n)) : Prop := {
  SECOND_COUNTABLE : False;
  HAUSDORFF : False;
}.

(** ** Abstract Simplicial Complex *)

(** We slightly deviate from the standard definition.
    Instead of requiring that every subset of the set of faces is nonempty,
    we require that the empty set is a face of every complex. *)

Class IsAbsSimpComp (A : Type) (F : Ensemble (Ensemble A)) : Prop := {
  nonempty : Ensembles.In F Empty_set;
  abs_simp_comp (P Q : Ensemble A) (C : Included P Q)
  (E : Ensembles.In F Q) : Ensembles.In F P;
}.

(** ** Real Simplicial Complex *)

(** TODO Embed into a manifold (chart) here. *)

Class IsRealSimpComp (A : Type) (F : Ensemble (Ensemble A))
  (n : nat) (f : A -> (Fin.t n -> R)) : Prop := {
  NONINTERSECTING : False;
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

Definition F : Ensemble (Ensemble nat) := fun P : Ensemble nat =>
  Exists (Same_set P) [P0; P1; P2; P3; P4; P5; P6; P7; P8; P9; P10].

#[local] Instance F_is_abs_simp_comp : IsAbsSimpComp F.
Proof.
  unfold F.
  split.
  { left. split. apply Included_Empty. apply Included_Empty. }
  (* unfold P0, P1, P2, P3, P4, P5, P6, P7, P8, P9, P10. *)
  (* unfold Ensemble_of_list. *)
  intros S T C E. inversion E as [V a X | V a X]; subst.
  - destruct X as [L0 L1]. hnf. left.
    split. eapply Inclusion_is_transitive; eauto.
    unfold P0. unfold Ensemble_of_list. apply Included_Empty.
  - hnf. right. inversion X; subst.
    admit.
Admitted.

(*
8.5, 161
143, 169
157.5, 8.5
255.5, 24
31, 260
*)

End Example.
