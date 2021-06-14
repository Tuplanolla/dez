(** * Extensionality of Functions *)

From Coq Require Import
  Logic.FunctionalExtensionality.
From Maniunfold Require Export
  Init.

(** We declare function extensionality as a class in hopes of it
    becoming a theorem once a better metatheory is implemented. *)

Class IsFunExt : Prop :=
  fun_ext (A B : Type) (f g : A -> B) (e : forall a : A, f a = g a) : f = g.

Class IsFunExtDep : Prop :=
  fun_ext_dep (A : Type) (P : A -> Type)
  (f g : forall a : A, P a) (e : forall a : A, f a = g a) : f = g.

Module FromAxioms.

#[local] Instance is_fun_ext : IsFunExt.
Proof.
  intros A B f g e.
  apply functional_extensionality.
  intros a.
  apply e. Qed.

#[local] Instance is_fun_ext_dep : IsFunExtDep.
Proof.
  intros A P f g e.
  apply functional_extensionality_dep.
  intros a.
  apply e. Qed.

#[export] Hint Resolve is_fun_ext is_fun_ext_dep : typeclass_instances.

End FromAxioms.
