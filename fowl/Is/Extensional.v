(** * Extensionality of Functions *)

From Coq Require Import
  Logic.FunctionalExtensionality.
From Maniunfold Require Export
  Init.

(** We declare function extensionality as a class in hopes of it
    becoming a theorem once a better metatheory is implemented. *)

Class IsFunExt : Prop :=
  fun_ext (A B : Type) (f g : A -> B) (a : forall x : A, f x = g x) : f = g.

Class IsFunExtDep : Prop :=
  fun_ext_dep (A : Type) (P : A -> Type)
  (f g : forall x : A, P x) (a : forall x : A, f x = g x) : f = g.

Section Context.

Context `(IsFunExtDep).

#[local] Instance is_fun_ext : IsFunExt.
Proof. intros A P f g a. apply fun_ext_dep. apply a. Qed.

End Context.

#[export] Hint Resolve is_fun_ext : typeclass_instances.

Module FromAxioms.

#[local] Instance is_fun_ext_dep : IsFunExtDep.
Proof.
  intros A P f g a.
  apply functional_extensionality_dep.
  intros x.
  apply a. Qed.

#[export] Hint Resolve is_fun_ext_dep : typeclass_instances.

End FromAxioms.
