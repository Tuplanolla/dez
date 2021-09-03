(** * Extensionality of Functions and Propositions *)

From Coq Require Import
  Logic.FunctionalExtensionality Logic.PropExtensionality.
From DEZ Require Export
  Init.

(** We declare function extensionality as a class in hopes of turning it
    into a theorem once a better metatheory is implemented. *)

Class IsFunExt : Prop :=
  fun_ext (A B : Type) (f g : A -> B) (a : forall x : A, f x = g x) : f = g.

Class IsFunExtDep : Prop :=
  fun_ext_dep (A : Type) (P : A -> Type)
  (f g : forall x : A, P x) (a : forall x : A, f x = g x) : f = g.

Class IsPropExt : Prop :=
  prop_ext (A B : Prop) (a : A <-> B) : A = B.

Lemma prop_eq_iff (A B : Prop) (a : A = B) : A <-> B.
Proof. rewrite a. reflexivity. Qed.

Lemma prop_iff_eq `(IsPropExt) (A B : Prop) (a : A <-> B) : A = B.
Proof. apply prop_ext. apply a. Qed.

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

#[local] Instance is_prop_ext : IsPropExt.
Proof.
  intros A B a.
  apply propositional_extensionality.
  apply a. Qed.

#[export] Hint Resolve is_fun_ext_dep is_prop_ext : typeclass_instances.

End FromAxioms.

(** Analogous in structure to [equal_f]. *)

Lemma iff_f (A B : Prop) (a : A = B) : A <-> B.
Proof. rewrite a. reflexivity. Qed.
