(** * Extensionality *)

From Coq Require Import
  Logic.FunctionalExtensionality Logic.PropExtensionality.
From DEZ.Is Require Export
  Isomorphic.

(** See, this is where setoids are no longer useful. *)

Class IsFunExtGen (X : forall {A : Type}, A -> A -> Prop) : Prop :=
  fun_ext_gen (A B : Type) (f g : A -> B)
  (a : forall x : A, X (f x) (g x)) : X f g.

Class IsFunExtDepGen (X : forall {A : Type}, A -> A -> Prop) : Prop :=
  fun_ext_dep_gen (A : Type) (P : A -> Type) (f g : forall x : A, P x)
  (a : forall x : A, X (f x) (g x)) : X f g.

Class IsPropExtGen (X : forall {A : Type}, A -> A -> Prop) : Prop :=
  prop_ext_gen (A B : Prop) (a : A <-> B) : X A B.

Class IsUnivGen (X : forall {A : Type}, A -> A -> Prop) : Prop :=
  univ_gen (A B : Type) (a : IsEquivTypes A B X X) : A = B.

(** We declare function extensionality as a class in hopes of turning it
    into a theorem once a better metatheory is implemented. *)

(** ** Function Extensionality *)

Class IsFunExt : Prop :=
  fun_ext (A B : Type) (f g : A -> B) (a : forall x : A, f x = g x) : f = g.

#[local] Lemma equal_f (A B : Type)
  (f g : A -> B) (a : f = g) (x : A) : f x = g x.
Proof. rewrite a. reflexivity. Qed.

(** ** Dependent Function Extensionality *)

Class IsFunExtDep : Prop :=
  fun_ext_dep (A : Type) (P : A -> Type)
  (f g : forall x : A, P x) (a : forall x : A, f x = g x) : f = g.

(** ** Propositional Extensionality *)

Class IsPropExt : Prop := prop_ext (A B : Prop) (a : A <-> B) : A = B.

#[local] Lemma eq_iff (A B : Prop) (a : A = B) : A <-> B.
Proof. rewrite a. reflexivity. Qed.

(** ** Univalence *)

Class IsUniv : Prop :=
  univ (A B : Type) (a : IsEquivTypes A B _=_ _=_) : A = B.

#[local] Lemma idtoeqv (A B : Type) (a : A = B) : IsEquivTypes A B _=_ _=_.
Proof.
  induction a. exists id, id. split.
  - intros x. reflexivity.
  - intros x. reflexivity. Qed.

Axiom univalence : forall A B : Type,
  exists ua : IsEquivTypes A B _=_ _=_ -> A = B,
  IsIso _=_ _=_ idtoeqv ua.

#[export] Instance is_fun_ext `{!IsFunExtDep} : IsFunExt.
Proof. intros A P f g a. apply fun_ext_dep. apply a. Qed.

Module FromAxioms.

#[export] Instance is_fun_ext_dep : IsFunExtDep.
Proof.
  intros A P f g a.
  apply functional_extensionality_dep.
  intros x.
  apply a. Qed.

#[export] Instance is_prop_ext : IsPropExt.
Proof.
  intros A B a.
  apply propositional_extensionality.
  apply a. Qed.

#[export] Instance is_univ : IsUniv.
Proof.
  intros A B a.
  apply univalence.
  apply a. Qed.

End FromAxioms.
