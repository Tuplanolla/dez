(** * Extensionality and Univalence *)

From Coq Require Import
  Logic.FunctionalExtensionality Logic.ProofIrrelevance
  Logic.PropExtensionality Logic.PropExtensionalityFacts.
From DEZ.Is Require Export
  Irrelevant Isomorphic.

(** We declare various axiom schemes as classes
    in hopes of one day turning them into theorems. *)

(** ** Proposition Extensionality *)

Class IsPropExt : Prop :=
  prop_ext (A B : Prop) (a : A <-> B) : A = B.

(** This lemma gets its name from [ZifyClasses.eq_iff]. *)

Lemma eq_iff (A B : Prop) (a : A = B) : A <-> B.
Proof. induction a. reflexivity. Qed.

(** ** Proposition Extensionality for Types *)

Class IsPropExtType : Prop :=
  prop_ext_type (A B : Type) `{!IsProp A} `{!IsProp B}
  (a : (A -> B) * (B -> A)) : A = B.

Lemma eq_iff_type (A B : Type) `{!IsProp A} `{!IsProp B}
  (a : A = B) : (A -> B) * (B -> A).
Proof. induction a. split; apply id. Defined.

(** Equal types are equivalent. *)

#[export] Instance idtoeqv (A B : Type) (a : A = B) : IsEquivTypes A B _=_ _=_.
Proof. induction a. typeclasses eauto. Defined.

(** ** Predicate Extensionality *)

Class IsPredExt : Prop :=
  pred_ext (A : Type) (P Q : A -> Prop) (a : forall x : A, P x <-> Q x) : P = Q.

(** ** Predicate Extensionality Axiom *)

Axiom predicate_extensionality :
  forall (A : Type) (P Q : A -> Prop) (a : forall x : A, P x <-> Q x),
  P = Q.

(** ** Function Extensionality *)

Class IsFunExt : Prop :=
  fun_ext (A B : Type) (f g : A -> B) (a : forall x : A, f x = g x) : f = g.

(** This lemma gets its name from [FunctionalExtensionality.equal_f]. *)

Lemma equal_f (A B : Type) (f g : A -> B) (a : f = g) (x : A) : f x = g x.
Proof. induction a. reflexivity. Qed.

(** ** Dependent Function Extensionality *)

Class IsFunExtDep : Prop :=
  fun_ext_dep (A : Type) (P : A -> Type)
  (f g : forall x : A, P x) (a : forall x : A, f x = g x) : f = g.

(** Dependent function extensionality implies function extensionality. *)

#[export] Instance fun_ext_dep_is_fun_ext
  `{!IsFunExtDep} : IsFunExt.
Proof. intros A B f g a. apply fun_ext_dep. intros x. apply a. Qed.

(** ** Univalence *)

Class IsUniv : Prop :=
  ua (A B : Type) (a : IsEquivTypes A B _=_ _=_) : A = B.

(** ** Univalence Axiom *)

Axiom univalence : forall A B : Type,
  exists ua : IsEquivTypes A B _=_ _=_ -> A = B,
  IsIso _=_ _=_ idtoeqv ua.

(** TODO Why? *)

(** Propositional extensionality 
    makes functional extensionality an equality. *)

Lemma prop_fun_ext_dep `{IsPropExt} `{IsFunExtDep}
  (A : Type) (P : A -> Type) (f g : forall x : A, P x) :
  (f = g) = (forall x : A, f x = g x).
Proof.
  apply prop_ext. split.
  - intros a x. apply equal_f_dep. apply a.
  - intros a. apply fun_ext_dep. intros x. apply a. Qed.

(** Families of propositions are propositions. *)

Lemma eq_pi_is_prop `{IsFunExtDep} (A : Type) (P : A -> Prop)
  `{!forall x : A, IsProp (P x)} : IsProp (forall x : A, P x).
Proof.
  match goal with
  | h : forall _ : _, IsProp _ |- _ => rename h into p
  end.
  intros g h. apply fun_ext_dep. intros x. apply p. Qed.

(** Families of contractible types are contractible. *)

Lemma eq_pi_is_contr `{IsFunExtDep} (A : Type) (P : A -> Prop)
  `{!forall x : A, IsContr (P x)} : IsContr (forall x : A, P x).
Proof.
  match goal with
  | h : forall _ : _, IsContr _ |- _ => rename h into c
  end.
  apply @inhabited_prop_is_contr.
  - intros x. apply c.
  - apply (@eq_pi_is_prop _). intros x. apply contr_is_prop. Qed.

(** TODO This is theorem 4.9.4 from the book. *)

Lemma eq_pi_is_contr' `{IsUniv} (A : Type) (P : A -> Prop)
  `{!forall x : A, IsContr (P x)} : IsContr (forall x : A, P x).
Proof.
  match goal with
  | h : forall _ : _, IsContr _ |- _ => rename h into c
  end. Admitted.

(** Families of sets are sets. *)

Lemma eq_pi_is_set `{IsPropExt} `{IsFunExtDep} (A : Type) (P : A -> Prop)
  `{!forall x : A, IsSet (P x)} : IsSet (forall x : A, P x).
Proof.
  match goal with
  | h : forall _ : _, IsSet _ |- _ => rename h into s
  end.
  intros f g.
  pose proof prop_fun_ext_dep f g as t. rewrite t. clear t.
  apply (@eq_pi_is_prop _).
  intros x. apply @set_is_prop_eq. apply s. Qed.

(** Fibrations are at the same homotopy level as their fibers. *)

Lemma eq_h_level_is_h_level `{IsPropExt} `{IsFunExtDep}
  (A : Type) (P : A -> Prop) (n : nat)
  `{!forall x : A, IsHLevel (P x) n} : IsHLevel (forall x : A, P x) n.
Proof.
  match goal with
  | h : forall _ : _, IsHLevel _ _ |- _ => rename h into a
  end.
  revert A P a. induction n as [| p b]; intros A P a.
  - apply @contr_is_h_level_0. apply (@eq_pi_is_contr _).
    intros x. apply @h_level_0_is_contr. apply a.
  - intros f g.
    pose proof prop_fun_ext_dep f g as t. rewrite t. clear t.
    apply b. intros x. apply h_level_S_is_h_level_eq. apply a. Qed.

Module FromAxioms.

#[export] Instance is_proof_irrel : IsProofIrrel.
Proof. intros A B. apply proof_irrelevance. Qed.

#[export] Instance is_prop_ext : IsPropExt.
Proof. intros A B. apply propositional_extensionality. Qed.

#[export] Instance is_prop_ext_type : IsPropExtType.
Proof.
  intros A B IPA IPB [f g]. pose proof univalence A B as s.
  destruct s as [ua [IPidtoeqv IPua r s]]. apply ua. exists f, g. split.
  - intros x y a. apply irrel.
  - intros x y a. apply irrel.
  - intros x. apply irrel.
  - intros x. apply irrel. Qed.

#[export] Instance is_pred_ext : IsPredExt.
Proof. intros A P Q. apply predicate_extensionality. Qed.

#[export] Instance is_fun_ext : IsFunExt.
Proof. intros A B. apply functional_extensionality. Qed.

#[export] Instance is_fun_ext_dep : IsFunExtDep.
Proof. intros A P. apply functional_extensionality_dep. Qed.

#[export] Instance is_univ : IsUniv.
Proof. intros A B. apply univalence. Qed.

End FromAxioms.
