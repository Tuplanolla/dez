(** * Extensionality *)

From Coq Require Import
  Logic.FunctionalExtensionality Logic.ProofIrrelevance
  Logic.PropExtensionality Logic.PropExtensionalityFacts.
From DEZ.Is Require Export
  Isomorphic.

(** We declare various axiom schemes as classes
    in hopes of one day turning them into theorems. *)

(** ** Contractible Type *)
(** ** Singleton *)

Class IsContr (A : Type) : Prop :=
  contr : exists x : A, forall y : A, x = y.

(** ** Contractible-If-Inhabited Type *)
(** ** Mere Proposition *)

Class IsProp (A : Type) : Prop :=
  irrel (x y : A) : x = y.

(** A boxed proposition is a proposition. *)

#[export] Instance prop_is_prop_inhabited (A : Type)
  `{!IsProp A} : IsProp (inhabited A).
Proof. intros [x] [y]. f_equal. apply irrel. Qed.

(** ** Proof Irrelevance *)

Class IsProofIrrel : Prop :=
  proof_irrel (A : Prop) :> IsProp A.

(** ** Discrete Type *)
(** ** Set *)

Fail Fail Class IsSet (A : Type) : Prop :=
  uip (x y : A) (a b : x = y) : a = b.

Arguments UIP _ : clear implicits.
Arguments uip {_ _} _ _ _ _.

Notation IsSet := UIP.
Notation uip := uip.

(** ** Streicher's K *)
(** ** Uniqueness of Identity Proofs *)

Class IsStreicher : Prop :=
  streicher (A : Type) :> IsSet A.

(** ** Homotopy [(n - 2)]-Type *)
(** ** Type of Homotopy Level [n] *)

(** For the sake of convenience, we count up from [0],
    even though homotopy levels conventionally start from [-2]. *)

Equations IsHLevel (A : Type) (n : nat) : Prop by struct n :=
  IsHLevel A O := IsContr A;
  IsHLevel A (S n) := forall x y : A, IsHLevel (x = y) n.

Existing Class IsHLevel.

(** ** Proposition Extensionality *)

Class IsPropExt : Prop :=
  prop_ext (A B : Prop) (a : A <-> B) : A = B.

(** ** Proposition Extensionality for Types *)

Class IsPropExtType : Prop :=
  prop_ext_type (A B : Type) `{!IsProp A} `{!IsProp B}
  (a : (A -> B) * (B -> A)) : A = B.

(** This lemma gets its name from [ZifyClasses.eq_iff]. *)

Lemma eq_iff (A B : Prop) (a : A = B) : A <-> B.
Proof. induction a. reflexivity. Qed.

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

Module FromAxioms.

#[export] Instance is_proof_irrel : IsProofIrrel.
Proof. intros A B. apply proof_irrelevance. Qed.

#[export] Instance is_prop_ext : IsPropExt.
Proof. intros A B. apply propositional_extensionality. Qed.

#[export] Instance is_pred_ext : IsPredExt.
Proof. intros A P Q. apply predicate_extensionality. Qed.

#[export] Instance is_fun_ext : IsFunExt.
Proof. intros A B. apply functional_extensionality. Qed.

#[export] Instance is_fun_ext_dep : IsFunExtDep.
Proof. intros A P. apply functional_extensionality_dep. Qed.

#[export] Instance is_univ : IsUniv.
Proof. intros A B. apply univalence. Qed.

End FromAxioms.
