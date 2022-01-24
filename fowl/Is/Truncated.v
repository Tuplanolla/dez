(** * Homotopy Levels *)

From Coq Require Import
  Logic.FunctionalExtensionality Logic.PropExtensionality.
From DEZ.Has Require Export
  Decisions.
From DEZ.Is Require Export
  Reflexive Symmetric Transitive Equivalence Extensional.
From DEZ.ShouldHave Require Import
  EquivalenceNotations.

#[local] Unset Universe Minimization ToSet.

#[local] Open Scope type_scope.

(** ** Contractibility *)
(** ** Singleton *)

Class IsContr (A : Type) (X : A -> A -> Prop) : Prop :=
  contr : exists x : A, forall y : A, X x y.

Class IsContrEq (A : Type) : Prop :=
  contr_eq : exists x : A, forall y : A, x = y.

Section Context.

Context (A : Type).

#[local] Instance is_contr_eq_is_contr `{IsContrEq A} : @IsContr A eq.
Proof. exact contr_eq. Qed.

#[local] Instance is_contr_is_contr_eq `{@IsContr A eq} : IsContrEq A.
Proof. exact contr. Qed.

End Context.

(** ** Proof Irrelevance *)
(** ** Proposition *)

Class IsProp (A : Type) (X : A -> A -> Prop) : Prop :=
  irrel (x y : A) : X x y.

Class IsPropEq (A : Type) : Prop :=
  irrel_eq (x y : A) : x = y.

Section Context.

Context (A : Type).

#[local] Instance is_prop_eq_is_prop `{IsPropEq A} : @IsProp A eq.
Proof. exact irrel_eq. Qed.

#[local] Instance is_prop_is_prop_eq `{@IsProp A eq} : IsPropEq A.
Proof. exact irrel. Qed.

End Context.

(** ** Set *)
(** ** Uniqueness of Identity Proofs *)

Fail Fail Class IsSetEq (A : Type) : Prop :=
  uip_eq (x y : A) (a b : x = y) : a = b.

Arguments uip {_ _} _ _ _ _.

Notation IsSetEq := UIP.
Notation uip_eq := uip.

Class IsSet (A : Type) (X : A -> A -> Prop)
  (Y : forall {x y : A}, X x y -> X x y -> Prop) : Prop :=
  uip (x y : A) (a b : X x y) : Y a b.

Section Context.

Context (A : Type).

Let Y (x y : A) (a b : x = y) := a = b.

#[local] Instance is_set_eq_is_set `{IsSetEq A} : @IsSet A eq (@Y).
Proof. exact uip_eq. Qed.

#[local] Instance is_set_is_set_eq `{@IsSet A eq (@Y)} : IsSetEq A.
Proof. exact uip. Qed.

End Context.

(** ** Homotopy [(2 + n)]-Type *)
(** ** Type of Homotopy Level [n] *)

(** For the sake of convenience, we count up from [0],
    even though homotopy levels conventionally count up from [-2]. *)

Inductive IsHLevel (A : Type) (X : forall {A : Type}, A -> A -> Prop) :
  nat -> Prop :=
  | h_level_zero
    `{@IsContr A X} : IsHLevel A (@X) O
  | h_level_succ (n : nat)
    `{forall x y : A, IsHLevel (X x y) (@X) n} : IsHLevel A (@X) (S n).

Existing Class IsHLevel.

Inductive IsHLevelEq (A : Type) : nat -> Prop :=
  | h_level_eq_zero
    `{IsContrEq A} : IsHLevelEq A O
  | h_level_eq_succ (n : nat)
    `{forall x y : A, IsHLevelEq (x = y) n} : IsHLevelEq A (S n).

Existing Class IsHLevelEq.

Section Context.

Context (A : Type).

Let X (A : Type) (x y : A) := x = y.

#[local] Instance is_h_level_eq_is_h_level (n : nat)
  `{IsHLevelEq A n} : IsHLevel A (@X) n.
Proof.
  match goal with
  | h : IsHLevelEq _ _ |- _ => rename h into a
  end.
  revert A X a. induction n as [| p b]; intros A X a.
  - constructor. inversion_clear a. eauto.
  - constructor. intros x y. inversion_clear a as [| ? c].
    pose proof (c x y) as d. eauto. Qed.

#[local] Instance is_h_level_is_h_level_eq (n : nat)
  `{@IsHLevel A (@X) n} : IsHLevelEq A n.
Proof.
  match goal with
  | h : IsHLevel _ _ _ |- _ => rename h into a
  end.
  revert A X a. induction n as [| p b]; intros A X a.
  - constructor. inversion_clear a. eauto.
  - constructor. intros x y. inversion_clear a as [| ? c].
    pose proof (c x y) as d. eauto. Qed.

End Context.

Section Context.

Context (A : Type) (X : forall {A : Type}, A -> A -> Prop).

(** Inversion of [h_level_zero]. *)

#[local] Instance is_h_level_is_contr
  `{IsHLevel A (@X) O} : @IsContr A X.
Proof.
  match goal with
  | h : IsHLevel _ _ _ |- _ => rename h into a
  end.
  inversion_clear a. eauto. Qed.

(** Biconditionality of [h_level_zero]. *)

Lemma iff_is_h_level_is_contr :
  IsHLevel A (@X) O <-> @IsContr A X.
Proof.
  esplit.
  - typeclasses eauto.
  - apply h_level_zero. Qed.

End Context.

Section Context.

Context (A : Type) (X : forall {A : Type}, A -> A -> Prop).

(** Inversion of [h_level_succ]. *)

#[local] Instance is_h_level_succ_is_h_level_eqv (n : nat)
  `{IsHLevel A (@X) (S n)} (x y : A) : IsHLevel (X x y) (@X) n.
Proof.
  match goal with
  | h : IsHLevel _ _ _ |- _ => rename h into a
  end.
  inversion_clear a. eauto. Qed.

(** Biconditionality of [h_level_succ]. *)

Lemma iff_is_h_level_succ_is_h_level_eqv (n : nat) :
  IsHLevel A (@X) (S n) <-> forall x y : A, IsHLevel (X x y) (@X) n.
Proof.
  esplit.
  - typeclasses eauto.
  - apply (@h_level_succ). Qed.

End Context.

(** Homotopy levels are cumulative. *)

Section Context.

Context (A : Type).

#[local] Instance eq_is_h_level_is_h_level_succ (n : nat)
  `{IsHLevel A (@eq) n} : IsHLevel A (@eq) (S n).
Proof.
  match goal with
  | h : IsHLevel _ _ _ |- _ => rename h into a
  end.
  revert A a. induction n as [| p c]; intros A a.
  - apply iff_is_h_level_is_contr in a. destruct a as [x f].
    apply iff_is_h_level_succ_is_h_level_eqv.
    intros y z. apply h_level_zero. exists (f z o f y ^-1).
    intros b. rewrite b. rewrite eq_trans_sym_inv_l. reflexivity.
  - apply (@h_level_succ).
    intros x y. apply c. apply (@is_h_level_succ_is_h_level_eqv). apply a. Qed.

#[local] Instance eq_is_h_level_is_h_level_add (p n : nat)
  `{IsHLevel A (@eq) n} : IsHLevel A (@eq) (p + n).
Proof.
  match goal with
  | h : IsHLevel _ _ _ |- _ => rename h into a
  end.
  revert n a. induction p as [| q c]; intros n a.
  - eauto.
  - replace (S q + n)%nat with (S (q + n))%nat by reflexivity.
    apply eq_is_h_level_is_h_level_succ. Qed.

End Context.

(** Homotopy level [-2] corresponds to contractibility. *)

Section Context.

Context (A : Type).

#[local] Instance eq_is_h_level_is_contr
  `{IsHLevel A (@eq) 0} : @IsContr A eq.
Proof. apply is_h_level_is_contr. Qed.

#[local] Instance eq_is_contr_is_h_level
  `{@IsContr A eq} : IsHLevel A (@eq) 0.
Proof. apply (h_level_zero _). Qed.

Lemma iff_eq_is_h_level_is_contr :
  IsHLevel A (@eq) 0 <-> @IsContr A eq.
Proof. esplit; typeclasses eauto. Qed.

End Context.

(** Homotopy level [-1] corresponds to proof irrelevance. *)

Section Context.

Context (A : Type).

#[local] Instance eq_is_prop_is_h_level
  `{@IsProp A eq} : IsHLevel A (@eq) 1.
Proof.
  apply iff_is_h_level_succ_is_h_level_eqv.
  intros x y. apply iff_is_h_level_is_contr.
  exists (irrel x y o irrel x x ^-1).
  intros a. rewrite a. rewrite eq_trans_sym_inv_l. reflexivity. Qed.

#[local] Instance eq_is_h_level_is_prop
  `{IsHLevel A (@eq) 1} : @IsProp A eq.
Proof.
  match goal with
  | h : IsHLevel _ _ _ |- _ => rename h into a
  end.
  intros x y.
  assert (b : @IsContr (x = y) eq).
  { inversion_clear a. apply iff_is_h_level_is_contr. eauto. }
  apply b. Qed.

Lemma iff_eq_is_h_level_is_prop :
  IsHLevel A (@eq) 1 <-> @IsProp A eq.
Proof. esplit; typeclasses eauto. Qed.

End Context.

(** Homotopy level [0] corresponds to uniqueness of identity proofs. *)

Section Context.

Context (A : Type).

Let Y (x y : A) (a b : x = y) := a = b.

#[local] Instance eq_is_set_is_h_level
  `{@IsSet A eq (@Y)} : IsHLevel A (@eq) 2.
Proof.
  apply iff_is_h_level_succ_is_h_level_eqv.
  intros x y. apply iff_eq_is_h_level_is_prop.
  intros a b. apply (@uip A eq (@Y)). eauto. Qed.

#[local] Instance eq_is_h_level_is_set
  `{IsHLevel A (@eq) 2} : @IsSet A eq (@Y).
Proof.
  match goal with
  | h : IsHLevel _ _ _ |- _ => rename h into a
  end.
  intros x y.
  assert (b : @IsProp (x = y) eq).
  { inversion_clear a. apply iff_eq_is_h_level_is_prop. eauto. }
  apply b. Qed.

Lemma iff_eq_is_h_level_is_set :
  IsHLevel A (@eq) 2 <-> @IsSet A eq (@Y).
Proof. esplit; typeclasses eauto. Qed.

End Context.

(** Hints that introduce and eliminate homotopy levels. *)

Create HintDb h_intro.

#[export] Hint Resolve
  h_level_zero h_level_succ
  is_h_level_eq_is_h_level is_h_level_succ_is_h_level_eqv
  eq_is_h_level_is_h_level_succ eq_is_h_level_is_h_level_add
  eq_is_contr_is_h_level eq_is_prop_is_h_level eq_is_set_is_h_level : h_intro.

Create HintDb h_elim.

#[export] Hint Resolve
  is_h_level_is_contr h_level_succ
  is_h_level_is_h_level_eq is_h_level_succ_is_h_level_eqv
  eq_is_h_level_is_h_level_succ eq_is_h_level_is_h_level_add
  eq_is_h_level_is_contr eq_is_h_level_is_prop eq_is_h_level_is_set : h_elim.

(** We now have enough machinery to automatically prove some basic results. *)

(** Proof irrelevance is equivalent
    to contractibility of identity proofs. *)

Section Context.

Context (A : Type).

#[local] Instance eq_is_prop_is_contr_eq
  `{@IsProp A eq} (x y : A) : @IsContr (x = y) eq.
Proof. eauto with h_intro h_elim. Qed.

#[local] Instance eq_is_contr_eq_is_prop
  `{forall x y : A, @IsContr (x = y) eq} : @IsProp A eq.
Proof. eauto with h_intro h_elim. Qed.

Lemma iff_eq_is_prop_is_contr_eq :
  @IsProp A eq <-> forall x y : A, @IsContr (x = y) eq.
Proof. esplit; typeclasses eauto. Qed.

End Context.

(** Uniqueness of identity proofs is equivalent
    to proof irrelevance of identity proofs. *)

Section Context.

Context (A : Type).

Let Y (x y : A) (a b : x = y) := a = b.

#[local] Instance eq_is_set_is_prop_eq
  `{@IsSet A eq (@Y)} (x y : A) : @IsProp (x = y) eq.
Proof. eauto with h_intro h_elim. Qed.

#[local] Instance eq_is_prop_eq_is_set
  `{forall x y : A, @IsProp (x = y) eq} : @IsSet A eq (@Y).
Proof. eauto with h_intro h_elim. Qed.

Lemma iff_eq_is_set_is_prop_eq :
  @IsSet A eq (@Y) <-> forall x y : A, @IsProp (x = y) eq.
Proof. esplit; typeclasses eauto. Qed.

End Context.

(** Contractibility implies proof irrelevance. *)

Section Context.

Context (A : Type).

#[local] Instance eq_is_contr_is_prop `{@IsContr A eq} : @IsProp A eq.
Proof. eauto with h_intro h_elim. Qed.

End Context.

(** Proof irrelevance implies uniqueness of identity proofs. *)

Section Context.

Context (A : Type).

Let Y (x y : A) (a b : x = y) := a = b.

#[local] Instance eq_is_prop_is_set `{@IsProp A eq} : @IsSet A eq (@Y).
Proof. eauto with h_intro h_elim. Qed.

End Context.

(** Inhabited propositions are contractible. *)

#[local] Instance eq_is_prop_is_contr (A : Type) (x : A)
  `{@IsProp A eq} : @IsContr A eq.
Proof. exists x. apply irrel. Qed.

(** Decidable propositions have unique identity proofs. *)

Section Context.

Let Y (x y : bool) (a b : x = y) := a = b.

#[local] Instance eq_bool_is_set : @IsSet bool eq (@Y).
Proof. intros x y a b. apply eqdec_uip. apply bool_EqDec. Qed.

End Context.

Lemma eq_pi_is_prop `{IsFunExtDep} (A : Type) (P : A -> Type)
  `{forall x : A, @IsProp (P x) eq} : @IsProp (forall x : A, P x) eq.
Proof.
  match goal with
  | h : forall _ : _, IsProp _ |- _ => rename h into f
  end.
  intros g h. apply fun_ext_dep. intros x. apply f. Qed.

Lemma eq_pi_is_set `{IsPropExt} `{IsFunExtDep} (A : Type) (P : A -> Type)
  `{forall x : A, @IsSet (P x) eq (fun y z : P x => eq)} :
  @IsSet (forall x : A, P x) eq (fun y z : forall x : A, P x => eq).
Proof.
  match goal with
  | h : forall _ : _, IsSet _ |- _ => rename h into f
  end.
  pose proof fun (x : A) (a b : P x) =>
  @eq_is_set_is_prop_eq _ (f x) a b as h'.
  intros g h.
  pose proof fun x : A => h' x (g x) (h x) as k.
  (* k' : IsPropEq (forall x : A, g x = h x) *)
  assert (k' : @IsProp (forall x : A, @eq (P x) (g x) (h x)) eq)
  by apply eq_pi_is_prop.
  enough (@IsProp (g = h) eq) by auto.
  pose proof (equal_f_dep (f := g) (g := h)) as l.
  pose proof (fun_ext_dep (f := g) (g := h)) as r.
  pose proof conj l r as e.
  pose proof prop_ext e as w.
  rewrite w. apply k'. Qed.

Lemma eq_pi_is_contr `{IsFunExtDep} (A : Type) (P : A -> Prop)
  `{forall x : A, @IsContr (P x) eq} : @IsContr (forall x : A, P x) eq.
Proof.
  match goal with
  | h : forall _ : _, IsContr _ |- _ => rename h into a
  end.
  assert (b : forall x : A, @IsProp (P x) eq).
  { intros x. apply (@eq_is_contr_is_prop). apply a. }
  apply (@eq_pi_is_prop) in b; eauto. apply eq_is_prop_is_contr; eauto.
  intros x. pose proof a x as c. apply c. Qed.

Lemma eq_h_level_is_h_level `{IsPropExt} `{IsFunExtDep}
  (A : Type) (P : A -> Prop) (n : nat)
  `{forall x : A, @IsHLevel (P x) (@eq) n} :
  @IsHLevel (forall x : A, P x) (@eq) n.
Proof.
  match goal with
  | h : forall _ : _, IsHLevel _ _ _ |- _ => rename h into f
  end.
  revert A P f. induction n as [| p t]; intros A P f.
  - pose proof fun x : A => @is_h_level_is_contr _ _ (f x) as m.
    apply iff_is_h_level_is_contr.
    apply eq_pi_is_contr.
  - apply (@h_level_succ).
    intros g h.
    pose proof fun_ext_dep (f := g) (g := h) as q.
    pose proof equal_f_dep (f := g) (g := h) as r.
    pose proof conj q r as w.
    pose proof prop_ext w as m.
    rewrite <- m. apply t. intros x.
    apply is_h_level_succ_is_h_level_eqv. Qed.

Module FromAxioms.

#[export] Instance prop_is_prop (A : Prop) : @IsProp A eq.
Proof. intros x y. apply proof_irrelevance. Qed.

End FromAxioms.
