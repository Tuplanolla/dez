(** * Groupoid Structure *)

From Coq Require Import
  Logic.ProofIrrelevance.
From DEZ.Has Require Export
  Decisions.
From DEZ.Is Require Export
  Reflexive Symmetric Transitive Equivalence.
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

#[local] Instance is_contr_eq_is_contr `{IsContrEq A} : @IsContr A _=_.
Proof. exact contr_eq. Qed.

#[local] Instance is_contr_is_contr_eq `{!@IsContr A _=_} : IsContrEq A.
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

#[local] Instance is_prop_eq_is_prop `{IsPropEq A} : @IsProp A _=_.
Proof. exact irrel_eq. Qed.

#[local] Instance is_prop_is_prop_eq `{!@IsProp A _=_} : IsPropEq A.
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

#[local] Instance is_set_eq_is_set `{!IsSetEq A} : @IsSet A _=_ (@Y).
Proof. exact uip_eq. Qed.

#[local] Instance is_set_is_set_eq `{!@IsSet A _=_ (@Y)} : IsSetEq A.
Proof. exact uip. Qed.

End Context.

(** ** Homotopy [(2 + n)]-Type *)
(** ** Type of Homotopy Level [n] *)

(** For the sake of convenience, we count up from [0],
    even though homotopy levels conventionally count up from [-2]. *)

Inductive IsHLevel (A : Type) (X : forall {A : Type}, A -> A -> Prop) :
  nat -> Prop :=
  | h_level_zero `{!@IsContr A X} : IsHLevel A (@X) O
  | h_level_succ (n : nat)
    `{forall x y : A, IsHLevel (X x y) (@X) n} : IsHLevel A (@X) (S n).

Existing Class IsHLevel.

Inductive IsHLevelEq (A : Type) : nat -> Prop :=
  | h_level_eq_zero `{IsContrEq A} : IsHLevelEq A O
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
  `{!@IsHLevel A (@X) n} : IsHLevelEq A n.
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
  split.
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
  split.
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
  `{IsHLevel A (@eq) 0} : @IsContr A _=_.
Proof. apply is_h_level_is_contr. Qed.

#[local] Instance eq_is_contr_is_h_level
  `{@IsContr A _=_} : IsHLevel A (@eq) 0.
Proof. apply (h_level_zero _). Qed.

Lemma iff_eq_is_h_level_is_contr :
  IsHLevel A (@eq) 0 <-> @IsContr A _=_.
Proof. split; typeclasses eauto. Qed.

End Context.

(** Homotopy level [-1] corresponds to proof irrelevance. *)

Section Context.

Context (A : Type).

#[local] Instance eq_is_prop_is_h_level
  `{@IsProp A _=_} : IsHLevel A (@eq) 1.
Proof.
  apply iff_is_h_level_succ_is_h_level_eqv.
  intros x y. apply iff_is_h_level_is_contr.
  exists (irrel x y o irrel x x ^-1).
  intros a. rewrite a. rewrite eq_trans_sym_inv_l. reflexivity. Qed.

#[local] Instance eq_is_h_level_is_prop
  `{IsHLevel A (@eq) 1} : @IsProp A _=_.
Proof.
  match goal with
  | h : IsHLevel _ _ _ |- _ => rename h into a
  end.
  intros x y.
  assert (b : @IsContr (x = y) _=_).
  { inversion_clear a. apply iff_is_h_level_is_contr. eauto. }
  apply b. Qed.

Lemma iff_eq_is_h_level_is_prop :
  IsHLevel A (@eq) 1 <-> @IsProp A _=_.
Proof. split; typeclasses eauto. Qed.

End Context.

(** Homotopy level [0] corresponds to uniqueness of identity proofs. *)

Section Context.

Context (A : Type).

Let Y (x y : A) (a b : x = y) := a = b.

#[local] Instance eq_is_set_is_h_level
  `{@IsSet A _=_ (@Y)} : IsHLevel A (@eq) 2.
Proof.
  apply iff_is_h_level_succ_is_h_level_eqv.
  intros x y. apply iff_eq_is_h_level_is_prop.
  intros a b. apply (@uip A _=_ (@Y)). eauto. Qed.

#[local] Instance eq_is_h_level_is_set
  `{IsHLevel A (@eq) 2} : @IsSet A _=_ (@Y).
Proof.
  match goal with
  | h : IsHLevel _ _ _ |- _ => rename h into a
  end.
  intros x y.
  assert (b : @IsProp (x = y) _=_).
  { inversion_clear a. apply iff_eq_is_h_level_is_prop. eauto. }
  apply b. Qed.

Lemma iff_eq_is_h_level_is_set :
  IsHLevel A (@eq) 2 <-> @IsSet A _=_ (@Y).
Proof. split; typeclasses eauto. Qed.

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
  `{@IsProp A _=_} (x y : A) : @IsContr (x = y) _=_.
Proof. eauto with h_intro h_elim. Qed.

#[local] Instance eq_is_contr_eq_is_prop
  `{forall x y : A, @IsContr (x = y) _=_} : @IsProp A _=_.
Proof. eauto with h_intro h_elim. Qed.

Lemma iff_eq_is_prop_is_contr_eq :
  @IsProp A _=_ <-> forall x y : A, @IsContr (x = y) _=_.
Proof. split; typeclasses eauto. Qed.

End Context.

(** Uniqueness of identity proofs is equivalent
    to proof irrelevance of identity proofs. *)

Section Context.

Context (A : Type).

Let Y (x y : A) (a b : x = y) := a = b.

#[local] Instance eq_is_set_is_prop_eq
  `{@IsSet A _=_ (@Y)} (x y : A) : @IsProp (x = y) _=_.
Proof. eauto with h_intro h_elim. Qed.

#[local] Instance eq_is_prop_eq_is_set
  `{forall x y : A, @IsProp (x = y) _=_} : @IsSet A _=_ (@Y).
Proof. eauto with h_intro h_elim. Qed.

Lemma iff_eq_is_set_is_prop_eq :
  @IsSet A _=_ (@Y) <-> forall x y : A, @IsProp (x = y) _=_.
Proof. split; typeclasses eauto. Qed.

End Context.

(** Contractibility implies proof irrelevance. *)

Section Context.

Context (A : Type).

#[local] Instance eq_is_contr_is_prop `{@IsContr A _=_} : @IsProp A _=_.
Proof. eauto with h_intro h_elim. Qed.

End Context.

(** Proof irrelevance implies uniqueness of identity proofs. *)

Section Context.

Context (A : Type).

Let Y (x y : A) (a b : x = y) := a = b.

#[local] Instance eq_is_prop_is_set `{@IsProp A _=_} : @IsSet A _=_ (@Y).
Proof. eauto with h_intro h_elim. Qed.

End Context.

(** Inhabited propositions are contractible. *)

#[local] Instance eq_is_prop_is_contr (A : Type) (x : A)
  `{@IsProp A _=_} : @IsContr A _=_.
Proof. exists x. apply irrel. Qed.

(** Decidable propositions have unique identity proofs. *)

Section Context.

Let Y (x y : bool) (a b : x = y) := a = b.

#[local] Instance eq_bool_is_set : @IsSet bool _=_ (@Y).
Proof. intros x y a b. apply eqdec_uip. apply bool_EqDec. Qed.

End Context.

(** TODO Clean up. *)

#[bad]
#[local] Instance h_level_contr_eq (A : Type) `(IsHLevelEq A 0) : IsContrEq A.
Proof. inversion_clear H. eauto. Qed.

#[bad]
#[local] Instance contr_eq_h_level (A : Type) `(IsContrEq A) : IsHLevelEq A 0.
Proof. apply h_level_eq_zero. Qed.

#[bad]
Lemma iff_contr_eq_h_level (A : Type) : IsContrEq A <-> IsHLevelEq A 0.
Proof. split; [apply contr_eq_h_level | apply h_level_contr_eq]. Qed.

#[bad]
#[local] Instance h_level_eq_succ_h_level_eq (A : Type) (n : nat)
  `{IsHLevelEq A (S n)} (x y : A) : IsHLevelEq (x = y) n.
Proof.
  match goal with
  | s : IsHLevelEq _ _ |- _ => inversion_clear s
  end.
  eauto. Qed.

#[bad] Lemma iff_h_level_eq_succ_h_level_eq
  (A : Type) (n : nat) :
  IsHLevelEq A (S n) <-> forall x y : A, IsHLevelEq (x = y) n.
Proof.
  split.
  - intros a. apply h_level_eq_succ_h_level_eq.
  - intros a. apply h_level_eq_succ. Qed.

#[bad]
Lemma is_h_level_eq_is_h_level_eq_suck (A : Type) (n : nat)
  `(IsHLevelEq A n) : IsHLevelEq A (S n).
Proof.
  match goal with
  | h : IsHLevelEq _ _ |- _ => induction h as [A [x a] | n A t t']
  end.
  - apply iff_h_level_eq_succ_h_level_eq.
    intros y z. apply contr_eq_h_level. exists (a z o a y ^-1).
    intros c. rewrite c.
    unfold symmetry, eq_Symmetric, transitivity, eq_Transitive.
    rewrite eq_trans_sym_inv_l. reflexivity.
  - apply h_level_eq_succ. Qed.

Section Context.

Context (A : Type).

#[bad]
Lemma prop_h_level `(IsPropEq A) : IsHLevelEq A 1.
Proof.
  apply iff_h_level_eq_succ_h_level_eq.
  intros x y. apply iff_contr_eq_h_level.
  exists (irrel_eq x y o irrel_eq x x ^-1). intros a.
  rewrite a. rewrite eq_trans_sym_inv_l. reflexivity. Qed.

#[bad]
Lemma h_level_prop `(IsHLevelEq A 1) : IsPropEq A.
Proof.
  match goal with
  | h : IsHLevelEq _ _ |- _ => inversion_clear h
  end.
  intros x y.
  assert (a : IsContrEq (x = y)).
  { apply iff_contr_eq_h_level. auto. }
  apply a. Qed.

#[bad]
Lemma iff_prop_h_level : IsPropEq A <-> IsHLevelEq A 1.
Proof. split; [apply prop_h_level | apply h_level_prop]. Qed.

#[bad]
Lemma set_h_level `(IsSetEq A) : IsHLevelEq A 2.
Proof.
  apply iff_h_level_eq_succ_h_level_eq.
  intros x y. apply (@is_h_level_is_h_level_eq).
  apply iff_is_h_level_succ_is_h_level_eqv.
  intros a b. Admitted.

#[bad]
Lemma h_level_set `(IsHLevelEq A 2) : IsSetEq A.
Proof.
  match goal with
  | h : IsHLevelEq _ _ |- _ => inversion_clear h
  end.
  intros x y.
  assert (a : IsPropEq (x = y)). Admitted.

#[bad]
Lemma iff_set_h_level : IsSetEq A <-> IsHLevelEq A 2.
Proof. split; [apply set_h_level | apply h_level_set]. Qed.

End Context.

From Coq Require Import
  Logic.FunctionalExtensionality Logic.PropExtensionality.
From DEZ.Is Require Import
  Extensional.
From Equations.Prop Require Import
  Logic.

Lemma pi_is_prop `(IsFunExtDep) (A : Type) (P : A -> Type)
  `(forall x : A, IsPropEq (P x)) : IsPropEq (forall x : A, P x).
Proof.
  rename H0 into h.
  unfold IsPropEq in *.
  intros f g.
  apply fun_ext_dep.
  intros x.
  specialize (h x (f x) (g x)).
  apply h. Qed.

Lemma pi_is_contr_eq `(IsFunExtDep) (A : Type) (P : A -> Prop)
  `(forall x : A, IsContrEq (P x)) : IsContrEq (forall x : A, P x).
Proof.
  assert (forall x : A, IsPropEq (P x)).
  { intros x. apply (@eq_is_contr_is_prop). apply H0. }
  apply pi_is_prop in H1; try eauto.
  apply eq_is_prop_is_contr.
  - intros x. pose proof H0 x. destruct H2. assumption.
  - assumption. Qed.

Lemma pi_is_set `(IsPropExt) `(IsFunExtDep) (A : Type) (P : A -> Type)
  `(forall x : A, IsSetEq (P x)) : IsSetEq (forall x : A, P x).
Proof.
  rename H1 into h.
  pose proof fun (x : A) (a b : P x) =>
  @eq_is_set_is_prop_eq _ (h x) a b as h'.
  intros f g.
  pose proof fun x : A => h' x (f x) (g x) as k.
  pose proof pi_is_prop _ k as k'. cbv beta in k'.
  enough (IsPropEq (f = g)) by auto.
  pose proof (equal_f_dep (f := f) (g := g)) as l.
  pose proof (fun_ext_dep (f := f) (g := g)) as r.
  pose proof conj l r as e.
  pose proof prop_ext e as w.
  rewrite w. apply k'. Qed.

Module FromAxioms.

#[local] Instance is_prop (A : Prop) : IsPropEq A.
Proof.
  intros x y.
  apply proof_irrelevance. Qed.

#[export] Hint Resolve is_prop : typeclass_instances.

End FromAxioms.

Lemma h_level_pi `(IsPropExt) `(IsFunExtDep) (A : Type) (P : A -> Prop) (n : nat)
  `(forall x : A, IsHLevelEq (P x) n) : IsHLevelEq (forall x : A, P x) n.
Proof.
  revert A P H1.
  induction n as [| p t]; intros A P H1.
  - pose proof fun x : A => h_level_contr_eq (H1 x).
    apply iff_contr_eq_h_level.
    apply (@pi_is_contr_eq H0 A P). apply H2.
  - apply (@h_level_eq_succ).
    intros f g.
    pose proof fun (x : A) a b =>
    h_level_eq_succ_h_level_eq (A := P x) (n := p) (H := H1 x) a b as u.
    pose proof fun_ext_dep (f := f) (g := g) as q.
    pose proof equal_f_dep (f := f) (g := g) as r.
    pose proof conj q r as w.
    pose proof prop_ext w.
    rewrite <- H2. apply t. intros x. apply h_level_eq_succ_h_level_eq. Qed.

(** Let us write something extra dubious! *)

Definition lep (x y : bool) : Prop := x -> y.

Definition decreasing (f : nat -> bool) : Prop :=
  forall i : nat, lep (f (S i)) (f i).

Definition nat_inf : Type := {f : nat -> bool | decreasing f}.

Definition zero_inf : nat_inf.
Proof.
  exists (const false). intros i y. apply y. Defined.

Definition succ_inf (x : nat_inf) : nat_inf.
Proof.
  destruct x as [f a].
  exists (fun n : nat =>
  match n with
  | O => true
  | S p => f n
  end). intros i. revert f a. induction i as [| j b]; intros f a.
  - intros y. reflexivity.
  - intros y. apply a. apply y. Defined.

Fixpoint under (n : nat) : nat_inf :=
  match n with
  | O => zero_inf
  | S p => succ_inf (under p)
  end.

Definition LPO : Type :=
  forall x : nat_inf, HasDec (exists n : nat, x = under n).

Unset Universe Checking.

Lemma cohedberg `(IsPropExt) `(IsFunExtDep) :
  ~ forall (A : Type) `(IsSetEq A), HasEqDec A.
Proof.
  intros f.
  pose proof f (nat -> bool) as g.
  assert (x : IsSetEq (nat -> bool)).
  apply (pi_is_set _ _). intros _. apply (@bool_is_set).
  pose proof g x as h.
  clear f g x.
  (** Metatheoretical contr_eqadiction! *) Abort.
