From Coq Require Import
  PeanoNat List.
From Maniunfold.Is Require Import
  Monoid.
From Maniunfold.Justifies Require Import
  NatTheorems ListTheorems.

Import ListNotations.

Definition sized_list (A : Type) (n : nat) : Type :=
  {xs : list A | length xs == n}.

Section Context.

Context {A : Type} {n : nat} `{is_setoid : IsSetoid A}.

Definition sized_list_eqv (xs ys : sized_list A n) : Prop :=
  proj1_sig xs == proj1_sig ys.

Global Instance : HasEqv (sized_list A n) := sized_list_eqv.

Global Instance : IsReflexive sized_list_eqv := {}.
Proof. intros ?. cbv -[eqv]. reflexivity. Qed.

Global Instance : IsSymmetric sized_list_eqv := {}.
Proof. intros ? ? ?. cbv -[eqv]. symmetry; auto. Qed.

Global Instance : IsTransitive sized_list_eqv := {}.
Proof. intros ? ? ? ? ?. cbv -[eqv]. etransitivity; eauto. Qed.

Global Instance : IsSetoid sized_list_eqv := {}.

End Context.

Section Context.

Import AdditiveNotations.

Context {A : Type} {n : nat} `{is_semigroup : IsSemigroup A}.

Program Definition sized_list_opr (xs ys : sized_list A n) : sized_list A n :=
  exist _ (proj1_sig xs + proj1_sig ys) _.
Next Obligation.
  destruct xs as [xs Hx], ys as [ys Hy]. cbn. rewrite (map2_length opr xs ys).
  rewrite Hx, Hy. rewrite Nat.min_id. reflexivity. Qed.

Global Instance : HasOpr (sized_list A n) := sized_list_opr.

Global Instance :
  IsProper (eqv ==> eqv ==> eqv) sized_list_opr := {}.
Proof. intros [] [] H [] [] H'. cbv [sized_list_opr]. cbn.
  apply Proper_instance_0; auto. Qed.

Global Instance : IsAssociative sized_list_opr := {}.
Proof. intros [] [] []. cbv [opr]; cbv [sized_list_opr]. hnf. cbn. Admitted.

Global Instance : IsSemigroup sized_list_opr := {}.

End Context.

Section Context.

Import AdditiveNotations.

Context {A : Type} {n : nat} `{is_monoid : IsMonoid A}.

Program Definition sized_list_idn : sized_list A n :=
  exist _ (repeat idn n) _.
Next Obligation.
  induction n as [| p IH].
  - reflexivity.
  - cbn. rewrite IH. reflexivity. Qed.

Global Instance : HasIdn (sized_list A n) := sized_list_idn.

Global Instance :
  IsLeftIdentifiable sized_list_opr sized_list_idn := {}.
Proof.
  intros []. cbv [opr idn]; cbv [sized_list_opr sized_list_idn].
  hnf. cbn. Admitted.

Global Instance :
  IsRightIdentifiable sized_list_opr sized_list_idn := {}.
Proof.
  intros []. cbv [opr idn]; cbv [sized_list_opr sized_list_idn].
  hnf. cbn. Admitted.

Global Instance :
  IsIdentifiable sized_list_opr sized_list_idn := {}.

Global Instance :
  IsMonoid sized_list_opr sized_list_idn := {}.

End Context.
