From Coq Require Import
  PeanoNat List.
From Maniunfold Require Export
  Init.
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

Global Instance sized_list_has_eqv : HasEqv (sized_list A n) := sized_list_eqv.

Global Instance sized_list_is_reflexive : IsReflexive sized_list_eqv := {}.
Proof. intros ?. cbv -[eqv]. reflexivity. Qed.

Global Instance sized_list_is_symmetric : IsSymmetric sized_list_eqv := {}.
Proof. intros ? ? ?. cbv -[eqv]. symmetry; auto. Qed.

Global Instance sized_list_is_transitive : IsTransitive sized_list_eqv := {}.
Proof. intros ? ? ? ? ?. cbv -[eqv]. etransitivity; eauto. Qed.

Global Instance sized_list_is_setoid : IsSetoid sized_list_eqv := {}.

End Context.

Section Context.

Import AdditiveNotations.

Context {A : Type} {n : nat} `{is_semigroup : IsSemigroup A}.

Program Definition sized_list_opr (xs ys : sized_list A n) : sized_list A n :=
  exist _ (proj1_sig xs + proj1_sig ys) _.
Next Obligation.
  destruct xs as [xs Hx], ys as [ys Hy]. cbn. rewrite (map2_length opr xs ys).
  rewrite Hx, Hy. rewrite Nat.min_id. reflexivity. Qed.

Global Instance sized_list_has_opr : HasOpr (sized_list A n) := sized_list_opr.

Global Instance sized_list_is_proper :
  IsProper (eqv ==> eqv ==> eqv) sized_list_opr := {}.
Proof. intros [] [] H [] [] H'. cbv [sized_list_opr]. cbn.
  apply list_is_proper; auto. Qed.

Global Instance sized_list_is_associative : IsAssociative sized_list_opr := {}.
Proof. intros [] [] []. cbv [opr]; cbv [sized_list_opr]. hnf. cbn. Admitted.

Global Instance sized_list_is_semigroup : IsSemigroup sized_list_opr := {}.

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

Global Instance sized_list_has_idn : HasIdn (sized_list A n) := sized_list_idn.

Global Instance sized_list_is_left_identifiable :
  IsLeftIdentifiable sized_list_opr sized_list_idn := {}.
Proof.
  intros []. cbv [opr idn]; cbv [sized_list_opr sized_list_idn].
  hnf. cbn. Admitted.

Global Instance sized_list_is_right_identifiable :
  IsRightIdentifiable sized_list_opr sized_list_idn := {}.
Proof.
  intros []. cbv [opr idn]; cbv [sized_list_opr sized_list_idn].
  hnf. cbn. Admitted.

Global Instance sized_list_is_identifiable :
  IsIdentifiable sized_list_opr sized_list_idn := {}.

Global Instance sized_list_is_monoid :
  IsMonoid sized_list_opr sized_list_idn := {}.

End Context.
