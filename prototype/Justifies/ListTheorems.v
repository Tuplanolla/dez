From Coq Require Import
  List.
From Maniunfold Require Export
  Init.
From Maniunfold.Is Require Import
  Semigroup.

Import ListNotations.

Section Context.

Context {A : Type} `{is_setoid : IsSetoid A}.

Definition list_eqv (xs ys : list A) : Prop :=
  Forall2 (fun x y : A => x == y) xs ys.

Global Instance list_has_eqv : HasEqv (list A) := list_eqv.

Global Instance list_is_reflexive : IsReflexive list_eqv := {}.
Proof.
  intros xs. induction xs as [| x xs IH].
  - apply Forall2_nil.
  - apply Forall2_cons.
    + reflexivity.
    + apply IH. Qed.

Global Instance list_is_symmetric : IsSymmetric list_eqv := {}.
Proof.
  intros xs. induction xs as [| x xs IH]; intros ys H.
  - destruct ys as [| y ys].
    + apply Forall2_nil.
    + inversion H.
  - destruct ys as [| y ys].
    + inversion H.
    + inversion H as [| ? ? ? ? H' Hs']. apply Forall2_cons.
      * symmetry. apply H'.
      * apply IH. apply Hs'. Qed.

Global Instance list_is_transitive : IsTransitive list_eqv := {}.
Proof.
  intros xs. induction xs as [| x xs IH]; intros ys zs H0 H1.
  - destruct ys as [| y ys], zs as [| z zs].
    + apply Forall2_nil.
    + inversion H1.
    + apply Forall2_nil.
    + inversion H0.
  - destruct ys as [| y ys], zs as [| z zs].
    + inversion H0.
    + inversion H1.
    + inversion H1.
    + inversion H0 as [| ? ? ? ? H0' Hs0'].
      inversion H1 as [| ? ? ? ? H1' Hs1']. apply Forall2_cons.
      * etransitivity.
        -- apply H0'.
        -- apply H1'.
      * eapply IH.
        -- apply Hs0'.
        -- apply Hs1'. Qed.

Global Instance list_is_setoid : IsSetoid list_eqv := {}.

End Context.

Fixpoint map2 {A0 A1 B : Type}
  (f : A0 -> A1 -> B) (xs0 : list A0) (xs1 : list A1) : list B :=
  match xs0, xs1 with
  | x0 :: xs0, x1 :: xs1 => f x0 x1 :: map2 f xs0 xs1
  | _, _ => []
  end.

Theorem map2_length : forall {A0 A1 B : Type}
  (f : A0 -> A1 -> B) (xs0 : list A0) (xs1 : list A1),
  length (map2 f xs0 xs1) = min (length xs0) (length xs1).
Proof.
  intros A0 A1 B f xxs0. induction xxs0 as [| x0 xs0 IH0]; intros xxs1.
  - reflexivity.
  - destruct xxs1 as [| x1 xs1].
    + reflexivity.
    + cbn. rewrite (IH0 xs1). reflexivity. Qed.

Section Context.

Import AdditiveNotations.

Context {A : Type} `{is_semigroup : IsSemigroup A}.

Definition list_opr (xs ys : list A) : list A := map2 opr xs ys.

Global Instance list_has_opr : HasOpr (list A) := list_opr.

Global Instance list_is_proper : IsProper (eqv ==> eqv ==> eqv) list_opr := {}.
Proof. intros xs ys H xs' ys' H'. cbv [list_opr]. Admitted.

Global Instance list_is_associative : IsAssociative list_opr := {}.
Proof. intros x y z. cbv [opr]; cbv [list_opr]. Admitted.

Global Instance list_is_semigroup : IsSemigroup list_opr := {}.

End Context.
