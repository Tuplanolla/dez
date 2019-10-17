From Coq Require Import
  List.
From Maniunfold.Is Require Import
  Setoid.

Section Suffering.

(** TODO Use this nice thing more. *)

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

End Suffering.
