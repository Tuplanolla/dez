From Coq Require Import
  List.
From Maniunfold.Is Require Import
  Setoid.

Section Suffering.

Context {A : Type} `{is_setoid : IsSetoid A}.

Definition option_eqv (xs ys : option A) : Prop :=
  match xs, ys with
  | Some x, Some y => x == y
  | None, None => True
  | _, _ => False
  end.

Global Instance : HasEqv (option A) := option_eqv.

Global Instance : IsReflexive option_eqv := {}.
Proof. intros [x |]. hnf. reflexivity. reflexivity. Qed.

Global Instance : IsSymmetric option_eqv := {}.
Proof. intros [x |] [y |] H; hnf. symmetry; auto.
  inversion H. inversion H. constructor. Qed.

Global Instance : IsTransitive option_eqv := {}.
Proof. intros [x |] [y |] [z |] Hxy Hyz; hnf. all: try etransitivity; eauto.
  all: inversion Hxy || inversion Hyz. Unshelve. apply x. Qed.

Global Instance : IsSetoid option_eqv := {}.

End Suffering.
