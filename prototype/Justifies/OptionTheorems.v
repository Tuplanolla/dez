From Coq Require Import
  List.
From Maniunfold.Is Require Import
  Setoid.

Section Suffering.

Context {A : Type} `{is_setoid : IsSetoid A}.

Global Instance option_has_eqv : HasEqv (option A) := fun xs ys : option A =>
  match xs, ys with
  | Some x, Some y => x == y
  | None, None => True
  | _, _ => False
  end.

Global Instance option_is_reflexive : IsReflexive (option A) := {}.
Proof. intros [x |]. hnf. reflexivity. reflexivity. Qed.

Global Instance option_is_symmetric : IsSymmetric (option A) := {}.
Proof. intros [x |] [y |] H; hnf. symmetry; auto.
  inversion H. inversion H. constructor. Qed.

Global Instance option_is_transitive : IsTransitive (option A) := {}.
Proof. intros [x |] [y |] [z |] Hxy Hyz; hnf. all: try etransitivity; eauto.
  all: inversion Hxy || inversion Hyz. Unshelve. apply x. Qed.

Global Instance option_is_setoid : IsSetoid (option A) := {}.

End Suffering.
