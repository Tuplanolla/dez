(** * Proof Irrelevance and Uniqueness of Identity Proofs *)

From Maniunfold Require Export
  Init.

Class IsProp (A : Type) : Prop :=
  irrel (x y : A) : x = y.

Fail Fail Class IsSet (A : Type) : Prop :=
  uip (x y : A) (a b : x = y) : a = b.

Notation IsSet := UIP.
Notation uip := (uip : IsSet _).

Section Context.

Context (A : Type) `(IsProp A).

#[local] Open Scope type_scope.

(** Uniqueness of identity proofs is a special case of proof irrelevance.
    In homotopy type theory parlance, mere propositions are sets. *)

#[local] Instance is_set : IsSet A.
Proof.
  assert (e : forall (x y z : A) (e : x = z), e = irrel y x ^-1 o irrel y z).
  { intros x y z e. rewrite e. rewrite eq_trans_sym_inv_l. reflexivity. }
  intros x y a b. rewrite (e x x y a), (e x x y b). reflexivity. Qed.

End Context.

#[export] Hint Resolve is_set : typeclass_instances.
