(** * Uniqueness of Identity Proofs *)

From Maniunfold.Is Require Export
  ProofIrrelevance.

Fail Fail Class IsUIP (A : Type) : Prop :=
  uip (x y : A) (a b : x = y) : a = b.

Notation IsUIP := UIP.
Notation uip := (uip : IsUIP _).

Section Context.

Context (A : Type) `(IsIrrel A).

#[local] Open Scope type_scope.

(** Uniqueness of identity proofs is a special case of proof irrelevance.
    In homotopy type theory parlance, mere propositions are sets. *)

#[local] Instance is_uip : IsUIP A.
Proof.
  intros x y a b.
  set (ex := irrel x).
  assert (ee : forall (w z : A) (e : w = z), e = ex w ^-1 o ex z).
  { intros w z e. rewrite e. rewrite eq_trans_sym_inv_l. reflexivity. }
  rewrite (ee _ _ a), (ee _ _ b). reflexivity. Qed.

End Context.

#[export] Hint Resolve is_uip : typeclass_instances.
