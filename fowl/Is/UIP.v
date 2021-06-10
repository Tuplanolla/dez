(** * Uniqueness of Identity Proofs *)

From Maniunfold.Has Require Export
  ProofIrrelevance.

Fail Fail Class IsUIP (A : Type) : Prop := uip (x y : A) (a b : x = y) : a = b.

Notation IsUIP := UIP.
Notation uip := (uip : IsUIP _).

Section Context.

Context (A : Type) (e : HasIrrel A).

(** TODO This is stupid. *)

#[local] Instance is_uip : IsUIP A.
Proof.
  intros x y a b.
  set (g (y : A) := e x y).
  assert (e' : forall (y z : A) (p : y = z),
    p = eq_trans (eq_sym (g y)) (g z)).
  { intros y' z' e''. rewrite e''. rewrite eq_trans_sym_inv_l. reflexivity. }
  rewrite e'. rewrite a. rewrite eq_trans_sym_inv_l. reflexivity. Qed.

End Context.

#[export] Hint Resolve is_uip : typeclass_instances.
