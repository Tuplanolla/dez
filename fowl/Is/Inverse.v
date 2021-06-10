(** * Left and Right Inverse or Section and Retraction of a Function *)

From Maniunfold Require Export
  Init.

Class IsInvL (A B : Type) (f : A -> B) (g : B -> A) : Prop :=
  inv_l (a : A) : g (f a) = a.

Class IsInvR (A B : Type) (f : A -> B) (g : B -> A) : Prop :=
  inv_r (b : B) : f (g b) = b.

Module RFromL.

Section Context.

Context (A B : Type) (f : A -> B) (g : B -> A) `(!IsInvL f g).

#[local] Instance is_inv_r : IsInvR g f.
Proof. auto. Qed.

End Context.

#[export] Hint Resolve is_inv_r : typeclass_instances.

End RFromL.

Module LFromR.

Section Context.

Context (A B : Type) (f : A -> B) (g : B -> A) `(!IsInvR f g).

#[local] Instance is_inv_l : IsInvL g f.
Proof. auto. Qed.

End Context.

#[export] Hint Resolve is_inv_l : typeclass_instances.

End LFromR.
