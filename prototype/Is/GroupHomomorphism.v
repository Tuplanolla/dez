From Maniunfold.Has Require Export
  Homomorphism EquivalenceRelation GroupOperation GroupIdentity GroupInverse.
From Maniunfold.Is Require Export
  MonoidHomomorphism Group.

Import AdditiveNotations.

Class IsGroupHomomorphism {A B : Type}
  {A_has_eqv : HasEqv A} (A_has_opr : HasOpr A)
  (A_has_idn : HasIdn A) (A_has_inv : HasInv A)
  {B_has_eqv : HasEqv B} (B_has_opr : HasOpr B)
  (B_has_idn : HasIdn B) (B_has_inv : HasInv B)
  (has_hom : HasHom A B) : Prop := {
  group_homomorphism_is_monoid_homomorphism :>
    IsMonoidHomomorphism (A := A) (B := B) opr idn opr idn hom;
  group_homomorphism_A_is_group :> IsGroup (A := A) opr idn inv;
  group_homomorphism_B_is_group :> IsGroup (A := B) opr idn inv;
}.

(** We can derive these theorems
    without knowing about the monoidal structure. *)

Theorem hom_preserves_identity : forall {A B : Type}
  `{is_group_homomorphism : IsGroupHomomorphism A B},
  hom 0 == 0.
Proof.
  intros A B ? ? ? ? ? ? ? ? ? ?.
  apply (left_injective (hom 0) 0 (hom 0)).
  rewrite <- (semigroup_homomorphism_preserves_operation 0 0).
  rewrite (right_identifiable 0).
  rewrite (right_identifiable (hom 0)).
  reflexivity. Qed.

Theorem hom_preserves_inverse : forall {A B : Type}
  `{is_group_homomorphism : IsGroupHomomorphism A B},
  forall x : A, hom (- x) == - hom x.
Proof.
  intros A B f ? ? ? ? ? ? ? ? ? x.
  apply (left_injective (hom (- x)) (- hom x) (hom x)).
  rewrite <- (semigroup_homomorphism_preserves_operation x (- x)).
  rewrite (right_invertible x).
  rewrite (right_invertible (hom x)).
  rewrite hom_preserves_identity.
  reflexivity. Qed.
