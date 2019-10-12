From Maniunfold.Has Require Export
  Homomorphism EquivalenceRelation GroupOperation GroupIdentity GroupInverse.
From Maniunfold.Is Require Export
  MonoidHomomorphism Group.

Import AdditiveNotations.

Class IsGroupHomomorphism (A B : Type) {has_hom : HasHom A B}
  {A_has_eqv : HasEqv A} {A_has_opr : HasOpr A}
  {A_has_idn : HasIdn A} {A_has_inv : HasInv A}
  {B_has_eqv : HasEqv B} {B_has_opr : HasOpr B}
  {B_has_idn : HasIdn B} {B_has_inv : HasInv B} : Prop := {
  hom_is_monoid_homomorphism :> IsMonoidHomomorphism A B;
  A_is_group :> IsGroup A;
  B_is_group :> IsGroup B;
}.

(** We can derive these theorems
    without knowing about the monoidal structure. *)

Theorem hom_preserves_identity : forall {A B : Type}
  `{is_group_homomorphism : IsGroupHomomorphism A B},
  hom 0 == 0.
Proof.
  intros A B f ? ? ? ? ? ? ? ? ?.
  apply (opr_left_injective (hom 0) 0 (hom 0)).
  rewrite <- (hom_preserves_operation 0 0).
  rewrite (opr_right_identifiable 0).
  rewrite (opr_right_identifiable (hom 0)).
  reflexivity. Qed.

Theorem hom_preserves_inverse : forall {A B : Type}
  `{is_group_homomorphism : IsGroupHomomorphism A B},
  forall x : A, hom (- x) == - hom x.
Proof.
  intros A B f ? ? ? ? ? ? ? ? ? x.
  apply (opr_left_injective (hom (- x)) (- hom x) (hom x)).
  rewrite <- (hom_preserves_operation x (- x)).
  rewrite (opr_right_invertible x).
  rewrite (opr_right_invertible (hom x)).
  rewrite hom_preserves_identity.
  reflexivity. Qed.
