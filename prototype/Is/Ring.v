From Maniunfold.Has Require Import EquivalenceRelation
  GroupOperation GroupIdentity GroupInverse
  FieldOperations FieldIdentities FieldInverses.
From Maniunfold.Is Require Import Semiring Identity Inverse
  Distributive Transitive Absorbing
  Setoid Semigroup Monoid Group AbelianGroup.

Class IsRing (A : Type) {has_eqv : HasEqv A}
  {has_add : HasAdd A} {has_zero : HasZero A} {has_neg : HasNeg A}
  {has_mul : HasMul A} {has_one : HasOne A} : Prop := {
  add_mul_is_semiring :> IsSemiring A;
  add_is_abelian_group :> IsAbelianGroup A
    (has_opr := has_add) (has_idn := has_zero) (has_inv := has_neg);
  mul_is_monoid :> IsMonoid A
    (has_opr := has_mul) (has_idn := has_one);
}.

Theorem zero_left_absorbing : forall {A : Type} `{is_ring : IsRing A},
  forall x : A, 0 * x == 0.
Proof.
  intros A ? ? ? ? ? ? ? x.
  pose proof add_is_abelian_group as add_is_abelian_group.
  pose proof opr_is_group as add_is_group.
  pose proof (opr_right_injective (0 * x) 0 x) as p.
  specialize (p : 0 * x + x == 0 * x -> 0 * x == 0).
  apply p. clear p.
  pose proof (opr_left_identity x) as p.
  specialize (p : 1 * x == x).
  rewrite <- p at 2. clear p.
  pose proof (mul_add_right_distributive 0 1 x) as p.
  specialize (p : (0 + 1) * x == 0 * x + 1 * x).
  Fail rewrite <- p. Admitted.
(** Cannot rewrite, because the following do not unify for some reason.

<<
@add A (@opr A (@add_has_opr A has_add))
  (@mul A has_mul (@zero A has_zero) x) (@mul A
    (@opr A (@add_has_opr A has_add))
    (@one A (@idn A (@zero_has_idn A has_zero))
      ) x)
@add A has_add
  (@mul A has_mul (@zero A has_zero) x) (@mul A
    has_mul
    (@one A has_one
      ) x)
>> *)

Theorem zero_right_absorbing : forall {A : Type} `{is_ring : IsRing A},
  forall x : A, x * 0 == 0.
Proof. Admitted.

Instance zero_is_left_absorbing {A : Type} `{is_ring : IsRing A} :
  IsLeftAbsorbing A := {}.
Proof. apply zero_left_absorbing. Qed.

Instance zero_is_right_absorbing {A : Type} `{is_ring : IsRing A} :
  IsRightAbsorbing A := {}.
Proof. apply zero_right_absorbing. Qed.

Instance zero_is_absorbing {A : Type} `{is_ring : IsRing A} :
  IsAbsorbing A := {}.
