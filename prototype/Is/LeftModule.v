From Maniunfold.Has Require Export
  ScalarMultiplication.
From Maniunfold.Is Require Export
  Ring AbelianGroup.

Import AdditiveNotations.

(** TODO Heterogeneous identity and distributivity
    as superclasses of the corresponding ordinary classes. *)

Class IsLeftModule (S A : Type) {S_has_eqv : HasEqv S}
  {S_has_add : HasAdd S} {S_has_zero : HasZero S} {S_has_neg : HasNeg S}
  {S_has_mul : HasMul S} {S_has_one : HasOne S}
  {A_has_eqv : HasEqv A}
  {A_has_opr : HasOpr A} {A_has_idn : HasIdn A} {A_has_inv : HasInv A}
  {has_lsmul : HasLSMul S A} : Prop := {
  S_add_mul_is_ring :> IsRing S;
  A_opr_is_abelian_group :> IsAbelianGroup A;
  lsmul_proper : lsmul ::> eqv ==> eqv ==> eqv;
  lsmul_identity : forall x : A, 1 <* x == x;
  lsmul_mul_compatible : forall (a b : S) (x : A),
    (a * b) <* x == a <* (b <* x);
  lsmul_add_distributive : forall (a b : S) (x : A),
    (a + b) <* x == a <* x + b <* x;
  lsmul_opr_distributive : forall (a : S) (x y : A),
    a <* (x + y) == a <* x + a <* y;
}.

Add Parametric Morphism {S A : Type}
  `{is_left_module : IsLeftModule S A} : lsmul
  with signature eqv ==> eqv ==> eqv
  as eqv_lsmul_morphism.
Proof. intros x y p z w q. apply lsmul_proper; auto. Qed.
