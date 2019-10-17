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
  left_module_is_ring :> IsRing S;
  left_module_is_abelian_group :> IsAbelianGroup A;
  left_module_lsmul_is_proper :> IsProper (eqv ==> eqv ==> eqv) lsmul;
  left_module_lsmul_identity : forall x : A, 1 <* x == x;
  left_module_lsmul_mul_compatible : forall (a b : S) (x : A),
    (a * b) <* x == a <* (b <* x);
  left_module_lsmul_add_distributive : forall (a b : S) (x : A),
    (a + b) <* x == a <* x + b <* x;
  left_module_lsmul_opr_distributive : forall (a : S) (x y : A),
    a <* (x + y) == a <* x + a <* y;
}.

Add Parametric Morphism {S A : Type}
  `{is_left_module : IsLeftModule S A} : lsmul
  with signature eqv ==> eqv ==> eqv
  as eqv_lsmul_morphism.
Proof. intros x y p z w q. apply left_module_lsmul_is_proper; auto. Qed.
