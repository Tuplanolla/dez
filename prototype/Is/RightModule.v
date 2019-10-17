From Maniunfold.Has Require Export
  ScalarMultiplication.
From Maniunfold.Is Require Export
  Ring AbelianGroup.

Import AdditiveNotations.

Class IsRightModule (S A : Type) {S_has_eqv : HasEqv S}
  {S_has_add : HasAdd S} {S_has_zero : HasZero S} {S_has_neg : HasNeg S}
  {S_has_mul : HasMul S} {S_has_one : HasOne S}
  {A_has_eqv : HasEqv A}
  {A_has_opr : HasOpr A} {A_has_idn : HasIdn A} {A_has_inv : HasInv A}
  {has_rsmul : HasRSMul S A} : Prop := {
  right_module_is_ring :> IsRing S;
  right_module_is_abelian_group :> IsAbelianGroup A;
  right_module_rsmul_is_proper :> IsProper (eqv ==> eqv ==> eqv) rsmul;
  right_module_rsmul_identity : forall x : A, x *> 1 == x;
  right_module_rsmul_mul_compatible : forall (a b : S) (x : A),
    x *> (a * b) == (x *> a) *> b;
  right_module_rsmul_add_distributive : forall (a b : S) (x : A),
    x *> (a + b) == x *> a + x *> b;
  right_module_rsmul_opr_distributive : forall (a : S) (x y : A),
    (x + y) *> a == x *> a + y *> a;
}.

Add Parametric Morphism {S A : Type}
  `{is_right_module : IsRightModule S A} : rsmul
  with signature eqv ==> eqv ==> eqv
  as eqv_rsmul_morphism.
Proof. intros x y p z w q. apply right_module_rsmul_is_proper; auto. Qed.
