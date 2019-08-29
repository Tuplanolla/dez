Set Warnings "-notation-overridden".

From Coq Require Extraction Setoid ZArith.

Module Classes.

Import Setoid Morphisms.

(* Definition relation (A : Type) : Type :=
  A -> A -> Prop.

Definition respectful {A B : Type}
  (R : relation A) (S : relation B) (f g : A -> B) : Prop :=
  forall x y : A, R x y -> S (f x) (g y).

Definition Proper {A : Type} (R : relation A) (x : A) : Prop :=
  R x x.

Reserved Notation "R '==>' S" (at level 55, right associativity).
Notation "R '==>' S" := (respectful R S). *)

Reserved Notation "x '::>' R" (at level 60, right associativity).
Notation "x '::>' R" := (Proper R x).

Class Eqv (A : Type) : Type := eqv : A -> A -> Prop.
Class Opr (A : Type) : Type := opr : A -> A -> A.
Class Idn (A : Type) : Type := idn : A.
Class Inv (A : Type) : Type := inv : A -> A.
Class Add (A : Type) : Type := add : A -> A -> A.
Class Zero (A : Type) : Type := zero : A.
Class Neg (A : Type) : Type := neg : A -> A.
Class Mul (A : Type) : Type := mul : A -> A -> A.
Class One (A : Type) : Type := one : A.
Class Recip (A : Type) : Type := recip : A -> A.
Class LSMul (S A : Type) : Type := lsmul : S -> A -> A.
Class RSMul (S A : Type) : Type := rsmul : S -> A -> A.

Reserved Notation "x '==' y" (at level 70, no associativity).
Notation "x '==' y" := (eqv x y).
Notation "x '+' y" := (add x y).
Notation "'0'" := zero.
Notation "'-' x" := (neg x).
Notation "x '-' y" := (x + (- y)).
Notation "x '*' y" := (mul x y).
Notation "'1'" := one.
Notation "'/' x" := (recip x).
Notation "x '/' y" := (x * (/ y)).
Reserved Notation "a '<*' x" (at level 45, left associativity).
Notation "a '<*' x" := (lsmul a x).
Reserved Notation "x '*>' a" (at level 45, left associativity).
Notation "x '*>' a" := (rsmul a x).

Module AdditiveNotations.

Notation "x '+' y" := (opr x y).
Notation "'0'" := idn.
Notation "'-' x" := (inv x).
Notation "x '-' y" := (x + (- y)).

End AdditiveNotations.

Module MultiplicativeNotations.

Notation "x '*' y" := (opr x y).
Notation "'1'" := idn.
Notation "'/' x" := (inv x).
Notation "x '/' y" := (x * (/ y)).

End MultiplicativeNotations.

Class Setoid (A : Type) {eqv : Eqv A} : Prop := {
  ref : forall x : A, x == x;
  sym : forall x y : A, x == y -> y == x;
  tra : forall x y z : A, x == y -> y == z -> x == z;
}.

Section Additive.

Import AdditiveNotations.

Class Semigroup (A : Type) {eqv : Eqv A} {opr : Opr A} : Prop := {
  setoid :> Setoid A;
  opr_pro : opr ::> eqv ==> eqv ==> eqv;
  ass : forall x y z : A, (x + y) + z = x + (y + z);
}.

Class Monoid (A : Type) {eqv : Eqv A} {opr : Opr A} {idn : Idn A} : Prop := {
  semigroup :> Semigroup A;
  idn_l : forall x : A, 0 + x = x;
  idn_r : forall x : A, x + 0 = x;
}.

Class Group (A : Type) {eqv : Eqv A}
  {opr : Opr A} {idn : Idn A} {inv : Inv A} : Prop := {
  monoid :> Monoid A;
  inv_pro : inv ::> eqv ==> eqv;
  inv_l : forall x : A, (- x) + x = 0;
  inv_r : forall x : A, x + (- x) = 0;
}.

End Additive.

Class Ring (A : Type) {eqv : Eqv A} {add : Add A} {zero : Zero A} {neg : Neg A}
  {mul : Mul A} {one : One A} : Prop := {
  add_group :> Group A (opr := add) (idn := zero) (inv := neg);
  add_com : forall x y : A, x + y = y + x;
  mul_monoid :> Monoid A (opr := mul) (idn := one);
  dis_l : forall x y z : A, x * (y + z) = x * y + x * z;
  dis_r : forall x y z : A, (x + y) * z = x * z + y * z;
}.

Module Left.

Class LeftModule (S A : Type)
  {seqv : Eqv S} {sadd : Add S} {szero : Zero S} {sneg : Neg S}
  {smul : Mul S} {sone : One S}
  {eqv : Eqv A} {add : Add A} {zero : Zero A} {neg : Neg A}
  {lsmul : LSMul S A} : Prop := {
  sring :> Ring S (add := sadd) (zero := szero) (neg := sneg)
    (mul := smul) (one := sone);
  group :> Group A (opr := add) (idn := zero) (inv := neg);
  sadd_com : forall x y : A, x + y = y + x;
  lsmul_pro : lsmul ::> seqv ==> eqv ==> eqv;
  lsmul_smul_cpt : forall (a b : S) (x : A), (a * b) <* x = a <* (b <* x);
  lsmul_idn : forall x : A, 1 <* x = x;
  lsmul_add_dis : forall (a : S) (x y : A), a <* (x + y) = a <* x + a <* y;
  lsmul_sadd_dis : forall (a b : S) (x : A), (a + b) <* x = a <* x + b <* x;
}.

End Left.

Module Right.

Class RightModule (S A : Type)
  {seqv : Eqv S} {sadd : Add S} {szero : Zero S} {sneg : Neg S}
  {smul : Mul S} {sone : One S}
  {eqv : Eqv A} {add : Add A} {zero : Zero A} {neg : Neg A}
  {rsmul : RSMul S A} : Prop := {
  sring :> Ring S (add := sadd) (zero := szero) (neg := sneg)
    (mul := smul) (one := sone);
  group :> Group A (opr := add) (idn := zero) (inv := neg);
  sadd_com : forall x y : A, x + y = y + x;
  rsmul_pro : rsmul ::> seqv ==> eqv ==> eqv;
  rsmul_smul_cpt : forall (a b : S) (x : A), x *> (a * b) = (x *> a) *> b;
  rsmul_idn : forall x : A, x *> 1 = x;
  rsmul_add_dis : forall (a : S) (x y : A), (x + y) *> a = x *> a + y *> a;
  rsmul_sadd_dis : forall (a b : S) (x : A), x *> (a + b) = x *> a + x *> b;
}.

End Right.

Add Parametric Relation {A : Type} {eqv' : Eqv A}
  {std' : Setoid A} : A eqv
  reflexivity proved by ref
  symmetry proved by sym
  transitivity proved by tra
  as eqv_relation.

Add Parametric Morphism {A : Type} {eqv' : Eqv A}
  {opr' : Opr A} {sgr' : Semigroup A} : opr
  with signature eqv ==> eqv ==> eqv
  as eqv_opr_morphism.
Proof.
  intros x y p z w q.
  destruct sgr' as [_ opr_pro _].
  cbv in opr_pro. apply opr_pro.
  - apply p.
  - apply q. Qed.

Add Parametric Morphism {A : Type} {eqv' : Eqv A}
  {opr' : Opr A} {idn' : Idn A} {inv' : Inv A} {grp' : Group A} : inv
  with signature eqv ==> eqv
  as eqv_inv_morphism.
Proof.
  intros x y p.
  destruct grp' as [_ inv_pro _ _].
  cbv in inv_pro. apply inv_pro. apply p. Qed.

Add Parametric Morphism {A : Type} {eqv' : Eqv A}
  {add' : Add A} {zero' : Zero A} {neg' : Neg A}
  {mul' : Mul A} {one' : One A} {rng' : Ring A} : add
  with signature eqv ==> eqv ==> eqv
  as eqv_add_morphism.
Proof.
  intros x y p z w q.
  destruct rng' as [[[[_ add_pro _] _ _] _ _ _] _ _ _ _].
  cbv in add_pro. apply add_pro.
  - apply p.
  - apply q. Qed.

Add Parametric Morphism {A : Type} {eqv' : Eqv A}
  {add' : Add A} {zero' : Zero A} {neg' : Neg A}
  {mul' : Mul A} {one' : One A} {rng' : Ring A} : neg
  with signature eqv ==> eqv
  as eqv_neg_morphism.
Proof.
  intros x y p.
  destruct rng' as [[[_ _ _] neg_pro _ _] _ _ _ _].
  cbv in neg_pro. apply neg_pro. apply p. Qed.

Add Parametric Morphism {A : Type} {eqv' : Eqv A}
  {add' : Add A} {zero' : Zero A} {neg' : Neg A}
  {mul' : Mul A} {one' : One A} {rng' : Ring A} : mul
  with signature eqv ==> eqv ==> eqv
  as eqv_mul_morphism.
Proof.
  intros x y p z w q.
  destruct rng' as [_ _ [[_ mul_pro _] _ _] _ _].
  cbv in mul_pro. apply mul_pro.
  - apply p.
  - apply q. Qed.

Import Left.

Add Parametric Morphism {S A : Type}
  {seqv' : Eqv S} {sadd' : Add S} {szero' : Zero S} {sneg' : Neg S}
  {smul' : Mul S} {sone' : One S}
  {eqv' : Eqv A} {add' : Add A} {zero' : Zero A} {neg' : Neg A}
  {lsmul' : LSMul S A} {lmod' : LeftModule S A} : lsmul
  with signature eqv ==> eqv ==> eqv
  as eqv_lsmul_morphism.
Proof.
  intros x y p z w q.
  destruct lmod' as [_ _ _ lsmul_pro _ _ _ _].
  cbv in lsmul_pro. apply lsmul_pro.
  - apply p.
  - apply q. Qed.

Import Right.

Add Parametric Morphism {S A : Type}
  {seqv' : Eqv S} {sadd' : Add S} {szero' : Zero S} {sneg' : Neg S}
  {smul' : Mul S} {sone' : One S}
  {eqv' : Eqv A} {add' : Add A} {zero' : Zero A} {neg' : Neg A}
  {rsmul' : RSMul S A} {rmod' : RightModule S A} : rsmul
  with signature eqv ==> eqv ==> eqv
  as eqv_rsmul_morphism.
Proof.
  intros x y p z w q.
  destruct rmod' as [_ _ _ rsmul_pro _ _ _ _].
  cbv in rsmul_pro. apply rsmul_pro.
  - apply p.
  - apply q. Qed.

End Classes.

Module Properties.

Import Classes AdditiveNotations.

Theorem ivl : forall {A : Type} {eqv : Eqv A}
  {opr : Opr A} {idn : Idn A} {inv : Inv A} {grp : Group A},
  forall x : A, - (- x) == x.
Proof.
  intros A eqv opr idn inv grp x.
  destruct grp as [[[ps pop pa] pnl pnr] pvp pvl pvr] eqn : pg.
  rewrite <- (pnr (- (- x))). rewrite <- (pvl x).
  rewrite <- (pa (- (- x)) (- x) x). rewrite (pvl (- x)). rewrite (pnl x).
  reflexivity. Qed.

Lemma inj_l : forall {A : Type} {eqv : Eqv A}
  {opr : Opr A} {idn : Idn A} {inv : Inv A} {grp : Group A},
  forall x y z : A, z + x == z + y -> x == y.
Proof.
  intros A eqv opr idn inv grp x y z p.
  destruct grp as [[[ps pop pa] pnl pnr] pvp pvl pvr] eqn : pg.
  rewrite <- (pnl x). rewrite <- (pvl z). rewrite (pa (- z) z x).
  rewrite p. rewrite <- (pa (- z) z y). rewrite (pvl z). rewrite (pnl y).
  reflexivity. Qed.

Lemma inj_r : forall {A : Type} {eqv : Eqv A}
  {opr : Opr A} {idn : Idn A} {inv : Inv A} {grp : Group A},
  forall x y z : A, x + z == y + z -> x == y.
Proof.
  intros A eqv opr idn inv grp x y z p.
  destruct grp as [[[ps pop pa] pnl pnr] pvp pvl pvr] eqn : pg.
  rewrite <- (pnr x). rewrite <- (pvr z). rewrite <- (pa x z (- z)).
  rewrite p. rewrite (pa y z (- z)). rewrite (pvr z). rewrite (pnr y).
  reflexivity. Qed.

Theorem dis : forall {A : Type} {eqv : Eqv A}
  {opr : Opr A} {idn : Idn A} {inv : Inv A} {grp : Group A},
  forall x y : A, - (y + x) == (- x) + (- y).
Proof.
  intros A eqv opr idn inv grp x y.
  apply (inj_l (- (y + x)) ((- x) + (- y)) (y + x)).
  destruct grp as [[[ps pop pa] pnl pnr] pvp pvl pvr] eqn : pg.
  rewrite (pvr (y + x)). rewrite <- (pa (y + x) (- x) (- y)).
  rewrite (pa y x (- x)). rewrite (pvr x). rewrite (pnr y). rewrite (pvr y).
  reflexivity. Qed.

End Properties.

Module Instances.

Import Classes ZArith Z.

Open Scope Z_scope.

Instance Z_Eqv : Eqv Z := fun x y : Z => x = y.

Instance Z_Setoid : Setoid Z := {
  ref := _;
  sym := _;
  tra := _;
}.
Proof.
  all: cbv [Classes.eqv Z_Eqv].
  - apply eq_refl.
  - apply eq_sym.
  - apply eq_trans. Qed.

Instance Z_AddOpr : Opr Z := fun x y : Z => x + y.

Instance Z_AddSemigroup : Semigroup Z := {
  opr_pro := _;
  ass := _;
}.
Proof.
  all: cbv [Classes.opr Z_AddOpr].
  - apply add_wd.
  - intros x y z. rewrite add_assoc. reflexivity. Qed.

Instance Z_AddIdn : Idn Z := 0.

Instance Z_AddMonoid : Monoid Z := {
  idn_l := _; idn_r := _;
}.
Proof.
  all: cbv [Classes.opr Z_AddOpr Classes.idn Z_AddIdn].
  - intros x. rewrite add_0_l. reflexivity.
  - intros x. rewrite add_0_r. reflexivity. Qed.

Instance Z_AddInv : Inv Z := fun x => - x.

Instance Z_AddGroup : Group Z := {
  inv_pro := _;
  inv_l := _; inv_r := _;
}.
Proof.
  all: cbv [Classes.opr Z_AddOpr Classes.idn Z_AddIdn Classes.inv Z_AddInv].
  - apply opp_wd.
  - intros x. rewrite add_opp_diag_l. reflexivity.
  - intros x. rewrite add_opp_diag_r. reflexivity. Qed.

Instance Z_MulOpr : Opr Z := fun x y : Z => x * y.

Instance Z_MulSemigroup : Semigroup Z := {
  opr_pro := _;
  ass := _;
}.
Proof.
  all: cbv [Classes.opr Z_MulOpr].
  - apply mul_wd.
  - intros x y z. rewrite mul_assoc. reflexivity. Qed.

Instance Z_MulIdn : Idn Z := 1.

Instance Z_MulMonoid : Monoid Z := {
  idn_l := _; idn_r := _;
}.
Proof.
  all: cbv [Classes.opr Z_MulOpr Classes.idn Z_MulIdn].
  - intros x. rewrite mul_1_l. reflexivity.
  - intros x. rewrite mul_1_r. reflexivity. Qed.

Instance Z_Add : Add Z := Z_AddOpr.
Instance Z_Zero : Zero Z := Z_AddIdn.
Instance Z_Neg : Neg Z := Z_AddInv.
Instance Z_Mul : Mul Z := Z_MulOpr.
Instance Z_One : One Z := Z_MulIdn.

Instance Z_Ring : Ring Z := {
  add_com := _;
  dis_l := _; dis_r := _;
}.
Proof.
  all: cbv [Classes.add Z_Add Classes.zero Z_Zero Classes.neg Z_Neg
    Classes.mul Z_Mul Classes.one Z_One].
  all: cbv [Z_AddOpr Z_AddIdn Z_AddInv Z_MulOpr Z_MulIdn].
  - intros x y. rewrite add_comm. reflexivity.
  - intros x y z. rewrite mul_add_distr_l. reflexivity.
  - intros x y z. rewrite mul_add_distr_r. reflexivity. Qed.

(** It would be more motivating to build a module over zip-lists. *)
(* Import List. *)

Instance Z_LSMul : LSMul Z Z := fun (a : Z) (x : Z) => a * x.

Import Left.

Instance Z_LeftModule : LeftModule Z Z := {
  sadd_com := _;
  lsmul_pro := _;
  lsmul_smul_cpt := _;
  lsmul_idn := _;
  lsmul_add_dis := _;
  lsmul_sadd_dis := _;
}.
Proof.
  all: cbv [Classes.add Z_Add Classes.zero Z_Zero Classes.neg Z_Neg
    Classes.mul Z_Mul Classes.one Z_One].
  all: cbv [Z_AddOpr Z_AddIdn Z_AddInv Z_MulOpr Z_MulIdn].
  - intros x y. rewrite add_comm. reflexivity.
  - apply mul_wd.
  - intros a b x. rewrite mul_assoc. reflexivity.
  - intros x. rewrite mul_1_l. reflexivity.
  - intros a x y. rewrite mul_add_distr_l. reflexivity.
  - intros a b x. rewrite mul_add_distr_r. reflexivity. Qed.

End Instances.

Module Computations.

Section Input.

Import ZArith Z.

Open Scope Z_scope.

Definition meaning := 42.
Definition luck := 7.
Definition fortune := 13.
Definition hope := 69.

End Input.

Section Output.

Import Classes.

Example fate := meaning * fortune - hope <* luck.

End Output.

End Computations.

Extraction "example.ml" Classes Properties Instances Computations.
