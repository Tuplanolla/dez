Set Warnings "-notation-overridden".

From Coq Require Extraction ZArith.

Module Classes.

Class Opr (A : Type) : Type := opr : A -> A -> A.
Class Idn (A : Type) : Type := idn : A.
Class Inv (A : Type) : Type := inv : A -> A.
Class Add (A : Type) : Type := add : A -> A -> A.
Class Zero (A : Type) : Type := zero : A.
Class Neg (A : Type) : Type := neg : A -> A.
Class Mul (A : Type) : Type := mul : A -> A -> A.
Class One (A : Type) : Type := one : A.
Class Recip (A : Type) : Type := recip : A -> A.

Notation "x '+' y" := (add x y).
Notation "'0'" := zero.
Notation "'-' x" := (neg x).
Notation "x '-' y" := (x + (- y)).
Notation "x '*' y" := (mul x y).
Notation "'1'" := one.
Notation "'/' x" := (recip x).
Notation "x '/' y" := (x * (/ y)).

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

Section Additive.

Import AdditiveNotations.

Class Semigroup (A : Type) {opr : Opr A} : Prop := {
  ass : forall x y z : A, (x + y) + z = x + (y + z);
}.

Class Monoid (A : Type) {opr : Opr A} {idn : Idn A} : Prop := {
  semigroup :> Semigroup A;
  idn_l : forall x : A, 0 + x = x;
  idn_r : forall x : A, x + 0 = x;
}.

Class Group (A : Type) {opr : Opr A} {idn : Idn A} {inv : Inv A} : Prop := {
  monoid :> Monoid A;
  inv_l : forall x : A, (- x) + x = 0;
  inv_r : forall x : A, x + (- x) = 0;
}.

End Additive.

Class Ring (A : Type) {add : Add A} {zero : Zero A} {neg : Neg A}
  {mul : Mul A} {one : One A} : Prop := {
  add_group :> Group A (opr := add) (idn := zero) (inv := neg);
  add_com : forall x y : A, x + y = y + x;
  mul_monoid :> Monoid A (opr := mul) (idn := one);
  dis_l : forall x y z : A, x * (y + z) = x * y + x * z;
  dis_r : forall x y z : A, (x + y) * z = x * z + y * z;
}.

End Classes.

Module Properties.

Import Classes AdditiveNotations.

Theorem ivl : forall {A : Type}
  {opr : Opr A} {idn : Idn A} {inv : Inv A} {grp : Group A},
  forall x : A, - (- x) = x.
Proof.
  intros A opr idn inv grp x.
  destruct grp as [[[pa] pnl pnr] pvl pvr].
  rewrite <- (pnr (- (- x))). rewrite <- (pvl x).
  rewrite <- (pa (- (- x)) (- x) x). rewrite (pvl (- x)). rewrite (pnl x).
  reflexivity. Qed.

Lemma inj_l : forall {A : Type}
  {opr : Opr A} {idn : Idn A} {inv : Inv A} {grp : Group A},
  forall x y z : A, z + x = z + y -> x = y.
Proof.
  intros A opr idn inv grp x y z p.
  destruct grp as [[[pa] pnl pnr] pvl pvr].
  rewrite <- (pnl x). rewrite <- (pvl z). rewrite (pa (- z) z x).
  rewrite p. rewrite <- (pa (- z) z y). rewrite (pvl z). rewrite (pnl y).
  reflexivity. Qed.

Lemma inj_r : forall {A : Type}
  {opr : Opr A} {idn : Idn A} {inv : Inv A} {grp : Group A},
  forall x y z : A, x + z = y + z -> x = y.
Proof.
  intros A opr idn inv grp x y z p.
  destruct grp as [[[pa] pnl pnr] pvl pvr].
  rewrite <- (pnr x). rewrite <- (pvr z). rewrite <- (pa x z (- z)).
  rewrite p. rewrite (pa y z (- z)). rewrite (pvr z). rewrite (pnr y).
  reflexivity. Qed.

Theorem dis : forall {A : Type}
  {opr : Opr A} {idn : Idn A} {inv : Inv A} {grp : Group A},
  forall x y : A, - (y + x) = (- x) + (- y).
Proof.
  intros A opr idn inv grp x y.
  apply (inj_l (- (y + x)) ((- x) + (- y)) (y + x)).
  destruct grp as [[[pa] pnl pnr] pvl pvr].
  rewrite (pvr (y + x)). rewrite <- (pa (y + x) (- x) (- y)).
  rewrite (pa y x (- x)). rewrite (pvr x). rewrite (pnr y). rewrite (pvr y).
  reflexivity. Qed.

End Properties.

Module Instances.

Import Classes ZArith Z.

Open Scope Z_scope.

Instance Z_AddOpr : Opr Z := fun x y : Z => x + y.

Instance Z_AddSemigroup : Semigroup Z := {
  ass := _;
}.
Proof.
  all: cbv [Classes.opr Z_AddOpr].
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
  inv_l := _; inv_r := _;
}.
Proof.
  all: cbv [Classes.opr Z_AddOpr Classes.idn Z_AddIdn Classes.inv Z_AddInv].
  - intros x. rewrite add_opp_diag_l. reflexivity.
  - intros x. rewrite add_opp_diag_r. reflexivity. Qed.

Instance Z_MulOpr : Opr Z := fun x y : Z => x * y.

Instance Z_MulSemigroup : Semigroup Z := {
  ass := _;
}.
Proof.
  all: cbv [Classes.opr Z_MulOpr].
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

End Instances.

Module Computations.

Section Input.

Import ZArith Z.

Open Scope Z_scope.

Definition meaning := 42.
Definition luck := 7.
Definition fortune := 13.

End Input.

Section Output.

Import Classes.

Example fate := meaning * fortune - luck.

End Output.

End Computations.

Extraction "example.ml" Classes Properties Instances Computations.
