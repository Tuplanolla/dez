From Coq Require ZArith.

Set Warnings "-notation-overridden".

Module Classes.

Class Opr (A : Type) : Type := opr : A -> A -> A.
Class Idn (A : Type) : Type := idn : A.
Class Inv (A : Type) : Type := inv : A -> A.

Local Notation "x '+' y" := (opr x y).
Local Notation "'0'" := idn.
Local Notation "'-' x" := (inv x).
Local Notation "x '*' y" := (opr x y).
Local Notation "'1'" := idn.
Local Notation "'/' x" := (inv x).

Class Group (A : Type) {opr : Opr A} {idn : Idn A} {inv : Inv A} : Prop := {
  assoc : forall x y z : A, (x + y) + z = x + (y + z);
  idn_l : forall x : A, 0 + x = x;
  idn_r : forall x : A, x + 0 = x;
  inv_l : forall x : A, (- x) + x = 0;
  inv_r : forall x : A, x + (- x) = 0;
}.

Class Add (A : Type) : Type := add : A -> A -> A.
Class Zero (A : Type) : Type := zero : A.
Class Neg (A : Type) : Type := neg : A -> A.
Class Mul (A : Type) : Type := mul : A -> A -> A.
Class One (A : Type) : Type := one : A.
Class Recip (A : Type) : Type := recip : A -> A.

Notation "x '+' y" := (add x y).
Notation "'0'" := zero.
Notation "'-' x" := (neg x).
Notation "x '*' y" := (mul x y).
Notation "'1'" := one.
Notation "'/' x" := (recip x).

Class Ring (A : Type) {add : Add A} {zero : Zero A} {neg : Neg A}
  {mul : Mul A} {one : One A} : Prop := {
  add_assoc : forall x y z : A, (x + y) + z = x + (y + z);
  add_idn_l : forall x : A, 0 + x = x;
  add_idn_r : forall x : A, x + 0 = x;
  add_inv_l : forall x : A, (- x) + x = 0;
  add_inv_r : forall x : A, x + (- x) = 0;
  add_comm : forall x y : A, y + x = x + y;
  mul_assoc : forall x y z : A, (x * y) * z = x * (y * z);
  mul_idn_l : forall x : A, 1 * x = x;
  mul_idn_r : forall x : A, x * 1 = x;
  distr_l : forall x y z : A, x * (y + z) = x * y + x * z;
  distr_r : forall x y z : A, (x + y) * z = x * z + y * z;
}.

Module WeakHierarchy.

Local Notation "x '+' y" := (opr x y).
Local Notation "'0'" := idn.
Local Notation "'-' x" := (inv x).

Class Semigroup (A : Type) {opr : Opr A} : Prop := {
  assoc : forall x y z : A, (x + y) + z = x + (y + z);
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

Notation "x '+' y" := (add x y).
Notation "'0'" := zero.
Notation "'-' x" := (neg x).
Notation "x '*' y" := (mul x y).
Notation "'1'" := one.
Notation "'/' x" := (recip x).

Class Ring (A : Type) {add : Add A} {zero : Zero A} {neg : Neg A}
  {mul : Mul A} {one : One A} : Prop := {
  add_group :> Group A (opr := add) (idn := zero) (inv := neg);
  add_comm : forall x y : A, y + x = x + y;
  mul_monoid :> Monoid A (opr := mul) (idn := one);
  distr_l : forall x y z : A, x * (y + z) = x * y + x * z;
  distr_r : forall x y z : A, (x + y) * z = x * z + y * z;
}.

End WeakHierarchy.

End Classes.

Module Properties.

Import Classes.

Local Notation "x '+' y" := (opr x y).
Local Notation "'0'" := idn.
Local Notation "'-' x" := (inv x).

Theorem invol :
  forall {A : Type} {opr : Opr A} {idn : Idn A} {inv : Inv A} {G : Group A},
  forall x : A, - (- x) = x.
Proof.
  intros A opr idn inv G x.
  destruct G as [pa pnl pnr pvl pvr].
  rewrite <- (pnr (- (- x))). rewrite <- (pvl x).
  rewrite <- (pa (- (- x)) (- x) x). rewrite (pvl (- x)). rewrite (pnl x).
  reflexivity. Qed.

Lemma inj_l :
  forall {A : Type} {opr : Opr A} {idn : Idn A} {inv : Inv A} {G : Group A},
  forall x y z : A, z + x = z + y -> x = y.
Proof.
  intros A opr idn inv G x y z p.
  destruct G as [pa pnl pnr pvl pvr].
  rewrite <- (pnl x). rewrite <- (pvl z). rewrite (pa (- z) z x).
  rewrite p. rewrite <- (pa (- z) z y). rewrite (pvl z). rewrite (pnl y).
  reflexivity. Qed.

Lemma inj_r :
  forall {A : Type} {opr : Opr A} {idn : Idn A} {inv : Inv A} {G : Group A},
  forall x y z : A, x + z = y + z -> x = y.
Proof.
  intros A opr idn inv G x y z p.
  destruct G as [pa pnl pnr pvl pvr].
  rewrite <- (pnr x). rewrite <- (pvr z). rewrite <- (pa x z (- z)).
  rewrite p. rewrite (pa y z (- z)). rewrite (pvr z). rewrite (pnr y).
  reflexivity. Qed.

Theorem distr :
  forall {A : Type} {opr : Opr A} {idn : Idn A} {inv : Inv A} {G : Group A},
  forall x y : A, - (y + x) = (- x) + (- y).
Proof.
  intros A opr idn inv G x y.
  apply (inj_l (- (y + x)) ((- x) + (- y)) (y + x)).
  destruct G as [pa pnl pnr pvl pvr].
  rewrite (pvr (y + x)). rewrite <- (pa (y + x) (- x) (- y)).
  rewrite (pa y x (- x)). rewrite (pvr x). rewrite (pnr y). rewrite (pvr y).
  reflexivity. Qed.

End Properties.

Module Instances.

Import Classes ZArith Z.

Open Scope Z_scope.

Instance Z_Opr : Opr Z := fun x y : Z => x + y.
Instance Z_Idn : Idn Z := 0.
Instance Z_Inv : Inv Z := fun x => - x.

Instance Z_Group : Group Z := {
  assoc := _;
  idn_l := _; idn_r := _;
  inv_l := _; inv_r := _;
}.
Proof.
  all: cbv [Classes.opr Z_Opr Classes.idn Z_Idn Classes.inv Z_Inv].
  - intros x y z. rewrite add_assoc. reflexivity.
  - intros x. rewrite add_0_l. reflexivity.
  - intros x. rewrite add_0_r. reflexivity.
  - intros x. rewrite add_opp_diag_l. reflexivity.
  - intros x. rewrite add_opp_diag_r. reflexivity. Qed.

Instance Z_Add : Add Z := fun x y : Z => x + y.
Instance Z_Zero : Zero Z := 0.
Instance Z_Neg : Neg Z := fun x => - x.
Instance Z_Mul : Mul Z := fun x y : Z => x * y.
Instance Z_One : One Z := 1.

Instance Z_Ring : Ring Z := {
  add_assoc := _;
  add_idn_l := _; add_idn_r := _;
  add_inv_l := _; add_inv_r := _;
  add_comm := _;
  mul_assoc := _;
  mul_idn_l := _; mul_idn_r := _;
  distr_l := _; distr_r := _;
}.
Proof.
  all: cbv [Classes.add Z_Add Classes.neg Z_Neg Classes.mul Z_Mul].
  - intros x y z. rewrite add_assoc. reflexivity.
  - intros x. rewrite add_0_l. reflexivity.
  - intros x. rewrite add_0_r. reflexivity.
  - intros x. rewrite add_opp_diag_l. reflexivity.
  - intros x. rewrite add_opp_diag_r. reflexivity.
  - intros x y. rewrite add_comm. reflexivity.
  - intros x y z. rewrite mul_assoc. reflexivity.
  - intros x. rewrite mul_1_l. reflexivity.
  - intros x. rewrite mul_1_r. reflexivity.
  - intros x y z. rewrite mul_add_distr_l. reflexivity.
  - intros x y z. rewrite mul_add_distr_r. reflexivity. Qed.

Module WeakestHierarchy.

Import WeakHierarchy.

Instance Z_AddOpr : Opr Z := fun x y : Z => x + y.

Instance Z_AddSemigroup : Semigroup Z := {
  assoc := _;
}.
Proof.
  all: cbv [Classes.opr Z_Opr Classes.idn Z_Idn Classes.inv Z_Inv].
  - intros x y z. rewrite add_assoc. reflexivity. Qed.

Instance Z_AddIdn : Idn Z := 0.

Instance Z_AddMonoid : Monoid Z := {
  idn_l := _; idn_r := _;
}.
Proof.
  all: cbv [Classes.opr Z_Opr Classes.idn Z_Idn Classes.inv Z_Inv].
  - intros x. rewrite add_0_l. reflexivity.
  - intros x. rewrite add_0_r. reflexivity. Qed.

Instance Z_AddInv : Inv Z := fun x => - x.

Instance Z_AddGroup : Group Z := {
  inv_l := _; inv_r := _;
}.
Proof.
  all: cbv [Classes.opr Z_Opr Classes.idn Z_Idn Classes.inv Z_Inv].
  - intros x. rewrite add_opp_diag_l. reflexivity.
  - intros x. rewrite add_opp_diag_r. reflexivity. Qed.

Instance Z_MulOpr : Opr Z := fun x y : Z => x * y.

Instance Z_MulSemigroup : Semigroup Z := {
  assoc := _;
}.
Proof.
  all: cbv [Classes.opr Z_Opr Classes.idn Z_Idn Classes.inv Z_Inv].
  - intros x y z. rewrite mul_assoc. reflexivity. Qed.

Instance Z_MulIdn : Idn Z := 1.

Instance Z_MulMonoid : Monoid Z := {
  idn_l := _; idn_r := _;
}.
Proof.
  all: cbv [Classes.opr Z_Opr Classes.idn Z_Idn Classes.inv Z_Inv].
  - intros x. rewrite mul_1_l. reflexivity.
  - intros x. rewrite mul_1_r. reflexivity. Qed.

Instance Z_Add : Add Z := Z_AddOpr.
Instance Z_Zero : Zero Z := Z_AddIdn.
Instance Z_Neg : Neg Z := Z_AddInv.
Instance Z_Mul : Mul Z := Z_MulOpr.
Instance Z_One : One Z := Z_MulIdn.

Instance Z_Ring : Ring Z := {
  add_comm := _;
  distr_l := _; distr_r := _;
}.
Proof.
  all: cbv [Classes.add Z_Add Classes.neg Z_Neg Classes.mul Z_Mul].
  - intros x y. rewrite Z.add_comm. reflexivity.
  - intros x y z. rewrite mul_add_distr_l. reflexivity.
  - intros x y z. rewrite mul_add_distr_r. reflexivity. Qed.

End WeakestHierarchy.

End Instances.

Module Computations.

Section Input.

Import ZArith Z.

Open Scope Z_scope.

Definition meaning := 42.
Definition luck := 7.

End Input.

Section Output.

Import Classes.

Example fate := meaning + (- luck).
Example nonsense := meaning * luck.

End Output.

End Computations.

From Coq Require Extraction.

Extraction "example.ml" Classes Properties Instances Computations.
