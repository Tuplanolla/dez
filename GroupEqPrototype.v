From Coq Require Extraction ZArith.

Set Warnings "-notation-overridden".

Module Classes.

Class Opr (A : Type) : Type := opr : A -> A -> A.
Class Idn (A : Type) : Type := idn : A.
Class Inv (A : Type) : Type := inv : A -> A.

Notation "x '+' y" := (opr x y).
Notation "'0'" := idn.
Notation "'-' x" := (inv x).

Class Group (A : Type) {opr : Opr A} {idn : Idn A} {inv : Inv A} : Prop := {
  ass : forall x y z : A, (x + y) + z = x + (y + z);
  idn_l : forall x : A, 0 + x = x;
  idn_r : forall x : A, x + 0 = x;
  inv_l : forall x : A, (- x) + x = 0;
  inv_r : forall x : A, x + (- x) = 0;
}.

Module WeakHierarchy.

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

End WeakHierarchy.

End Classes.

Module Properties.

Import Classes.

Theorem ivl : forall {A : Type}
  {opr : Opr A} {idn : Idn A} {inv : Inv A} {grp : Group A},
  forall x : A, - (- x) = x.
Proof.
  intros A opr idn inv grp x.
  destruct grp as [pa pnl pnr pvl pvr].
  rewrite <- (pnr (- (- x))). rewrite <- (pvl x).
  rewrite <- (pa (- (- x)) (- x) x). rewrite (pvl (- x)). rewrite (pnl x).
  reflexivity. Qed.

Lemma inj_l : forall {A : Type}
  {opr : Opr A} {idn : Idn A} {inv : Inv A} {grp : Group A},
  forall x y z : A, z + x = z + y -> x = y.
Proof.
  intros A opr idn inv grp x y z p.
  destruct grp as [pa pnl pnr pvl pvr].
  rewrite <- (pnl x). rewrite <- (pvl z). rewrite (pa (- z) z x).
  rewrite p. rewrite <- (pa (- z) z y). rewrite (pvl z). rewrite (pnl y).
  reflexivity. Qed.

Lemma inj_r : forall {A : Type}
  {opr : Opr A} {idn : Idn A} {inv : Inv A} {grp : Group A},
  forall x y z : A, x + z = y + z -> x = y.
Proof.
  intros A opr idn inv grp x y z p.
  destruct grp as [pa pnl pnr pvl pvr].
  rewrite <- (pnr x). rewrite <- (pvr z). rewrite <- (pa x z (- z)).
  rewrite p. rewrite (pa y z (- z)). rewrite (pvr z). rewrite (pnr y).
  reflexivity. Qed.

Theorem dis : forall {A : Type}
  {opr : Opr A} {idn : Idn A} {inv : Inv A} {grp : Group A},
  forall x y : A, - (y + x) = (- x) + (- y).
Proof.
  intros A opr idn inv grp x y.
  apply (inj_l (- (y + x)) ((- x) + (- y)) (y + x)).
  destruct grp as [pa pnl pnr pvl pvr].
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
  ass := _;
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

Module WeakestHierarchy.

Import WeakHierarchy.

Instance Z_Opr : Opr Z := fun x y : Z => x + y.

Instance Z_Semigroup : Semigroup Z := {
  ass := _;
}.
Proof.
  all: cbv [Classes.opr Z_Opr Classes.idn Z_Idn Classes.inv Z_Inv].
  - intros x y z. rewrite add_assoc. reflexivity. Qed.

Instance Z_Idn : Idn Z := 0.

Instance Z_Monoid : Monoid Z := {
  idn_l := _; idn_r := _;
}.
Proof.
  all: cbv [Classes.opr Z_Opr Classes.idn Z_Idn Classes.inv Z_Inv].
  - intros x. rewrite add_0_l. reflexivity.
  - intros x. rewrite add_0_r. reflexivity. Qed.

Instance Z_Inv : Inv Z := fun x => - x.

Instance Z_Group : Group Z := {
  inv_l := _; inv_r := _;
}.
Proof.
  all: cbv [Classes.opr Z_Opr Classes.idn Z_Idn Classes.inv Z_Inv].
  - intros x. rewrite add_opp_diag_l. reflexivity.
  - intros x. rewrite add_opp_diag_r. reflexivity. Qed.

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

End Output.

End Computations.

Extraction "example.ml" Classes Properties Instances Computations.
