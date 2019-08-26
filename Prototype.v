Require Props.

Import Props.

Definition relation (A : Type) : Type := A -> A -> Prop.

Definition Reflexive {A : Type} (R : relation A) : Prop :=
  forall x : A, R x x.

Definition Symmetric {A : Type} (R : relation A) : Prop :=
  forall x y : A, R x y -> R y x.

Definition Transitive {A : Type} (R : relation A) : Prop :=
  forall x y z : A, R x y -> R y z -> R x z.

Class Equivalence {A : Type} (R : relation A) : Prop := BuildEquivalence {
  Equivalence_Reflexive : Reflexive R;
  Equivalence_Symmetric : Symmetric R;
  Equivalence_Transitive : Transitive R;
}.

Class SemiGroup {G : Type} (e : relation G) (op : G -> G -> G) : Prop := {
  sg_setoid : Equivalence e;
  sg_ass : Props.assoc op;
}.

Theorem example (G : Type) (e : relation G) (op : G -> G -> G)
  {P : SemiGroup e op} :
  forall x y z : G, e (op (op x y) z) (op (op z y) x).
Proof. destruct P. Abort.

Module principle.
Class EquivOp A := eq_op : relation A.
Class SemiGroupOp A := sg_op : A -> A -> A.
Infix "==" := eq_op (at level 70) : type_scope.
Infix "&" := sg_op (at level 50, left associativity).

Class SemiGrouped {G : Type} (e : EquivOp G) (op : SemiGroupOp G) : Prop := {
  sg_setoid : Equivalence e;
  sg_ass : Props.assoc op;
}.

Theorem exampled (G : Type) (e : EquivOp G) (op : SemiGroupOp G)
  {P : SemiGrouped e op} :
  forall x y z : G, x & y & z == z & y & x.
Proof. cbv [EquivOp SemiGroupOp] in *. destruct P. Abort.

Class MonoidZeroOp A := mon_zero : A.
Notation "'#'" := mon_zero (at level 0).

Definition id_l {G} (E : EquivOp G) (op : G -> G -> G) (id : G) : Prop :=
  forall x : G, op id x == x.

Definition id_r {G} (E : EquivOp G) (op : G -> G -> G) (id : G) : Prop :=
  forall x : G, op x id == x.

Class Monoided {G : Type} (e : EquivOp G)
  (op : SemiGroupOp G) (z : MonoidZeroOp G) : Prop := {
  mon_sg : SemiGrouped e op;
  mon_l : id_l e op #;
  mon_r : id_r e op #;
}.

Theorem something (G : Type) (e : EquivOp G)
  (op : SemiGroupOp G) (z : MonoidZeroOp G)
  {P : Monoided e op z} :
  forall x : G, x & # == # & x.
Proof.
  intros x. destruct P. destruct mon_sg0. cbv [id_l id_r] in *.
  eapply Equivalence_Transitive.
  - cbv in *. apply mon_r0.
  - cbv in *. apply Equivalence_Symmetric. apply mon_l0. Qed.
End principle.

Module LeftModule.
Record members_of {A L : Type} : Type := MembersOf {
  add : A -> A -> A;
  zero : A;
  neg : A -> A;
  ladd : L -> L -> L;
  lzero : L;
  lneg : L -> L;
  lmul : L -> L -> L;
  lone : L;
  lsmul : L -> A -> A;
}.
Arguments members_of : clear implicits.
Arguments MembersOf {_ _}.
Notation "x 'ADD' '[' mo ']' y" := (add mo x y).
Notation "'ZERO' '[' mo ']'" := (zero mo).
Notation "'NEG' '[' mo ']' x" := (neg mo x).
Notation "x 'LADD' '[' mo ']' y" := (ladd mo x y).
Notation "'LZERO' '[' mo ']'" := (lzero mo).
Notation "'LNEG' '[' mo ']' x" := (lneg mo x).
Notation "x 'LMUL' '[' mo ']' y" := (lmul mo x y).
Notation "'LONE' '[' mo ']'" := (lone mo).
Notation "a 'LSMUL' '[' mo ']' x" := (lsmul mo a x).
Record laws_of {A L : Type} (mo : members_of A L) : Prop := LawsOf {
  add_assoc : Props.assoc (add mo);
  add_id_l : Props.id_l (add mo) (zero mo);
  add_id_r : Props.id_r (add mo) (zero mo);
  add_inv_l : Props.inv_l (add mo) (zero mo) (neg mo);
  add_inv_r : Props.inv_r (add mo) (zero mo) (neg mo);
  add_comm : Props.comm (add mo);
  ladd_assoc : Props.assoc (ladd mo);
  ladd_id_l : Props.id_l (ladd mo) (lzero mo);
  ladd_id_r : Props.id_r (ladd mo) (lzero mo);
  ladd_inv_l : Props.inv_l (ladd mo) (lzero mo) (lneg mo);
  ladd_inv_r : Props.inv_r (ladd mo) (lzero mo) (lneg mo);
  ladd_comm : Props.comm (ladd mo);
  lmul_assoc : Props.assoc (lmul mo);
  lmul_id_l : Props.id_l (lmul mo) (lone mo);
  lmul_id_r : Props.id_r (lmul mo) (lone mo);
  ldist_l : Props.dist_l (ladd mo) (lmul mo);
  ldist_r : Props.dist_r (ladd mo) (lmul mo);
  lsid : Props.lsid (lone mo) (lsmul mo);
  lsassoc : Props.lsassoc (lmul mo) (lsmul mo);
  lsdist_l : Props.lsdist_l (add mo) (lsmul mo);
  lsdist_r : Props.lsdist_r (add mo) (ladd mo) (lsmul mo);
}.
End LeftModule.

Module ModuleHom.
Record members_of {A L : Type} : Type := MembersOf {
  from : LeftModule.members_of A L;
  to : LeftModule.members_of A L;
  hom : A -> A;
}.
Arguments members_of : clear implicits.
Arguments MembersOf {_ _}.
Notation "'HOM' '[' mo ']' x" := (hom mo x) (at level 42).
Record laws_of {A L : Type} (mo : members_of A L) : Prop := LawsOf {
  hom_from : LeftModule.laws_of (from mo);
  hom_to : LeftModule.laws_of (to mo);
  hom_dist : forall x y : A,
    hom mo (LeftModule.add (from mo) x y) =
    LeftModule.add (from mo) (hom mo x) (hom mo y);
  hom_lscomm : forall (a : L) (x : A),
    hom mo (LeftModule.lsmul (from mo) a x) =
    LeftModule.lsmul (to mo) a (hom mo x);
}.
End ModuleHom.

Module DiffOp.
Record members_of {A L : Type} : Type := MembersOf {
  diff : nat -> ModuleHom.members_of A L;
}.
Arguments members_of : clear implicits.
Arguments MembersOf {_ _}.
Notation "'DIFF' '[' mo ']' x" := (diff mo x) (at level 42).
Record laws_of {A L : Type} (mo : members_of A L) : Prop := LawsOf {
  zero_diff : forall n : nat, ModuleHom.laws_of (diff mo n);
  zero_square : forall (n : nat) (x : A),
    ModuleHom.hom (diff mo n) (ModuleHom.hom (diff mo (S n)) x) =
    LeftModule.zero (ModuleHom.to (diff mo n));
}.
End DiffOp.

Module ChainComplex.
Record members_of {A L : Type} : Type := MembersOf {
  mod : nat -> LeftModule.members_of A L;
  dop : DiffOp.members_of A L;
}.
Arguments members_of : clear implicits.
Arguments MembersOf {_ _}.
Record laws_of {A L : Type} (mo : members_of A L) : Prop := LawsOf {
}.
End ChainComplex.
