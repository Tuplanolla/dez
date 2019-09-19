Set Warnings "-notation-overridden".

From Coq Require Extraction Setoid Morphisms Vector ZArith.

Module Export SetoidClass.

(** TODO Manage exports. *)
Export Setoid.
Import Morphisms.

Delimit Scope setoid_scope with setoid.

Open Scope setoid_scope.

Module Export ProperNotations.

Reserved Notation "R '==>' S" (at level 55, right associativity).
Notation "R '==>' S" := (respectful R S) : setoid_scope.

Reserved Notation "x '::>' R" (at level 60, right associativity).
Notation "x '::>' R" := (Proper R x) : setoid_scope.

End ProperNotations.

(* start snippet setoid *)
(** Equivalence relation.
    We do not use the abbreviation [eq],
    because it is reserved for propositional equality. *)
Class Eqv (A : Type) : Type := eqv : A -> A -> Prop.

Reserved Notation "x '==' y" (at level 70, no associativity).
Notation "x '==' y" := (eqv x y) : setoid_scope.

(** Setoid, equivalence relation.
    We do not use the standard library setoid,
    because it is not constrained by an operational class like [Eqv] and
    it is not itself a predicative class in [Prop]. *)
Class Setoid (A : Type) {eqv : Eqv A} : Prop := {
  reflexive : forall x : A, x == x;
  symmetric : forall x y : A, x == y -> y == x;
  transitive : forall x y z : A, x == y -> y == z -> x == z;
}.
(* end snippet setoid *)

Add Parametric Relation {A : Type} `{setoid : Setoid A} : A eqv
  reflexivity proved by reflexive
  symmetry proved by symmetric
  transitivity proved by transitive
  as eqv_relation.

End SetoidClass.

Module Export OrderClass.

Delimit Scope order_scope with order.

Open Scope order_scope.

(* start snippet order *)
(** Total order relation. *)
Class Ord (A : Type) : Type := ord : A -> A -> Prop.

Notation "x '<=' y" := (ord x y).

(** Total order, less-than-or-equal relation. *)
Class Order (A : Type) {eqv : Eqv A} {ord : Ord A} : Prop := {
  setoid :> Setoid A;
  antisymmetric : forall x y : A, x <= y -> y <= x -> x == y;
  transitive : forall x y z : A, x <= y -> y <= z -> x <= z;
  connex : forall x y : A, x <= y \/ y <= x;
}.
(* end snippet order *)

End OrderClass.

Module Export DecEqvTypeClass.

Delimit Scope eqdec_scope with eqdec.

Open Scope eqdec_scope.

(** Decidable equality, discreteness. *)
Class DecEqv (A : Type) {eqv : Eqv A} : Type :=
  deceqv : forall x y : A, {x == y} + {~ x == y}.

Reserved Notation "x '==?' y" (at level 70, no associativity).
Notation "x '==?' y" := (deceqv x y).

(** Decidable equality. *)
Class DecEqvType (A : Type) {eqv : Eqv A} {deceqv : DecEqv A} : Prop := {
  setoid :> Setoid A;
}.

End DecEqvTypeClass.

Module Export FiniteClass.

Delimit Scope finite_scope with finite.

Open Scope finite_scope.

(** Size, finite cardinality. *)
Class Size (A : Type) : Type := size : nat.

(** To size, injection into finite type. *)
Class ToSize (A : Type) {size : Size A} : Type := tosize : A -> Fin.t size.

(** From size, projection out of finite type. *)
Class FromSize (A : Type) {size : Size A} : Type := fromsize : Fin.t size -> A.

Reserved Notation "'#' x" (at level 35, no associativity).
Notation "'#' x" := (size x).

(** Finite size, bijection with the canonical finite type. *)
Class FiniteSize (A : Type) {eqv : Eqv A}
  {size : Size A} {tosize : ToSize A} {fromsize : FromSize A} : Prop := {
  setoid :> Setoid A;
  to_from : forall x : A, fromsize (tosize x) == x;
  from_to : forall a : Fin.t size, tosize (fromsize a) = a;
}.

End FiniteClass.

Module Export FiniteClass'.

Delimit Scope finite_scope with finite.

Open Scope finite_scope.

(** Enumeration, finite list. *)
Class Enum (A : Type) : Type := enum : list A.

(** Finite enumeration, finite list without duplicates. *)
Class FiniteEnum (A : Type) {eqv : Eqv A} {enum : Enum A} : Prop := {
  setoid :> Setoid A;
  covering : forall x : A, List.Exists (fun y : A => x == y) enum;
  disjoint : List.NoDup enum;
}.

End FiniteClass'.

Module Export SemigroupClass.

Delimit Scope semigroup_scope with semigroup.

Open Scope semigroup_scope.

(* start snippet semigroup *)
(** Operation.
    We do not use the abbreviation [op],
    because it is reserved for dual morphisms. *)
Class Opr (A : Type) : Type := opr : A -> A -> A.

Module AdditiveNotations.

Notation "x '+' y" := (opr x y) : semigroup_scope.

End AdditiveNotations.

Module MultiplicativeNotations.

Notation "x '*' y" := (opr x y) : semigroup_scope.

End MultiplicativeNotations.

Import AdditiveNotations.

(** Semigroup. *)
Class Semigroup (A : Type) {eqv : Eqv A} {opr : Opr A} : Prop := {
  setoid :> Setoid A;
  opr_proper : opr ::> eqv ==> eqv ==> eqv;
  opr_associative : forall x y z : A, (x + y) + z == x + (y + z);
}.
(* end snippet semigroup *)

Add Parametric Morphism {A : Type} `{semigroup : Semigroup A} : opr
  with signature eqv ==> eqv ==> eqv
  as eqv_opr_morphism.
Proof.
  intros x y p z w q. destruct semigroup as [_ r _]. apply r.
  - apply p.
  - apply q. Qed.

End SemigroupClass.

Module Export MonoidClass.

Delimit Scope monoid_scope with monoid.

Open Scope monoid_scope.

(* start snippet monoid *)
(** Identity.
    We do not use the abbreivation [id],
    because it is reserved for identity morphisms. *)
Class Idn (A : Type) : Type := idn : A.

Module AdditiveNotations.

Export SemigroupClass.AdditiveNotations.

Notation "'0'" := idn : monoid_scope.

End AdditiveNotations.

Module MultiplicativeNotations.

Export SemigroupClass.MultiplicativeNotations.

Notation "'1'" := idn : monoid_scope.

End MultiplicativeNotations.

Import AdditiveNotations.

(** Monoid, semigroup with identity. *)
Class Monoid (A : Type) {eqv : Eqv A} {opr : Opr A} {idn : Idn A} : Prop := {
  semigroup :> Semigroup A;
  left_identity : forall x : A, 0 + x == x;
  right_identity : forall x : A, x + 0 == x;
}.

(** Commutative monoid. *)
Class CommutativeMonoid (A : Type) {eqv : Eqv A}
  {opr : Opr A} {idn : Idn A} : Prop := {
  monoid :> Monoid A;
  opr_commutative : forall x y : A, x + y == y + x;
}.
(* end snippet monoid *)

End MonoidClass.

Module Export MetricClass.

Delimit Scope metric_scope with metric.

Open Scope metric_scope.

(** Distance. *)
Class Dist (S A : Type) : Type := dist : A -> A -> S.

Import AdditiveNotations.

(** Metric space. *)
Class Metric (S A : Type) {seqv : Eqv S} {sord : Ord S}
  {sopr : Opr S} {sidn : Idn S}
  {eqv : Eqv A} {dist : Dist S A} : Prop := {
  sorder :> Order S;
  scmonoid :> CommutativeMonoid S;
  dist_proper : dist ::> eqv ==> eqv ==> seqv;
  indiscernible : forall x y : A, dist x y == 0 <-> x == y;
  symmetric : forall x y : A, dist x y == dist y x;
  triangle : forall x y z : A, dist x z <= dist x y + dist y z;
}.

Add Parametric Morphism {S A : Type} `{metric : Metric S A} : dist
  with signature eqv ==> eqv ==> eqv
  as eqv_dist_morphism.
Proof.
  intros x y p z w q. destruct metric as [_ _ r _ _]. apply r.
  - apply p.
  - apply q. Qed.

End MetricClass.

Module Export GroupClass.

Delimit Scope group_scope with group.

Open Scope group_scope.

(** Inverse. *)
Class Inv (A : Type) : Type := inv : A -> A.

Module AdditiveNotations.

Export MonoidClass.AdditiveNotations.

Notation "'-' x" := (inv x) : group_scope.
Notation "x '-' y" := (opr x (inv y)) : group_scope.

End AdditiveNotations.

Module MultiplicativeNotations.

Export MonoidClass.MultiplicativeNotations.

Notation "'/' x" := (inv x) : group_scope.
Notation "x '/' y" := (opr x (inv y)) : group_scope.

End MultiplicativeNotations.

Import AdditiveNotations.

(** Group, monoid with inverse. *)
Class Group (A : Type) {eqv : Eqv A}
  {opr : Opr A} {idn : Idn A} {inv : Inv A} : Prop := {
  monoid :> Monoid A;
  inv_proper : inv ::> eqv ==> eqv;
  left_inverse : forall x : A, (- x) + x == 0;
  right_inverse : forall x : A, x + (- x) == 0;
}.

(** Abelian group, commutative group. *)
Class AbelianGroup (A : Type) {eqv : Eqv A}
  {opr : Opr A} {idn : Idn A} {inv : Inv A} : Prop := {
  group :> Group A;
  opr_commutative : forall x y : A, x + y == y + x;
}.

Add Parametric Morphism {A : Type} `{group : Group A} : inv
  with signature eqv ==> eqv
  as eqv_inv_morphism.
Proof.
  intros x y p. destruct group as [_ q _ _]. apply q. apply p. Qed.

End GroupClass.

Module Export GroupTheorems.

Export GroupClass.

Import AdditiveNotations ZArith Pos.

(** Positive repetition of operation. *)
Definition popr {A : Type} `{semigroup : Semigroup A}
  (n : positive) (x : A) : A :=
  iter_op opr n x.

(** Natural repetition of operation. *)
Definition nopr {A : Type} `{monoid : Monoid A} (n : N) (x : A) : A :=
  match n with
  | N0 => 0
  | Npos p => popr p x
  end.

(** Integer repetition of operation. *)
Definition zopr {A : Type} `{group : Group A} (n : Z) (x : A) : A :=
  match n with
  | Z0 => 0
  | Zpos p => popr p x
  | Zneg p => popr p (- x)
  end.

Module AdditiveNotations.

Export GroupClass.AdditiveNotations.

Notation "n '*' x" := (popr n x) : positive_scope.
Notation "n '*' x" := (nopr n x) : N_scope.
Notation "n '*' x" := (zopr n x) : Z_scope.

End AdditiveNotations.

Module MultiplicativeNotations.

Export GroupClass.MultiplicativeNotations.

Notation "x '^' n" := (popr n x) : positive_scope.
Notation "x '^' n" := (nopr n x) : N_scope.
Notation "x '^' n" := (zopr n x) : Z_scope.

End MultiplicativeNotations.

Import AdditiveNotations.

(* start snippet theorems *)
(** Inverse is involutive. *)
Theorem ivl : forall {A : Type} `{group : Group A},
  forall x : A, - (- x) == x.
Proof.
  intros A ? ? ? ? grp x.
  destruct grp as [[[ps pop pa] pnl pnr] pvp pvl pvr] eqn : pg.
  rewrite <- (pnr (- (- x))). rewrite <- (pvl x).
  rewrite <- (pa (- (- x)) (- x) x). rewrite (pvl (- x)). rewrite (pnl x).
  reflexivity. Qed.

(** Operation with the left argument fixed is injective. *)
Lemma inj_l : forall {A : Type} `{group : Group A},
  forall x y z : A, z + x == z + y -> x == y.
Proof.
  intros A ? ? ? ? grp x y z p.
  destruct grp as [[[ps pop pa] pnl pnr] pvp pvl pvr] eqn : pg.
  rewrite <- (pnl x). rewrite <- (pvl z). rewrite (pa (- z) z x).
  rewrite p. rewrite <- (pa (- z) z y). rewrite (pvl z). rewrite (pnl y).
  reflexivity. Qed.

(** Operation with the right argument fixed is injective. *)
Lemma inj_r : forall {A : Type} `{group : Group A},
  forall x y z : A, x + z == y + z -> x == y.
Proof.
  intros A ? ? ? ? grp x y z p.
  destruct grp as [[[ps pop pa] pnl pnr] pvp pvl pvr] eqn : pg.
  rewrite <- (pnr x). rewrite <- (pvr z). rewrite <- (pa x z (- z)).
  rewrite p. rewrite (pa y z (- z)). rewrite (pvr z). rewrite (pnr y).
  reflexivity. Qed.

(** Inverse distributes over operation. *)
Theorem dis : forall {A : Type} `{group : Group A},
  forall x y : A, - (x + y) == (- y) + (- x).
Proof.
  intros A ? ? ? ? grp x y.
  apply (inj_l (- (x + y)) ((- y) + (- x)) (x + y)).
  destruct grp as [[[ps pop pa] pnl pnr] pvp pvl pvr] eqn : pg.
  rewrite (pvr (x + y)). rewrite <- (pa (x + y) (- y) (- x)).
  rewrite (pa x y (- y)). rewrite (pvr y). rewrite (pnr x). rewrite (pvr x).
  reflexivity. Qed.

(** Inverse is absorbed by identity. *)
Theorem inv_0 : forall {A : Type} `{group : Group A},
  - 0 == 0.
Proof.
  intros A ? ? ? ? grp.
  destruct grp as [[[ps pop pa] pnl pnr] pvp pvl pvr] eqn : pg.
  rewrite <- (pnr (- 0)). rewrite (pvl 0).
  reflexivity. Qed.
(* end snippet theorems *)

Lemma iter_op_succ : forall {A : Type} `{setoid : Setoid A} (op : A -> A -> A),
 (forall x y z, op x (op y z) == op (op x y) z) ->
 forall p a, iter_op op (succ p) a == op a (iter_op op p a).
Proof.
  induction p; simpl; intros; try reflexivity.
  rewrite H. apply IHp. Qed.

(** Inverse distributes over integer repetition of operation. *)
(** TODO Assuming nonabelian groups here should suffice; investigate. *)
Theorem zdis : forall {A : Type} `{agroup : AbelianGroup A},
  forall (n : Z) (x : A), (n * (- x)%group)%Z == - (n * x)%Z.
Proof.
  intros A ? ? ? ? grp n x. induction n as [| p | p].
  - cbn. rewrite inv_0. reflexivity.
  - cbn. induction p as [| q r] using peano_ind.
    + cbn. reflexivity.
    + cbv [popr] in *.
      destruct grp as [[[[ps pop pa] pnl pnr] pvp pvl pvr] pc] eqn : pg.
      pose proof iter_op_succ opr as s. repeat rewrite s.
      rewrite r. rewrite dis. rewrite pc. reflexivity.
      intros y z w. rewrite pa. reflexivity.
      intros y z w. rewrite pa. reflexivity.
  - cbn. induction p as [| q r] using peano_ind.
    + cbn. reflexivity.
    + cbv [popr] in *.
      destruct grp as [[[[ps pop pa] pnl pnr] pvp pvl pvr] pc] eqn : pg.
      pose proof iter_op_succ opr as s. repeat rewrite s.
      rewrite r. rewrite dis. repeat rewrite ivl. rewrite pc. reflexivity.
      intros y z w. rewrite pa. reflexivity.
      intros y z w. rewrite pa. reflexivity. Qed.

End GroupTheorems.

Module Export RingClass.

Delimit Scope ring_scope with ring.

Open Scope ring_scope.

(* start snippet ring *)
(** Addition, additive operation. *)
Class Add (A : Type) : Type := add : A -> A -> A.

Notation "x '+' y" := (add x y) : ring_scope.

(** Zero, additive identity. *)
Class Zero (A : Type) : Type := zero : A.

Notation "'0'" := zero : ring_scope.

(** Negation, additive inverse. *)
Class Neg (A : Type) : Type := neg : A -> A.

Notation "'-' x" := (neg x) : ring_scope.
Notation "x '-' y" := (add x (neg y)) : ring_scope.

(** Multiplication, multiplicative operation. *)
Class Mul (A : Type) : Type := mul : A -> A -> A.

Notation "x '*' y" := (mul x y) : ring_scope.

(** One, multiplicative identity. *)
Class One (A : Type) : Type := one : A.

Notation "'1'" := one : ring_scope.

(** Ring, distributive additive abelian group and multiplicative monoid. *)
Class Ring (A : Type) {eqv : Eqv A}
  {add : Add A} {zero : Zero A} {neg : Neg A}
  {mul : Mul A} {one : One A} : Prop := {
  add_agroup :> AbelianGroup A (opr := add) (idn := zero) (inv := neg);
  mul_monoid :> Monoid A (opr := mul) (idn := one);
  left_distributive : forall x y z : A, x * (y + z) == x * y + x * z;
  right_distributive : forall x y z : A, (x + y) * z == x * z + y * z;
}.
(* end snippet ring *)

Add Parametric Morphism {A : Type} `{ring : Ring A} : add
  with signature eqv ==> eqv ==> eqv
  as eqv_add_morphism.
Proof.
  intros x y p z w q. destruct ring as [[[[[_ r _] _ _] _ _ _] _] _ _ _].
  apply r.
  - apply p.
  - apply q. Qed.

Add Parametric Morphism {A : Type} `{ring : Ring A} : neg
  with signature eqv ==> eqv
  as eqv_neg_morphism.
Proof.
  intros x y p. destruct ring as [[[[_ _ _] q _ _] _] _ _ _].
  apply q. apply p. Qed.

Add Parametric Morphism {A : Type} `{ring : Ring A} : mul
  with signature eqv ==> eqv ==> eqv
  as eqv_mul_morphism.
Proof.
  intros x y p z w q. destruct ring as [_ [[_ r _] _ _] _ _]. apply r.
  - apply p.
  - apply q. Qed.

(** Numeral notations do not work with type classes,
    so we need to construct this explicit tree of additions. *)
Definition two {A : Type} {add : Add A} {one : One A} : A := add one one.
Definition three {A : Type} {add : Add A} {one : One A} : A := add two one.
Definition four {A : Type} {add : Add A} {one : One A} : A := add two two.
Definition five {A : Type} {add : Add A} {one : One A} : A := add four one.
Definition six {A : Type} {add : Add A} {one : One A} : A := add four two.
Definition seven {A : Type} {add : Add A} {one : One A} : A := add four three.
Definition eight {A : Type} {add : Add A} {one : One A} : A := add four four.
Definition nine {A : Type} {add : Add A} {one : One A} : A := add eight one.

Notation "'2'" := two : ring_scope.
Notation "'3'" := three : ring_scope.
Notation "'4'" := four : ring_scope.
Notation "'5'" := five : ring_scope.
Notation "'6'" := six : ring_scope.
Notation "'7'" := seven : ring_scope.
Notation "'8'" := eight : ring_scope.
Notation "'9'" := nine : ring_scope.

End RingClass.

Module Export FieldClass.

Delimit Scope field_scope with field.

Open Scope field_scope.

(** Reciprocal, multiplicative inverse. *)
Class Recip (A : Type) : Type := recip : A -> A.

Notation "'/' x" := (recip x) : field_scope.
Notation "x '/' y" := (mul x (recip y)) : field_scope.

(** Field, ring with inverse. *)
Class Field (A : Type) {eqv : Eqv A}
  {add : Add A} {zero : Zero A} {neg : Neg A}
  {mul : Mul A} {one : One A} {recip : Recip A} : Prop := {
  ring :> Ring A;
  mul_group :> Group A (opr := mul) (idn := one) (inv := recip);
}.

Add Parametric Morphism {A : Type} `{field : Field A} : recip
  with signature eqv ==> eqv
  as eqv_recip_morphism.
Proof.
  intros x y p. destruct field as [_ [_ q _ _]]. apply q. apply p. Qed.

End FieldClass.

Module Export ModuleClass.

Delimit Scope module_scope with module.

Open Scope module_scope.

(* start snippet module *)
(** Left scalar multiplication, mixed multiplicative operation. *)
Class LSMul (S A : Type) : Type := lsmul : S -> A -> A.

Reserved Notation "a '<*' x" (at level 45, left associativity).
Notation "a '<*' x" := (lsmul a x) : module_scope.

(** Right scalar multiplication, mixed multiplicative operation. *)
Class RSMul (S A : Type) : Type := rsmul : S -> A -> A.

Reserved Notation "x '*>' a" (at level 45, left associativity).
Notation "x '*>' a" := (rsmul a x) : module_scope.

Import AdditiveNotations.

(** Left module over a ring, some sort of space. *)
Class LeftModule (S A : Type)
  {seqv : Eqv S} {sadd : Add S} {szero : Zero S} {sneg : Neg S}
  {smul : Mul S} {sone : One S}
  {eqv : Eqv A} {opr : Opr A} {idn : Idn A} {inv : Inv A}
  {lsmul : LSMul S A} : Prop := {
  left_sring :> Ring S (add := sadd) (zero := szero) (neg := sneg)
    (mul := smul) (one := sone);
  left_agroup :> AbelianGroup A (opr := opr) (idn := idn) (inv := inv);
  lsmul_proper : lsmul ::> seqv ==> eqv ==> eqv;
  lsmul_smul_compatible : forall (a b : S) (x : A),
    (a * b) <* x == a <* (b <* x);
  lsmul_identity : forall x : A, 1 <* x == x;
  lsmul_add_distributive : forall (a : S) (x y : A),
    a <* (x + y)%semigroup == (a <* x + a <* y)%semigroup;
  lsmul_sadd_distributive : forall (a b : S) (x : A),
    (a + b) <* x == (a <* x + b <* x)%semigroup;
}.

(** Right module over a ring, some sort of space. *)
Class RightModule (S A : Type)
  {seqv : Eqv S} {sadd : Add S} {szero : Zero S} {sneg : Neg S}
  {smul : Mul S} {sone : One S}
  {eqv : Eqv A} {opr : Opr A} {idn : Idn A} {inv : Inv A}
  {rsmul : RSMul S A} : Prop := {
  right_sring :> Ring S (add := sadd) (zero := szero) (neg := sneg)
    (mul := smul) (one := sone);
  right_agroup :> AbelianGroup A (opr := opr) (idn := idn) (inv := inv);
  rsmul_proper : rsmul ::> seqv ==> eqv ==> eqv;
  rsmul_smul_compatible : forall (a b : S) (x : A),
    x *> (a * b) == (x *> a) *> b;
  rsmul_identity : forall x : A, x *> 1 == x;
  rsmul_add_distributive : forall (a : S) (x y : A),
    (x + y)%semigroup *> a == (x *> a + y *> a)%semigroup;
  rsmul_sadd_distributive : forall (a b : S) (x : A),
    x *> (a + b) == (x *> a + x *> b)%semigroup;
}.

(** Heterogeneous bimodule over a ring. *)
Class Bimodule (LS RS A : Type)
  {lseqv : Eqv LS} {lsadd : Add LS} {lszero : Zero LS} {lsneg : Neg LS}
  {lsmul : Mul LS} {lsone : One LS}
  {rseqv : Eqv RS} {rsadd : Add RS} {rszero : Zero RS} {rsneg : Neg RS}
  {rsmul : Mul RS} {rsone : One RS}
  {eqv : Eqv A} {opr : Opr A} {idn : Idn A} {inv : Inv A}
  {lsmul : LSMul LS A} {rsmul : RSMul RS A} : Prop := {
  left_module :> LeftModule LS A;
  right_module :> RightModule RS A;
  smul_compatible : forall (a : LS) (b : RS) (x : A),
    (a <* x) *> b == a <* (x *> b);
}.

(** Homogeneous bimodule over a ring. *)
Class HomoBimodule (S A : Type)
  {seqv : Eqv S} {sadd : Add S} {szero : Zero S} {sneg : Neg S}
  {smul : Mul S} {sone : One S}
  {eqv : Eqv A} {opr : Opr A} {idn : Idn A} {inv : Inv A}
  {lsmul : LSMul S A} {lsmul : RSMul S A} : Prop := {
  bimodule :> Bimodule S S A;
}.
(* end snippet module *)

Add Parametric Morphism {S A : Type} `{lmod : LeftModule S A} : lsmul
  with signature eqv ==> eqv ==> eqv
  as eqv_lsmul_morphism.
Proof.
  intros x y p z w q. destruct lmod as [_ _ r _ _ _ _]. apply r.
  - apply p.
  - apply q. Qed.

Add Parametric Morphism {S A : Type} `{rmod : RightModule S A} : rsmul
  with signature eqv ==> eqv ==> eqv
  as eqv_rsmul_morphism.
Proof.
  intros x y p z w q. destruct rmod as [_ _ r _ _ _ _]. apply r.
  - apply p.
  - apply q. Qed.

End ModuleClass.

Module Export FinitelyFreeLeftModuleClass.

Delimit Scope ffmodule_scope with ffmodule.

Open Scope ffmodule_scope.

(* start snippet ffmodule *)
(** Basis, spanning linearly-independent generators. *)
Class Basis (D A : Type) : Type := basis : D -> A.

Import AdditiveNotations.

(** Finitely generated left module over a ring, left module with a basis. *)
Class FinitelyFreeLeftModule (D S A : Type) {deqv : Eqv D} {denum : Enum D}
  {seqv : Eqv S} {sadd : Add S} {szero : Zero S} {sneg : Neg S}
  {smul : Mul S} {sone : One S}
  {eqv : Eqv A} {opr : Opr A} {idn : Idn A} {inv : Inv A}
  {basis : Basis D A} {lsmul : LSMul S A} : Prop := {
  finite :> FiniteEnum D;
  lmodule :> LeftModule S A;
  span : forall x : A, exists coeffs : D -> S,
    let terms (d' : D) := coeffs d' <* basis d' in
    List.fold_right opr idn (List.map terms enum) == x;
  lindep : forall coeffs : D -> S,
    let terms (d' : D) := coeffs d' <* basis d' in
    List.fold_right opr idn (List.map terms enum) == 0%monoid ->
    List.Forall (fun a : S => a == 0) (List.map coeffs enum);
}.
(* end snippet ffmodule *)

End FinitelyFreeLeftModuleClass.

Module Instances.

Import ZArith Z.

Open Scope Z_scope.

(* start snippet z *)
Instance Z_Eqv : Eqv Z := fun x y : Z => x = y.

Instance Z_Setoid : Setoid Z := {}.
Proof.
  all: cbv [eqv].
  all: cbv [Z_Eqv].
  - apply eq_refl.
  - apply eq_sym.
  - apply eq_trans. Qed.

Instance Z_MulOpr : Opr Z := fun x y : Z => x * y.

Instance Z_MulSemigroup : Semigroup Z := {}.
Proof.
  all: cbv [eqv opr].
  all: cbv [Z_Eqv Z_MulOpr].
  - apply mul_wd.
  - intros x y z. rewrite mul_assoc. reflexivity. Qed.

Instance Z_MulIdn : Idn Z := 1.

Instance Z_MulMonoid : Monoid Z := {}.
Proof.
  all: cbv [eqv opr idn].
  all: cbv [Z_Eqv Z_MulOpr Z_MulIdn].
  - intros x. rewrite mul_1_l. reflexivity.
  - intros x. rewrite mul_1_r. reflexivity. Qed.

Instance Z_AddOpr : Opr Z := fun x y : Z => x + y.

Instance Z_AddSemigroup : Semigroup Z := {}.
Proof.
  all: cbv [eqv opr].
  all: cbv [Z_Eqv Z_AddOpr].
  - apply add_wd.
  - intros x y z. rewrite add_assoc. reflexivity. Qed.

Instance Z_AddIdn : Idn Z := 0.

Instance Z_AddMonoid : Monoid Z := {}.
Proof.
  all: cbv [eqv opr idn].
  all: cbv [Z_Eqv Z_AddOpr Z_AddIdn].
  - intros x. rewrite add_0_l. reflexivity.
  - intros x. rewrite add_0_r. reflexivity. Qed.

Instance Z_AddInv : Inv Z := fun x => - x.

Instance Z_AddGroup : Group Z := {}.
Proof.
  all: cbv [eqv opr idn inv].
  all: cbv [Z_Eqv Z_AddOpr Z_AddIdn Z_AddInv].
  - apply opp_wd.
  - intros x. rewrite add_opp_diag_l. reflexivity.
  - intros x. rewrite add_opp_diag_r. reflexivity. Qed.

Instance Z_AddAbelianGroup : AbelianGroup Z := {}.
Proof.
  all: cbv [eqv opr idn inv].
  all: cbv [Z_Eqv Z_AddOpr Z_AddIdn Z_AddInv].
  - intros x y. rewrite add_comm. reflexivity. Qed.

Instance Z_Add : Add Z := Z_AddOpr.
Instance Z_Zero : Zero Z := Z_AddIdn.
Instance Z_Neg : Neg Z := Z_AddInv.
Instance Z_Mul : Mul Z := Z_MulOpr.
Instance Z_One : One Z := Z_MulIdn.

Instance Z_Ring : Ring Z := {}.
Proof.
  - intros x y z. rewrite mul_add_distr_l. reflexivity.
  - intros x y z. rewrite mul_add_distr_r. reflexivity. Qed.
(* end snippet z *)

Import Vector VectorNotations.

Section VectorLemmas.

Import Eqdep_dec PeanoNat.

Lemma case_nil : forall {A : Type} (xs : t A O),
  xs = [].
Proof.
  intros A xs. set (P (xs : t A O) := xs = []).
  apply (case0 P). reflexivity. Qed.

Lemma case_cons : forall {A : Type} {n : nat} (xs : t A (S n)),
  exists (y : A) (ys : t A n), xs = y :: ys.
Proof.
  intros A n xs. set (P (n : nat) (xs : t A (S n)) :=
    exists (y : A) (ys : t A n), xs = y :: ys).
  apply (caseS P). intros y p ys. exists y, ys. reflexivity. Qed.

Lemma const_cons : forall {A : Type} {n : nat} (x : A),
  const x (S n) = x :: const x n.
Proof. intros A n x. reflexivity. Qed.

Lemma Forall_inversion : forall {A : Type} (f : A -> Prop)
  {n : nat} (x : A) (xs : t A n),
  Forall f (x :: xs) -> f x /\ Forall f xs.
Proof.
  intros A f n x xs p.
  inversion p as [| n' x' xs' phd ptl pn' [px' pxs']].
  apply (inj_pair2_eq_dec nat Nat.eq_dec) in pxs'.
  subst. split.
  - apply phd.
  - apply ptl. Qed.

Lemma Forall2_inversion : forall {A B : Type} (f : A -> B -> Prop)
  {n : nat} (x : A) (xs : t A n) (y : B) (ys : t B n),
  Forall2 f (x :: xs) (y :: ys) -> f x y /\ Forall2 f xs ys.
Proof.
  intros A B f n x xs y ys p.
  inversion p as [| n' x' y' xs' ys' phd ptl pn' [px' pxs'] [py' pys']].
  apply (inj_pair2_eq_dec nat Nat.eq_dec) in pxs'.
  apply (inj_pair2_eq_dec nat Nat.eq_dec) in pys'.
  subst. split.
  - apply phd.
  - apply ptl. Qed.

Lemma Forall_if : forall {A : Type} (P Q : A -> Prop)
  {n : nat} (xs : t A n),
  (forall x : A, P x -> Q x) -> (Forall P xs -> Forall Q xs).
Proof.
  intros A P Q n xs. induction n as [| n p].
  - intros f q.
    pose proof case_nil xs as pxs'.
    subst. apply Forall_nil.
  - intros f q.
    pose proof case_cons xs as pxs'. destruct pxs' as [x' [xs' pxs']].
    subst; rename x' into x, xs' into xs.
    apply Forall_inversion in q. destruct q as [qhd qtl].
    apply Forall_cons.
    + apply f. apply qhd.
    + apply p.
      * apply f.
      * apply qtl. Qed.

Lemma Forall_map : forall {A B : Type} (P : B -> Prop) (f : A -> B)
  {n : nat} (xs : t A n),
  Forall P (map f xs) <-> Forall (fun x : A => P (f x)) xs.
Proof.
  intros A B P f n xs. induction n as [| n p].
  - pose proof case_nil xs as pxs'.
    subst. split.
    + intros q. apply Forall_nil.
    + intros q. apply Forall_nil.
  - pose proof case_cons xs as pxs'. destruct pxs' as [x' [xs' pxs']].
    subst; rename x' into x, xs' into xs. split.
    + cbn. intros q.
      apply Forall_inversion in q. destruct q as [qhd qtl].
      apply Forall_cons.
      * apply qhd.
      * apply p. apply qtl.
    + cbn. intros q.
      apply Forall_inversion in q. destruct q as [qhd qtl].
      apply Forall_cons.
      * apply qhd.
      * apply p. apply qtl. Qed.

Lemma map_cons : forall {A B : Type} (f : A -> B)
  {n : nat} (x : A) (xs : t A n),
  map f (x :: xs) = f x :: map f xs.
Proof. intros A B f n x xs. reflexivity. Qed.

Lemma map_id : forall {A : Type} {n : nat} (xs : t A n),
  map (fun x : A => x) xs = xs.
Proof.
  intros A n xs. induction n as [| n p].
  - pose proof case_nil xs as pxs'.
    subst. reflexivity.
  - pose proof case_cons xs as pxs'. destruct pxs' as [x' [xs' pxs']].
    subst; rename x' into x, xs' into xs.
    cbn. f_equal. apply p. Qed.

Lemma map_map : forall {A B C : Type} (f : A -> B) (g : B -> C)
  {n : nat} (xs : t A n),
  map g (map f xs) = map (fun x : A => g (f x)) xs.
Proof.
  intros A B C f g n xs. induction n as [| n p].
  - pose proof case_nil xs as pxs'.
    subst. reflexivity.
  - pose proof case_cons xs as pxs'. destruct pxs' as [x' [xs' pxs']].
    subst; rename x' into x, xs' into xs.
    cbn. f_equal. apply p. Qed.

Lemma map2_cons : forall {A0 A1 B : Type} (f : A0 -> A1 -> B)
  {n : nat} (x0 : A0) (xs0 : t A0 n) (x1 : A1) (xs1 : t A1 n),
  map2 f (x0 :: xs0) (x1 :: xs1) = f x0 x1 :: map2 f xs0 xs1.
Proof. intros A0 A1 n x0 xs0 x1 xs1. reflexivity. Qed.

Lemma map2_id_0 : forall {A0 A1 B : Type}
  {n : nat} (xs0 : t A0 n) (xs1 : t A1 n),
  map2 (fun (x0 : A0) (x1 : A1) => x0) xs0 xs1 = xs0.
Proof.
  intros A0 A1 B n xs0 xs1. induction n as [| n p].
  - pose proof case_nil xs0 as pxs0'.
    pose proof case_nil xs1 as pxs1'.
    subst. reflexivity.
  - pose proof case_cons xs0 as pxs0'. destruct pxs0' as [x0' [xs0' pxs0']].
    pose proof case_cons xs1 as pxs1'. destruct pxs1' as [x1' [xs1' pxs1']].
    subst; rename x0' into x0, xs0' into xs0, x1' into x1, xs1' into xs1.
    cbn. f_equal. apply p. Qed.

Lemma map2_id_1 : forall {A0 A1 B : Type}
  {n : nat} (xs0 : t A0 n) (xs1 : t A1 n),
  map2 (fun (x0 : A0) (x1 : A1) => x1) xs0 xs1 = xs1.
Proof.
  intros A0 A1 B n xs0 xs1. induction n as [| n p].
  - pose proof case_nil xs0 as pxs0'.
    pose proof case_nil xs1 as pxs1'.
    subst. reflexivity.
  - pose proof case_cons xs0 as pxs0'. destruct pxs0' as [x0' [xs0' pxs0']].
    pose proof case_cons xs1 as pxs1'. destruct pxs1' as [x1' [xs1' pxs1']].
    subst; rename x0' into x0, xs0' into xs0, x1' into x1, xs1' into xs1.
    cbn. f_equal. apply p. Qed.

Lemma map2_fun_0 : forall {A0 A1 B : Type} (f0 : A0 -> B)
  {n : nat} (xs0 : t A0 n) (xs1 : t A1 n),
  map2 (fun (x0 : A0) (x1 : A1) => f0 x0) xs0 xs1 = map f0 xs0.
Proof.
  intros A0 A1 B f0 n xs0 xs1. induction n as [| n p].
  - pose proof case_nil xs0 as pxs0'.
    pose proof case_nil xs1 as pxs1'.
    subst. reflexivity.
  - pose proof case_cons xs0 as pxs0'. destruct pxs0' as [x0' [xs0' pxs0']].
    pose proof case_cons xs1 as pxs1'. destruct pxs1' as [x1' [xs1' pxs1']].
    subst; rename x0' into x0, xs0' into xs0, x1' into x1, xs1' into xs1.
    cbn. f_equal. apply p. Qed.

Lemma map2_fun_1 : forall {A0 A1 B : Type} (f1 : A1 -> B)
  {n : nat} (xs0 : t A0 n) (xs1 : t A1 n),
  map2 (fun (x0 : A0) (x1 : A1) => f1 x1) xs0 xs1 = map f1 xs1.
Proof.
  intros A0 A1 B f1 n xs0 xs1. induction n as [| n p].
  - pose proof case_nil xs0 as pxs0'.
    pose proof case_nil xs1 as pxs1'.
    subst. reflexivity.
  - pose proof case_cons xs0 as pxs0'. destruct pxs0' as [x0' [xs0' pxs0']].
    pose proof case_cons xs1 as pxs1'. destruct pxs1' as [x1' [xs1' pxs1']].
    subst; rename x0' into x0, xs0' into xs0, x1' into x1, xs1' into xs1.
    cbn. f_equal. apply p. Qed.

Lemma map2_map_0 : forall {A0 A1 B C : Type} (f0 : A0 -> B) (g : B -> A1 -> C)
  {n : nat} (xs0 : t A0 n) (xs1 : t A1 n),
  map2 g (map f0 xs0) xs1 =
  map2 (fun (x0 : A0) (x1 : A1) => g (f0 x0) x1) xs0 xs1.
Proof.
  intros A0 A1 B C f0 g n xs0 xs1. induction n as [| n p].
  - pose proof case_nil xs0 as pxs0'.
    pose proof case_nil xs1 as pxs1'.
    subst. reflexivity.
  - pose proof case_cons xs0 as pxs0'. destruct pxs0' as [x0' [xs0' pxs0']].
    pose proof case_cons xs1 as pxs1'. destruct pxs1' as [x1' [xs1' pxs1']].
    subst; rename x0' into x0, xs0' into xs0, x1' into x1, xs1' into xs1.
    cbn. f_equal. apply p. Qed.

Lemma map2_map_1 : forall {A0 A1 B C : Type} (f1 : A1 -> B) (g : A0 -> B -> C)
  {n : nat} (xs0 : t A0 n) (xs1 : t A1 n),
  map2 g xs0 (map f1 xs1) =
  map2 (fun (x0 : A0) (x1 : A1) => g x0 (f1 x1)) xs0 xs1.
Proof.
  intros A0 A1 B C f0 g n xs0 xs1. induction n as [| n p].
  - pose proof case_nil xs0 as pxs0'.
    pose proof case_nil xs1 as pxs1'.
    subst. reflexivity.
  - pose proof case_cons xs0 as pxs0'. destruct pxs0' as [x0' [xs0' pxs0']].
    pose proof case_cons xs1 as pxs1'. destruct pxs1' as [x1' [xs1' pxs1']].
    subst; rename x0' into x0, xs0' into xs0, x1' into x1, xs1' into xs1.
    cbn. f_equal. apply p. Qed.

Fixpoint nat_fold {A : Type} (f : nat -> A -> A) (z : A) (n : nat) : A :=
  match n with
  | O => z
  | S p => f p (nat_fold f z p)
  end.

Fixpoint fold {A B : Type} (f : A -> B -> B) (z : B)
  {n : nat} (xs : Vector.t A n) : B :=
  match xs with
  | @Vector.nil _ => z
  | @Vector.cons _ x _ xs => f x (fold f z xs)
  end.

Lemma fold_cons : forall {A B : Type} (f : A -> B -> B) (z : B)
  {n : nat} (x : A) (xs : t A n),
  fold f z (x :: xs) = f x (fold f z xs).
Proof. intros A B f z n x xs. reflexivity. Qed.

Lemma fold_map : forall {A B C : Type} (f : A -> B) (g : B -> C -> C) (z : C)
  {n : nat} (xs : t A n),
  fold g z (map f xs) = fold (fun x : A => g (f x)) z xs.
Proof.
  intros A B C f g z n xs. induction n as [| n p].
  - pose proof case_nil xs as pxs'.
    subst. reflexivity.
  - pose proof case_cons xs as pxs'. destruct pxs' as [x' [xs' pxs']].
    subst; rename x' into x, xs' into xs.
    cbn. f_equal. apply p. Qed.

Lemma fold_map2 : forall {A0 A1 B C : Type}
  (f : A0 -> A1 -> B) (g : B -> C -> C) (z : C)
  {n : nat} (xs0 : t A0 n) (xs1 : t A1 n),
  fold g z (map2 f xs0 xs1) =
  fold (fun p : A0 * A1 => g (f (fst p) (snd p))) z (map2 pair xs0 xs1).
Proof.
  intros A0 A1 B C f g z n xs0 xs1. induction n as [| n p].
  - pose proof case_nil xs0 as pxs0'.
    pose proof case_nil xs1 as pxs1'.
    subst. reflexivity.
  - pose proof case_cons xs0 as pxs0'. destruct pxs0' as [x0' [xs0' pxs0']].
    pose proof case_cons xs1 as pxs1'. destruct pxs1' as [x1' [xs1' pxs1']].
    subst; rename x0' into x0, xs0' into xs0, x1' into x1, xs1' into xs1.
    cbn. f_equal. apply p. Qed.

End VectorLemmas.

(** Vectors admit pointwise equality. *)
Lemma Forall2_eq : forall {A : Type} {n : nat} (xs ys : t A n),
  Forall2 (fun x y : A => x = y) xs ys <-> xs = ys.
Proof.
  intros A n. induction n as [| p q].
  - intros xs ys.
    pose proof case_nil xs as pxs.
    pose proof case_nil ys as pys.
    subst xs ys. split.
    + intros r. reflexivity.
    + intros r. apply Forall2_nil.
  - intros xxs yys.
    pose proof case_cons xxs as pxxs. destruct pxxs as [x [xs pxxs]].
    pose proof case_cons yys as pyys. destruct pyys as [y [ys pyys]].
    subst xxs yys. split.
    + intros r. apply Forall2_inversion in r. destruct r as [rhd rtl]. f_equal.
      * apply rhd.
      * apply q. apply rtl.
    + intros r.
      pose proof f_equal hd r as rhd. cbv in rhd.
      pose proof f_equal tl r as rtl. cbv in rtl.
      apply Forall2_cons.
      * apply rhd.
      * apply q. apply rtl. Qed.

(** Vectors admit pointwise equivalence. *)
(* start snippet zs *)
Instance VectorEqv {A : Type} `{setoid : Setoid A} {n : nat} : Eqv (t A n) :=
  Forall2 (fun x y : A => x == y).

Instance VectorSetoid {A : Type} `{setoid : Setoid A}
  {n : nat} : Setoid (t A n) := {}.
Proof.
  all: cbv [eqv].
  all: cbv [VectorEqv].
  - induction n as [| p q].
    + intros xs.
      pose proof case_nil xs as pxs.
      subst xs. apply Forall2_nil.
    + intros xxs.
      pose proof case_cons xxs as pxxs. destruct pxxs as [x [xs pxxs]].
      subst xxs. apply Forall2_cons.
      * reflexivity.
      * apply q.
  - induction n as [| p q].
    + intros xs ys r.
      pose proof case_nil xs as pxs.
      pose proof case_nil ys as pys.
      subst xs ys. apply Forall2_nil.
    + intros xxs yys r.
      pose proof case_cons xxs as pxxs. destruct pxxs as [x [xs pxxs]].
      pose proof case_cons yys as pyys. destruct pyys as [y [ys pyys]].
      subst xxs yys.
      apply Forall2_inversion in r. destruct r as [rhd rtl].
      apply Forall2_cons.
      * symmetry. apply rhd.
      * apply q. apply rtl.
  - induction n as [| p q].
    + intros xs ys zs r s.
      pose proof case_nil xs as pxs.
      pose proof case_nil ys as pys.
      pose proof case_nil zs as pzs.
      subst xs ys zs. apply Forall2_nil.
    + intros xxs yys zzs r s.
      pose proof case_cons xxs as pxxs. destruct pxxs as [x [xs pxxs]].
      pose proof case_cons yys as pyys. destruct pyys as [y [ys pyys]].
      pose proof case_cons zzs as pzzs. destruct pzzs as [z [zs pzzs]].
      subst xxs yys zzs.
      apply Forall2_inversion in r. destruct r as [rhd rtl].
      apply Forall2_inversion in s. destruct s as [shd stl].
      apply Forall2_cons.
      * etransitivity.
        -- apply rhd.
        -- apply shd.
      * eapply q.
        -- apply rtl.
        -- apply stl. Qed.

Instance Z_VectorOpr {n : nat} : Opr (t Z n) := map2 Z_AddOpr.

Instance Z_VectorSemigroup {n : nat} : Semigroup (t Z n) := {}.
Proof.
  all: cbv [eqv opr].
  all: cbv [VectorEqv Z_VectorOpr].
  all: cbv [eqv opr].
  all: cbv [Z_Eqv Z_AddOpr].
  all: set (P (x y : Z) := x = y).
  - intros xs ys p zs ws q.
    apply Forall2_eq in p.
    apply Forall2_eq in q.
    subst. apply Forall2_eq. reflexivity.
  - intros xs ys zs. apply Forall2_eq. induction n as [| p q].
    + pose proof case_nil xs as pxs.
      pose proof case_nil ys as pys.
      pose proof case_nil zs as pzs.
      subst. reflexivity.
    + rename xs into xxs, ys into yys, zs into zzs.
      pose proof case_cons xxs as pxxs. destruct pxxs as [x [xs pxxs]].
      pose proof case_cons yys as pyys. destruct pyys as [y [ys pyys]].
      pose proof case_cons zzs as pzzs. destruct pzzs as [z [zs pzzs]].
      subst. cbn -[add]. rewrite add_assoc. f_equal. apply q. Qed.

Instance Z_VectorIdn {n : nat} : Idn (t Z n) := const Z_AddIdn n.

Instance Z_VectorMonoid {n : nat} : Monoid (t Z n) := {}.
Proof.
  all: cbv [eqv opr idn].
  all: cbv [VectorEqv Z_VectorOpr Z_VectorIdn].
  all: cbv [eqv opr idn].
  all: cbv [Z_Eqv Z_AddOpr Z_AddIdn].
  all: set (P (x y : Z) := x = y).
  - intros xs. apply Forall2_eq. induction n as [| p q].
    + pose proof case_nil xs as pxs.
      subst. reflexivity.
    + rename xs into xxs.
      pose proof case_cons xxs as pxxs. destruct pxxs as [x [xs px]].
      subst. cbn -[add]. rewrite add_0_l. f_equal. apply q.
  - intros xs. apply Forall2_eq. induction n as [| p q].
    + pose proof case_nil xs as pxs.
      subst. reflexivity.
    + rename xs into xxs.
      pose proof case_cons xxs as pxxs. destruct pxxs as [x [xs px]].
      subst. cbn -[add]. rewrite add_0_r. f_equal. apply q. Qed.
(* end snippet zs *)

Instance Z_VectorInv {n : nat} : Inv (t Z n) := map Z_AddInv.

Instance Z_VectorGroup {n : nat} : Group (t Z n) := {}.
Proof.
  all: cbv [eqv opr idn inv].
  all: cbv [VectorEqv Z_VectorOpr Z_VectorIdn Z_VectorInv].
  all: cbv [Z_Eqv Z_AddOpr Z_AddIdn Z_AddInv].
  all: set (P (x y : Z) := x = y).
  - induction n as [| n p].
    + intros xs ys q.
      pose proof case_nil xs as pxs'.
      pose proof case_nil ys as pys'.
      subst. apply Forall2_nil.
    + intros xs ys q.
      pose proof case_cons xs as pxs'. destruct pxs' as [x' [xs' pxs']].
      pose proof case_cons ys as pys'. destruct pys' as [y' [ys' pys']].
      subst; rename x' into x, xs' into xs, y' into y, ys' into ys.
      apply Forall2_inversion in q. destruct q as [qhd qtl].
      cbn -[Z.add Z.zero Z.opp]. apply Forall2_cons.
      * apply opp_wd. apply qhd.
      * apply p. apply qtl.
  - induction n as [| n p].
    + intros xs.
      pose proof case_nil xs as pxs'.
      subst. apply Forall2_nil.
    + intros xs.
      pose proof case_cons xs as pxs'. destruct pxs' as [x' [xs' pxs']].
      subst; rename x' into x, xs' into xs.
      cbn -[Z.add Z.zero Z.opp]. apply Forall2_cons.
      * cbv -[Z.add Z.zero Z.opp]. rewrite add_opp_diag_l. reflexivity.
      * apply p.
  - induction n as [| n p].
    + intros xs.
      pose proof case_nil xs as pxs'.
      subst. apply Forall2_nil.
    + intros xs.
      pose proof case_cons xs as pxs'. destruct pxs' as [x' [xs' pxs']].
      subst; rename x' into x, xs' into xs.
      cbn -[Z.add Z.zero Z.opp]. apply Forall2_cons.
      * cbv -[Z.add Z.zero Z.opp]. rewrite add_opp_diag_r. reflexivity.
      * apply p. Qed.

Instance Z_VectorAbelianGroup {n : nat} : AbelianGroup (t Z n) := {}.
Proof.
  all: cbv [eqv opr idn inv].
  all: cbv [VectorEqv Z_VectorOpr Z_VectorIdn Z_VectorInv].
  all: cbv [eqv opr idn inv].
  all: cbv [Z_Eqv Z_AddOpr Z_AddIdn Z_AddInv].
  all: set (P (x y : Z) := x = y).
  - induction n as [| n p].
    + intros xs ys.
      pose proof case_nil xs as pxs'.
      pose proof case_nil ys as pys'.
      subst. apply Forall2_nil.
    + intros xs ys.
      pose proof case_cons xs as pxs'. destruct pxs' as [x' [xs' pxs']].
      pose proof case_cons ys as pys'. destruct pys' as [y' [ys' pys']].
      subst; rename x' into x, xs' into xs, y' into y, ys' into ys.
      cbn -[Z.add Z.zero Z.opp]. apply Forall2_cons.
      * cbn -[Z.add Z.zero Z.opp]. rewrite add_comm. reflexivity.
      * apply p. Qed.

Instance Z_LSMul {n : nat} : LSMul Z (t Z n) :=
  fun a : Z => map (fun x : Z => a * x).

Instance Z_LeftModule {n : nat} : LeftModule Z (t Z n) := {}.
Proof.
  all: cbv [eqv opr idn inv lsmul].
  all: cbv [VectorEqv Z_VectorOpr Z_VectorIdn Z_VectorInv Z_LSMul].
  all: cbv [eqv opr idn inv].
  all: cbv [Z_Eqv Z_AddOpr Z_AddIdn Z_AddInv Z_MulOpr Z_MulIdn].
  all: set (P (x y : Z) := x = y).
  - induction n as [| n p].
    + intros a b q xs ys r.
      pose proof case_nil xs as pxs'.
      pose proof case_nil ys as pys'.
      subst. apply Forall2_nil.
    + intros a b q xs ys r.
      pose proof case_cons xs as pxs'. destruct pxs' as [x' [xs' pxs']].
      pose proof case_cons ys as pys'. destruct pys' as [y' [ys' pys']].
      subst; rename x' into x, xs' into xs, y' into y, ys' into ys.
      apply Forall2_inversion in r. destruct r as [rhd rtl].
      cbn -[Z.mul Z.one]. apply Forall2_cons.
      * apply mul_wd.
        -- apply q.
        -- apply rhd.
      * apply p.
        -- apply q.
        -- apply rtl.
  - induction n as [| n p].
    + intros a b xs.
      pose proof case_nil xs as pxs'.
      subst. apply Forall2_nil.
    + intros a b xs.
      pose proof case_cons xs as pxs'. destruct pxs' as [x' [xs' pxs']].
      subst; rename x' into x, xs' into xs.
      cbn -[Z.mul Z.one]. apply Forall2_cons.
      * cbv -[Z.mul Z.one]. rewrite mul_assoc. reflexivity.
      * apply p.
  - induction n as [| n p].
    + intros xs.
      pose proof case_nil xs as pxs'.
      subst. apply Forall2_nil.
    + intros xs.
      pose proof case_cons xs as pxs'. destruct pxs' as [x' [xs' pxs']].
      subst; rename x' into x, xs' into xs.
      cbn -[Z.mul Z.one]. apply Forall2_cons.
      * cbv -[Z.mul Z.one]. rewrite mul_1_l. reflexivity.
      * apply p.
  - induction n as [| n p].
    + intros a xs ys.
      pose proof case_nil xs as pxs'.
      pose proof case_nil ys as pys'.
      subst. apply Forall2_nil.
    + intros a xs ys.
      pose proof case_cons xs as pxs'. destruct pxs' as [x' [xs' pxs']].
      pose proof case_cons ys as pys'. destruct pys' as [y' [ys' pys']].
      subst; rename x' into x, xs' into xs, y' into y, ys' into ys.
      cbn -[Z.add Z.zero Z.opp Z.mul Z.one]. apply Forall2_cons.
      * cbn -[Z.add Z.zero Z.opp Z.mul Z.one].
        rewrite mul_add_distr_l. reflexivity.
      * apply p.
  - induction n as [| n p].
    + intros a b xs.
      pose proof case_nil xs as pxs'.
      subst. apply Forall2_nil.
    + intros a b xs.
      pose proof case_cons xs as pxs'. destruct pxs' as [x' [xs' pxs']].
      subst; rename x' into x, xs' into xs.
      cbn -[Z.add Z.zero Z.opp Z.mul Z.one]. apply Forall2_cons.
      * cbn -[Z.add Z.zero Z.opp Z.mul Z.one].
        rewrite mul_add_distr_r. reflexivity.
      * apply p. Qed.

Instance Z_RSMul {n : nat} : RSMul Z (t Z n) :=
  fun a : Z => map (fun x : Z => x * a).

Instance Z_RightModule {n : nat} : RightModule Z (t Z n) := {}.
Proof.
  all: cbv [eqv opr idn inv rsmul].
  all: cbv [VectorEqv Z_VectorOpr Z_VectorIdn Z_VectorInv Z_RSMul].
  all: cbv [eqv opr idn inv].
  all: cbv [Z_Eqv Z_AddOpr Z_AddIdn Z_AddInv Z_MulOpr Z_MulIdn].
  all: set (P (x y : Z) := x = y).
  - induction n as [| n p].
    + intros a b q xs ys r.
      pose proof case_nil xs as pxs'.
      pose proof case_nil ys as pys'.
      subst. apply Forall2_nil.
    + intros a b q xs ys r.
      pose proof case_cons xs as pxs'. destruct pxs' as [x' [xs' pxs']].
      pose proof case_cons ys as pys'. destruct pys' as [y' [ys' pys']].
      subst; rename x' into x, xs' into xs, y' into y, ys' into ys.
      apply Forall2_inversion in r. destruct r as [rhd rtl].
      cbn -[Z.mul Z.one]. apply Forall2_cons.
      * apply mul_wd.
        -- apply rhd.
        -- apply q.
      * apply p.
        -- apply q.
        -- apply rtl.
  - induction n as [| n p].
    + intros a b xs.
      pose proof case_nil xs as pxs'.
      subst. apply Forall2_nil.
    + intros a b xs.
      pose proof case_cons xs as pxs'. destruct pxs' as [x' [xs' pxs']].
      subst; rename x' into x, xs' into xs.
      cbn -[Z.mul Z.one]. apply Forall2_cons.
      * cbv -[Z.mul Z.one]. rewrite mul_assoc. reflexivity.
      * apply p.
  - induction n as [| n p].
    + intros xs.
      pose proof case_nil xs as pxs'.
      subst. apply Forall2_nil.
    + intros xs.
      pose proof case_cons xs as pxs'. destruct pxs' as [x' [xs' pxs']].
      subst; rename x' into x, xs' into xs.
      cbn -[Z.mul Z.one]. apply Forall2_cons.
      * cbv -[Z.mul Z.one]. rewrite mul_1_r. reflexivity.
      * apply p.
  - induction n as [| n p].
    + intros a xs ys.
      pose proof case_nil xs as pxs'.
      pose proof case_nil ys as pys'.
      subst. apply Forall2_nil.
    + intros a xs ys.
      pose proof case_cons xs as pxs'. destruct pxs' as [x' [xs' pxs']].
      pose proof case_cons ys as pys'. destruct pys' as [y' [ys' pys']].
      subst; rename x' into x, xs' into xs, y' into y, ys' into ys.
      cbn -[Z.add Z.zero Z.opp Z.mul Z.one]. apply Forall2_cons.
      * cbn -[Z.add Z.zero Z.opp Z.mul Z.one].
        rewrite mul_add_distr_r. reflexivity.
      * apply p.
  - induction n as [| n p].
    + intros a b xs.
      pose proof case_nil xs as pxs'.
      subst. apply Forall2_nil.
    + intros a b xs.
      pose proof case_cons xs as pxs'. destruct pxs' as [x' [xs' pxs']].
      subst; rename x' into x, xs' into xs.
      cbn -[Z.add Z.zero Z.opp Z.mul Z.one]. apply Forall2_cons.
      * cbn -[Z.add Z.zero Z.opp Z.mul Z.one].
        rewrite mul_add_distr_l. reflexivity.
      * apply p. Qed.

Instance Z_Bimodule {n : nat} : Bimodule Z Z (t Z n) := {}.
Proof.
  all: cbv [eqv opr idn inv lsmul rsmul].
  all: cbv [VectorEqv Z_VectorOpr Z_VectorIdn Z_VectorInv Z_LSMul Z_RSMul].
  all: cbv [eqv opr idn inv].
  all: cbv [Z_Eqv Z_AddOpr Z_AddIdn Z_AddInv Z_MulOpr Z_MulIdn].
  all: set (P (x y : Z) := x = y).
  - induction n as [| n p].
    + intros a b xs.
      pose proof case_nil xs as pxs'.
      subst. apply Forall2_nil.
    + intros a b xs.
      pose proof case_cons xs as pxs'. destruct pxs' as [x' [xs' pxs']].
      subst; rename x' into x, xs' into xs.
      cbn -[Z.mul Z.one]. apply Forall2_cons.
      * cbv -[Z.mul Z.one]. rewrite mul_assoc. reflexivity.
      * apply p. Qed.

Instance Z_HomoBimodule {n : nat} : HomoBimodule Z (t Z n) := {}.

Section NatLemmas.

Import PeanoNat Nat.

Open Scope nat_scope.

Fixpoint range (n : nat) : Vector.t nat n :=
  match n with
  | O => []
  | S p => 0 :: map succ (range p)
  end.

Lemma range_le : forall n : nat,
  Forall (fun p : nat => p <= n) (range n).
Proof.
  intros n. induction n as [| n p].
  - apply Forall_nil.
  - cbn. apply Forall_cons.
    + apply le_0_l.
    + remember (range n) as ns eqn : pns'; clear pns'. apply Forall_map.
      apply (Forall_if (fun p : nat => p <= n) (fun p : nat => S p <= S n)).
      * intros q r. apply le_n_S. apply r.
      * apply p. Qed.

Fixpoint indicator (n i : nat) : Vector.t nat n :=
  match n with
  | O => []
  | S p => match i with
    | O => 1 :: const 0 p
    | S j => 0 :: indicator p j
    end
  end.

Lemma indicator_le : forall n i : nat,
  Forall (fun p : nat => p <= 1) (indicator n i).
Proof.
  intros n. induction n as [| n p]; intros i.
  - apply Forall_nil.
  - induction i as [| i q].
    + apply Forall_cons.
      * apply le_n.
      * clear p. induction n as [| n p].
        -- apply Forall_nil.
        -- cbn. apply Forall_cons.
          ++ apply le_0_l.
          ++ apply p.
    + cbn. apply Forall_cons.
      * apply le_0_l.
      * apply p. Qed.

End NatLemmas.

Instance Fin_Eqv {n : nat} : Eqv (Fin.t n) := fun x y : Fin.t n => x = y.

Fixpoint Fin_range (n : nat) : list (Fin.t n) :=
  match n with
  | O => List.nil
  | S p => List.cons Fin.F1 (List.map Fin.FS (Fin_range p))
  end.

Import PeanoNat.

Lemma Fin_inversion : forall x : Fin.t O,
  False.
Proof.
  intros x. set (P (x : Fin.t O) := False).
  apply (Fin.case0 P). apply x. Qed.

Lemma Fin_inversion_F1 : forall x : Fin.t (S O),
  x = Fin.F1.
Proof.
  intros x. set (P (x : Fin.t (S O)) := x = Fin.F1).
  apply (Fin.caseS' x P).
  - reflexivity.
  - intros p. inversion p. Qed.

Lemma Fin_inversion_FS : forall {n : nat} (x : Fin.t (S n)),
  x = Fin.F1 \/ exists y : Fin.t n, x = Fin.FS y.
Proof.
  intros n x. set (P (x : Fin.t (S n)) := x = Fin.F1 \/
    exists y : Fin.t n, x = Fin.FS y).
  apply (Fin.caseS' x P).
  - left. reflexivity.
  - intros p. right. exists p. reflexivity. Qed.

Instance Fin_Enum {n : nat} : Enum (Fin.t n) := Fin_range n.

Instance Fin_FiniteEnum {n : nat} : FiniteEnum (Fin.t n) := {}.
Proof. Admitted.

Instance Z_Basis {n : nat} : Basis (Fin.t n) (Vector.t Z n) :=
  let ns := map (indicator n) (range n) in
  nth (map (map of_nat) ns).

Compute basis Fin.F1 : t Z 3.
Compute basis (Fin.FS Fin.F1) : t Z 3.
Compute basis (Fin.FS (Fin.FS Fin.F1)) : t Z 3.

Compute List.fold_right Z_VectorOpr Z_VectorIdn
  (List.map basis enum) : t Z 3.
(* Compute List.fold_right RingClass.add RingClass.zero
  (List.map basis enum) : t Z 3. *)

End Instances.

(* start snippet computations *)
Module Computations.

Section Input.

Import Vector VectorNotations ZArith Z.

Open Scope Z_scope.

Definition meaning := 42.
Definition luck := [13; 31].
Definition fortune := 7.
Definition hope := [69; 96].

End Input.

Section Output.

Import AdditiveNotations.

Open Scope module_scope.
Open Scope ring_scope.
Open Scope group_scope.

Example fate := (meaning * fortune) <* hope - luck *> one.

End Output.

Section Test.

Import Vector VectorNotations ZArith Z.

Open Scope Z_scope.

Compute if Vector.eq_dec _ eqb _ _ fate [20273; 28193] then true else false.

End Test.

End Computations.
(* end snippet computations *)

Extraction "example.ml" Instances Computations.
