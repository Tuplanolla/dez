Set Warnings "-notation-overridden".

From Coq Require FunctionalExtensionality Setoid Morphisms ZArith.

Module Export SetoidClass.

Export Setoid Morphisms.

Delimit Scope setoid_scope with setoid.

Open Scope setoid_scope.

Module Export ProperNotations.

Reserved Notation "R '==>' S" (at level 55, right associativity).
Notation "R '==>' S" := (respectful R S) : setoid_scope.

Reserved Notation "x '::>' R" (at level 60, right associativity).
Notation "x '::>' R" := (Proper R x) : setoid_scope.

End ProperNotations.

(* start snippet setoid *)
Class Eqv (A : Type) : Type := eqv : A -> A -> Prop.

Reserved Notation "x '==' y" (at level 70, no associativity).
Notation "x '==' y" := (eqv x y) : setoid_scope.

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
Class Ord (A : Type) : Type := ord : A -> A -> Prop.

Notation "x '<=' y" := (ord x y).

Class Order (A : Type) {eqv : Eqv A} {ord : Ord A} : Prop := {
  setoid :> Setoid A;
  antisymmetric : forall x y : A, x <= y -> y <= x -> x == y;
  transitive : forall x y z : A, x <= y -> y <= z -> x <= z;
  connex : forall x y : A, x <= y \/ y <= x;
}.
(* end snippet order *)

End OrderClass.

Module Export SemigroupClass.

Delimit Scope semigroup_scope with semigroup.

Open Scope semigroup_scope.

(* start snippet semigroup *)
Class Opr (A : Type) : Type := opr : A -> A -> A.

Module AdditiveNotations.

Notation "x '+' y" := (opr x y) : semigroup_scope.

End AdditiveNotations.

Module MultiplicativeNotations.

Notation "x '*' y" := (opr x y) : semigroup_scope.

End MultiplicativeNotations.

Import AdditiveNotations.

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

Class Monoid (A : Type) {eqv : Eqv A} {opr : Opr A} {idn : Idn A} : Prop := {
  semigroup :> Semigroup A;
  left_identity : forall x : A, 0 + x == x;
  right_identity : forall x : A, x + 0 == x;
}.

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

(* start snippet metric *)
Class Dist (S A : Type) : Type := dist : A -> A -> S.

Import AdditiveNotations.

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
(* end snippet metric *)

Add Parametric Morphism {S A : Type} `{metric : Metric S A} : dist
  with signature eqv ==> eqv ==> eqv
  as eqv_dist_morphism.
Proof.
  intros x y p z w q. destruct metric as [_ _ r _ _]. apply r.
  - apply p.
  - apply q. Qed.

End MetricClass.

Module Export IsoClass.

Delimit Scope iso_scope with iso.

Open Scope iso_scope.

(* start snippet iso *)
Class Go (A B : Type) : Type := go : A -> B.
Class Come (A B : Type) : Type := come : B -> A.

Class Iso (A B : Type)
  {aeqv : Eqv A} {beqv : Eqv B} {ago : Go A B} {acome : Come A B} : Prop := {
  asetoid :> Setoid A;
  bsetoid :> Setoid B;
  go_proper : go ::> aeqv ==> beqv;
  come_proper : come ::> beqv ==> aeqv;
  ainverse : forall x : A, come (go x) == x;
  binverse : forall y : B, go (come y) == y;
}.
(* end snippet iso *)

Add Parametric Morphism {A B : Type} `{iso : Iso A B} : go
  with signature aeqv ==> beqv
  as eqv_go_morphism.
Proof.
  intros x y p. destruct iso as [_ _ q _ _ _]. apply q. apply p. Qed.

Add Parametric Morphism {A B : Type} `{iso : Iso A B} : come
  with signature beqv ==> aeqv
  as eqv_come_morphism.
Proof.
  intros x y p. destruct iso as [_ _ _ q _ _]. apply q. apply p. Qed.

End IsoClass.

Module Export GroupClass.

Delimit Scope group_scope with group.

Open Scope group_scope.

(* start snippet group *)
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

Class Group (A : Type) {eqv : Eqv A}
  {opr : Opr A} {idn : Idn A} {inv : Inv A} : Prop := {
  monoid :> Monoid A;
  inv_proper : inv ::> eqv ==> eqv;
  left_inverse : forall x : A, (- x) + x == 0;
  right_inverse : forall x : A, x + (- x) == 0;
}.

Class AbelianGroup (A : Type) {eqv : Eqv A}
  {opr : Opr A} {idn : Idn A} {inv : Inv A} : Prop := {
  group :> Group A;
  opr_commutative : forall x y : A, x + y == y + x;
}.
(* end snippet group *)

Add Parametric Morphism {A : Type} `{group : Group A} : inv
  with signature eqv ==> eqv
  as eqv_inv_morphism.
Proof.
  intros x y p. destruct group as [_ q _ _]. apply q. apply p. Qed.

End GroupClass.

Module Instances.

Import ZArith Z.

Open Scope Z_scope.

(* start snippet arith *)
Instance Z_Eqv : Eqv Z := fun x y : Z => x = y.

Instance Z_Setoid : Setoid Z := {}.
Proof.
  all: cbv [eqv].
  all: cbv [Z_Eqv].
  - intros x. reflexivity.
  - intros x y p. symmetry. apply p.
  - intros x y z p q. transitivity y.
    + apply p.
    + apply q. Qed.

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
(* end snippet arith *)

(* start snippet digression *)
Fixpoint Pos_even (x : positive) : bool :=
  match x with
  | xH => false
  | xO y => true
  | xI y => false
  end.

Instance N_Eqv : Eqv N := fun x y : N => x = y.

Instance N_Setoid : Setoid N := {}.
Proof.
  all: cbv [eqv].
  all: cbv [N_Eqv].
  - intros x. reflexivity.
  - intros x y p. symmetry. apply p.
  - intros x y z p q. transitivity y.
    + apply p.
    + apply q. Qed.

(** One isomorphism. *)

Instance Z_N_Go : Go Z N := fun x : Z =>
  match x with
  | Z0 => N0
  | Zpos y => Npos (2 * y)
  | Zneg y => Npos (2 * y - 1)
  end.

Instance Z_N_Come : Come Z N := fun x : N =>
  match x with
  | N0 => Z0
  | Npos y => if Pos_even y then
    Zpos (Pos.div2 y) else
    Zneg (Pos.div2 (1 + y))
  end.

Instance Z_N_Iso : Iso Z N := {}.
Proof.
  - intros x y p. rewrite p. reflexivity.
  - intros x y p. rewrite p. reflexivity.
  - intros [| y | y].
    + reflexivity.
    + reflexivity.
    + induction y as [z p | z p |].
      * reflexivity.
      * cbn. rewrite Pos.succ_pred_double. reflexivity.
      * reflexivity.
  - intros [| y].
    + reflexivity.
    + induction y as [z p | z p |].
      * cbn. rewrite Pos.pred_double_succ. reflexivity.
      * reflexivity.
      * reflexivity. Qed.

(** One flipped isomorphism. *)

Instance N_Z_Go : Go N Z := come.
Instance N_Z_Come : Come N Z := go.

Instance N_Z_Iso : Iso N Z := {}.
Proof.
  - intros x. apply binverse.
  - intros x. apply ainverse. Qed.

(** Another isomorphism. *)

Instance Z_N_Go' : Go Z N := fun x : Z =>
  match x with
  | Z0 => N0
  | Zpos y => Npos (2 * y - 1)
  | Zneg y => Npos (2 * y)
  end.

Instance Z_N_Come' : Come Z N := fun x : N =>
  match x with
  | N0 => Z0
  | Npos y => if Pos_even y then
    Zneg (Pos.div2 y) else
    Zpos (Pos.div2 (1 + y))
  end.

Instance Z_N_Iso' : Iso Z N := {}.
Proof.
  - intros x y p. rewrite p. reflexivity.
  - intros x y p. rewrite p. reflexivity.
  - intros [| y | y].
    + reflexivity.
    + induction y as [z p | z p |].
      * reflexivity.
      * cbn. rewrite Pos.succ_pred_double. reflexivity.
      * reflexivity.
    + reflexivity.
  - intros [| y].
    + reflexivity.
    + induction y as [z p | z p |].
      * cbn. rewrite Pos.pred_double_succ. reflexivity.
      * reflexivity.
      * reflexivity. Qed.

(** Another flipped isomorphism. *)

Instance N_Z_Go' : Go N Z := come.
Instance N_Z_Come' : Come N Z := go.

Instance N_Z_Iso' : Iso N Z := {}.
Proof.
  - intros x. apply binverse.
  - intros x. apply ainverse. Qed.

(** Concrete stuff. *)

Instance Z_N_Go_Eqv : Eqv (Go Z N) :=
  fun f g : Go Z N => forall x : Z, f x == g x.

Instance Z_N_Go_Setoid : Setoid (Go Z N) := {}.
Proof.
  - intros f x. reflexivity.
  - intros f g p x. rewrite p. reflexivity.
  - intros f g h p q x. rewrite p, q. reflexivity. Qed.

Instance N_Z_Go_Eqv : Eqv (Go N Z) :=
  fun f g : Go N Z => forall x : N, f x == g x.

Instance N_Z_Go_Setoid : Setoid (Go N Z) := {}.
Proof.
  - intros f x. reflexivity.
  - intros f g p x. rewrite p. reflexivity.
  - intros f g h p q x. rewrite p, q. reflexivity. Qed.

Instance Z_N_Go_Go : Go (Go Z N) (Go N Z) :=
  fun f : Go Z N => fun x : N => Z_N_Come (f (Z_N_Come x)).

Instance Z_N_Go_Come : Come (Go Z N) (Go N Z) :=
  fun f : Go N Z => fun x : Z => Z_N_Go (f (Z_N_Go x)).

Instance Z_N_Iso_Iso : Iso (Go Z N) (Go N Z) := {}.
Proof.
  - intros f g p x.
    unfold go, Z_N_Go_Go.
    rewrite p. reflexivity.
  - intros f g p x.
    unfold come, Z_N_Go_Come.
    rewrite p. reflexivity.
  - intros f x.
    unfold go, come, Z_N_Go_Go, Z_N_Go_Come.
    fold (go (Go := Z_N_Go) (Z_N_Come (f (Z_N_Come (Z_N_Go x))))).
    fold (come (Come := Z_N_Come) (f (Z_N_Come (Z_N_Go x)))).
    fold (come (Come := Z_N_Come) (Z_N_Go x)).
    fold (go (Go := Z_N_Go) x).
    rewrite binverse. hnf. f_equal. rewrite ainverse. reflexivity.
  - intros f x.
    unfold go, come, Z_N_Go_Go, Z_N_Go_Come.
    fold (come (Come := Z_N_Come) (Z_N_Go (f (Z_N_Go (Z_N_Come x))))).
    fold (go (Go := Z_N_Go) (f (Z_N_Go (Z_N_Come x)))).
    fold (go (Go := Z_N_Go) (Z_N_Come x)).
    fold (come (Come := Z_N_Come) x).
    rewrite ainverse. hnf. f_equal. rewrite binverse. reflexivity. Qed.

(** Abstract stuff. *)

(* Instance Go_Eqv {A B : Type}
  `{astd : Setoid A} `{bstd : Setoid B} : Eqv (Go A B) :=
  fun f g : Go A B => forall x : A, f x == g x.

Instance Go_Setoid {A B : Type}
  `{astd : Setoid A} `{bstd : Setoid B} : Setoid (Go A B) := {}.
Proof.
  - intros f x. reflexivity.
  - intros f g p x. rewrite (p x). reflexivity.
  - intros f g h p q x. rewrite (p x), (q x). reflexivity. Qed.

Instance Go2_Go {A B : Type} `{iso : Iso A B} : Go (Go A B) (Go B A) :=
  fun f : Go A B => fun x : B => come (f (come x)).

Instance Go2_Come {A B : Type} `{iso : Iso A B} : Come (Go A B) (Go B A) :=
  fun f : Go B A => fun x : A => go (f (go x)).

Instance Go2_Iso {A B : Type} `{iso : Iso A B} :
  Iso (Go A B) (Go B A) := {}.
Proof.
  - intros f g p x.
    destruct iso as [? ? ? q ? ?].
    pose proof p (come x) as r.
    pose proof q _ _ r as s.
    apply s.
  - intros f g p x.
    destruct iso as [? ? q ? ? ?].
    pose proof p (go x) as r.
    pose proof q _ _ r as s.
    apply s.
  - intros f x. hnf in f.
    assert (f ::> aeqv ==> beqv) as p by shelve.
    destruct iso as [? [? ? q] ? ? r s].
    pose proof r x as t.
    pose proof p _ _ t as u.
    epose proof s (f (come (go x))) as v.
    epose proof q _ _ _ v u as w.
    apply w.
  - intros f x. hnf in f.
    assert (f ::> beqv ==> aeqv) as p by shelve.
    destruct iso as [[? ? q] ? ? ? r s].
    pose proof s x as t.
    pose proof p _ _ t as u.
    epose proof r (f (come (go x))) as v.
    epose proof q _ _ _ v u as w.
    apply w. Admitted.

Instance Come_Eqv {A B : Type}
  `{astd : Setoid A} `{bstd : Setoid B} : Eqv (Come A B) :=
  fun f g : Come A B => forall x : B, f x == g x.

Instance Come_Setoid {A B : Type}
  `{astd : Setoid A} `{bstd : Setoid B} : Setoid (Come A B) := {}.
Proof.
  - intros f x. reflexivity.
  - intros f g p x. rewrite (p x). reflexivity.
  - intros f g h p q x. rewrite (p x), (q x). reflexivity. Qed.

Instance Come2_Go {A B : Type} `{iso : Iso A B} :
  Go (Come A B) (Come B A) :=
  fun f : Come A B => fun x : A => go (f (go x)).

Instance Come2_Come {A B : Type} `{iso : Iso A B} :
  Come (Come A B) (Come B A) :=
  fun f : Come B A => fun x : B => come (f (come x)).

Instance Come2_Iso {A B : Type} `{iso : Iso A B} :
  Iso (Come A B) (Come B A) := {}.
Proof. Admitted. *)

(** The problem is that [go] and [come] are decoupled,
    so respectfulness is not conserved. *)

Instance pair_Eqv {A B : Type}
  `{astd : Setoid A} `{bstd : Setoid B} : Eqv (A * B) := fun x y : A * B =>
  fst x == fst y /\ snd x == snd y.

Instance pair_Setoid {A B : Type}
  `{astd : Setoid A} `{bstd : Setoid B} : Setoid (A * B) := {}.
Proof.
  - intros [x0 x1]. split.
    + reflexivity.
    + reflexivity.
  - intros [x0 x1] [y0 y1] p. inversion p as [p0 p1]. split.
    + symmetry. apply p0.
    + symmetry. apply p1.
  - intros [x0 x1] [y0 y1] [z0 z1] p q.
    inversion p as [p0 p1]. inversion q as [q0 q1]. split.
    + etransitivity.
      * apply p0.
      * apply q0.
    + etransitivity.
      * apply p1.
      * apply q1. Qed.

Instance Iso_Eqv {A B : Type}
  `{astd : Setoid A} `{bstd : Setoid B} : Eqv (Go A B * Come A B) :=
  fun f g : Go A B * Come A B =>
  (forall x : A, fst f x == fst g x) /\
  (forall x : B, snd f x == snd g x).

Instance Go_Eqv {A B : Type}
  `{astd : Setoid A} `{bstd : Setoid B} : Eqv (Go A B) :=
  fun f g : Go A B => forall x : A, f x == g x.

Instance Go_Setoid {A B : Type}
  `{astd : Setoid A} `{bstd : Setoid B} : Setoid (Go A B) := {}.
Proof.
  - intros f x. reflexivity.
  - intros f g p x. rewrite (p x). reflexivity.
  - intros f g h p q x. rewrite (p x), (q x). reflexivity. Qed.

Instance Come_Eqv {A B : Type}
  `{astd : Setoid A} `{bstd : Setoid B} : Eqv (Come A B) :=
  fun f g : Come A B => forall x : B, f x == g x.

Instance Come_Setoid {A B : Type}
  `{astd : Setoid A} `{bstd : Setoid B} : Setoid (Come A B) := {}.
Proof.
  - intros f x. reflexivity.
  - intros f g p x. rewrite (p x). reflexivity.
  - intros f g h p q x. rewrite (p x), (q x). reflexivity. Qed.

Instance Iso_Setoid {A B : Type}
  `{astd : Setoid A} `{bstd : Setoid B} : Setoid (Go A B * Come A B) := {}.
Proof.
  - intros x. pose proof pair_Setoid (A := Go A B) (B := Come A B).
    reflexivity.
  - intros x y p. pose proof pair_Setoid (A := Go A B) (B := Come A B).
    symmetry. apply p.
  - intros x y z p q. pose proof pair_Setoid (A := Go A B) (B := Come A B).
    etransitivity.
    + apply p.
    + apply q. Qed.

Instance Iso_Go {A B : Type} `{iso : Iso A B} :
  Go (Go A B * Come A B) (Go B A * Come B A) :=
  fun f : Go A B * Come A B => (snd f, fst f).

Instance Iso_Come {A B : Type} `{iso : Iso A B} :
  Come (Go A B * Come A B) (Go B A * Come B A) :=
  fun f : Go B A * Come B A => (snd f, fst f).

Instance Iso_Iso {A B : Type} `{iso : Iso A B} :
  Iso (Go A B * Come A B) (Go B A * Come B A) := {}.
Proof.
  - intros f [g0 g1] [p0 p1]. split.
    + intros x. apply p1.
    + intros x. apply p0.
  - intros f [g0 g1] [p0 p1]. split.
    + intros x. apply p1.
    + intros x. apply p0.
  - intros f. split.
    + intros x. reflexivity.
    + intros x. reflexivity.
  - intros f. split.
    + intros x. reflexivity.
    + intros x. reflexivity. Qed.
(* end snippet digression *)

End Instances.

(* start snippet computations *)
Module Computations.

Section Input.

Import ZArith Z.

Open Scope Z_scope.

Definition meaning := 42.
Definition luck := 13.
Definition fortune := 7.

End Input.

Section Output.

Import AdditiveNotations.

Open Scope setoid_scope.
Open Scope order_scope.
Open Scope semigroup_scope.
Open Scope monoid_scope.
Open Scope metric_scope.
Open Scope group_scope.

Example fate := meaning + fortune - luck.

End Output.

Section Test.

Import ZArith Z.

Open Scope Z_scope.

Compute if eq_dec 36 fate then true else false.

End Test.

End Computations.
(* end snippet computations *)
