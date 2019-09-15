Set Warnings "-notation-overridden".

From Coq Require Eqdep_dec Extraction List Setoid Vector ZArith.

Module Classes.

Export Setoid Morphisms.

(* Definition relation (A : Type) : Type :=
  A -> A -> Prop.

Definition respectful {A B : Type}
  (R : relation A) (S : relation B) (f g : A -> B) : Prop :=
  forall x y : A, R x y -> S (f x) (g y).

Definition Proper {A : Type} (R : relation A) (x : A) : Prop :=
  R x x.

Reserved Notation "R '==>' S" (at level 55, right associativity).
Notation "R '==>' S" := (respectful R S) : signature_scope. *)
Reserved Notation "x '::>' R" (at level 60, right associativity).
Notation "x '::>' R" := (Proper R x) : signature_scope.

Class Eqv (A : Type) : Type := eqv : A -> A -> Prop.
Class Enum (A : Type) : Type := enum : list A.
Class SubInj (A B : Type) : Type := subinj : A -> B.
Class SubProp (A B : Type) (P : B -> Prop) : Type :=
  subprop : forall x : B, P x -> A.
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
Class Basis (D A : Type) : Type := basis : D -> A.
Class Diff (D S' A : Type) : Type := diff : forall n : nat, A -> A.

Delimit Scope group_scope with group.
Delimit Scope field_scope with field.
Delimit Scope module_scope with module.

Reserved Notation "x '==' y" (at level 70, no associativity).
Notation "x '==' y" := (eqv x y) : type_scope.
(* Reserved Notation "x '<:' y" (at level 70, no associativity).
Notation "x '<:' y" := (subinj x y) : type_scope. *)
Notation "x '+' y" := (add x y) : field_scope.
Notation "'0'" := zero : field_scope.
Notation "'-' x" := (neg x) : field_scope.
Notation "x '-' y" := (add x (neg y)) : field_scope.
Notation "x '*' y" := (mul x y) : field_scope.
Notation "'1'" := one : field_scope.
Notation "'/' x" := (recip x) : field_scope.
Notation "x '/' y" := (mul x (recip y)) : field_scope.
Reserved Notation "a '<*' x" (at level 45, left associativity).
Notation "a '<*' x" := (lsmul a x) : module_scope.
Reserved Notation "x '*>' a" (at level 45, left associativity).
Notation "x '*>' a" := (rsmul a x) : module_scope.
Reserved Notation "'ddd' x" (at level 35, right associativity).
Notation "'ddd' x" := (diff x) : module_scope.

Class Dec (A : Type) {eqv : Eqv A} : Type :=
  dec : forall x y : A, {x == y} + {~ x == y}.

Reserved Notation "x '==?' y" (at level 70, no associativity).
Notation "x '==?' y" := (dec x y) : type_scope.

Module AdditiveNotations.

Notation "x '+' y" := (opr x y) : group_scope.
Notation "'0'" := idn : group_scope.
Notation "'-' x" := (inv x) : group_scope.
Notation "x '-' y" := (opr x (inv y)) : group_scope.

End AdditiveNotations.

Module MultiplicativeNotations.

Notation "x '*' y" := (opr x y) : group_scope.
Notation "'1'" := idn : group_scope.
Notation "'/' x" := (inv x) : group_scope.
Notation "x '/' y" := (opr x (inv y)) : group_scope.

End MultiplicativeNotations.

Class Setoid (A : Type) {eqv : Eqv A} : Prop := {
  ref : forall x : A, x == x;
  sym : forall x y : A, x == y -> y == x;
  tra : forall x y z : A, x == y -> y == z -> x == z;
}.

Add Parametric Relation {A : Type} {eqv' : Eqv A}
  {std' : Setoid A} : A eqv
  reflexivity proved by ref
  symmetry proved by sym
  transitivity proved by tra
  as eqv_relation.

Module Setoidless.

(** In essence, [A] is equivalent to [{x : B | P x}]. *)
Class Subtype (A B : Type) (P : B -> Prop)
  {subinj : SubInj A B} {subprop : SubProp A B P} : Prop := {
  sub : forall (y : B) (p : P y), subinj (subprop y p) = y;
  scrub : forall Q : A -> Prop,
    (forall (y : B) (p : P y), Q (subprop y p)) -> forall x : A, Q x;
}.

Definition subprop_uncurried {A B : Type} {P : B -> Prop}
  {subprop : SubProp A B P} (p : {x : B | P x}) : A :=
  subprop (proj1_sig p) (proj2_sig p).

Definition subinj_unprojected {A B : Type} {P : B -> Prop}
  {subinj : SubInj A B} {subprop : SubProp A B P}
  {subtype : Subtype A B P}
  (x : A) : {x : B | P x} :=
  exist P (subinj x)
  match subtype with
  | {| sub := sub; scrub := scrub |} => scrub
    (fun x : A => P (subinj x)) (fun (y : B) (p : P y) =>
      eq_ind y P p (subinj (subprop y p)) (eq_sym (sub y p))) x
  end.
(* Proof.
  match goal with
  | A' : Type,
    B' : Type,
    P' : ?B' -> Prop,
    eqv' : Eqv ?B',
    subinj' : SubInj ?A' ?B',
    subprop' : SubProp ?A' ?B' ?P',
    subtype' : Subtype ?A' ?B' ?P',
    x' : ?A' |- _ => rename
      A' into A, B' into B, P' into P,
      eqv' into eqv, subinj' into subinj, subprop' into subprop,
      subtype' into subtype, x' into x
  end.
  hnf in *. destruct subtype as [sub scrub].
  exists (subinj x). generalize dependent x. eapply scrub.
  intros y p. pose proof (sub y p) as q.
  rewrite q. apply p. Defined. *)

End Setoidless.

Module Setoidful.

Open Scope signature_scope.

(** In essence, [A] is equivalent to [{x : B | P x}]. *)
Class Subtype (A B : Type) (P : B -> Prop)
  {eqv : Eqv B} {subinj : SubInj A B} {subprop : SubProp A B P} : Prop := {
  subsetoid :> Setoid B;
  sub_pro : P ::> eqv ==> Basics.flip Basics.impl;
  sub : forall (y : B) (p : P y), subinj (subprop y p) == y;
  scrub : forall Q : A -> Prop,
    (forall (y : B) (p : P y), Q (subprop y p)) -> forall x : A, Q x;
}.

Definition subprop_uncurried {A B : Type} {P : B -> Prop}
  {subprop : SubProp A B P} (p : {x : B | P x}) : A :=
  subprop (proj1_sig p) (proj2_sig p).

Definition subinj_unprojected {A B : Type} {P : B -> Prop}
  {eqv : Eqv B} {subinj : SubInj A B} {subprop : SubProp A B P}
  {subtype : Subtype A B P}
  (x : A) : {x : B | P x} :=
  exist (fun x : B => P x) (subinj x)
  match subtype with
  | {| sub_pro := pro; sub := sub; scrub := scrub |} => scrub
    (fun x : A => P (subinj x)) (fun (y : B) (p : P y) =>
      pro (subinj (subprop y p)) y (sub y p) p) x
  end.
(* Proof.
  match goal with
  | A' : Type,
    B' : Type,
    P' : ?B' -> Prop,
    eqv' : Eqv ?B',
    subinj' : SubInj ?A' ?B',
    subprop' : SubProp ?A' ?B' ?P',
    subtype' : Subtype ?A' ?B' ?P',
    x' : ?A' |- _ => rename
      A' into A, B' into B, P' into P,
      eqv' into eqv, subinj' into subinj, subprop' into subprop,
      subtype' into subtype, x' into x
  end.
  hnf in *. destruct subtype as [std pro sub scrub].
  exists (subinj x). generalize dependent x. eapply scrub.
  intros y p. pose proof (sub y p) as q.
  rewrite q. apply p. Defined. *)

End Setoidful.

Section ListDefinitions.

Import List PeanoNat.
Import ListNotations Nat.

Fixpoint count {A : Type} {eqv : Eqv A} {dec : Dec A}
  (x : A) (xs : list A) : nat :=
  match xs with
  | [] => O
  | y :: ys => if x ==? y then S (count x ys) else count x ys
  end.

Import AdditiveNotations.

Open Scope signature_scope.
Open Scope group_scope.

Definition folding {A : Type} {eqv : Eqv A} {opr : Opr A} {idn : Idn A}
  (xs : list A) : A := fold_right opr idn xs.

Definition summation {A : Type}
  {eqv : Eqv A} {add : Classes.Add A} {zero : Zero A} (xs : list A) : A :=
  fold_right add zero xs.

Definition product {A : Type}
  {eqv : Eqv A} {mul : Classes.Mul A} {one : One A} (xs : list A) : A :=
  fold_right mul one xs.

Global Instance nat_Eqv : Eqv nat := eq.
Global Instance nat_Dec : Dec nat := eq_dec.

End ListDefinitions.

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

Instance Fin_Dec {n : nat} : Dec (Fin.t n) := Fin.eq_dec.

Class FinCard (A : Type) : Type := fincard : nat.
Class FinTo (A : Type) {fincard : FinCard A} : Type :=
  finto : A -> Fin.t fincard.
Class FinFrom (A : Type) {fincard : FinCard A} : Type :=
  finfrom : Fin.t fincard -> A.
Class FiniteBi (A : Type) {eqv : Eqv A}
  {fincard : FinCard A} {finto : FinTo A} {finfrom : FinFrom A} : Prop := {
  fins_here : forall x : A, finfrom (finto x) == x;
  fins_there : forall a : Fin.t fincard, finto (finfrom a) = a;
}.

Class Finite' (A : Type) {eqv : Eqv A} {enum : Enum A} : Prop := {
  fin'_in : forall x : A, List.In x enum;
  fin'_nodup : List.NoDup enum;
}.

(** Every finite set is discrete,
    so you cannot have a finite set that is not also discrete,
    which suggests that these constraints are reasonable. *)
Class Finite (A : Type) {eqv : Eqv A} {dec : Dec A} {enum : Enum A} : Prop := {
  fin : forall x : A, count x enum == 1;
}.

Definition card {A : Type}
  {eqv : Eqv A} {dec : Dec A} {enum : Enum A} {fin : Finite A} : nat :=
  length enum.

Section Additive.

Import AdditiveNotations.

Open Scope signature_scope.
Open Scope group_scope.

Class Semigroup (A : Type) {eqv : Eqv A} {opr : Opr A} : Prop := {
  setoid :> Setoid A;
  opr_pro : opr ::> eqv ==> eqv ==> eqv;
  ass : forall x y z : A, (x + y) + z == x + (y + z);
}.

Import ZArith.

Fixpoint sgfold {A : Type} `{Semigroup A} (n : positive) (x : A) : A :=
  Pos.iter_op opr n x.

Class Monoid (A : Type) {eqv : Eqv A} {opr : Opr A} {idn : Idn A} : Prop := {
  semigroup :> Semigroup A;
  idn_l : forall x : A, 0 + x == x;
  idn_r : forall x : A, x + 0 == x;
}.

Fixpoint monfold {A : Type} `{Monoid A} (n : N) (x : A) : A :=
  match n with
  | N0 => 0
  | Npos p => sgfold p x
  end.

Class Group (A : Type) {eqv : Eqv A}
  {opr : Opr A} {idn : Idn A} {inv : Inv A} : Prop := {
  monoid :> Monoid A;
  inv_pro : inv ::> eqv ==> eqv;
  inv_l : forall x : A, (- x) + x == 0;
  inv_r : forall x : A, x + (- x) == 0;
}.

Fixpoint grpfold {A : Type} `{Group A} (n : Z) (x : A) : A :=
  match n with
  | Z0 => 0
  | Zpos p => sgfold p x
  | Zneg p => sgfold p (- x)
  end.

Class AbelianGroup (A : Type) {eqv : Eqv A}
  {opr : Opr A} {idn : Idn A} {inv : Inv A} : Prop := {
  group :> Group A;
  add_com : forall x y : A, x + y == y + x;
}.

End Additive.

Module AdditiveNotations'.

Export AdditiveNotations.

Reserved Notation "n 'P*' x" (at level 40, left associativity).
Notation "n 'P*' x" := (sgfold n x) : group_scope.

Reserved Notation "n 'N*' x" (at level 40, left associativity).
Notation "n 'N*' x" := (monfold n x) : group_scope.

Reserved Notation "n 'Z*' x" (at level 40, left associativity).
Notation "n 'Z*' x" := (grpfold n x) : group_scope.

End AdditiveNotations'.

Module MultiplicativeNotations'.

Export MultiplicativeNotations.

Reserved Notation "x 'P^' n" (at level 40, left associativity).
Notation "x 'P^' n" := (sgfold n x) : group_scope.

Reserved Notation "x 'N^' n" (at level 40, left associativity).
Notation "x 'N^' n" := (monfold n x) : group_scope.

Reserved Notation "x 'Z^' n" (at level 40, left associativity).
Notation "x 'Z^' n" := (grpfold n x) : group_scope.

End MultiplicativeNotations'.

Section Arbitrary.

Open Scope field_scope.

Class Ring (A : Type) {eqv : Eqv A} {add : Add A} {zero : Zero A} {neg : Neg A}
  {mul : Mul A} {one : One A} : Prop := {
  add_agroup :> AbelianGroup A (opr := add) (idn := zero) (inv := neg);
  mul_monoid :> Monoid A (opr := mul) (idn := one);
  dis_l : forall x y z : A, x * (y + z) == x * y + x * z;
  dis_r : forall x y z : A, (x + y) * z == x * z + y * z;
}.

Class Field (A : Type) {eqv : Eqv A} {add : Add A} {zero : Zero A} {neg : Neg A}
  {mul : Mul A} {one : One A} {recip : Recip A} : Prop := {
  fadd_agroup :> AbelianGroup A (opr := add) (idn := zero) (inv := neg);
  fmul_group :> Group A (opr := mul) (idn := one) (inv := recip);
  fdis_l : forall x y z : A, x * (y + z) == x * y + x * z;
  fdis_r : forall x y z : A, (x + y) * z == x * z + y * z;
}.

End Arbitrary.

Section Additive.

Import AdditiveNotations.

Open Scope signature_scope.
Open Scope module_scope.
Open Scope field_scope.
Open Scope group_scope.

Class LeftModule (S A : Type)
  {seqv : Eqv S} {sadd : Add S} {szero : Zero S} {sneg : Neg S}
  {smul : Mul S} {sone : One S}
  {eqv : Eqv A} {opr : Opr A} {idn : Idn A} {inv : Inv A}
  {lsmul : LSMul S A} : Prop := {
  lsring :> Ring S (add := sadd) (zero := szero) (neg := sneg)
    (mul := smul) (one := sone);
  lagroup :> AbelianGroup A (opr := opr) (idn := idn) (inv := inv);
  lsmul_pro : lsmul ::> seqv ==> eqv ==> eqv;
  lsmul_smul_cpt : forall (a b : S) (x : A), (a * b) <* x == a <* (b <* x);
  lsmul_idn : forall x : A, 1 <* x == x;
  lsmul_add_dis : forall (a : S) (x y : A), a <* (x + y) == a <* x + a <* y;
  lsmul_sadd_dis : forall (a b : S) (x : A),
    (a + b)%field <* x == a <* x + b <* x;
}.

Class RightModule (S A : Type)
  {seqv : Eqv S} {sadd : Add S} {szero : Zero S} {sneg : Neg S}
  {smul : Mul S} {sone : One S}
  {eqv : Eqv A} {opr : Opr A} {idn : Idn A} {inv : Inv A}
  {rsmul : RSMul S A} : Prop := {
  rsring :> Ring S (add := sadd) (zero := szero) (neg := sneg)
    (mul := smul) (one := sone);
  ragroup :> AbelianGroup A (opr := opr) (idn := idn) (inv := inv);
  rsmul_pro : rsmul ::> seqv ==> eqv ==> eqv;
  rsmul_smul_cpt : forall (a b : S) (x : A), x *> (a * b) == (x *> a) *> b;
  rsmul_idn : forall x : A, x *> 1 == x;
  rsmul_add_dis : forall (a : S) (x y : A), (x + y) *> a == x *> a + y *> a;
  rsmul_sadd_dis : forall (a b : S) (x : A),
    x *> (a + b)%field == x *> a + x *> b;
}.

Class Bimodule (LS RS A : Type)
  {lseqv : Eqv LS} {lsadd : Add LS} {lszero : Zero LS} {lsneg : Neg LS}
  {lsmul : Mul LS} {lsone : One LS}
  {rseqv : Eqv RS} {rsadd : Add RS} {rszero : Zero RS} {rsneg : Neg RS}
  {rsmul : Mul RS} {rsone : One RS}
  {eqv : Eqv A} {opr : Opr A} {idn : Idn A} {inv : Inv A}
  {lsmul : LSMul LS A} {rsmul : RSMul RS A} : Prop := {
  lmodule :> LeftModule LS A;
  rmodule :> RightModule RS A;
  smul_cpt : forall (a : LS) (b : RS) (x : A), (a <* x) *> b == a <* (x *> b);
}.

Class HomoBimodule (S A : Type)
  {seqv : Eqv S} {sadd : Add S} {szero : Zero S} {sneg : Neg S}
  {smul : Mul S} {sone : One S}
  {eqv : Eqv A} {opr : Opr A} {idn : Idn A} {inv : Inv A}
  {lsmul : LSMul S A} {lsmul : RSMul S A} : Prop := {
  bimodule :> Bimodule S S A;
}.

Class FinitelyFreeLeftModule (D S A : Type)
  {deqv : Eqv D} {denum : Enum D} {ddec : Dec D}
  {seqv : Eqv S} {sadd : Add S} {szero : Zero S} {sneg : Neg S}
  {smul : Mul S} {sone : One S}
  {eqv : Eqv A} {opr : Opr A} {idn : Idn A} {inv : Inv A}
  {lsmul : LSMul S A} {basis : Basis D A} : Prop := {
  finite :> Finite D;
  module :> LeftModule S A;
  (** In words, this says "if you pick any point,
      I can find coefficients for the basis,
      such that the linear combination equals your point".
      In pseudocode, this says
      [forall x : A, exists cs : S ^ dim,
      x == cs_1 <* basis_1 + cs_2 <* basis_2 + ... + cs_dim <* basis_dim]. *)
  basis_span : forall x : A, exists coeffs : D -> S,
    let terms (d' : D) := coeffs d' <* basis d' in
    folding (List.map terms enum) == x;
  (** In words, this says "if you can find any coefficients of the basis,
      such that the linear combination is zero,
      I can prove that all your coefficients are zero".
      In pseudocode, this says
      [forall (cs : S ^ dim),
      cs_1 <* basis_1 + cs_2 <* basis_2 + ... + cs_dim <* basis_dim = 0 ->
      cs_1 = 0 /\ cs_2 = 0 /\ ... /\ cs_dim = 0]. *)
  basis_lind : forall coeffs : D -> S,
    let terms (d' : D) := coeffs d' <* basis d' in
    folding (List.map terms enum) == 0 ->
    List.Forall (fun a : S => a == 0%field) (List.map coeffs enum);
}.

Class FinitelyFreeGradedLeftModule (G D S A : Type)
  {deqv : Eqv D} {denum : Enum D} {ddec : Dec D}
  {seqv : Eqv S} {sadd : Add S} {szero : Zero S} {sneg : Neg S}
  {smul : Mul S} {sone : One S}
  {eqv : Eqv A} {opr : Opr A} {idn : Idn A} {inv : Inv A}
  {lsmul : LSMul S A} {basis : Basis D A} : Prop := {
  family : G -> FinitelyFreeLeftModule D S A;
}.

Class ChainComplex (D S' A : Type) `{Diff D S' A}
  `{FinitelyFreeGradedLeftModule nat D S' A} : Prop := {
  zero_square : forall (n : nat) (x : A), diff n (diff (S n) x) == 0;
}.

(** TODO Wedge product, simplices, reductions, homology. *)

Section Analysis.

(*
Definition ClassicalCauchy {A : Type} {d : Metric A} (x : nat -> A) : Prop :=
  forall k : nat, exists n : nat,
  forall p q : nat, n <= p -> n <= q ->
  d (x p) (x q) <= 1 / 2 ^ k.

Definition ConstructiveCauchy {A : Type} {d : Metric A} (x : nat -> A) : Prop :=
  exists n : nat -> nat, forall k : nat,
  forall p q : nat, n k <= p -> n k <= q ->
  d (x p) (x q) <= 1 / 2 ^ k.
*)

Local Parameter embed : forall {S : Type}, nat -> S.
Local Notation "'!' n" := (embed n) (at level 35, no associativity).
Local Parameter power : forall {S : Type}, S -> nat -> S.
Local Notation "x '^' n" := (power x n).
Local Parameter division : forall {S : Type}, S -> S -> S.
Local Notation "x '/' y" := (division x y).
Local Parameter lessthanorequal : forall {S : Type}, S -> S -> Prop.
Local Notation "x '<<' y" := (lessthanorequal x y) (at level 70, no associativity).

Class Cmp (A : Type) : Type := compare : A -> A -> Prop.
Notation "x '<=' y" := (compare x y).
Class Order (A : Type) {eqv : Eqv A} {cmp : Cmp A} : Prop := {
  toset :> Setoid A;
  toanti : forall x y : A, x <= y -> y <= x -> x == y;
  totrans : forall x y z : A, x <= y -> y <= z -> x <= z;
  toconn : forall x y : A, x <= y \/ y <= x;
}.
Class Dist (S A : Type) : Type := dist : A -> A -> S.
Class Metric (S A : Type) {seqv : Eqv S} {scmp : Cmp S} {sord : Order S}
  {sopr : Opr S} {sidn : Idn S} {eqv : Eqv A} {dist : Dist S A} : Prop := {
  smonoid :> Monoid S;
  sorder :> Order S;
  mind : forall x y : A, dist x y == 0 <-> x == y;
  msym : forall x y : A, dist x y == dist y x;
  mtri : forall x y z : A, dist x z <= dist x y + dist y z;
}.

Definition Subsequence {A : Type} (x : nat -> A) (n : nat) : Fin.t n -> A :=
  fun a : Fin.t n => x (proj1_sig (Fin.to_nat a)).

Instance nat_Cmp : Cmp nat := Nat.le.

Import ZArith.

Definition Limit {S A : Type} `{Metric S A} (x : nat -> A) (y : A) : Prop :=
  forall k : nat, exists n : nat,
  forall p : nat, n <= p ->
  monfold (N.of_nat (2 ^ k)) (dist (x p) y) << !1.

Parameter FinSum : forall {A : Type} {n : nat} (x : Fin.t n -> A), A.

Definition InfSum {S A : Type} `{Metric S A} (x : nat -> A) (y : A) : Prop :=
  Limit (fun n : nat => FinSum (Subsequence x n)) y.

(** TODO Use operationally injective, propositionally countable [D]. *)
Class CountablyFreeLeftModule (S A : Type)
  `{Metric S A}
  {seqv : Eqv S} {sadd : Add S} {szero : Zero S} {sneg : Neg S}
  {smul : Mul S} {sone : One S}
  {eqv : Eqv A} {opr : Opr A} {idn : Idn A} {inv : Inv A}
  {lsmul : LSMul S A} {basis : Basis nat A} : Prop := {
  wmodule :> LeftModule S A;
  (** In words, this says "if you pick any point,
      I can find coefficients for the basis,
      such that the linear combination converges and equals your point".
      In pseudocode, this says
      [forall x : A, exists cs : S ^ omega,
      x == cs_1 <* basis_1 + cs_2 <* basis_2 + ...]. *)
  wbasis_span : let D := nat in
    forall x : A, exists coeffs : D -> S,
    let terms (d : D) := coeffs d <* basis d in
    InfSum terms x;
  (** In words, this says "if you can find any coefficients
      for any finite subset of the basis,
      such that the linear combination is zero,
      I can prove that all your coefficients are zero".
      In pseudocode, this says
      [forall (subdim : nat) (subbasis <: basis) (cs : S ^ subdim),
      cs_1 <* basis_1 + cs_2 <* basis_2 + ... + cs_subdim <* basis_subdim = 0 ->
      cs_1 = 0 /\ cs_2 = 0 /\ ... /\ cs_subdim = 0]. *)
  wbasis_lind : let D := nat in
    forall {deqv : Eqv D} {F : Type} {P : D -> Prop}
    {feqv : Eqv F} {fsubinj : SubInj F D} {fsubprop : SubProp F D P}
    {fstd : Setoidful.Subtype F D P}
    {fenum : Enum F} {fdec : Dec F} {ffin : Finite F},
    let subbasis (d : F) := basis (subinj d) in
    forall subcoeffs : F -> S,
    let subterms (d : F) := subcoeffs d <* subbasis d in
    folding (List.map subterms enum) == 0 ->
    List.Forall (fun a : S => a == 0%field) (List.map subcoeffs enum);
}.

End Analysis.

End Additive.

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
  destruct rng' as [[[[[_ add_pro _] _ _] _ _ _] _] _ _ _].
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
  destruct rng' as [[[[_ _ _] neg_pro _ _] _] _ _ _].
  cbv in neg_pro. apply neg_pro. apply p. Qed.

Add Parametric Morphism {A : Type} {eqv' : Eqv A}
  {add' : Add A} {zero' : Zero A} {neg' : Neg A}
  {mul' : Mul A} {one' : One A} {rng' : Ring A} : mul
  with signature eqv ==> eqv ==> eqv
  as eqv_mul_morphism.
Proof.
  intros x y p z w q.
  destruct rng' as [_ [[_ mul_pro _] _ _] _ _].
  cbv in mul_pro. apply mul_pro.
  - apply p.
  - apply q. Qed.

Add Parametric Morphism {S A : Type}
  {seqv' : Eqv S} {sadd' : Add S} {szero' : Zero S} {sneg' : Neg S}
  {smul' : Mul S} {sone' : One S}
  {eqv' : Eqv A} {opr' : Opr A} {idn' : Idn A} {inv' : Inv A}
  {lsmul' : LSMul S A} {lmod' : LeftModule S A} : lsmul
  with signature eqv ==> eqv ==> eqv
  as eqv_lsmul_morphism.
Proof.
  intros x y p z w q.
  destruct lmod' as [_ _ lsmul_pro _ _ _ _].
  cbv in lsmul_pro. apply lsmul_pro.
  - apply p.
  - apply q. Qed.

Add Parametric Morphism {S A : Type}
  {seqv' : Eqv S} {sadd' : Add S} {szero' : Zero S} {sneg' : Neg S}
  {smul' : Mul S} {sone' : One S}
  {eqv' : Eqv A} {opr' : Opr A} {idn' : Idn A} {inv' : Inv A}
  {rsmul' : RSMul S A} {rmod' : RightModule S A} : rsmul
  with signature eqv ==> eqv ==> eqv
  as eqv_rsmul_morphism.
Proof.
  intros x y p z w q.
  destruct rmod' as [_ _ rsmul_pro _ _ _ _].
  cbv in rsmul_pro. apply rsmul_pro.
  - apply p.
  - apply q. Qed.

End Classes.

Module Properties.

Import Classes AdditiveNotations.

Open Scope group_scope.

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

Import ZArith Z Classes.

Open Scope Z_scope.

Instance Z_Eqv : Eqv Z := fun x y : Z => x = y.

Instance Z_Setoid : Setoid Z := {
  ref := _;
  sym := _;
  tra := _;
}.
Proof.
  all: cbv [eqv].
  all: cbv [Z_Eqv].
  - apply eq_refl.
  - apply eq_sym.
  - apply eq_trans. Qed.

Instance Z_MulOpr : Opr Z := fun x y : Z => x * y.

Instance Z_MulSemigroup : Semigroup Z := {
  opr_pro := _;
  ass := _;
}.
Proof.
  all: cbv [eqv opr].
  all: cbv [Z_Eqv Z_MulOpr].
  - apply mul_wd.
  - intros x y z. rewrite mul_assoc. reflexivity. Qed.

Instance Z_MulIdn : Idn Z := 1.

Instance Z_MulMonoid : Monoid Z := {
  idn_l := _; idn_r := _;
}.
Proof.
  all: cbv [eqv opr idn].
  all: cbv [Z_Eqv Z_MulOpr Z_MulIdn].
  - intros x. rewrite mul_1_l. reflexivity.
  - intros x. rewrite mul_1_r. reflexivity. Qed.

Instance Z_AddOpr : Opr Z := fun x y : Z => x + y.

Instance Z_AddSemigroup : Semigroup Z := {
  opr_pro := _;
  ass := _;
}.
Proof.
  all: cbv [eqv opr].
  all: cbv [Z_Eqv Z_AddOpr].
  - apply add_wd.
  - intros x y z. rewrite add_assoc. reflexivity. Qed.

Instance Z_AddIdn : Idn Z := 0.

Instance Z_AddMonoid : Monoid Z := {
  idn_l := _; idn_r := _;
}.
Proof.
  all: cbv [eqv opr idn].
  all: cbv [Z_Eqv Z_AddOpr Z_AddIdn].
  - intros x. rewrite add_0_l. reflexivity.
  - intros x. rewrite add_0_r. reflexivity. Qed.

Instance Z_AddInv : Inv Z := fun x => - x.

Instance Z_AddGroup : Group Z := {
  inv_pro := _;
  inv_l := _; inv_r := _;
}.
Proof.
  all: cbv [eqv opr idn inv].
  all: cbv [Z_Eqv Z_AddOpr Z_AddIdn Z_AddInv].
  - apply opp_wd.
  - intros x. rewrite add_opp_diag_l. reflexivity.
  - intros x. rewrite add_opp_diag_r. reflexivity. Qed.

Instance Z_AddAbelianGroup : AbelianGroup Z := {
  add_com := _;
}.
Proof.
  all: cbv [eqv opr idn inv].
  all: cbv [Z_Eqv Z_AddOpr Z_AddIdn Z_AddInv].
  - intros x y. rewrite add_comm. reflexivity. Qed.

Instance Z_Add : Add Z := Z_AddOpr.
Instance Z_Zero : Zero Z := Z_AddIdn.
Instance Z_Neg : Neg Z := Z_AddInv.
Instance Z_Mul : Mul Z := Z_MulOpr.
Instance Z_One : One Z := Z_MulIdn.

Instance Z_Ring : Ring Z := {
  dis_l := _; dis_r := _;
}.
Proof.
  all: cbv [eqv add zero neg mul one].
  all: cbv [Z_Eqv Z_Add Z_Zero Z_Neg Z_Mul Z_One].
  all: cbv [eqv add zero neg mul one].
  all: cbv [Z_AddOpr Z_AddIdn Z_AddInv Z_MulOpr Z_MulIdn].
  - intros x y z. rewrite mul_add_distr_l. reflexivity.
  - intros x y z. rewrite mul_add_distr_r. reflexivity. Qed.

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

Fixpoint Fin_fold {A : Type} {n : nat} (f : Fin.t n -> A -> A) (z : A) {struct n} : A.
destruct n as [| p]. apply z. apply f. apply (@Fin.of_nat_lt p). omega. apply (Fin_fold A p).
  2: apply z. intros a x. apply f. 2: apply x.
  set (q := Fin.to_nat a). destruct q as [q r]. apply lt_S in r.
  pose proof (@Fin.of_nat_lt q (S p) r). apply H. Defined.

Compute nat_fold (fun x y => List.cons x y) List.nil 5.
Compute Fin_fold (n := 5) (fun x y => List.cons (proj1_sig (Fin.to_nat x)) y) List.nil.

Lemma Fin_fold_cons : forall {A : Type}
  {n : nat} (f : Fin.t n -> A -> A) (z : A),
  Fin_fold f z = Fin_fold f z.
Proof. intros A n f z. Abort.

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

Instance Z_VectorEqv {n : nat} : Eqv (t Z n) := Forall2 eqv.

Lemma Forall2_eq : forall {A : Type} {n : nat} (xs ys : t A n),
  Forall2 Logic.eq xs ys <-> Logic.eq xs ys.
Proof.
  intros A n xs ys. induction n as [| p q].
  - pose proof case_nil xs as pxs.
    pose proof case_nil ys as pys.
    subst xs ys. split.
    + intros r. reflexivity.
    + intros r. apply Forall2_nil.
  - rename xs into xxs, ys into yys.
    pose proof case_cons xxs as pxxs. destruct pxxs as [x [xs pxs]].
    pose proof case_cons yys as pyys. destruct pyys as [y [ys pys]].
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

Open Scope signature_scope.

Lemma s_equal : forall {A B : Type} `{Setoid A} `{Setoid B}
  (f : A -> B) {p : f ::> eqv ==> eqv} (x y : A),
  x == y -> f x == f y.
Proof.
  intros A B ? ? ? ? f ? x y p.
  rewrite p. reflexivity. Qed.

Lemma s_equal2 : forall {A0 A1 B : Type} `{Setoid A0} `{Setoid A1} `{Setoid B}
  (f : A0 -> A1 -> B) {p : f ::> eqv ==> eqv ==> eqv}
  (x0 y0 : A0) (x1 y1 : A1),
  x0 == y0 -> x1 == y1 -> f x0 x1 == f y0 y1.
Proof.
  intros A0 A1 B ? ? ? ? ? ? f ? x0 y0 x1 y1 p q.
  rewrite p, q. reflexivity. Qed.

Lemma Forall2_eqv : forall {A : Type} {n : nat} `{Setoid A} `{Setoid (t A n)}
  (xs ys : t A n),
  Forall2 eqv xs ys <-> eqv xs ys.
Proof.
  intros A n eqv std eqvs stds xs ys. induction n as [| p q].
  - pose proof case_nil xs as pxs.
    pose proof case_nil ys as pys.
    subst xs ys. split.
    + intros r. reflexivity.
    + intros r. apply Forall2_nil.
  - rename xs into xxs, ys into yys.
    pose proof case_cons xxs as pxxs. destruct pxxs as [x [xs pxs]].
    pose proof case_cons yys as pyys. destruct pyys as [y [ys pys]].
    subst xxs yys. split.
    + intros r. apply Forall2_inversion in r. destruct r as [rhd rtl].
      admit.
    + intros r.
      admit. Admitted.

Instance Z_VectorSetoid {n : nat} : Setoid (t Z n) := {
  ref := _;
  sym := _;
  tra := _;
}.
Proof.
  all: cbv [eqv].
  all: cbv [Z_VectorEqv].
  all: cbv [eqv].
  all: cbv [Z_Eqv].
  all: set (P (x y : Z) := x = y).
  - intros xs. apply Forall2_eq. reflexivity.
  - intros xs ys p. apply Forall2_eq. symmetry. apply Forall2_eq. apply p.
  - intros xs ys zs p q. apply Forall2_eq. transitivity ys.
    + apply Forall2_eq. apply p.
    + apply Forall2_eq. apply q. Qed.

(** There exists an easier way to carry out these proofs
    by first showing that [Forall2 eq] is equivalent to [eq],
    as we just did, but we pretend this is not the case here. *)

Instance Z_VectorOpr {n : nat} : Opr (t Z n) := map2 Z_AddOpr.

Instance Z_VectorSemigroup {n : nat} : Semigroup (t Z n) := {
  opr_pro := _;
  ass := _;
}.
Proof.
  all: cbv [eqv opr].
  all: cbv [Z_VectorEqv Z_VectorOpr].
  all: cbv [Z_Eqv Z_AddOpr].
  all: set (P (x y : Z) := x = y).
  - induction n as [| n p].
    + intros xs ys q zs ws r.
      pose proof case_nil xs as pxs'.
      pose proof case_nil ys as pys'.
      pose proof case_nil zs as pzs'.
      pose proof case_nil ws as pws'.
      subst. apply Forall2_nil.
    + intros xs ys q zs ws r.
      pose proof case_cons xs as pxs'. destruct pxs' as [x' [xs' pxs']].
      pose proof case_cons ys as pys'. destruct pys' as [y' [ys' pys']].
      pose proof case_cons zs as pzs'. destruct pzs' as [z' [zs' pzs']].
      pose proof case_cons ws as pws'. destruct pws' as [w' [ws' pws']].
      subst; rename x' into x, xs' into xs, y' into y, ys' into ys,
        z' into z, zs' into zs, w' into w, ws' into ws.
      apply Forall2_inversion in q. destruct q as [qhd qtl].
      apply Forall2_inversion in r. destruct r as [rhd rtl].
      cbn -[Z.add]. apply Forall2_cons.
      * apply add_wd.
        -- apply qhd.
        -- apply rhd.
      * apply p.
        -- apply qtl.
        -- apply rtl.
  - induction n as [| n p].
    + intros xs ys zs.
      pose proof case_nil xs as pxs'.
      pose proof case_nil ys as pys'.
      pose proof case_nil zs as pzs'.
      subst. apply Forall2_nil.
    + intros xs ys zs.
      pose proof case_cons xs as pxs'. destruct pxs' as [x' [xs' pxs']].
      pose proof case_cons ys as pys'. destruct pys' as [y' [ys' pys']].
      pose proof case_cons zs as pzs'. destruct pzs' as [z' [zs' pzs']].
      subst; rename x' into x, xs' into xs, y' into y, ys' into ys,
        z' into z, zs' into zs.
      cbn -[Z.add]. apply Forall2_cons.
      * cbv -[Z.add]. rewrite add_assoc. reflexivity.
      * apply p. Qed.

Instance Z_VectorIdn {n : nat} : Idn (t Z n) := const Z_AddIdn n.

Instance Z_VectorMonoid {n : nat} : Monoid (t Z n) := {
  idn_l := _; idn_r := _;
}.
Proof.
  all: cbv [eqv opr idn].
  all: cbv [Z_VectorEqv Z_VectorOpr Z_VectorIdn].
  all: cbv [Z_Eqv Z_AddOpr Z_AddIdn].
  all: set (P (x y : Z) := x = y).
  - induction n as [| n p].
    + intros xs.
      pose proof case_nil xs as pxs'.
      subst. apply Forall2_nil.
    + intros xs.
      pose proof case_cons xs as pxs'. destruct pxs' as [x' [xs' pxs']].
      subst; rename x' into x, xs' into xs.
      cbn -[Z.add Z.zero]. apply Forall2_cons.
      * rewrite add_0_l. reflexivity.
      * apply p.
  - induction n as [| n p].
    + intros xs.
      pose proof case_nil xs as pxs'.
      subst. apply Forall2_nil.
    + intros xs.
      pose proof case_cons xs as pxs'. destruct pxs' as [x' [xs' pxs']].
      subst; rename x' into x, xs' into xs.
      cbn -[Z.add Z.zero]. apply Forall2_cons.
      * rewrite add_0_r. reflexivity.
      * apply p. Qed.

Instance Z_VectorInv {n : nat} : Inv (t Z n) := map Z_AddInv.

Instance Z_VectorGroup {n : nat} : Group (t Z n) := {
  inv_pro := _;
  inv_l := _; inv_r := _;
}.
Proof.
  all: cbv [eqv opr idn inv].
  all: cbv [Z_VectorEqv Z_VectorOpr Z_VectorIdn Z_VectorInv].
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

Instance Z_VectorAbelianGroup {n : nat} : AbelianGroup (t Z n) := {
  add_com := _;
}.
Proof.
  all: cbv [eqv opr idn inv].
  all: cbv [Z_VectorEqv Z_VectorOpr Z_VectorIdn Z_VectorInv].
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

Instance Z_LeftModule {n : nat} : LeftModule Z (t Z n) := {
  lsmul_pro := _;
  lsmul_smul_cpt := _;
  lsmul_idn := _;
  lsmul_add_dis := _;
  lsmul_sadd_dis := _;
}.
Proof.
  all: cbv [eqv opr idn inv lsmul].
  all: cbv [Z_VectorEqv Z_VectorOpr Z_VectorIdn Z_VectorInv Z_LSMul].
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

Instance Z_RightModule {n : nat} : RightModule Z (t Z n) := {
  rsmul_pro := _;
  rsmul_smul_cpt := _;
  rsmul_idn := _;
  rsmul_add_dis := _;
  rsmul_sadd_dis := _;
}.
Proof.
  all: cbv [eqv opr idn inv rsmul].
  all: cbv [Z_VectorEqv Z_VectorOpr Z_VectorIdn Z_VectorInv Z_RSMul].
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

Instance Z_Bimodule {n : nat} : Bimodule Z Z (t Z n) := {
  smul_cpt := _;
}.
Proof.
  all: cbv [eqv opr idn inv lsmul rsmul].
  all: cbv [Z_VectorEqv Z_VectorOpr Z_VectorIdn Z_VectorInv Z_LSMul Z_RSMul].
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

Instance Fin_Finite {n : nat} : Finite (Fin.t n) := {
  fin := _
}.
Proof.
  cbv [Fin_Enum].
  induction n as [| n p]; intros x.
  - inversion x.
  - pose proof Fin_inversion_FS x as q. destruct q as [q | q]; subst.
    + cbn. cbv [dec Fin_Dec]. destruct (Fin.eq_dec Fin.F1 Fin.F1) as [q | q]; subst.
      * clear q. replace eqv with (@Logic.eq nat) in p by admit.
        remember (Fin_range n) as xs eqn : e. clear e.
        induction xs as [| y ys q].
        -- reflexivity.
        -- cbn. apply q. intros x. specialize (p x). cbn in p.
          cbv [dec Fin_Dec] in p. destruct (Fin.eq_dec x y) as [r | r]; subst.
          admit. admit.
      * congruence.
    + admit. Admitted.

Instance Z_Basis {n : nat} : Basis (Fin.t n) (Vector.t Z n) :=
  let ns := map (indicator n) (range n) in
  nth (map (map of_nat) ns).

Compute basis Fin.F1 : t Z 3.
Compute basis (Fin.FS Fin.F1) : t Z 3.
Compute basis (Fin.FS (Fin.FS Fin.F1)) : t Z 3.

Compute summation (add := Z_VectorOpr) (zero := Z_VectorIdn)
  (List.map basis enum) : t Z 3.

Instance Z_FinitelyFreeLeftModule {n : nat} :
  FinitelyFreeLeftModule (Fin.t n) Z (t Z n) := {
  basis_span := _;
  basis_lind := _;
}.
Proof.
  all: cbv [eqv opr idn inv lsmul basis].
  all: cbv [Z_VectorEqv Z_VectorOpr Z_VectorIdn Z_VectorInv Z_LSMul Z_Basis].
  all: cbv [eqv opr idn inv].
  all: cbv [Z_Eqv Z_AddOpr Z_AddIdn Z_AddInv Z_MulOpr Z_MulIdn].
  all: set (P (x y : Z) := x = y).
  - intros xs. exists (nth xs). induction n as [| n p].
    + pose proof case_nil xs as pxs'.
      subst. apply Forall2_nil.
    + pose proof case_cons xs as pxs'. destruct pxs' as [x' [xs' pxs']].
      subst; rename x' into x, xs' into xs.
(*
Forall2 P (Fin_fold
  (fun (a : Fin.t (S n)) (ys : t Z (S n)) =>
    map2 add (map (fun y : Z => (x :: xs)[@a] * y)
      (map (map of_nat) (map (indicator (S n)) (range (S n))))[@a]) ys)
  (const 0 (S n))) (x :: xs)

Forall2 P (Fin_fold
  (fun (a : Fin.t (S n)) (ys : t Z (S n)) =>
    map2 (fun y z : Z => y + z)
      (map (fun y : Z => (x :: xs)[@a] * y)
        (map (fun p : nat => map (fun q : nat => of_nat q) p) (map
          (fun i : nat => indicator (S n) i)
          (range (S n))))[@a]) ys)
  (const 0 (S n))) (x :: xs)

Forall2 P (Fin_fold
  (fun (a : Fin.t (S n)) (ys : t Z (S n)) =>
    map2 (fun y z : Z => y + z)
      (map (fun y : Z => (x :: xs)[@a] * y)
        (map (fun p : nat => map (fun q : nat => of_nat q) p) (map
          (fun i : nat =>
            match i with
            | O => S O :: const O n
            | S j => O :: indicator n j
            end)
          (O :: map S (range n))))[@a]) ys)
  (0 :: const 0 n)) (x :: xs)

Forall2 P (Fin_fold
  (fun (a : Fin.t (S n)) (ys : t Z (S n)) =>
    map2 (fun (p : nat) (z : Z) => (x :: xs)[@a] * of_nat p + z) (
      match nth (O :: map S (range n)) a with
      | O => S O :: const O n
      | S j => O :: indicator n j
      end) ys)
  (0 :: const 0 n)) (x :: xs)
*)
      admit.
  - intros. induction n as [| n p].
    + admit.
    + admit. Admitted.

End Instances.

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

Import Classes AdditiveNotations.

Open Scope module_scope.
Open Scope field_scope.
Open Scope group_scope.

Example fate := (meaning * fortune) <* hope - luck *> one.

End Output.

Section Test.

Import Vector VectorNotations ZArith Z.

Open Scope Z_scope.

Compute if Vector.eq_dec _ eqb _ _ fate [20273; 28193] then true else false.

End Test.

End Computations.

Extraction "example.ml" Classes Properties Instances Computations.
