Set Warnings "-notation-overridden".

From Coq Require Eqdep_dec Extraction Setoid Vector ZArith.

(** TODO Modules for namespacing classes. *)
(** TODO Organization to mix concrete instances into class definitions. *)

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

(* start snippet ops *)
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
(* end snippet ops *)

(* start snippet notations *)
Delimit Scope group_scope with group.
Delimit Scope field_scope with field.
Delimit Scope module_scope with module.

Reserved Notation "x '==' y" (at level 70, no associativity).
Notation "x '==' y" := (eqv x y) : type_scope.
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
(* end snippet notations *)

Class Setoid (A : Type) {eqv : Eqv A} : Prop := {
  ref : forall x : A, x == x;
  sym : forall x y : A, x == y -> y == x;
  tra : forall x y z : A, x == y -> y == z -> x == z;
}.

Add Parametric Relation {A : Type} `{std : Setoid A} : A eqv
  reflexivity proved by ref
  symmetry proved by sym
  transitivity proved by tra
  as eqv_relation.

(* start snippet grouplikes *)
Section Additive.

Import AdditiveNotations.

Open Scope signature_scope.
Open Scope group_scope.

Class Semigroup (A : Type) {eqv : Eqv A} {opr : Opr A} : Prop := {
  setoid :> Setoid A;
  opr_pro : opr ::> eqv ==> eqv ==> eqv;
  ass : forall x y z : A, (x + y) + z == x + (y + z);
}.

Class Monoid (A : Type) {eqv : Eqv A} {opr : Opr A} {idn : Idn A} : Prop := {
  semigroup :> Semigroup A;
  idn_l : forall x : A, 0 + x == x;
  idn_r : forall x : A, x + 0 == x;
}.

Class Group (A : Type) {eqv : Eqv A}
  {opr : Opr A} {idn : Idn A} {inv : Inv A} : Prop := {
  monoid :> Monoid A;
  inv_pro : inv ::> eqv ==> eqv;
  inv_l : forall x : A, (- x) + x == 0;
  inv_r : forall x : A, x + (- x) == 0;
}.

Class AbelianGroup (A : Type) {eqv : Eqv A}
  {opr : Opr A} {idn : Idn A} {inv : Inv A} : Prop := {
  group :> Group A;
  add_com : forall x y : A, x + y == y + x;
}.

End Additive.
(* end snippet grouplikes *)

Add Parametric Morphism {A : Type} `{sgr : Semigroup A} : opr
  with signature eqv ==> eqv ==> eqv
  as eqv_opr_morphism.
Proof.
  intros x y p z w q. destruct sgr as [_ opr_pro _].
  cbv in opr_pro. apply opr_pro.
  - apply p.
  - apply q. Qed.

Add Parametric Morphism {A : Type} `{grp : Group A} : inv
  with signature eqv ==> eqv
  as eqv_inv_morphism.
Proof.
  intros x y p. destruct grp as [_ inv_pro _ _].
  cbv in inv_pro. apply inv_pro. apply p. Qed.

(* start snippet generics *)
Section Additive.

Import AdditiveNotations ZArith Pos.

Open Scope signature_scope.
Open Scope group_scope.

Definition popr {A : Type} `{Semigroup A} (n : positive) (x : A) : A :=
  iter_op opr n x.

Definition nopr {A : Type} `{Monoid A} (n : N) (x : A) : A :=
  match n with
  | N0 => 0
  | Npos p => popr p x
  end.

Definition zopr {A : Type} `{Group A} (n : Z) (x : A) : A :=
  match n with
  | Z0 => 0
  | Zpos p => popr p x
  | Zneg p => popr p (- x)
  end.

Theorem ivl : forall {A : Type} `{Group A},
  forall x : A, - (- x) == x.
Proof.
  intros A ? ? ? ? grp x.
  destruct grp as [[[ps pop pa] pnl pnr] pvp pvl pvr] eqn : pg.
  rewrite <- (pnr (- (- x))). rewrite <- (pvl x).
  rewrite <- (pa (- (- x)) (- x) x). rewrite (pvl (- x)). rewrite (pnl x).
  reflexivity. Qed.

Lemma inj_l : forall {A : Type} `{Group A},
  forall x y z : A, z + x == z + y -> x == y.
Proof.
  intros A ? ? ? ? grp x y z p.
  destruct grp as [[[ps pop pa] pnl pnr] pvp pvl pvr] eqn : pg.
  rewrite <- (pnl x). rewrite <- (pvl z). rewrite (pa (- z) z x).
  rewrite p. rewrite <- (pa (- z) z y). rewrite (pvl z). rewrite (pnl y).
  reflexivity. Qed.

Lemma inj_r : forall {A : Type} `{Group A},
  forall x y z : A, x + z == y + z -> x == y.
Proof.
  intros A ? ? ? ? grp x y z p.
  destruct grp as [[[ps pop pa] pnl pnr] pvp pvl pvr] eqn : pg.
  rewrite <- (pnr x). rewrite <- (pvr z). rewrite <- (pa x z (- z)).
  rewrite p. rewrite (pa y z (- z)). rewrite (pvr z). rewrite (pnr y).
  reflexivity. Qed.

Theorem dis : forall {A : Type} `{Group A},
  forall x y : A, - (x + y) == (- y) + (- x).
Proof.
  intros A ? ? ? ? grp x y.
  apply (inj_l (- (x + y)) ((- y) + (- x)) (x + y)).
  destruct grp as [[[ps pop pa] pnl pnr] pvp pvl pvr] eqn : pg.
  rewrite (pvr (x + y)). rewrite <- (pa (x + y) (- y) (- x)).
  rewrite (pa x y (- y)). rewrite (pvr y). rewrite (pnr x). rewrite (pvr x).
  reflexivity. Qed.

Theorem inv_0 : forall {A : Type} `{Group A},
  - 0 == 0.
Proof.
  intros A ? ? ? ? grp.
  destruct grp as [[[ps pop pa] pnl pnr] pvp pvl pvr] eqn : pg.
  rewrite <- (pnr (- 0)). rewrite (pvl 0).
  reflexivity. Qed.

End Additive.

Module MultipleNotations.

Export AdditiveNotations.

Reserved Notation "n '*%positive' x" (at level 40, left associativity).
Notation "n '*%positive' x" := (popr n x) : group_scope.

Reserved Notation "n '*%N' x" (at level 40, left associativity).
Notation "n '*%N' x" := (nopr n x) : group_scope.

Reserved Notation "n '*%Z' x" (at level 40, left associativity).
Notation "n '*%Z' x" := (zopr n x) : group_scope.

End MultipleNotations.

Module PowerNotations.

Export MultiplicativeNotations.

Reserved Notation "x '^%positive' n" (at level 40, left associativity).
Notation "x '^%positive' n" := (popr n x) : group_scope.

Reserved Notation "x '^%N' n" (at level 40, left associativity).
Notation "x '^%N' n" := (nopr n x) : group_scope.

Reserved Notation "x '^%Z' n" (at level 40, left associativity).
Notation "x '^%Z' n" := (zopr n x) : group_scope.

End PowerNotations.
(* end snippet generics *)

Section Multiple.

Import MultipleNotations ZArith Pos.

Open Scope signature_scope.
Open Scope group_scope.

Lemma iter_op_succ : forall {A : Type} `{Setoid A} (op : A -> A -> A),
 (forall x y z, op x (op y z) == op (op x y) z) ->
 forall p a, iter_op op (succ p) a == op a (iter_op op p a).
Proof.
  induction p; simpl; intros; try reflexivity.
  rewrite H0. apply IHp. Qed.

(** TODO Also true of nonabelian groups. *)
Theorem zdis : forall {A : Type} `{AbelianGroup A},
  forall (n : Z) (x : A), n *%Z (- x) == - (n *%Z x).
Proof.
  intros A ? ? ? ? grp n x. induction n as [| p | p].
  - cbn. rewrite inv_0. reflexivity.
  - cbn. induction p as [| q r] using peano_ind.
    + cbn. reflexivity.
    + cbv [popr] in *.
      destruct grp as [[[[ps pop pa] pnl pnr] pvp pvl pvr] pc] eqn : pg.
      pose proof iter_op_succ Classes.opr as s. repeat rewrite s.
      rewrite r. rewrite dis. rewrite pc. reflexivity.
      intros y z w. rewrite pa. reflexivity.
      intros y z w. rewrite pa. reflexivity.
  - cbn. induction p as [| q r] using peano_ind.
    + cbn. reflexivity.
    + cbv [popr] in *.
      destruct grp as [[[[ps pop pa] pnl pnr] pvp pvl pvr] pc] eqn : pg.
      pose proof iter_op_succ Classes.opr as s. repeat rewrite s.
      rewrite r. rewrite dis. repeat rewrite ivl. rewrite pc. reflexivity.
      intros y z w. rewrite pa. reflexivity.
      intros y z w. rewrite pa. reflexivity. Qed.

End Multiple.

(* start snippet fieldlikes *)
Section Arbitrary.

Open Scope field_scope.

Class Ring (A : Type) {eqv : Eqv A}
  {add : Add A} {zero : Zero A} {neg : Neg A}
  {mul : Mul A} {one : One A} : Prop := {
  add_agroup :> AbelianGroup A (opr := add) (idn := zero) (inv := neg);
  mul_monoid :> Monoid A (opr := mul) (idn := one);
  dis_l : forall x y z : A, x * (y + z) == x * y + x * z;
  dis_r : forall x y z : A, (x + y) * z == x * z + y * z;
}.

Class Field (A : Type) {eqv : Eqv A}
  {add : Add A} {zero : Zero A} {neg : Neg A}
  {mul : Mul A} {one : One A} {recip : Recip A} : Prop := {
  ring :> Ring A;
  mul_group :> Group A (opr := mul) (idn := one) (inv := recip);
}.

End Arbitrary.
(* end snippet fieldlikes *)

Add Parametric Morphism {A : Type} `{rng : Ring A} : add
  with signature eqv ==> eqv ==> eqv
  as eqv_add_morphism.
Proof.
  intros x y p z w q. destruct rng as [[[[[_ add_pro _] _ _] _ _ _] _] _ _ _].
  cbv in add_pro. apply add_pro.
  - apply p.
  - apply q. Qed.

Add Parametric Morphism {A : Type} `{rng : Ring A} : neg
  with signature eqv ==> eqv
  as eqv_neg_morphism.
Proof.
  intros x y p. destruct rng as [[[[_ _ _] neg_pro _ _] _] _ _ _].
  cbv in neg_pro. apply neg_pro. apply p. Qed.

Add Parametric Morphism {A : Type} `{rng : Ring A} : mul
  with signature eqv ==> eqv ==> eqv
  as eqv_mul_morphism.
Proof.
  intros x y p z w q.
  destruct rng as [_ [[_ mul_pro _] _ _] _ _].
  cbv in mul_pro. apply mul_pro.
  - apply p.
  - apply q. Qed.

(* start snippet spacelikes *)
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

Fail Class FinitelyFreeLeftModule (D S A : Type)
  {deqv : Eqv D} {denum : Enum D} {ddec : Dec D}
  {seqv : Eqv S} {sadd : Add S} {szero : Zero S} {sneg : Neg S}
  {smul : Mul S} {sone : One S}
  {eqv : Eqv A} {opr : Opr A} {idn : Idn A} {inv : Inv A}
  {lsmul : LSMul S A} {basis : Basis D A} : Prop := {
  finite :> Finite D;
  module :> LeftModule S A;
  basis_span : forall x : A, exists coeffs : D -> S,
    let terms (d' : D) := coeffs d' <* basis d' in
    folding (List.map terms enum) == x;
  basis_lind : forall coeffs : D -> S,
    let terms (d' : D) := coeffs d' <* basis d' in
    folding (List.map terms enum) == 0 ->
    List.Forall (fun a : S => a == 0%field) (List.map coeffs enum);
}.

End Additive.
(* end snippet spacelikes *)

Add Parametric Morphism {S A : Type} `{lmod : LeftModule S A} : lsmul
  with signature eqv ==> eqv ==> eqv
  as eqv_lsmul_morphism.
Proof.
  intros x y p z w q. destruct lmod as [_ _ lsmul_pro _ _ _ _].
  cbv in lsmul_pro. apply lsmul_pro.
  - apply p.
  - apply q. Qed.

Add Parametric Morphism {S A : Type} `{rmod : RightModule S A} : rsmul
  with signature eqv ==> eqv ==> eqv
  as eqv_rsmul_morphism.
Proof.
  intros x y p z w q. destruct rmod as [_ _ rsmul_pro _ _ _ _].
  cbv in rsmul_pro. apply rsmul_pro.
  - apply p.
  - apply q. Qed.

End Classes.

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

Lemma Forall2_inversion : forall {A B : Type} (P : A -> B -> Prop)
  {n : nat} (x : A) (xs : t A n) (y : B) (ys : t B n),
  Forall2 P (x :: xs) (y :: ys) -> P x y /\ Forall2 P xs ys.
Proof.
  intros A B P n x xs y ys p.
  inversion p as [| n' x' y' xs' ys' phd ptl pn' [px' pxs'] [py' pys']].
  apply (inj_pair2_eq_dec nat Nat.eq_dec) in pxs'.
  apply (inj_pair2_eq_dec nat Nat.eq_dec) in pys'.
  subst. split.
  - apply phd.
  - apply ptl. Qed.

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

Extraction "example.ml" Classes Instances Computations.
