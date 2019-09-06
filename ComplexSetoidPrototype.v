Set Warnings "-notation-overridden".

From Coq Require Eqdep_dec Extraction Setoid Vector ZArith.

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
Class Span (D A : Type) : Type := span : (D -> A) -> A.

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

Class Setoid (A : Type) {eqv : Eqv A} : Prop := {
  ref : forall x : A, x == x;
  sym : forall x y : A, x == y -> y == x;
  tra : forall x y z : A, x == y -> y == z -> x == z;
}.

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

Section Arbitrary.

Open Scope field_scope.

Class Ring (A : Type) {eqv : Eqv A} {add : Add A} {zero : Zero A} {neg : Neg A}
  {mul : Mul A} {one : One A} : Prop := {
  add_agroup :> AbelianGroup A (opr := add) (idn := zero) (inv := neg);
  mul_monoid :> Monoid A (opr := mul) (idn := one);
  dis_l : forall x y z : A, x * (y + z) == x * y + x * z;
  dis_r : forall x y z : A, (x + y) * z == x * z + y * z;
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

Class FreeLeftModule (D S A : Type)
  {seqv : Eqv S} {sadd : Add S} {szero : Zero S} {sneg : Neg S}
  {smul : Mul S} {sone : One S}
  {eqv : Eqv A} {opr : Opr A} {idn : Idn A} {inv : Inv A}
  {lsmul : LSMul S A} {lsmul : RSMul S A}
  {basis : Basis D A} {span : Span D A} : Prop := {
  module :> LeftModule S A;
  (** In words, this says "if you pick any point,
      I can find coefficients for the basis,
      such that the linear combination equals your point".
      In pseudocode, this says
      [forall x : A, exists cs : S ^ dim,
      x == cs_1 <* basis_1 + cs_2 <* basis_2 + ... + cs_dim <* basis_dim]. *)
  basis_span : forall x : A, exists cs : D -> S,
    let ys (d : D) := cs d <* basis d in
    span ys == x;
  (** In words, this says "if you can find any coefficients
      for any subset of the basis, such that the linear combination is zero,
      I can prove that all your coefficients are zero".
      In pseudocode, this says
      [forall (subdim <= dim) (subbasis <: basis) (cs : S ^ subdim),
      cs_1 <* basis_1 + cs_2 <* basis_2 + ... + cs_subdim <* basis_subdim = 0 ->
      cs_1 = 0 /\ cs_2 = 0 /\ ... /\ cs_subdim = 0]. *)
  (** TODO Fix this. *)
  basis_lind : forall embed : D -> D,
    let subbasis (d : D) : A := basis (embed d) in
    forall cs : D -> S,
    let ys (d : D) : A := cs d <* subbasis d in
    span ys == 0 -> forall d : D, ys d == 0;
}.

End Additive.

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

Require Import Program.
Obligation Tactic := idtac.
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

(** There exists an easier way to carry out these proofs
    by first showing that [Forall2 eq] is equivalent to [eq],
    but we pretend this is not the case here. *)

Instance Z_VectorSetoid {n : nat} : Setoid (t Z n) := {
  ref := _;
  sym := _;
  tra := _;
}.
Proof.
  all: cbv [eqv].
  all: cbv [Z_VectorEqv].
  all: cbv [Z_Eqv].
  all: set (P (x y : Z) := x = y).
  - intros xs. induction n as [| n p].
    + pose proof case_nil xs as pxs'.
      subst. apply Forall2_nil.
    + pose proof case_cons xs as pxs'. destruct pxs' as [x' [xs' pxs']].
      subst; rename x' into x, xs' into xs. apply Forall2_cons.
      * reflexivity.
      * apply p.
  - intros xs ys. induction n as [| n p].
    + intros q.
      pose proof case_nil xs as pxs'.
      pose proof case_nil ys as pys'.
      subst. apply Forall2_nil.
    + intros q.
      pose proof case_cons xs as pxs'. destruct pxs' as [x' [xs' pxs']].
      pose proof case_cons ys as pys'. destruct pys' as [y' [ys' pys']].
      subst; rename x' into x, xs' into xs, y' into y, ys' into ys.
      apply Forall2_inversion in q. destruct q as [qhd qtl].
      apply Forall2_cons.
      * symmetry. apply qhd.
      * apply p. apply qtl.
  - intros xs ys zs. induction n as [| n p].
    + intros q r.
      pose proof case_nil xs as pxs'.
      pose proof case_nil ys as pys'.
      pose proof case_nil zs as pzs'.
      subst. apply Forall2_nil.
    + intros q r.
      pose proof case_cons xs as pxs'. destruct pxs' as [x' [xs' pxs']].
      pose proof case_cons ys as pys'. destruct pys' as [y' [ys' pys']].
      pose proof case_cons zs as pzs'. destruct pzs' as [z' [zs' pzs']].
      subst; rename x' into x, xs' into xs, y' into y, ys' into ys,
        z' into z, zs' into zs.
      apply Forall2_inversion in q. destruct q as [qhd qtl].
      apply Forall2_inversion in r. destruct r as [rhd rtl].
      apply Forall2_cons.
      * etransitivity.
        -- apply qhd.
        -- apply rhd.
      * eapply p.
        -- apply qtl.
        -- apply rtl. Qed.

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

Instance Fin_Eqv {n : nat} : Eqv (Fin.t n) := fun x y : Fin.t n => x = y.

Instance Z_Basis {n : nat} : Basis (Fin.t n) (Vector.t Z n) :=
  let ns := map (indicator n) (range n) in
  nth (map (map of_nat) ns).

Compute basis Fin.F1 : t Z 3.
Compute basis (Fin.FS Fin.F1) : t Z 3.
Compute basis (Fin.FS (Fin.FS Fin.F1)) : t Z 3.

Instance Z_Span {n : nat} : Span (Fin.t n) (t Z n) :=
  fun (f : Fin.t n -> t Z n) =>
  Fin_fold (fun (a : Fin.t n) (x : t Z n) => map2 add (f a) x) (const 0 n).

Compute span basis : t Z 3.

Instance Z_FreeLeftModule {n : nat} : FreeLeftModule (Fin.t n) Z (t Z n) := {
  basis_span := _;
  basis_lind := _;
}.
Proof.
  all: cbv [eqv opr idn inv lsmul basis span].
  all: cbv [Z_VectorEqv Z_VectorOpr Z_VectorIdn Z_VectorInv
    Z_LSMul Z_Basis Z_Span].
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
