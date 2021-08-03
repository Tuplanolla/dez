(** * Basic Logic *)

From Maniunfold Require Export
  Init.
From Maniunfold.Is Require Export
  Extensional Semiring.

(** ** Equalities *)

(** This is a negative version of [f_equal]. *)

Lemma f_nequal (A B : Type) (f : A -> B) (x y : A) (fxy : f x <> f y) : x <> y.
Proof. auto using f_equal. Qed.

(** ** Strict Propositions *)

(** This is another way to state [Spr1_inj]
    without breaking unification when universe polymorphism is turned off. *)

Lemma eq_Ssig (A : Type) (P : A -> SProp)
  (a0 : A) (b0 : P a0) (a1 : A) (b1 : P a1)
  (e : a0 = a1) : Sexists P a0 b0 = Sexists P a1 b1.
Proof. auto using Spr1_inj. Qed.

(** ** Semiring of Logical Equivalences *)

Lemma and_True_l (A : Prop) : 1 /\ A <-> A.
Proof. intuition. Qed.

Lemma and_True_r (A : Prop) : A /\ 1 <-> A.
Proof. intuition. Qed.

Lemma or_False_l (A : Prop) : 0 \/ A <-> A.
Proof. intuition. Qed.

Lemma or_False_r (A : Prop) : A \/ 0 <-> A.
Proof. intuition. Qed.

Lemma and_or_distr_l (A B C : Prop) : A /\ (B \/ C) <-> A /\ B \/ A /\ C.
Proof. intuition. Qed.

Lemma and_or_distr_r (A B C : Prop) : (A \/ B) /\ C <-> A /\ C \/ B /\ C.
Proof. intuition. Qed.

Lemma impl_and_l (A B C : Prop) : (A -> B /\ C) <-> (A -> B) /\ (A -> C).
Proof. intuition. Qed.

Lemma impl_and_r (A B C : Prop) : (A /\ B -> C) <-> (A -> B -> C).
Proof. intuition. Qed.

Lemma impl_or_r (A B C : Prop) : (A \/ B -> C) <-> (A -> C) /\ (B -> C).
Proof. intuition. Qed.

Section Context.

Context `(IsPropExt).

#[local] Instance is_mon : IsMon 0 _\/_.
Proof.
  repeat split; hnf; unfold null_op, bin_op;
  intros; apply prop_ext; intuition. Qed.

(** TODO This could be nicer. *)

#[local] Instance is_semiring : IsSemiring _\/_ 0 _/\_ 1.
Proof.
  repeat split; hnf; unfold zero, add, one, mul, null_op, bin_op;
  intros; apply prop_ext; intuition. Qed.

End Context.

(** ** Category of Types *)

(** Composition of functions with the identity function
    as the identity element form a category. *)

Lemma compose_assoc (A B C D : Type)
  (h : C -> D) (g : B -> C) (f : A -> B) (a : A) :
  (h o (g o f)) a = ((h o g) o f) a.
Proof. reflexivity. Qed.

Lemma compose_id_l (A B : Type) (f : A -> B) (a : A) :
  (id o f) a = f a.
Proof. reflexivity. Qed.

Lemma compose_id_r (A B : Type) (f : A -> B) (a : A) :
  (f o id) a = f a.
Proof. reflexivity. Qed.

(** Dependent composition is more complicated and
    involves the S and K combinators. *)

Section Context.

#[local] Notation "'_o_'" := compose_dep : core_scope.
#[local] Notation "g 'o' f" := (compose_dep g f) : core_scope.

Lemma compose_dep_assoc
  (A : Type) (P : A -> Type) (Q : forall a : A, P a -> Type)
  (R : forall (a : A) (b : P a), Q a b -> Type)
  (h : forall (a : A) (b : P a) (c : Q a b), R a b c)
  (g : forall (a : A) (b : P a), Q a b) (f : forall a : A, P a) (a : A) :
  ((fun x : A => h _ _) o (g o f)) a = ((fun x : A => h _ o g _) o f) a.
  (* (h o (g o f)) a = ((h o g) o f) a *)
Proof. reflexivity. Qed.

Lemma compose_dep_id_l (A : Type) (P : A -> Type)
  (f : forall a : A, P a) (a : A) :
  ((fun x : A => id) o f) a = f a.
  (* (const id o f) a = f a *)
Proof. reflexivity. Qed.

Lemma compose_dep_id_r (A : Type) (P : A -> Type)
  (f : forall a : A, P a) (a : A) :
  ((fun x : A => f) o id) a = f a.
  (* (const f o id) a = f a *)
Proof. reflexivity. Qed.

End Context.

(** ** Passing Arguments *)

(** Flipping is a section and a retraction of itself,
    making it an involution. *)

Lemma flip_involutive (A B C : Type)
  (f : A -> B -> C) (a : A) (b : B) :
  flip (flip f) a b = f a b.
Proof. reflexivity. Qed.

Lemma flip_dep_involutive (A B : Type) (P : A -> B -> Type)
  (f : forall (a : A) (b : B), P a b) (b : B) (a : A) :
  flip_dep (flip_dep f) a b = f a b.
Proof. reflexivity. Qed.

(** ** Currying and Uncurrying *)

(** Currying is a section of uncurrying. *)

Lemma eq_ex_uncurry_curry
  (A : Prop) (P : A -> Prop) (B : Prop)
  (f : (exists a : A, P a) -> B) (x : exists a : A, P a) :
  ex_uncurry (ex_curry f) x = f x.
Proof. destruct x as [a b]. reflexivity. Qed.

(** Currying is a retraction of uncurrying. *)

Lemma eq_ex_curry_uncurry
  (A : Prop) (P : A -> Prop) (B : Prop)
  (f : forall a : A, P a -> B) (a : A) (b : P a) :
  ex_curry (ex_uncurry f) a b = f a b.
Proof. reflexivity. Qed.

Lemma eq_ex_uncurry_dep_curry_dep
  (A : Prop) (P : A -> Prop) (Q : forall a : A, P a -> Prop)
  (f : forall x : exists a : A, P a, Q (ex_proj1 x) (ex_proj2 x))
  (x : exists a : A, P a) :
  ex_uncurry_dep (ex_curry_dep f) x = f x.
Proof. destruct x as [a b]. reflexivity. Qed.

Lemma eq_ex_curry_dep_uncurry_dep
  (A : Prop) (P : A -> Prop) (Q : forall a : A, P a -> Prop)
  (f : forall (a : A) (b : P a), Q a b)
  (a : A) (b : P a) :
  ex_curry_dep (ex_uncurry_dep f) a b = f a b.
Proof. reflexivity. Qed.

Lemma eq_prod_uncurry_curry (A B C : Type)
  (f : A * B -> C) (x : A * B) :
  prod_uncurry (prod_curry f) x = f x.
Proof. destruct x as [a b]. reflexivity. Qed.

Lemma eq_prod_curry_uncurry (A B C : Type)
  (f : A -> B -> C) (a : A) (b : B) :
  prod_curry (prod_uncurry f) a b = f a b.
Proof. reflexivity. Qed.

Lemma eq_prod_uncurry_dep_curry_dep (A B : Type) (P : A -> B -> Type)
  (f : forall x : A * B, P (fst x) (snd x)) (x : A * B) :
  prod_uncurry_dep (prod_curry_dep f) x = f x.
Proof. destruct x as [a b]. reflexivity. Qed.

Lemma eq_prod_curry_dep_uncurry_dep (A B : Type) (P : A -> B -> Type)
  (f : forall (a : A) (b : B), P a b) (a : A) (b : B) :
  prod_curry_dep (prod_uncurry_dep f) a b = f a b.
Proof. reflexivity. Qed.

Lemma eq_sig_uncurry_curry
  (A : Type) (P : A -> Prop) (B : Type)
  (f : {a : A | P a} -> B) (x : {a : A | P a}) :
  sig_uncurry (sig_curry f) x = f x.
Proof. destruct x as [a b]. reflexivity. Qed.

Lemma eq_sig_curry_uncurry
  (A : Type) (P : A -> Prop) (B : Type)
  (f : forall a : A, P a -> B) (a : A) (b : P a) :
  sig_curry (sig_uncurry f) a b = f a b.
Proof. reflexivity. Qed.

Lemma eq_sig_uncurry_dep_curry_dep
  (A : Type) (P : A -> Prop) (Q : forall a : A, P a -> Type)
  (f : forall x : {a : A | P a}, Q (proj1_sig x) (proj2_sig x))
  (x : {a : A | P a}) :
  sig_uncurry_dep (sig_curry_dep f) x = f x.
Proof. destruct x as [a b]. reflexivity. Qed.

Lemma eq_sig_curry_dep_uncurry_dep
  (A : Type) (P : A -> Prop) (Q : forall a : A, P a -> Type)
  (f : forall (a : A) (b : P a), Q a b)
  (a : A) (b : P a) :
  sig_curry_dep (sig_uncurry_dep f) a b = f a b.
Proof. reflexivity. Qed.

Lemma eq_sigT_uncurry_curry
  (A : Type) (P : A -> Type) (B : Type)
  (f : {a : A & P a} -> B) (x : {a : A & P a}) :
  sigT_uncurry (sigT_curry f) x = f x.
Proof. destruct x as [a b]. reflexivity. Qed.

Lemma eq_sigT_curry_uncurry
  (A : Type) (P : A -> Type) (B : Type)
  (f : forall a : A, P a -> B) (a : A) (b : P a) :
  sigT_curry (sigT_uncurry f) a b = f a b.
Proof. reflexivity. Qed.

Lemma eq_sigT_uncurry_dep_curry_dep
  (A : Type) (P : A -> Type) (Q : forall a : A, P a -> Type)
  (f : forall x : {a : A & P a}, Q (projT1 x) (projT2 x))
  (x : {a : A & P a}) :
  sigT_uncurry_dep (sigT_curry_dep f) x = f x.
Proof. destruct x as [a b]. reflexivity. Qed.

Lemma eq_sigT_curry_dep_uncurry_dep
  (A : Type) (P : A -> Type) (Q : forall a : A, P a -> Type)
  (f : forall (a : A) (b : P a), Q a b)
  (a : A) (b : P a) :
  sigT_curry_dep (sigT_uncurry_dep f) a b = f a b.
Proof. reflexivity. Qed.

Lemma eq_Ssig_uncurry_curry
  (A : Type) (P : A -> SProp) (B : Type)
  (f : {a : A $ P a} -> B) (x : {a : A $ P a}) :
  Ssig_uncurry (Ssig_curry f) x = f x.
Proof. destruct x as [a b]. reflexivity. Qed.

Lemma eq_Ssig_curry_uncurry
  (A : Type) (P : A -> SProp) (B : Type)
  (f : forall a : A, P a -> B) (a : A) (b : P a) :
  Ssig_curry (Ssig_uncurry f) a b = f a b.
Proof. reflexivity. Qed.

Lemma eq_Ssig_uncurry_dep_curry_dep
  (A : Type) (P : A -> SProp) (Q : forall a : A, P a -> Type)
  (f : forall x : {a : A $ P a}, Q (Spr1 x) (Spr2 x))
  (x : {a : A $ P a}) :
  Ssig_uncurry_dep (Ssig_curry_dep f) x = f x.
Proof. destruct x as [a b]. reflexivity. Qed.

Lemma eq_Ssig_curry_dep_uncurry_dep
  (A : Type) (P : A -> SProp) (Q : forall a : A, P a -> Type)
  (f : forall (a : A) (b : P a), Q a b)
  (a : A) (b : P a) :
  Ssig_curry_dep (Ssig_uncurry_dep f) a b = f a b.
Proof. reflexivity. Qed.
