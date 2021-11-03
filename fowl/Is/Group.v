(** * Group Structure *)

From DEZ.Has Require Export
  EquivalenceRelation NullaryOperation UnaryOperation BinaryOperation.
From DEZ.Is Require Export
  Monoid Invertible Proper
  Fixed Involutive Injective Cancellative Distributive.
From DEZ.ShouldHave Require Import
  EquivalenceRelationNotations AdditiveNotations.

(** ** Group *)

Class IsGrp (A : Type) (X : A -> A -> Prop)
  (x : A) (f : A -> A) (k : A -> A -> A) : Prop := {
  is_mon :> IsMon X x k;
  is_inv_l_r :> IsInvLR X x f k;
  is_proper :> IsProper (X ==> X) f;
}.

Section Context.

Context (A : Type) (X : A -> A -> Prop)
  (x : A) (f : A -> A) (k : A -> A -> A)
  `(!IsGrp X x f k).

#[local] Instance has_eq_rel : HasEqRel A := X.
#[local] Instance has_null_op : HasNullOp A := x.
#[local] Instance has_un_op : HasUnOp A := f.
#[local] Instance has_bin_op : HasBinOp A := k.

Ltac note := progress (
  try change X with eq_rel in *;
  try change x with null_op in *;
  try change f with un_op in *;
  try change k with bin_op in *).

#[local] Instance is_fixed : IsFixed X x f.
Proof.
  note.
  unfold IsFixed, IsFixed2.
  setoid_rewrite <- (unl_r (- x)).
  setoid_rewrite (inv_l x).
  reflexivity. Qed.

#[local] Instance is_invol : IsInvol X f.
Proof.
  note.
  intros y.
  setoid_rewrite <- (unl_r (- (- y))).
  setoid_rewrite <- (inv_l y).
  setoid_rewrite (assoc (- (- y)) (- y) y).
  setoid_rewrite (inv_l (- y)).
  setoid_rewrite (unl_l y).
  reflexivity. Qed.

#[local] Instance is_inj : IsInj X X f.
Proof.
  note.
  intros y z a.
  setoid_rewrite <- (unl_l z).
  setoid_rewrite <- (inv_r y).
  setoid_rewrite a.
  setoid_rewrite <- (assoc y (- z) z).
  setoid_rewrite (inv_l z).
  setoid_rewrite (unl_r y).
  reflexivity. Qed.

#[local] Instance is_cancel_l : IsCancelL X k.
Proof.
  note.
  intros y z w a.
  setoid_rewrite <- (unl_l y).
  setoid_rewrite <- (inv_l w).
  setoid_rewrite <- (assoc (- w) w y).
  setoid_rewrite a.
  setoid_rewrite (assoc (- w) w z).
  setoid_rewrite (inv_l w).
  setoid_rewrite (unl_l z).
  reflexivity. Qed.

#[local] Instance is_cancel_r : IsCancelR X k.
Proof.
  note.
  intros y z w a.
  setoid_rewrite <- (unl_r y).
  setoid_rewrite <- (inv_r w).
  setoid_rewrite (assoc y w (- w)).
  setoid_rewrite a.
  setoid_rewrite <- (assoc z w (- w)).
  setoid_rewrite (inv_r w).
  setoid_rewrite (unl_r z).
  reflexivity. Qed.

#[local] Instance is_cancel_l_r : IsCancelLR X k.
Proof. esplit; typeclasses eauto. Qed.

#[local] Instance is_antidistr : IsAntidistr X f k k.
Proof.
  note.
  intros y z.
  apply (cancel_l (- (y + z)) ((- z) + (- y)) (y + z)).
  setoid_rewrite (inv_r (y + z)).
  setoid_rewrite (assoc (y + z) (- z) (- y)).
  setoid_rewrite <- (assoc y z (- z)).
  setoid_rewrite (inv_r z).
  setoid_rewrite (unl_r y).
  setoid_rewrite (inv_r y).
  reflexivity. Qed.

End Context.

#[export] Hint Resolve is_fixed is_invol is_inj
  is_cancel_l is_cancel_r is_cancel_l_r is_antidistr : typeclass_instances.

(** ** Homomorphism Preserves Nullary Operations *)

Class IsNullPres (A B : Type) (X : B -> B -> Prop)
  (x : A) (y : B) (h : A -> B) : Prop :=
  null_pres : X (h x) y.

Class IsNullPres' (A B C : Type) (X : B -> C -> Prop)
  (x : A) (y : C) (h : A -> B) : Prop :=
  null_pres' : X (h x) y.

#[global] Instance is_null_pres (A B : Type) (X : B -> B -> Prop)
  (x : A) (y : B) (h : A -> B) `(!IsNullPres' X x y h) : IsNullPres X x y h.
Proof. apply null_pres'. Qed.

(** ** Homomorphism Preserves Unary Operations *)

Class IsUnPres (A B : Type) (X : B -> B -> Prop)
  (f : A -> A) (g : B -> B) (h : A -> B) : Prop :=
  un_pres (x : A) : X (h (f x)) (g (h x)).

(** ** Homomorphism Preserves Binary Operations *)

Class IsBinPres (A B : Type) (X : B -> B -> Prop)
  (k : A -> A -> A) (m : B -> B -> B) (h : A -> B) : Prop :=
  bin_pres (x y : A) : X (h (k x y)) (m (h x) (h y)).

(** ** Group Homomorphism *)

Class IsGrpHom (A B : Type)
  (X : A -> A -> Prop) (x : A) (f : A -> A) (k : A -> A -> A)
  (Y : B -> B -> Prop) (y : B) (g : B -> B) (m : B -> B -> B)
  (h : A -> B) : Prop := {
  dom_is_grp :> IsGrp X x f k;
  codom_is_grp :> IsGrp Y y g m;
  hom_is_bin_pres :> IsBinPres Y k m h;
  hom_is_proper :> IsProper (X ==> Y) h;
}.

Section Context.

Context (A B : Type)
  (X : A -> A -> Prop) (x : A) (f : A -> A) (k : A -> A -> A)
  (Y : B -> B -> Prop) (y : B) (g : B -> B) (m : B -> B -> B)
  (h : A -> B) `(!IsGrpHom X x f k Y y g m h).

#[local] Instance dom_has_eq_rel : HasEqRel A := X.
#[local] Instance dom_has_null_op : HasNullOp A := x.
#[local] Instance dom_has_un_op : HasUnOp A := f.
#[local] Instance dom_has_bin_op : HasBinOp A := k.
#[local] Instance codom_has_eq_rel : HasEqRel B := Y.
#[local] Instance codom_has_null_op : HasNullOp B := y.
#[local] Instance codom_has_un_op : HasUnOp B := g.
#[local] Instance codom_has_bin_op : HasBinOp B := m.

Ltac note := progress (
  try change X with (eq_rel (A := A)) in *;
  try change x with (null_op (A := A)) in *;
  try change f with (un_op (A := A)) in *;
  try change k with (bin_op (A := A)) in *;
  try change Y with (eq_rel (A := B)) in *;
  try change y with (null_op (A := B)) in *;
  try change g with (un_op (A := B)) in *;
  try change m with (bin_op (A := B)) in *).

#[local] Instance hom_is_null_pres : IsNullPres Y x y h.
Proof.
  unfold IsNullPres.
  note.
  pose proof bin_pres 0 0 as a.
  setoid_rewrite <- (unl_r (h (0 + 0))) in a.
  setoid_rewrite (unl_l 0) in a.
  apply cancel_l in a.
  setoid_rewrite <- a.
  reflexivity. Qed.

#[local] Instance hom_is_un_pres : IsUnPres Y f g h.
Proof.
  note.
  intros z.
  pose proof bin_pres z (- z) as a.
  setoid_rewrite (inv_r z) in a.
  eapply cancel_l with (h z).
  setoid_rewrite <- a.
  setoid_rewrite inv_r.
  apply null_pres. Qed.

End Context.

(** Now, let us make a mess! *)

From DEZ.Has Require Import
  Decidability.
From DEZ.Is Require Import
  Extensional.
From Coq Require Import
  Extraction Lists.List ZArith.ZArith.

Module Mess.

(** This alternative definition is closer to the one in abstract algebra. *)

Module Existential.

#[local] Reserved Notation "'f'".

Class IsGrp (A : Type) (X : A -> A -> Prop)
  (x : A) (k : A -> A -> A) : Type := {
  is_mon :> IsMon X x k;
  inv_l_r (y : A) : {z : A | X (k z y) x /\ X (k y z) x}
    where "'f'" := (fun x : A => proj1_sig (inv_l_r x));
  is_proper :> IsProper (X ==> X) f;
}.

End Existential.

(** The definitions are equivalent. *)

Section Context.

Lemma choice (A B : Type) (X : A -> B -> Prop) :
  (forall x : A, {y : B | X x y}) -> {f : A -> B | forall x : A, X x (f x)}.
Proof.
  intro Hs. exists (fun x : A => proj1_sig (Hs x)).
  intros x. destruct (Hs x) as [y HX]. cbn. apply HX. Defined.

Lemma cochoice (A B : Type) (X : A -> B -> Prop) :
  {f : A -> B | forall x : A, X x (f x)} -> forall x : A, {y : B | X x y}.
Proof.
  intros [f HX]. intros x. exists (f x). cbn. apply (HX x). Defined.

Lemma choiceT (A B : Type) (X : A -> B -> Type) :
  (forall x : A, {y : B & X x y}) -> {f : A -> B & forall x : A, X x (f x)}.
Proof.
  intro Hs. exists (fun x : A => projT1 (Hs x)).
  intros x. destruct (Hs x) as [y HX]. cbn. apply HX. Defined.

Lemma cochoiceT (A B : Type) (X : A -> B -> Type) :
  {f : A -> B & forall x : A, X x (f x)} -> forall x : A, {y : B & X x y}.
Proof.
  intros [f HX]. intros x. exists (f x). cbn. apply (HX x). Defined.

Lemma sectT `(!IsFunExtDep) (A B : Type) (X : A -> B -> Type)
  (a : forall x : A, {y : B & X x y}) : cochoiceT _ (choiceT a) = a.
Proof.
  unfold choiceT, cochoiceT. apply fun_ext_dep. intros x.
  destruct (a x) as [y b]. f_equal. Defined.

Lemma retrT `(!IsFunExtDep) (A B : Type) (X : A -> B -> Type)
  (a : {f : A -> B & forall x : A, X x (f x)}) : choiceT (cochoiceT _ a) = a.
Proof.
  unfold choiceT, cochoiceT. destruct a as [f b]. f_equal. Defined.

Context (A : Type) (X : A -> A -> Prop)
  (x : A) (k : A -> A -> A).

Lemma herbrandize : {f : A -> A | IsGrp X x f k} -> Existential.IsGrp X x k.
Proof.
  intros [f ?]. esplit. all: shelve. Unshelve.
  - intros y. exists (f y). split.
    + apply inv_l.
    + apply inv_r.
  - typeclasses eauto.
  - intros y z a. cbv. apply is_proper. apply a. Defined.

Lemma skolemize : Existential.IsGrp X x k -> {f : A -> A | IsGrp X x f k}.
Proof.
  intros ?.
  set (f (y : A) := proj1_sig (Existential.inv_l_r y)).
  set (g (y : A) := proj2_sig (Existential.inv_l_r y)).
  exists f. esplit.
  - typeclasses eauto.
  - split.
    + intros y. destruct (g y) as [l r]. apply l.
    + intros y. destruct (g y) as [l r]. apply r.
  - typeclasses eauto. Defined.

End Context.

#[global] Instance and_has_dec (A B : Prop)
  (d : HasDec A) (e : HasDec B) : HasDec (A /\ B).
Proof.
  destruct d as [[] x], e as [[] y].
  - exists true. intuition.
  - exists false. intuition.
  - exists false. intuition.
  - exists false. intuition. Defined.

#[global] Instance or_has_dec (A B : Prop)
  (d : HasDec A) (e : HasDec B) : HasDec (A \/ B).
Proof.
  destruct d as [[] x], e as [[] y].
  - exists true. intuition.
  - exists true. intuition.
  - exists true. intuition.
  - exists false. intuition. Defined.

#[local] Instance Forall_has_eq_dec (A : Type) (a : list (A * A))
  (d : HasEqDec A) : HasDec (Forall
  (fun a : A * A => match a with (x, y) => x = y end) a).
Proof.
  pose proof (Forall_dec
  (fun a : A * A => match a with (x, y) => x = y end)
  (fun a : A * A => match a with (x, y) => eq_dec x y end)) as e.
  destruct (e a) as [b | b].
  - exists true. intuition.
  - exists false. split.
    + intros c. inversion c.
    + intuition. Defined.

Import ListNotations.

Section Context.

Context (A : Type) (d : forall x y : A, {x = y} + {x <> y})
  (x : A) (f : A -> A) (k : A -> A -> A).

#[local] Instance has_eq_dec : HasEqDec A := d.

(** We should use finger trees for this.
    It is possible to achieve constant time cons, snoc,
    logarithmic time append and linear time iteration.
    See the paper by Hinze and Paterson for details. *)

Definition F_sup : Type := list (bool * A).

Definition F_wfb (a : F_sup) : bool :=
  forallb (fun '((i, x), (j, y)) => decide (i = j \/ x <> y))
  (combine a (skipn 1 a)).

Definition F_wf (a : F_sup) : Prop :=
  forall (n : nat) (i j : bool) (x y : A),
  nth_error a n = Some (i, x) ->
  nth_error a (S n) = Some (j, y) ->
  i = j \/ x <> y.

(** Technically, we should form this quotient, but we are lazy. *)

Fail Fail Definition F : Type := {x : F_sup $ Squash (F_wfb x)}.

Definition F : Type := F_sup.

Definition rel (x y : F) : Prop := if eq_dec x y then true else false.

Definition null : F := [].

Fail Fail Definition un (a : F) : F :=
  map (fun x : bool * A => (negb (fst x), snd x)) (rev a).

Fixpoint un_rev (b a : F) : F :=
  match a with
  | [] => b
  | (i, x) :: xs => un_rev ((negb i, x) :: b) xs
  end.

Definition un (a : F) : F :=
  un_rev [] a.

Fail Fail Fixpoint bin (a b : F) {struct b} : F :=
  match rev a, b with
  | (i, x) :: xs, (j, y) :: ys => if
      decide (i = negb j /\ x = y) then
      bin (rev xs) ys else
      a ++ b
  | _, [] => a
  | [], _ => b
  end.

Fixpoint bin_rev (a b : F) {struct b} : F * F :=
  match a, b with
  | (i, x) :: xs, (j, y) :: ys => if
      decide (i = j /\ x = y) then
      bin_rev xs ys else
      (a, b)
  | _, [] => (a, [])
  | [], _ => ([], b)
  end.

Definition bin (a b : F) : F :=
  let (c, d) := bin_rev (un a) b in
  un c ++ d.

#[local] Instance is_grp : IsGrp rel null un bin.
Proof.
  esplit.
  - esplit.
    + esplit.
      * esplit.
        -- admit.
        -- admit.
        -- admit.
      * admit.
      * admit.
    + esplit.
      * admit.
      * admit.
  - esplit.
    + admit.
    + admit.
  - admit. Admitted.

End Context.

Section Context.

#[local] Instance Z_has_eq_dec : HasEqDec Z := Z.eq_dec.

#[local] Open Scope Z_scope.

Definition hm (x : F Z) : Z :=
  fold_right Z.add Z.zero (map (fun a : bool * Z =>
  match a with
  (i, x) => if i then Z.opp x else x
  end) x).

#[local] Instance is_grp_hom :
  IsGrpHom (rel eq_dec) (null Z) un (bin Z.eq_dec) eq Z.zero Z.opp Z.add hm.
Proof.
  esplit.
  - apply is_grp.
    + apply Z.zero.
    + apply Z.opp.
    + apply Z.add.
  - (** Yes, [+%Z] forms a group. *) admit.
  - intros z w. unfold hm, bin. admit.
  - intros z w. unfold rel. destruct (eq_dec z w).
    + intros _. rewrite e. reflexivity.
    + intros a. inversion a. Admitted.

Equations tt1 (x : unit) : unit :=
  tt1 _ := tt.

Equations tt2 (x y : unit) : unit :=
  tt2 _ _ := tt.

Equations const_tt (x : Z) : unit :=
  const_tt _ := tt.

#[local] Instance is_grp_hom' :
  IsGrpHom eq Z.zero Z.opp Z.add eq tt tt1 tt2 const_tt.
Proof.
  esplit.
  - (** Yes, [+%Z] forms a group. *) admit.
  - (** Yes, [+%unit] forms a group. *) admit.
  - intros ? ?. reflexivity.
  - intros ? ? _. reflexivity. Admitted.

End Context.

#[local] Open Scope Z_scope.

(* - (b a' c a c' b b) *)
(* b' b' c a' c' a b' *)

Compute
  let a := (false, 1) in
  let b := (false, 2) in
  let c := (false, 3) in
  let a' := (negb (fst a), snd a) in
  let b' := (negb (fst b), snd b) in
  let c' := (negb (fst c), snd c) in
  un [b; a'; c; a; c'; b; b].

(* b a' c a' + a c' b b *)
(* b a' c + c' b b *)
(* b a' + b b *)
(* b a' b b *)

Compute
  let a := (false, 1) in
  let b := (false, 2) in
  let c := (false, 3) in
  let a' := (negb (fst a), snd a) in
  let b' := (negb (fst b), snd b) in
  let c' := (negb (fst c), snd c) in
  bin Z.eq_dec [b; a'; c; a'] [a; c'; b; b].

Compute
  let a := (false, 1) in
  let b := (false, 2) in
  let c := (false, 3) in
  let a' := (negb (fst a), snd a) in
  let b' := (negb (fst b), snd b) in
  let c' := (negb (fst c), snd c) in
  (fold_right Z.add Z.zero [2; -1; 3; -1; 1; -3; 2; 2],
  hm (bin Z.eq_dec [b; a'; c; a'] [a; c'; b; b])).

End Mess.

(* Extraction Mess. *)
