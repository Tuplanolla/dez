From Coq Require Import
  Lia Lists.List NArith.NArith Bool.Sumbool.
From Maniunfold.Has Require Export
  OneSorted.Decision.
From Maniunfold.Provides Require Export
  OptionTheorems PositiveTheorems ProductTheorems.

Ltac flatten_this op :=
  repeat match goal with
  | x : context [op (op ?f)] |- _ => change (op (op f)) with (op f) in x
  | |- context [op (op ?f)] => change (op (op f)) with (op f)
  end.

Ltac flatten :=
  repeat match goal with
  | h : context [?f (?f ?x)] |- _ => change (f (f x)) with (f x) in h
  | |- context [?f (?f ?x)] => change (f (f x)) with (f x)
  end.

Import ListNotations N.

#[local] Open Scope N_scope.

(** We use different names to refer to the domain and the codomain,
    even though they are the same. *)

Definition A : Type := N.
Definition B : Type := N.

Ltac forget := unfold A, B in *.

(** We define inverses by either
    extending the domain or restricting the codomain. *)

(** We are interested in monotonic injective functions
    with a fixed point at zero, who we shall considered miffing. *)

Class HasMiff : Type := miff (a : A) : B.

Typeclasses Transparent HasMiff.

(** Miffs are true to their name. *)

Class IsMonoMiff `(HasMiff) : Prop :=
  mono_miff (x y : A) (l : x < y) : miff x < miff y.

Class IsInjMiff `(HasMiff) : Prop :=
  inj_miff (x y : A) (e : miff x = miff y) : x = y.

Fail Fail Class IsSurjMiff `(HasMiff) : Prop :=
  surj_miff (b : B) : exists a : A, b = miff a.

Class IsFixedMiff `(HasMiff) : Prop :=
  fixed_miff : miff 0 = 0.

(** Monotonicity implies injectivity, but not vice versa. *)

#[global] Instance is_inj_miff `(IsMonoMiff) : IsInjMiff miff.
Proof.
  intros x y e.
  destruct (lt_trichotomy x y) as [la | [ea | la]].
  - apply mono_miff in la.
    flatten. forget. lia.
  - flatten. forget. lia.
  - apply mono_miff in la.
    flatten. forget. lia. Qed.

Class IsMiff `(HasMiff) : Prop := {
  base_is_mono_miff :> IsMonoMiff miff;
  base_is_inj_miff :> IsInjMiff miff;
  base_is_fixed_miff :> IsFixedMiff miff;
}.

(** We provide three ways to pseudoinvert miffs. *)

(** The first way is to extend the domain with a point. *)

Section Context.

Context `(IsMiff).

Class HasUnmiffError : Type := unmiff_error (b : B) : option A.

Typeclasses Transparent HasUnmiffError.

Class IsSectMiffError `(HasUnmiffError) : Prop :=
  sect_miff_error (a : A) : unmiff_error (miff a) = Some a.

(** The following statements are equivalent,
    although we favor the first one,
    because it does not mention [option_map]. *)

Class IsRetrMiffError `(HasUnmiffError) : Prop :=
  retr_miff_error (a : A) (b : B)
  (e : unmiff_error b = Some a) : b = miff a.

Class IsRetrMiffError' `(HasUnmiffError) : Prop :=
  retr_miff_error' (x y : B)
  (e : option_map miff (unmiff_error x) = Some y) : x = y.

Class IsMiffError `(HasUnmiffError) : Prop := {
  unmiff_error_is_sect_miff_error :> IsSectMiffError unmiff_error;
  unmiff_error_is_retr_miff_error :> IsRetrMiffError unmiff_error;
}.

End Context.

Module Retr'FromRetr.

#[local] Instance is_retr_miff_error' `(IsRetrMiffError) :
  IsRetrMiffError' unmiff_error.
Proof.
  intros x y e'.
  destruct (unmiff_error x) as [a |] eqn : e.
  - unfold option_map in e'.
    apply retr_miff_error in e.
    flatten. rewrite <- e in e'.
    injection e'. clear e'. intros e'. apply e'.
  - unfold option_map in e'.
    inversion e'. Qed.

#[export] Hint Resolve is_retr_miff_error' : typeclass_instances.

End Retr'FromRetr.

Module RetrFromRetr'.

#[local] Instance is_retr_miff_error `(IsRetrMiffError') :
  IsRetrMiffError unmiff_error.
Proof.
  intros a b e.
  destruct (unmiff_error b) as [x |] eqn : e'.
  - apply retr_miff_error'.
    flatten. rewrite e'. rewrite e.
    unfold option_map.
    reflexivity.
  - inversion e. Qed.

#[export] Hint Resolve is_retr_miff_error : typeclass_instances.

End RetrFromRetr'.

(** TODO Weak stuff here. *)

(** The second way is to round down. *)

Section Context.

Context `(IsMiff).

Class HasUnmiffDown : Type := unmiff_down (b : B) : A.

Typeclasses Transparent HasUnmiffDown.

Class IsSectMiffDown `(HasUnmiffDown) : Prop :=
  sect_miff_down (a : A) : unmiff_down (miff a) = a.

Class IsRetrMiffDown `(HasUnmiffDown) : Prop :=
  retr_miff_down (b : B) :
  miff (unmiff_down b) <= b < miff (succ (unmiff_down b)).

Class IsMiffDown `(HasUnmiffDown) : Prop := {
  unmiff_down_is_sect_miff_down :> IsSectMiffDown unmiff_down;
  unmiff_down_is_retr_miff_down :> IsRetrMiffDown unmiff_down;
}.

End Context.

(** Restrict the codomain. *)

Section Context.

Context `(IsMiffDown).

Definition B_quot : Type := {b : B $ Squash (miff (unmiff_down b) = b)}.

Equations B_pr (b : B) : B_quot :=
  B_pr b := Sexists _ (miff (unmiff_down b)) _.
Next Obligation.
  intros b.
  apply squash.
  rewrite (sect_miff_down (unmiff_down b)).
  reflexivity. Qed.

Equations miff_down_dep (a : A) : B_quot :=
  miff_down_dep a := B_pr (miff a).

Class HasUnmiffDownDep : Type := unmiff_down_dep (x : B_quot) : A.

Typeclasses Transparent HasUnmiffDownDep.

Class IsSectMiffDownDep `(HasUnmiffDownDep) : Prop :=
  sect_miff_down_dep (a : A) : unmiff_down_dep (miff_down_dep a) = a.

Class IsRetrMiffDownDep `(HasUnmiffDownDep) : Prop :=
  retr_miff_down_dep (x : B_quot) : miff_down_dep (unmiff_down_dep x) = x.

Class IsMiffDownDep `(HasUnmiffDownDep) : Prop := {
  unmiff_down_dep_is_sect_miff_down_dep :> IsSectMiffDownDep unmiff_down_dep;
  unmiff_down_dep_is_retr_miff_down_dep :> IsRetrMiffDownDep unmiff_down_dep;
}.

End Context.

(** The third way is to carry a remainder. *)

Section Context.

Context `(IsMiff).

Equations miff_rem_down (x : A + A * B) : B :=
  miff_rem_down (inl a) := miff a;
  miff_rem_down (inr (a, b)) := b + miff a.

Class HasUnmiffRemDown : Type := unmiff_rem_down (b : B) : A + A * B.

Typeclasses Transparent HasUnmiffRemDown.

Class IsRefineMiffRemDown `(HasUnmiffRemDown) : Prop :=
  refine_miff_down (x : B) :
  match unmiff_rem_down x with
  | inl a => True
  | inr (a, b) => miff a < b + miff a < miff (succ a)
  end.

(** Miffing is not a section of unmiffing with a remainder,
    unless we restrict the codomain to make it so.
    The unrestricted version is only presented for the sake of completeness,
    as it would be suspect to inhabit it. *)

Class IsSectMiffRemDown' `(HasUnmiffRemDown) : Prop :=
  sect_miff_rem_down' (x : A + A * B) : unmiff_rem_down (miff_rem_down x) = x.

Class IsSectMiffRemDown `(HasUnmiffRemDown) : Prop :=
  sect_miff_rem_down (a : A) : unmiff_rem_down (miff a) = inl a.

Class IsRetrMiffRemDown `(HasUnmiffRemDown) : Prop :=
  retr_miff_rem_down (b : B) : miff_rem_down (unmiff_rem_down b) = b.

Class IsUnmiffRemDown `(HasUnmiffRemDown) : Prop := {
  unmiff_rem_down_is_sect_miff_rem_down :> IsSectMiffRemDown unmiff_rem_down;
  unmiff_rem_down_is_retr_miff_rem_down :> IsRetrMiffRemDown unmiff_rem_down;
}.

End Context.

Section Context.

Context `(IsMiff).

Definition P (a : A) (b : B) : Prop := miff a < b + miff a < miff (succ a).

Definition S : Type := A + {x : A * B $ Squash (prod_uncurry P x)}.

Equations miff_rem_down_dep (x : S) : B :=
  miff_rem_down_dep (inl a) := miff a;
  miff_rem_down_dep (inr (Sexists _ (a, b) _)) := b + miff a.

Class HasUnmiffRemDownDep : Type := unmiff_rem_down_dep (b : B) : S.

Typeclasses Transparent HasUnmiffRemDownDep.

Class IsSectMiffRemDownDep `(HasUnmiffRemDownDep) : Prop :=
  sect_miff_rem_down_dep (x : S) :
  unmiff_rem_down_dep (miff_rem_down_dep x) = x.

Class IsRetrMiffRemDownDep `(HasUnmiffRemDownDep) : Prop :=
  retr_miff_rem_down_dep (b : B) :
  miff_rem_down_dep (unmiff_rem_down_dep b) = b.

Class IsUnmiffRemDownDep `(HasUnmiffRemDownDep) : Prop := {
  unmiff_rem_down_dep_is_sect_miff_rem_down_dep :>
    IsSectMiffRemDownDep unmiff_rem_down_dep;
  unmiff_rem_down_dep_is_retr_miff_rem_down_dep :>
    IsRetrMiffRemDownDep unmiff_rem_down_dep;
}.

End Context.
