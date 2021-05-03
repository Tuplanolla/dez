From Coq Require Import
  Lia Lists.List NArith.NArith Bool.Sumbool.
From Maniunfold.Has Require Export
  OneSorted.Decision.
From Maniunfold.Provides Require Export
  NTheorems OptionTheorems PositiveTheorems ProductTheorems.

(** TODO This may be built into [setoid_rewrite]. *)

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

Ltac lia := flatten; forget; Lia.lia.

(** We are interested in monotonic injective functions
    with a fixed point at zero, which we shall consider miffing. *)

Class HasMiff : Type := miff (a : A) : B.

Typeclasses Transparent HasMiff.

(** Miffs are true to their name. *)

Class IsMonoMiff `(HasMiff) : Prop :=
  mono_miff (x y : A) (l : x <= y) : miff x <= miff y.

Class IsInjMiff `(HasMiff) : Prop :=
  inj_miff (x y : A) (e : miff x = miff y) : x = y.

Class IsFixedMiff `(HasMiff) : Prop :=
  fixed_miff : miff 0 = 0.

(** TODO Generalize like this. *)

Fail Fail Class IsStrictMonoMiff `(HasMiff) : Prop :=
  strict_mono_miff : Morphisms.respectful lt lt miff miff.

Class IsStrictMonoMiff `(HasMiff) : Prop :=
  strict_mono_miff (x y : A) (l : x < y) : miff x < miff y.

(** Monotonicity and injectivity together imply strict monotonicity. *)

#[global] Instance is_strict_mono_miff `(HasMiff)
  `(!IsMonoMiff miff) `(!IsInjMiff miff) : IsStrictMonoMiff miff.
Proof.
  intros x y la.
  pose proof mono_miff x y ltac:(lia) as lb.
  destruct (eqb_spec (miff x) (miff y)) as [eb | fb].
  - pose proof inj_miff x y ltac:(lia) as ea. lia.
  - lia. Qed.

(** Strict monotonicity implies monotonicity. *)

#[global] Instance is_mono_miff `(IsStrictMonoMiff) : IsMonoMiff miff.
Proof.
  intros x y la.
  pose proof strict_mono_miff x y as lb.
  destruct (eqb_spec x y) as [ea | fa].
  - pose proof f_equal miff ea as eb. lia.
  - lia. Qed.

(** Strict monotonicity implies injectivity. *)

#[global] Instance is_inj_miff `(IsStrictMonoMiff) : IsInjMiff miff.
Proof.
  intros x y eb.
  destruct (lt_trichotomy x y) as [la | [ea | la]].
  - pose proof strict_mono_miff x y ltac:(lia) as lb. lia.
  - lia.
  - pose proof strict_mono_miff y x ltac:(lia) as lb. lia. Qed.

Class IsMiff `(HasMiff) : Prop := {
  miff_is_mono_miff :> IsMonoMiff miff;
  miff_is_inj_miff :> IsInjMiff miff;
  miff_is_fixed_miff :> IsFixedMiff miff;
}.

(** We investigate three ways to pseudoinvert miffs. *)

(** The first way to form the pseudoinverse is
    to extend the domain with a point. *)

Section Context.

Context `(IsMiff).

Class HasUnmiffError : Type := unmiff_error (b : B) : option A.

Typeclasses Transparent HasUnmiffError.

(** Partially, the pseudoinverse behaves like an inverse. *)

(** The following statements are equivalent,
    although we favor the first one,
    because it does not mention [option_map] or [option_bind]. *)

Class IsPartSectMiffError `(HasUnmiffError) : Prop :=
  part_sect_miff_error (a : A) : unmiff_error (miff a) = Some a.

Class IsPartSectMiffError' `(HasUnmiffError) : Prop :=
  part_sect_miff_error' (x : option A) :
  option_bind unmiff_error (option_map miff x) = x.

Class IsPartRetrMiffError `(HasUnmiffError) : Prop :=
  part_retr_miff_error (a : A) (b : B)
  (e : unmiff_error b = Some a) : b = miff a.

Class IsPartRetrMiffError' `(HasUnmiffError) : Prop :=
  part_retr_miff_error' (x y : B)
  (e : option_map miff (unmiff_error x) = Some y) : x = y.

Class IsPartUnmiffError `(HasUnmiffError) : Prop := {
  unmiff_error_is_part_sect_miff_error :> IsPartSectMiffError unmiff_error;
  unmiff_error_is_part_retr_miff_error :> IsPartRetrMiffError unmiff_error;
}.

(** Totally, the pseudoinverse behaves like a weak inverse. *)

(** TODO Generalize like this. *)

(* Class IsWeakSect (A B : Type)
  (f : A -> B) (unf_error : B -> option A) : Prop :=
  weak_sect (x : option A) : let y := option_map f x in
  option_map f (option_bind unf_error y) = y. *)

Class IsWeakSectMiffError `(HasUnmiffError) : Prop :=
  weak_sect_miff_error (x : option A) : let y := option_map miff x in
  option_map miff (option_bind unmiff_error y) = y.

Class IsWeakRetrMiffError `(HasUnmiffError) : Prop :=
  weak_retr_miff_error (y : option B) : let x := option_bind unmiff_error y in
  option_bind unmiff_error (option_map miff x) = x.

Class IsWeakUnmiffError `(HasUnmiffError) : Prop := {
  unmiff_error_is_weak_sect_miff_error :> IsWeakSectMiffError unmiff_error;
  unmiff_error_is_weak_retr_miff_error :> IsWeakRetrMiffError unmiff_error;
}.

End Context.

Module PartSect'FromPartSect.

#[local] Instance is_part_sect_miff_error' `(IsPartSectMiffError) :
  IsPartSectMiffError' unmiff_error.
Proof.
  intros [a |].
  - unfold option_bind, option_map.
    apply part_sect_miff_error.
  - unfold option_bind, option_map.
    reflexivity. Qed.

#[export] Hint Resolve is_part_sect_miff_error' : typeclass_instances.

End PartSect'FromPartSect.

Module PartSectFromPartSect'.

#[local] Instance is_part_sect_miff_error `(IsPartSectMiffError') :
  IsPartSectMiffError unmiff_error.
Proof.
  intros a.
  pose proof part_sect_miff_error' (Some a) as e.
  unfold option_bind, option_map in e.
  apply e. Qed.

#[export] Hint Resolve is_part_sect_miff_error : typeclass_instances.

End PartSectFromPartSect'.

Module PartRetr'FromPartRetr.

#[local] Instance is_part_retr_miff_error' `(IsPartRetrMiffError) :
  IsPartRetrMiffError' unmiff_error.
Proof.
  intros x y e'.
  destruct (unmiff_error x) as [a |] eqn : e.
  - unfold option_map in e'.
    apply part_retr_miff_error in e.
    setoid_rewrite <- e in e'.
    injection e'. clear e'. intros e'. apply e'.
  - unfold option_map in e'.
    inversion e'. Qed.

#[export] Hint Resolve is_part_retr_miff_error' : typeclass_instances.

End PartRetr'FromPartRetr.

Module PartRetrFromPartRetr'.

#[local] Instance is_part_retr_miff_error `(IsPartRetrMiffError') :
  IsPartRetrMiffError unmiff_error.
Proof.
  intros a b e.
  destruct (unmiff_error b) as [x |] eqn : e'.
  - apply part_retr_miff_error'.
    setoid_rewrite e'. rewrite e.
    unfold option_map.
    reflexivity.
  - inversion e. Qed.

#[export] Hint Resolve is_part_retr_miff_error : typeclass_instances.

End PartRetrFromPartRetr'.

(** The second way to form the pseudoinverse is
    to restrict the codomain by rounding. *)

(** In the whole codomain of the miff,
    the pseudoinverse behaves like a bound. *)

Section Context.

Context `(IsMiff).

Class HasUnmiffRoundDown : Type := unmiff_round_down (b : B) : A.

Class HasUnmiffRoundUp : Type := unmiff_round_up (b : B) : A.

Typeclasses Transparent HasUnmiffRoundDown HasUnmiffRoundUp.

Class IsMonoUnmiffRoundDown `(HasUnmiffRoundDown) : Prop :=
  mono_unmiff_round_down (x y : B) (l : x <= y) :
  unmiff_round_down x <= unmiff_round_down y.

Class IsSurjUnmiffRoundDown `(HasUnmiffRoundDown) : Prop :=
  surj_unmiff_round_down (a : A) : exists b : B, a = unmiff_round_down b.

Class IsSectMiffRoundDown `(HasUnmiffRoundDown) : Prop :=
  sect_miff_round_down (a : A) : unmiff_round_down (miff a) = a.

Class IsSectMiffRoundUp `(HasUnmiffRoundUp) : Prop :=
  sect_miff_round_up (a : A) : unmiff_round_up (miff a) = a.

(** The following statements are a bit awkward,
    because the predecessor function can be saturative. *)

Class IsBoundRetrMiffRoundDown `(HasUnmiffRoundDown) : Prop :=
  bound_retr_miff_round_down (b : B) :
  miff (unmiff_round_down b) <= b < miff (succ (unmiff_round_down b)).

Class IsBoundRetrMiffRoundUp `(HasUnmiffRoundUp) : Prop :=
  bound_retr_miff_round_up (b : B) (l : pred b < b) :
  miff (pred (unmiff_round_up b)) < b <= miff (unmiff_round_up b).

(** TODO Check which classes need [IsMiff] and name them properly. *)

Class IsUnmiffRoundDown `(HasUnmiffRoundDown) : Prop := {
  miff_is_miff_round_down :> IsMiff miff;
  unmiff_round_down_is_sect_miff_round_down :>
    IsSectMiffRoundDown unmiff_round_down;
  unmiff_round_down_is_bound_retr_miff_round_down :>
    IsBoundRetrMiffRoundDown unmiff_round_down;
}.

Class IsUnmiffRoundUp `(HasUnmiffRoundUp) : Prop := {
  miff_is_miff_round_up :> IsMiff miff;
  unmiff_round_up_is_sect_miff_round_up :>
    IsSectMiffRoundUp unmiff_round_up;
  unmiff_round_up_is_bound_retr_miff_round_up :>
    IsBoundRetrMiffRoundUp unmiff_round_up;
}.

(** TODO We could probably use this coherence condition
    to derive the rounding modes from each other. *)

Class IsHomUnmiffRound `(HasUnmiffRoundDown) `(HasUnmiffRoundUp) : Prop :=
  hom_unmiff_round (b : B) :
  unmiff_round_up (succ b) = succ (unmiff_round_down b).

Class IsUnmiffRound `(HasUnmiffRoundDown) `(HasUnmiffRoundUp) : Prop := {
  unmiff_round_down_is_unmiff_round_down :>
    IsUnmiffRoundDown unmiff_round_down;
  unmiff_round_up_is_unmiff_round_up :>
    IsUnmiffRoundUp unmiff_round_up;
  unmiff_round_down_unmiff_round_up_is_hom_unmiff_round :>
    IsHomUnmiffRound unmiff_round_down unmiff_round_up;
}.

End Context.

Section Context.

Context `(IsUnmiffRoundDown).

(** TODO These follow. *)

#[global] Instance is_mono_unmiff_round_down :
  IsMonoUnmiffRoundDown unmiff_round_down.
Proof.
  intros x y l.
  assert (ae : exists (a : A) (b : B), y = b + miff a).
  { exists (unmiff_round_down y), (y - miff (unmiff_round_down y)).
    pose proof bound_retr_miff_round_down y as ll.
    lia. }
  destruct ae as [a [b e]]. subst y.
  induction b as [| b' e] using peano_ind.
    + rewrite add_0_l in *.
      rewrite sect_miff_round_down.
      revert x l.
      induction a as [| a' e] using peano_ind; intros x l.
      rewrite fixed_miff in l.
      assert (e : x = 0) by lia. subst x. clear l.
      enough (unmiff_round_down 0 = 0) by (flatten; lia).
      apply inj_miff.
      pose proof bound_retr_miff_round_down 0.
      setoid_rewrite fixed_miff. lia.
      specialize (e (miff (pred (unmiff_round_down x)))).
      setoid_rewrite sect_miff_round_down in e.
      enough (pred (unmiff_round_down x) <= a') by (flatten; lia).
      apply e.
      pose proof bound_retr_miff_round_down x.
      pose proof inj_miff.
      pose proof strict_mono_miff. Restart.
  intros x y l.
  remember (x - miff (unmiff_round_down x)) as b eqn : e.
  fold B in b.
  induction b as [| b eb] using peano_ind.
  pose proof bound_retr_miff_round_down x as llx.
  assert (ex : x = miff (unmiff_round_down x)) by lia.
  rewrite ex. Admitted.

#[global] Instance is_surj_unmiff_round_down :
  IsSurjUnmiffRoundDown unmiff_round_down.
Proof.
  intros a.
  exists (miff a).
  rewrite sect_miff_round_down.
  reflexivity. Qed.

End Context.

(** In the image of the miff,
    the pseudoinverse behaves like an inverse. *)

Section Context.

(** Forming the quotient would be much nicer with higher inductive types,
    because then we would not need to choose an arbitrary rounding mode. *)

Context `(IsUnmiffRoundDown).

Definition R (x y : B) : Prop :=
  exists a : A, miff a <= x < miff (succ a) /\ miff a <= y < miff (succ a).

Definition B_R : Type := {b : B $ Squash (miff (unmiff_round_down b) = b)}.

Equations pr (b : B) : B_R :=
  pr b := Sexists _ (miff (unmiff_round_down b)) _.
Next Obligation.
  intros b.
  apply squash.
  rewrite (sect_miff_round_down (unmiff_round_down b)).
  reflexivity. Qed.

(** TODO You should be able to write this. *)

Lemma wtf (a : A) (b : B) (ll : miff a <= b < miff (succ a)) :
  unmiff_round_down b = a.
Proof.
  revert b ll.
  induction a using peano_ind; intros b ll.
  - induction b using peano_ind.
    + pose proof proj1 (bound_retr_miff_round_down 0) as ll0.
      assert (eh : miff (unmiff_round_down 0) = 0) by lia.
      rewrite <- fixed_miff in eh at 2.
      apply inj_miff in eh. auto.
    + setoid_rewrite fixed_miff in ll.
      setoid_rewrite fixed_miff in IHb.
      specialize (IHb ltac:(lia)).
      pose proof bound_retr_miff_round_down b as ll0. Admitted.

Lemma quotient (x y : B) (r : R x y) : pr x = pr y.
Proof.
  unfold pr.
  apply Spr1_inj.
  unfold Spr1.
  f_equal.
  destruct r as [a [lx ly]].
  destruct (lt_trichotomy x y) as [la | [ea | la]].
  - rewrite (wtf a x) by assumption. rewrite (wtf a y) by assumption.
    reflexivity.
  - subst y. reflexivity.
  - rewrite (wtf a x) by assumption. rewrite (wtf a y) by assumption.
    reflexivity. Qed.

Equations miff_round_dep (a : A) : B_R :=
  miff_round_dep a := pr (miff a).

Class HasUnmiffRoundDep : Type := unmiff_round_dep (x : B_R) : A.

Typeclasses Transparent HasUnmiffRoundDep.

Class IsSectMiffRoundDep `(HasUnmiffRoundDep) : Prop :=
  sect_miff_round_dep (a : A) : unmiff_round_dep (miff_round_dep a) = a.

Class IsRetrMiffRoundDep `(HasUnmiffRoundDep) : Prop :=
  retr_miff_round_dep (x : B_R) : miff_round_dep (unmiff_round_dep x) = x.

Class IsUnmiffRoundDep `(HasUnmiffRoundDep) : Prop := {
  miff_is_miff_round_dep :> IsMiff miff;
  unmiff_round_dep_is_sect_miff_round_dep :>
    IsSectMiffRoundDep unmiff_round_dep;
  unmiff_round_dep_is_retr_miff_round_dep :>
    IsRetrMiffRoundDep unmiff_round_dep;
}.

End Context.

(** The third way to form the pseudoinverse is
    to extend the domain by carrying a remainder. *)

(** With an arbitrary remainder,
    the pseudoinverse behaves like a weak inverse. *)

Section Context.

Context `(IsMiff).

Equations miff_rem_down (x : A + A * B) : B :=
  miff_rem_down (inl a) := miff a;
  miff_rem_down (inr (a, b)) := b + miff a.

Equations miff_rem_up (x : A + A * B) : B :=
  miff_rem_up (inl a) := miff a;
  miff_rem_up (inr (a, b)) := miff a - b.

Class HasUnmiffRemDown : Type := unmiff_rem_down (b : B) : A + A * B.

Class HasUnmiffRemUp : Type := unmiff_rem_up (b : B) : A + A * B.

Typeclasses Transparent HasUnmiffRemDown HasUnmiffRemUp.

Class IsPartSectMiffRemDown `(HasUnmiffRemDown) : Prop :=
  part_sect_miff_rem_down (a : A) : unmiff_rem_down (miff a) = inl a.

Class IsPartSectMiffRemUp `(HasUnmiffRemUp) : Prop :=
  part_sect_miff_rem_up (a : A) : unmiff_rem_up (miff a) = inl a.

Class IsRetrMiffRemDown `(HasUnmiffRemDown) : Prop :=
  retr_miff_rem_down (b : B) : miff_rem_down (unmiff_rem_down b) = b.

Class IsRetrMiffRemUp `(HasUnmiffRemUp) : Prop :=
  retr_miff_rem_up (b : B) : miff_rem_up (unmiff_rem_up b) = b.

Class IsUnmiffRemDown `(HasUnmiffRemDown) : Prop := {
  miff_is_miff_rem_down :> IsMiff miff;
  unmiff_rem_down_is_part_sect_miff_rem_down :>
    IsPartSectMiffRemDown unmiff_rem_down;
  unmiff_rem_down_is_retr_miff_rem_down :> IsRetrMiffRemDown unmiff_rem_down;
}.

Class IsUnmiffRemUp `(HasUnmiffRemUp) : Prop := {
  miff_is_miff_rem_up :> IsMiff miff;
  unmiff_rem_up_is_part_sect_miff_rem_up :>
    IsPartSectMiffRemUp unmiff_rem_up;
  unmiff_rem_up_is_retr_miff_rem_up :> IsRetrMiffRemUp unmiff_rem_up;
}.

Class IsUnmiffRem `(HasUnmiffRemDown) `(HasUnmiffRemUp) : Prop := {
  unmiff_rem_down_is_unmiff_rem_down :> IsUnmiffRemDown unmiff_rem_down;
  unmiff_rem_up_is_unmiff_rem_up :> IsUnmiffRemUp unmiff_rem_up;
}.

End Context.

(** With a well-formed remainder,
    the pseudoinverse behaves like an inverse. *)

Section Context.

Context `(IsMiff).

Definition P_down (a : A) (b : B) : Prop :=
  miff a < b + miff a < miff (succ a).

Definition P_up (a : A) (b : B) : Prop :=
  miff (pred a) < miff a - b < miff a.

Definition S_down : Type := A + {x : A * B $ Squash (prod_uncurry P_down x)}.

Definition S_up : Type := A + {x : A * B $ Squash (prod_uncurry P_up x)}.

Equations miff_rem_down_dep (x : S_down) : B :=
  miff_rem_down_dep (inl a) := miff a;
  miff_rem_down_dep (inr (Sexists _ (a, b) _)) := b + miff a.

Equations miff_rem_up_dep (x : S_up) : B :=
  miff_rem_up_dep (inl a) := miff a;
  miff_rem_up_dep (inr (Sexists _ (a, b) _)) := miff a - b.

Class HasUnmiffRemDownDep : Type := unmiff_rem_down_dep (b : B) : S_down.

Class HasUnmiffRemUpDep : Type := unmiff_rem_up_dep (b : B) : S_up.

Typeclasses Transparent HasUnmiffRemDownDep HasUnmiffRemUpDep.

Class IsSectMiffRemDownDep `(HasUnmiffRemDownDep) : Prop :=
  sect_miff_rem_down_dep (x : S_down) :
  unmiff_rem_down_dep (miff_rem_down_dep x) = x.

Class IsSectMiffRemUpDep `(HasUnmiffRemUpDep) : Prop :=
  sect_miff_rem_up_dep (x : S_up) :
  unmiff_rem_up_dep (miff_rem_up_dep x) = x.

Class IsRetrMiffRemDownDep `(HasUnmiffRemDownDep) : Prop :=
  retr_miff_rem_down_dep (b : B) :
  miff_rem_down_dep (unmiff_rem_down_dep b) = b.

Class IsRetrMiffRemUpDep `(HasUnmiffRemUpDep) : Prop :=
  retr_miff_rem_up_dep (b : B) :
  miff_rem_up_dep (unmiff_rem_up_dep b) = b.

Class IsUnmiffRemDownDep `(HasUnmiffRemDownDep) : Prop := {
  miff_is_miff_rem_down_dep :> IsMiff miff;
  unmiff_rem_down_dep_is_sect_miff_rem_down_dep :>
    IsSectMiffRemDownDep unmiff_rem_down_dep;
  unmiff_rem_down_dep_is_retr_miff_rem_down_dep :>
    IsRetrMiffRemDownDep unmiff_rem_down_dep;
}.

Class IsUnmiffRemUpDep `(HasUnmiffRemUpDep) : Prop := {
  miff_is_miff_rem_up_dep :> IsMiff miff;
  unmiff_rem_up_dep_is_sect_miff_rem_up_dep :>
    IsSectMiffRemUpDep unmiff_rem_up_dep;
  unmiff_rem_up_dep_is_retr_miff_rem_up_dep :>
    IsRetrMiffRemUpDep unmiff_rem_up_dep;
}.

Class IsUnmiffRemDep `(HasUnmiffRemDownDep) `(HasUnmiffRemUpDep) : Prop := {
  unmiff_rem_down_dep_is_unmiff_rem_down_dep :>
    IsUnmiffRemDownDep unmiff_rem_down_dep;
  unmiff_rem_up_dep_is_unmiff_rem_up_dep :>
    IsUnmiffRemUpDep unmiff_rem_up_dep;
}.

End Context.
