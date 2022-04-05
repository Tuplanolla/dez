From Coq Require Import
  Lia Lists.List NArith.NArith Bool.Sumbool.
From DEZ.Is Require Export
  Fixed Injective Monotonic Comonotonic Isomorphic.
From DEZ.Justifies Require Export
  OptionTheorems.

(** TODO This may be built into [setoid_rewrite]. *)

Ltac flatten :=
  repeat match goal with
  | h : context [?f (?f ?x)] |- _ => change (f (f x)) with (f x) in h
  | |- context [?f (?f ?x)] => change (f (f x)) with (f x)
  end.

Ltac flatten' :=
  repeat match goal with
  | h : context [?g (?f ?x)] |- _ =>
    unify f g;
    change (g (f x)) with (f x) in h
  | |- context [?g (?f ?x)] =>
    unify f g;
    change (g (f x)) with (f x)
  end.

Import ListNotations N.

#[local] Open Scope N_scope.

(** We use different names to refer to the domain and the codomain,
    even though they are the same. *)

Definition A : Type := N.
Definition B : Type := N.

Ltac forget := unfold A, B in *.

Ltac lia := flatten'; forget; unfold ord_rel in *; Lia.lia.

(** We are interested in monotonic injective functions
    with a fixed point at zero, which we shall consider miffing.
    In order theory, these are called order embeddings
    with a fixed point at the bottom. *)

Class HasMiff : Type := miff (a : A) : B.

#[export] Typeclasses Transparent HasMiff.

(** Miffs are true to their name. *)

Notation IsMonoMiff miff := (Proper (le ==> le) miff).
Notation mono_miff := (proper_prf (R := le ==> le) miff : IsMonoMiff miff).

#[export] Instance has_ord_rel : HasOrdRel N := le.
#[export] Instance has_str_ord_rel : HasStrOrdRel N := lt.

(** TODO This might be a better way to specialize. Investigate. *)

Class IsInjMiff (f : HasMiff) : Prop :=
  is_inj :> IsInj _=_ f.

Notation inj_miff := (inj (f := miff) : IsInjMiff miff).

Notation IsFixedMiff := (IsFixed _=_ 0).
Notation fixed_miff := (@fixed _ _=_ 0 _ _ : _ 0 = 0).

Notation IsStrMonoMiff miff := (Proper (lt ==> lt) miff).
Notation str_mono_miff := (proper_prf (R := lt ==> lt) miff : IsStrMonoMiff miff).

Notation IsStrComonoMiff := (IsInj lt).
Notation str_comono_miff := (inj : IsStrComonoMiff miff).

(** Such a function is said to be inflationary or progressive. *)

Class IsInflateMiff `(HasMiff) : Prop :=
  inflate_miff (a : A) : a <= miff a.

Fail Class IsExpand (A B : Type)
  `(HasDist A) `(HasDist B) (f : A -> B) : Prop :=
  expand (x y : A) : dist x y <= dist (fn x) (fn y).

(** Strict monotonicity implies strict comonotonicity. *)

#[global] Instance is_str_comono_miff `(HasMiff) `(!IsStrMonoMiff miff) :
  IsStrComonoMiff miff.
Proof.
  intros x y lb.
  destruct (lt_trichotomy x y) as [la | [ea | la']].
  - lia.
  - subst y. lia.
  - pose proof str_mono_miff y x ltac:(lia) as lb'. lia. Qed.

(** Strict monotonicity implies monotonicity. *)

#[global] Instance is_mono_miff `(HasMiff) `(!IsStrMonoMiff miff) :
  IsMonoMiff miff.
Proof.
  intros x y la.
  pose proof str_mono_miff x y as lb.
  destruct (eqb_spec x y) as [ea | fa].
  - pose proof f_equal miff ea as eb. lia.
  - lia. Qed.

(** Strict monotonicity implies injectivity. *)

#[global] Instance is_inj_miff `(HasMiff) `(!IsStrMonoMiff miff) :
  IsInjMiff miff.
Proof.
  intros x y eb.
  destruct (lt_trichotomy x y) as [la | [ea | la']].
  - pose proof str_mono_miff x y ltac:(lia) as lb. lia.
  - lia.
  - pose proof str_mono_miff y x ltac:(lia) as lb'. lia. Qed.

(** Monotonicity and injectivity together imply strict monotonicity. *)

(** TODO This might cause a cycle. *)

#[global] Instance is_str_mono_miff `(HasMiff)
  `(!IsMonoMiff miff) `(!IsInjMiff miff) : IsStrMonoMiff miff.
Proof.
  intros x y la.
  destruct (eqb_spec (miff x) (miff y)) as [ea | fa].
  - pose proof inj_miff x y ltac:(lia) as eb. lia.
  - pose proof mono_miff x y ltac:(lia) as lb. lia. Qed.

(** Strict monotonicity and fixed point at zero together
    imply that the function is expansive. *)

#[global] Instance is_inflate_fixed_miff `(HasMiff)
  `(!IsStrMonoMiff miff) `(!IsFixedMiff miff) : IsInflateMiff miff.
Proof.
  intros a.
  induction a as [| p lp] using peano_ind.
  - rewrite fixed_miff. reflexivity.
  - pose proof str_mono_miff p (succ p) ltac:(lia) as lb. lia. Qed.

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
    to restrict the codomain by introducing rounding. *)

(** In the whole codomain of the miff,
    the pseudoinverse behaves like a bound. *)

Notation IsSectMiffRoundDown g := (IsRetr _=_ miff g).
Notation sect_miff_round_down := (retr : IsSectMiffRoundDown _).

Section Context.

Context `(IsMiff).

Class HasUnmiffRoundDown : Type := unmiff_round_down (b : B) : A.

Class HasUnmiffRoundUp : Type := unmiff_round_up (b : B) : A.

Typeclasses Transparent HasUnmiffRoundDown HasUnmiffRoundUp.

Class IsMonoUnmiffRoundDown `(HasUnmiffRoundDown) : Prop :=
  mono_unmiff_round_down (x y : B) (l : x <= y) :
  unmiff_round_down x <= unmiff_round_down y.

Class IsSurjUnmiffRoundDown `(HasUnmiffRoundDown) : Prop :=
  surj_unmiff_round_down (a : A) : exists b : B, unmiff_round_down b = a.

Class IsContractUnmiffRoundDown `(HasUnmiffRoundDown) : Prop :=
  contract_unmiff_round_down (x : A) : unmiff_round_down x <= x.

Fail Fail Class IsSectMiffRoundDown `(HasUnmiffRoundDown) : Prop :=
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

(** The sketch of this proof was contributed by Paolo Giarrusso. *)

#[global] Instance is_mono_unmiff_round_down :
  IsMonoUnmiffRoundDown unmiff_round_down.
Proof.
  intros x y lb.
  destruct (lt_trichotomy (unmiff_round_down x) (unmiff_round_down y))
  as [la | [ea | la']].
  - apply le_neq. lia.
  - lia.
  - exfalso.
    pose proof bound_retr_miff_round_down x as lx.
    pose proof bound_retr_miff_round_down y as ly.
    assert (l : miff (unmiff_round_down x) < miff (succ (unmiff_round_down y)))
    by lia.
    apply str_comono_miff in l.
    lia. Qed.

#[global] Instance is_surj_unmiff_round_down :
  IsSurjUnmiffRoundDown unmiff_round_down.
Proof.
  intros a.
  exists (miff a).
  pose proof sect_miff_round_down as e.
  rewrite e.
  reflexivity. Qed.

#[global] Instance is_contract_unmiff_round_down :
  IsContractUnmiffRoundDown unmiff_round_down.
Proof.
  intros a.
  pose proof inflate_miff a as l.
  apply mono_unmiff_round_down in l.
  rewrite sect_miff_round_down in l.
  apply l. Qed.

Lemma unmiff_round_down_elim (a : A) (b : B)
  (ll : miff a <= b < miff (succ a)) : unmiff_round_down b = a.
Proof.
  destruct (eqb_spec (unmiff_round_down b) (succ a)) as [eb | fb].
  - exfalso.
    apply (f_equal miff) in eb.
    pose proof bound_retr_miff_round_down b as lb.
    lia.
  - assert (lb : b <= miff (succ a)) by lia.
    apply mono_unmiff_round_down in lb.
    rewrite sect_miff_round_down in lb.
    assert (lb1 : unmiff_round_down b <= a) by lia.
    clear fb lb.
    pose proof mono_unmiff_round_down (miff a) b ltac:(lia) as lb0.
    rewrite sect_miff_round_down in lb0.
    lia. Qed.

End Context.

Section Context.

Context `(IsUnmiffRoundUp).

(** TODO Use generalizations here. *)

#[global] Instance is_mono_unmiff_round_up :
  IsMonoUnmiffRoundDown unmiff_round_up.
Proof.
  intros x y lb.
  unfold unmiff_round_down.
  destruct (lt_trichotomy (unmiff_round_up x) (unmiff_round_up y))
  as [la | [ea | la']].
  - apply le_neq. lia.
  - lia.
  - exfalso.
    destruct (eqb_spec x 0) as [ex | fx].
    subst x.
    rewrite <- fixed_miff in la'.
    rewrite sect_miff_round_up in la'.
    lia.
    destruct (eqb_spec y 0) as [ey | fy].
    subst y.
    lia.
    pose proof bound_retr_miff_round_up x ltac:(lia) as lx.
    pose proof bound_retr_miff_round_up y ltac:(lia) as ly.
    assert (l : miff (pred (unmiff_round_up x)) < miff (unmiff_round_up y))
    by lia.
    apply str_comono_miff in l.
    lia. Qed.

#[global] Instance is_surj_unmiff_round_up :
  IsSurjUnmiffRoundDown unmiff_round_up.
Proof.
  intros a.
  unfold unmiff_round_down.
  exists (miff a).
  rewrite sect_miff_round_up.
  reflexivity. Qed.

#[global] Instance is_contract_unmiff_round_up :
  IsContractUnmiffRoundDown unmiff_round_up.
Proof.
  intros a.
  unfold unmiff_round_down.
  pose proof inflate_miff a as l.
  apply (@mono_unmiff_round_down unmiff_round_up _) in l.
  setoid_rewrite sect_miff_round_up in l.
  apply l. Qed.

Lemma unmiff_round_up_elim (a : A) (b : B)
  (ll : miff (pred a) < b <= miff a) : unmiff_round_up b = a.
Proof.
  destruct (eqb_spec (unmiff_round_up b) (pred a)) as [eb | fb].
  - exfalso.
    apply (f_equal miff) in eb.
    pose proof bound_retr_miff_round_up b as lb.
    lia.
  - assert (lb : miff (pred a) <= b) by lia.
    apply (@mono_unmiff_round_down unmiff_round_up _) in lb.
    unfold unmiff_round_down in lb.
    rewrite sect_miff_round_up in lb.
    assert (lb1 : a <= unmiff_round_up b) by lia.
    clear fb lb.
    pose proof (@mono_unmiff_round_down unmiff_round_up _) b (miff a) ltac:(lia) as lb0.
    setoid_rewrite sect_miff_round_up in lb0.
    lia. Qed.

End Context.

Module RoundUpFromRoundDown.

Section Context.

Context `(IsUnmiffRoundDown).

Equations unmiff_round_up_def (b : B) : A :=
  unmiff_round_up_def N0 := 0;
  unmiff_round_up_def (Npos p) := succ (unmiff_round_down (Pos.pred_N p)).

Instance has_unmiff_round_up : HasUnmiffRoundUp := unmiff_round_up_def.

Instance is_sect_miff_round_up : IsSectMiffRoundUp unmiff_round_up.
Proof.
  intros a.
  unfold unmiff_round_up, has_unmiff_round_up.
  induction a as [| p e] using peano_ind.
  - rewrite fixed_miff.
    simp unmiff_round_up_def.
    reflexivity.
  - simp unmiff_round_up_def. Admitted.

Instance is_bound_retr_miff_round_up : IsBoundRetrMiffRoundUp unmiff_round_up.
Proof.
  intros b l.
  unfold unmiff_round_up, has_unmiff_round_up.
  pose proof bound_retr_miff_round_down b as ll. Admitted.

Instance is_unmiff_round_up : IsUnmiffRoundUp unmiff_round_up.
Proof. esplit; typeclasses eauto. Qed.

End Context.

#[export] Hint Resolve has_unmiff_round_up is_sect_miff_round_up
  is_bound_retr_miff_round_up is_unmiff_round_up : typeclass_instances.

End RoundUpFromRoundDown.

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

Lemma quotient (x y : B) (r : R x y) : pr x = pr y.
Proof.
  unfold pr.
  apply Spr1_inj.
  unfold Spr1.
  f_equal.
  destruct r as [a [lx ly]].
  rewrite (unmiff_round_down_elim _ a x),
  (unmiff_round_down_elim _ a y) by assumption.
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

(** TODO Now show the relative strength lattice. *)
