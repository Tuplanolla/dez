(** * Bijectivity *)

From DEZ.Is Require Export
  Injective Surjective Equivalence Proper Isomorphic.

(** ** Bijective Unary Function *)
(** ** Isomorphism *)

Class IsBijUnFn (A B : Type) (X : A -> A -> Prop) (Y : B -> B -> Prop)
  (f : A -> B) : Prop := {
  bij_un_fn_is_inj_un_fn :> IsInjUnFn X Y f;
  bij_un_fn_is_surj_un_fn :> IsSurjUnFn Y f;
}.

(** ** Bijective Unary Operation *)

Class IsBij (A : Type) (X : A -> A -> Prop)
  (f : A -> A) : Prop := {
  bij_is_inj :> IsInj X f;
  bij_is_surj :> IsSurj X f;
}.

Section Context.

Context (A B : Type) (X : A -> A -> Prop) (Y : B -> B -> Prop)
  (f : A -> B) (g : B -> A)
  `{!IsEquiv X} `{!IsEquiv Y}
  `{!IsProper (X ==> Y) f} `{!IsProper (Y ==> X) g}.

(** An isomorphism is bijective. *)

#[export] Instance iso_is_bij_un_fn
  `{!IsIso X Y f g} : IsBijUnFn X Y f.
Proof.
  split.
  - intros x y a. rewrite <- (sect x), <- (sect y). rewrite a. reflexivity.
  - intros y. exists (g y). rewrite sect. reflexivity.
Qed.

End Context.
