(** * Bijectivity *)

From DEZ.Is Require Export
  Injective Surjective.

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
