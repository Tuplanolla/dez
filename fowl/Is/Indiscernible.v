(** * Identity of Indiscernibles *)

From DEZ.Has Require Export
  NullaryOperation Distance EquivalenceRelation.
From DEZ.ShouldHave Require Import
  AdditiveNotations EquivalenceNotations.

Class IsIndiscGen (A B C D E F : Type) (X : E -> F -> Prop)
  (x : D) (k : C -> D -> E) (m : A -> B -> F) (n : A -> B -> C) : Prop :=
  indisc_gen (y : A) (z : B) : X (k (n y z) x) (m y z).

Class IsIndisc (A B : Type) (X : HasEqRel A) (S : HasEqRel B)
  (Hx : HasNullOp A) (Hd : HasDist A B) : Prop :=
  indisc (x y : B) : dist x y == 0 <-> x == y.

Check IsIndiscGen _<->_ 0 _==_ _==_ dist.
