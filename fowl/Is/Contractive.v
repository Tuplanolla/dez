(** * Contractivity *)

From DEZ.Has Require Export
  Distance.

Class IsContractGen (A B C D E F : Type) (R : E -> F -> Prop)
  (f : A -> C) (g : B -> D) (m : C -> D -> E) (k : A -> B -> F) : Prop :=
  contract_gen (x : A) (y : B) : R (m (f x) (g y)) (k x y).

(** ** Contractive Function *)
(** ** Short Map *)

Fail Fail Class IsContract (A B C : Type)
  (R : C -> C -> Prop) (HdA : HasDist C A) (HdB : HasDist C B)
  (f : A -> B) : Prop :=
  is_contract_gen :> IsContractGen R f f dist dist.

Class IsContract (A B C : Type)
  (R : C -> C -> Prop) (HdA : HasDist C A) (HdB : HasDist C B)
  (f : A -> B) : Prop :=
  contract (x y : A) : R (dist (f x) (f y)) (dist x y).
