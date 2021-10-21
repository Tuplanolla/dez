(** * Contractivity *)

From DEZ.Has Require Export
  Distance.

Class IsContractGen (A B C D E F : Type) (X : E -> F -> Prop)
  (f : A -> C) (g : B -> D) (m : C -> D -> E) (k : A -> B -> F) : Prop :=
  contract_gen (x : A) (y : B) : X (m (f x) (g y)) (k x y).

(** ** Contractive Function *)
(** ** Short Map *)

Fail Fail Class IsContract (A B C : Type)
  (X : C -> C -> Prop) (HdA : HasDist C A) (HdB : HasDist C B)
  (f : A -> B) : Prop :=
  is_contract_gen :> IsContractGen X f f dist dist.

Class IsContract (A B C : Type)
  (X : C -> C -> Prop) (HdA : HasDist C A) (HdB : HasDist C B)
  (f : A -> B) : Prop :=
  contract (x y : A) : X (dist (f x) (f y)) (dist x y).
