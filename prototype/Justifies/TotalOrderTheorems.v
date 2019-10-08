From Maniunfold.Has Require Import Relation EquivalenceRelation OrderRelation.
From Maniunfold.Is Require Import Reflexive PartialOrder TotalOrder.

Theorem ord_reflexive : forall {A : Type} `{is_total_order : IsTotalOrder A},
  forall x : A, x <= x.
Proof.
  intros A ? ? ? x.
  destruct (ord_is_connex x x) as [p | p].
  - specialize (p : x <= x) as p. apply p.
  - specialize (p : x <= x) as p. apply p. Qed.

Instance ord_is_reflexive {A : Type} `{is_total_order : IsTotalOrder A} :
  IsReflexive A (has_rel := ord) := ord_reflexive.

Instance total_order_is_partial_order {A : Type}
  `{is_total_order : IsTotalOrder A} : IsPartialOrder A := {}.
