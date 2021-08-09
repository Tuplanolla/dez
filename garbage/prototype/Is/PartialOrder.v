From DEZ.Has Require Export
  EquivalenceRelation OrderRelation.
From DEZ.Is Require Export
  Preorder Antisymmetric.

Class IsPartialOrder {A : Type} {has_eqv : HasEqv A}
  (has_ord : HasOrd A) : Prop := {
  ord_is_preorder :> IsPreorder ord;
  ord_is_antisymmetric :> IsAntisymmetric ord;
}.

Section Context.

Context {A : Type} `{is_partial_order : IsPartialOrder A}.

Global Instance eqv_ord_partial_order : PartialOrder eqv ord | 0 := {
  partial_order_equivalence := _;
}.
Proof.
  cbv [relation_equivalence relation_conjunction].
  cbv [predicate_equivalence predicate_intersection].
  cbv [pointwise_lifting pointwise_extension].
  cbv [flip].
  intros x y. split.
  - intros Hxy. rewrite Hxy. split; reflexivity.
  - intros [Hxy Hyx]. apply antisymmetric; assumption. Qed.

End Context.
