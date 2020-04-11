(* bad *)
From Coq Require Import
  Classes.RelationClasses.
From Maniunfold.Has.OneSorted Require Export
  OrderRelation.
From Maniunfold.Is Require Export
  Irreflexive Transitive.
From Maniunfold.ShouldHave Require Import
  OrderRelationNotations.

Class IsStrPartOrd (A : Type) (A_has_ord_rel : HasOrdRel A) : Prop := {
  A_ord_rel_is_irrefl :> IsIrrefl A ord_rel;
  A_ord_rel_is_trans :> IsTrans A ord_rel;
}.

Section Context.

Context {A : Type} `{is_str_part_ord : IsStrPartOrd A}.

Global Instance ord_rel_asymmetric : StrictOrder ord_rel | 0.
Proof. split; typeclasses eauto. Defined.

End Context.
