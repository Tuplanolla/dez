From Coq Require Import
  Classes.RelationClasses.
From Maniunfold.Has Require Export
  OneSorted.OrderRelation.
From Maniunfold.Is Require Export
  Reflexive Transitive.

Class IsPreord {A : Type} (has_ord_rel : HasOrdRel A) : Prop := {
  ord_rel_is_refl :> IsRefl ord_rel;
  ord_rel_is_trans :> IsTrans ord_rel;
}.

Section Context.

Context {A : Type} `{is_preord : IsPreord A}.

Global Instance ord_rel_pre_order : PreOrder ord_rel | 0.
Proof. constructor; typeclasses eauto. Qed.

End Context.
