From Maniunfold.Has Require Import
  Relation.

Delimit Scope equivalence_relation_scope with equivalence_relation.

Open Scope equivalence_relation_scope.

(** We do not use the abbreviation [eq],
    because it is reserved for propositional equality. *)
Class HasEqv (A : Type) : Type := eqv : A -> A -> Prop.

Typeclasses Transparent HasEqv.

Reserved Notation "x '==' y" (at level 70, no associativity).
Notation "x '==' y" := (eqv x y) : equivalence_relation_scope.

Reserved Notation "x '=/=' y" (at level 70, no associativity).
Notation "x '=/=' y" := (~ x == y) : equivalence_relation_scope.

Section Context.

Context {A : Type} {has_eqv : HasEqv A}.

Global Instance : HasRel A := eqv.

End Context.
