From Maniunfold.Has Require Export
  OneSorted.OrderRelation.

Reserved Notation "x '<=' y" (at level 70, no associativity).
Reserved Notation "'_<=_'" (at level 0, no associativity).
Reserved Notation "x '</=' y" (at level 70, no associativity).
Reserved Notation "'_</=_'" (at level 0, no associativity).

Declare Scope rel_scope.

Delimit Scope rel_scope with rel.

Open Scope rel_scope.

Notation "x '<=' y" := (ord_rel x y) : rel_scope.
Notation "'_<=_'" := ord_rel (only parsing) : rel_scope.
Notation "x '</=' y" := (not (ord_rel x y)) : rel_scope.
Notation "'_</=_'" := (fun x y : _ => not (ord_rel x y))
  (only parsing) : rel_scope.
