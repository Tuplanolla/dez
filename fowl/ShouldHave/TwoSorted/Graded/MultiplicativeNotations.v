From Maniunfold.Has Require Export
  OneSorted.Graded.UnaryOperation
  TwoSorted.Graded.LeftAction TwoSorted.Graded.RightAction.

(** We can only assert these reserved notations,
    because they are fixed by the standard library. *)

Reserved Notation "x '*' y" (at level 40, left associativity).
Reserved Notation "x '/' y" (at level 40, left associativity).

Reserved Notation "'_*_'" (at level 0, no associativity).
Reserved Notation "'_/_'" (at level 0, no associativity).

(** We do not open [grd_l_mod_scope] or [grd_r_mod_scope],
    because we do not want to favor one over the other. *)

Declare Scope grd_l_mod_scope.

Delimit Scope grd_l_mod_scope with grd_l_mod.

Notation "a '*' x" := (grd_l_act _ _ a x) : grd_l_mod_scope.
Notation "'_*_'" := (grd_l_act _ _) (only parsing) : grd_l_mod_scope.
Notation "a '/' x" := (grd_l_act _ _ a (grd_un_op _ x)) : grd_l_mod_scope.
Notation "'_/_'" := (fun a x : _ => grd_l_act _ _ a (grd_un_op _ x))
  (only parsing) : grd_l_mod_scope.

Declare Scope grd_r_mod_scope.

Delimit Scope grd_r_mod_scope with grd_r_mod.

Notation "x '*' a" := (grd_r_act _ _ x a) : grd_r_mod_scope.
Notation "'_*_'" := (grd_r_act _ _) (only parsing) : grd_r_mod_scope.
Notation "x '/' a" := (grd_r_act _ _ x (grd_un_op _ a)) : grd_r_mod_scope.
Notation "'_/_'" := (fun x a : _ => grd_r_act _ _ x (grd_un_op _ a))
  (only parsing) : grd_r_mod_scope.
