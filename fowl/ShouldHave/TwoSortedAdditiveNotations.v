From DEZ.Has Require Import
  UnaryOperation
  Action Torsion.

(** We do not open [l_mod_scope] or [r_mod_scope],
    because we do not want to favor one over the other.
    The same applies to [l_subgrp_scope] and [r_subgrp_scope]. *)

Declare Scope l_mod_scope.

Delimit Scope l_mod_scope with l_mod.

Notation "a '+' x" := (act_l a x) : l_mod_scope.
Notation "a '-' x" := (act_l a (un_op x)) : l_mod_scope.

Notation "'_+_'" := act_l (only parsing) : l_mod_scope.
Notation "'_-_'" := (fun a x : _ => act_l a (un_op x))
  (only parsing) : l_mod_scope.

Declare Scope r_mod_scope.

Delimit Scope r_mod_scope with r_mod.

Notation "x '+' a" := (act_r x a) : r_mod_scope.
Notation "x '-' a" := (act_r x (un_op a)) : r_mod_scope.

Notation "'_+_'" := act_r (only parsing) : r_mod_scope.
Notation "'_-_'" := (fun x a : _ => act_r x (un_op a))
  (only parsing) : r_mod_scope.

Declare Scope l_subgrp_scope.

Delimit Scope l_subgrp_scope with l_subgrp.

Notation "x '-' y" := (tor_l x y) : l_subgrp_scope.

Notation "'_-_'" := tor_l (only parsing) : l_subgrp_scope.

Declare Scope r_subgrp_scope.

Delimit Scope r_subgrp_scope with r_subgrp.

Notation "x '-' y" := (tor_r x y) : r_subgrp_scope.

Notation "'_-_'" := tor_r (only parsing) : r_subgrp_scope.
