(** * Tactics for Using Typeclasses *)

From DEZ Require Export
  Init.

(** The idea behind this tactic is to be able to replace terms
    with the corresponding operational classes.
    If you write

<<
Ltac note := progress (
  denote X with (equiv_rel (A := A));
  denote k with (bin_op (A := A))).
>>

    and have the appropriate notations imported,
    then [note] will replace [X (k x y) z] with [x + y == y].
    More explicitly, it will replace [X (k x y) z] with
    [@equiv_rel A grp_has_equiv_rel (@bin_op A grp_has_bin_op x y) z].

    The repetition is there to prevent a problem with recursion.
    You could change [a = []], which is [@eq (list A) a (@nil A)]
    into [@eq (list A) (@enum A a) (@nil A)],
    but subsequent invocations would change it
    into [@eq (list A) (@enum A (@enum A a)) (@nil A)],
    which would break rewriting. *)

#[deprecated (since="now")]
Tactic Notation "denote" uconstr(x) "with" uconstr(y) :=
  repeat change y with x in *; try change x with y in *.

(** TODO Document this new form that allows writing the following.

<<
Ltac notations f := progress (
  f X (equiv_rel (A := A));
  f k (bin_op (A := A))).
>> *)

Ltac disabled x y :=
  repeat change y with x in *.

Ltac enabled x y :=
  repeat change y with x in *;
  try change x with y in *.
