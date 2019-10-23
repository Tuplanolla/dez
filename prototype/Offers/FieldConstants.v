From Maniunfold.Has Require Export
  FieldOperations FieldIdentities FieldInverses.
From Maniunfold.ShouldHave Require Export
  FieldNotations.

Section Context.

Context {A : Type} {has_add : HasAdd A} {has_one : HasOne A}.

(** Semirings only come with zero and one,
    but we can construct any other natural number
    by adding or multiplying them together.
    The optimal way to do this is quite complicated,
    as demonstrated in OEIS sequence A005245.
    However, we can make the construction more manageable
    by limiting ourselves to just addition.
    The following definitions produce an optimal reduction tree (one of many)
    for constructing the first few natural numbers from additions. *)

Definition two : A := one + one.
Definition three : A := two + one.
Definition four : A := two + two.
Definition five : A := four + one.
Definition six : A := four + two.
Definition seven : A := four + three.
Definition eight : A := four + four.
Definition nine : A := eight + one.

End Context.
