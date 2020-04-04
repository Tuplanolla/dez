From Coq Require Import
  NArith.NArith.
From Maniunfold Require Export
  Init.

Class HasCard (A : Type) : Type := card : N.

Arguments card _ : clear implicits.
Arguments card _ {_}.

Typeclasses Transparent HasCard.