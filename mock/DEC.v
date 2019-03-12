From Coq Require Extraction.
From Coq Require ZArith.

Module DEC.

Import ZArith.
Open Scope Z_scope.

Definition crunch (x y : Z) : Z := x ^ 3 - 3 * x * y ^ 2.

Compute crunch 42 13.

End DEC.

Extraction "dec.ml" DEC.
