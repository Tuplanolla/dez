(** DEC Library Coq Implementation *)

From Coq Require Extraction.
From Coq Require ZArith.

Module Dec.

Import ZArith.
Import Z.
Open Scope Z_scope.

Definition monkey_saddle (x y : Z) : Z := x * (x ^ 2 - 3 * y ^ 2).

Notation "'(|' x '|)'" := (abs x).

Theorem monkey_saddle_overflow : forall x y z : Z,
  (|x * (x ^ 2 - 3 * y ^ 2)|) <= z ->
  (|x|) <= z /\ (|x ^ 2 - 3 * y ^ 2|) <= z /\
  (|x ^ 2|) <= z /\ (|3 * y ^ 2|) <= z /\
  (|x|) <= z /\ (|2|) <= z /\ (|3|) <= z /\ (|y ^ 2|) <= z /\
  (|y|) <= z /\ (|2|) <= z.
Proof.
  intros x y z Hl. repeat split.
  - admit.
  - destruct (abs_spec x) as [[Hl0 He0] | [Hl0 He0]].
    (* pose proof Ztrichotomy_inf x 0 as Hs. destruct Hs as [[Hl0 | He0] | Hg0]. *)
    rewrite abs_mul in Hl. rewrite He0 in Hl.
    eapply le_trans. 2: apply Hl.
    rewrite (mul_comm x _). eapply le_mul_diag_r.
    admit. admit.
    rewrite abs_mul in Hl. rewrite He0 in Hl. admit.
  - admit. Admitted.

End Dec.

Extraction "spec.ml" Dec.
