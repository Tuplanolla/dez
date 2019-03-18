(** DEC Library Coq Implementation *)

Set Warnings "-extraction-logical-axiom".

From Coq Require Extraction.
From Coq Require ZArith.
From DEC Require ZTriangle.

Module Dec.

Import ZArith.
Import Z.
Import ZTriangle.
Open Scope Z_scope.

Definition monkey_saddle (x y : Z) : Z := x * (x ^ 2 - 3 * y ^ 2).

(** This estimate is based on the Manhattan metric. *)
Definition monkey_saddle_bound_1 (x y : Z) : Z := ((|x|) + (|y|)) ^ 3.

(** This estimate is based on a scaled version of the Chebyshev metric. *)
Definition monkey_saddle_bound_2inf (x y : Z) : Z := 2 * max (|x|) (|y|) ^ 3.

Lemma abs_le_nonneg : forall x y : Z,
  (|x|) <= y -> 0 <= y.
Proof.
  intros x y Hl. apply (le_trans _ (|x|) _).
  - apply abs_nonneg.
  - apply Hl. Qed.

Lemma abs_nonneg_le : forall x y : Z,
  x <= 0 -> x <= (|y|).
Proof.
  intros x y Hl. apply (le_trans _ 0 _).
  - apply Hl.
  - apply abs_nonneg. Qed.

Lemma abs_le_abs : forall x y : Z,
  (|x|) <= y -> (|x|) <= (|y|).
Proof.
  intros x y Hl. apply (le_stepr _ y _).
  - apply Hl.
  - apply eq_sym. apply abs_eq. apply (abs_le_nonneg x _). apply Hl. Qed.

Lemma abs_abs_le : forall x y : Z,
  (|x|) <= (|y|) -> x <= (|y|).
Proof.
  intros x y Hl. apply (le_trans _ (|x|) _).
  - apply abs_le. apply le_refl.
  - apply Hl. Qed.

Fact Even_2 : Even 2.
Proof. now exists 1. Qed.

Fact le_0_3 : 0 <= 3.
Proof. intros He. inversion He. Qed.

Theorem monkey_saddle_bounded_1 : forall a b x y : Z,
  (|x|) <= a -> (|y|) <= b ->
  (|monkey_saddle x y|) <= monkey_saddle_bound_1 a b.
Proof with auto using Even_2, le_0_3.
  unfold monkey_saddle, monkey_saddle_bound_1.
  intros a b x y Hlxa Hlyb.
  apply abs_le_abs in Hlxa. apply abs_le_abs in Hlyb.
  (** We work through the proof in a pedagogical manner. *)
  rewrite (abs_mul x _).
  (** We weaken the estimate by replacing [sub] with [add]. *)
  apply (le_trans _ ((|x|) * (|x ^ 2 + 3 * y ^ 2|)) _).
  { apply mul_le_mono_nonneg_l.
    - apply abs_nonneg.
    - rewrite (pow_even_abs x 2)...
      rewrite <- (abs_pow x 2). rewrite <- (abs_eq 3)...
      rewrite (pow_even_abs y 2)...
      rewrite <- (abs_pow y 2). rewrite <- (abs_mul 3 _).
      apply abs_rev_quadrangle_abs. }
  (** We weaken the estimate further by distributing [abs] over [add]. *)
  apply (le_trans _ ((|x|) * ((|x ^ 2|) + (|3 * y ^ 2|))) _).
  { apply mul_le_mono_nonneg_l.
    - apply abs_nonneg.
    - apply abs_triangle. }
  (** We expand the left side manually. *)
  rewrite (mul_add_distr_l _ _ _). rewrite (abs_pow x 2).
  rewrite <- (pow_succ_r _ 2); replace (succ 2) with 3...
  rewrite (abs_mul 3 _). rewrite (abs_eq 3)...
  rewrite (abs_pow y 2). rewrite (mul_shuffle3 _ 3 _).
  rewrite (mul_assoc 3 _ _).
  (** We expand the right side automatically. *)
  ring_simplify.
  (** We eliminate [(|x|) ^ 3] and [(|a|) ^ 3]. *)
  repeat rewrite <- (add_assoc _ _ _).
  apply add_le_mono.
  { apply pow_le_mono_l. split...
    apply abs_nonneg. }
  (** We eliminate [3 * (|x|) * (|y|) ^ 2] and [3 * (|a|) * (|b|) ^ 2]. *)
  rewrite (add_shuffle3 _ _ _).
  match goal with |- ?x <= ?y => rewrite <- (add_0_r x) end.
  apply add_le_mono.
  { apply mul_le_mono_nonneg.
    - rewrite <- (abs_mul 3 _).
      apply abs_nonneg.
    - apply mul_le_mono_nonneg_l...
    - rewrite <- (abs_pow y 2).
      apply abs_nonneg.
    - apply pow_le_mono_l. split...
      apply abs_nonneg. }
  (** We resolve that [3 * (|a|) ^ 2 * (|b|) + (|b|) ^ 3] is nonnegative. *)
  rewrite <- (abs_eq 3) at 1...
  rewrite <- (abs_pow a 2). rewrite <- (abs_mul 3 _).
  rewrite <- (abs_mul _ b). rewrite <- (abs_pow b 3).
  { apply (le_trans _ (|(|3 * a ^ 2 * b|) + (|b ^ 3|)|) _).
    - apply abs_nonneg.
    - apply abs_le_add_abs. } Qed.

(** We omit most of this proof to demonstrate its effect on the extraction. *)
Theorem monkey_saddle_bounded_2inf : forall a b x y : Z,
  (|x|) <= a -> (|y|) <= b ->
  (|monkey_saddle x y|) <= monkey_saddle_bound_2inf a b.
Proof.
  unfold monkey_saddle, monkey_saddle_bound_2inf.
  intros a b x y Hlxa Hlyb.
  apply abs_le_abs in Hlxa. apply abs_le_abs in Hlyb.
  destruct (max_spec (|a|) (|b|)) as [[Hlab He] | [Hlba He]];
  [apply lt_le_incl in Hlab |]; rewrite He; clear He.
  - assert (Hlxb : (|x|) <= (|b|)).
    + apply (le_trans _ (|a|) _).
      * apply Hlxa.
      * apply Hlab.
    + admit.
  - assert (Hlya : (|y|) <= (|a|)).
    + apply (le_trans _ (|b|) _).
      * apply Hlyb.
      * apply Hlba.
    + admit. Admitted.

End Dec.

Extraction "spec.ml" Dec.
