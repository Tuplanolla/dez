(** DEC Library Coq Implementation *)

From Coq Require Extraction.
From Coq Require ZArith.

Module Dec.

Import ZArith.
Import Z.
Open Scope Z_scope.

Notation "'(|' x '|)'" := (abs x).

Definition monkey_saddle (x y : Z) : Z := x * (x ^ 2 - 3 * y ^ 2).

(** Estimate via the Manhattan metric. *)
Definition monkey_saddle_bound_1 (x y : Z) : Z := ((|x|) + (|y|)) ^ 3.

(** Estimate via a scaled version of the Chebyshev metric. *)
Definition monkey_saddle_bound_2inf (x y : Z) : Z := 2 * max (|x|) (|y|) ^ 3.

Section Absolutes.

Lemma abs_le : forall x : Z,
  x <= (|x|).
Proof.
  intros x. destruct (abs_spec x) as [[Hl He] | [Hl He]].
  - apply (le_stepl (|x|) (|x|) x).
    + apply le_refl.
    + apply He.
  - apply lt_le_incl in Hl. apply (le_trans x 0 (|x|)).
    + apply Hl.
    + apply abs_nonneg. Qed.

Lemma abs_le_nonneg : forall x y : Z,
  (|x|) <= y -> 0 <= y.
Proof.
  intros x y Hl. apply (le_trans 0 (|x|) y).
  - apply abs_nonneg.
  - apply Hl. Qed.

Lemma abs_nonneg_le : forall x y : Z,
  x <= 0 -> x <= (|y|).
Proof.
  intros x y Hl. apply (le_trans x 0 (|y|)).
  - apply Hl.
  - apply abs_nonneg. Qed.

Lemma abs_le_abs : forall x y : Z,
  (|x|) <= y -> (|x|) <= (|y|).
Proof.
  intros x y Hl. apply (le_stepr (|x|) y (|y|)).
  - apply Hl.
  - apply eq_sym. apply abs_eq. apply (abs_le_nonneg x y). apply Hl. Qed.

Lemma abs_abs_le : forall x y : Z,
  (|x|) <= (|y|) -> x <= (|y|).
Proof.
  intros x y Hl. apply (le_trans x (|x|) (|y|)).
  - apply abs_le.
  - apply Hl. Qed.

End Absolutes.

Section Triangles.

Import Logic.

Check abs_triangle : forall x y : Z,
  (|x + y|) <= (|x|) + (|y|).

Lemma abs_opp_triangle : forall x y : Z,
  (|x - y|) <= (|x|) + (|y|).
Proof.
  intros x y. rewrite <- (add_opp_r x y). rewrite <- (abs_opp y).
  remember (- y) as z eqn : He. apply abs_triangle. Qed.

Check abs_sub_triangle : forall x y : Z,
  (|x|) - (|y|) <= (|x - y|).

Lemma abs_opp_sub_triangle : forall x y : Z,
  (|x|) - (|y|) <= (|x + y|).
Proof.
  intros x y. rewrite <- (abs_opp y). rewrite <- (sub_opp_r x y).
  remember (- y) as z eqn : He. apply abs_sub_triangle. Qed.

Example not_abs_add_sub : ~ forall x y : Z,
  (|x + y|) <= (|x - y|).
Proof.
  intros Hl. apply (Hl 1 1). apply eq_refl. Qed.

Example not_abs_sub_add : ~ forall x y : Z,
  (|x - y|) <= (|x + y|).
Proof.
  intros Hl. apply (Hl 1 (- 1)). apply eq_refl. Qed.

Lemma abs_le_sub : forall x y : Z,
  (|x|) - (|y|) <= (|(|x|) - (|y|)|).
Proof.
  intros x y. apply abs_le. Qed.

Lemma abs_le_final : forall x y : Z,
  (|x|) + (|y|) <= (|(|x|) + (|y|)|).
Proof.
  intros x y. apply abs_le. Qed.

Lemma abs_le_cofinal : forall x y : Z,
  (|(|x|) + (|y|)|) <= (|x|) + (|y|).
Proof.
  intros x y. rewrite abs_eq.
  - apply le_refl.
  - apply (le_trans 0 (|x - y|) ((|x|) + (|y|))).
    + apply abs_nonneg.
    + apply abs_opp_triangle. Qed.

Lemma abs_eq_final : forall x y : Z,
  (|x|) + (|y|) = (|(|x|) + (|y|)|).
Proof.
  intros x y. apply le_antisymm.
  - apply abs_le_final.
  - apply abs_le_cofinal. Qed.

Lemma abs_rev_triangle : forall x y : Z,
  (|(|x|) - (|y|)|) <= (|x - y|).
Proof.
  intros x y. Admitted.

Lemma abs_opp_rev_triangle : forall x y : Z,
  (|(|x|) - (|y|)|) <= (|x + y|).
Proof.
  intros x y. rewrite <- (abs_opp y). rewrite <- (sub_opp_r x y).
  remember (- y) as z eqn : He. apply abs_rev_triangle. Qed.

Lemma abs_trans_triangle : forall x y : Z,
  (|x|) - (|y|) <= (|x|) + (|y|).
Proof.
  intros x y. apply (le_trans ((|x|) - (|y|)) (|x - y|) ((|x|) + (|y|))).
  - apply abs_sub_triangle.
  - apply abs_opp_triangle. Qed.

Lemma what : forall x y : Z,
  (|(|x|) - (|y|)|) <= (|(|x|) + (|y|)|).
Proof.
  intros x y. eapply le_trans.
  - apply abs_opp_rev_triangle.
  - eapply le_trans.
    + apply abs_triangle.
    + apply abs_le_final. Qed.

End Triangles.

Lemma even_2 : Even 2.
Proof. now exists 1. Qed.

Theorem monkey_saddle_bounded_1 : forall a b x y : Z,
  (|x|) <= a -> (|y|) <= b ->
  (|monkey_saddle x y|) <= monkey_saddle_bound_1 a b.
Proof.
  unfold monkey_saddle, monkey_saddle_bound_1.
  intros a b x y Hlxa Hlyb.
  apply abs_le_abs in Hlxa. apply abs_le_abs in Hlyb.
  rewrite (abs_mul x _). eapply (le_trans _ _ _).
    + apply mul_le_mono_nonneg_l.
      * apply abs_nonneg.
      * rewrite (pow_even_abs x 2) by apply even_2.
        rewrite <- (abs_pow x 2).
        rewrite (pow_even_abs y 2) by apply even_2.
        rewrite <- (abs_pow y 2).
        rewrite <- (abs_eq 3) by omega.
        rewrite <- (abs_mul 3 _).
        apply what.
    + eapply (le_trans _ _ _).
      * apply mul_le_mono_nonneg_l.
        { apply abs_nonneg. }
        { apply abs_triangle. }
      * rewrite (mul_add_distr_l _ _ _).
        rewrite (abs_involutive _).
        rewrite (abs_involutive _).
        rewrite (abs_pow x 2).
        rewrite (abs_mul 3 _).
        rewrite (abs_pow y 2).
        rewrite (abs_eq 3) by omega.
        rewrite mul_shuffle3.
        rewrite mul_assoc.
        ring_simplify.
        (* Notice.
        (|x|) ^ 3                         + 3 * (|x|) * (|y|) ^ 2             <=
        (|a|) ^ 3 + 3 * (|a|) ^ 2 * (|b|) + 3 * (|a|) * (|b|) ^ 2 + (|b|) ^ 3
        *)
        eapply le_trans.
        apply add_le_mono_r.
        apply pow_le_mono_l. split. apply abs_nonneg. apply Hlxa.
        (* Now we got x into a. *)
        repeat rewrite <- add_assoc.
        Search (?y <= ?z <-> ?x + ?y <= ?x + ?z).
        apply add_le_mono_l.
        repeat rewrite add_assoc.
        (* Now we got rid of them. *)
        repeat rewrite <- add_assoc.
        rewrite add_shuffle3.
        repeat rewrite add_assoc.
        (* Now we got rid of them. *)
        eapply le_trans.
        apply mul_le_mono_nonneg_r.
        rewrite <- abs_pow. apply abs_nonneg.
        apply mul_le_mono_nonneg_l. omega. apply Hlxa.
        (* Now we got x into a. *)
        eapply le_trans.
        apply mul_le_mono_nonneg_l.
        rewrite <- (abs_eq 3). rewrite <- abs_mul. apply abs_nonneg. omega.
        apply pow_le_mono_l. split. apply abs_nonneg. apply Hlyb.
        (* Now we got y into b. *)
        repeat rewrite <- add_assoc.
        match goal with |- ?x <= ?y => rewrite <- (add_0_r x) at 1 end.
        apply add_le_mono_l.
        repeat rewrite add_assoc.
        (* Now we got rid of them. *)
        repeat rewrite <- abs_pow. rewrite <- (abs_eq 3) at 1. 2: omega.
        repeat rewrite <- abs_mul.
        eapply le_trans. 2: apply abs_triangle. apply abs_nonneg. Qed.

Theorem monkey_saddle_bounded_2inf : forall a b x y : Z,
  (|x|) <= a -> (|y|) <= b ->
  (|monkey_saddle x y|) <= monkey_saddle_bound_2inf a b.
Proof.
  unfold monkey_saddle, monkey_saddle_bound_2inf.
  intros a b x y Hlxa Hlyb.
  apply abs_le_abs in Hlxa. apply abs_le_abs in Hlyb.
  destruct (max_spec (|a|) (|b|)) as [[Hlab He] | [Hlba He]];
  [apply lt_le_incl in Hlab |]; rewrite He; clear He.
  - assert (Hlxb : (|x|) <= (|b|)) by omega.
    admit.
  - assert (Hlya : (|y|) <= (|a|)) by omega.
    admit. Admitted.

End Dec.

Extraction "spec.ml" Dec.
