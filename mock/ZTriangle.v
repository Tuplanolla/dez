(** DEC Library Coq Implementation *)

From Coq Require ZArith.

Module Export Inequalities.

Set Warnings "-undo-batch-mode".

Import ZArith.
Import Z.

Open Scope Z_scope.

Notation "'(|' x '|)'" := (abs x).

Lemma le_refl : forall x : Z,
  x <= x.
Proof.
  intros x. apply le_refl. Qed.

Corollary le_refl_add : forall x y : Z,
  x + y <= x + y.
Proof. intros x y. apply le_refl. Qed.

Corollary le_refl_sub : forall x y : Z,
  x - y <= x - y.
Proof. intros x y. apply le_refl. Qed.

Corollary le_refl_abs_add : forall x y : Z,
  (|x + y|) <= (|x + y|).
Proof. intros x y. apply le_refl. Qed.

Corollary le_refl_abs_sub : forall x y : Z,
  (|x - y|) <= (|x - y|).
Proof. intros x y. apply le_refl. Qed.

Corollary le_refl_add_abs : forall x y : Z,
  (|x|) + (|y|) <= (|x|) + (|y|).
Proof. intros x y. apply le_refl. Qed.

Corollary le_refl_sub_abs : forall x y : Z,
  (|x|) - (|y|) <= (|x|) - (|y|).
Proof. intros x y. apply le_refl. Qed.

Corollary le_refl_abs_add_abs : forall x y : Z,
  (|(|x|) + (|y|)|) <= (|(|x|) + (|y|)|).
Proof. intros x y. apply le_refl. Qed.

Corollary le_refl_abs_sub_abs : forall x y : Z,
  (|(|x|) - (|y|)|) <= (|(|x|) - (|y|)|).
Proof. intros x y. apply le_refl. Qed.

Lemma le_abs : forall x : Z,
  x <= (|x|).
Proof.
  intros x. apply abs_le. apply le_refl. Qed.

Corollary le_abs_add : forall x y : Z,
  x + y <= (|x + y|).
Proof. intros x y. apply le_abs. Qed.

Corollary le_abs_sub : forall x y : Z,
  x - y <= (|x - y|).
Proof. intros x y. apply le_abs. Qed.

Corollary le_abs_add_abs : forall x y : Z,
  (|x|) + (|y|) <= (|(|x|) + (|y|)|).
Proof. intros x y. apply le_abs. Qed.

Corollary le_abs_sub_abs : forall x y : Z,
  (|x|) - (|y|) <= (|(|x|) - (|y|)|).
Proof. intros x y. apply le_abs. Qed.

Theorem abs_triangle : forall x y : Z,
  (|x + y|) <= (|x|) + (|y|).
Proof.
  intros x y.
  destruct (abs_spec (x + y)) as [[_ Hexy] | [_ Hexy]].
  - rewrite Hexy. destruct (abs_spec x) as [[_ Hex] | [_ Hex]].
    + rewrite Hex.
      apply add_le_mono_l. apply le_abs.
    + destruct (abs_spec y) as [[_ Hey] | [_ Hey]].
      * rewrite Hey. apply add_le_mono_r. apply le_abs.
      * apply add_le_mono.
        { apply le_abs. }
        { apply le_abs. }
  - rewrite Hexy. destruct (abs_spec x) as [[_ Hex] | [_ Hex]].
    + destruct (abs_spec y) as [[_ Hey] | [_ Hey]].
      * rewrite (opp_add_distr x y). rewrite <- (abs_opp x), <- (abs_opp y).
        apply add_le_mono.
        { apply le_abs. }
        { apply le_abs. }
      * rewrite Hey. rewrite (opp_add_distr x y). rewrite <- (abs_opp x).
        apply add_le_mono_r. apply le_abs.
    + rewrite Hex. rewrite (opp_add_distr x y). rewrite <- (abs_opp y).
      apply add_le_mono_l. apply le_abs. Qed.

Theorem abs_opp_triangle : forall x y : Z,
  (|x - y|) <= (|x|) + (|y|).
Proof.
  intros x y.
  rewrite <- (add_opp_r x y). rewrite <- (abs_opp y).
  remember (- y) as z eqn : Hez.
  apply abs_triangle. Qed.

Theorem abs_sub_triangle : forall x y : Z,
  (|x|) - (|y|) <= (|x - y|).
Proof.
  intros x y. apply (add_le_mono_r _ _ (|y|)).
  rewrite (sub_add _ _). remember (x - y) as z eqn : Hez.
  rewrite <- (sub_add y x). rewrite <- Hez.
  apply abs_triangle. Qed.

Theorem abs_opp_sub_triangle : forall x y : Z,
  (|x|) - (|y|) <= (|x + y|).
Proof.
  intros x y.
  rewrite <- (abs_opp y). rewrite <- (sub_opp_r x y).
  remember (- y) as z eqn : Hez.
  apply abs_sub_triangle. Qed.

Lemma abs_sub_comm : forall x y : Z,
  (|x - y|) = (|y - x|).
Proof.
  intros x y. destruct (abs_spec (x - y)) as [[Hlxy Hexy] | [Hlxy Hexy]].
  - rewrite Hexy. rewrite <- (add_opp_l x y). rewrite <- (opp_sub_distr y x).
    apply eq_sym. apply abs_neq.
    apply (le_sub_le_add_l y x 0). rewrite (add_0_r x).
    rewrite <- (add_0_r y). apply (le_add_le_sub_l y x 0).
    apply Hlxy.
  - apply lt_le_incl in Hlxy.
    rewrite Hexy. rewrite (opp_sub_distr x y). rewrite (add_opp_l y x).
    apply eq_sym. apply abs_eq.
    apply (le_add_le_sub_l x y 0). rewrite (add_0_r x).
    rewrite <- (add_0_r y). apply (le_sub_le_add_l x y 0).
    apply Hlxy. Qed.

Theorem abs_rev_triangle : forall x y : Z,
  (|(|x|) - (|y|)|) <= (|x - y|).
Proof.
  intros x y. apply abs_le. split.
  - apply opp_le_mono.
    rewrite (opp_sub_distr _ _). rewrite (add_opp_l _ _).
    rewrite (opp_involutive _). rewrite (abs_sub_comm x y).
    apply abs_sub_triangle.
  - apply abs_sub_triangle. Qed.

Theorem abs_opp_rev_triangle : forall x y : Z,
  (|(|x|) - (|y|)|) <= (|x + y|).
Proof.
  intros x y.
  rewrite <- (abs_opp y). rewrite <- (sub_opp_r x y).
  remember (- y) as z eqn : Hez.
  apply abs_rev_triangle. Qed.

Theorem abs_quadrangle : forall x y : Z,
  (|x|) - (|y|) <= (|x|) + (|y|).
Proof.
  intros x y. apply (le_trans _ (|x - y|) _).
  - apply abs_sub_triangle.
  - apply abs_opp_triangle.
    all: fail "not done". Restart.
  intros x y. apply (le_trans _ (|x + y|) _).
  - apply abs_opp_sub_triangle.
  - apply abs_triangle. Qed.

Theorem abs_rev_quadrangle : forall x y : Z,
  (|(|x|) - (|y|)|) <= (|x|) + (|y|).
Proof.
  intros x y. apply (le_trans _ (|x - y|) _).
  - apply abs_rev_triangle.
  - apply abs_opp_triangle.
    all: fail "not done". Restart.
  intros x y. apply (le_trans _ (|x + y|) _).
  - apply abs_opp_rev_triangle.
  - apply abs_triangle. Qed.

Theorem abs_pre_triangle : forall x y : Z,
  x + y <= (|x|) + (|y|).
Proof.
  intros x y. apply (le_trans _ (|x + y|) _).
  - apply le_abs.
  - apply abs_triangle. Qed.

Theorem abs_opp_pre_triangle : forall x y : Z,
  x - y <= (|x|) + (|y|).
Proof.
  intros x y.
  rewrite <- (add_opp_r x y). rewrite <- (abs_opp y).
  remember (- y) as z eqn : Hez.
  apply abs_pre_triangle. Qed.

Theorem abs_le_add_abs : forall x y : Z,
  (|(|x|) + (|y|)|) <= (|x|) + (|y|).
Proof.
  intros x y. apply (le_stepl ((|x|) + (|y|)) _ _).
  - apply le_refl.
  - apply eq_sym. apply abs_eq. apply (le_trans _ (|x + y|) _).
    + apply abs_nonneg.
    + apply abs_triangle. Qed.

Theorem abs_triangle_abs : forall x y : Z,
  (|x + y|) <= (|(|x|) + (|y|)|).
Proof.
  intros x y. apply (le_trans _ ((|x|) + (|y|)) _).
  - apply abs_triangle.
  - apply le_abs. Qed.

Theorem abs_opp_triangle_abs : forall x y : Z,
  (|x - y|) <= (|(|x|) + (|y|)|).
Proof.
  intros x y. apply (le_trans _ ((|x|) + (|y|)) _).
  - apply abs_opp_triangle.
  - apply le_abs. Qed.

Theorem abs_quadrangle_abs : forall x y : Z,
  (|x|) - (|y|) <= (|(|x|) + (|y|)|).
Proof.
  intros x y. apply (le_trans _ ((|x|) + (|y|)) _).
  - apply abs_quadrangle.
  - apply le_abs. Qed.

Theorem abs_rev_quadrangle_abs : forall x y : Z,
  (|(|x|) - (|y|)|) <= (|(|x|) + (|y|)|).
Proof.
  intros x y. apply (le_trans _ ((|x|) + (|y|)) _).
  - apply abs_rev_quadrangle.
  - apply le_abs. Qed.

Theorem abs_pre_triangle_abs : forall x y : Z,
  x + y <= (|(|x|) + (|y|)|).
Proof.
  intros x y. apply (le_trans _ ((|x|) + (|y|)) _).
  - apply abs_pre_triangle.
  - apply le_abs. Qed.

Theorem abs_opp_pre_triangle_abs : forall x y : Z,
  x - y <= (|(|x|) + (|y|)|).
Proof.
  intros x y.
  rewrite <- (add_opp_r x y). rewrite <- (abs_opp y).
  remember (- y) as z eqn : Hez.
  apply abs_pre_triangle_abs. Qed.

End Inequalities.
