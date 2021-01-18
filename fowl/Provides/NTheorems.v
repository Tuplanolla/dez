(** Lemmas and instances for [N]. *)

From Coq Require Import
  Lia NArith.NArith.
From Maniunfold Require Import
  DatatypeTactics RewritingTactics.
From Maniunfold.Is Require Export
  OneSorted.AbelianGroup OneSorted.CommutativeSemigroup
  OneSorted.CommutativeMonoid OneSorted.CommutativeSemiring.

Module N.

(** We extend the [N] module here. *)

Export BinNat.N.

Local Open Scope N_scope.

(** A specialization of [seq] for [N]. *)

Fixpoint seq (n : N) (p : nat) : list N :=
  match p with
  | O => nil
  | S q => n :: seq (succ n) q
  end.

(** Division, rounding down. *)

Definition pos_div (n : N) (p : positive) : N :=
  match n with
  | N0 => 0
  | Npos q => fst (pos_div_eucl q (Npos p))
  end.

Arguments pos_div !_ _.

(** Division, rounding up. *)

Definition pos_div_up (n : N) (p : positive) : N :=
  match n with
  | N0 => 0
  | Npos q =>
    match peanoView q with
    | PeanoOne => 1
    | PeanoSucc r _ => succ (fst (pos_div_eucl r (Npos p)))
    end
  end.

Arguments pos_div_up !_ _ : simpl nomatch.

(** Binary logarithm, rounding down.
    Sequence A000523. *)

Fixpoint pos_log2 (n : positive) : N :=
  match n with
  | xI p => succ (pos_log2 p)
  | xO p => succ (pos_log2 p)
  | xH => 0
  end.

Arguments pos_log2 !_.

(** Binary logarithm, rounding up.
    Sequence A029837. *)

Definition pos_log2_up (n : positive) : N :=
  match peanoView n with
  | PeanoOne => 0
  | PeanoSucc p _ => succ (pos_log2 p)
  end.

Arguments pos_log2_up _ : simpl nomatch.

(** Definition of [div] as an equation.
    Analogous in structure to [sqrtrem_sqrt]. *)

Lemma div_eucl_div (a b : N) : fst (div_eucl a b) = a / b.
Proof. reflexivity. Qed.

(** More elaborate specification for [div_eucl] than [div_eucl_spec].
    Analogous in structure to [sqrtrem_spec]. *)

Lemma div_eucl_spec' (n p : N) :
  let (q, r) := div_eucl n p in n = p * q + r /\ (p <> 0 -> r < p).
Proof.
  destruct n as [| n], p as [| p]; cbv [div_eucl] in *.
  - lia.
  - lia.
  - lia.
  - pose proof pos_div_eucl_spec n (pos p) as enp.
    pose proof pos_div_eucl_remainder n (pos p) as lnp.
    destruct (pos_div_eucl n (pos p)) as [q r]; cbv [fst snd] in *. lia. Qed.

(** Replace a call to [div_eucl] with its specification
    in the goal and hypotheses. *)

Ltac destruct_div_eucl :=
  match goal with
  | |- context [let (a, b) := div_eucl ?x ?y in _] =>
    let a' := fresh a in
    let b' := fresh b in
    let aab' := fresh "a" a' b' in
    let ea' := fresh "e" a' in
    let eab' := fresh "e" a' b' in
    let e0ab' := fresh "e0" a' b' in
    let l1ab' := fresh "l1" a' b' in
    pose proof div_eucl_spec' x y as aab';
    destruct (div_eucl x y) as [a' b'] eqn : eab';
    pose proof (eq_trans (z := a') (eq_sym (div_eucl_div x y))
      (f_equal fst eab')) as ea';
    destruct aab' as [e0ab' l1ab']
  | h : context [let (a, b) := div_eucl ?x ?y in _] |- _ =>
    let a' := fresh a in
    let b' := fresh b in
    let aab' := fresh "a" a' b' in
    let ea' := fresh "e" a' in
    let eab' := fresh "e" a' b' in
    let e0ab' := fresh "e0" a' b' in
    let l1ab' := fresh "l1" a' b' in
    pose proof div_eucl_spec' x y as aab';
    destruct (div_eucl x y) as [a' b'] eqn : eab';
    pose proof (eq_trans (z := a') (eq_sym (div_eucl_div x y))
      (f_equal fst eab')) as ea';
    destruct aab' as [e0ab' l1ab']
  end.

(** Replace a call to [sqrtrem] with its specification
    in the goal and hypotheses. *)

Ltac destruct_sqrtrem :=
  match goal with
  | |- context [let (a, b) := sqrtrem ?x in _] =>
    let a' := fresh a in
    let b' := fresh b in
    let aab' := fresh "a" a' b' in
    let ea' := fresh "e" a' in
    let eab' := fresh "e" a' b' in
    let e0ab' := fresh "e0" a' b' in
    let l1ab' := fresh "l1" a' b' in
    pose proof sqrtrem_spec x as aab';
    destruct (sqrtrem x) as [a' b'] eqn : eab';
    pose proof (eq_trans (z := a') (eq_sym (sqrtrem_sqrt x))
      (f_equal fst eab')) as ea';
    destruct aab' as [e0ab' l1ab']
  | h : context [let (a, b) := sqrtrem ?x in _] |- _ =>
    let a' := fresh a in
    let b' := fresh b in
    let aab' := fresh "a" a' b' in
    let ea' := fresh "e" a' in
    let eab' := fresh "e" a' b' in
    let e0ab' := fresh "e0" a' b' in
    let l1ab' := fresh "l1" a' b' in
    pose proof sqrtrem_spec x as aab';
    destruct (sqrtrem x) as [a' b'] eqn : eab';
    pose proof (eq_trans (z := a') (eq_sym (sqrtrem_sqrt x))
      (f_equal fst eab')) as ea';
    destruct aab' as [e0ab' l1ab']
  end.

(** These lemmas are missing from the standard library. *)

Lemma shiftl_1_r (a : N) : shiftl a 1 = a * 2.
Proof. rewrite shiftl_mul_pow2. rewrite pow_1_r. reflexivity. Qed.

Lemma shiftr_1_l (n : N) : shiftr 1 n = 1 / 2 ^ n.
Proof. rewrite shiftr_div_pow2. reflexivity. Qed.

Lemma shiftr_1_r (a : N) : shiftr a 1 = a / 2.
Proof. rewrite <- div2_spec. rewrite div2_div. reflexivity. Qed.

(** If we admit that subtraction is saturative (by [sub_0_l]),
    we might as well admit that division and binary logarithm are total
    (by [div_0_r] and [log2_0] respectively). *)

Lemma div_0_r (a : N) : a / 0 = 0.
Proof. destruct a as [| p]; reflexivity. Qed.

Lemma log2_0 : log2 0 = 0.
Proof. reflexivity. Qed.

(** Every natural number is either even or odd.
    Either the number itself or its predecessor can be halved. *)

Lemma exist_even_odd (n : N) : exists p : N, n = 2 * p \/ n = 1 + 2 * p.
Proof.
  induction n as [| q ei] using peano_ind.
  - exists 0. lia.
  - destruct ei as [r [e | e]].
    + exists (q / 2). subst q. right.
      replace (2 * r) with (r * 2) by lia.
      rewrite div_mul by lia. lia.
    + exists ((1 + q) / 2). subst q. left.
      replace (1 + (1 + 2 * r)) with ((1 + r) * 2) by lia.
      rewrite div_mul by lia. lia. Qed.

(** Product of two consecutive natural numbers is even. *)

Lemma mod_mul_even_odd (n : N) : n * (1 + n) mod 2 = 0.
Proof.
  induction n as [| p ei] using peano_ind.
  - reflexivity.
  - replace (succ p * (1 + succ p)) with (p * (1 + p) + (1 + p) * 2) by lia.
    rewrite mod_add by lia. apply ei. Qed.

(** Another way to state [mod_mul_even_odd]. *)

Lemma double_mul_even_odd (n : N) : 2 * (n * (1 + n) / 2) = n * (1 + n).
Proof.
  replace (2 * (n * (1 + n) / 2))
  with (2 * (n * (1 + n) / 2) + n * (1 + n) mod 2)
  by (rewrite mod_mul_even_odd; lia).
  rewrite <- div_mod by lia. lia. Qed.

(** Eliminate all occurrences of
    [shiftl], [double], [succ], [shiftr], [div2] and [pred]. *)

Ltac eliminate :=
  (** Eliminate [shiftl 0 _].
      This shortcut is equivalent to [shiftl_mul_pow2]
      followed by [mul_0_l]. *)
  repeat rewrite shiftl_0_l in *;
  (** Eliminate [shiftl _ 0].
      This shortcut is equivalent to [shiftl_mul_pow2]
      followed by [pow_0_r] and [mul_1_r]. *)
  repeat rewrite shiftl_0_r in *;
  (** Eliminate [shiftl 1 _] into [2 ^ _].
      This shortcut is equivalent to [shiftl_mul_pow2]
      followed by [mul_1_l]. *)
  repeat rewrite shiftl_1_l in *;
  (** Eliminate [shiftl _ 1] into [_ * 2].
      This shortcut is equivalent to [shiftl_mul_pow2]
      followed by [pow_1_r]. *)
  repeat rewrite shiftl_1_r in *;
  (** Eliminate [shiftl _ _] into [_ * 2 ^ _]. *)
  repeat rewrite shiftl_mul_pow2 in *;
  (** Eliminate [double _] into [2 * _]. *)
  repeat rewrite double_spec in *;
  (** Eliminate [succ _] into [1 + _]. *)
  repeat rewrite <- add_1_l in *;
  (** Eliminate [shiftr 0 _].
      This shortcut is equivalent to [shiftr_div_pow2]
      followed by [div_0_l] with [pow_nonzero]. *)
  repeat rewrite shiftr_0_l in *;
  (** Eliminate [shiftr _ 0].
      This shortcut is equivalent to [shiftr_div_pow2]
      followed by [pow_0_r] and [div_1_r]. *)
  repeat rewrite shiftr_0_r in *;
  (** Eliminate [shiftr 1 _] into [1 / 2 ^ _].
      This shortcut is equivalent to [shiftr_div_pow2]. *)
  repeat rewrite shiftr_1_l in *;
  (** Eliminate [shiftr _ 1] into [_ / 2].
      This shortcut is equivalent to [shiftr_div_pow2]
      followed by [pow_1_r]. *)
  repeat rewrite shiftr_1_r in *;
  (** Eliminate [shiftr _ _] into [_ / 2 ^ _]. *)
  repeat rewrite shiftr_div_pow2 in *;
  (** Eliminate [div2 _] into [_ / 2]. *)
  repeat rewrite div2_div in *;
  (** Eliminate [pred] into [_ - 1]. *)
  repeat rewrite <- sub_1_r in *;
  idtac.

(** Simplify occurrences of
    [_ ^ _], [_ * _], [_ + _], [log2], [_ / _] and [_ - _].
    Rewrite rules that produce subgoals will fail,
    unless they can be immediately proven with [force]. *)

Ltac simplify_by force :=
  (** Reduce [_ ^ _], [_ * _], [_ + _], [log2], [_ / _] and [_ - _]. *)
  (** Try to eliminate [0 ^ _]. *)
  repeat rewrite pow_0_l in * by force;
  (** Eliminate [_ ^ 0]. *)
  repeat rewrite pow_0_r in *;
  (** Eliminate [1 ^ _]. *)
  repeat rewrite pow_1_l in *;
  (** Eliminate [_ ^ 1]. *)
  repeat rewrite pow_1_r in *;
  (** Do not try to eliminate [_ ^ _],
      because it would be impossible. *)
  (* repeat rewrite _ in *; *)
  (** Eliminate [0 * _]. *)
  repeat rewrite mul_0_l in *;
  (** Eliminate [_ * 0]. *)
  repeat rewrite mul_0_r in *;
  (** Eliminate [1 * _]. *)
  repeat rewrite mul_1_l in *;
  (** Eliminate [_ * 1]. *)
  repeat rewrite mul_1_r in *;
  (** Do not try to eliminate [_ * _],
      because it would be impossible. *)
  (* repeat rewrite _ in *; *)
  (** Eliminate [0 + _]. *)
  repeat rewrite add_0_l in *;
  (** Eliminate [_ + 0]. *)
  repeat rewrite add_0_r in *;
  (** Do not try to eliminate [_ + _],
      because it would be impossible. *)
  (* repeat rewrite _ in *; *)
  (** Eliminate [log2 0].
      This is specific to the way [log2] is defined. *)
  repeat rewrite log2_0 in *;
  (** Eliminate [log2 1]. *)
  repeat rewrite log2_1 in *;
  (** Eliminate [log2 2]. *)
  repeat rewrite log2_2 in *;
  (** Do not eliminate [log2 _],
      because it would be impossible. *)
  (* repeat rewrite _ in *; *)
  (** Try to eliminate [0 / _]. *)
  repeat rewrite div_0_l in * by force;
  (** Eliminate [_ / 0].
      This is specific to the way [div] is defined. *)
  repeat rewrite div_0_r in *;
  (** Try to eliminate [1 / _]. *)
  repeat rewrite div_1_l in * by force;
  (** Eliminate [_ / 1]. *)
  repeat rewrite div_1_r in *;
  (** Do not try to eliminate [_ / _],
      because it would be impossible. *)
  (* repeat rewrite _ in *; *)
  (** Eliminate [0 - _].
      This is specific to the way [sub] is defined. *)
  repeat rewrite sub_0_l in *;
  (** Eliminate [_ - 0]. *)
  repeat rewrite sub_0_r in *;
  (** Do not try to eliminate [_ - _],
      because it would be impossible. *)
  (* repeat rewrite _ in *; *)
  idtac.

(** Prepare or reduce occurrences of
    [_ ^ _], [_ * _], [_ + _], [log2], [_ / _] and [_ - _].
    Rewrite rules that produce subgoals will fail,
    unless they can be immediately proven with [force]. *)

Ltac preduce :=
  (** Reduce [_ ^ _], [_ * _], [_ + _], [log2], [_ / _] and [_ - _]. *)
  repeat reduce_2 is_N is_N pow;
  repeat reduce_2 is_N is_N mul;
  repeat reduce_2 is_N is_N add;
  repeat reduce_1 is_N log2;
  repeat reduce_2 is_N is_N div;
  repeat reduce_2 is_N is_N sub;
  (** Commute [_ * _] and [_ + _],
      so that constants always appear on the left side
      (corresponding to the structurally recursive parameter). *)
  repeat recomm_2_0 is_N mul mul_comm;
  repeat recomm_2_0 is_N add add_comm;
  (** Associate [_ * _] and [_ + _],
      so that constants always appear on the deeper level
      (and thus reduce). *)
  repeat reassoc_2 is_N mul mul_assoc;
  repeat reassoc_2 is_N add add_assoc;
  idtac.

(** Convert expressions involving bit manipulation
    into expressions involving basic arithmetic.

    The conversion repeats three steps
    until they no longer make progress in the proof.
    In the first step, we eliminate occurrences of
    [shiftl], [double], [succ], [shiftr], [div2] and [pred], and
    in the remaining steps, we simplify and reduce occurrences of
    [_ ^ _], [_ * _], [_ + _], [log2], [_ / _] and [_ - _].

    After the conversion,
    we expect two kinds of properties to hold.
    Most importantly,
    no occurrence of [_ * _] or [_ + _]
    will have constants appear on the right side,
    no occurrence of [_ ^ _], [_ / _] or [_ - _]
    will have constants appear on both sides and
    no occurrence of [log2] will have constants appear anywhere.
    Less importantly,
    no occurrence of [0], [1] or [2] should be unnecessary
    according to the algebraic structure of the operations. *)

Ltac arithmetize_by force := eliminate; repeat (simplify_by force; preduce).

(** Specialization of [arithmetize_by] using [lia]. *)

Ltac arithmetize := arithmetize_by lia.

End N.

(** Additive monoid structure. *)

Module Additive.

Global Instance N_has_bin_op : HasBinOp N := N.add.
Global Instance N_has_null_op : HasNullOp N := N.zero.

Global Instance N_bin_op_is_mag : IsMag (bin_op (A := N)).
Proof. Defined.

Global Instance N_bin_op_is_assoc : IsAssoc (bin_op (A := N)).
Proof. intros x y z. apply N.add_assoc. Defined.

Global Instance N_bin_op_is_sgrp : IsSgrp (bin_op (A := N)).
Proof. split; typeclasses eauto. Defined.

Global Instance N_bin_op_is_comm : IsComm (bin_op (A := N)).
Proof. intros x y. apply N.add_comm. Defined.

Global Instance N_bin_op_is_comm_sgrp : IsCommSgrp (bin_op (A := N)).
Proof. split; typeclasses eauto. Defined.

Global Instance N_bin_op_null_op_is_l_unl : IsLUnl (bin_op (A := N)) null_op.
Proof. intros x. apply N.add_0_l. Defined.

Global Instance N_bin_op_null_op_is_r_unl : IsRUnl (bin_op (A := N)) null_op.
Proof. intros x. apply N.add_0_r. Defined.

Global Instance N_bin_op_null_op_is_unl : IsUnl (bin_op (A := N)) null_op.
Proof. split; typeclasses eauto. Defined.

Global Instance N_bin_op_null_op_is_mon : IsMon (bin_op (A := N)) null_op.
Proof. split; typeclasses eauto. Defined.

Global Instance N_bin_op_null_op_is_comm_mon : IsCommMon (bin_op (A := N)) null_op.
Proof. split; typeclasses eauto. Defined.

End Additive.

(** Multiplicative monoid structure. *)

Module Multiplicative.

Global Instance N_bin_op_has_bin_op : HasBinOp N := N.mul.
Global Instance N_has_null_op : HasNullOp N := N.one.

Global Instance N_bin_op_is_mag : IsMag (bin_op (A := N)).
Proof. Defined.

Global Instance N_bin_op_is_assoc : IsAssoc (bin_op (A := N)).
Proof. intros x y z. apply N.mul_assoc. Defined.

Global Instance N_bin_op_is_sgrp : IsSgrp (bin_op (A := N)).
Proof. split; typeclasses eauto. Defined.

Global Instance N_bin_op_is_comm : IsComm (bin_op (A := N)).
Proof. intros x y. apply N.mul_comm. Defined.

Global Instance N_bin_op_is_comm_sgrp : IsCommSgrp (bin_op (A := N)).
Proof. split; typeclasses eauto. Defined.

Global Instance N_bin_op_null_op_is_l_unl : IsLUnl (bin_op (A := N)) null_op.
Proof. intros x. apply N.mul_1_l. Defined.

Global Instance N_bin_op_null_op_is_r_unl : IsRUnl (bin_op (A := N)) null_op.
Proof. intros x. apply N.mul_1_r. Defined.

Global Instance N_bin_op_null_op_is_unl : IsUnl (bin_op (A := N)) null_op.
Proof. split; typeclasses eauto. Defined.

Global Instance N_bin_op_null_op_is_mon : IsMon (bin_op (A := N)) null_op.
Proof. split; typeclasses eauto. Defined.

Global Instance N_bin_op_null_op_is_comm_mon : IsCommMon (bin_op (A := N)) null_op.
Proof. split; typeclasses eauto. Defined.

End Multiplicative.

(** Semiring structure. *)

Global Instance N_has_add : HasAdd N := N.add.
Global Instance N_has_zero : HasZero N := N.zero.
Global Instance N_has_mul : HasMul N := N.mul.
Global Instance N_has_one : HasOne N := N.one.

Global Instance N_add_is_comm : IsComm add.
Proof. intros x y. apply N.add_comm. Defined.

Global Instance N_add_mul_is_l_distr : IsLDistr add mul.
Proof. intros x y z. apply N.mul_add_distr_l. Defined.

Global Instance N_add_mul_is_r_distr : IsRDistr add mul.
Proof. intros x y z. apply N.mul_add_distr_r. Defined.

Global Instance N_add_mul_is_distr : IsDistr add mul.
Proof. split; typeclasses eauto. Defined.

Global Instance N_zero_mul_is_l_absorb : IsLAbsorb zero mul.
Proof. intros x. apply N.mul_0_l. Defined.

Global Instance N_zero_mul_is_r_absorb : IsRAbsorb zero mul.
Proof. intros x. apply N.mul_0_r. Defined.

Global Instance N_zero_mul_is_absorb : IsAbsorb zero mul.
Proof. split; typeclasses eauto. Defined.

Global Instance N_add_zero_mul_one_is_sring : IsSring add zero mul one.
Proof. split; typeclasses eauto. Defined.

Global Instance N_mul_is_comm : IsComm mul.
Proof. intros x y. apply N.mul_comm. Defined.

Global Instance N_add_zero_mul_one_is_comm_sring :
  IsCommSring add zero mul one.
Proof. split; typeclasses eauto. Defined.
