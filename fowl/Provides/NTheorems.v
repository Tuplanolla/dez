(** Lemmas and instances for [N]. *)

From Coq Require Import
  Lia NArith.NArith.
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
