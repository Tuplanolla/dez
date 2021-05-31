From Coq Require Import
  NArith.NArith.
From Maniunfold.Has Require Import
  Unsquashing.
From Maniunfold.Provides Require Export
  LogicalTheorems NTheorems PositiveTheorems.

Import N.

Local Open Scope N_scope.

(** Split the given positive number into a binary factor and an odd factor.

    See [pos_binfactor] and [pos_oddfactor] for details on the factors.
    This function is an inverse of [pos_binoddprod]. *)

Equations pos_binoddfactor (n : positive) : N * positive :=
  pos_binoddfactor (xI p) := (0, xI p);
  pos_binoddfactor (xO p) := let (b, c) := pos_binoddfactor p in (succ b, c);
  pos_binoddfactor xH := (0, xH).

(** Combine the given binary factor and odd factor into a positive number.

    This function is an inverse of [pos_binoddfactor]. *)

Equations pos_binoddprod (b : N) (c : positive) : positive :=
  pos_binoddprod b c := c * Pos.shiftl 1 b.

(** This function is a dependent version of [pos_binoddfactor]. *)

Equations pos_binoddfactor_dep (n : positive) :
  {x : N * positive $ Squash (Pos.odd (snd x))} :=
  pos_binoddfactor_dep n := Sexists _ (pos_binoddfactor n) _.
Next Obligation.
  intros n.
  apply squash.
  induction n as [p ep | p ep |].
  - reflexivity.
  - simp pos_binoddfactor.
    destruct (pos_binoddfactor p) as [b c].
    apply ep.
  - reflexivity. Qed.

(** This function is a dependent version of [pos_binoddprod]. *)

Equations pos_binoddprod_dep
  (b : N) (c : positive) (e : Squash (Pos.odd c)) : positive :=
  pos_binoddprod_dep b c e := pos_binoddprod b c.

(** Find the binary factor of the given positive number.

    The factor is
    - the largest power of two to divide the given number and
    - the number of trailing zeros
      in the binary representation of the given number.
    This function generates the OEIS sequence A007814. *)

Equations pos_binfactor (n : positive) : N :=
  pos_binfactor n := fst (pos_binoddfactor n).

(** Find the odd factor of the given positive number.

    The factor is
    - the largest odd number to divide the given number and
    - whatever remains of the given number
      after removing trailing zeros from its binary representation.
    This function generates the OEIS sequence A000265. *)

Equations pos_oddfactor (n : positive) : positive :=
  pos_oddfactor n := snd (pos_binoddfactor n).

(** The function [pos_binoddfactor] can be written in components. *)

Lemma pair_pos_binoddfactor (n : positive) :
  pos_binoddfactor n = (pos_binfactor n, pos_oddfactor n).
Proof.
  simp pos_binfactor. simp pos_oddfactor.
  destruct (pos_binoddfactor n) as [b c].
  reflexivity. Qed.

(** The binary factor of a power of two is
    the binary logarithm of the number. *)

Lemma bin_pos_binfactor (n : positive) (e : Pos.bin n) :
  pos_binfactor n = pos_log2 n.
Proof.
  induction n as [p ep | p ep |].
  - inversion e.
  - simp pos_binfactor. simp pos_binoddfactor.
    assert (e' : Pos.bin p) by assumption.
    specialize (ep e').
    simp pos_binfactor in ep.
    destruct (pos_binoddfactor p) as [b c].
    simp fst in ep.
    rewrite ep.
    reflexivity.
  - reflexivity. Qed.

(** The odd factor of an odd number is the number itself. *)

Lemma odd_pos_oddfactor (n : positive) (e : Pos.odd n) :
  pos_oddfactor n = n.
Proof.
  destruct n as [p | p |].
  - reflexivity.
  - inversion e.
  - reflexivity. Qed.

(** The binary factor of an odd number is zero. *)

Lemma odd_pos_binfactor (n : positive) (e : Pos.odd n) :
  pos_binfactor n = 0.
Proof.
  destruct n as [p | p |].
  - reflexivity.
  - inversion e.
  - reflexivity. Qed.

(** The odd factor of a power of two is one. *)

Lemma bin_pos_oddfactor (n : positive) (e : Pos.bin n) :
  pos_oddfactor n = 1%positive.
Proof.
  induction n as [p ep | p ep |].
  - inversion e.
  - simp pos_oddfactor. simp pos_binoddfactor.
    assert (e' : Pos.bin p) by assumption.
    specialize (ep e').
    simp pos_oddfactor in ep.
    destruct (pos_binoddfactor p) as [b c].
    simp snd in ep.
  - reflexivity. Qed.

(** The function [pos_binoddprod] is an inverse of [pos_binoddfactor]. *)

Lemma pos_binoddprod_pos_binoddfactor (n : positive) :
  prod_uncurry pos_binoddprod (pos_binoddfactor n) = n.
Proof.
  destruct (pos_binoddfactor n) as [b c] eqn : e.
  simp prod_uncurry. simp pos_binoddprod.
  generalize dependent b. induction n as [p ep | p ep |]; intros b e.
  - simp pos_binoddfactor in e.
    injection e. clear e. intros ec eb. subst b c.
    rewrite Pos.shiftl_0_r. rewrite Pos.mul_1_r.
    reflexivity.
  - simp pos_binoddfactor in e.
    destruct (pos_binoddfactor p) as [b' c'] eqn : e'.
    injection e. clear e. intros ec eb. subst b c.
    rewrite pos_shiftl_succ_r'. rewrite Pos.mul_xO_r.
    rewrite ep by reflexivity.
    reflexivity.
  - simp pos_binoddfactor in e.
    injection e. clear e. intros ec eb. subst b c.
    reflexivity. Qed.

(** The function [pos_binoddfactor] is not an inverse of [pos_binoddprod]. *)

Lemma not_pos_binoddfactor_pos_binoddprod : ~ forall (b : N) (c : positive),
  pos_binoddfactor (pos_binoddprod b c) = (b, c).
Proof. intros e. specialize (e 2%N 2%positive). cbv in e. inversion e. Qed.

(** The function [pos_binoddfactor] is an inverse of [pos_binoddprod],
    when the second factor is odd. *)

Lemma pos_binoddfactor_pos_binoddprod (b : N) (c : positive) (e : Pos.odd c) :
  pos_binoddfactor (pos_binoddprod b c) = (b, c).
Proof.
  simp pos_binoddprod.
  destruct b as [| p].
  - rewrite Pos.shiftl_0_r. rewrite Pos.mul_1_r.
    rewrite pair_pos_binoddfactor.
    rewrite odd_pos_binfactor by assumption.
    rewrite odd_pos_oddfactor by assumption.
    reflexivity.
  - induction p as [| q eq] using Pos.peano_ind.
    + simp shiftl. simp iter.
      rewrite (Pos.mul_comm c 2). change (2 * c)%positive with (xO c).
      simp pos_binoddfactor.
      rewrite pair_pos_binoddfactor.
      rewrite odd_pos_binfactor by assumption.
      rewrite odd_pos_oddfactor by assumption.
      reflexivity.
    + simp shiftl. simp shiftl in eq.
      rewrite Pos.iter_succ.
      rewrite Pos.mul_xO_r.
      simp pos_binoddfactor.
      rewrite eq by assumption.
      reflexivity. Qed.

(** The function [pos_binoddprod_dep] is an inverse
    of [pos_binoddfactor_dep]. *)

Lemma pos_binoddprod_dep_pos_binoddfactor_dep (n : positive) :
  Ssig_uncurry (prod_uncurry_dep pos_binoddprod_dep)
  (pos_binoddfactor_dep n) = n.
Proof.
  pose proof pos_binoddprod_pos_binoddfactor n as e.
  rewrite prod_uncurry_proj in e.
  unfold Ssig_uncurry.
  rewrite prod_uncurry_dep_proj. simp pos_binoddprod_dep. Qed.

(** The function [pos_binoddfactor_dep] is an inverse
    of [pos_binoddprod_dep]. *)

Lemma pos_binoddfactor_dep_pos_binoddprod_dep
  (b : N) (c : positive) (e : Squash (Pos.odd c)) :
  pos_binoddfactor_dep (pos_binoddprod_dep b c e) = Sexists _ (b, c) e.
Proof.
  pose proof pos_binoddfactor_pos_binoddprod b c as f.
  simp pos_binoddprod_dep. simp pos_binoddfactor_dep.
  apply Spr1_inj. unfold Spr1.
  apply unsquash in e.
  auto. Qed.

(** Split the given natural number into a binary factor and an odd factor,
    except for the degenerate case at zero.

    See [pos_binoddfactor] for details on this function. *)

Equations binoddfactor (n : N) : N * N :=
  binoddfactor N0 := (0, 0);
  binoddfactor (Npos p) := let (b, c) := pos_binoddfactor p in (b, Npos c).

(** Combine the given binary factor and odd factor into a natural number,
    except for the degenerate case at zero.

    See [pos_binoddprod] for details on this function. *)

Equations binoddprod (b c : N) : N :=
  binoddprod b N0 := 0;
  binoddprod b (Npos p) := Npos (pos_binoddprod b p).

(** The function [binoddprod] has an arithmetic form. *)

Lemma binoddprod_eqn (b c : N) : binoddprod b c = c * 2 ^ b.
Proof.
  destruct c as [| p].
  - reflexivity.
  - simp binoddprod.
    simp pos_binoddprod.
    rewrite <- shiftl_1_l.
    reflexivity. Qed.

(** Find the binary factor of the given positive number.
    except for the degenerate case at zero.

    See [pos_binfactor] for details on this function. *)

Equations binfactor (n : N) : N :=
  binfactor n := fst (binoddfactor n).

(** Find the odd factor of the given positive number.
    except for the degenerate case at zero.

    See [pos_oddfactor] for details on this function. *)

Equations oddfactor (n : N) : N :=
  oddfactor n := snd (binoddfactor n).

(** The function [binoddprod] is an inverse of [binoddfactor]. *)

Lemma binoddprod_binoddfactor (n : N) :
  prod_uncurry binoddprod (binoddfactor n) = n.
Proof.
  destruct n as [| p].
  - reflexivity.
  - pose proof pos_binoddprod_pos_binoddfactor p as e.
    simp binoddfactor.
    destruct (pos_binoddfactor p) as [b c].
    unfold prod_uncurry, fst, snd. simp binoddprod.
    unfold prod_uncurry, fst, snd in e.
    rewrite e.
    reflexivity. Qed.

(** The function [binoddfactor] is not an inverse of [binoddprod]. *)

Lemma not_binoddfactor_binoddprod : ~ forall b c : N,
  binoddfactor (binoddprod b c) = (b, c).
Proof.
  intros e.
  apply not_pos_binoddfactor_pos_binoddprod.
  intros b c.
  specialize (e b (Npos c)).
  simp binoddprod in e. simp binoddfactor in e.
  destruct (pos_binoddfactor (pos_binoddprod b c)) as [b' c'].
  injection e. clear e. intros ec eb. subst b c.
  reflexivity. Qed.

(** The function [binoddfactor] is an inverse of [binoddprod],
    when the second factor is odd. *)

Lemma odd_binoddfactor_binoddprod (b c : N) (e : odd c) :
  binoddfactor (binoddprod b c) = (b, c).
Proof.
  destruct b as [| p], c as [| q].
  - reflexivity.
  - rewrite binoddprod_eqn.
    rewrite pow_0_r. rewrite mul_1_r.
    simp binoddfactor.
    rewrite pair_pos_binoddfactor.
    rewrite odd_pos_binfactor by assumption.
    rewrite odd_pos_oddfactor by assumption.
    reflexivity.
  - inversion e.
  - rewrite binoddprod_eqn.
    change (Npos q * 2 ^ Npos p) with (Npos (q * 2 ^ p)).
    simp binoddfactor.
    change (q * 2 ^ p)%positive with (pos_binoddprod (Npos p) q).
    rewrite pos_binoddfactor_pos_binoddprod by assumption.
    reflexivity. Qed.
