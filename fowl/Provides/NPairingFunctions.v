From Coq Require Import
  Lia Lists.List NArith.NArith Bool.Sumbool.
From Maniunfold Require Import
  Equations.
From Maniunfold.Has Require Export
  OneSorted.Decision.
From Maniunfold.Provides Require Export
  OptionTheorems PositiveTheorems ProductTheorems NTriangularNumbers.

Import ListNotations N.

Local Open Scope N_scope.

(** Whether the given number is a power of two or not. *)

Equations pos_bin (n : positive) : bool :=
  pos_bin (xO p) := pos_bin p;
  pos_bin (xI p) := false;
  pos_bin xH := true.

(** Whether the given number is a power of two or not. *)

Equations bin (n : N) : bool :=
  bin N0 := false;
  bin (Npos p) := pos_bin p.

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
  {x : N * positive $ Squash (pos_odd (snd x))} :=
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
  (b : N) (c : positive) (e : Squash (pos_odd c)) : positive :=
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

Lemma bin_pos_binfactor (n : positive) (e : pos_bin n) :
  pos_binfactor n = pos_log2 n.
Proof.
  induction n as [p ep | p ep |].
  - inversion e.
  - simp pos_binfactor. simp pos_binoddfactor.
    assert (e' : pos_bin p) by assumption.
    specialize (ep e').
    simp pos_binfactor in ep.
    destruct (pos_binoddfactor p) as [b c].
    simp fst in ep.
    rewrite ep.
    reflexivity.
  - reflexivity. Qed.

(** The odd factor of an odd number is the number itself. *)

Lemma odd_pos_oddfactor (n : positive) (e : pos_odd n) :
  pos_oddfactor n = n.
Proof.
  destruct n as [p | p |].
  - reflexivity.
  - inversion e.
  - reflexivity. Qed.

(** The binary factor of an odd number is zero. *)

Lemma odd_pos_binfactor (n : positive) (e : pos_odd n) :
  pos_binfactor n = 0.
Proof.
  destruct n as [p | p |].
  - reflexivity.
  - inversion e.
  - reflexivity. Qed.

(** The odd factor of a power of two is one. *)

Lemma bin_pos_oddfactor (n : positive) (e : pos_bin n) :
  pos_oddfactor n = 1%positive.
Proof.
  induction n as [p ep | p ep |].
  - inversion e.
  - simp pos_oddfactor. simp pos_binoddfactor.
    assert (e' : pos_bin p) by assumption.
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
    rewrite pos_shiftl_0_r. rewrite Pos.mul_1_r.
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

(** The function [pos_binoddfactor] is an inverse of [pos_binoddprod]
    when the second factor is odd. *)

Lemma pos_binoddfactor_pos_binoddprod (b : N) (c : positive) (e : pos_odd c) :
  pos_binoddfactor (pos_binoddprod b c) = (b, c).
Proof.
  simp pos_binoddprod.
  destruct b as [| p].
  - rewrite pos_shiftl_0_r. rewrite Pos.mul_1_r.
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
Proof. apply (pos_binoddprod_pos_binoddfactor n). Qed.

(** The function [pos_binoddfactor_dep] is an inverse
    of [pos_binoddprod_dep]. *)

Lemma pos_binoddfactor_dep_pos_binoddprod_dep
  (b : N) (c : positive) (e : Squash (pos_odd c)) :
  pos_binoddfactor_dep (pos_binoddprod_dep b c e) = Sexists _ (b, c) e.
Proof.
  simp pos_binoddprod_dep. simp pos_binoddfactor_dep.
  apply Spr1_inj.
  simp Spr1.
  apply pos_binoddfactor_pos_binoddprod.
  apply unsquash in e. auto. Qed.

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
    cbv [prod_uncurry fst snd]. simp binoddprod.
    cbv [prod_uncurry fst snd] in e.
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

(** The function [binoddfactor] is an inverse of [binoddprod]
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

Module PairingFunction.

Class HasSize : Type := size (a : N) : positive.

Class HasShell : Type := shell (n : N) : N * N.

Class HasShellDep `(HasSize) : Type :=
  shell_dep (n : N) : {x : N * N $ Squash (snd x < Npos (size (fst x)))}.

Class HasUnshell : Type := unshell (a b : N) : N.

Class HasUnshellDep `(HasSize) : Type :=
  unshell_dep (a b : N) (l : Squash (b < Npos (size a))) : N.

Class HasTaco : Type := taco (x y : N) : N * N.

Class HasTacoDep `(HasSize) : Type :=
  taco_dep (x y : N) : {x : N * N $ Squash (snd x < Npos (size (fst x)))}.

Class HasUntaco : Type := untaco (a b : N) : N * N.

Class HasUntacoDep `(HasSize) : Type :=
  untaco_dep (a b : N) (l : Squash (b < Npos (size a))) : N * N.

Class HasLifting `(HasShell) `(HasUnshell) `(HasTaco) `(HasUntaco) : Type :=
  lifting : unit.

Global Instance has_lifting `(HasShell) `(HasUnshell) `(HasTaco) `(HasUntaco) :
  HasLifting shell unshell taco untaco := tt.

Class HasLiftingDep `(HasSize)
  `(!HasShellDep size) `(!HasUnshellDep size)
  `(!HasTacoDep size) `(!HasUntacoDep size) : Type := lifting_dep : unit.

Global Instance has_lifting_dep `(HasSize)
  `(!HasShellDep size) `(!HasUnshellDep size)
  `(!HasTacoDep size) `(!HasUntacoDep size) :
  HasLiftingDep size shell_dep unshell_dep taco_dep untaco_dep := tt.

(** We avoid defining instances involving interplay
    between dependent and nondependent versions of the same type classes,
    because they quickly lead into circular dependencies. *)

(** We can derive dependent versions from nondependent ones. *)

Section Context.

Context `(HasSize) `(HasShell).

Equations shell_dep_fix (a b : N) :
  {x : N * N $ Squash (snd x < Npos (size (fst x)))} by wf (to_nat b) :=
  shell_dep_fix a b := if sumbool_of_bool (b <? Npos (size a)) then
  Sexists _ (a, b) _ else shell_dep_fix (1 + a) (b - Npos (size a)).
Next Obligation.
  intros a b f e.
  apply squash.
  simp fst snd.
  destruct (ltb_spec0 b (Npos (size a))) as [l | l]; lia. Qed.
Next Obligation.
  intros a b f e.
  destruct (ltb_spec0 b (Npos (size a))) as [l | l]; lia. Qed.

Equations shell_dep_def (n : N) :
  {x : N * N $ Squash (snd x < Npos (size (fst x)))} :=
  shell_dep_def n := prod_uncurry shell_dep_fix (shell n).

Definition has_shell_dep : HasShellDep size :=
  fun n : N => shell_dep_def n.

End Context.

Definition has_unshell_dep `(HasSize) `(HasUnshell) : HasUnshellDep size :=
  fun (a b : N) (l : Squash (b < Npos (size a))) => unshell a b.

Section Context.

Context `(HasSize) `(HasTaco).

Equations taco_dep_fix (a b : N) :
  {x : N * N $ Squash (snd x < Npos (size (fst x)))} by wf (to_nat b) :=
  taco_dep_fix a b := if sumbool_of_bool (b <? Npos (size a)) then
  Sexists _ (a, b) _ else taco_dep_fix (1 + a) (b - Npos (size a)).
Next Obligation.
  intros a b f e.
  apply squash.
  simp fst snd.
  destruct (ltb_spec0 b (Npos (size a))) as [l | l]; lia. Qed.
Next Obligation.
  intros a b f e.
  destruct (ltb_spec0 b (Npos (size a))) as [l | l]; lia. Qed.

Equations taco_dep_def (x y : N) :
  {x : N * N $ Squash (snd x < Npos (size (fst x)))} :=
  taco_dep_def x y :=
  prod_uncurry taco_dep_fix (taco x y).

Definition has_taco_dep : HasTacoDep size :=
  taco_dep_def.

End Context.

Definition has_untaco_dep `(HasSize) `(HasUntaco) : HasUntacoDep size :=
  fun (a b : N) (l : Squash (b < Npos (size a))) => untaco a b.

(** We can also derive nondependent versions from dependent ones. *)

Definition has_shell `(HasSize) `(!HasShellDep size) : HasShell :=
  fun n : N => Spr1 (shell_dep n).

Section Context.

Context `(HasSize) `(!HasUnshellDep size).

Equations unshell_fix (a b : N) : N by wf (to_nat b) :=
  unshell_fix a b := if sumbool_of_bool (b <? Npos (size a)) then
  unshell_dep a b _ else unshell_fix (1 + a) (b - Npos (size a)).
Next Obligation.
  intros a b f e.
  apply squash.
  destruct (ltb_spec b (Npos (size a))) as [l | l]; lia. Qed.
Next Obligation.
  intros a b f e.
  destruct (ltb_spec b (Npos (size a))) as [l | l]; lia. Qed.

Definition has_unshell : HasUnshell := unshell_fix.

End Context.

Definition has_taco `(HasSize) `(!HasTacoDep size) : HasTaco :=
  fun x y : N => Spr1 (taco_dep x y).

Section Context.

Context `(HasSize) `(!HasUntacoDep size).

Equations untaco_fix (a b : N) : N * N by wf (to_nat b) :=
  untaco_fix a b := if sumbool_of_bool (b <? Npos (size a)) then
  untaco_dep a b _ else untaco_fix (1 + a) (b - Npos (size a)).
Next Obligation.
  intros a b f e.
  apply squash.
  destruct (ltb_spec b (Npos (size a))) as [l | l]; lia. Qed.
Next Obligation.
  intros a b f e.
  destruct (ltb_spec b (Npos (size a))) as [l | l]; lia. Qed.

Definition has_untaco `(HasSize) `(!HasUntacoDep size) : HasUntaco :=
  untaco_fix.

End Context.

(** TODO Lexicographic ordering of the shell-taco space. *)

(** We want to say that [unshell] is a retraction of [shell] and
    [shell] is a section of [unshell] and then vice versa. *)

Class IsSectShell `(HasLifting) : Prop :=
  sect_shell (n : N) : prod_uncurry unshell (shell n) = n.

Class IsSectShellDep `(HasLiftingDep) : Prop :=
  sect_shell_dep (n : N) :
  Ssig_uncurry (prod_uncurry_dep unshell_dep) (shell_dep n) = n.

Class IsRetrShell `(HasLifting) : Prop :=
  retr_shell (a b : N) : shell (unshell a b) = (a, b).

Class IsRetrShellDep `(HasLiftingDep) : Prop :=
  retr_shell_dep (a b : N) (l : Squash (b < Npos (size a))) :
  shell_dep (unshell_dep a b l) = Sexists _ (a, b) l.

Class IsSectTaco `(HasLifting) : Prop :=
  sect_taco (x y : N) : prod_uncurry untaco (taco x y) = (x, y).

Class IsSectTacoDep `(HasLiftingDep) : Prop :=
  sect_taco_dep (x y : N) :
  Ssig_uncurry (prod_uncurry_dep untaco_dep) (taco_dep x y) = (x, y).

Class IsRetrTaco `(HasLifting) : Prop :=
  retr_taco (a b : N) : prod_uncurry taco (untaco a b) = (a, b).

Class IsRetrTacoDep `(HasLiftingDep) : Prop :=
  retr_taco_dep (a b : N) (l : Squash (b < Npos (size a))) :
  prod_uncurry taco_dep (untaco_dep a b l) = Sexists _ (a, b) l.

Class IsLifting `(HasLifting) : Prop := {
  lifting_is_sect_shell :> IsSectShell lifting;
  lifting_is_retr_shell :> IsRetrShell lifting;
  lifting_is_sect_taco :> IsSectTaco lifting;
  lifting_is_retr_taco :> IsRetrTaco lifting;
}.

Class IsLiftingDep `(HasLiftingDep) : Prop := {
  lifting_dep_is_sect_shell_dep :> IsSectShellDep lifting_dep;
  lifting_dep_is_retr_shell_dep :> IsRetrShellDep lifting_dep;
  lifting_dep_is_sect_taco_dep :> IsSectTacoDep lifting_dep;
  lifting_dep_is_retr_taco_dep :> IsRetrTacoDep lifting_dep;
}.

Section Context.

Existing Instance has_shell.
Existing Instance has_unshell.
Existing Instance has_taco.
Existing Instance has_untaco.

(** This can be done, but retractions should not be possible. *)

Global Instance is_sect_shell `(IsSectShellDep) : IsSectShell lifting_dep.
Proof.
  intros n.
  pose proof sect_shell_dep n as e.
  unfold shell, has_shell, unshell, has_unshell.
  destruct (shell_dep n) as [[a b] l].
  simp Ssig_uncurry in e. simp prod_uncurry_dep in e.
  unfold Spr1. simp prod_uncurry.
  epose proof unsquash l as l'.
  simp fst snd in l'.
  rewrite unshell_fix_equation_1.
  destruct (sumbool_of_bool (b <? pos (size a))) as [e' | e'].
  - apply e.
  - apply ltb_ge in e'. pose proof lt_le_trans _ _ _ l' e'. lia. Qed.

End Context.

Section Context.

Context `(HasLiftingDep).

Fail Equations pair (n : N) : N * N :=
  pair n := prod_uncurry untaco (shell n).

Equations pair (n : N) : N * N :=
  pair n := Ssig_uncurry (prod_uncurry_dep untaco_dep) (shell_dep n).

Fail Equations unpair (x y : N) : N :=
  unpair x y := prod_uncurry unshell (taco x y).

Equations unpair (x y : N) : N :=
  unpair x y := Ssig_uncurry (prod_uncurry_dep unshell_dep) (taco_dep x y).

Context `(!IsLiftingDep lifting_dep).

Theorem retr_pair (n : N) : prod_uncurry unpair (pair n) = n.
Proof.
  destruct (pair n) as [x y] eqn : exy.
  simp pair in exy.
  destruct (shell_dep n) as [[a b] l] eqn : eab.
  simp Ssig_uncurry in exy. simp prod_uncurry_dep in exy.
  simp prod_uncurry. simp unpair.
  destruct (taco_dep x y) as [[a' b'] l'] eqn : eab'.
  simp Ssig_uncurry. simp prod_uncurry_dep.
  pose proof retr_taco_dep a b l as loop_t.
  pose proof sect_shell_dep n as loop_s.
  (** We need to reduce implicit arguments before rewriting. *)
  unfold size in loop_t.
  (** Contract [t ^-1]. *)
  rewrite exy in loop_t.
  simp prod_uncurry in loop_t. rewrite eab' in loop_t.
  inversion loop_t; subst a' b'.
  (* assert (l' = l) by reflexivity; subst l'. *)
  clear loop_t.
  (** Contract [s]. *)
  rewrite eab in loop_s.
  simp Ssig_uncurry in loop_s. Qed.

Theorem sect_pair (x y : N) : pair (unpair x y) = (x, y).
Proof.
  simp pair.
  destruct (shell_dep (unpair x y)) as [[a b] l] eqn : eab.
  simp unpair in eab.
  destruct (taco_dep x y) as [[a' b'] l'] eqn : eab'.
  simp Ssig_uncurry in eab. simp prod_uncurry_dep in eab.
  simp Ssig_uncurry. simp prod_uncurry_dep.
  pose proof retr_shell_dep a' b' l' as loop_s.
  pose proof sect_taco_dep x y as loop_t.
  (** We need to reduce implicit arguments before rewriting. *)
  unfold size in loop_s.
  (** Contract [s ^-1]. *)
  rewrite eab in loop_s.
  inversion loop_s; subst a' b'.
  (* assert (l' = l) by reflexivity; subst l'. *)
  clear loop_s.
  (** Contract [t]. *)
  rewrite eab' in loop_t.
  simp Ssig_uncurry in loop_t. Qed.

Theorem mono_shell (n n' a a' b b' : N)
  (ln : n < n') (la : a < a') (lb : b < b') :
  fst (Spr1 (shell_dep n)) < fst (Spr1 (shell_dep n')) \/
  snd (Spr1 (shell_dep n)) < snd (Spr1 (shell_dep n')).
Proof. Abort.

Theorem lex_shell (n a b : N)
  (e : (a, b) = Spr1 (shell_dep n)) :
  (a, 1 + b) = Spr1 (shell_dep (1 + n)) \/
  (1 + a, 0) = Spr1 (shell_dep (1 + n)).
Proof. Abort.

End Context.

End PairingFunction.

Module Cantor.

Equations size (a : N) : positive :=
  size a := succ_pos a.

Equations shell (n : N) : N * N :=
  shell n := untri_rem n.

Equations shell_dep (n : N) :
  {x : N * N $ Squash (snd x < Npos (size (fst x)))} :=
  shell_dep n := Sexists _ (shell n) _.
Next Obligation.
  intros n.
  apply squash.
  simp size.
  rewrite succ_pos_spec.
  simp shell.
  rewrite untri_rem_tri_untri.
  simp fst snd.
  pose proof tri_untri_untri_rem n as l.
  lia. Qed.

Equations unshell (a b : N) : N :=
  unshell a b := b + tri a.

Equations unshell_dep (a b : N) (l : Squash (b < Npos (size a))) : N :=
  unshell_dep a b l := unshell a b.

Lemma sect_shell_dep (n : N) :
  Ssig_uncurry (prod_uncurry_dep unshell_dep) (shell_dep n) = n.
Proof.
  cbv [Ssig_uncurry Spr1 Spr2].
  simp shell_dep.
  cbv [prod_uncurry_dep].
  simp unshell_dep.
  simp unshell.
  simp shell.
  rewrite untri_rem_tri_untri.
  cbv [fst snd].
  pose proof tri_untri n as l.
  lia. Qed.

Lemma retr_shell_dep (a b : N) (l : Squash (b < Npos (size a))) :
  shell_dep (unshell_dep a b l) = Sexists _ (a, b) l.
Proof.
  simp shell_dep.
  apply Spr1_inj.
  cbv [Spr1].
  simp shell.
  simp unshell_dep.
  simp unshell.
  eapply unsquash in l.
  simp size in l.
  rewrite succ_pos_spec in l.
  rewrite untri_rem_tri_untri.
  assert (l' : b <= a) by lia.
  pose proof tri_why a b l' as e.
  rewrite e.
  f_equal. lia. Qed.

Equations taco (x y : N) : N * N :=
  taco x y := (y + x, y).

Equations taco_dep (x y : N) :
  {x : N * N $ Squash (snd x < Npos (size (fst x)))} :=
  taco_dep x y := Sexists _ (taco x y) _.
Next Obligation.
  intros x y.
  apply squash.
  simp size.
  rewrite succ_pos_spec.
  simp taco.
  simp fst snd.
  lia. Qed.

Equations untaco (a b : N) : N * N :=
  untaco a b := (a - b, b).

Equations untaco_dep (a b : N) (l : Squash (b < Npos (size a))) : N * N :=
  untaco_dep a b l := untaco a b.

Lemma sect_taco_dep (x y : N) :
  Ssig_uncurry (prod_uncurry_dep untaco_dep) (taco_dep x y) = (x, y).
Proof.
  cbv [Ssig_uncurry Spr1 Spr2].
  simp taco_dep.
  cbv [prod_uncurry_dep].
  simp untaco_dep.
  simp untaco.
  simp taco.
  cbv [fst snd].
  f_equal.
  lia. Qed.

Lemma retr_taco_dep (a b : N) (l : Squash (b < Npos (size a))) :
  prod_uncurry taco_dep (untaco_dep a b l) = Sexists _ (a, b) l.
Proof.
  cbv [prod_uncurry].
  simp taco_dep.
  apply Spr1_inj.
  cbv [Spr1].
  simp untaco_dep.
  simp untaco.
  simp taco.
  cbv [fst snd].
  f_equal.
  eapply unsquash in l.
  simp size in l.
  rewrite succ_pos_spec in l.
  lia. Qed.

Module PF := PairingFunction.

Global Instance has_size : PF.HasSize := size.
Global Instance has_shell_dep : PF.HasShellDep size := shell_dep.
Global Instance has_unshell_dep : PF.HasUnshellDep size := unshell_dep.
Global Instance has_taco_dep : PF.HasTacoDep size := taco_dep.
Global Instance has_untaco_dep : PF.HasUntacoDep size := untaco_dep.
Global Instance has_lifting_dep : PF.HasLiftingDep size shell_dep unshell_dep taco_dep untaco_dep := tt.

Global Instance is_sect_shell_dep : PF.IsSectShellDep PF.lifting_dep.
Proof. exact @sect_shell_dep. Qed.
Global Instance is_retr_shell_dep : PF.IsRetrShellDep PF.lifting_dep.
Proof. exact @retr_shell_dep. Qed.
Global Instance is_sect_taco_dep : PF.IsSectTacoDep PF.lifting_dep.
Proof. exact @sect_taco_dep. Qed.
Global Instance is_retr_taco_dep : PF.IsRetrTacoDep PF.lifting_dep.
Proof. exact @retr_taco_dep. Qed.
Global Instance is_lifting_dep : PF.IsLiftingDep PF.lifting_dep.
Proof. esplit; typeclasses eauto. Qed.

Compute map PF.pair (seq 0 64).
Compute map (prod_uncurry PF.unpair o PF.pair) (seq 0 64).

End Cantor.

Module RosenbergStrong.

Definition pair_shell (n : N) : N := sqrt n.

Arguments pair_shell _ : assert.

(* Definition z (x : N) : N := 1 + 2 * x.
Definition sum_z (x : N) : N := x ^ 2.
Compute map z (seq 0 32).
Compute map sum_z (seq 0 32).
Compute map (fun x : N => (z x, sum_z (1 + x) - sum_z x)) (seq 0 32).
Program Fixpoint s (tot ix : N) (x : N) {measure (N.to_nat x)} : N * N :=
  if x <? z ix + tot then (ix, x - tot) else s (z ix + tot) (1 + ix) x.
Next Obligation. Admitted.
Next Obligation. Tactics.program_solve_wf. Defined.
Compute map (s 0 0) (seq 0 32).
Compute map sqrtrem (seq 0 32). *)

Definition unpair_shell (p q : N) : N := max q p.

Arguments unpair_shell _ _ : assert.

Definition pair (n : N) : N * N :=
  let (s, t) := sqrtrem n in
  if s <=? t then (s - (t - s), s) else (s, t).

Arguments pair _ : assert.

Definition unpair (p q : N) : N :=
  if p <=? q then (q - p) + q * (1 + q) else q + p * p.

Arguments unpair _ _ : assert.

Theorem unpair_pair' (n : N) :
  prod_uncurry unpair_shell (pair n) = pair_shell n.
Proof.
  cbv [prod_uncurry fst snd unpair_shell pair pair_shell].
  rewrite <- sqrtrem_sqrt. cbv [fst snd].
  destruct_sqrtrem s t est es e0st l1st.
  clear est es.
  destruct (leb_spec s t) as [lst | lst]; lia. Qed.

Theorem pair_unpair' (p q : N) :
  pair_shell (unpair p q) = unpair_shell p q.
Proof.
  cbv [pair_shell unpair unpair_shell].
  rewrite <- sqrtrem_sqrt. cbv [fst snd].
  destruct_sqrtrem s t est es e0st l1st.
  clear est es.
  destruct (leb_spec p q) as [lpq | lpq]; nia. Qed.

Theorem unpair_pair (n : N) : prod_uncurry unpair (pair n) = n.
Proof.
  cbv [prod_uncurry fst snd unpair pair].
  destruct_sqrtrem s t est es e0st l1st.
  clear est es.
  destruct (leb_spec s t) as [lst | lst].
  - destruct (leb_spec (s - (t - s)) s) as [lst' | lst']; lia.
  - destruct (leb_spec s t) as [lst' | lst']; lia. Qed.

Theorem pair_unpair (p q : N) : pair (unpair p q) = (p, q).
Proof.
  cbv [pair unpair].
  destruct_sqrtrem s t est es e0st l1st.
  clear est es.
  destruct (leb_spec s t) as [lst | lst].
  - destruct (leb_spec p q) as [lpq | lpq].
    + assert (e : s = q) by nia. subst s. f_equal; nia.
    + assert (f : s <> q) by nia. exfalso.
      assert (l : p <= s) by nia. nia.
  - destruct (leb_spec p q) as [lpq | lpq].
    + assert (f : s <> p) by nia. exfalso.
      assert (l : q < s) by nia. nia.
    + assert (e : s = p) by nia. subst s. f_equal; nia. Qed.

End RosenbergStrong.

Module Szudzik.

Definition pair_shell (n : N) : N := sqrt n.

Arguments pair_shell _ : assert.

Definition unpair_shell (p q : N) : N := max q p.

Arguments unpair_shell _ _ : assert.

Definition pair (n : N) : N * N :=
  let (s, t) := sqrtrem n in
  if s <=? t then (t - s, s) else (s, t).

Arguments pair _ : assert.

Definition unpair (p q : N) : N :=
  if p <=? q then p + q * (1 + q) else q + p * p.

Arguments unpair _ _ : assert.

(** Note how the three following proofs are
    nearly exactly the same as in [RosenbergStrong]. *)

Theorem unpair_shell' (n : N) :
  prod_uncurry unpair_shell (pair n) = pair_shell n.
Proof.
  cbv [prod_uncurry fst snd unpair_shell pair pair_shell].
  rewrite <- sqrtrem_sqrt. cbv [fst snd].
  destruct_sqrtrem s t est es e0st l1st.
  clear est es.
  destruct (leb_spec s t) as [lst | lst]; lia. Qed.

Theorem pair_taco (p q : N) :
  pair_shell (unpair p q) = unpair_shell p q.
Proof.
  cbv [pair_shell unpair unpair_shell].
  rewrite <- sqrtrem_sqrt. cbv [fst snd].
  destruct_sqrtrem s t est es e0st l1st.
  clear est es.
  destruct (leb_spec p q) as [lpq | lpq]; nia. Qed.

Theorem unpair_pair (n : N) : prod_uncurry unpair (pair n) = n.
Proof.
  cbv [prod_uncurry fst snd unpair pair].
  destruct_sqrtrem s t est es e0st l1st.
  clear est es.
  destruct (leb_spec s t) as [lst | lst].
  - destruct (leb_spec (t - s) s) as [lst' | lst']; lia.
  - destruct (leb_spec s t) as [lst' | lst']; lia. Qed.

Theorem pair_unpair (p q : N) : pair (unpair p q) = (p, q).
Proof.
  cbv [pair unpair].
  destruct_sqrtrem s t est es e0st l1st.
  clear est es.
  destruct (leb_spec s t) as [lst | lst].
  - destruct (leb_spec p q) as [lpq | lpq].
    + assert (e : s = q) by nia. subst s. f_equal; nia.
    + assert (f : s <> q) by nia. exfalso.
      assert (l : p <= s) by nia. nia.
  - destruct (leb_spec p q) as [lpq | lpq].
    + assert (f : s <> p) by nia. exfalso.
      assert (l : q < s) by nia. nia.
    + assert (e : s = p) by nia. subst s. f_equal; nia. Qed.

End Szudzik.

#[ugly]
Module Hausdorff.

Lemma pos_binfactor_even (n : positive) :
  pos_binfactor (2 * n) = 1 + pos_binfactor n.
Proof.
  simp pos_binfactor.
  induction n as [p ei | p ei |].
  - reflexivity.
  - simp pos_binoddfactor in *.
    destruct (pos_binoddfactor p) as [b c].
    change (fst (succ b, c)) with (succ (fst (b, c))).
    replace (1 + succ (fst (b, c))) with (succ (1 + fst (b, c))) by lia.
    rewrite <- ei. reflexivity.
  - reflexivity. Qed.

Lemma part_factor (n : N) (f : n <> 0) :
  exists p q : N, n = (1 + 2 * q) * 2 ^ p.
Proof.
  destruct n as [| p].
  - contradiction.
  - exists (pos_binfactor p), ((Npos (pos_oddfactor p) - 1) / 2). clear f.
    induction p as [q ei | q ei |].
    + cbn [pos_binfactor pos_oddfactor]. rewrite pow_0_r. rewrite mul_1_r.
      rewrite <- divide_div_mul_exact. rewrite (mul_comm 2 _). rewrite div_mul.
      reflexivity.
      lia. lia. cbn. replace (q~0)%positive with (2 * q)%positive by lia.
      replace (pos (2 * q)%positive) with (2 * Npos q) by lia.
      apply divide_factor_l.
    + simp pos_binfactor pos_oddfactor pos_binoddfactor in *.
      destruct (pos_binoddfactor q) as [b c]. simp fst snd in *.
      rewrite pow_succ_r by lia.
      rewrite mul_assoc. lia.
    + reflexivity. Qed.

Lemma part_factor_again (p q : N) :
  exists n : N, n = (1 + 2 * q) * 2 ^ p.
Proof. exists ((1 + 2 * q) * 2 ^ p). reflexivity. Qed.

Lemma part_urgh (n : positive) :
  let p := pos_binfactor n in
  let q := (Npos (pos_oddfactor n) - 1) / 2 in
  Npos n = (1 + 2 * q) * 2 ^ p.
Proof.
  intros p' q'. subst p' q'.
  induction n as [q ei | q ei |].
  + cbn [pos_binfactor pos_oddfactor]. rewrite pow_0_r. rewrite mul_1_r.
    rewrite <- divide_div_mul_exact. rewrite (mul_comm 2 _). rewrite div_mul.
    reflexivity. lia. lia. cbn. replace (q~0)%positive with (2 * q)%positive by lia.
    replace (pos (2 * q)%positive) with (2 * Npos q) by lia.
    apply divide_factor_l.
  + simp pos_binfactor pos_oddfactor pos_binoddfactor in *.
    destruct (pos_binoddfactor q) as [b c]. simp fst snd in *.
    rewrite pow_succ_r by lia.
    rewrite mul_assoc. lia.
  + reflexivity. Qed.

Lemma binfactor_odd (n : N) : binfactor (1 + 2 * n) = 0.
Proof.
  destruct n as [| p].
  - arithmetize. reflexivity.
  - induction p as [q ei | q ei |].
    + reflexivity.
    + reflexivity.
    + reflexivity. Qed.

Lemma binfactor_even (n : N) (f : n <> 0) :
  binfactor (2 * n) = 1 + binfactor n.
Proof.
  destruct n as [| p].
  - arithmetize. cbn. lia.
  - simp binfactor binoddfactor.
    rewrite (pos_binfactor_even p). Qed.

Lemma binfactor_pow_2 (n p : N) (f : p <> 0) :
  binfactor (2 ^ n * p) = n + binfactor p.
Proof.
  destruct n as [| q].
  - arithmetize. reflexivity.
  - generalize dependent p. induction q as [r ei | r ei |]; intros p f.
    + replace (pos r~1) with (succ (2 * pos r)) by lia.
      rewrite pow_succ_r'.
      rewrite <- mul_assoc.
      rewrite binfactor_even.
      replace (2 * pos r) with (pos r + pos r) by lia.
      rewrite pow_add_r.
      rewrite <- mul_assoc.
      rewrite ei.
      rewrite ei. lia. lia.
      specialize (ei p).
      destruct p. lia.
      pose proof pow_nonzero 2 (pos r).
      lia.
      pose proof pow_nonzero 2 (2 * pos r).
      lia.
    + replace (pos r~0) with (2 * pos r) by lia.
      replace (2 * pos r) with (pos r + pos r) by lia.
      rewrite pow_add_r.
      rewrite <- mul_assoc.
      rewrite ei.
      rewrite ei. lia.
      lia.
      pose proof pow_nonzero 2 (pos r).
      lia.
    + arithmetize.
      destruct p. lia.
      rewrite binfactor_even.
      lia. lia. Qed.

Lemma binfactor_trivial (p q : N) :
  binfactor ((1 + 2 * q) * 2 ^ p) = p.
Proof.
  destruct p as [| r].
  - arithmetize. apply binfactor_odd.
  - generalize dependent q. induction r as [s ei | s ei |]; intros q.
    + replace (pos s~1) with (succ (2 * pos s)) by lia.
      rewrite pow_succ_r'.
      replace (2 * pos s) with (pos s + pos s) by lia.
      rewrite pow_add_r.
      rewrite mul_shuffle3.
      rewrite binfactor_even.
      rewrite mul_shuffle3.
      rewrite binfactor_pow_2.
      rewrite ei. lia.
      pose proof pow_nonzero 2 (pos s).
      lia.
      pose proof pow_nonzero 2 (pos s).
      lia.
    + replace (pos s~0) with (2 * pos s) by lia.
      replace (2 * pos s) with (pos s + pos s) by lia.
      rewrite pow_add_r.
      rewrite mul_shuffle3.
      rewrite binfactor_pow_2.
      rewrite ei. lia.
      pose proof pow_nonzero 2 (pos s).
      lia.
    + arithmetize.
      rewrite binfactor_even.
      rewrite binfactor_odd.
      lia. lia. Qed.

Lemma pos_binfactor_trivial (p q : N) :
  pos_binfactor (succ_pos ((1 + 2 * q) * 2 ^ p - 1)) = p.
Proof.
  pose proof binfactor_trivial p q as e.
  remember ((1 + 2 * q) * 2 ^ p) as r eqn : er.
  destruct r as [| s].
  - arithmetize. cbn. rewrite <- e. reflexivity.
  - replace (succ_pos (Npos s - 1)) with s. rewrite <- e. reflexivity.
    induction s.
    reflexivity.
    cbn. rewrite Pos.pred_double_spec. rewrite Pos.succ_pred; lia.
    reflexivity. Qed.

Lemma oddfactor_odd (n : N) : oddfactor (1 + 2 * n) = 1 + 2 * n.
Proof.
  destruct n as [| p].
  - arithmetize. reflexivity.
  - induction p as [q ei | q ei |].
    + reflexivity.
    + reflexivity.
    + reflexivity. Qed.

Lemma oddfactor_even (n : N) :
  oddfactor (2 * n) = oddfactor n.
Proof.
  destruct n as [| p].
  - arithmetize. cbn. lia.
  - reflexivity. Qed.

Lemma oddfactor_pow_2 (n p : N) (f : p <> 0) :
  oddfactor (2 ^ n * p) = oddfactor p.
Proof.
  destruct n as [| q].
  - arithmetize. cbn. lia.
  - generalize dependent p. induction q as [s ei | s ei |]; intros p f.
    + replace (pos s~1) with (succ (2 * pos s)) by lia.
      rewrite pow_succ_r'.
      replace (2 * pos s) with (pos s + pos s) by lia.
      rewrite pow_add_r.
      rewrite <- mul_assoc.
      rewrite oddfactor_even.
      rewrite <- mul_assoc.
      rewrite ei.
      rewrite ei.
      lia.
      lia.
      pose proof pow_nonzero 2 (pos s).
      lia.
    + replace (pos s~0) with (2 * pos s) by lia.
      replace (2 * pos s) with (pos s + pos s) by lia.
      rewrite pow_add_r.
      rewrite <- mul_assoc.
      rewrite ei.
      rewrite ei.
      lia.
      lia.
      pose proof pow_nonzero 2 (pos s).
      lia.
    + arithmetize.
      rewrite oddfactor_even.
      lia. Qed.

Lemma oddfactor_trivial (p q : N) :
  oddfactor ((1 + 2 * q) * 2 ^ p) = 1 + 2 * q.
Proof.
  destruct p as [| r].
  - arithmetize. apply oddfactor_odd.
  - generalize dependent q. induction r as [s ei | s ei |]; intros q.
    + replace (pos s~1) with (succ (2 * pos s)) by lia.
      rewrite pow_succ_r'.
      replace (2 * pos s) with (pos s + pos s) by lia.
      rewrite pow_add_r.
      rewrite mul_shuffle3.
      rewrite oddfactor_even.
      rewrite mul_shuffle3.
      rewrite oddfactor_pow_2.
      rewrite ei. lia.
      pose proof pow_nonzero 2 (pos s).
      lia.
    + replace (pos s~0) with (2 * pos s) by lia.
      replace (2 * pos s) with (pos s + pos s) by lia.
      rewrite pow_add_r.
      rewrite mul_shuffle3.
      rewrite oddfactor_pow_2.
      rewrite ei. lia.
      pose proof pow_nonzero 2 (pos s).
      lia.
    + arithmetize.
      rewrite oddfactor_even.
      rewrite oddfactor_odd.
      lia. Qed.

Lemma pos_oddfactor_trivial (p q : N) :
  Npos (pos_oddfactor (succ_pos ((1 + 2 * q) * 2 ^ p - 1))) = 1 + 2 * q.
Proof.
  pose proof oddfactor_trivial p q as e.
  remember ((1 + 2 * q) * 2 ^ p) as r eqn : er.
  destruct r as [| s].
  - arithmetize. rewrite <- e. cbn. pose proof pow_nonzero 2 p. lia.
  - replace (succ_pos (Npos s - 1)) with s. rewrite <- e. reflexivity.
    induction s.
    reflexivity.
    cbn. rewrite Pos.pred_double_spec. rewrite Pos.succ_pred; lia.
    reflexivity. Qed.

Local Lemma logging (n : positive) : pos_log2 n = log2 (Npos n).
Proof.
  induction n; cbn.
  rewrite IHn; destruct n; reflexivity.
  rewrite IHn; destruct n; reflexivity.
  reflexivity. Qed.

Definition pair_shell (n : N) : N :=
  pos_log2 (succ_pos n).

Arguments pair_shell _ : assert.

Lemma pair_shell_eqn (n : N) : pair_shell n =
  log2 (1 + n).
Proof.
  cbv [pair_shell]. rewrite logging.
  rewrite succ_pos_spec. rewrite add_1_l. reflexivity. Qed.

Definition unpair_shell (p q : N) : N := p + pos_log2 (succ_pos (shiftl q 1)).

Arguments unpair_shell _ _ : assert.

Lemma unpair_shell_eqn (p q : N) : unpair_shell p q =
  log2 (binoddprod p (1 + 2 * q)).
Proof. cbv [unpair_shell]. arithmetize. Admitted.

Definition pair (n : N) : N * N :=
  let (p, q) := binoddfactor (succ n) in
  (p, shiftr (pred q) 1).
  (* (pos_binfactor (succ_pos n), shiftr (pred (pos_oddfactor (succ_pos n))) 1). *)

Arguments pair _ : assert.

Lemma pair_eqn (n : N) : pair n =
  (pos_binfactor (succ_pos n), (Npos (pos_oddfactor (succ_pos n)) - 1) / 2).
Proof. Admitted.

Definition unpair (p q : N) : N := pred (binoddprod p (succ (shiftl q 1))).

Arguments unpair _ _ : assert.

Lemma unpair_eqn (p q : N) : unpair p q =
  (1 + 2 * q) * 2 ^ p - 1.
Proof. cbv [unpair]. rewrite binoddprod_eqn. arithmetize. reflexivity. Qed.

Compute map pair (seq 0 64).
Compute map (prod_uncurry unpair o pair) (seq 0 64).

Compute map pair_shell (seq 0 64).
Compute map (prod_uncurry unpair_shell o pair) (seq 0 64).

Theorem unpair_shell' (n : N) :
  prod_uncurry unpair_shell (pair n) = pair_shell n.
Proof.
  cbv [prod_uncurry fst snd unpair_shell pair pair_shell]. Admitted.

Theorem pair_taco (p q : N) :
  pair_shell (unpair p q) = unpair_shell p q.
Proof.
  cbv [pair_shell unpair unpair_shell]. Admitted.

Theorem unpair_pair (n : N) : prod_uncurry unpair (pair n) = n.
Proof.
  cbv [prod_uncurry]. rewrite unpair_eqn. rewrite pair_eqn. cbv [fst snd].
  destruct (eqb_spec n 0) as [e | f].
  - subst n. reflexivity.
  - pose proof (part_urgh (succ_pos n)) as e.
    rewrite <- e. rewrite succ_pos_spec. lia. Qed.

Theorem pair_unpair (p q : N) : pair (unpair p q) = (p, q).
Proof.
  cbv [prod_uncurry]. rewrite pair_eqn. rewrite unpair_eqn.
  f_equal.
  - rewrite pos_binfactor_trivial. reflexivity.
  - rewrite pos_oddfactor_trivial.
    replace (1 + 2 * q - 1) with (2 * q) by lia.
    rewrite div_Even. reflexivity. Qed.

End Hausdorff.
