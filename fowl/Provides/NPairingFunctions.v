From Coq Require Import
  Lia Lists.List NArith.NArith Bool.Sumbool.
From Maniunfold.Has Require Export
  OneSorted.Decision.
From Maniunfold.Provides Require Export
  OptionTheorems PositiveTheorems ProductTheorems
  NBinaryOddFactoring NTriangularNumbers.

Import ListNotations N.

Local Open Scope N_scope.

(** We define pairing functions by partitioning natural numbers
    into an infinite sequence of finite subintervals, which we call shells. *)

Module PairingFunction.

(** We call the sizes of the shells strides. *)

Class HasStride : Type := stride (a : N) : positive.

(** We call first indexes of the shells bases. *)

Class HasBase : Type := base (a : N) : N.

(** Bases have to be strictly increasing,
    since shells are always nonempty. *)

Class IsMonoBase `(HasBase) : Prop :=
  mono_base (a a' : N) (l : a < a') : base a < base a'.

(** Strides and bases both partition the natural numbers. *)

Class HasPartition `(HasStride) `(HasBase) : Type := partition : unit.

(** Bases are partial sums of strides. *)

Class IsPartialSum `(HasPartition) : Prop :=
  partial_sum (a : N) : base (1 + a) = Npos (stride a) + base a.

(** Bases can be derived from strides and vice versa.
    It is generally more sensible to derive strides from bases,
    since partial sums (discrete integrals) are harder to compute
    than differences (discrete derivatives). *)

Module BaseFromStride.

Section Context.

Context `(HasStride).

Equations base_fix (a : N) : N by wf (to_nat a) :=
  base_fix N0 := 0;
  base_fix (Npos n) :=
    let p := pred (Npos n) in
    Npos (stride p) + base_fix p.
Next Obligation. intros a f p. lia. Qed.

Local Instance has_base : HasBase := base_fix.

Local Instance is_mono_base : IsMonoBase base.
Proof.
  intros a a' l.
  unfold base, has_base.
  generalize dependent a.
  induction a' as [| p' li] using peano_ind; intros a l.
  - lia.
  - rewrite <- succ_pos_spec.
    simp base_fix.
    cbv zeta.
    rewrite succ_pos_spec.
    rewrite pred_succ.
    destruct (eqb_spec a p') as [e | f].
    + subst a. lia.
    + assert (l' : a < p') by lia.
      apply li in l'.
      clear li.
      lia. Qed.

Local Instance has_partition : HasPartition stride base := tt.

Local Instance is_partial_sum : IsPartialSum partition.
Proof.
  intros a.
  unfold base, has_base.
  destruct a as [| n].
  - rewrite add_0_r.
    simp base_fix.
    cbv zeta.
    simp pred. simp pred_N.
    simp base_fix.
    rewrite add_0_r.
    reflexivity.
  - replace (1 + Npos n) with (Npos (Pos.succ n)) by lia.
    simp base_fix.
    cbv zeta.
    simp pred.
    rewrite Pos.pred_N_succ.
    simp base_fix.
    cbv zeta.
    change (pred (Npos n)) with (Pos.pred_N n).
    reflexivity. Qed.

End Context.

End BaseFromStride.

Module StrideFromBase.

Section Context.

Context `(HasBase).

Equations stride_def (a : N) : positive by wf (to_nat a) :=
  stride_def a :=
  match base (succ a) - base a with
  | N0 => xH
  | Npos n => n
  end%N.

Local Instance has_stride : HasStride := stride_def.

Local Instance has_partition : HasPartition stride base := tt.

Context `(!IsMonoBase base).

Local Instance is_partial_sum : IsPartialSum partition.
Proof.
  intros a.
  unfold stride, has_stride.
  destruct a as [| p].
  - rewrite add_0_r.
    simp stride_def.
    change (succ 0) with 1.
    destruct (base 1 - base 0) as [| n] eqn : e.
    + pose proof mono_base 0 1 as l. lia.
    + lia.
  - simp stride_def.
    replace (succ (Npos p)) with (1 + Npos p) by lia.
    destruct (base (1 + Npos p) - base (Npos p)) as [| n] eqn : e.
    + pose proof mono_base (Npos p) (1 + Npos p) as l. lia.
    + lia. Qed.

End Context.

End StrideFromBase.

Class HasShell : Type := shell (n : N) : N * N.

Class HasShellDep `(HasStride) : Type :=
  shell_dep (n : N) : {x : N * N $ Squash (snd x < Npos (stride (fst x)))}.

Class HasUnshell : Type := unshell (a b : N) : N.

Class HasUnshellDep `(HasStride) : Type :=
  unshell_dep (a b : N) (l : Squash (b < Npos (stride a))) : N.

Class HasTaco : Type := taco (x y : N) : N * N.

Class HasTacoDep `(HasStride) : Type :=
  taco_dep (x y : N) : {x : N * N $ Squash (snd x < Npos (stride (fst x)))}.

Class HasUntaco : Type := untaco (a b : N) : N * N.

Class HasUntacoDep `(HasStride) : Type :=
  untaco_dep (a b : N) (l : Squash (b < Npos (stride a))) : N * N.

Class HasLifting `(HasShell) `(HasUnshell) `(HasTaco) `(HasUntaco) : Type :=
  lifting : unit.

Class HasLiftingDep `(HasStride)
  `(!HasShellDep stride) `(!HasUnshellDep stride)
  `(!HasTacoDep stride) `(!HasUntacoDep stride) : Type := lifting_dep : unit.

(** We avoid defining instances involving interplay
    between dependent and nondependent versions of the same type classes,
    because they quickly lead into circular dependencies. *)

(** We can derive dependent versions from nondependent ones. *)

Module DepFromNondep.

Section Context.

Context `(HasStride) `(HasShell) `(HasUnshell) `(HasTaco) `(HasUntaco).

Equations shell_dep_fix (a b : N) :
  {x : N * N $ Squash (snd x < Npos (stride (fst x)))} by wf (to_nat b) :=
  shell_dep_fix a b := if sumbool_of_bool (b <? Npos (stride a)) then
  Sexists _ (a, b) _ else shell_dep_fix (1 + a) (b - Npos (stride a)).
Next Obligation.
  intros a b f e.
  apply squash.
  simp fst snd.
  destruct (ltb_spec0 b (Npos (stride a))) as [l | l]; lia. Qed.
Next Obligation.
  intros a b f e.
  destruct (ltb_spec0 b (Npos (stride a))) as [l | l]; lia. Qed.

Equations shell_dep_def (n : N) :
  {x : N * N $ Squash (snd x < Npos (stride (fst x)))} :=
  shell_dep_def n := prod_uncurry shell_dep_fix (shell n).

Local Instance has_shell_dep : HasShellDep stride :=
  fun n : N => shell_dep_def n.

Local Instance has_unshell_dep : HasUnshellDep stride :=
  fun (a b : N) (l : Squash (b < Npos (stride a))) => unshell a b.

Equations taco_dep_fix (a b : N) :
  {x : N * N $ Squash (snd x < Npos (stride (fst x)))} by wf (to_nat b) :=
  taco_dep_fix a b := if sumbool_of_bool (b <? Npos (stride a)) then
  Sexists _ (a, b) _ else taco_dep_fix (1 + a) (b - Npos (stride a)).
Next Obligation.
  intros a b f e.
  apply squash.
  simp fst snd.
  destruct (ltb_spec0 b (Npos (stride a))) as [l | l]; lia. Qed.
Next Obligation.
  intros a b f e.
  destruct (ltb_spec0 b (Npos (stride a))) as [l | l]; lia. Qed.

Equations taco_dep_def (x y : N) :
  {x : N * N $ Squash (snd x < Npos (stride (fst x)))} :=
  taco_dep_def x y :=
  prod_uncurry taco_dep_fix (taco x y).

Local Instance has_taco_dep : HasTacoDep stride :=
  taco_dep_def.

Local Instance has_untaco_dep : HasUntacoDep stride :=
  fun (a b : N) (l : Squash (b < Npos (stride a))) => untaco a b.

Local Instance has_lifting_dep :
  HasLiftingDep stride shell_dep unshell_dep taco_dep untaco_dep := tt.

End Context.

End DepFromNondep.

(** We can also derive nondependent versions from dependent ones. *)

Module NondepFromDep.

Section Context.

Context `(HasStride)
  `(!HasShellDep stride) `(!HasUnshellDep stride)
  `(!HasTacoDep stride) `(!HasUntacoDep stride).

Local Instance has_shell : HasShell := fun n : N => Spr1 (shell_dep n).

Equations unshell_fix (a b : N) : N by wf (to_nat b) :=
  unshell_fix a b := if sumbool_of_bool (b <? Npos (stride a)) then
  unshell_dep a b _ else unshell_fix (1 + a) (b - Npos (stride a)).
Next Obligation.
  intros a b f e.
  apply squash.
  destruct (ltb_spec b (Npos (stride a))) as [l | l]; lia. Qed.
Next Obligation.
  intros a b f e.
  destruct (ltb_spec b (Npos (stride a))) as [l | l]; lia. Qed.

Local Instance has_unshell : HasUnshell := unshell_fix.

Local Instance has_taco : HasTaco := fun x y : N => Spr1 (taco_dep x y).

Equations untaco_fix (a b : N) : N * N by wf (to_nat b) :=
  untaco_fix a b := if sumbool_of_bool (b <? Npos (stride a)) then
  untaco_dep a b _ else untaco_fix (1 + a) (b - Npos (stride a)).
Next Obligation.
  intros a b f e.
  apply squash.
  destruct (ltb_spec b (Npos (stride a))) as [l | l]; lia. Qed.
Next Obligation.
  intros a b f e.
  destruct (ltb_spec b (Npos (stride a))) as [l | l]; lia. Qed.

Local Instance has_untaco : HasUntaco := untaco_fix.

Local Instance has_lifting : HasLifting shell unshell taco untaco := tt.

End Context.

End NondepFromDep.

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
  retr_shell_dep (a b : N) (l : Squash (b < Npos (stride a))) :
  shell_dep (unshell_dep a b l) = Sexists _ (a, b) l.

Class IsSectTaco `(HasLifting) : Prop :=
  sect_taco (x y : N) : prod_uncurry untaco (taco x y) = (x, y).

Class IsSectTacoDep `(HasLiftingDep) : Prop :=
  sect_taco_dep (x y : N) :
  Ssig_uncurry (prod_uncurry_dep untaco_dep) (taco_dep x y) = (x, y).

Class IsRetrTaco `(HasLifting) : Prop :=
  retr_taco (a b : N) : prod_uncurry taco (untaco a b) = (a, b).

Class IsRetrTacoDep `(HasLiftingDep) : Prop :=
  retr_taco_dep (a b : N) (l : Squash (b < Npos (stride a))) :
  prod_uncurry taco_dep (untaco_dep a b l) = Sexists _ (a, b) l.

(** Lexicographic enumeration implies lexicographic ordering. *)

Class IsLexOrdShell `(HasLifting) : Prop :=
  lex_ord_shell (p n : N) :
  fst (shell p) < fst (shell n) \/
  snd (shell p) < snd (shell n).

Class IsLexOrdShellDep `(HasLiftingDep) : Prop :=
  lex_ord_shell_dep (p n : N) :
  fst (Spr1 (shell_dep p)) < fst (Spr1 (shell_dep n)) \/
  snd (Spr1 (shell_dep p)) < snd (Spr1 (shell_dep n)).

Class IsLexEnumShell `(HasLifting) : Prop :=
  lex_enum_shell (p n : N) :
  fst (shell p) < fst (shell n) /\ snd (shell n) = 0 \/
  fst (shell n) = fst (shell p) /\ snd (shell p) < snd (shell n).

Class IsLexEnumShellDep `(HasLiftingDep) : Prop :=
  lex_enum_shell_dep (p n : N) :
  fst (Spr1 (shell_dep p)) < fst (Spr1 (shell_dep n)) /\
  snd (Spr1 (shell_dep n)) = 0 \/
  fst (Spr1 (shell_dep n)) = fst (Spr1 (shell_dep p)) /\
  snd (Spr1 (shell_dep p)) < snd (Spr1 (shell_dep n)).

Global Instance is_lex_ord_shell `(IsLexEnumShell) : IsLexOrdShell lifting.
Proof.
  intros p n.
  destruct (lex_enum_shell p n) as [[l0 l1] | [l0 l1]]; auto. Qed.

Global Instance is_lex_ord_shell_dep `(IsLexEnumShellDep) :
  IsLexOrdShellDep lifting_dep.
Proof.
  intros p n.
  destruct (lex_enum_shell_dep p n) as [[l0 l1] | [l0 l1]]; auto. Qed.

Class IsLifting `(HasLifting) : Prop := {
  lifting_is_sect_shell :> IsSectShell lifting;
  (* lifting_is_retr_shell :> IsRetrShell lifting; *)
  lifting_is_sect_taco :> IsSectTaco lifting;
  (* lifting_is_retr_taco :> IsRetrTaco lifting; *)
  (* lifting_is_lex_enum_shell :> IsLexEnumShell lifting; *)
}.

Class IsLiftingDep `(HasLiftingDep) : Prop := {
  lifting_dep_is_sect_shell_dep :> IsSectShellDep lifting_dep;
  lifting_dep_is_retr_shell_dep :> IsRetrShellDep lifting_dep;
  lifting_dep_is_sect_taco_dep :> IsSectTacoDep lifting_dep;
  lifting_dep_is_retr_taco_dep :> IsRetrTacoDep lifting_dep;
  (* lifting_dep_is_lex_enum_shell_dep :> IsLexEnumShellDep lifting_dep; *)
}.

Section Context.

Import NondepFromDep.

Local Existing Instance has_shell.
Local Existing Instance has_unshell.
Local Existing Instance has_taco.
Local Existing Instance has_untaco.
Local Existing Instance has_lifting.

(** This can be done, but retractions should not be possible. *)

Local Instance is_sect_shell `(IsSectShellDep) : IsSectShell lifting_dep.
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
  destruct (sumbool_of_bool (b <? pos (stride a))) as [e' | e'].
  - apply e.
  - apply ltb_ge in e'. pose proof lt_le_trans _ _ _ l' e'. lia. Qed.

End Context.

Class HasPair : Type := pair (n : N) : N * N.

Class HasUnpair : Type := unpair (x y : N) : N.

Class HasPairing `(HasPair) `(HasUnpair) : Type :=
  pairing : unit.

Class IsSectPair `(HasPairing) : Prop :=
  sect_pair (n : N) : prod_uncurry unpair (pair n) = n.

Class IsRetrPair `(HasPairing) : Prop :=
  retr_pair (x y : N) : pair (unpair x y) = (x, y).

Class IsPairing `(HasPairing) : Prop := {
  pairing_is_sect_pair :> IsSectPair pairing;
  pairing_is_retr_pair :> IsRetrPair pairing;
}.

Module PairingFromLifting.

Section Context.

Context `(HasLiftingDep).

Fail Equations pair_def (n : N) : N * N :=
  pair_def n := prod_uncurry untaco (shell n).

Equations pair_def (n : N) : N * N :=
  pair_def n := Ssig_uncurry (prod_uncurry_dep untaco_dep) (shell_dep n).

Fail Equations unpair_def (x y : N) : N :=
  unpair_def x y := prod_uncurry unshell (taco x y).

Equations unpair_def (x y : N) : N :=
  unpair_def x y := Ssig_uncurry (prod_uncurry_dep unshell_dep) (taco_dep x y).

Local Instance has_pair : HasPair := pair_def.
Local Instance has_unpair : HasUnpair := unpair_def.
Local Instance has_pairing : HasPairing pair unpair := tt.

Context `(!IsLiftingDep lifting_dep).

Local Instance is_sect_pair : IsSectPair pairing.
Proof.
  intros n.
  unfold pair, has_pair, unpair, has_unpair.
  destruct (pair_def n) as [x y] eqn : exy.
  simp pair_def in exy.
  destruct (shell_dep n) as [[a b] l] eqn : eab.
  simp Ssig_uncurry in exy. simp prod_uncurry_dep in exy.
  simp prod_uncurry. simp unpair_def.
  destruct (taco_dep x y) as [[a' b'] l'] eqn : eab'.
  simp Ssig_uncurry. simp prod_uncurry_dep.
  pose proof retr_taco_dep a b l as loop_t.
  pose proof sect_shell_dep n as loop_s.
  (** We need to reduce implicit arguments before rewriting. *)
  unfold stride in loop_t.
  (** Contract [t ^-1]. *)
  rewrite exy in loop_t.
  simp prod_uncurry in loop_t. rewrite eab' in loop_t.
  inversion loop_t; subst a' b'.
  (* assert (l' = l) by reflexivity; subst l'. *)
  clear loop_t.
  (** Contract [s]. *)
  rewrite eab in loop_s.
  simp Ssig_uncurry in loop_s. Qed.

Local Instance is_retr_pair : IsRetrPair pairing.
Proof.
  intros x y.
  unfold pair, has_pair, unpair, has_unpair.
  simp pair_def.
  destruct (shell_dep (unpair_def x y)) as [[a b] l] eqn : eab.
  simp unpair_def in eab.
  destruct (taco_dep x y) as [[a' b'] l'] eqn : eab'.
  simp Ssig_uncurry in eab. simp prod_uncurry_dep in eab.
  simp Ssig_uncurry. simp prod_uncurry_dep.
  pose proof retr_shell_dep a' b' l' as loop_s.
  pose proof sect_taco_dep x y as loop_t.
  (** We need to reduce implicit arguments before rewriting. *)
  unfold stride in loop_s.
  (** Contract [s ^-1]. *)
  rewrite eab in loop_s.
  inversion loop_s; subst a' b'.
  (* assert (l' = l) by reflexivity; subst l'. *)
  clear loop_s.
  (** Contract [t]. *)
  rewrite eab' in loop_t.
  simp Ssig_uncurry in loop_t. Qed.

Local Instance is_pairing : IsPairing pairing.
Proof. esplit; typeclasses eauto. Qed.

End Context.

End PairingFromLifting.

End PairingFunction.

Module Cantor.

Equations stride (a : N) : positive :=
  stride a := succ_pos a.

Equations base (a : N) : N :=
  base a := tri a.

Lemma mono_base (a b : N) (l : a < b) : base a < base b.
Proof. apply tri_lt_mono. auto. Qed.

Lemma partial_sum (a : N) : base (1 + a) = Npos (stride a) + base a.
Proof. unfold stride, base. rewrite tri_succ. rewrite succ_pos_spec. lia. Qed.

Equations shell (n : N) : N * N :=
  shell n := untri_rem n.

Equations shell_dep (n : N) :
  {x : N * N $ Squash (snd x < Npos (stride (fst x)))} :=
  shell_dep n := Sexists _ (shell n) _.
Next Obligation.
  intros n.
  apply squash.
  simp stride.
  rewrite succ_pos_spec.
  simp shell.
  rewrite untri_rem_tri_untri.
  simp fst snd.
  pose proof tri_untri_untri_rem n as l.
  lia. Qed.

Equations unshell (a b : N) : N :=
  unshell a b := b + tri a.

Equations unshell_dep (a b : N) (l : Squash (b < Npos (stride a))) : N :=
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

Lemma retr_shell_dep (a b : N) (l : Squash (b < Npos (stride a))) :
  shell_dep (unshell_dep a b l) = Sexists _ (a, b) l.
Proof.
  simp shell_dep.
  apply Spr1_inj.
  cbv [Spr1].
  simp shell.
  simp unshell_dep.
  simp unshell.
  eapply unsquash in l.
  simp stride in l.
  rewrite succ_pos_spec in l.
  rewrite untri_rem_tri_untri.
  assert (l' : b <= a) by lia.
  pose proof tri_why a b l' as e.
  rewrite e.
  f_equal. lia. Qed.

Equations taco (x y : N) : N * N :=
  taco x y := (y + x, y).

Equations taco_dep (x y : N) :
  {x : N * N $ Squash (snd x < Npos (stride (fst x)))} :=
  taco_dep x y := Sexists _ (taco x y) _.
Next Obligation.
  intros x y.
  apply squash.
  simp stride.
  rewrite succ_pos_spec.
  simp taco.
  simp fst snd.
  lia. Qed.

Equations untaco (a b : N) : N * N :=
  untaco a b := (a - b, b).

Equations untaco_dep (a b : N) (l : Squash (b < Npos (stride a))) : N * N :=
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

Lemma retr_taco_dep (a b : N) (l : Squash (b < Npos (stride a))) :
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
  simp stride in l.
  rewrite succ_pos_spec in l.
  lia. Qed.

Local Notation pred_N := Pos.pred_N.

Lemma lex_shell_dep (n a b : N) (e : Spr1 (shell_dep n) = (a, b)) :
  Spr1 (shell_dep (1 + n)) = (a, 1 + b) \/
  Spr1 (shell_dep (1 + n)) = (1 + a, 0).
Proof.
  simp shell_dep in *. unfold Spr1 in *. simp shell in *.
  rewrite untri_rem_tri_untri in *.
  injection e. clear e. intros ea eb.
  subst a b.
  destruct (eqb_spec (1 + n) (tri (untri (1 + n)))) as [e | f].
  - right. f_equal.
    + admit.
    + rewrite <- e. lia.
  - left. f_equal.
    + admit.
    + admit. Admitted.

Module PF := PairingFunction.

Global Instance has_stride : PF.HasStride := stride.
Global Instance has_base : PF.HasBase := base.
Global Instance has_partition : PF.HasPartition stride base := tt.
Global Instance has_shell_dep : PF.HasShellDep stride := shell_dep.
Global Instance has_unshell_dep : PF.HasUnshellDep stride := unshell_dep.
Global Instance has_taco_dep : PF.HasTacoDep stride := taco_dep.
Global Instance has_untaco_dep : PF.HasUntacoDep stride := untaco_dep.
Global Instance has_lifting_dep :
  PF.HasLiftingDep stride shell_dep unshell_dep taco_dep untaco_dep := tt.

Global Instance is_mono_base : PF.IsMonoBase base.
Proof. exact @mono_base. Qed.
Global Instance is_partial_sum : PF.IsPartialSum PF.partition.
Proof. exact @partial_sum. Qed.
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

Import PF.PairingFromLifting.

Local Existing Instance has_pair.
Local Existing Instance has_unpair.
Local Existing Instance has_pairing.

Global Instance has_pair : PF.HasPair := PF.pair.
Global Instance has_unpair : PF.HasUnpair := PF.unpair.
Global Instance has_pairing : PF.HasPairing PF.pair PF.unpair := tt.

Local Existing Instance is_sect_pair.
Local Existing Instance is_retr_pair.
Local Existing Instance is_pairing.

(** TODO Why does type class resolution fail here? *)

Global Instance is_sect_pair : PF.IsSectPair PF.pairing.
Proof. apply is_pairing; typeclasses eauto. Qed.
Global Instance is_retr_pair : PF.IsRetrPair PF.pairing.
Proof. apply is_pairing; typeclasses eauto. Qed.
Global Instance is_pairing : PF.IsPairing PF.pairing.
Proof. esplit; typeclasses eauto. Qed.

End Cantor.

Module PF := PairingFunction.

Compute map PF.pair (seq 0 64).
Compute map (prod_uncurry PF.unpair o PF.pair) (seq 0 64).

(** TODO The rest of this module is in serious disrepair. *)

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
