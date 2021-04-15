From Coq Require
  ssreflect.
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

(** We call the sizes of shells strides. *)

Class HasStride : Type := stride (a : N) : positive.

Class IsStride `(HasStride) : Prop := {}.

(** We call the first indexes of shells bases. *)

Class HasBase : Type := base (a : N) : N.

(** Bases should be strictly increasing,
    because shells are supposed to be nonempty. *)

Class IsMonoBase `(HasBase) : Prop :=
  mono_base (a b : N) (l : a < b) : base a < base b.

(** Bases should have a fixed point at zero,
    because shells are supposed to be a covering. *)

Class IsFixedBase `(HasBase) : Prop :=
  fixed_base : base 0 = 0.

Class IsBase `(HasBase) : Prop := {
  base_is_mono_base :> IsMonoBase base;
  base_is_fixed_base :> IsFixedBase base;
}.

(** Strides and bases both partition the natural numbers. *)

Class HasPartition `(HasStride) `(HasBase) : Type := partition : unit.

(** Bases are partial sums of strides. *)

Class IsPartialSum `(HasPartition) : Prop :=
  partial_sum (a : N) : base (succ a) = Npos (stride a) + base a.

Class IsPartition `(HasPartition) : Prop := {
  stride_is_stride :> IsStride stride;
  base_is_base :> IsBase base;
  partition_is_partial_sum :> IsPartialSum partition;
}.

(** Bases can be derived from strides and vice versa.
    Even though strides are easier to define than bases,
    it is generally more sensible to derive strides from bases,
    because differences (discrete derivatives) are easier to compute
    than partial sums (discrete integrals). *)

Module BaseFromStride.

Section Context.

Context `(IsStride).

(** Calculate the partial sum up to the given shell. *)

Equations base_fix (a : N) : N by wf (to_nat a) :=
  base_fix N0 := 0;
  base_fix (Npos n) :=
    let p := pred (Npos n) in
    Npos (stride p) + base_fix p.
Next Obligation. intros n f p. lia. Qed.

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
    rewrite succ_pos_spec. rewrite pred_succ.
    destruct (eqb_spec a p') as [e | f].
    + subst a. lia.
    + assert (l' : a < p') by lia. clear l f.
      apply li in l'. clear li.
      lia. Qed.

Local Instance is_fixed_base : IsFixedBase base.
Proof.
  hnf.
  unfold base, has_base.
  simp base_fix.
  reflexivity. Qed.

Local Instance is_base : IsBase base.
Proof. esplit; typeclasses eauto. Qed.

Local Instance has_partition : HasPartition stride base := tt.

Local Instance is_partial_sum : IsPartialSum partition.
Proof.
  intros a.
  unfold base, has_base.
  destruct a as [| n].
  - rewrite add_0_r.
    simp base_fix.
    cbv zeta.
    unfold pred. unfold Pos.pred_N.
    simp base_fix.
    reflexivity.
  - unfold succ.
    simp base_fix.
    cbv zeta.
    unfold pred.
    rewrite Pos.pred_N_succ.
    simp base_fix.
    cbv zeta.
    unfold pred.
    reflexivity. Qed.

Local Instance is_partition : IsPartition partition.
Proof. esplit; typeclasses eauto. Qed.

End Context.

End BaseFromStride.

Module StrideFromBase.

Section Context.

Context `(IsBase).

(** Calculate the difference up from the given shell. *)

Equations stride_def (a : N) : positive :=
  stride_def a :=
    let n := base (succ a) - base a in
    match n with
    | N0 => xH
    | Npos p => p
    end.

(** We could also write the definition without the absurd case,
    but its equations would become unnecessarily complicated. *)

Equations stride_def' (a : N) : positive :=
  stride_def' a :=
    let n := base (succ a) - base a in
    match n with
    | N0 => fun e : n = N0 => _
    | Npos p => fun e : n = Npos p => p
    end (eq_refl n).
Next Obligation.
  intros a n e.
  subst n.
  pose proof mono_base a (succ a) as l.
  lia. Qed.

Section Context.

Import ssreflect.

Lemma eq_stride_def (a : N) : stride_def' a = stride_def a.
Proof.
  simp stride_def' stride_def.
  cbv zeta.
  set (n := base (succ a) - base a).
  generalize (eq_refl n).
  case: {2 3 7} n.
  - intros e.
    subst n.
    pose proof mono_base a (succ a) as l.
    lia.
  - intros p e.
    reflexivity. Qed.

End Context.

Local Instance has_stride : HasStride := stride_def.

Local Instance is_stride : IsStride stride.
Proof. Qed.

Local Instance has_partition : HasPartition stride base := tt.

Local Instance is_partial_sum : IsPartialSum partition.
Proof.
  intros a.
  unfold stride, has_stride.
  simp stride_def.
  cbv zeta.
  destruct (base (succ a) - base a) as [| n] eqn : e.
  + pose proof mono_base a (succ a) as l. lia.
  + lia. Qed.

Local Instance is_partition : IsPartition partition.
Proof. esplit; typeclasses eauto. Qed.

End Context.

End StrideFromBase.

(** We place each natural number on a shell
    by assigning it an index in the infinite sequence and
    an index on the corresponding finite subinterval. *)

Class HasShell : Type := shell (n : N) : N * N.

(** The placement function is injective, but not surjective,
    unless we restrict the codomain to make it so. *)

Class HasShellDep `(HasStride) : Type :=
  shell_dep (n : N) : {x : N * N $ Squash (snd x < Npos (stride (fst x)))}.

(** The placement can be undone. *)

Class HasUnshell : Type := unshell (a b : N) : N.

Class HasUnshellDep `(HasStride) : Type :=
  unshell_dep (a b : N) (l : Squash (b < Npos (stride a))) : N.

(** We place each pair of natural numbers on a shell as well.
    Since the placement of pairs is intrinsically different
    from that of numbers, we call the shells tacos instead.
    The motive is that tacos are just more delicious kinds of shells,
    as you would expect, which we will prove later. *)

Class HasTaco : Type := taco (x y : N) : N * N.

Class HasTacoDep `(HasStride) : Type :=
  taco_dep (x y : N) : {x : N * N $ Squash (snd x < Npos (stride (fst x)))}.

Class HasUntaco : Type := untaco (a b : N) : N * N.

Class HasUntacoDep `(HasStride) : Type :=
  untaco_dep (a b : N) (l : Squash (b < Npos (stride a))) : N * N.

(** Shells and tacos are both ways to place things. *)

Class HasPlacement `(HasShell) `(HasUnshell) `(HasTaco) `(HasUntaco) : Type :=
  placement : unit.

Class HasPlacementDep `(HasStride)
  `(!HasShellDep stride) `(!HasUnshellDep stride)
  `(!HasTacoDep stride) `(!HasUntacoDep stride) : Type := placement_dep : unit.

(** The shell placement function is a section
    of the function that undoes it and thus
    the function that undoes it is a retraction
    of the shell placement function. *)

Class IsSectShell `(HasShell) `(HasUnshell) : Prop :=
  sect_shell (n : N) : prod_uncurry unshell (shell n) = n.

Class IsSectShellDep `(HasStride)
  `(!HasShellDep stride) `(!HasUnshellDep stride) : Prop :=
  sect_shell_dep (n : N) :
  Ssig_uncurry (prod_uncurry_dep unshell_dep) (shell_dep n) = n.

(** The shell placement function is not a retraction
    of the function that undoes it unless it is made surjective.
    The unrestricted version is only presented for the sake of completeness,
    as it would be suspect to be able to inhabit it. *)

Class IsRetrShell `(HasShell) `(HasUnshell) : Prop :=
  retr_shell (a b : N) : shell (unshell a b) = (a, b).

Class IsRetrShellDep `(HasStride)
  `(!HasShellDep stride) `(!HasUnshellDep stride) : Prop :=
  retr_shell_dep (a b : N) (l : Squash (b < Npos (stride a))) :
  shell_dep (unshell_dep a b l) = Sexists _ (a, b) l.

(** The shell placement function produces a lexicographic enumeration. *)

Class IsLexEnumShell `(HasShell) `(HasUnshell) : Prop :=
  lex_enum_shell (n : N) :
  fst (shell (succ n)) = fst (shell n) /\
  snd (shell (succ n)) = succ (snd (shell n)) \/
  fst (shell (succ n)) = succ (fst (shell n)) /\
  snd (shell (succ n)) = 0.

Class IsLexEnumShellDep `(HasStride)
  `(!HasShellDep stride) `(!HasUnshellDep stride) : Prop :=
  lex_enum_shell_dep (n : N) :
  fst (Spr1 (shell_dep (succ n))) = fst (Spr1 (shell_dep n)) /\
  snd (Spr1 (shell_dep (succ n))) = succ (snd (Spr1 (shell_dep n))) \/
  fst (Spr1 (shell_dep (succ n))) = succ (fst (Spr1 (shell_dep n))) /\
  snd (Spr1 (shell_dep (succ n))) = 0.

(** Lexicographic enumerations are just
    particular kinds of lexicographic orderings. *)

Class IsLexOrdShell `(HasShell) `(HasUnshell) : Prop :=
  lex_ord_shell (p n : N) (l : p < n) :
  fst (shell p) < fst (shell n) \/
  snd (shell p) < snd (shell n).

Class IsLexOrdShellDep `(HasStride)
  `(!HasShellDep stride) `(!HasUnshellDep stride) : Prop :=
  lex_ord_shell_dep (p n : N) (l : p < n) :
  fst (Spr1 (shell_dep p)) < fst (Spr1 (shell_dep n)) \/
  snd (Spr1 (shell_dep p)) < snd (Spr1 (shell_dep n)).

Global Instance is_lex_ord_shell `(IsLexEnumShell) :
  IsLexOrdShell shell unshell.
Proof.
  intros p n l.
  assert (x : exists q : N, n = p + succ q).
  { exists (n - p - 1). lia. }
  destruct x as [q e].
  subst n.
  generalize dependent p.
  induction q as [| r li] using peano_ind; intros p l.
  - clear l.
    replace (p + succ 0) with (succ p) by lia.
    pose proof (lex_enum_shell p) as e.
    destruct (shell p) as [p0 p1], (shell (succ p)) as [q0 q1].
    unfold fst, snd in *.
    lia.
  - destruct (eqb_spec p (p + succ r)) as [e | f].
    + lia.
    + assert (l' : p < p + succ r) by lia. clear l f.
      apply li in l'. rename l' into l.
      destruct l as [l0 | l1].
      * left.
        pose proof (lex_enum_shell (p + succ r)) as e.
        replace (succ (p + succ r)) with (p + succ (succ r)) in * by lia.
        repeat match goal with
        | x : context [@shell (@shell ?f)] |- _ =>
          change (@shell (@shell f)) with (@shell f) in x
        end.
        destruct (shell p) as [p0 p1],
        (shell (p + succ r)) as [q0 q1],
        (shell (p + succ (succ r))) as [r0 r1].
        unfold fst, snd in *.
        lia.
      * right.
        pose proof (lex_enum_shell (p + succ r)) as e.
        replace (succ (p + succ r)) with (p + succ (succ r)) in * by lia.
        repeat match goal with
        | x : context [@shell (@shell ?f)] |- _ =>
          change (@shell (@shell f)) with (@shell f) in x
        end.
        destruct (shell p) as [p0 p1],
        (shell (p + succ r)) as [q0 q1],
        (shell (p + succ (succ r))) as [r0 r1].
        unfold fst, snd in *.
        destruct e as [[e0 e1] | [e0 e1]].
        -- lia.
        -- subst. Abort.

Global Instance is_lex_ord_shell_dep `(IsLexEnumShellDep) :
  IsLexOrdShellDep stride shell_dep unshell_dep.
Proof.
  intros p n l. Abort.

(** The taco placement function has the same basic properties
    as the shell placement function,
    except for the emergence of a lexicographic enumeration. *)

Class IsSectTaco `(HasTaco) `(HasUntaco) : Prop :=
  sect_taco (x y : N) : prod_uncurry untaco (taco x y) = (x, y).

Class IsSectTacoDep `(HasStride)
  `(!HasTacoDep stride) `(!HasUntacoDep stride) : Prop :=
  sect_taco_dep (x y : N) :
  Ssig_uncurry (prod_uncurry_dep untaco_dep) (taco_dep x y) = (x, y).

Class IsRetrTaco `(HasTaco) `(HasUntaco) : Prop :=
  retr_taco (a b : N) : prod_uncurry taco (untaco a b) = (a, b).

Class IsRetrTacoDep `(HasStride)
  `(!HasTacoDep stride) `(!HasUntacoDep stride) : Prop :=
  retr_taco_dep (a b : N) (l : Squash (b < Npos (stride a))) :
  prod_uncurry taco_dep (untaco_dep a b l) = Sexists _ (a, b) l.

Class IsPlacement `(HasPlacement) : Prop := {
  shell_unshell_is_sect_shell :> IsSectShell shell unshell;
  (* shell_unshell_is_retr_shell :> IsRetrShell shell unshell; *)
  shell_unshell_is_lex_enum_shell :> IsLexEnumShell shell unshell;
  taco_untaco_is_sect_taco :> IsSectTaco taco untaco;
  (* taco_untaco_is_retr_taco :> IsRetrTaco taco untaco; *)
}.

Class IsPlacementDep `(HasPlacementDep) : Prop := {
  stride_shell_dep_unshell_dep_is_sect_shell_dep :>
    IsSectShellDep stride shell_dep unshell_dep;
  stride_shell_dep_unshell_dep_is_retr_shell_dep :>
    IsRetrShellDep stride shell_dep unshell_dep;
  stride_shell_dep_unshell_dep_is_lex_enum_shell_dep :>
    IsLexEnumShellDep stride shell_dep unshell_dep;
  stride_taco_dep_untaco_dep_is_sect_taco_dep :>
    IsSectTacoDep stride taco_dep untaco_dep;
  stride_taco_dep_untaco_dep_is_retr_taco_dep :>
    IsRetrTacoDep stride taco_dep untaco_dep;
}.

(** Shells can be derived from strides or bases, but tacos cannot.
    Once again, tacos prove to be the ultimate form of food
    that remains largely untamed. *)

Module ShellFromStride.

Section Context.

Context `(IsStride).

Import BaseFromStride.

Local Existing Instance has_base.
Local Existing Instance is_mono_base.
Local Existing Instance is_fixed_base.
Local Existing Instance is_base.
Local Existing Instance has_partition.
Local Existing Instance is_partial_sum.
Local Existing Instance is_partition.

Equations shell_fix (a b : N) : N * N by wf (to_nat b) :=
  shell_fix a b :=
    if sumbool_of_bool (b <? Npos (stride a)) then
    (a, b) else shell_fix (1 + a) (b - Npos (stride a)).
Next Obligation.
  intros a b f l.
  apply ltb_ge in l.
  lia. Qed.

Equations shell_def (n : N) : N * N :=
  shell_def n := shell_fix 0 n.

Local Instance has_shell : HasShell := shell_def.

Equations shell_dep_def (n : N) :
  {x : N * N $ Squash (snd x < Npos (stride (fst x)))} :=
  shell_dep_def n := Sexists _ (shell n) _.
Next Obligation.
  intros n.
  apply squash.
  unfold shell, has_shell, shell_def.
  apply shell_fix_elim.
  clear n.
  intros a b lab.
  destruct (sumbool_of_bool (b <? Npos (stride a))) as [l | l].
  - unfold fst, snd.
    apply ltb_lt in l.
    lia.
  - auto. Qed.

Local Instance has_shell_dep : HasShellDep stride := shell_dep_def.

Equations unshell_def (a b : N) : N :=
  unshell_def a b := b + base a.

Local Instance has_unshell : HasUnshell := unshell_def.

Equations unshell_dep_def (a b : N) (l : Squash (b < Npos (stride a))) : N :=
  unshell_dep_def a b l := unshell a b.

Local Instance has_unshell_dep : HasUnshellDep stride := unshell_dep_def.

Local Instance is_sect_shell : IsSectShell shell unshell.
Proof.
  intros n.
  unfold prod_uncurry.
  unfold PairingFunction.shell, shell, has_shell, shell_def,
  PairingFunction.unshell, unshell, has_unshell, unshell_def.
  induction n as [| p e] using peano_ind.
  - reflexivity.
  - rewrite shell_fix_equation_1 in *.
    destruct (sumbool_of_bool (p <? Npos (stride 0))),
    (sumbool_of_bool (succ p <? Npos (stride 0))).
    + unfold base, has_base.
      simp base_fix.
      rewrite add_0_r.
      reflexivity.
    + rewrite add_0_r.
      apply ltb_lt in e0.
      apply ltb_ge in e1.
      admit.
    + rewrite add_0_r.
      apply ltb_ge in e0.
      apply ltb_lt in e1.
      lia.
    + rewrite add_0_r in *.
      apply ltb_ge in e0.
      apply ltb_ge in e1. Abort.

Local Instance is_sect_shell_dep : IsSectShellDep stride shell_dep unshell_dep.
Proof.
  intros n.
  unfold Ssig_uncurry, prod_uncurry_dep.
  unfold PairingFunction.shell_dep, shell_dep, shell,
  PairingFunction.unshell_dep, unshell_dep, unshell.
  unfold Spr1. Abort.

Local Instance is_retr_shell_dep : IsRetrShellDep stride shell_dep unshell_dep.
Proof.
  intros a b l.
  unfold PairingFunction.shell_dep, shell_dep, shell.
  apply Spr1_inj.
  unfold Spr1.
  unfold PairingFunction.unshell_dep, unshell_dep, unshell. Abort.

Local Instance is_lex_enum_shell : IsLexEnumShell shell unshell.
Proof.
  intros n. Abort.

Local Instance is_lex_enum_shell_dep :
  IsLexEnumShellDep stride shell_dep unshell_dep.
Proof. Abort.

End Context.

End ShellFromStride.

Module ShellFromBase.

Section Context.

Context `(IsBase).

Import StrideFromBase.

Local Existing Instance has_stride.
Local Existing Instance is_stride.
Local Existing Instance has_partition.
Local Existing Instance is_partial_sum.
Local Existing Instance is_partition.

Equations shell_fix (a b : N) : N * N by wf (to_nat (b - base a)) :=
  shell_fix a b :=
    if sumbool_of_bool (b <? base (succ a)) then
    (a, b - base a) else shell_fix (succ a) b.
Next Obligation.
  intros a b f l.
  apply ltb_ge in l.
  pose proof mono_base a (succ a) as l'.
  lia. Qed.

Equations shell_def (n : N) : N * N :=
  shell_def n := shell_fix 0 n.

Local Instance has_shell : HasShell := shell_def.

Equations shell_dep_def (n : N) :
  {x : N * N $ Squash (snd x < Npos (stride (fst x)))} :=
  shell_dep_def n := Sexists _ (shell n) _.
Next Obligation.
  intros n.
  apply squash.
  unfold shell, has_shell, shell_def.
  apply shell_fix_elim.
  intros a b lab.
  pose proof mono_base a (succ a) as la.
  pose proof partial_sum a as ea.
  destruct (sumbool_of_bool (b <? base (succ a))) as [l | l].
  - unfold fst, snd.
    apply ltb_lt in l.
    lia.
  - auto. Qed.

Local Instance has_shell_dep : HasShellDep stride := shell_dep_def.

Equations unshell_def (a b : N) : N :=
  unshell_def a b := b + base a.

Local Instance has_unshell : HasUnshell := unshell_def.

Equations unshell_dep_def (a b : N) (l : Squash (b < Npos (stride a))) : N :=
  unshell_dep_def a b l := unshell a b.

Local Instance has_unshell_dep : HasUnshellDep stride := unshell_dep_def.

Local Instance is_sect_shell : IsSectShell shell unshell.
Proof. Abort.

Local Instance is_sect_shell_dep : IsSectShellDep stride shell_dep unshell_dep.
Proof. Abort.

Local Instance is_retr_shell_dep : IsRetrShellDep stride shell_dep unshell_dep.
Proof. Abort.

Local Instance is_lex_enum_shell : IsLexEnumShell shell unshell.
Proof. Abort.

Local Instance is_lex_enum_shell_dep :
  IsLexEnumShellDep stride shell_dep unshell_dep.
Proof. Abort.

End Context.

End ShellFromBase.

(** Some restricted versions can be derived
    from unrestricted ones and vice versa. *)

Module DepAndNondep.

Section Context.

Local Instance has_shell `(HasShellDep) : HasShell :=
  fun n : N => Spr1 (shell_dep n).

Local Instance has_unshell_dep `(HasStride) `(HasUnshell) :
  HasUnshellDep stride :=
  fun (a b : N) (l : Squash (b < Npos (stride a))) => unshell a b.

Local Instance has_taco `(HasTacoDep) : HasTaco :=
  fun x y : N => Spr1 (taco_dep x y).

Local Instance has_untaco_dep `(HasStride) `(HasUntaco) :
  HasUntacoDep stride :=
  fun (a b : N) (l : Squash (b < Npos (stride a))) => untaco a b.

Local Instance has_placement `(HasStride)
  `(!HasShellDep stride) `(HasUnshell) `(!HasTacoDep stride) `(HasUntaco) :
  HasPlacement shell unshell taco untaco := tt.

Fail Local Instance has_placement_dep `(HasStride)
  `(!HasShellDep stride) `(HasUnshell) `(!HasTacoDep stride) `(HasUntaco) :
  HasPlacementDep stride shell_dep unshell_dep taco_dep untaco_dep := tt.

Local Instance has_placement_dep `(HasStride)
  `(!HasShellDep stride) `(HasUnshell) `(!HasTacoDep stride) `(HasUntaco) :
  HasPlacementDep stride
  shell_dep (@unshell_dep stride (@has_unshell_dep stride unshell))
  taco_dep (@untaco_dep stride (@has_untaco_dep stride untaco)) := tt.

(*
Local Instance is_sect_shell_dep : IsSectShellDep stride shell_dep unshell_dep.
Proof.
  intros n.
  pose proof sect_shell n as e.
  unfold prod_uncurry in e.
  unfold Ssig_uncurry, prod_uncurry_dep.
  unfold unshell_dep, has_unshell_dep. Abort.

Local Instance is_retr_shell_dep : IsRetrShellDep stride shell_dep unshell_dep.
Proof. Abort.

Local Instance is_sect_taco_dep : IsSectTacoDep stride taco_dep untaco_dep.
Proof. Abort.

Local Instance is_retr_taco_dep : IsRetrTacoDep stride taco_dep untaco_dep.
Proof. Abort.

Local Instance is_placement_dep : IsPlacementDep placement_dep.
Proof. Abort.
*)

End Context.

End DepAndNondep.

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

Module PairingFromPlacement.

Section Context.

Context `(IsPlacementDep).

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

End PairingFromPlacement.

End PairingFunction.

Module Cantor.

Import PairingFunction.

Equations stride_def (a : N) : positive :=
  stride_def a := succ_pos a.

Global Instance has_stride : HasStride := stride_def.

Equations base_def (a : N) : N :=
  base_def a := tri a.

Global Instance has_base : HasBase := base_def.

Global Instance has_partition : HasPartition stride base := tt.

Global Instance is_mono_base : IsMonoBase base.
Proof. intros a b l. apply tri_lt_mono. auto. Qed.

Global Instance is_partial_sum : IsPartialSum partition.
Proof.
  intros a.
  unfold stride, has_stride, stride_def, base, has_base, base_def.
  rewrite <- add_1_l.
  rewrite tri_succ. rewrite succ_pos_spec.
  lia. Qed.

Equations shell_def (n : N) : N * N :=
  shell_def n := untri_rem n.

Global Instance has_shell : HasShell := shell_def.

Equations shell_dep_def (n : N) :
  {x : N * N $ Squash (snd x < Npos (stride (fst x)))} :=
  shell_dep_def n := Sexists _ (shell n) _.
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

Global Instance has_shell_dep : HasShellDep stride := shell_dep_def.

Equations unshell_def (a b : N) : N :=
  unshell_def a b := b + tri a.

Global Instance has_unshell : HasUnshell := unshell_def.

Equations unshell_dep_def (a b : N) (l : Squash (b < Npos (stride a))) : N :=
  unshell_dep_def a b l := unshell a b.

Global Instance has_unshell_dep : HasUnshellDep stride := unshell_dep_def.

Global Instance is_sect_shell_dep :
  IsSectShellDep stride shell_dep unshell_dep.
Proof.
  intros n.
  cbv [Ssig_uncurry Spr1 Spr2].
  unfold shell_dep, has_shell_dep, shell_dep_def.
  cbv [prod_uncurry_dep].
  unfold unshell_dep, has_unshell_dep, unshell_dep_def.
  unfold unshell, has_unshell, unshell_def.
  unfold shell, has_shell, shell_def.
  rewrite untri_rem_tri_untri.
  cbv [fst snd].
  pose proof tri_untri n as l.
  lia. Qed.

Global Instance is_retr_shell_dep :
  IsRetrShellDep stride shell_dep unshell_dep.
Proof.
  intros a b l.
  unfold shell_dep, has_shell_dep, shell_dep_def.
  apply Spr1_inj.
  cbv [Spr1].
  unfold shell, has_shell, shell_def.
  unfold unshell_dep, has_unshell_dep, unshell_dep_def.
  unfold unshell, has_unshell, unshell_def.
  apply unsquash in l.
  simp stride in l.
  rewrite succ_pos_spec in l.
  rewrite untri_rem_tri_untri.
  assert (l' : b <= a) by lia.
  pose proof tri_why a b l' as e.
  rewrite e.
  f_equal. lia. Qed.

Equations taco_def (x y : N) : N * N :=
  taco_def x y := (y + x, y).

Global Instance has_taco : HasTaco := taco_def.

Equations taco_dep_def (x y : N) :
  {x : N * N $ Squash (snd x < Npos (stride (fst x)))} :=
  taco_dep_def x y := Sexists _ (taco x y) _.
Next Obligation.
  intros x y.
  apply squash.
  unfold stride, has_stride, stride_def.
  rewrite succ_pos_spec.
  unfold taco, has_taco, taco_def.
  simp fst snd.
  lia. Qed.

Global Instance has_taco_dep : HasTacoDep stride := taco_dep_def.

Equations untaco_def (a b : N) : N * N :=
  untaco_def a b := (a - b, b).

Global Instance has_untaco : HasUntaco := untaco_def.

Equations untaco_dep_def (a b : N) (l : Squash (b < Npos (stride a))) : N * N :=
  untaco_dep_def a b l := untaco a b.

Global Instance has_untaco_dep : HasUntacoDep stride := untaco_dep_def.

Global Instance has_placement_dep :
  HasPlacementDep stride shell_dep unshell_dep taco_dep untaco_dep := tt.

Global Instance is_sect_taco_dep : IsSectTacoDep stride taco_dep untaco_dep.
Proof.
  intros x y.
  cbv [Ssig_uncurry Spr1 Spr2].
  unfold untaco_dep, has_untaco_dep, untaco_dep_def.
  cbv [prod_uncurry_dep].
  unfold taco_dep, has_taco_dep, taco_dep_def.
  unfold taco, has_taco, taco_def.
  unfold untaco, has_untaco, untaco_def.
  cbv [fst snd].
  f_equal.
  lia. Qed.

Global Instance is_retr_taco_dep : IsRetrTacoDep stride taco_dep untaco_dep.
Proof.
  intros a b l.
  cbv [prod_uncurry].
  unfold taco_dep, has_taco_dep, taco_dep_def.
  apply Spr1_inj.
  cbv [Spr1].
  unfold untaco_dep, has_untaco_dep, untaco_dep_def.
  unfold untaco, has_untaco, untaco_def.
  unfold taco, has_taco, taco_def.
  cbv [fst snd].
  f_equal.
  eapply unsquash in l.
  simp stride in l.
  rewrite succ_pos_spec in l.
  lia. Qed.

Local Instance is_lex_enum_shell_dep :
  IsLexEnumShellDep stride shell_dep unshell_dep.
Proof.
  intros n.
  unfold shell_dep, has_shell_dep, shell_dep_def.
  unfold Spr1.
  unfold shell, has_shell, shell_def.
  do 2 rewrite untri_rem_tri_untri.
  unfold fst, snd.
  destruct (eqb_spec (tri (untri (succ n))) (succ n)) as [e | f].
  Admitted.

Global Instance is_placement_dep : IsPlacementDep placement_dep.
Proof. esplit; typeclasses eauto. Qed.

Import PairingFromPlacement.

Local Existing Instance has_pair.
Local Existing Instance has_unpair.
Local Existing Instance has_pairing.

Global Instance has_pair : HasPair := pair.
Global Instance has_unpair : HasUnpair := unpair.
Global Instance has_pairing : HasPairing pair unpair := tt.

Local Existing Instance is_sect_pair.
Local Existing Instance is_retr_pair.
Local Existing Instance is_pairing.

(** TODO Why does type class resolution fail here? *)

Global Instance is_sect_pair : IsSectPair pairing.
Proof. apply is_pairing; typeclasses eauto. Qed.
Global Instance is_retr_pair : IsRetrPair pairing.
Proof. apply is_pairing; typeclasses eauto. Qed.
Global Instance is_pairing : IsPairing pairing.
Proof. esplit; typeclasses eauto. Qed.

End Cantor.

Module PF := PairingFunction.

Compute map PF.pair (seq 0 64).
Compute map (prod_uncurry PF.unpair o PF.pair) (seq 0 64).

(** TODO The rest of this module is in serious disrepair. *)

Module RosenbergStrong.

Definition pair_shell (n : N) : N := sqrt n.

Arguments pair_shell _ : assert.

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
