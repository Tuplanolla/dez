From Coq Require
  ssr.ssreflect.
From Coq Require Import
  Lia Lists.List NArith.NArith Bool.Sumbool.
From Maniunfold.Provides Require Export
  OptionTheorems PositiveTheorems ProductTheorems
  NBinaryOddFactoring NTriangularNumbers.

Import ListNotations N.

#[local] Open Scope N_scope.

(** We define pairing functions by partitioning natural numbers
    into an infinite sequence of finite subintervals, which we call shells. *)

(** We call the sizes of shells strides. *)

Class HasStride : Type := stride (a : N) : positive.

(** If we do not mark operational classes transparent,
    instance resolution will fail to unify
    [@HasShellDep (@stride (@stride H))] with [@HasShellDep (@stride H)]
    among other ones. *)

Typeclasses Transparent HasStride.

Class IsStride `(HasStride) : Prop := {}.

(** We call the first indexes of shells bases. *)

Class HasBase : Type := base (a : N) : N.

Typeclasses Transparent HasBase.

(** Bases should be strictly increasing,
    because shells are supposed to be nonempty. *)

Class IsStrictMonoBase `(HasBase) : Prop :=
  strict_mono_base (x y : N) (l : x < y) : base x < base y.

(** Bases should have a fixed point at zero,
    because shells are supposed to be a covering. *)

Class IsFixedBase `(HasBase) : Prop :=
  fixed_base : base 0 = 0.

Class IsBase `(HasBase) : Prop := {
  base_is_strict_mono_base :> IsStrictMonoBase base;
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

Equations base_fix (a : N) : N by wf a lt :=
  base_fix N0 := 0;
  base_fix (Npos p) :=
    let n := pred (Npos p) in
    Npos (stride n) + base_fix n.
Next Obligation. intros p _ n. lia. Qed.

#[local] Instance has_base : HasBase := base_fix.

#[local] Instance is_strict_mono_base : IsStrictMonoBase base.
Proof.
  intros a b l.
  unfold base, has_base.
  revert a l; induction b as [| c li] using peano_ind; intros a l.
  - lia.
  - rewrite <- succ_pos_spec.
    simp base_fix. cbv zeta.
    rewrite succ_pos_spec. rewrite pred_succ.
    destruct (eqb_spec a c) as [e | f].
    + subst c.
      clear l li.
      lia.
    + assert (lf : a < c) by lia.
      clear l f.
      apply li in lf.
      clear li.
      lia. Qed.

#[local] Instance is_fixed_base : IsFixedBase base.
Proof.
  hnf. unfold base, has_base. simp base_fix.
  reflexivity. Qed.

#[local] Instance is_base : IsBase base.
Proof. esplit; typeclasses eauto. Qed.

#[local] Instance has_partition : HasPartition stride base := tt.

#[local] Instance is_partial_sum : IsPartialSum partition.
Proof.
  intros a.
  unfold base, has_base.
  destruct a as [| p].
  - unfold succ. simp base_fix. cbv zeta. unfold pred.
    unfold Pos.pred_N. simp base_fix.
    reflexivity.
  - unfold succ. simp base_fix. cbv zeta. unfold pred.
    rewrite Pos.pred_N_succ.
    simp base_fix. cbv zeta. unfold pred.
    reflexivity. Qed.

#[local] Instance is_partition : IsPartition partition.
Proof. esplit; typeclasses eauto. Qed.

End Context.

#[export] Hint Resolve has_base is_strict_mono_base is_fixed_base is_base
  has_partition is_partial_sum is_partition : typeclass_instances.

End BaseFromStride.

Module StrideFromBase.

Section Context.

Context `(IsBase).

(** Calculate the difference up from the given shell. *)

Equations stride_def (a : N) : positive :=
  stride_def a with base (succ a) - base a := {
    | N0 => _;
    | Npos p => p
  }.
Next Obligation. intros a. apply xH. Qed.

(** We could also write the definition without the absurd case,
    but its equations would become unnecessarily complicated. *)

Section Context.

Equations stride_def' (a : N) : positive :=
  stride_def' a with exist _ (base (succ a) - base a) (eq_refl _) := {
    | exist _ N0 _ => _;
    | exist _ (Npos p) _ => p
  }.
Next Obligation.
  intros a e.
  pose proof strict_mono_base a (succ a) as l.
  lia. Qed.

Import ssreflect.

Lemma eq_stride_def' (a : N) : stride_def' a = stride_def a.
Proof.
  simp stride_def' stride_def.
  unfold stride_def'_clause_1, stride_def_clause_1.
  set (n := base (succ a) - base a).
  generalize (eq_refl n).
  case : {2 3 7} n.
  - intros e.
    subst n.
    pose proof strict_mono_base a (succ a) as l.
    lia.
  - intros p e.
    reflexivity. Qed.

End Context.

#[local] Instance has_stride : HasStride := stride_def.

#[local] Instance is_stride : IsStride stride.
Proof. Qed.

#[local] Instance has_partition : HasPartition stride base := tt.

#[local] Instance is_partial_sum : IsPartialSum partition.
Proof.
  intros a.
  unfold stride, has_stride. simp stride_def. unfold stride_def_clause_1.
  destruct (base (succ a) - base a) as [| n] eqn : e.
  + pose proof strict_mono_base a (succ a) as l. lia.
  + lia. Qed.

#[local] Instance is_partition : IsPartition partition.
Proof. esplit; typeclasses eauto. Qed.

End Context.

#[export] Hint Resolve has_stride is_stride
  has_partition is_partial_sum is_partition : typeclass_instances.

End StrideFromBase.

(** We place each natural number on a shell
    by assigning it an index in the infinite sequence and
    an index on the corresponding finite subinterval. *)

Class HasShell : Type := shell (n : N) : N * N.

Typeclasses Transparent HasShell.

(** The placement function is injective, but not surjective,
    unless we restrict the codomain to make it so. *)

Class HasShellDep `(HasStride) : Type :=
  shell_dep (n : N) : {x : N * N $ Squash (snd x < Npos (stride (fst x)))}.

Typeclasses Transparent HasShellDep.

(** The placement can be undone. *)

Class HasUnshell : Type := unshell (a b : N) : N.

Typeclasses Transparent HasUnshell.

Class HasUnshellDep `(HasStride) : Type :=
  unshell_dep (a b : N) (l : Squash (b < Npos (stride a))) : N.

Typeclasses Transparent HasUnshellDep.

(** We place each pair of natural numbers on a shell as well.
    Since the placement of pairs is intrinsically different
    from that of numbers, we call the shells tacos instead.
    The motive is that tacos are just more delicious kinds of shells,
    as you would expect, which we will prove later. *)

Class HasTaco : Type := taco (x y : N) : N * N.

Typeclasses Transparent HasTaco.

Class HasTacoDep `(HasStride) : Type :=
  taco_dep (x y : N) : {x : N * N $ Squash (snd x < Npos (stride (fst x)))}.

Typeclasses Transparent HasTacoDep.

Class HasUntaco : Type := untaco (a b : N) : N * N.

Typeclasses Transparent HasUntaco.

Class HasUntacoDep `(HasStride) : Type :=
  untaco_dep (a b : N) (l : Squash (b < Npos (stride a))) : N * N.

Typeclasses Transparent HasUntacoDep.

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
    of the function that undoes it,
    unless we restrict the codomain to make it so.
    The unrestricted version is only presented for the sake of completeness,
    as it would be suspect to inhabit it. *)

Class IsRetrShell `(HasShell) `(HasUnshell) : Prop :=
  retr_shell (a b : N) : shell (unshell a b) = (a, b).

Class IsRetrShellDep `(HasStride)
  `(!HasShellDep stride) `(!HasUnshellDep stride) : Prop :=
  retr_shell_dep (a b : N) (l : Squash (b < Npos (stride a))) :
  shell_dep (unshell_dep a b l) = Sexists _ (a, b) l.

(** The shell placement function produces a lexicographic enumeration. *)

Class IsLexEnumShell `(HasShell) : Prop := {
  lex_enum_zero_shell : shell 0 = (0, 0);
  lex_enum_succ_shell (n : N) :
    let (a, b) := shell n in
    shell (succ n) = (a, succ b) \/ shell (succ n) = (succ a, 0);
}.

Class IsLexEnumShellDep `(HasStride) `(!HasShellDep stride) : Prop := {
  lex_enum_zero_shell_dep : Spr1 (shell_dep 0) = (0, 0);
  lex_enum_succ_shell_dep (n : N) :
    let (a, b) := Spr1 (shell_dep n) in
    Spr1 (shell_dep (succ n)) = (a, succ b) \/
    Spr1 (shell_dep (succ n)) = (succ a, 0);
}.

(** Lexicographic enumerations are particular kinds
    of lexicographic orderings. *)

Class IsLexOrdShell `(HasShell) : Prop :=
  lex_ord_shell (p n : N) (l : p < n) :
  fst (shell p) < fst (shell n) \/
  fst (shell p) = fst (shell n) /\ snd (shell p) < snd (shell n).

Class IsLexOrdShellDep `(HasStride) `(!HasShellDep stride) : Prop :=
  lex_ord_shell_dep (p n : N) (l : p < n) :
  fst (Spr1 (shell_dep p)) < fst (Spr1 (shell_dep n)) \/
  fst (Spr1 (shell_dep p)) = fst (Spr1 (shell_dep n)) /\
  snd (Spr1 (shell_dep p)) < snd (Spr1 (shell_dep n)).

(** The sketch of this proof was contributed by David Holland.
    While the proof is not complicated,
    it is still surprisingly easy to get lost in it. *)

#[global] Instance is_lex_ord_shell `(IsLexEnumShell) : IsLexOrdShell shell.
Proof.
  intros p n l.
  generalize dependent p.
  induction n as [| q x] using peano_ind; intros p l.
  - lia.
  - destruct (eqb_spec p q) as [e | f].
    + subst p.
      clear l x.
      pose proof lex_enum_succ_shell q as e.
      destruct (shell q) as [a b], (shell (succ q)) as [a' b'].
      unfold fst, snd in *.
      destruct e as [e | e]; injection e; clear e; intros e0 e1.
      * subst a' b'.
        lia.
      * subst a' b'.
        lia.
    + assert (l' : p < q) by lia.
      specialize (x p l').
      clear l f l'.
      pose proof lex_enum_succ_shell q as e.
      destruct (shell q) as [a b], (shell (succ q)) as [a' b'].
      destruct e as [e | e]; injection e; clear e; intros e0 e1.
      * subst a' b'.
        destruct (shell p) as [a'' b''].
        unfold fst, snd in *.
        lia.
      * subst a' b'.
        destruct (shell p) as [a'' b''].
        unfold fst, snd in *.
        lia. Qed.

#[global] Instance is_lex_ord_shell_dep `(IsLexEnumShellDep) :
  IsLexOrdShellDep stride shell_dep.
Proof.
  intros p n l.
  generalize dependent p.
  induction n as [| q x] using peano_ind; intros p l.
  - lia.
  - destruct (eqb_spec p q) as [e | f].
    + subst p.
      clear l x.
      pose proof lex_enum_succ_shell_dep q as e.
      destruct (shell_dep q) as [[a b] l],
      (shell_dep (succ q)) as [[a' b'] l'].
      unfold fst, snd, Spr1 in *.
      destruct e as [e | e]; injection e; clear e; intros e0 e1.
      * subst a' b'.
        lia.
      * subst a' b'.
        lia.
    + assert (l' : p < q) by lia.
      specialize (x p l').
      clear l f l'.
      pose proof lex_enum_succ_shell_dep q as e.
      destruct (shell_dep q) as [[a b] l],
      (shell_dep (succ q)) as [[a' b'] l'].
      destruct e as [e | e]; injection e; clear e; intros e0 e1.
      * subst a' b'.
        destruct (shell_dep p) as [[a'' b''] l''].
        unfold fst, snd, Spr1 in *.
        lia.
      * subst a' b'.
        destruct (shell_dep p) as [[a'' b''] l''].
        unfold fst, snd, Spr1 in *.
        lia. Qed.

(** The taco placement function has the same basic properties
    as the shell placement function,
    with the exception that it does not produce a lexicographic enumeration. *)

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
  shell_unshell_is_lex_enum_shell :> IsLexEnumShell shell;
  taco_untaco_is_sect_taco :> IsSectTaco taco untaco;
  (* taco_untaco_is_retr_taco :> IsRetrTaco taco untaco; *)
}.

Class IsPlacementDep `(HasPlacementDep) : Prop := {
  shell_dep_unshell_dep_is_sect_shell_dep :>
    IsSectShellDep stride shell_dep unshell_dep;
  shell_dep_unshell_dep_is_retr_shell_dep :>
    IsRetrShellDep stride shell_dep unshell_dep;
  shell_dep_unshell_dep_is_lex_enum_shell_dep :>
    IsLexEnumShellDep stride shell_dep;
  taco_dep_untaco_dep_is_sect_taco_dep :>
    IsSectTacoDep stride taco_dep untaco_dep;
  taco_dep_untaco_dep_is_retr_taco_dep :>
    IsRetrTacoDep stride taco_dep untaco_dep;
}.

(** Some of the restricted versions can be derived
    from the unrestricted ones and vice versa.
    There is a minimal basis of definitions
    that covers every version without incurring an overhead. *)

Class HasPlacementBasis `(HasStride)
  `(!HasShellDep stride) `(HasUnshell)
  `(!HasTacoDep stride) `(HasUntaco) : Type :=
  placement_basis : unit.

Section Context.

Context `(HasPlacementBasis).

#[global] Instance has_shell : HasShell := fun n : N => Spr1 (shell_dep n).

#[global] Instance has_unshell_dep : HasUnshellDep stride :=
  fun (a b : N) (l : Squash (b < Npos (stride a))) => unshell a b.

#[global] Instance has_taco : HasTaco := fun x y : N => Spr1 (taco_dep x y).

#[global] Instance has_untaco_dep : HasUntacoDep stride :=
  fun (a b : N) (l : Squash (b < Npos (stride a))) => untaco a b.

#[global] Instance has_placement : HasPlacement shell unshell taco untaco := tt.

#[global] Instance has_placement_dep :
  HasPlacementDep stride shell_dep unshell_dep taco_dep untaco_dep := tt.

End Context.

(** The restricted and unrestricted
    section and enumeration properties are equally strong,
    while the retraction properties are not. *)

Module NondepFromDep.

Section Context.

Context `(HasPlacementBasis).

#[local] Instance is_sect_shell `(!IsSectShellDep stride shell_dep unshell_dep) :
  IsSectShell shell unshell.
Proof. exact sect_shell_dep. Qed.

#[local] Instance is_sect_taco `(!IsSectTacoDep stride taco_dep untaco_dep) :
  IsSectTaco taco untaco.
Proof. exact sect_taco_dep. Qed.

#[local] Instance is_lex_enum_shell `(!IsLexEnumShellDep stride shell_dep) :
  IsLexEnumShell shell.
Proof.
  esplit.
  - exact lex_enum_zero_shell_dep.
  - exact lex_enum_succ_shell_dep. Qed.

End Context.

#[export] Hint Resolve is_sect_shell is_sect_taco
  is_lex_enum_shell : typeclass_instances.

End NondepFromDep.

Module DepFromNondep.

Section Context.

Context `(HasPlacementBasis).

#[local] Instance is_sect_shell_dep `(!IsSectShell shell unshell) :
  IsSectShellDep stride shell_dep unshell_dep.
Proof. exact sect_shell. Qed.

(** Note that this instance is just the principle of explosion in disguise. *)

#[local] Instance is_retr_shell_dep `(!IsRetrShell shell unshell) :
  IsRetrShellDep stride shell_dep unshell_dep.
Proof.
  intros a b l.
  pose proof retr_shell a b as e.
  unfold shell, has_shell in e.
  unfold unshell_dep, has_unshell_dep.
  apply Spr1_inj.
  unfold Spr1.
  apply e. Qed.

#[local] Instance is_sect_taco_dep `(!IsSectTaco taco untaco) :
  IsSectTacoDep stride taco_dep untaco_dep.
Proof. exact sect_taco. Qed.

#[local] Instance is_retr_taco_dep `(!IsRetrTaco taco untaco) :
  IsRetrTacoDep stride taco_dep untaco_dep.
Proof.
  intros a b l.
  pose proof retr_taco a b as e.
  unfold prod_uncurry in e.
  unfold taco, has_taco in e.
  unfold prod_uncurry.
  unfold untaco_dep, has_untaco_dep.
  apply Spr1_inj.
  unfold Spr1.
  apply e. Qed.

#[local] Instance is_lex_enum_shell_dep `(!IsLexEnumShell shell) :
  IsLexEnumShellDep stride shell_dep.
Proof.
  esplit.
  - exact lex_enum_zero_shell.
  - exact lex_enum_succ_shell. Qed.

End Context.

#[export] Hint Resolve is_sect_shell_dep is_retr_shell_dep
  is_sect_taco_dep is_retr_taco_dep
  is_lex_enum_shell_dep : typeclass_instances.

End DepFromNondep.

(** Shells can be derived from strides or bases, but tacos cannot.
    Once again, tacos prove to be the ultimate form of food,
    remaining largely untamed. *)

Module ShellFromStride.

Section Context.

Context `(IsStride).

Import BaseFromStride.

Equations shell_fix (a b : N) : N * N by wf b lt :=
  shell_fix a b with sumbool_of_bool (b <? Npos (stride a)) => {
    | left _ => (a, b);
    | right _ => shell_fix (succ a) (b - Npos (stride a))
  }.
Next Obligation.
  intros a b l _.
  apply ltb_ge in l.
  lia. Qed.

Lemma shell_fix_invariant (a b a' b' : N) (e : shell_fix a b = (a', b')) :
  b' + base a' = b + base a.
Proof.
  simp shell_fix in e.
  destruct (sumbool_of_bool (b <? pos (stride a))) as [l | l].
  - simp shell_fix in e.
    apply ltb_lt in l.
    injection e. clear e. intros ea' eb'. subst a' b'.
    reflexivity.
  - simp shell_fix in e.
    apply ltb_ge in l.
    destruct (sumbool_of_bool (b - pos (stride a) <? pos (stride (succ a)))) as [l' | l'].
    + simp shell_fix in e.
      apply ltb_lt in l'.
      injection e. clear e. intros ea' eb'. subst a' b'.
      rewrite partial_sum.
      lia.
    + simp shell_fix in e.
      apply ltb_ge in l'. Restart.
  assert (eps : forall a : N, Npos (stride a) = base (succ a) - base a).
  { intros ?. rewrite partial_sum. lia. }
  simp shell_fix in e.
  unfold shell_fix_unfold_clause_1 in e. rewrite eps in e.
  induction a using peano_ind. admit. Abort.

Lemma shell_fix_fst (a b : N) : a <= fst (shell_fix a b).
Proof.
  apply_funelim (shell_fix a b).
  - clear a b. intros a b _ _.
    unfold fst.
    reflexivity.
  - clear a b. intros a b _ l _.
    lia. Qed.

Lemma shell_fix_snd (a b : N) : snd (shell_fix a b) <= b.
Proof.
  apply_funelim (shell_fix a b).
  - clear a b. intros a b _ _.
    unfold snd.
    reflexivity.
  - clear a b. intros a b _ l _.
    lia. Qed.

Lemma shell_fix_case_1 (a b : N) (l : b < Npos (stride a)) :
  shell_fix a b = (a, b).
Proof.
  simp shell_fix. unfold shell_fix_unfold_clause_1.
  apply ltb_lt in l. rewrite l.
  unfold sumbool_of_bool.
  reflexivity. Qed.

Lemma shell_fix_case_2 (a b : N) (l : Npos (stride a) <= b) :
  shell_fix a b = shell_fix (succ a) (b - Npos (stride a)).
Proof.
  rewrite shell_fix_equation_1. unfold shell_fix_unfold_clause_1.
  apply ltb_ge in l. rewrite l.
  unfold sumbool_of_bool.
  reflexivity. Qed.

Lemma shell_fix_case_2' (a b : N) :
  shell_fix a (b + Npos (stride a)) = shell_fix (succ a) b.
Proof.
  rewrite shell_fix_case_2 by lia.
  rewrite add_sub.
  reflexivity. Qed.

Lemma shell_fix_0_l' (a b : N) : shell_fix 0 (b + base a) = shell_fix a b.
Proof.
  generalize dependent b.
  induction a as [| a e] using peano_ind; intros b.
  - rewrite fixed_base. rewrite add_0_r.
    reflexivity.
  - rewrite partial_sum. rewrite add_assoc.
    specialize (e (b + Npos (stride a))).
    rewrite e. clear e.
    rewrite (shell_fix_equation_1 a). unfold shell_fix_unfold_clause_1.
    assert (l : Npos (stride a) <= b + Npos (stride a)) by lia.
    apply ltb_ge in l. rewrite l.
    unfold sumbool_of_bool.
    rewrite add_sub.
    reflexivity. Qed.

Lemma shell_fix_0_l (a b : N) (l : base a <= b) :
  shell_fix 0 b = shell_fix a (b - base a).
Proof.
  rewrite <- (shell_fix_0_l' a).
  rewrite sub_add by lia.
  reflexivity. Qed.

Lemma shell_fix_0_r (a : N) : shell_fix a 0 = (a, 0).
Proof.
  simp shell_fix. unfold shell_fix_unfold_clause_1.
  assert (l : 0 < Npos (stride a)) by lia.
  apply ltb_lt in l. rewrite l.
  unfold sumbool_of_bool.
  reflexivity. Qed.

Equations shell_dep_def (n : N) :
  {x : N * N $ Squash (snd x < Npos (stride (fst x)))} :=
  shell_dep_def n := Sexists _ (shell_fix 0 n) _.
Next Obligation.
  intros n.
  apply squash.
  apply_funelim (shell_fix 0 n).
  - clear n.
    intros a b l _.
    unfold fst, snd.
    apply ltb_lt in l.
    lia.
  - clear n.
    intros a b _ l _.
    auto. Qed.

#[local] Instance has_shell_dep : HasShellDep stride := shell_dep_def.

Equations unshell_def (a b : N) : N :=
  unshell_def a b := b + base a.

#[local] Instance has_unshell : HasUnshell := unshell_def.

Lemma lt_wf_ind (n : N) (P : N -> Prop)
  (g : forall (j : N) (x : forall (i : N) (l : i < j), P i), P j) : P n.
Proof. Admitted.

#[local] Instance is_sect_shell : IsSectShell shell unshell.
Proof.
  intros n.
  unfold prod_uncurry.
  unfold unshell, has_unshell, unshell_def.
  unfold shell, has_shell, shell_dep, has_shell_dep, shell_dep_def.
  unfold Spr1.
  (* Search N "induction". *)
  apply (lt_wf_ind n).
  intros p g.
  simp shell_fix in *. unfold shell_fix_unfold_clause_1 in *.
  destruct (ltb_spec n (Npos (stride 0))) as [l | l].
  - unfold sumbool_of_bool in *. unfold fst, snd in *.
    rewrite fixed_base in *. rewrite add_0_r in *. apply g. admit.
  - unfold sumbool_of_bool in *. apply g. admit.
  Restart.
  intros n.
  unfold prod_uncurry.
  unfold unshell, has_unshell, unshell_def.
  unfold shell, has_shell, shell_dep, has_shell_dep, shell_dep_def.
  unfold Spr1.
  remember 0 as a eqn : ea.
  (* apply_funelim (shell_fix a n).
  - clear n a ea. intros a b l _. unfold fst, snd. apply ltb_lt in l. *)
  revert a ea.
  induction n as [| p ep] using peano_ind; intros a ea.
  - subst a.
    simp shell_fix. unfold shell_fix_unfold_clause_1.
    assert (l : 0 < Npos (stride 0)) by lia.
    apply ltb_lt in l. rewrite l.
    unfold sumbool_of_bool. unfold fst, snd.
    rewrite fixed_base. rewrite add_0_r.
    reflexivity.
  - subst a.
    simp shell_fix. unfold shell_fix_unfold_clause_1.
    destruct (ltb_spec (succ p) (Npos (stride 0))) as [l' | l'].
    + unfold sumbool_of_bool. unfold fst, snd.
      rewrite fixed_base. rewrite add_0_r.
      reflexivity.
    + unfold sumbool_of_bool.
      pose proof shell_fix_case_2 _ _ l' as e.
      replace (succ p - Npos (stride 0))
      with (succ (p - Npos (stride 0))). Restart.
  intros n.
  unfold prod_uncurry.
  unfold unshell, has_unshell, unshell_def.
  unfold shell, has_shell, shell_dep, has_shell_dep, shell_dep_def.
  unfold Spr1.
  induction n as [| p ep] using peano_ind.
  - Admitted.

#[local] Instance is_retr_shell_dep : IsRetrShellDep stride shell_dep unshell_dep.
Proof.
  intros a b l.
  unfold unshell_dep, has_unshell_dep.
  unfold unshell, has_unshell, unshell_def.
  unfold shell_dep, has_shell_dep, shell_dep_def.
  apply Spr1_inj.
  unfold Spr1. Admitted.

#[local] Instance is_lex_enum_shell : IsLexEnumShell shell.
Proof. Admitted.

End Context.

#[export] Hint Resolve has_shell_dep has_unshell
  is_sect_shell is_retr_shell_dep is_lex_enum_shell : typeclass_instances.

End ShellFromStride.

Module ShellFromBase.

Section Context.

Context `(IsBase).

Import StrideFromBase.

Equations shell_fix (a b : N) : N * N by wf (b - base a) lt :=
  shell_fix a b with sumbool_of_bool (b <? base (succ a)) => {
    | left _ => (a, b - base a);
    | right _ => shell_fix (succ a) b
  }.
Next Obligation.
  intros a b l _.
  apply ltb_ge in l.
  pose proof strict_mono_base a (succ a) as l'.
  lia. Qed.

Hint Unfold shell_fix_unfold_clause_1 : shell_fix.

Equations shell_dep_def (n : N) :
  {x : N * N $ Squash (snd x < Npos (stride (fst x)))} :=
  shell_dep_def n := Sexists _ (shell_fix 0 n) _.
Next Obligation.
  intros n.
  apply squash.
  unfold shell, has_shell.
  apply shell_fix_elim.
  - intros a b l _.
    pose proof strict_mono_base a (succ a) as la.
    pose proof partial_sum a as ea.
    unfold fst, snd.
    apply ltb_lt in l.
    lia.
  - intros a b _ l _.
    auto. Qed.

#[local] Instance has_shell_dep : HasShellDep stride := shell_dep_def.

Equations unshell_def (a b : N) : N :=
  unshell_def a b := b + base a.

#[local] Instance has_unshell : HasUnshell := unshell_def.

#[local] Instance is_sect_shell : IsSectShell shell unshell.
Proof.
  intros n.
  unfold prod_uncurry.
  unfold unshell, has_unshell, unshell_def.
  unfold shell, has_shell, shell_dep, has_shell_dep, shell_dep_def.
  unfold Spr1.
  induction n as [| p e] using peano_ind.
  - simp shell_fix. unfold shell_fix_unfold_clause_1.
    rewrite partial_sum. rewrite fixed_base. rewrite add_0_r.
    assert (l : 0 < Npos (stride 0)) by lia.
    apply ltb_lt in l.
    rewrite l.
    unfold sumbool_of_bool. unfold fst, snd.
    rewrite fixed_base.
    reflexivity.
  - simp shell_fix in *. unfold shell_fix_unfold_clause_1 in *.
    destruct (eqb_spec (succ p) (base (succ 0))) as [e' | f'].
    + rewrite e'.
      clear e.
      assert (l : base (succ 0) <= base (succ 0)) by lia.
      apply ltb_ge in l.
      rewrite l.
      unfold sumbool_of_bool. admit. Admitted.

#[local] Instance is_retr_shell_dep : IsRetrShellDep stride shell_dep unshell_dep.
Proof. Admitted.

#[local] Instance is_lex_enum_shell : IsLexEnumShell shell.
Proof. Admitted.

End Context.

#[export] Hint Unfold shell_fix_unfold_clause_1 : shell_fix.

#[export] Hint Resolve has_shell_dep has_unshell
  is_sect_shell is_retr_shell_dep is_lex_enum_shell : typeclass_instances.

End ShellFromBase.

(** Pairing functions witness the isomorphism
    between natural numbers and pairs of natural numbers. *)

Class HasPair : Type := pair (n : N) : N * N.

Typeclasses Transparent HasPair.

Class HasUnpair : Type := unpair (x y : N) : N.

Typeclasses Transparent HasUnpair.

Class HasPairing `(HasPair) `(HasUnpair) : Type := pairing : unit.

Class IsSectPair `(HasPairing) : Prop :=
  sect_pair (n : N) : prod_uncurry unpair (pair n) = n.

Class IsRetrPair `(HasPairing) : Prop :=
  retr_pair (x y : N) : pair (unpair x y) = (x, y).

Class IsPairing `(HasPairing) : Prop := {
  pairing_is_sect_pair :> IsSectPair pairing;
  pairing_is_retr_pair :> IsRetrPair pairing;
}.

(** Pairing functions can be derived
    from placement functions by diagram chasing. *)

Module PairingFromPlacement.

Section Context.

Context `(IsPlacementDep).

Equations pair_def (n : N) : N * N :=
  pair_def n := Ssig_uncurry (prod_uncurry_dep untaco_dep) (shell_dep n).

#[local] Instance has_pair : HasPair := pair_def.

Equations unpair_def (x y : N) : N :=
  unpair_def x y := Ssig_uncurry (prod_uncurry_dep unshell_dep) (taco_dep x y).

#[local] Instance has_unpair : HasUnpair := unpair_def.

#[local] Instance has_pairing : HasPairing pair unpair := tt.

#[local] Instance is_sect_pair : IsSectPair pairing.
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

#[local] Instance is_retr_pair : IsRetrPair pairing.
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

#[local] Instance is_pairing : IsPairing pairing.
Proof. esplit; typeclasses eauto. Qed.

End Context.

#[export] Hint Resolve has_pair has_unpair has_pairing
  is_sect_pair is_sect_pair is_pairing : typeclass_instances.

End PairingFromPlacement.

(** We start by defining the Cantor pairing function.
    We instantiate more classes than is absolutely necessary,
    because it yields better performance and
    deeper insights into the nature of the function. *)

Module Cantor.

Equations stride_def (a : N) : positive :=
  stride_def a := succ_pos a.

#[local] Instance has_stride : HasStride := stride_def.

Equations base_def (a : N) : N :=
  base_def a := tri a.

#[local] Instance has_base : HasBase := base_def.

#[local] Instance has_partition : HasPartition stride base := tt.

#[local] Instance is_strict_mono_base : IsStrictMonoBase base.
Proof. intros a b l. apply tri_lt_mono. auto. Qed.

#[local] Instance is_fixed_base : IsFixedBase base.
Proof. reflexivity. Qed.

#[local] Instance is_base : IsBase base.
Proof. esplit; typeclasses eauto. Qed.

#[local] Instance is_partial_sum : IsPartialSum partition.
Proof.
  intros a.
  unfold stride, has_stride, stride_def, base, has_base, base_def.
  rewrite <- add_1_l.
  rewrite tri_succ. rewrite succ_pos_spec.
  lia. Qed.

(*
Scheme Equality for prod.
Import ShellFromStride.
Compute map (fun bx => map (b2n o fun b =>
  implb (succ (snd (shell_fix 0 b)) <? Npos (stride (fst (shell_fix 0 b))))
  (prod_beq eqb eqb (shell_fix 0 (succ b)) (prod_rmap succ (shell_fix 0 b)))
  ) (seq 0 24)) (seq 0 16).
Compute map (fun bx => map (b2n o fun b =>
  implb (succ (snd (shell_fix 0 b)) =? Npos (stride (fst (shell_fix 0 b))))
  (prod_beq eqb eqb (shell_fix 0 (succ b)) (prod_bimap succ (const 0) (shell_fix 0 b)))
  ) (seq 0 24)) (seq 0 16).
*)

Equations shell_def (n : N) : N * N :=
  shell_def n := untri_rem n.

#[local] Instance has_shell : HasShell := shell_def.

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

#[local] Instance has_shell_dep : HasShellDep stride := shell_dep_def.

Equations unshell_def (a b : N) : N :=
  unshell_def a b := b + tri a.

#[local] Instance has_unshell : HasUnshell := unshell_def.

Equations unshell_dep_def (a b : N) (l : Squash (b < Npos (stride a))) : N :=
  unshell_dep_def a b l := unshell a b.

#[local] Instance has_unshell_dep : HasUnshellDep stride := unshell_dep_def.

#[local] Instance is_sect_shell_dep :
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

#[local] Instance is_retr_shell_dep :
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

#[local] Instance has_taco : HasTaco := taco_def.

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

#[local] Instance has_taco_dep : HasTacoDep stride := taco_dep_def.

Equations untaco_def (a b : N) : N * N :=
  untaco_def a b := (a - b, b).

#[local] Instance has_untaco : HasUntaco := untaco_def.

Equations untaco_dep_def (a b : N) (l : Squash (b < Npos (stride a))) : N * N :=
  untaco_dep_def a b l := untaco a b.

#[local] Instance has_untaco_dep : HasUntacoDep stride := untaco_dep_def.

#[local] Instance has_placement_dep :
  HasPlacementDep stride shell_dep unshell_dep taco_dep untaco_dep := tt.

#[local] Instance is_sect_taco_dep : IsSectTacoDep stride taco_dep untaco_dep.
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

#[local] Instance is_retr_taco_dep : IsRetrTacoDep stride taco_dep untaco_dep.
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

#[local] Instance is_lex_enum_shell_dep :
  IsLexEnumShellDep stride shell_dep.
Proof.
  split.
  - reflexivity.
  - intros n.
    unfold shell_dep, has_shell_dep, shell_dep_def.
    unfold Spr1.
    unfold shell, has_shell, shell_def.
    do 2 rewrite untri_rem_tri_untri.
    destruct (eqb_spec (tri (untri (succ n))) (succ n)) as [e | f].
    + rewrite e. rewrite sub_diag.
      right. f_equal.
      admit.
    + left.
      f_equal.
      * admit.
      * do 2 rewrite <- add_1_l.
        pose proof tri_untri n as l.
        rewrite add_sub_assoc by lia.
        f_equal.
        admit.
    Admitted.

#[local] Instance is_placement_dep : IsPlacementDep placement_dep.
Proof. esplit; typeclasses eauto. Qed.

Import PairingFromPlacement.

#[local] Instance has_pair : HasPair := pair.
#[local] Instance has_unpair : HasUnpair := unpair.
#[local] Instance has_pairing : HasPairing pair unpair := tt.

#[local] Instance is_sect_pair : IsSectPair pairing.
Proof. typeclasses eauto. Qed.
#[local] Instance is_retr_pair : IsRetrPair pairing.
Proof. typeclasses eauto. Qed.
#[local] Instance is_pairing : IsPairing pairing.
Proof. esplit; typeclasses eauto. Qed.

#[export] Hint Resolve has_pair has_unpair has_pairing
  is_sect_pair is_sect_pair is_pairing : typeclass_instances.

End Cantor.

Import Cantor.
Compute map pair (seq 0 64).
Compute map (prod_uncurry unpair o pair) (seq 0 64).

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

(*
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
*)
