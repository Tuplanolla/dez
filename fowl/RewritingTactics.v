(** * Higher-Order Tactics for Rewriting *)

From DEZ Require Export
  Init.

(** Reduce a call to the given [1]-parameter function
    in the goal and hypotheses.
    The call to the function [f] is only reduced when
    the argument at index [0]
    satisfies the tactical predicate [p0]. *)

Ltac reduce_1 p0 f :=
  match goal with
  | |- context c [f ?x0] =>
    p0 x0;
    let a := context c [f x0] in
    match eval cbv in (f x0) with
    | ?y => let b := context c [y] in
      change a with b
    end
  | h : context c [f ?x0] |- _ =>
    p0 x0;
    let a := context c [f x0] in
    match eval cbv in (f x0) with
    | ?y => let b := context c [y] in
      change a with b in h
    end
  end.

(** Reduce a call to the given [2]-parameter function
    in the goal and hypotheses.
    The call to the function [f] is only reduced when
    the arguments at indexes [0] and [1]
    satisfy the tactical predicates [p0] and [p1]. *)

Ltac reduce_2 p0 p1 f :=
  match goal with
  | |- context c [f ?x0 ?x1] =>
    p0 x0; p1 x1;
    let a := context c [f x0 x1] in
    match eval cbv in (f x0 x1) with
    | ?y => let b := context c [y] in
      change a with b
    end
  | h : context c [f ?x0 ?x1] |- _ =>
    p0 x0; p1 x1;
    let a := context c [f x0 x1] in
    match eval cbv in (f x0 x1) with
    | ?y => let b := context c [y] in
      change a with b in h
    end
  end.

(** Reduce a call to the given [3]-parameter function
    in the goal and hypotheses.
    The call to the function [f] is only reduced when
    the arguments at indexes [0], [1] and [2]
    satisfy the tactical predicates [p0], [p1] and [p2]. *)

Ltac reduce_3 p0 p1 p2 f :=
  match goal with
  | |- context c [f ?x0 ?x1 ?x2] =>
    p0 x0; p1 x1; p2 x2;
    let a := context c [f x0 x1 x2] in
    match eval cbv in (f x0 x1 x2) with
    | ?y => let b := context c [y] in
      change a with b
    end
  | h : context c [f ?x0 ?x1 ?x2] |- _ =>
    p0 x0; p1 x1; p2 x2;
    let a := context c [f x0 x1 x2] in
    match eval cbv in (f x0 x1 x2) with
    | ?y => let b := context c [y] in
      change a with b in h
    end
  end.

(** The tactics from [reduce_4] onwards can be defined analogously. *)

Ltac reduce_4 p0 p1 p2 p3 f :=
  fail "Not implemented".

(** Commute the arguments of a call
    to the given [2]-parameter function in the goal and hypotheses,
    so that the argument at index [0] comes first
    (there are no other guarantees as the ordering is partial).
    The arguments of the function [f] are only sorted when
    it makes the argument at the appropriate index
    satisfy the tactical predicate [p],
    can be justified by the equality [e] and
    makes progress in the proof.
    The possible outcomes are the following.

    - [replace (f 0 1) with (f 0 1) by idtac]
    - [replace (f 0 y) with (f 0 y) by idtac]
    - [replace (f x 1) with (f 1 x)]
      - [by rewrite comm_0_1]
      - [by rewrite cycle_2]
    - [replace (f x y) with (f x y) by fail] *)

Ltac recomm_2_0 p f e :=
  match goal with
  | |- context c [f ?x0 ?x1] =>
    assert_fails (idtac; p x0); p x1;
    let a := context c [f x0 x1] in
    let b := context c [f x1 x0] in
    replace a with b by (rewrite (e x0 x1); reflexivity)
  | h : context c [f ?x0 ?x1] |- _ =>
    assert_fails (idtac; p x0); p x1;
    let a := context c [f x0 x1] in
    let b := context c [f x1 x0] in
    replace a with b in h by (rewrite (e x0 x1); reflexivity)
  end.

(** Commute the arguments of a call
    to the given [2]-parameter function in the goal and hypotheses,
    so that the argument at index [1] comes first
    (there are no other guarantees as the ordering is partial).
    The arguments of the function [f] are only sorted when
    it makes the argument at the appropriate index
    satisfy the tactical predicate [p],
    can be justified by the equality [e] and
    makes progress in the proof. *)

Ltac recomm_2_1 p f e :=
  match goal with
  | |- context c [f ?x0 ?x1] =>
    assert_fails (idtac; p x1); p x0;
    let a := context c [f x0 x1] in
    let b := context c [f x1 x0] in
    replace a with b by (rewrite (e x0 x1); reflexivity)
  | h : context c [f ?x0 ?x1] |- _ =>
    assert_fails (idtac; p x1); p x0;
    let a := context c [f x0 x1] in
    let b := context c [f x1 x0] in
    replace a with b in h by (rewrite (e x0 x1); reflexivity)
  end.

(** Commute the arguments of a call
    to the given [3]-parameter function in the goal and hypotheses,
    so that the argument at index [0] comes first
    (there are no other guarantees as the ordering is partial).
    The arguments of the function [f] are only sorted when
    it makes the argument at the appropriate index
    satisfy the tactical predicate [p],
    can be justified by the equality [e] and
    makes progress in the proof.
    The possible outcomes are the following.

    - [replace (f 0 1 2) with (f 0 1 2) by idtac]
    - [replace (f 0 1 z) with (f 0 1 z) by idtac]
    - [replace (f 0 y 2) with (f 0 y 2) by idtac]
    - [replace (f 0 y z) with (f 0 y z) by idtac]
    - [replace (f x 1 2)]
      - [with (f 1 x 2) by rewrite comm_0_1]
      - [with (f 2 1 x) by rewrite comm_0_2]
      - [with (f 2 x 1) by rewrite cycle_3]
      - [with (f 1 2 x) by rewrite <- cycle_3]
    - [replace (f x 1 z)]
      - [with (f 1 x z) by rewrite comm_0_1]
      - [with (f 1 z x) by rewrite <- cycle_3]
    - [replace (f x y 2)]
      - [with (f 2 y x) by rewrite comm_0_2]
      - [with (f 2 x y) by rewrite cycle_3]
    - [replace (f x y z) with (f x y z) by fail] *)

Ltac recomm_3_0 p f e :=
  match goal with
  | |- context c [f ?x0 ?x1 ?x2] => first [
    assert_fails (idtac; p x0); p x1; first [
    let a := context c [f x0 x1 x2] in
    let b := context c [f x1 x0 x2] in
    replace a with b by (rewrite (e x0 x1); reflexivity) |
    let a := context c [f x0 x1 x2] in
    let b := context c [f x1 x2 x0] in
    replace a with b by (rewrite <- (e x1 x2 x0); reflexivity)] |
    assert_fails (idtac; p x0); p x2; first [
    let a := context c [f x0 x1 x2] in
    let b := context c [f x2 x1 x0] in
    replace a with b by (rewrite (e x0 x1 x2); reflexivity) |
    let a := context c [f x0 x1 x2] in
    let b := context c [f x2 x0 x1] in
    replace a with b by (rewrite (e x0 x1 x2); reflexivity)]]
  | h : context c [f ?x0 ?x1 ?x2] |- _ => first [
    assert_fails (idtac; p x0); p x1; first [
    let a := context c [f x0 x1 x2] in
    let b := context c [f x1 x0 x2] in
    replace a with b in h by (rewrite (e x0 x1); reflexivity) |
    let a := context c [f x0 x1 x2] in
    let b := context c [f x1 x2 x0] in
    replace a with b in h by (rewrite <- (e x1 x2 x0); reflexivity)] |
    assert_fails (idtac; p x0); p x2; first [
    let a := context c [f x0 x1 x2] in
    let b := context c [f x2 x1 x0] in
    replace a with b in h by (rewrite (e x0 x1 x2); reflexivity) |
    let a := context c [f x0 x1 x2] in
    let b := context c [f x2 x0 x1] in
    replace a with b in h by (rewrite (e x0 x1 x2); reflexivity)]]
  end.

(** Commute the arguments of a call
    to the given [3]-parameter function in the goal and hypotheses,
    so that the argument at index [1] comes first
    (there are no other guarantees as the ordering is partial).
    The arguments of the function [f] are only sorted when
    it makes the argument at the appropriate index
    satisfy the tactical predicate [p],
    can be justified by the equality [e] and
    makes progress in the proof. *)

Ltac recomm_3_1 p f e :=
  match goal with
  | |- context c [f ?x0 ?x1 ?x2] => first [
    assert_fails (idtac; p x1); p x0; first [
    let a := context c [f x0 x1 x2] in
    let b := context c [f x1 x0 x2] in
    replace a with b by (rewrite (e x0 x1); reflexivity) |
    let a := context c [f x0 x1 x2] in
    let b := context c [f x2 x0 x1] in
    replace a with b by (rewrite (e x0 x1 x2); reflexivity)] |
    assert_fails (idtac; p x1); p x2; first [
    let a := context c [f x0 x1 x2] in
    let b := context c [f x0 x2 x1] in
    replace a with b by (rewrite (e x0 x1 x2); reflexivity) |
    let a := context c [f x0 x1 x2] in
    let b := context c [f x1 x2 x0] in
    replace a with b by (rewrite <- (e x1 x2 x0); reflexivity)]]
  | h : context c [f ?x0 ?x1 ?x2] |- _ => first [
    assert_fails (idtac; p x1); p x0; first [
    let a := context c [f x0 x1 x2] in
    let b := context c [f x1 x0 x2] in
    replace a with b in h by (rewrite (e x0 x1); reflexivity) |
    let a := context c [f x0 x1 x2] in
    let b := context c [f x2 x0 x1] in
    replace a with b in h by (rewrite (e x0 x1 x2); reflexivity)] |
    assert_fails (idtac; p x1); p x2; first [
    let a := context c [f x0 x1 x2] in
    let b := context c [f x0 x2 x1] in
    replace a with b in h by (rewrite (e x0 x1 x2); reflexivity) |
    let a := context c [f x0 x1 x2] in
    let b := context c [f x1 x2 x0] in
    replace a with b in h by (rewrite <- (e x1 x2 x0); reflexivity)]]
  end.

(** Commute the arguments of a call
    to the given [3]-parameter function in the goal and hypotheses,
    so that the argument at index [2] comes first
    (there are no other guarantees as the ordering is partial).
    The arguments of the function [f] are only sorted when
    it makes the argument at the appropriate index
    satisfy the tactical predicate [p],
    can be justified by the equality [e] and
    makes progress in the proof. *)

Ltac recomm_3_2 p f e :=
  match goal with
  | |- context c [f ?x0 ?x1 ?x2] => first [
    assert_fails (idtac; p x2); p x0; first [
    let a := context c [f x0 x1 x2] in
    let b := context c [f x2 x1 x0] in
    replace a with b by (rewrite (e x0 x1 x2); reflexivity) |
    let a := context c [f x0 x1 x2] in
    let b := context c [f x1 x2 x0] in
    replace a with b by (rewrite <- (e x1 x2 x0); reflexivity)] |
    assert_fails (idtac; p x2); p x1; first [
    let a := context c [f x0 x1 x2] in
    let b := context c [f x0 x2 x1] in
    replace a with b by (rewrite (e x0 x1 x2); reflexivity) |
    let a := context c [f x0 x1 x2] in
    let b := context c [f x2 x0 x1] in
    replace a with b by (rewrite (e x0 x1 x2); reflexivity)]]
  | h : context c [f ?x0 ?x1 ?x2] |- _ => first [
    assert_fails (idtac; p x2); p x0; first [
    let a := context c [f x0 x1 x2] in
    let b := context c [f x2 x1 x0] in
    replace a with b in h by (rewrite (e x0 x1); reflexivity) |
    let a := context c [f x0 x1 x2] in
    let b := context c [f x1 x2 x0] in
    replace a with b in h by (rewrite <- (e x1 x2 x0); reflexivity)] |
    assert_fails (idtac; p x2); p x1; first [
    let a := context c [f x0 x1 x2] in
    let b := context c [f x0 x2 x1] in
    replace a with b in h by (rewrite (e x0 x1 x2); reflexivity) |
    let a := context c [f x0 x1 x2] in
    let b := context c [f x2 x0 x1] in
    replace a with b in h by (rewrite (e x0 x1 x2); reflexivity)]]
  end.

(** The tactics from [recomm_4_0] onwards can be defined analogously. *)

Ltac recomm_4_0 p f e :=
  fail "Not implemented".

Ltac recomm_4_1 p f e :=
  fail "Not implemented".

Ltac recomm_4_2 p f e :=
  fail "Not implemented".

Ltac recomm_4_3 p f e :=
  fail "Not implemented".

(** Associate the arguments of two nested calls
    to the given [2]-parameter function in the goal and hypotheses,
    so that the arguments at the deeper level come first
    (there are no other guarantees as the ordering is partial).
    The arguments of the function [f] are only reassociated when
    it makes the arguments at the appropriate indexes
    satisfy the tactical predicate [p],
    can be justified by the equality [e10] and
    makes progress in the proof.
    The possible outcomes are the following,
    where the alternatives involving least work are favored
    (including number of rewrites and uses of symmetry).

    - [replace (f (f 0 1) 2)]
      - [with (f (f 0 1) 2) by idtac]
      - [with (f 0 (f 1 2)) by assoc_2_0_1]
    - [replace (f (f 0 1) z) with (f (f 0 1) z) by idtac]
    - [replace (f (f 0 y) 2) with (f (f 0 y) 2) by fail]
    - [replace (f (f 0 y) z) with (f (f 0 y) z) by fail]
    - [replace (f (f x 1) 2) with (f x (f 1 2)) by rewrite assoc_2_0_1]
    - [replace (f (f x 1) z) with (f (f x 1) z) by fail]
    - [replace (f (f x y) 2) with (f (f x y) 2) by fail]
    - [replace (f (f x y) z) with (f (f x y) z) by fail]

    - [replace (f 0 (f 1 2))]
      - [with (f (f 0 1) 2) by <- assoc_2_0_1]
      - [with (f 0 (f 1 2)) by idtac]
    - [replace (f 0 (f 1 z)) with (f (f 0 1) z) by rewrite <- assoc_2_0_1]
    - [replace (f 0 (f y 2)) with (f 0 (f y 2)) by fail]
    - [replace (f 0 (f y z)) with (f 0 (f y z)) by fail]
    - [replace (f x (f 1 2)) with (f x (f 1 2)) by idtac]
    - [replace (f x (f 1 z)) with (f x (f 1 z)) by fail]
    - [replace (f x (f y 2)) with (f x (f y 2)) by fail]
    - [replace (f x (f y z)) with (f x (f y z)) by fail] *)

Ltac reassoc_2 p f e10 :=
  match goal with
  | |- context c [f (f ?x0 ?x1) ?x2] =>
    assert_fails (idtac; p x0); p x1; p x2;
    let a := context c [f (f x0 x1) x2] in
    let b := context c [f x0 (f x1 x2)] in
    replace a with b by (rewrite <- (e10 x0 x1 x2); reflexivity)
  | |- context c [f ?x0 (f ?x1 ?x2)] =>
    assert_fails (idtac; p x2); p x0; p x1;
    let a := context c [f x0 (f x1 x2)] in
    let b := context c [f (f x0 x1) x2] in
    replace a with b by (rewrite (e10 x0 x1 x2); reflexivity)
  | h : context c [f (f ?x0 ?x1) ?x2] |- _ =>
    assert_fails (idtac; p x0); p x1; p x2;
    let a := context c [f (f x0 x1) x2] in
    let b := context c [f x0 (f x1 x2)] in
    replace a with b in h by (rewrite <- (e10 x0 x1 x2); reflexivity)
  | h : context c [f ?x0 (f ?x1 ?x2)] |- _ =>
    assert_fails (idtac; p x2); p x0; p x1;
    let a := context c [f x0 (f x1 x2)] in
    let b := context c [f (f x0 x1) x2] in
    replace a with b in h by (rewrite (e10 x0 x1 x2); reflexivity)
  end.

(** Associate the arguments of two nested calls
    to the given [3]-parameter function in the goal and hypotheses,
    so that the arguments at the deeper level come first
    (there are no other guarantees as the ordering is partial).
    The arguments of the function [f] are only reassociated when
    it makes the arguments at the appropriate indexes
    satisfy the tactical predicate [p],
    can be justified by the equalities [e10] and [e21] and
    makes progress in the proof.
    The possible outcomes are the following,
    where the alternatives involving least work are favored
    (including number of rewrites and uses of symmetry).

    - [replace (f (f 0 1 2) 3 4)]
      - [with (f (f 0 1 2) 3 4) by idtac]
      - [with (f 0 (f 1 2 3) 4) by rewrite assoc_3_0_1]
      - [with (f 0 1 (f 2 3 4)) by rewrite assoc_3_0_1, assoc_3_1_2]
    - [replace (f (f 0 1 2) 3 b)]
      - [with (f (f 0 1 2) 3 b) by idtac]
      - [with (f 0 (f 1 2 3) b) by rewrite assoc_3_0_1]
    - [replace (f (f 0 1 2) a 4) with (f (f 0 1 2) a 4) by idtac]
    - [replace (f (f 0 1 2) a b) with (f (f 0 1 2) a b) by idtac]
    - [replace (f (f 0 1 z) 3 4) with (f (f 0 1 z) 3 4) by fail]
    - [replace (f (f 0 1 z) 3 b) with (f (f 0 1 z) 3 b) by fail]
    - [replace (f (f 0 1 z) a 4) with (f (f 0 1 z) a 4) by fail]
    - [replace (f (f 0 1 z) a b) with (f (f 0 1 z) a b) by fail]
    - [replace (f (f 0 y 2) 3 4) with (f 0 y (f 2 3 4))
      by rewrite assoc_3_0_1, assoc_3_1_2]
    - [replace (f (f 0 y 2) 3 b) with (f (f 0 y 2) 3 b) by fail]
    - [replace (f (f 0 y 2) a 4) with (f (f 0 y 2) a 4) by fail]
    - [replace (f (f 0 y 2) a b) with (f (f 0 y 2) a b) by fail]
    - [replace (f (f 0 y z) 3 4) with (f (f 0 y z) 3 4) by fail]
    - [replace (f (f 0 y z) 3 b) with (f (f 0 y z) 3 b) by fail]
    - [replace (f (f 0 y z) a 4) with (f (f 0 y z) a 4) by fail]
    - [replace (f (f 0 y z) a b) with (f (f 0 y z) a b) by fail]
    - [replace (f (f x 1 2) 3 4)]
      - [with (f x (f 1 2 3) 4) by rewrite assoc_3_0_1]
      - [with (f x 1 (f 2 3 4)) by rewrite assoc_3_0_1, assoc_3_1_2]
    - [replace (f (f x 1 2) 3 b) with (f x (f 1 2 3) b)
      by rewrite assoc_3_0_1]
    - [replace (f (f x 1 2) a 4) with (f (f x 1 2) a 4) by fail]
    - [replace (f (f x 1 2) a b) with (f (f x 1 2) a b) by fail]
    - [replace (f (f x 1 z) 3 4) with (f (f x 1 z) 3 4) by fail]
    - [replace (f (f x 1 z) 3 b) with (f (f x 1 z) 3 b) by fail]
    - [replace (f (f x 1 z) a 4) with (f (f x 1 z) a 4) by fail]
    - [replace (f (f x 1 z) a b) with (f (f x 1 z) a b) by fail]
    - [replace (f (f x y 2) 3 4) with (f x y (f 2 3 4))
      by rewrite assoc_3_0_1, assoc_3_1_2]
    - [replace (f (f x y 2) 3 b) with (f (f x y 2) 3 b) by fail]
    - [replace (f (f x y 2) a 4) with (f (f x y 2) a 4) by fail]
    - [replace (f (f x y 2) a b) with (f (f x y 2) a b) by fail]
    - [replace (f (f x y z) 3 4) with (f (f x y z) 3 4) by fail]
    - [replace (f (f x y z) 3 b) with (f (f x y z) 3 b) by fail]
    - [replace (f (f x y z) a 4) with (f (f x y z) a 4) by fail]
    - [replace (f (f x y z) a b) with (f (f x y z) a b) by fail]

    - [replace (f 0 (f 1 2 3) 4)] ...

    - [replace (f 0 1 (f 2 3 4))] ... *)

Ltac reassoc_3 p f e10 e21 :=
  match goal with
  | |- context c [f (f ?x0 ?x1 ?x2) ?x3 ?x4] => first [
    assert_fails (idtac; p x0); p x1; p x2; p x3;
    let a := context c [f (f x0 x1 x2) x3 x4] in
    let b := context c [f x0 (f x1 x2 x3) x4] in
    replace a with b by (rewrite <- (e10 x0 x1 x2 x3 x4); reflexivity) |
    assert_fails (idtac; p x1); p x2; p x3; p x4;
    let a := context c [f (f x0 x1 x2) x3 x4] in
    let b := context c [f x0 x1 (f x2 x3 x4)] in
    replace a with b by (rewrite <- (e10 x0 x1 x2 x3 x4),
    <- (e21 x0 x1 x2 x3 x4); reflexivity)]
  | |- context c [f ?x0 (f ?x1 ?x2 ?x3) ?x4] => first [
    assert_fails (idtac; p x3); p x0; p x1; p x2;
    let a := context c [f x0 (f x1 x2 x3) x4] in
    let b := context c [f (f x0 x1 x2) x3 x4] in
    replace a with b by (rewrite (e10 x0 x1 x2 x3 x4); reflexivity) |
    assert_fails (idtac; p x1); p x2; p x3; p x4;
    let a := context c [f x0 (f x1 x2 x3) x4] in
    let b := context c [f x0 x1 (f x2 x3 x4)] in
    replace a with b by (rewrite <- (e21 x0 x1 x2 x3 x4); reflexivity)]
  | |- context c [f ?x0 ?x1 (f ?x2 ?x3 ?x4)] => first [
    assert_fails (idtac; p x4); p x1; p x2; p x3;
    let a := context c [f x0 x1 (f x2 x3 x4)] in
    let b := context c [f x0 (f x1 x2 x3) x4] in
    replace a with b by (rewrite (e21 x0 x1 x2 x3 x4); reflexivity) |
    assert_fails (idtac; p x4); p x0; p x1; p x2;
    let a := context c [f x0 x1 (f x2 x3 x4)] in
    let b := context c [f (f x0 x1 x2) x3 x4] in
    replace a with b by (rewrite (e21 x0 x1 x2 x3 x4),
    (e10 x0 x1 x2 x3 x4); reflexivity)]
  | h : context c [f (f ?x0 ?x1 ?x2) ?x3 ?x4] |- _ => first [
    assert_fails (idtac; p x0); p x1; p x2; p x3;
    let a := context c [f (f x0 x1 x2) x3 x4] in
    let b := context c [f x0 (f x1 x2 x3) x4] in
    replace a with b in h by (rewrite <- (e10 x0 x1 x2 x3 x4); reflexivity) |
    assert_fails (idtac; p x1); p x2; p x3; p x4;
    let a := context c [f (f x0 x1 x2) x3 x4] in
    let b := context c [f x0 x1 (f x2 x3 x4)] in
    replace a with b in h by (rewrite <- (e10 x0 x1 x2 x3 x4),
    <- (e21 x0 x1 x2 x3 x4); reflexivity)]
  | h : context c [f ?x0 (f ?x1 ?x2 ?x3) ?x4] |- _ => first [
    assert_fails (idtac; p x3); p x0; p x1; p x2;
    let a := context c [f x0 (f x1 x2 x3) x4] in
    let b := context c [f (f x0 x1 x2) x3 x4] in
    replace a with b in h by (rewrite (e10 x0 x1 x2 x3 x4); reflexivity) |
    assert_fails (idtac; p x1); p x2; p x3; p x4;
    let a := context c [f x0 (f x1 x2 x3) x4] in
    let b := context c [f x0 x1 (f x2 x3 x4)] in
    replace a with b in h by (rewrite <- (e21 x0 x1 x2 x3 x4); reflexivity)]
  | h : context c [f ?x0 ?x1 (f ?x2 ?x3 ?x4)] |- _ => first [
    assert_fails (idtac; p x4); p x1; p x2; p x3;
    let a := context c [f x0 x1 (f x2 x3 x4)] in
    let b := context c [f x0 (f x1 x2 x3) x4] in
    replace a with b in h by (rewrite (e21 x0 x1 x2 x3 x4); reflexivity) |
    assert_fails (idtac; p x4); p x0; p x1; p x2;
    let a := context c [f x0 x1 (f x2 x3 x4)] in
    let b := context c [f (f x0 x1 x2) x3 x4] in
    replace a with b in h by (rewrite (e21 x0 x1 x2 x3 x4),
    (e10 x0 x1 x2 x3 x4); reflexivity)]
  end.

(** The tactics from [reassoc_4] onwards can be defined analogously. *)

Ltac reassoc_4 p f e :=
  fail "Not implemented".
