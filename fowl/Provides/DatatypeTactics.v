(** * Tactics for Data Types *)

From Coq Require Import
  PArith.PArith NArith.NArith ZArith.ZArith QArith.QArith QArith.Qcanon.
From DEZ Require Export
  Init.

(** ** Constant Checking *)

(** Succeed when the given term is a constant of type [A -> B] and
    its subterms are constants of type [B]
    as determined by the tactical predicate [is_B]. *)

Ltac is_fun is_B f :=
  match f with
  | fun _ : _ => ?x => is_B x
  | _ => fail "Not a constant"
  end.

(** Succeed when the given term is a constant of type [A -> B]. *)

Ltac is_fun' f :=
  match f with
  | fun _ : _ => _ => idtac
  | _ => fail "Not a constant"
  end.

(** Succeed when the given term is a constant of type [forall x : A, P x] and
    its subterms are constants of type [P x]
    as determined by the tactical predicate [is_P]. *)

Ltac is_pi is_P f :=
  match f with
  | fun _ : _ => ?x => is_P x
  | _ => fail "Not a constant"
  end.

(** Succeed when the given term is a constant of type [forall x : A, P x]. *)

Ltac is_pi' f :=
  match f with
  | fun _ : _ => _ => idtac
  | _ => fail "Not a constant"
  end.

(** Succeed when the given term is a constant of type [Empty_set]. *)

Ltac is_Empty_set e :=
  match e with
  | _ => fail "Not a constant"
  end.

(** Succeed when the given term is a constant of type [unit]. *)

Ltac is_unit t :=
  match t with
  | tt => idtac
  | _ => fail "Not a constant"
  end.

(** Succeed when the given term is a constant of type [bool]. *)

Ltac is_bool b :=
  match b with
  | true => idtac
  | false => idtac
  | _ => fail "Not a constant"
  end.

(** Succeed when the given term is a constant of type [nat]. *)

Ltac is_nat n :=
  match n with
  | O => idtac
  | S ?p => is_nat p
  | _ => fail "Not a constant"
  end.

(** Succeed when the given term is a constant of type [option A] and
    its subterms are constants of type [A]
    as determined by the tactical predicate [is_A]. *)

Ltac is_option is_A x :=
  match x with
  | Some ?a => is_A a
  | None => idtac
  | _ => fail "Not a constant"
  end.

(** Succeed when the given term is a constant of type [option A]. *)

Ltac is_option' x :=
  match x with
  | Some _ => idtac
  | None => idtac
  | _ => fail "Not a constant"
  end.

(** Succeed when the given term is a constant of type [A + B] and
    its subterms are constants of type [A] and [B]
    as determined by the tactical predicates [is_A] and [is_B]. *)

Ltac is_sum is_A is_B x :=
  match x with
  | inl ?a => is_A a
  | inr ?b => is_B b
  | _ => fail "Not a constant"
  end.

(** Succeed when the given term is a constant of type [A + B]. *)

Ltac is_sum' x :=
  match x with
  | inl _ => idtac
  | inr _ => idtac
  | _ => fail "Not a constant"
  end.

(** Succeed when the given term is a constant of type [A * B] and
    its subterms are constants of type [A] and [B]
    as determined by the tactical predicates [is_A] and [is_B]. *)

Ltac is_prod is_A is_B x :=
  match x with
  | pair ?a ?b => is_A a; is_B b
  | _ => fail "Not a constant"
  end.

(** Succeed when the given term is a constant of type [A * B]. *)

Ltac is_prod' x :=
  match x with
  | pair _ _ => idtac
  | _ => fail "Not a constant"
  end.

(** Succeed when the given term is a constant of type [list A] and
    its subterms are constants of type [A]
    as determined by the tactical predicate [is_A]. *)

Ltac is_list is_A x :=
  match x with
  | nil => idtac
  | cons ?a ?y => is_A a; is_list is_A y
  | _ => fail "Not a constant"
  end.

(** Succeed when the given term is a constant of type [list A]. *)

Ltac is_list' x :=
  match x with
  | nil => idtac
  | cons _ ?y => is_list' y
  | _ => fail "Not a constant"
  end.

(** Succeed when the given term is a constant of type [exists x : A, P x] and
    its subterms are constants of type [x : A] and [P x]
    as determined by the tactical predicates [is_A] and [is_P]. *)

Ltac is_ex is_A is_P x :=
  match x with
  | ex_intro _ ?a ?b => is_A a; is_P a b
  | _ => fail "Not a constant"
  end.

(** Succeed when the given term is a constant of type [exists x : A, P x]. *)

Ltac is_ex' x :=
  match x with
  | ex_intro _ _ _ => idtac
  | _ => fail "Not a constant"
  end.

(** Succeed when the given term is a constant of type [{x : A | P x}] and
    its subterms are constants of type [x : A] and [P x]
    as determined by the tactical predicates [is_A] and [is_P]. *)

Ltac is_sig is_A is_P x :=
  match x with
  | exist _ ?a ?b => is_A a; is_P a b
  | _ => fail "Not a constant"
  end.

(** Succeed when the given term is a constant of type [{x : A | P x}]. *)

Ltac is_sig' x :=
  match x with
  | exist _ _ _ => idtac
  | _ => fail "Not a constant"
  end.

(** Succeed when the given term is a constant of type [{x : A & P x}] and
    its subterms are constants of type [x : A] and [P x]
    as determined by the tactical predicates [is_A] and [is_P]. *)

Ltac is_sigT is_A is_P x :=
  match x with
  | existT _ ?a ?b => is_A a; is_P a b
  | _ => fail "Not a constant"
  end.

(** Succeed when the given term is a constant of type [{x : A & P x}]. *)

Ltac is_sigT' x :=
  match x with
  | existT _ _ _ => idtac
  | _ => fail "Not a constant"
  end.

(** Succeed when the given term is a constant of type [{x : A $ P x}] and
    its subterms are constants of type [x : A] and [P x]
    as determined by the tactical predicates [is_A] and [is_P]. *)

Ltac is_Ssig is_A is_P x :=
  match x with
  | Sexists _ ?a ?b => is_A a; is_P a b
  | _ => fail "Not a constant"
  end.

(** Succeed when the given term is a constant of type [{x : A $ P x}]. *)

Ltac is_Ssig' x :=
  match x with
  | Sexists _ _ _ => idtac
  | _ => fail "Not a constant"
  end.

(** Succeed when the given term is a constant of type [{A} + {B}] and
    its subterms are constants of type [A] and [B]
    as determined by the tactical predicates [is_A] and [is_B]. *)

Ltac is_sumbool is_A is_B x :=
  match x with
  | left ?a => is_A a
  | right ?b => is_B b
  | _ => fail "Not a constant"
  end.

(** Succeed when the given term is a constant of type [{A} + {B}]. *)

Ltac is_sumbool' x :=
  match x with
  | left _ => idtac
  | right _ => idtac
  | _ => fail "Not a constant"
  end.

(** Succeed when the given term is a constant of type [A + {B}] and
    its subterms are constants of type [A] and [B]
    as determined by the tactical predicates [is_A] and [is_B]. *)

Ltac is_sumor is_A is_B x :=
  match x with
  | inleft ?a => is_A a
  | inright ?b => is_B b
  | _ => fail "Not a constant"
  end.

(** Succeed when the given term is a constant of type [A + {B}]. *)

Ltac is_sumor' x :=
  match x with
  | inleft _ => idtac
  | inright _ => idtac
  | _ => fail "Not a constant"
  end.

(** Succeed when the given term is a constant of type [positive]. *)

Ltac is_positive n :=
  match n with
  | xI ?p => is_positive p
  | xO ?p => is_positive p
  | xH => idtac
  | _ => fail "Not a constant"
  end.

(** Succeed when the given term is a constant of type [N]. *)

Ltac is_N n :=
  match n with
  | N0 => idtac
  | Npos ?p => is_positive p
  | _ => fail "Not a constant"
  end.

(** Succeed when the given term is a constant of type [Z]. *)

Ltac is_Z n :=
  match n with
  | Z0 => idtac
  | Zpos ?p => is_positive p
  | Zneg ?p => is_positive p
  | _ => fail "Not a constant"
  end.

(** Succeed when the given term is a constant of type [Q]. *)

Ltac is_Q x :=
  match x with
  | Qmake ?n ?p => is_Z n; is_positive ?p
  | _ => fail "Not a constant"
  end.

(** Succeed when the given term is a constant of type [Qc]. *)

Ltac is_Qc x :=
  match x with
  | Qcmake ?a _ => is_Q a
  | _ => fail "Not a constant"
  end.
