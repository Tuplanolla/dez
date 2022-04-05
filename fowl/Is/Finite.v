(** * Finite Types *)

From Coq Require Import
  Lists.List Logic.FinFun NArith.NArith.
From DEZ Require Export
  Init.
From DEZ.Is Require Export
  Isomorphic.

Import ListNotations.

(** ** Unsorted Enumeration of a Type *)

(** This is a generalized version of [Full]. *)

Class IsFull (A : Type) (X : A -> A -> Prop) (a : list A) : Prop :=
  full (x : A) : Exists (X x) a.

(** ** Finiteness in the Kuratowski Sense *)

Class IsFiniteFull (A : Type) (X : A -> A -> Prop) : Prop :=
  finite_full : exists a : list A, IsFull X a.

(** ** Uniqueness of a Listing *)

(** This is a generalized version of [NoDup]. *)

Inductive IsNoDup (A : Type) (X : A -> A -> Prop) : list A -> Prop :=
  | IsNoDup_nil : IsNoDup X []
  | IsNoDup_cons (x : A) (a : list A) (s : ~ Exists (X x) a)
    (t : IsNoDup X a) : IsNoDup X (x :: a).

Existing Class IsNoDup.

(** ** Unsorted Unique Enumeration of a Type *)

Class IsListing (A : Type) (X : A -> A -> Prop) (a : list A) : Prop := {
  listing_is_full :> IsFull X a;
  listing_is_no_dup :> IsNoDup X a;
}.

(** ** Finiteness in the Bishop Sense *)

Class IsFiniteListing (A : Type) (X : A -> A -> Prop) : Prop :=
  finite_list : exists a : list A, IsListing X a.

(** ** Size of a Type *)

Class IsSize (A : Type) (X : A -> A -> Prop) (n : N) : Prop :=
  size_is_iso : IsConv (A := {p : N | p < n}%N) (B := A) _=_ X.

(** ** Finiteness *)

Class IsFiniteSize (A : Type) (X : A -> A -> Prop) : Prop :=
  finite_size : exists n : N, IsSize X n.

#[deprecated (since = "now")] Notation IsKFin := IsFiniteFull.
#[deprecated (since = "now")] Notation IsBFin := IsFiniteListing.
#[deprecated (since = "now")] Notation IsNFin := IsFiniteSize.
