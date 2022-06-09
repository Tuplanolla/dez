(** * Irrelevance and Homotopy Levels *)

From Coq Require Import
  Logic.Eqdep Logic.ProofIrrelevance micromega.Lia.
From DEZ.Has Require Export
  Decisions.
From DEZ.Is Require Export
  Contractible Reflexive Symmetric Transitive.

#[local] Open Scope type_scope.

(** ** Contractible-If-Inhabited Type *)
(** ** Mere Proposition *)

Class IsProp (A : Type) : Prop :=
  irrel (x y : A) : x = y.

(** A boxed proposition is a proposition. *)

#[export] Instance prop_is_prop_inhabited (A : Type)
  `{!IsProp A} : IsProp (inhabited A).
Proof. intros [x] [y]. f_equal. apply irrel. Qed.

(** ** Proof Irrelevance *)

Class IsProofIrrel : Prop :=
  proof_irrel (A : Prop) :> IsProp A.

(** ** Discrete Type *)
(** ** Set *)

Fail Fail Class IsSet (A : Type) : Prop :=
  uip (x y : A) (a b : x = y) : a = b.

Arguments UIP _ : clear implicits.
Arguments uip {_ _} _ _ _ _.

Notation IsSet := UIP.
Notation uip := uip.

(** ** Streicher's K *)
(** ** Uniqueness of Identity Proofs *)

Class IsStreicher : Prop :=
  streicher (A : Type) :> IsSet A.

(** ** Homotopy [(n - 2)]-Type *)
(** ** Type of Homotopy Level [n] *)

(** For the sake of convenience, we count up from [0],
    even though homotopy levels conventionally start from [-2]. *)

Equations IsHLevel (n : nat) (A : Type) : Prop by struct n :=
  IsHLevel O A := IsContr A _=_;
  IsHLevel (S n) A := forall x y : A, IsHLevel n (x = y).

Existing Class IsHLevel.

Section Context.

Context (A : Type).

(** Homotopy levels are inductive. *)

#[local] Instance contr_is_h_level_O
  `{!IsContr A _=_} : IsHLevel O A.
Proof. eauto. Qed.

#[local] Instance h_level_O_is_contr
  `{!IsHLevel O A} : IsContr A _=_.
Proof. eauto. Qed.

Lemma contr_iff_h_level_O :
  IsContr A _=_ <-> IsHLevel O A.
Proof. esplit; typeclasses eauto. Qed.

#[local] Instance h_level_S_is_h_level_eq (n : nat)
  `{!IsHLevel (S n) A} (x y : A) : IsHLevel n (x = y).
Proof. eauto. Qed.

#[local] Instance h_level_eq_is_h_level_S (n : nat)
  `{!forall x y : A, IsHLevel n (x = y)} : IsHLevel (S n) A.
Proof. eauto. Qed.

Lemma h_level_S_iff_h_level_eq (n : nat) :
  IsHLevel (S n) A <-> forall x y : A, IsHLevel n (x = y).
Proof. esplit; typeclasses eauto. Qed.

End Context.

Section Context.

Context (A : Type).

(** Homotopy levels are cumulative. *)

#[local] Instance h_level_is_h_level_S (n : nat)
  `{!IsHLevel n A} : IsHLevel (S n) A.
Proof.
  match goal with
  | x : IsHLevel _ _ |- _ => rename x into IHL
  end.
  revert A IHL. induction n as [| p IHL']; intros A IHL.
  - apply @h_level_O_is_contr in IHL. destruct IHL as [x a].
    apply @h_level_eq_is_h_level_S. intros y z. exists (a z o a y ^-1).
    intros b. rewrite b. apply eq_trans_sym_inv_l.
  - intros x y. apply IHL'. apply @h_level_S_is_h_level_eq. apply IHL. Qed.

#[local] Instance h_level_is_h_level_add (n p : nat)
  `{!IsHLevel n A} : IsHLevel (p + n) A.
Proof.
  match goal with
  | x : IsHLevel _ _ |- _ => rename x into IHL
  end.
  revert n IHL. induction p as [| q IHL']; intros n IHL.
  - change (0 + n)%nat with n. apply IHL.
  - change (S q + n)%nat with (S (q + n))%nat.
    apply @h_level_is_h_level_S. apply IHL'. apply IHL. Qed.

#[local] Instance h_level_sub_is_h_level (n p : nat)
  `{!IsHLevel (n - p) A} : IsHLevel n A.
Proof.
  match goal with
  | x : IsHLevel _ _ |- _ => rename x into IHL
  end.
  revert n IHL. induction p as [| q IHL']; intros n IHL.
  - replace (n - 0)%nat with n in IHL by lia. apply IHL.
  - destruct n as [| r].
    + replace (0 - S q)%nat with 0%nat in IHL by lia. apply IHL.
    + replace (S r - S q)%nat with (r - q)%nat in IHL by lia.
      apply @h_level_is_h_level_S. apply IHL'. apply IHL. Qed.

End Context.

Section Context.

Context (A : Type).

(** Homotopy level [0] corresponds to contractibility. *)

#[local] Instance contr_is_h_level_0
  `{!IsContr A _=_} : IsHLevel 0 A.
Proof. apply contr_is_h_level_O. Qed.

#[local] Instance h_level_0_is_contr
  `{!IsHLevel 0 A} : IsContr A _=_.
Proof. apply h_level_O_is_contr. Qed.

Lemma contr_iff_h_level_0 :
  IsContr A _=_ <-> IsHLevel 0 A.
Proof. apply contr_iff_h_level_O. Qed.

End Context.

Section Context.

Context (A : Type).

(** Homotopy level [1] corresponds to contractibility-if-inhabited. *)

#[local] Instance prop_is_h_level_1
  `{!IsProp A} : IsHLevel 1 A.
Proof.
  apply @h_level_eq_is_h_level_S.
  intros x y. apply @contr_is_h_level_0. exists (irrel x y o irrel x x ^-1).
  intros a. rewrite a. apply eq_trans_sym_inv_l. Qed.

#[local] Instance h_level_1_is_prop
  `{!IsHLevel 1 A} : IsProp A.
Proof.
  match goal with
  | x : IsHLevel _ _ |- _ => rename x into IHL
  end.
  intros x y. assert (IC : IsContr (x = y) _=_).
  { apply @h_level_0_is_contr. apply @h_level_S_is_h_level_eq. apply IHL. }
  apply IC. Qed.

Lemma prop_iff_h_level_1 :
  IsProp A <-> IsHLevel 1 A.
Proof. esplit; typeclasses eauto. Qed.

End Context.

Section Context.

Context (A : Type).

(** Homotopy level [2] corresponds to discreteness. *)

#[local] Instance set_is_h_level_2
  `{!IsSet A} : IsHLevel 2 A.
Proof.
  apply @h_level_eq_is_h_level_S.
  intros x y. apply @prop_is_h_level_1.
  intros a b. apply uip. Qed.

#[local] Instance h_level_2_is_set
  `{!IsHLevel 2 A} : IsSet A.
Proof.
  match goal with
  | x : IsHLevel _ _ |- _ => rename x into IHL
  end.
  intros x y. assert (IP : IsProp (x = y)).
  { apply @h_level_1_is_prop. apply @h_level_S_is_h_level_eq. apply IHL. }
  apply IP. Qed.

Lemma set_iff_h_level_2 :
  IsSet A <-> IsHLevel 2 A.
Proof. esplit; typeclasses eauto. Qed.

End Context.

(** These hints introduce and eliminate homotopy levels. *)

Create HintDb h_intro.

#[export] Hint Resolve
  contr_is_h_level_O h_level_eq_is_h_level_S h_level_is_h_level_S
  h_level_is_h_level_add contr_is_h_level_0 prop_is_h_level_1 set_is_h_level_2 :
  h_intro.

Create HintDb h_elim.

#[export] Hint Resolve
  h_level_O_is_contr h_level_S_is_h_level_eq h_level_sub_is_h_level
  h_level_0_is_contr h_level_1_is_prop h_level_2_is_set : h_elim.

Section Context.

Context (A : Type).

#[local] Instance prop_is_contr_eq
  `{!IsProp A} (x y : A) : IsContr (x = y) _=_.
Proof. eauto with h_intro h_elim. Qed.

#[local] Instance contr_eq_is_prop
  `{!forall x y : A, IsContr (x = y) _=_} : IsProp A.
Proof. eauto with h_intro h_elim. Qed.

Lemma prop_iff_contr_eq :
  IsProp A <-> forall x y : A, IsContr (x = y) _=_.
Proof. esplit; typeclasses eauto. Qed.

#[local] Instance set_is_prop_eq
  `{!IsSet A} (x y : A) : IsProp (x = y).
Proof. eauto with h_intro h_elim. Qed.

#[local] Instance prop_eq_is_set
  `{!forall x y : A, IsProp (x = y)} : IsSet A.
Proof. eauto with h_intro h_elim. Qed.

Lemma set_iff_prop_eq :
  IsSet A <-> forall x y : A, IsProp (x = y).
Proof. esplit; typeclasses eauto. Qed.

(** Contractible types are propositions. *)

#[local] Instance contr_is_prop
  `{!IsContr A _=_} : IsProp A.
Proof. eauto with h_intro h_elim. Qed.

(** Propositions are sets. *)

#[local] Instance prop_is_set
  `{!IsProp A} : IsSet A.
Proof. eauto with h_intro h_elim. Qed.

(** Inhabited propositions are contractible. *)

#[local] Instance inhabited_prop_is_contr (x : A)
  `{!IsProp A} : IsContr A _=_.
Proof. exists x. apply irrel. Qed.

(** Reflections of propositions are sets. *)

#[local] Instance bool_is_set : IsSet bool.
Proof. intros x y a b. apply eqdec_uip. apply bool_EqDec. Qed.

End Context.

Module FromAxioms.

#[export] Instance is_proof_irrel : IsProofIrrel.
Proof. intros A B. apply proof_irrelevance. Qed.

#[export] Instance is_streicher : IsStreicher.
Proof. intros A. hnf. apply EqdepTheory.UIP. Qed.

End FromAxioms.
