From Coq Require Import
  Bool.Sumbool Classes.DecidableClass Classes.SetoidDec.
From DEZ Require Export
  Init.

Definition is_Some (A : Type) (x : option A) : bool :=
  if x then true else false.

Definition option_bind (A B : Type)
  (f : A -> option B) (x : option A) : option B :=
  match x with
  | Some a => f a
  | None => None
  end.

Arguments option_bind _ _ _ !_.

Definition option_extract (A : Type) (a : A) (x : option A) : A :=
  match x with
  | Some b => b
  | None => a
  end.

Arguments option_extract _ _ !_.

Definition fst_option (A B : Type) (x : option A * B) : option (A * B) :=
  match x with
  | (y, b) =>
    match y with
    | Some a => Some (a, b)
    | None => None
    end
  end.

Arguments fst_option _ _ !_ : simpl nomatch.

Definition snd_option (A B : Type) (x : A * option B) : option (A * B) :=
  match x with
  | (a, y) =>
    match y with
    | Some b => Some (a, b)
    | None => None
    end
  end.

Arguments snd_option _ _ !_ : simpl nomatch.

Definition pair_option (A B : Type)
  (x : option A * option B) : option (A * B) :=
  match x with
  | (y, z) =>
    match y, z with
    | Some a, Some b => Some (a, b)
    | _, _ => None
    end
  end.

Arguments pair_option _ _ !_ : simpl nomatch.

Lemma option_map_id (A : Type) (x : option A) :
  option_map id x = x.
Proof. destruct x as [a |]; auto. Qed.

Lemma option_map_compose (A B C : Type)
  (g : B -> C) (f : A -> B) (x : option A) :
  option_map (g o f) x = option_map g (option_map f x).
Proof. destruct x as [a |]; auto. Qed.

Global Program Instance Decidable_option (A : Type)
  `(forall a b : A, Decidable (a = b)) (x y : option A) :
  Decidable (x = y) := {
  Decidable_witness := match x, y with
  | Some a, Some b => decide (a = b)
  | None, Some _ => false
  | Some _, None => false
  | None, None => true
  end;
  Decidable_spec := _;
}.
Next Obligation.
  intros A ? x y. destruct x, y; split; cbn; auto; try congruence.
  intros. f_equal. decide (a = a0); auto. inversion H0.
  intros. decide (a = a0); auto. inversion H0. intuition. Qed.
