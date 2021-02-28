From Maniunfold Require Export
  Init.

Definition is_Some (A : Type) (x : option A) : bool :=
  if x then true else false.

Definition option_bind (A B : Type)
  (f : A -> option B) (x : option A) : option B :=
  match x with
  | Some a => f a
  | None => None
  end.

Lemma option_map_id (A : Type) (x : option A) :
  option_map id x = x.
Proof. destruct x as [a |]; auto. Qed.

Lemma option_map_compose (A B C : Type)
  (g : B -> C) (f : A -> B) (x : option A) :
  option_map (g o f) x = option_map g (option_map f x).
Proof. destruct x as [a |]; auto. Qed.
