From Maniunfold Require Export
  Init.

Definition prod_bimap (A B C D : Type)
  (f : A -> C) (g : B -> D) (x : A * B) : C * D :=
  match x with
  | (a, b) => (f a, g b)
  end.

Definition prod_lmap (A B C : Type)
  (f : A -> C) (x : A * B) : C * B :=
  match x with
  | (a, b) => (f a, b)
  end.

Definition prod_rmap (A B C : Type)
  (g : B -> C) (x : A * B) : A * C :=
  match x with
  | (a, b) => (a, g b)
  end.

Definition prod_map (A B : Type) (f : A -> B) (x : A * A) : B * B :=
  match x with
  | (a, b) => (f a, f b)
  end.

Definition prod_swap (A B : Type) (x : A * B) : B * A :=
  match x with
  | (a, b) => (b, a)
  end.

Definition prod_sort_by (A : Type) (f : A -> A -> bool) (x : A * A) : A * A :=
  match x with
  | (a, b) => if f a b then (a, b) else (b, a)
  end.

(** The specializations are related as follows. *)

Fact eq_prod_bimap_prod_lmap (A B C : Type) (f : A -> C) (x : A * B) :
  prod_bimap f id x = prod_lmap f x.
Proof. reflexivity. Qed.

Fact eq_prod_bimap_prod_rmap (A B C : Type) (f : B -> C) (x : A * B) :
  prod_bimap id f x = prod_rmap f x.
Proof. reflexivity. Qed.

Fact eq_prod_bimap_prod_map (A B : Type) (f g : A -> B) (x : A * A) :
  prod_bimap f f x = prod_map f x.
Proof. reflexivity. Qed.

(** Some other properties also hold. *)

Lemma prod_map_id (A : Type) (x : A * A) :
  prod_map id x = x.
Proof. destruct x as [a b]; auto. Qed.

Lemma prod_map_compose (A B C : Type) (g : B -> C) (f : A -> B) (x : A * A) :
  prod_map (g o f) x = prod_map g (prod_map f x).
Proof. destruct x as [a b]; auto. Qed.

Lemma prod_lmap_id (A B : Type) (x : A * B) :
  prod_lmap id x = x.
Proof. destruct x as [a b]; auto. Qed.

Lemma prod_lmap_compose (A B C D : Type)
  (g : C -> D) (f : A -> C) (x : A * B) :
  prod_lmap (g o f) x = prod_lmap g (prod_lmap f x).
Proof. destruct x as [a b]; auto. Qed.

Lemma prod_rmap_id (A B : Type) (x : A * B) :
  prod_rmap id x = x.
Proof. destruct x as [a b]; auto. Qed.

Lemma prod_rmap_compose (A B C D : Type)
  (g : C -> D) (f : B -> C) (x : A * B) :
  prod_rmap (g o f) x = prod_rmap g (prod_rmap f x).
Proof. destruct x as [a b]; auto. Qed.

Lemma prod_swap_involutive (A B : Type) (x : A * B) :
  prod_swap (prod_swap x) = x.
Proof. destruct x as [a b]; auto. Qed.
