(** Some unification problems. *)

(* assoc *)
Check forall (e : ?[T] -> ?T -> Prop)
  (f : _ -> _ -> _) (g : _ -> _ -> _)
  (h : _ -> _ -> _) (k : _ -> _ -> _) (x y z : _),
  e (f x (g y z)) (h (k x y) z).

(* l_unl *)
Check forall (e : ?[T] -> ?T -> Prop) (f : _ -> _ -> _) (a x : _),
  e (f a x) x.

(* r_unl *)
Check forall (e : ?[T] -> ?T -> Prop) (f : _ -> _ -> _) (a x : _),
  e (f x a) x.

(* l_inv *)
Check forall (e : ?[T] -> ?T -> Prop)
  (f : _ -> _ -> _) (g : _ -> _) (x : _),
  e (f (g x) x) x.

(* r_inv *)
Check forall (e : ?[T] -> ?T -> Prop)
  (f : _ -> _ -> _) (g : _ -> _) (x : _),
  e (f x (g x)) x.

(* absorb *)
Check forall (e : ?[T] -> ?T -> Prop)
  (f : _ -> _) (a : _),
  e (f a) a.

(* idemp *)
Check forall (e : ?[T] -> ?T -> Prop)
  (f : _ -> _) (g : _ -> _) (h : _ -> _) (x : _),
  e (f (g x)) (h x).

(* invol *)
Check forall (e : ?[T] -> ?T -> Prop)
  (f : _ -> _) (g : _ -> _) (x : _),
  e (f (g x)) x.

(* antidistr *)
Check forall (e : ?[A] -> ?A -> Prop)
  (f : _ -> _ -> _) (g : _ -> _ -> _)
  (h : _ -> _) (k : _ -> _) (m : _ -> _) (x y : _),
  e (h (f x y)) (g (k y) (m x)).

(* l_distr *)
Check forall (e : ?[T] -> ?T -> Prop)
  (f : _ -> _ -> _) (g : _ -> _ -> _)
  (h : _ -> _ -> _) (k : _ -> _ -> _) (m : _ -> _ -> _) (x y z : _),
  e (f x (g y z)) (h (k x y) (m x z)).

(* r_distr *)
Check forall (e : ?[T] -> ?T -> Prop)
  (f : _ -> _ -> _) (g : _ -> _ -> _)
  (h : _ -> _ -> _) (k : _ -> _ -> _) (m : _ -> _ -> _) (x y z : _),
  e (f (g x y) z) (h (k x z) (m y z)).
