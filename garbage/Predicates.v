Section Homomorphism.

Context {A B : Type} (f : A -> B) (x : A).

Goal A. Proof. exact (x). Defined.
Goal B. Proof. exact (f x). Defined.

End Homomorphism.

Section Endomorphism.

Context {A : Type} (f : A -> A) (x : A).

Goal A. Proof. exact (x). Defined.
Goal A. Proof. exact (f x). Defined.
Goal A. Proof. exact (f (f x)). Defined.
(* ... *)

End Endomorphism.

Section Bihomomorphism.

Context {A B C : Type} (f : A -> B -> C) (x : A) (y : B).

Goal A. Proof. exact (x). Defined.
Goal B. Proof. exact (y). Defined.
Goal C. Proof. exact (f x y). Defined.

End Bihomomorphism.

Section Valuation.

Context {A B : Type} (f : A -> A -> B) (x y : A).

Goal A. Proof. exact (x). Defined.
Goal B. Proof. exact (f x x). Defined.
Goal B. Proof. exact (f x y). Defined.
Goal B. Proof. exact (f y x). Defined.

End Valuation.

Section Scaling.

Context {A B : Type} (f : A -> B -> B) (x : A) (y : B).

Goal A. Proof. exact (x). Defined.

Goal B. Proof. exact (f x y). Defined.
Goal B. Proof. exact (f x (f x y)). Defined.
Goal B. Proof. exact (f x (f x (f x y))). Defined.
(* ... *)

End Scaling.

Section Operator.

Context {A : Type} (f : A -> A -> A) (x y z w : A).

Goal A. Proof. exact (x). Defined.
Goal A. Proof. exact (f x x). Defined.
Goal A. Proof. exact (f x (f x x)). Defined.
Goal A. Proof. exact (f (f x x) x). Defined.
Goal A. Proof. exact (f (f x x) (f x x)). Defined.
(* ... *)

Goal A. Proof. exact (f x y). Defined.
Goal A. Proof. exact (f y x). Defined.
Goal A. Proof. exact (f x (f x y)). Defined.
Goal A. Proof. exact (f x (f y x)). Defined.
Goal A. Proof. exact (f x (f y y)). Defined.
Goal A. Proof. exact (f y (f x x)). Defined.
Goal A. Proof. exact (f y (f x y)). Defined.
Goal A. Proof. exact (f y (f y x)). Defined.
Goal A. Proof. exact (f (f x x) y). Defined.
Goal A. Proof. exact (f (f x y) x). Defined.
Goal A. Proof. exact (f (f x y) y). Defined.
Goal A. Proof. exact (f (f y x) x). Defined.
Goal A. Proof. exact (f (f y x) y). Defined.
Goal A. Proof. exact (f (f y y) x). Defined.
Goal A. Proof. exact (f (f x x) (f x y)). Defined.
Goal A. Proof. exact (f (f x x) (f y x)). Defined.
Goal A. Proof. exact (f (f x x) (f y y)). Defined.
Goal A. Proof. exact (f (f x y) (f x x)). Defined.
Goal A. Proof. exact (f (f x y) (f x y)). Defined.
Goal A. Proof. exact (f (f x y) (f y x)). Defined.
Goal A. Proof. exact (f (f x y) (f y y)). Defined.
Goal A. Proof. exact (f (f y x) (f x x)). Defined.
Goal A. Proof. exact (f (f y x) (f x y)). Defined.
Goal A. Proof. exact (f (f y x) (f y x)). Defined.
Goal A. Proof. exact (f (f y x) (f y y)). Defined.
Goal A. Proof. exact (f (f y y) (f x x)). Defined.
Goal A. Proof. exact (f (f y y) (f x y)). Defined.
Goal A. Proof. exact (f (f y y) (f y x)). Defined.
(* ... *)

(** It is apparent that we count up from [0] to [2 ^ 4 - 1] in base [2],
    but omit those numbers that do not feature at least one of each digit.
    The following Haskell program generates the general case.

<<
traverse_ putStrLn $
  let intToVar x = chr (ord 'x' + x) in
  let subs = 4 in
  let vars = 3 in
  [str | perm <- [0 .. vars ^ subs - 1],
    let str = let substr = showIntAtBase vars intToVar perm "" in
    replicate (subs - length substr) (intToVar 0) ++ substr,
    length (nub str) == vars]
>> *)

Goal A. Proof. exact (f x (f y z)). Defined.
Goal A. Proof. exact (f x (f z y)). Defined.
Goal A. Proof. exact (f y (f x z)). Defined.
Goal A. Proof. exact (f y (f z x)). Defined.
Goal A. Proof. exact (f z (f x y)). Defined.
Goal A. Proof. exact (f z (f y x)). Defined.
Goal A. Proof. exact (f (f x y) z). Defined.
Goal A. Proof. exact (f (f x z) y). Defined.
Goal A. Proof. exact (f (f y x) z). Defined.
Goal A. Proof. exact (f (f y z) x). Defined.
Goal A. Proof. exact (f (f z x) y). Defined.
Goal A. Proof. exact (f (f z y) x). Defined.
Goal A. Proof. exact (f (f x x) (f y z)). Defined.
Goal A. Proof. exact (f (f x x) (f z y)). Defined.
Goal A. Proof. exact (f (f x y) (f x z)). Defined.
Goal A. Proof. exact (f (f x y) (f y z)). Defined.
Goal A. Proof. exact (f (f x y) (f z x)). Defined.
Goal A. Proof. exact (f (f x y) (f z y)). Defined.
Goal A. Proof. exact (f (f x y) (f z z)). Defined.
Goal A. Proof. exact (f (f x z) (f x y)). Defined.
Goal A. Proof. exact (f (f x z) (f y x)). Defined.
Goal A. Proof. exact (f (f x z) (f y y)). Defined.
Goal A. Proof. exact (f (f x z) (f y z)). Defined.
Goal A. Proof. exact (f (f x z) (f z y)). Defined.
Goal A. Proof. exact (f (f y x) (f x z)). Defined.
Goal A. Proof. exact (f (f y x) (f y z)). Defined.
Goal A. Proof. exact (f (f y x) (f z x)). Defined.
Goal A. Proof. exact (f (f y x) (f z y)). Defined.
Goal A. Proof. exact (f (f y x) (f z z)). Defined.
Goal A. Proof. exact (f (f y y) (f x z)). Defined.
Goal A. Proof. exact (f (f y y) (f z x)). Defined.
Goal A. Proof. exact (f (f y z) (f x x)). Defined.
Goal A. Proof. exact (f (f y z) (f x y)). Defined.
Goal A. Proof. exact (f (f y z) (f x z)). Defined.
Goal A. Proof. exact (f (f y z) (f y x)). Defined.
Goal A. Proof. exact (f (f y z) (f z x)). Defined.
Goal A. Proof. exact (f (f z x) (f x y)). Defined.
Goal A. Proof. exact (f (f z x) (f y x)). Defined.
Goal A. Proof. exact (f (f z x) (f y y)). Defined.
Goal A. Proof. exact (f (f z x) (f y z)). Defined.
Goal A. Proof. exact (f (f z x) (f z y)). Defined.
Goal A. Proof. exact (f (f z y) (f x x)). Defined.
Goal A. Proof. exact (f (f z y) (f x y)). Defined.
Goal A. Proof. exact (f (f z y) (f x z)). Defined.
Goal A. Proof. exact (f (f z y) (f y x)). Defined.
Goal A. Proof. exact (f (f z y) (f z x)). Defined.
Goal A. Proof. exact (f (f z z) (f x y)). Defined.
Goal A. Proof. exact (f (f z z) (f y x)). Defined.
(* ... *)

End Operator.

(** Now for some mixed things. *)

Section HomomorphismBihomomorphism.

Context {A B C : Type} (f : A -> B) (g : A -> B -> C) (x : A) (y : B).

Goal C. Proof. exact (g x (f x)). Defined.

End HomomorphismBihomomorphism.

Section HomomorphismBihomomorphism.

Context {A B C : Type} (f : A -> C) (g : A -> B -> C) (x : A) (y : B).

End HomomorphismBihomomorphism.

Section HomomorphismBihomomorphism.

Context {A B C : Type} (f : B -> C) (g : A -> B -> C) (x : A) (y : B).

End HomomorphismBihomomorphism.

Section EndomorphismBihomomorphism.

Context {A B C : Type} (f : A -> A) (g : A -> B -> C) (x : A) (y : B).

Goal C. Proof. exact (g (f x) y). Defined.
Goal C. Proof. exact (g (f (f x)) y). Defined.
Goal C. Proof. exact (g (f (f (f x))) y). Defined.
(* ... *)

End EndomorphismBihomomorphism.

Section EndomorphismBihomomorphism.

Context {A B C : Type} (f : B -> B) (g : A -> B -> C) (x : A) (y : B).

Goal C. Proof. exact (g x (f y)). Defined.
Goal C. Proof. exact (g x (f (f y))). Defined.
Goal C. Proof. exact (g x (f (f (f y)))). Defined.
(* ... *)

End EndomorphismBihomomorphism.

Section EndomorphismBihomomorphism.

Context {A B C : Type} (f : C -> C) (g : A -> B -> C) (x : A) (y : B).

Goal C. Proof. exact (f (g x y)). Defined.
Goal C. Proof. exact (f (f (g x y))). Defined.
Goal C. Proof. exact (f (f (f (g x y)))). Defined.
(* ... *)

End EndomorphismBihomomorphism.

Section HomomorphismValuation.

Context {A B : Type} (f : A -> B) (g : A -> A -> B) (x : A).

End HomomorphismValuation.

Section EndomorphismValuation.

Context {A B : Type} (f : A -> A) (g : A -> A -> B) (x : A).

Goal B. Proof. exact (g x (f x)). Defined.
Goal B. Proof. exact (g x (f (f x))). Defined.
Goal B. Proof. exact (g (f x) x). Defined.
Goal B. Proof. exact (g (f x) (f x)). Defined.
Goal B. Proof. exact (g (f x) (f (f x))). Defined.
Goal B. Proof. exact (g (f (f x)) (f x)). Defined.
Goal B. Proof. exact (g (f (f x)) (f (f x))). Defined.
(* ... *)

End EndomorphismValuation.

Section EndomorphismValuation.

Context {A B : Type} (f : B -> B) (g : A -> A -> B) (x y : A).

Goal B. Proof. exact (f (g x x)). Defined.
Goal B. Proof. exact (f (g x y)). Defined.
Goal B. Proof. exact (f (g y x)). Defined.
Goal B. Proof. exact (f (g y y)). Defined.
Goal B. Proof. exact (f (f (g x x))). Defined.
Goal B. Proof. exact (f (f (g x y))). Defined.
Goal B. Proof. exact (f (f (g y x))). Defined.
Goal B. Proof. exact (f (f (g y y))). Defined.
(* ... *)

End EndomorphismValuation.

(* HomomorphismScaling, EndomorphismScaling,
    HomomorphismOperator, EndomorphismOperator, ... *)
