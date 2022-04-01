(** * Contractivity *)

(** The dual notion of contractivity or a short map
    is an expansivity or a long map,
    which is why we do not define it separately. *)

From DEZ Require Export
  Init.

(** ** Contractive Unary Function *)
(** ** Short Map *)

Class IsContract (A B C : Type) (X : A -> A -> Prop)
  (s : B -> B -> A) (t : C -> C -> A) (f : B -> C) : Prop :=
  contract (a b : B) : X (t (f a) (f b)) (s a b).
