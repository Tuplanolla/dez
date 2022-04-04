(** * Indiscernibility *)

From DEZ Require Export
  Init.

(** ** Indiscernibility of Identicals for a Form *)

Class IsIndiscIdForm (A B : Type) (X : A -> A -> Prop) (Y : B -> B -> Prop)
  (x : A) (s : B -> B -> A) : Prop :=
  indisc_id_form (a b : B) (t : Y a b) : X (s a b) x.

(** ** Identity of Indiscernibles for a Form *)

Class IsIdIndiscForm (A B : Type) (X : A -> A -> Prop) (Y : B -> B -> Prop)
  (x : A) (s : B -> B -> A) : Prop :=
  id_indisc_form (a b : B) (t : X (s a b) x) : Y a b.
