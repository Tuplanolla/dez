(* bad *)
From Maniunfold.Has Require Export
  TwoSorted.Isomorphism.

Section Context.

Context {A B : Type} {A_B_has_iso : HasIso A B}.

Definition sect : A -> B := fst iso.

Definition retr : B -> A := snd iso.

End Context.
