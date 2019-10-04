Definition map_pair {A B C D : Type} (f : A -> C) (g : B -> D) :=
  map (fun p : A * B => (f (fst p), g (snd p))).

Lemma map_combine : forall {A B C D : Type}
  (f : A -> C) (g : B -> D) (xs : list A) (ys : list B),
  combine (map f xs) (map g ys) = map_pair f g (combine xs ys).
Proof.
  intros A B C D f g xs. induction xs as [| x xs p]; intros ys.
  - reflexivity.
  - induction ys as [| y ys q].
    + reflexivity.
    + cbn. f_equal. apply p. Qed.
