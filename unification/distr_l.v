Check let T0 := ?[T0] in
  fun (X : _ -> _ -> Prop) (k m n p q : _ -> _ -> _) =>
  forall x y z : _, X (p x (k y z)) (q (m x y) (n x z)).
