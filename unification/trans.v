Check let T0 := ?[T0] in
  fun (X : _ -> _ -> Prop) (k m n p : _ -> _ -> _) =>
  forall x y z : _, X (n (k x y) (m y z)) (p x z).
