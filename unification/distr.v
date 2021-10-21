Check let T0 := ?[T0] in
  fun (X : _ -> _ -> Prop) (f g h : _ -> _) (k m : _ -> _ -> _) =>
  forall x y : _, X (h (k x y)) (m (f x) (g y)).
