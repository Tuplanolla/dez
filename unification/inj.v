Check let T0 := ?[T0] in
  fun (X : _ -> _ -> Prop) (f g : _ -> _) (k m : _ -> _) =>
  forall x y : _, X (m (f x) (g y)) (k x y).
