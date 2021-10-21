Check let T0 := ?[T0] in
  fun (X : _ -> _ -> Prop) (x : _) (f : _ -> _) (k : _ -> _ -> _) =>
  forall y : _, X (k (f y) y) x.
