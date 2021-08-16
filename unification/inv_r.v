Check let T0 := ?[T0] in
  fun (R : _ -> _ -> Prop) (x : _) (f : _ -> _) (k : _ -> _ -> _) =>
  forall y : _, R (k y (f y)) x.
