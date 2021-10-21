Check let T0 := ?[T0] in
  fun (X : _ -> _ -> Prop) (x : _) (k : _ -> _ -> _) =>
  forall y : _, X (k y x) x.
