Check let T0 := ?[T0] in
  fun (X : _ -> _ -> Prop) (k m : _ -> _ -> _) =>
  forall x y : _, X (k x y) (m y x).
