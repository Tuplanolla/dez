Check let T0 := ?[T0] in
  fun (R : _ -> _ -> Prop) (k m : _ -> _ -> _) =>
  forall x y : _, R (k x y) (m y x).
