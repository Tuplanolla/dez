Check let T0 := ?[T0] in
  fun (R : _ -> _ -> Prop) (f g h : _ -> _) (k m : _ -> _ -> _) =>
  forall x y : _, R (h (k x y)) (m (f x) (g y)).
