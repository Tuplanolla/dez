Check let T0 := ?[T0] in
  fun (R : _ -> _ -> Prop) (f g : _ -> _) (k m : _ -> _ -> _) =>
  forall x y : _, R (k x (f y)) (g (m x y)).
