Check let T0 := ?[T0] in
  fun (X : _ -> _ -> Prop) (f g : _ -> _) (k m : _ -> _ -> _) =>
  forall x y : _, X (m (f x) y) (g (k x y)).
