Check let T0 := ?[T0] in
  fun (R : _ -> _ -> Prop) (k m n p : _ -> _ -> _) =>
  forall x y z : _, R (n x (m y z)) (p (k x y) z).
