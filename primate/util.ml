let bracket ~acquire work ~release =
  let a = acquire () in
  let w = try work a with
    | e -> release a ;
      raise e in
  release a ;
  w
