let bracket ~acquire work ~release =
  let a = acquire () in
  let w = try work a with
    | e -> release a;
      raise e in
  release a;
  w

let string_is_prefix s t =
  let n = String.length s in
  if n <= String.length t then String.equal s (String.sub t 0 n) else false
