open Big_int
open BinNums
open ZTheorems

let big_int_of_pos x =
  let rec f x =
    match x with
    | Coq_xI y -> add_int_big_int 1 (mult_int_big_int 2 (f y))
    | Coq_xO y -> mult_int_big_int 2 (f y)
    | Coq_xH -> unit_big_int in
  f x

let big_int_of_z x =
  match x with
  | Z0 -> zero_big_int
  | Zpos y -> big_int_of_pos y
  | Zneg y -> minus_big_int (big_int_of_pos y)

let pos_of_big_int x =
  if lt_big_int x unit_big_int then
    raise (Invalid_argument "nonpositive integer") else
    let rec f x =
      let (q, m) = quomod_big_int x (big_int_of_int 2) in
      if eq_big_int q zero_big_int then
        Coq_xH else
        if eq_big_int m zero_big_int then
          Coq_xO (f q) else
          Coq_xI (f q) in
    f x

let z_of_big_int x =
  let s = sign_big_int x in
  if s = 0 then
    (* Z0 *) coq_Z_has_zero else
    if s > 0 then
      Zpos (pos_of_big_int x) else
      Zneg (pos_of_big_int (minus_big_int x))

let z_of_int x = z_of_big_int (big_int_of_int x)

let string_of_z x = string_of_big_int (big_int_of_z x)
