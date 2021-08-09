module Log = (val Logs.src_log (Logs.Src.create "dez.camel"))

let crunch coeffs point =
  Log.info (fun m -> m "Crunched real hard!");
  Hashtbl.fold
  (fun i a y -> y +. a *. point ** Int32.to_float i)
  coeffs
  (Big_int.float_of_big_int (Adapter.big_int_of_z ZTheorems.coq_Z_has_zero))
