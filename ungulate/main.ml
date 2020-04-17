let () =
  print_endline "main -> extraction";
  print_endline (Adapter.string_of_z (Obj.magic
    Extraction.monkey_saddle (Adapter.z_of_int 42) (Adapter.z_of_int 13)));
