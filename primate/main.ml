(** Tag carrying location information. *)
let loc_tag : (string * int) Logs.Tag.def =
  Logs.Tag.def "loc" begin fun fmt (s, i) ->
    Format.fprintf fmt "%a %a"
    Format.pp_print_string s Format.pp_print_int i
  end

(** Attach location information. *)
let loc file line =
  Logs.Tag.add loc_tag (file, line) Logs.Tag.empty

(** TODO Upgrade to OCaml 4.08. *)
module Option =
  struct
    let bind xs m =
      match xs with
      | None -> None
      | Some x -> m x
  end

(** Report a log message with location information.

    Log messages follow a format, where
    - [[%0.03f]] mimicks [dmesg],
    - [==%d==] mimicks [valgrind],
    - ["%s"] mimicks [httpd],
    - [<%s>] mimicks [objdump] and
    - [%s:%d: %a: %a] mimicks [cc]. *)
let reporter ppf =
  let report src level ~over f msgf =
    let k _ =
      over ();
      f () in
    msgf
      begin fun ?header ?tags fmt ->
        match Option.bind tags (Logs.Tag.find loc_tag) with
        | None -> Format.kfprintf k ppf
            ("[%0.3f] ==%d== \"%s\" %a: " ^^ fmt ^^ "@.")
            (Unix.gettimeofday ()) (Unix.getpid ()) (Logs.Src.name src)
            Logs.pp_level level
        | Some (file, line) -> Format.kfprintf k ppf
            ("[%0.3f] ==%d== \"%s\" %s:%d: %a: " ^^ fmt ^^ "@.")
            (Unix.gettimeofday ()) (Unix.getpid ()) (Logs.Src.name src)
            file line Logs.pp_level level
      end in
  {Logs.report = report}

module Log = (val Logs.src_log (Logs.Src.create "maniunfold.primate"))

(** Configure logging. *)
let config_logging ppf =
  Logs.set_reporter (reporter ppf);
  Logs.set_level (Some Logs.Debug);
  Log.debug (fun m -> m "Set the log level to %s."
    (Logs.level_to_string (Logs.level ())))

(** Configure signal handling. *)
let config_signals () =
  Array.iter
    begin fun (i, b) ->
      try
        Def_sys.set_signal i b;
        Log.debug (fun m -> m "Set the behavior of SIG%s (%d)."
          (Def_sys.string_of_signal i) i) with
      | _ ->
          Log.warn (fun m -> m "Failed to set the behavior of SIG%s (%d)."
            (Def_sys.string_of_signal i) i)
    end
    [|(Sys.sigabrt, Def_sys.Signal_raise);
      (Sys.sigalrm, Def_sys.Signal_raise);
      (Sys.sigfpe, Def_sys.Signal_raise);
      (Sys.sighup, Def_sys.Signal_raise);
      (Sys.sigill, Def_sys.Signal_raise);
      (Sys.sigint, Def_sys.Signal_raise);
      (** We cannot catch this signal. *)
      (Sys.sigkill, Def_sys.Signal_skip);
      (Sys.sigpipe, Def_sys.Signal_raise);
      (Sys.sigquit, Def_sys.Signal_raise);
      (Sys.sigsegv, Def_sys.Signal_raise);
      (Sys.sigterm, Def_sys.Signal_raise);
      (Sys.sigusr1, Def_sys.Signal_raise);
      (Sys.sigusr2, Def_sys.Signal_raise);
      (** We ignore this signal,
          so that we do not have to wait for subprocesses. *)
      (Sys.sigchld, Def_sys.Signal_ignore);
      (Sys.sigcont, Def_sys.Signal_default);
      (** We cannot catch this signal. *)
      (Sys.sigstop, Def_sys.Signal_skip);
      (** We keep the default behavior of these signals,
          even though we may need to account for them at some point. *)
      (Sys.sigtstp, Def_sys.Signal_default);
      (Sys.sigttin, Def_sys.Signal_default);
      (Sys.sigttou, Def_sys.Signal_default);
      (Sys.sigvtalrm, Def_sys.Signal_raise);
      (Sys.sigprof, Def_sys.Signal_raise);
      (Sys.sigbus, Def_sys.Signal_raise);
      (Sys.sigpoll, Def_sys.Signal_raise);
      (Sys.sigsys, Def_sys.Signal_raise);
      (Sys.sigtrap, Def_sys.Signal_raise);
      (** We ignore this signal,
          because we do not have any urgent data. *)
      (Sys.sigurg, Def_sys.Signal_ignore);
      (Sys.sigxcpu, Def_sys.Signal_raise);
      (Sys.sigxfsz, Def_sys.Signal_raise)|]

(** Configure and start the message broker. *)
let main () =
  Util.bracket
    ~acquire:begin fun () ->
      open_out "/tmp/primate.log"
    end
    ~release:close_out
    begin fun oc ->
      config_logging (Format.formatter_of_out_channel oc);
      config_signals ();
      Broker.start ()
    end

let () =
  main ()
