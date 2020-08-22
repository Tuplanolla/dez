open Util

module Log = (val Logs.src_log (Logs.Src.create "maniunfold.primate"))

(** Tag carrying location information. *)
let loc_tag : (string * int) Logs.Tag.def =
  Logs.Tag.def "loc" begin fun fmt (s, i) ->
    Format.fprintf fmt "%a %a"
    Format.pp_print_string s Format.pp_print_int i
  end

(** Location information. *)
let loc file line =
  Logs.Tag.add loc_tag (file, line) Logs.Tag.empty

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
    msgf begin fun ?header ?tags fmt ->
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

(** Some things that go together. *)
module Custom =
  struct
    type signal_behavior =
      | Signal_default
      | Signal_ignore
      | Signal_raise
      | Signal_skip

    let set_signal =
      Array.iter
        begin fun (i, b) ->
          try
            begin match b with
              | Signal_default -> Sys.set_signal i Sys.Signal_default
              | Signal_ignore -> Sys.set_signal i Sys.Signal_ignore
              | Signal_raise -> Sys.set_signal i (Sys.Signal_handle raise_signal)
              | Signal_skip -> ()
            end;
            Log.info (fun m -> m "Set to ignore SIG%s (%d)."
              (string_of_signal i) i)
          with
          | _ ->
            Log.warn (fun m ->
              m "Failed to set the behavior of SIG%s (%d)."
              (string_of_signal i) i)
        end
  end

(** Set up logging and signal handling and start the message broker. *)
let main () =
  bracket
    ~acquire:begin fun () ->
      open_out "/tmp/primate.log"
    end
    ~release:close_out
    begin fun oc ->
      Logs.set_reporter (reporter (Format.formatter_of_out_channel oc));
      Logs.set_level (Some Logs.Debug);
      Log.debug (fun m -> m "Set up logging.");
      Custom.set_signal [|
        (Sys.sigabrt, Custom.Signal_raise);
        (Sys.sigalrm, Custom.Signal_raise);
        (Sys.sigfpe, Custom.Signal_raise);
        (Sys.sighup, Custom.Signal_raise);
        (Sys.sigill, Custom.Signal_raise);
        (Sys.sigint, Custom.Signal_raise);
        (** We cannot catch this signal. *)
        (Sys.sigkill, Custom.Signal_skip);
        (Sys.sigpipe, Custom.Signal_raise);
        (Sys.sigquit, Custom.Signal_raise);
        (Sys.sigsegv, Custom.Signal_raise);
        (Sys.sigterm, Custom.Signal_raise);
        (Sys.sigusr1, Custom.Signal_raise);
        (Sys.sigusr2, Custom.Signal_raise);
        (** We keep the default behavior of this signal
            in order to be able to wait for subprocesses. *)
        (Sys.sigchld, Custom.Signal_default);
        (** We keep the default behavior of this signal,
            even though we may find a different use for it at some point. *)
        (Sys.sigcont, Custom.Signal_default);
        (** We cannot catch this signal. *)
        (Sys.sigstop, Custom.Signal_skip);
        (** We keep the default behavior of these signals,
            even though we may find a different use for them at some point. *)
        (Sys.sigtstp, Custom.Signal_default);
        (Sys.sigttin, Custom.Signal_default);
        (Sys.sigttou, Custom.Signal_default);
        (Sys.sigvtalrm, Custom.Signal_raise);
        (Sys.sigprof, Custom.Signal_raise);
        (Sys.sigbus, Custom.Signal_raise);
        (Sys.sigpoll, Custom.Signal_raise);
        (Sys.sigsys, Custom.Signal_raise);
        (Sys.sigtrap, Custom.Signal_raise);
        (** We ignore this signal,
            because we do not care about urgent data. *)
        (Sys.sigurg, Custom.Signal_ignore);
        (Sys.sigxcpu, Custom.Signal_raise);
        (Sys.sigxfsz, Custom.Signal_raise)|];
      Broker.start ()
    end

let () =
  main ()
