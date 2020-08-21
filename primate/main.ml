open Broker
open Util

module Log = (val Logs.src_log (Logs.Src.create "maniunfold.primate"))

(** Log messages follow a format, where
    - `[%f]` mimicks `dmesg`,
    - `==%d==` mimicks `valgrind`,
    - `"%s"` mimicks `httpd`,
    - `<%s>` mimicks `objdump` and
    - `%s:%d: %a: %a` mimicks `cc`. *)

let loc_tag : (string * int) Logs.Tag.def =
  Logs.Tag.def "loc" (fun fmt (s, i) ->
    Format.fprintf fmt "%a %a" Format.pp_print_string s Format.pp_print_int i)

let loc file line =
  Logs.Tag.add loc_tag (file, line) Logs.Tag.empty

let reporter ppf =
  let report src level ~over k msgf =
    let with_stamp _h tags k ppf fmt =
      let file, line =
        match
          match tags with
          | None -> None
          | Some ts -> Logs.Tag.find loc_tag ts with
        | None -> ("//toplevel//", 1)
        | Some x -> x in
      Format.kfprintf k ppf
        ("[%0.3f] ==%d== \"%s\" %s:%d: %a: " ^^ fmt ^^ "@.")
        (Unix.gettimeofday ()) (Unix.getpid ()) (Logs.Src.name src)
        file line Logs.pp_level level in
    let k_ _ = over () ; k () in
    msgf (fun ?header ?tags fmt -> with_stamp header tags k_ ppf fmt) in
  {Logs.report = report}

let catch_signals =
  Array.iter
    begin fun i ->
      let open Sys in
      try
        set_signal i (Signal_handle raise_signal) ;
        Log.info (fun m ->
          m "Set the behavior of SIG%s (%d) to raise an exception."
          (string_of_signal i) i)
      with
      | _ ->
        Log.warn (fun m ->
          m "Failed to set the behavior of SIG%s (%d)."
          (string_of_signal i) i)
    end

let ignore_signals =
  Array.iter
    begin fun i ->
      let open Sys in
      try
        set_signal i Signal_ignore ;
        Log.info (fun m ->
          m "Set the behavior of SIG%s (%d) to be ignored."
          (string_of_signal i) i)
      with
      | _ ->
        Log.warn (fun m ->
          m "Failed to set the behavior of SIG%s (%d)."
          (string_of_signal i) i)
    end

let main () =
  bracket
    ~acquire:begin fun () ->
      open_out "/tmp/primate.log"
    end
    ~release:close_out
    begin fun oc ->
      let fmt = Format.formatter_of_out_channel oc in
      Logs.set_reporter (Logs.format_reporter ~app:fmt ~dst:fmt ()) ;
      Logs.set_reporter (reporter fmt) ;
      Logs.set_level (Some Logs.Debug) ;
      Log.debug (fun m -> m "Timed!") ;
      Log.debug (fun m -> m "Timed!" ~tags:(loc __FILE__ __LINE__)) ;

      let open Sys in
      catch_signals [|
        sigabrt; sigalrm; sigfpe; sighup; sigill; sigint;
        (** We cannot catch this signal. *)
        (* sigkill; *)
        sigpipe; sigquit; sigsegv; sigterm; sigusr1; sigusr2;
        (** We cannot catch this signal. *)
        (* sigstop; *)
        sigvtalrm; sigprof; sigbus; sigpoll; sigsys; sigtrap;
        sigxcpu; sigxfsz|] ;
      ignore_signals [|
        (** We do not ignore this signal,
            because we want to be able to wait for subprocesses. *)
        (* sigchld; *)
        (** We do not ignore these signals,
            because we may find a use for them at some point. *)
        (* sigcont; sigtstp; sigttin; sigttou; *)
        (** We ignore this signal,
            because we do not care about urgent data. *)
        sigurg|] ;

      Broker.start ()
    end

let () =
  main ()
