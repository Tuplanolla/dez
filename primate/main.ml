open Util

let main () =
  bracket
    ~acquire:begin fun () ->
      open_out "/tmp/primate.log"
    end
    ~release:begin fun oc ->
      close_out oc
    end
    begin fun oc ->
      let fmt = Format.formatter_of_out_channel oc in
      Logs.set_reporter (Logs.format_reporter ~app:fmt ~dst:fmt ()) ;
      Logs.set_level (Some Logs.Debug) ;

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
