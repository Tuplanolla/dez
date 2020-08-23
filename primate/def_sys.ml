let posix_signals_array =
  let open Sys in [|
    (sigabrt, "ABRT");
    (sigalrm, "ALRM");
    (sigfpe, "FPE");
    (sighup, "HUP");
    (sigill, "ILL");
    (sigint, "INT");
    (sigkill, "KILL");
    (sigpipe, "PIPE");
    (sigquit, "QUIT");
    (sigsegv, "SEGV");
    (sigterm, "TERM");
    (sigusr1, "USR1");
    (sigusr2, "USR2");
    (sigchld, "CHLD");
    (sigcont, "CONT");
    (sigstop, "STOP");
    (sigtstp, "TSTP");
    (sigttin, "TTIN");
    (sigttou, "TTOU");
    (sigvtalrm, "VTALRM");
    (sigprof, "PROF");
    (sigbus, "BUS");
    (sigpoll, "POLL");
    (sigsys, "SYS");
    (sigtrap, "TRAP");
    (sigurg, "URG");
    (sigxcpu, "XCPU");
    (sigxfsz, "XFSZ")|]

let posix_signals =
  Array.map fst posix_signals_array

let string_of_signal =
  let h = Hashtbl.create (Array.length posix_signals_array) in
  Array.iter (fun (i, s) -> Hashtbl.add h i s) posix_signals_array;
  Hashtbl.find h

let signal_of_string =
  let h = Hashtbl.create (Array.length posix_signals_array) in
  Array.iter (fun (i, s) -> Hashtbl.add h s i) posix_signals_array;
  Hashtbl.find h

exception Signal of int

let raise_signal i =
  raise (Signal i)

type signal_behavior =
  | Signal_default
  | Signal_ignore
  | Signal_raise
  | Signal_skip

let set_signal i b =
  match b with
  | Signal_default -> Sys.set_signal i Sys.Signal_default
  | Signal_ignore -> Sys.set_signal i Sys.Signal_ignore
  | Signal_raise -> Sys.set_signal i (Sys.Signal_handle raise_signal)
  | Signal_skip -> ()
