let posix_signals_array =
  [|(Sys.sigabrt, "ABRT");
    (Sys.sigalrm, "ALRM");
    (Sys.sigfpe, "FPE");
    (Sys.sighup, "HUP");
    (Sys.sigill, "ILL");
    (Sys.sigint, "INT");
    (Sys.sigkill, "KILL");
    (Sys.sigpipe, "PIPE");
    (Sys.sigquit, "QUIT");
    (Sys.sigsegv, "SEGV");
    (Sys.sigterm, "TERM");
    (Sys.sigusr1, "USR1");
    (Sys.sigusr2, "USR2");
    (Sys.sigchld, "CHLD");
    (Sys.sigcont, "CONT");
    (Sys.sigstop, "STOP");
    (Sys.sigtstp, "TSTP");
    (Sys.sigttin, "TTIN");
    (Sys.sigttou, "TTOU");
    (Sys.sigvtalrm, "VTALRM");
    (Sys.sigprof, "PROF");
    (Sys.sigbus, "BUS");
    (Sys.sigpoll, "POLL");
    (Sys.sigsys, "SYS");
    (Sys.sigtrap, "TRAP");
    (Sys.sigurg, "URG");
    (Sys.sigxcpu, "XCPU");
    (Sys.sigxfsz, "XFSZ")|]

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
