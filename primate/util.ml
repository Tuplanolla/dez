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
