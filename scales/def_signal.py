import enum
import signal

def signals():
  '''
  All the non-real-time signals.
  '''
  return [
      signal.SIGHUP,
      signal.SIGINT,
      signal.SIGQUIT,
      signal.SIGILL,
      signal.SIGTRAP,
      signal.SIGABRT,
      signal.SIGBUS,
      signal.SIGFPE,
      signal.SIGKILL,
      signal.SIGUSR1,
      signal.SIGSEGV,
      signal.SIGUSR2,
      signal.SIGPIPE,
      signal.SIGALRM,
      signal.SIGTERM,
      signal.SIGCHLD,
      signal.SIGCONT,
      signal.SIGSTOP,
      signal.SIGTSTP,
      signal.SIGTTIN,
      signal.SIGTTOU,
      signal.SIGURG,
      signal.SIGXCPU,
      signal.SIGXFSZ,
      signal.SIGVTALRM,
      signal.SIGPROF,
      signal.SIGWINCH,
      signal.SIGIO,
      signal.SIGPWR,
      signal.SIGSYS]

def real_time_signals():
  '''
  All the real-time signal numbers.
  '''
  return range(signal.SIGRTMIN.value, 1 + signal.SIGRTMAX.value)

class Signal(Exception):
  '''
  Exception raised on a signal.
  '''
  pass

def raise_signal(signum, frame):
  '''
  Raise a ``Signal`` exception for the given signal and stack frame.
  '''
  raise Signal(signum)

class SignalBehavior(enum.Enum):
  '''
  Defunctionalized version of ``signal.SIG_*``.
  '''
  DEFAULT = enum.auto()
  IGNORE = enum.auto()
  RAISE = enum.auto()
  SKIP = enum.auto()

def set_signal(signum, behavior):
  '''
  Defunctionalized version of ``signal.signal``.
  '''
  if behavior is SignalBehavior.DEFAULT:
    return signal.signal(signum, signal.SIG_DFL)
  if behavior is SignalBehavior.IGNORE:
    return signal.signal(signum, signal.SIG_IGN)
  if behavior is SignalBehavior.RAISE:
    return signal.signal(signum, raise_signal)
