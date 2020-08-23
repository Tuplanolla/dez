import client_proxy
from def_signal import *
import logging
import signal

logger = logging.getLogger('maniunfold.scales')

def config_logging():
  '''
  Configure logging.

  Log messages follow a format, where

  * ``[%(asctime)s.%(msecs)03d]`` mimicks ``dmesg``,
  * ``==%(process)d==`` mimicks ``valgrind``,
  * ``"%(name)s"`` mimicks ``httpd``,
  * ``<%(funcName)s>`` mimicks ``objdump`` and
  * ``%(filename)s:%(lineno)d: %(levelname)s: %(message)s`` mimicks ``cc``.
  '''
  logging.basicConfig(
    filename='/tmp/scales.log',
    filemode='w',
    format=' '.join([
      '[%(asctime)s.%(msecs)03d]',
      '==%(process)d==',
      '"%(name)s"',
      '%(levelname)s: %(message)s']),
    datefmt='%s',
    level=logging.DEBUG)

def config_signals():
  '''
  Configure signal handling.
  '''
  for sig, behavior in [
      (signal.SIGHUP, SignalBehavior.SIGNAL_RAISE),
      (signal.SIGINT, SignalBehavior.SIGNAL_RAISE),
      (signal.SIGQUIT, SignalBehavior.SIGNAL_RAISE),
      (signal.SIGILL, SignalBehavior.SIGNAL_RAISE),
      (signal.SIGTRAP, SignalBehavior.SIGNAL_RAISE),
      (signal.SIGABRT, SignalBehavior.SIGNAL_RAISE),
      (signal.SIGBUS, SignalBehavior.SIGNAL_RAISE),
      (signal.SIGFPE, SignalBehavior.SIGNAL_RAISE),
      # We cannot catch this signal.
      (signal.SIGKILL, SignalBehavior.SIGNAL_SKIP),
      (signal.SIGUSR1, SignalBehavior.SIGNAL_RAISE),
      (signal.SIGSEGV, SignalBehavior.SIGNAL_RAISE),
      (signal.SIGUSR2, SignalBehavior.SIGNAL_RAISE),
      (signal.SIGPIPE, SignalBehavior.SIGNAL_RAISE),
      (signal.SIGALRM, SignalBehavior.SIGNAL_RAISE),
      (signal.SIGTERM, SignalBehavior.SIGNAL_RAISE),
      # We keep the default behavior of this signal
      # in order to be able to wait for subprocesses.
      (signal.SIGCHLD, SignalBehavior.SIGNAL_DEFAULT),
      (signal.SIGCONT, SignalBehavior.SIGNAL_DEFAULT),
      # We cannot catch this signal.
      (signal.SIGSTOP, SignalBehavior.SIGNAL_SKIP),
      # We keep the default behavior of these signals,
      # even though we may need to account for them at some point.
      (signal.SIGTSTP, SignalBehavior.SIGNAL_DEFAULT),
      (signal.SIGTTIN, SignalBehavior.SIGNAL_DEFAULT),
      (signal.SIGTTOU, SignalBehavior.SIGNAL_DEFAULT),
      # We ignore this signal,
      # because we do not have any urgent data.
      (signal.SIGURG, SignalBehavior.SIGNAL_IGNORE),
      (signal.SIGXCPU, SignalBehavior.SIGNAL_RAISE),
      (signal.SIGXFSZ, SignalBehavior.SIGNAL_RAISE),
      (signal.SIGVTALRM, SignalBehavior.SIGNAL_RAISE),
      (signal.SIGPROF, SignalBehavior.SIGNAL_RAISE),
      # We ignore this signal,
      # because we do not manage windows.
      (signal.SIGWINCH, SignalBehavior.SIGNAL_IGNORE),
      (signal.SIGIO, SignalBehavior.SIGNAL_RAISE),
      (signal.SIGPWR, SignalBehavior.SIGNAL_RAISE),
      (signal.SIGSYS, SignalBehavior.SIGNAL_RAISE)]:
    try:
      set_signal(sig, behavior)
      logger.debug('Set the behavior of SIG{} ({}).'
          .format(sig.name, sig.value))
    except OSError:
      logger.warn('Failed to set the behavior of SIG{} ({}).'
          .format(sig.name, sig.value))

  # We ignore these signals,
  # because we do have real-time constraints.
  for signum in real_time_signals():
    try:
      set_signal(signum, SignalBehavior.SIGNAL_IGNORE)
      logger.debug('Set the behavior of SIGRTMIN + {} ({}).'
          .format(signum - signal.SIGRTMIN.value, signum))
    except OSError:
      logger.warn('Failed to set the behavior of SIGRTMIN + {} ({}).'
          .format(signum - signal.SIGRTMIN.value, signum))

def main():
  '''
  Configure and start the message broker.
  '''
  config_logging()
  config_signals()
  client_proxy.start()

main()
