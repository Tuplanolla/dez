import client_proxy
import def_signal
import logging
import signal
import sys
from def_signal import SignalBehavior

logger = logging.getLogger('dez.scales')

def config_logging(loc=None):
  '''
  Configure logging.

  Log messages follow a format, where

  * ``[%(asctime)s.%(msecs)03d]`` mimicks ``dmesg``,
  * ``==%(process)d==`` mimicks ``valgrind``,
  * ``"%(name)s"`` mimicks ``httpd``,
  * ``<%(funcName)s>`` mimicks ``objdump`` and
  * ``%(filename)s:%(lineno)d: %(levelname)s: %(message)s`` mimicks ``cc``.
  '''
  if loc is None:
    raise ValueError('loc')

  if loc:
    fmt = ' '.join([
      '[%(asctime)s.%(msecs)03d]',
      '==%(process)d==',
      '"%(name)s"',
      '%(filename)s:%(lineno)d: %(levelname)s: %(message)s'])
  else:
    fmt = ' '.join([
      '[%(asctime)s.%(msecs)03d]',
      '==%(process)d==',
      '"%(name)s"',
      '%(levelname)s: %(message)s'])

  logging.basicConfig(
    filename='/tmp/scales.log',
    filemode='w',
    format=fmt,
    datefmt='%s',
    level=logging.DEBUG)

def config_signals():
  '''
  Configure signal handling.
  '''
  for sig, behavior in [
      (signal.SIGHUP, SignalBehavior.RAISE),
      (signal.SIGINT, SignalBehavior.RAISE),
      (signal.SIGQUIT, SignalBehavior.RAISE),
      (signal.SIGILL, SignalBehavior.RAISE),
      (signal.SIGTRAP, SignalBehavior.RAISE),
      (signal.SIGABRT, SignalBehavior.RAISE),
      (signal.SIGBUS, SignalBehavior.RAISE),
      (signal.SIGFPE, SignalBehavior.RAISE),
      # We cannot catch this signal.
      (signal.SIGKILL, SignalBehavior.SKIP),
      (signal.SIGUSR1, SignalBehavior.RAISE),
      (signal.SIGSEGV, SignalBehavior.RAISE),
      (signal.SIGUSR2, SignalBehavior.RAISE),
      (signal.SIGPIPE, SignalBehavior.RAISE),
      (signal.SIGALRM, SignalBehavior.RAISE),
      (signal.SIGTERM, SignalBehavior.RAISE),
      # We keep the default behavior of this signal,
      # so that we can wait for subprocesses.
      (signal.SIGCHLD, SignalBehavior.DEFAULT),
      (signal.SIGCONT, SignalBehavior.DEFAULT),
      # We cannot catch this signal.
      (signal.SIGSTOP, SignalBehavior.SKIP),
      # We keep the default behavior of these signals,
      # even though we may need to account for them at some point.
      (signal.SIGTSTP, SignalBehavior.DEFAULT),
      (signal.SIGTTIN, SignalBehavior.DEFAULT),
      (signal.SIGTTOU, SignalBehavior.DEFAULT),
      # We ignore this signal,
      # because we do not have any urgent data.
      (signal.SIGURG, SignalBehavior.IGNORE),
      (signal.SIGXCPU, SignalBehavior.RAISE),
      (signal.SIGXFSZ, SignalBehavior.RAISE),
      (signal.SIGVTALRM, SignalBehavior.RAISE),
      (signal.SIGPROF, SignalBehavior.RAISE),
      # We ignore this signal,
      # because we do not manage windows.
      (signal.SIGWINCH, SignalBehavior.IGNORE),
      (signal.SIGIO, SignalBehavior.RAISE),
      (signal.SIGPWR, SignalBehavior.RAISE),
      (signal.SIGSYS, SignalBehavior.RAISE)]:
    try:
      def_signal.set_signal(sig, behavior)
      logger.debug('Set the behavior of {} ({}).'
          .format(sig.name, sig.value))
    except OSError:
      logger.warn('Failed to set the behavior of {} ({}).'
          .format(sig.name, sig.value))

  # We ignore these signals,
  # because we do not have real-time constraints.
  for signum in def_signal.real_time_signals():
    try:
      def_signal.set_signal(signum, SignalBehavior.IGNORE)
      logger.debug('Set the behavior of SIGRTMIN + {} ({}).'
          .format(signum - signal.SIGRTMIN.value, signum))
    except OSError:
      logger.warn('Failed to set the behavior of SIGRTMIN + {} ({}).'
          .format(signum - signal.SIGRTMIN.value, signum))

def main():
  '''
  Configure and start the client.
  '''
  config_logging(loc=False)
  config_signals()
  if len(sys.argv) == 3:
    client_proxy.start(addr=sys.argv[1], port=sys.argv[2])
  elif len(sys.argv) == 2:
    client_proxy.start(addr=sys.argv[1])
  else:
    client_proxy.start()

if __name__ == '__main__':
  main()
