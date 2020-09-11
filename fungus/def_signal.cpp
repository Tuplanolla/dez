#include <csignal>
#include <mutex>
#include "def_signal.hpp"

static std::mutex cache_mutex;
static bool stale = true;
static struct sig_info posix_signals_cache[NSIG];

struct sig_info const (*posix_signals_array())[NSIG] {
  std::lock_guard<std::mutex> const cache_guard(cache_mutex);

  if (stale) {
    for (int i = 0; i < NSIG; ++i)
      posix_signals_cache[i].type = SIG_TYPE_MISSING;

    posix_signals_cache[SIGHUP].type = SIG_TYPE_NONRT;
    posix_signals_cache[SIGHUP].info.nonrt.num = SIGHUP;
    posix_signals_cache[SIGHUP].info.nonrt.str = "HUP";

    posix_signals_cache[SIGINT].type = SIG_TYPE_NONRT;
    posix_signals_cache[SIGINT].info.nonrt.num = SIGINT;
    posix_signals_cache[SIGINT].info.nonrt.str = "INT";

    posix_signals_cache[SIGQUIT].type = SIG_TYPE_NONRT;
    posix_signals_cache[SIGQUIT].info.nonrt.num = SIGQUIT;
    posix_signals_cache[SIGQUIT].info.nonrt.str = "QUIT";

    posix_signals_cache[SIGILL].type = SIG_TYPE_NONRT;
    posix_signals_cache[SIGILL].info.nonrt.num = SIGILL;
    posix_signals_cache[SIGILL].info.nonrt.str = "ILL";

    posix_signals_cache[SIGTRAP].type = SIG_TYPE_NONRT;
    posix_signals_cache[SIGTRAP].info.nonrt.num = SIGTRAP;
    posix_signals_cache[SIGTRAP].info.nonrt.str = "TRAP";

    posix_signals_cache[SIGABRT].type = SIG_TYPE_NONRT;
    posix_signals_cache[SIGABRT].info.nonrt.num = SIGABRT;
    posix_signals_cache[SIGABRT].info.nonrt.str = "ABRT";

    posix_signals_cache[SIGBUS].type = SIG_TYPE_NONRT;
    posix_signals_cache[SIGBUS].info.nonrt.num = SIGBUS;
    posix_signals_cache[SIGBUS].info.nonrt.str = "BUS";

    posix_signals_cache[SIGFPE].type = SIG_TYPE_NONRT;
    posix_signals_cache[SIGFPE].info.nonrt.num = SIGFPE;
    posix_signals_cache[SIGFPE].info.nonrt.str = "FPE";

    posix_signals_cache[SIGKILL].type = SIG_TYPE_NONRT;
    posix_signals_cache[SIGKILL].info.nonrt.num = SIGKILL;
    posix_signals_cache[SIGKILL].info.nonrt.str = "KILL";

    posix_signals_cache[SIGUSR1].type = SIG_TYPE_NONRT;
    posix_signals_cache[SIGUSR1].info.nonrt.num = SIGUSR1;
    posix_signals_cache[SIGUSR1].info.nonrt.str = "USR1";

    posix_signals_cache[SIGSEGV].type = SIG_TYPE_NONRT;
    posix_signals_cache[SIGSEGV].info.nonrt.num = SIGSEGV;
    posix_signals_cache[SIGSEGV].info.nonrt.str = "SEGV";

    posix_signals_cache[SIGUSR2].type = SIG_TYPE_NONRT;
    posix_signals_cache[SIGUSR2].info.nonrt.num = SIGUSR2;
    posix_signals_cache[SIGUSR2].info.nonrt.str = "USR2";

    posix_signals_cache[SIGPIPE].type = SIG_TYPE_NONRT;
    posix_signals_cache[SIGPIPE].info.nonrt.num = SIGPIPE;
    posix_signals_cache[SIGPIPE].info.nonrt.str = "PIPE";

    posix_signals_cache[SIGALRM].type = SIG_TYPE_NONRT;
    posix_signals_cache[SIGALRM].info.nonrt.num = SIGALRM;
    posix_signals_cache[SIGALRM].info.nonrt.str = "ALRM";

    posix_signals_cache[SIGTERM].type = SIG_TYPE_NONRT;
    posix_signals_cache[SIGTERM].info.nonrt.num = SIGTERM;
    posix_signals_cache[SIGTERM].info.nonrt.str = "TERM";

    posix_signals_cache[SIGSTKFLT].type = SIG_TYPE_NONRT;
    posix_signals_cache[SIGSTKFLT].info.nonrt.num = SIGSTKFLT;
    posix_signals_cache[SIGSTKFLT].info.nonrt.str = "STKFLT";

    posix_signals_cache[SIGCHLD].type = SIG_TYPE_NONRT;
    posix_signals_cache[SIGCHLD].info.nonrt.num = SIGCHLD;
    posix_signals_cache[SIGCHLD].info.nonrt.str = "CHLD";

    posix_signals_cache[SIGCONT].type = SIG_TYPE_NONRT;
    posix_signals_cache[SIGCONT].info.nonrt.num = SIGCONT;
    posix_signals_cache[SIGCONT].info.nonrt.str = "CONT";

    posix_signals_cache[SIGSTOP].type = SIG_TYPE_NONRT;
    posix_signals_cache[SIGSTOP].info.nonrt.num = SIGSTOP;
    posix_signals_cache[SIGSTOP].info.nonrt.str = "STOP";

    posix_signals_cache[SIGTSTP].type = SIG_TYPE_NONRT;
    posix_signals_cache[SIGTSTP].info.nonrt.num = SIGTSTP;
    posix_signals_cache[SIGTSTP].info.nonrt.str = "TSTP";

    posix_signals_cache[SIGTTIN].type = SIG_TYPE_NONRT;
    posix_signals_cache[SIGTTIN].info.nonrt.num = SIGTTIN;
    posix_signals_cache[SIGTTIN].info.nonrt.str = "TTIN";

    posix_signals_cache[SIGTTOU].type = SIG_TYPE_NONRT;
    posix_signals_cache[SIGTTOU].info.nonrt.num = SIGTTOU;
    posix_signals_cache[SIGTTOU].info.nonrt.str = "TTOU";

    posix_signals_cache[SIGURG].type = SIG_TYPE_NONRT;
    posix_signals_cache[SIGURG].info.nonrt.num = SIGURG;
    posix_signals_cache[SIGURG].info.nonrt.str = "URG";

    posix_signals_cache[SIGXCPU].type = SIG_TYPE_NONRT;
    posix_signals_cache[SIGXCPU].info.nonrt.num = SIGXCPU;
    posix_signals_cache[SIGXCPU].info.nonrt.str = "XCPU";

    posix_signals_cache[SIGXFSZ].type = SIG_TYPE_NONRT;
    posix_signals_cache[SIGXFSZ].info.nonrt.num = SIGXFSZ;
    posix_signals_cache[SIGXFSZ].info.nonrt.str = "XFSZ";

    posix_signals_cache[SIGVTALRM].type = SIG_TYPE_NONRT;
    posix_signals_cache[SIGVTALRM].info.nonrt.num = SIGVTALRM;
    posix_signals_cache[SIGVTALRM].info.nonrt.str = "VTALRM";

    posix_signals_cache[SIGPROF].type = SIG_TYPE_NONRT;
    posix_signals_cache[SIGPROF].info.nonrt.num = SIGPROF;
    posix_signals_cache[SIGPROF].info.nonrt.str = "PROF";

    posix_signals_cache[SIGWINCH].type = SIG_TYPE_NONRT;
    posix_signals_cache[SIGWINCH].info.nonrt.num = SIGWINCH;
    posix_signals_cache[SIGWINCH].info.nonrt.str = "WINCH";

    posix_signals_cache[SIGIO].type = SIG_TYPE_NONRT;
    posix_signals_cache[SIGIO].info.nonrt.num = SIGIO;
    posix_signals_cache[SIGIO].info.nonrt.str = "IO";

    posix_signals_cache[SIGPWR].type = SIG_TYPE_NONRT;
    posix_signals_cache[SIGPWR].info.nonrt.num = SIGPWR;
    posix_signals_cache[SIGPWR].info.nonrt.str = "PWR";

    posix_signals_cache[SIGSYS].type = SIG_TYPE_NONRT;
    posix_signals_cache[SIGSYS].info.nonrt.num = SIGSYS;
    posix_signals_cache[SIGSYS].info.nonrt.str = "SYS";

    for (int i = SIGRTMIN; i <= SIGRTMAX; ++i) {
      posix_signals_cache[i].type = SIG_TYPE_RT;
      posix_signals_cache[i].info.rt.num = i;
      posix_signals_cache[i].info.rt.off = i - SIGRTMIN;
    }

    stale = false;
  }

  return &posix_signals_cache;
}
