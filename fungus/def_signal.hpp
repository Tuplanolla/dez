#ifndef DEF_SIGNAL_HPP
#define DEF_SIGNAL_HPP

#include <csignal>

enum sig_type {
  SIG_TYPE_MISSING,
  SIG_TYPE_NONRT,
  SIG_TYPE_RT
};

struct sig_info {
  enum sig_type type;
  union {
    struct {
      int num;
      char const *str;
    } nonrt;
    struct {
      int num;
      int off;
    } rt;
  } info;
};

struct sig_info const (*posix_signals_array())[NSIG];

#endif
