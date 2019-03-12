#ifndef JRWRAPPER_H
#define JRWRAPPER_H

#include <stddef.h>

int crunchz_wrap(unsigned char *, size_t *, size_t,
    unsigned char const *, size_t,
    unsigned char const *, size_t);

int crunch_wrap(int, int);

#endif
