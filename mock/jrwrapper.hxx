#ifndef JRWRAPPER_HXX
#define JRWRAPPER_HXX

// These are nonempty buffers, where the first byte is the sign.
// The accompanying sizes are the sizes without the first byte.
extern "C" int crunchz_wrap(unsigned char *, size_t *, size_t,
    unsigned char const *, size_t,
    unsigned char const *, size_t);

extern "C" int crunch_wrap(int, int);

#endif
