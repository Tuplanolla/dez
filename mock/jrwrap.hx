/** JR Wrapper C/C++ Interface */

#ifndef JRWRAP_HX
#define JRWRAP_HX

#ifdef __cplusplus
extern "C" {
#endif

#include <stddef.h>

/** Call the corresponding C++ function directly. */
int wrap_monkey_saddle_unsafe(int, int);

/** Conservatively estimate the required memory usage. */
size_t wrap_monkey_saddle_buffer_size(size_t, size_t);

/** Deserialize the coordinates from the given buffer-size pairs,
    call the corresponding C++ function with them and
    serialize the result back into the given buffer-size-capacity triple.
    The first element of each buffer carries the sign and
    the rest carry the absolute value
    from the least to the most significant byte.

    If memory allocation fails, then the program will terminate.
    Ideally a nonzero value would be returned,
    but GMP developers fucked up (see section 13 in its manual). */
int wrap_monkey_saddle(unsigned char *, size_t *, size_t,
    unsigned char const *, size_t,
    unsigned char const *, size_t);

#ifdef __cplusplus
}
#endif

#endif
