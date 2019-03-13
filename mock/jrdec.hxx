/** JR Library C++ Interface */

#ifndef JRDEC_HXX
#define JRDEC_HXX

#include <gmpxx.h>

/** Quickly evaluate a point on the monkey saddle in cartesian coordinates.

    If the result would overflow, then the behavior is undefined. */
int monkey_saddle_unsafe(int, int);

/** Evaluate a point on the monkey saddle in cartesian coordinates.

    If memory allocation fails, then the program will terminate.
    Ideally an exception would be thrown,
    but GMP developers fucked up (see section 13 in its manual). */
mpz_class monkey_saddle(mpz_class, mpz_class);

#endif
