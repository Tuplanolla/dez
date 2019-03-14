/** JR Library C++ Implementation */

#include <gmpxx.h>
#include "jrlib.hxx"

int monkey_saddle_unsafe(int const x, int const y) {
  /** We factor $x^3 - 3 x y^2$ into $x (x^2 - 3 y^2)$,
      because the factored expression has one fewer multiplication and
      does not contain subexpressions that would overflow
      when the whole expression would not. */
  return x * (x * x - 3 * (y * y));
}

mpz_class monkey_saddle(mpz_class const xc, mpz_class const yc) {
  /** Even though it is not necessary to use `mpz_pow_ui` here,
      we do so anyway to have an excuse to reach around the class interface. */

  mpz_class x2c;
  mpz_pow_ui(x2c.get_mpz_t(), xc.get_mpz_t(), 2);

  mpz_class y2c;
  mpz_pow_ui(y2c.get_mpz_t(), yc.get_mpz_t(), 2);

  return xc * (x2c - 3 * y2c);
}
