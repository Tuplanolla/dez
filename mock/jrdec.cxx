#include <cmath>
#include <gmpxx.h>
#include "jrdec.hxx"

mpz_class crunchz(mpz_class const xc, mpz_class const yc) {
  mpz_class x3c;
  mpz_pow_ui(x3c.get_mpz_t(), xc.get_mpz_t(), 3);

  mpz_class y2c;
  mpz_pow_ui(y2c.get_mpz_t(), yc.get_mpz_t(), 2);

  return x3c - 3 * xc * y2c;
}

int crunch(int const x, int const y) {
  return pow(x, 3) - 3 * x * pow(y, 2);
}
