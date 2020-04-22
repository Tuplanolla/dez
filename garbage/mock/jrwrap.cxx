/** JR Wrapper C++ Implementation */

#include <algorithm>
#include <cstring>
#include <gmpxx.h>
#include "jrlib.hxx"
#include "jrwrap.hx"

int wrap_monkey_saddle_unsafe(int const x, int const y) {
  return monkey_saddle_unsafe(x, y);
}

static void wrap_monkey_saddle_safe(mpz_t zt, mpz_t const xt, mpz_t const yt) {
  mpz_set(zt, monkey_saddle(mpz_class(xt), mpz_class(yt)).get_mpz_t());
}

size_t wrap_monkey_saddle_buffer_size(size_t const nxb, size_t const nyb) {
  /** This estimate is derived as follows.

      Since the monkey saddle is bounded
      from above and below by $\sqrt{x^2 + y^2}^3$ and
      it just so happens that $\sqrt{x^2 + y^2}^3 \le \sqrt 2 (\max |x| |y|)^3
      \le 2 (\max |x| |y|)^3$,
      it suffices to be able to store a number
      with the magnitude $2 (\max |x| |y|)^3$.
      Further, since
      $\log (2 (\max |x| |y|)^3) = \log 2 + 3 \max (\log |x|) (\log |y|)
      \le 1 + 3 \max (\log |x|) (\log |y|)$,
      the number of bits needed
      to do that is $1 + 3 \max (\log |x|) (\log |y|)$. */
  return nxb == 0 && nyb == 0 ? 0 : 1 + (1 + 3 * (std::max(nxb - 1, nyb - 1)));
}

static int const order = -1;
static int const endian = 0;
static size_t const nails = 0;

int wrap_monkey_saddle(unsigned char *const zb, size_t *const nzb,
    size_t const mzb,
    unsigned char const *const xb, size_t const nxb,
    unsigned char const *const yb, size_t const nyb) {
  mpz_t xt;
  mpz_init(xt);
  if (nxb != 0) {
    mpz_import(xt, nxb - 1, order, sizeof *xb, endian, nails, &xb[1]);
    if (xb[0] != 0)
      mpz_neg(xt, xt);
  }

  mpz_t yt;
  mpz_init(yt);
  if (nyb != 0) {
    mpz_import(yt, nyb - 1, order, sizeof *yb, endian, nails, &yb[1]);
    if (yb[0] != 0)
      mpz_neg(yt, yt);
  }

  mpz_t zt;
  mpz_init(zt);
  wrap_monkey_saddle_safe(zt, xt, yt);

  size_t nb;
  void *const b = mpz_export(NULL, &nb, order, sizeof *zb, endian, nails, zt);
  if (nb != 0 && b == NULL) {
    mpz_clear(zt);
    mpz_clear(yt);
    mpz_clear(xt);

    return 1;
  }

  void (*f)(void *, size_t);
  mp_get_memory_functions(NULL, NULL, &f);

  if (1 + nb > mzb) {
    f(b, nb);
    mpz_clear(zt);
    mpz_clear(yt);
    mpz_clear(xt);

    return 1;
  }

  zb[0] = mpz_sgn(zt) < 0 ? 1 : 0;
  (void) std::memcpy(&zb[1], b, nb);
  *nzb = 1 + nb;

  f(b, nb);
  mpz_clear(zt);
  mpz_clear(yt);
  mpz_clear(xt);

  return 0;
}
