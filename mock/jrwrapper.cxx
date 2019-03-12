#include <gmpxx.h>
#include "jrdec.hxx"
#include "jrwrapper.hxx"

static void cruncht_wrap(mpz_t zt, mpz_t const xt, mpz_t const yt) {
  mpz_set(zt, crunchz(mpz_class(xt), mpz_class(yt)).get_mpz_t());
}

static int const order = -1;
static int const endian = 0;
static size_t const nails = 0;

extern "C" int crunchz_wrap(unsigned char *const z, size_t *const zz,
    size_t const zc,
    unsigned char const *const x, size_t const xz,
    unsigned char const *const y, size_t const yz) {
  mpz_t xt;
  mpz_init(xt);
  mpz_import(xt, xz, order, sizeof *x, endian, nails, &x[1]);
  if (x[0] != 0)
    mpz_neg(xt, xt);

  mpz_t yt;
  mpz_init(yt);
  mpz_import(yt, yz, order, sizeof *y, endian, nails, &y[1]);
  if (y[0] != 0)
    mpz_neg(yt, yt);

  mpz_t zt;
  mpz_init(zt);
  cruncht_wrap(zt, xt, yt);

  void *const v = mpz_export(NULL, zz, order, sizeof *z, endian, nails, zt);
  size_t const zr = *zz;
  // Allocation failure for `v`.
  if (v == NULL) {
    mpz_clear(zt);
    mpz_clear(yt);
    mpz_clear(xt);

    return 0;
  }

  // Not enough capacity in `z`.
  if (zr > zc) {
    free(v);
    mpz_clear(zt);
    mpz_clear(yt);
    mpz_clear(xt);

    return 0;
  }

  z[0] = mpz_sgn(zt) < 0 ? 1 : 0;
  (void) memcpy(&z[1], v, zr);

  free(v);
  mpz_clear(zt);
  mpz_clear(yt);
  mpz_clear(xt);

  return 1;
}

extern "C" int crunch_wrap(int const x, int const y) {
  return crunch(x, y);
}
