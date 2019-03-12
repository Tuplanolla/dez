#include <limits.h>
#include <stdio.h>
#include "jrwrapper.h"

int main(void) {
  (void) printf("%d\n", crunch_wrap(42, 13));

  unsigned char x[] = {0, 42};
  size_t const xz = sizeof x / sizeof *x - 1;
  unsigned char y[] = {0, 13};
  size_t const yz = sizeof y / sizeof *y - 1;
  unsigned char z[3];
  size_t zz;
  size_t const zc = sizeof z / sizeof *z - 1;
  if (!crunchz_wrap(z, &zz, zc, x, xz, y, yz))
    return 1;

  (void) printf("%d\n", (z[0] != 0 ? -1 : 1) *
      ((int) z[1] + ((int) z[2] << CHAR_BIT)));

  return 0;
}
