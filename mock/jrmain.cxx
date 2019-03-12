#include <gmpxx.h>
#include <iostream>
#include "jrdec.hxx"

int main() {
  std::cout << crunch(42, 13) << std::endl;

  mpz_class const xc = 42;
  mpz_class const yc = 13;
  std::cout << crunchz(xc, yc) << std::endl;

  return 0;
}
