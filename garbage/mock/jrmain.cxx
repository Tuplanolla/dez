/** JR Executable C++ Implementation */

#include <gmpxx.h>
#include <iostream>
#include "jrlib.hxx"

int main() {
  std::cout << "jrmain -> jrlib (unsafe)" << std::endl;
  std::cout << monkey_saddle_unsafe(42, 13) << std::endl;
  std::cout << "jrmain -> jrlib" << std::endl;
  std::cout << monkey_saddle(42, 13) << std::endl;

  return EXIT_SUCCESS;
}
