#include <cstdio>
#include <cstdlib>
#include <iostream>
#include "def_signal.hpp"
#include "gen-cpp/component_types.h"
#include "gen-cpp/polynomial_types.h"

/** TODO Do something useful here. */

int main() {
  identity id;
  id.name = "spores";
  std::cout << "Here comes a C++ object!" << std::endl;
  id.printTo(std::cout);
  std::cout << std::endl;

  std::cout << "Here comes a C value!" << std::endl;
  if ((*posix_signals_array())[2].type == SIG_TYPE_NONRT)
    (void) puts((*posix_signals_array())[2].info.nonrt.str);

  return EXIT_SUCCESS;
}
