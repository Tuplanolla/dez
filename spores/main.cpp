#include <cstdio>
#include <cstdlib>
#include <iostream>
#include "def_signal.hpp"
#include "component_types.h"
#include "polynomial_types.h"

/** TODO Do something useful here. */

int main() {
  identity id;
  id.name = "spores";
  std::cout << "Here comes a C++ object!" << std::endl;
  /** All compatible versions of Thrift do not have this debug utility. */
  /* id.printTo(std::cout); */
  std::cout << id.name << std::endl;
  std::cout << "identity(" << "name=" << id.name << ")" << std::endl;

  std::cout << "Here comes a C value!" << std::endl;
  if ((*posix_signals_array())[2].type == SIG_TYPE_NONRT)
    (void) puts((*posix_signals_array())[2].info.nonrt.str);

  return EXIT_SUCCESS;
}
