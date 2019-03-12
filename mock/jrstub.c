#include <caml/mlvalues.h>
#include "jrstub.h"
#include "jrwrapper.h"

CAMLprim value crunch_driver(value const xv, value const yv) {
  return Val_long(crunch_wrap(Long_val(xv), Long_val(yv)));
}
