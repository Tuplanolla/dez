/** DEC JR Stub C Implementation */

#include <caml/alloc.h>
#include <caml/fail.h>
#include <caml/memory.h>
#include <caml/mlvalues.h>
#include <stdlib.h>
#include "jrwrap.hx"
#include "stubjr.h"

CAMLprim value stub_monkey_saddle_unsafe(value xv, value yv) {
  CAMLparam2(xv, yv);

  CAMLreturn(Val_int(wrap_monkey_saddle_unsafe(Int_val(xv), Int_val(yv))));
}

static char const *const cam = "cannot allocate memory";

CAMLprim value stub_monkey_saddle(value xv, value yv) {
  CAMLparam2(xv, yv);

  size_t const nxb = Wosize_val(xv);
  size_t const nyb = Wosize_val(yv);
  size_t const nzb = wrap_monkey_saddle_buffer_size(nxb, nyb);

  /** Instead of allocating separate blocks for all the buffers,
      it should be faster to allocate only one shared block and
      partition it manually. */

#ifdef STUBJR_ALLOCATE_SEPARATE

  unsigned char *const zb = malloc(nzb);
  if (zb == NULL)
    caml_failwith(cam);

  unsigned char *const xb = malloc(nxb);
  if (xb == NULL)
    caml_failwith(cam);

  for (size_t i = 0; i < nxb; ++i)
    xb[i] = Int_val(Field(xv, i));

  unsigned char *const yb = malloc(nyb);
  if (yb == NULL)
    caml_failwith(cam);

  for (size_t i = 0; i < nyb; ++i)
    yb[i] = Int_val(Field(yv, i));

  size_t nz;
  if (wrap_monkey_saddle(zb, &nz, nzb, xb, nxb, yb, nyb) != 0)
    caml_failwith(cam);

  free(yb);
  free(xb);

  CAMLlocal1(zv);
  zv = caml_alloc(nz, 0);

  for (size_t i = 0; i < nz; ++i)
    Store_field(zv, i, Val_int(zb[i]));

  free(zb);

#else

  unsigned char *const b = malloc(nzb + nxb + nyb);
  if (b == NULL)
    caml_failwith(cam);

  unsigned char *const zb = &b[0];
  unsigned char *const xb = &b[nzb];
  unsigned char *const yb = &b[nzb + nxb];

  for (size_t i = 0; i < nxb; ++i)
    xb[i] = Int_val(Field(xv, i));

  for (size_t i = 0; i < nyb; ++i)
    yb[i] = Int_val(Field(yv, i));

  size_t nz;
  if (wrap_monkey_saddle(zb, &nz, nzb, xb, nxb, yb, nyb) != 0)
    caml_failwith(cam);

  CAMLlocal1(zv);
  zv = caml_alloc(nz, 0);

  for (size_t i = 0; i < nz; ++i)
    Store_field(zv, i, Val_int(zb[i]));

  free(b);

#endif

  CAMLreturn(zv);
}
