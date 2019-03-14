# # Jolly Coexistence of Coq and C++
#
# We need a simple use case,
# so we pick one from a recent mathematical publication.
# The monkey saddle [@peckham-2011] is a surface generated
# by the function $(r, t) \mapsto r^3 \cos (3 t)$ in polar coordinates or
# by the function $(x, y) \mapsto x^3 - 3 x y^2$ in Cartesian coordinates.

build: build-jr1 build-jr2 build-dec

clean: clean-dec clean-jr2 clean-jr1

# Suppose we have a numerical solver called JR
# that is written in C++ and built like this.
# The actual example code here is just some GMP bit pushing.

build-jr1:
	g++ -c jrlib.cxx
	g++ -c jrmain.cxx
	g++ -o jrmain jrlib.o jrmain.o -lgmpxx -lgmp
	./jrmain

clean-jr1:
	$(RM) jrlib.o
	$(RM) jrmain.o
	$(RM) jrmain

# It is generally a good idea to isolate the library code from the executable,
# which is what we do for JR here.

build-jr2:
	g++ -c -fPIC jrlib.cxx
	g++ -o libjrlib.so -shared jrlib.o -lgmpxx -lgmp
	# As JR was designed well in the first place, with reentrancy in mind,
	# the same old executable still works without modifications.
	g++ -c jrmain.cxx
	# Since `jrlib.so` is not installed system-wide,
	# we specify `LIBRARY_PATH=.` and `LD_LIBRARY_PATH=.` equivalents as follows.
	# LIBRARY_PATH=. g++ -o jrmain jrmain.o -ljrlib -lgmpxx -lgmp
	# LD_LIBRARY_PATH=. ./jrmain
	g++ -L. -Wl,-rpath=. -o jrmain jrmain.o -ljrlib -lgmpxx -lgmp
	./jrmain

clean-jr2:
	$(RM) jrlib.o
	$(RM) libjrlib.so
	$(RM) jrmain.o
	$(RM) jrmain

# For compatibility with languages other than C++,
# we write a C wrapper for JR and include it in the library as well.

build-jr3:
	g++ -c -fPIC jrlib.cxx
	g++ -c -fPIC jrwrap.cxx
	g++ -o libjrlib.so -shared jrlib.o jrwrap.o -lgmpxx -lgmp
	# We can still compile the original executable without using the wrapper.
	g++ -c jrmain.cxx
	g++ -L. -Wl,-rpath=. -o jrmain jrmain.o -ljrlib -lgmpxx -lgmp
	./jrmain

clean-jr3:
	$(RM) jrlib.o
	$(RM) jrwrap.o
	$(RM) libjrlib.so
	$(RM) jrmain.o
	$(RM) jrmain

# Now we are ready to write the formal specification called DEC and
# extract OCaml code from it.
# We also independently check the proofs for consistency.

build-spec:
	coqc Spec.v
	echo coqchk Spec.vo > Spec.log

clean-spec:
	$(RM) Spec.vo Spec.glob spec.mli spec.ml
	$(RM) Spec.log

# In order to bring DEC and JR together, we do two things.
# First, we write a plugin manager for DEC,
# such that the extracted OCaml code can interface
# with the C wrappers of other libraries.
# Second, we write a driver for JR and
# integrate it into the plugin manager.

build-dec: build-jr3 build-spec
	# This is the driver.
	ocamlfind ocamlopt -c stubjr.c
	ocamlfind ocamlopt -c driver_jr.mli
	ocamlfind ocamlopt -c driver_jr.ml
	# We optimize the extracted code here.
	ocamlfind ocamlopt -c spec.mli
	ocamlfind ocamlopt -c spec.ml
	# This is the plugin manager.
	ocamlfind ocamlopt -c -package num adapter.mli
	ocamlfind ocamlopt -c -package num adapter.ml
	ocamlfind ocamlopt -c -package num main.ml
	# All we have to do is link now.
	# Note that `jrlib` requires `gmp` and `gmpxx`.
	# Argument order also matters in the usual linker fashion.
	ocamlfind ocamlopt -linkpkg -o main -package num \
	stubjr.o driver_jr.cmx spec.cmx adapter.cmx main.cmx \
	-ccopt -L. -ccopt -Wl,-rpath=. -cclib -ljrlib -cclib -lgmpxx -cclib -lgmp
	./jrmain

clean-dec: clean-spec clean-jr3
	$(RM) stubjr.o
	$(RM) driver_jr.cmi driver_jr.cmx driver_jr.o
	$(RM) spec.cmi spec.cmx spec.o
	$(RM) adapter.cmi adapter.cmx adapter.o
	$(RM) main.cmi main.cmx main.o
	$(RM) main
