all: jr jrmod decster

clean: clean-decster clean-jrmod clean-jr

# The monkey saddle [@peckham-2011] is a surface generated
# by the function $(r, t) \mapsto r^3 \cos (3 t)$ in polar coordinates or
# by the function $(x, y) \mapsto x^3 - 3 x y^2$ in cartesian coordinates.
# Funny that someone has recently published such an elementary result.
#
# @conference{peckham-2011,
#   author = {S. D. Peckham},
#   title = {Monkey, Starfish and Octopus Saddles},
#   date = {2011-05-30},
#   editor = {T. Hengl and I. S. Evans and J. P. Wilson and M. Gould},
#   booktitle = {Geomorphometry 2011},
#   pages = {31--34},
#   location = {Redlands, California, USA},
#   url = {http://geomorphometry.org/Peckham2011b},
# }
#
# The following files are in order.
#
# JR Project
# [X] jrdec.cxx
# [X] jrdec.hxx
# [X] jrmain.cxx
# [X] jrwrap.hx
# [X] jrwrap.cxx
# DEC Project
# [ ] stubjr.c
# [ ] stubjr.h
# [ ] driver_jr.ml
# [ ] driver_jr.mli
# [ ] DEC.v
# [ ] main.ml

# Suppose we have a numerical solver called JR
# that is written in C++ and built like this.
# The actual example code here is just some GMP bit pushing.
jr:
	g++ -c jrdec.cxx
	g++ -c jrmain.cxx
	g++ -o jrmain jrdec.o jrmain.o -lgmpxx -lgmp
	./jrmain

clean-jr:
	$(RM) jrdec.o
	$(RM) jrmain.o
	$(RM) jrmain

# It is generally a good idea to isolate the library code from the executable,
# which is what we do for JR here.
jrmod:
	g++ -c -fPIC jrdec.cxx
	g++ -o libjrdec.so -shared jrdec.o
	# As JR was designed well in the first place, with reentrancy in mind,
	# the same old executable still works without modifications.
	g++ -c jrmain.cxx
	# Since `jrdec.so` is not installed system-wide,
	# we specify `LIBRARY_PATH=.` and `LD_LIBRARY_PATH=.` as follows.
	# Using `-L.` or such would also work.
	LIBRARY_PATH=. g++ -o jrmain jrmain.o -ljrdec -lgmpxx -lgmp
	LD_LIBRARY_PATH=. ./jrmain

clean-jrmod:
	$(RM) jrdec.o
	$(RM) libjrdec.so
	$(RM) jrmain.o
	$(RM) jrmain

# For compatibility with languages other than C++,
# we write a C wrapper for JR and include it in the library as well.
jrwrap: jrmod
	g++ -c -fPIC jrwrap.cxx
	g++ -o libjrdec.so -shared jrdec.o jrwrap.o
	# We compile the original executable without the wrapper.
	g++ -c jrmain.cxx
	LIBRARY_PATH=. g++ -o jrmain jrmain.o -ljrdec -lgmpxx -lgmp
	LD_LIBRARY_PATH=. ./jrmain

clean-jrwrap: clean-jrmod
	$(RM) jrwrap.o
	$(RM) libjrdec.so
	$(RM) jrmain.o
	$(RM) jrmain

# Now we are ready to write the formal specification called DEC and
# extract OCaml code from it.
# We also independently check the proofs for consistency.
dec:
	coqc DEC.v
	echo coqchk DEC.vo > DEC.log

clean-dec:
	$(RM) DEC.vo DEC.glob dec.mli dec.ml
	$(RM) DEC.log

# In order to bring DEC and JR together, we do two things.
# First, we write a plugin manager for DEC,
# such that the extracted OCaml code can interface
# with the C wrappers of other libraries.
# Second, we write a driver for JR and
# integrate it into the plugin manager.
decster: jrwrap dec
	# This is the driver.
	ocamlfind ocamlopt -c stubjr.c -ccopt -Wall -ccopt -Wextra -g
	ocamlfind ocamlopt -c driver_jr.mli -g
	ocamlfind ocamlopt -c driver_jr.ml -g
	# We optimize the extracted code here.
	ocamlfind ocamlopt -c dec.mli -g
	ocamlfind ocamlopt -c dec.ml -g
	# This is the plugin manager.
	ocamlfind ocamlopt -c -package num main.ml -g
	# All we have to do is link now.
	LIBRARY_PATH=. ocamlfind ocamlopt -linkpkg -o main -package num \
	stubjr.o driver_jr.cmx \
	-cclib -ljrdec -cclib -lgmpxx -cclib -lgmp -cclib -lstdc++ -cclib -lm \
	dec.cmx main.cmx
	LD_LIBRARY_PATH=. ./main

clean-decster: clean-dec clean-jrwrap
	$(RM) stubjr.o
	$(RM) driver_jr.cmi driver_jr.cmx driver_jr.o
	$(RM) dec.cmi dec.cmx dec.o
	$(RM) main.cmi main.cmx main.o
	$(RM) main
