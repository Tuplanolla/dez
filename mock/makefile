all: manager

clean: clean-manager

# Suppose we have a numerical solver called JRDEC
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
# which is what we do for JRDEC here.
jrmod:
	g++ -c -fPIC jrdec.cxx
	g++ -o libjrdec.so -shared jrdec.o
	# As JRDEC was designed well in the first place, with reentrancy in mind,
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
# we write a C wrapper for JRDEC and include it in the library as well.
jrwrapmod:
	g++ -c -fPIC jrdec.cxx
	g++ -c -fPIC jrwrapper.cxx
	g++ -o libjrdec.so -shared jrdec.o jrwrapper.o
	# We demonstrate how the executable can be replaced with one written in C,
	# as long as we link all the dependencies correctly.
	gcc -c jrwrapmain.c
	LIBRARY_PATH=. gcc -o jrwrapmain jrwrapmain.o -ljrdec -lgmpxx -lgmp -lstdc++ -lm
	LD_LIBRARY_PATH=. ./jrwrapmain

clean-jrwrapmod:
	$(RM) jrdec.o
	$(RM) jrwrapper.o
	$(RM) libjrdec.so
	$(RM) jrwrapmain.o
	$(RM) jrwrapmain

# Now we are ready to write the formal specification called DEC and
# extract OCaml code from it.
# We also independently check the proofs for consistency.
dec:
	coqc DEC.v
	echo coqchk DEC.vo > DEC.log

clean-dec:
	$(RM) DEC.vo DEC.glob dec.mli dec.ml
	$(RM) DEC.log

# In order to bring DEC and JRDEC together, we do two things.
# First, we write a plugin manager for DEC,
# such that the extracted OCaml code can interface
# with the C wrappers of other libraries.
# Second, we write a driver for JRDEC and
# integrate it into the plugin manager.
manager: jrwrapmod dec
	# This is the driver.
	ocamlfind ocamlopt -c jrstub.c
	ocamlfind ocamlopt -c jr_driver.mli
	ocamlfind ocamlopt -c jr_driver.ml
	# We optimize the extracted code here.
	ocamlfind ocamlopt -c dec.mli
	ocamlfind ocamlopt -c dec.ml
	# This is the plugin manager.
	ocamlfind ocamlopt -c -package num main.ml
	# All we have to do is link now.
	LIBRARY_PATH=. ocamlfind ocamlopt -linkpkg -o main -package num \
	jrstub.o jr_driver.cmx \
	-cclib -ljrdec -cclib -lgmpxx -cclib -lgmp -cclib -lstdc++ -cclib -lm \
	dec.cmx main.cmx
	LD_LIBRARY_PATH=. ./main

clean-manager: clean-dec clean-jrwrapmod
	$(RM) jrstub.o
	$(RM) jr_driver.cmi jr_driver.cmx jr_driver.o
	$(RM) dec.cmi dec.cmx dec.o
	$(RM) main.cmi main.cmx main.o
	$(RM) main
