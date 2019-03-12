all: bridge jr jrwrapmod bridgemod jrmod dec jrwrap

clean: clean-dec clean-jrwrap clean-jr clean-jrwrapmod clean-bridge clean-jrmod

dec:
	coqc DEC.v
	echo coqchk DEC.vo > DEC.log

jrwrapmod:
	g++ -c -fPIC jrdec.cxx
	g++ -c -fPIC jrwrapper.cxx
	g++ -o libjrdec.so -shared jrdec.o jrwrapper.o
	gcc -c jrwrapmain.c
	# If `jrdec.so` is not installed, specify `-L.` as follows.
	gcc -L. -o jrwrapmain jrwrapmain.o -ljrdec  -lgmpxx -lgmp -lstdc++ -lm
	# If `jrdec.so` is not installed, specify `LD_LIBRARY_PATH=.` as follows.
	LD_LIBRARY_PATH=. ./jrwrapmain

jrwrap:
	g++ -c jrdec.cxx
	g++ -c jrwrapper.cxx
	gcc -c jrwrapmain.c
	gcc -o jrwrapmain jrdec.o jrwrapper.o jrwrapmain.o -lgmpxx -lgmp -lstdc++ -lm
	./jrwrapmain

jrmod:
	g++ -c -fPIC jrdec.cxx
	g++ -o libjrdec.so -shared jrdec.o
	g++ -c jrmain.cxx
	# If `jrdec.so` is not installed, specify `-L.` as follows.
	g++ -L. -o jrmain jrmain.o -ljrdec -lgmpxx -lgmp
	# If `jrdec.so` is not installed, specify `LD_LIBRARY_PATH=.` as follows.
	LD_LIBRARY_PATH=. ./jrmain

jr:
	g++ -c jrdec.cxx
	g++ -c jrmain.cxx
	g++ -o jrmain jrdec.o jrmain.o -lgmpxx -lgmp
	./jrmain

bridgemod: jrwrapmod
	ocamlfind ocamlopt -c jrstub.c
	ocamlfind ocamlopt -c jr_driver.mli
	ocamlfind ocamlopt -c jr_driver.ml
	ocamlfind ocamlopt -c dec.mli
	ocamlfind ocamlopt -c dec.ml
	ocamlfind ocamlopt -c -package num main.ml
	# If `jrdec.so` is not installed, specify `-L.` as follows.
	ocamlfind ocamlopt -linkpkg -o main -package num \
	-ccopt -L. \
	jrstub.o jr_driver.cmx \
	-cclib -ljrdec -cclib -lgmpxx -cclib -lgmp -cclib -lstdc++ -cclib -lm \
	dec.cmx main.cmx
	# If `jrdec.so` is not installed, specify `LD_LIBRARY_PATH=.` as follows.
	LD_LIBRARY_PATH=. ./main

bridge: jrwrap
	ocamlfind ocamlopt -c jrstub.c
	ocamlfind ocamlopt -c jr_driver.mli
	ocamlfind ocamlopt -c jr_driver.ml
	ocamlfind ocamlopt -c dec.mli
	ocamlfind ocamlopt -c dec.ml
	ocamlfind ocamlopt -c -package num main.ml
	ocamlfind ocamlopt -linkpkg -o main -package num \
	jrdec.o jrwrapper.o jrstub.o jr_driver.cmx \
	-cclib -lgmpxx -cclib -lgmp -cclib -lstdc++ -cclib -lm \
	dec.cmx main.cmx
	./main

clean-bridgemod: clean-jrwrapmod
	$(RM) jrstub.o
	$(RM) jr_driver.cmi jr_driver.cmx jr_driver.o
	$(RM) dec.cmi dec.cmx dec.o
	$(RM) main.cmi main.cmx main.o
	$(RM) main

clean-bridge: clean-jrwrap
	$(RM) jrstub.o
	$(RM) jr_driver.cmi jr_driver.cmx jr_driver.o
	$(RM) dec.cmi dec.cmx dec.o
	$(RM) main.cmi main.cmx main.o
	$(RM) main

clean-jr:
	$(RM) jrdec.o
	$(RM) jrmain.o
	$(RM) jrmain

clean-jrmod:
	$(RM) jrdec.o
	$(RM) libjrdec.so
	$(RM) jrmain.o
	$(RM) jrmain

clean-jrwrap:
	$(RM) jrdec.o
	$(RM) jrwrapper.o
	$(RM) jrwrapmain.o
	$(RM) jrwrapmain

clean-jrwrapmod:
	$(RM) jrdec.o
	$(RM) jrwrapper.o
	$(RM) libjrdec.so
	$(RM) jrwrapmain.o
	$(RM) jrwrapmain

clean-dec:
	$(RM) DEC.glob DEC.vo dec.mli dec.ml
	$(RM) DEC.log
