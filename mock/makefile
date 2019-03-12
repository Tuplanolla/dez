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

dec:
	coqc DEC.v
	echo coqchk DEC.vo > DEC.log
	ocamlfind ocamlopt -c dec.mli
	ocamlfind ocamlopt -c dec.ml

bridge:
	ocamlfind ocamlopt -c -package num main.ml
	ocamlfind ocamlopt -linkpkg -o main -package num dec.cmx main.cmx
	./main

clean-dec:
	$(RM) DEC.glob DEC.vo dec.ml dec.mli
	$(RM) DEC.log
	$(RM) dec.cmi dec.cmx dec.o

clean-bridge:
	$(RM) main.cmx main.o main.cmi
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
