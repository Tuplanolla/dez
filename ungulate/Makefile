CMD:=$(if $(VERBOSE),,@ )
MSG:=$(if $(VERBOSE),@ true || ,@ )

all:: main
	$(MSG) echo MAIN test
	@ ./main test
.PHONY: all

clean::
	$(CMD) $(RM) .*.aux *.glob *.vo*
	$(CMD) $(RM) extraction.ml extraction.mli
	$(CMD) $(RM) extraction.cmi extraction.cmx extraction.o
	$(CMD) $(RM) adapter.cmi adapter.cmx adapter.o
	$(CMD) $(RM) main.cmi main.cmx main.o main
.PHONY: clean

main:: extraction.mli
	$(MSG) echo OCAMLOPT extraction
	$(CMD) ocamlfind ocamlopt -O2 -c -package num extraction.mli
	$(CMD) ocamlfind ocamlopt -O2 -c -package num extraction.ml
	$(MSG) echo OCAMLOPT adapter
	$(CMD) ocamlfind ocamlopt -O2 -c -package num adapter.mli
	$(CMD) ocamlfind ocamlopt -O2 -c -package num adapter.ml
	$(MSG) echo OCAMLOPT main
	$(CMD) ocamlfind ocamlopt -O2 -c -package num main.ml
	$(CMD) ocamlfind ocamlopt -O2 -linkpkg -o main -package num \
	extraction.cmx adapter.cmx main.cmx

extraction.mli::
	$(CMD) make -C ../bird
	$(CMD) coqc -Q ../bird Maniunfold Extraction.v

dune::
	dune build @install
.PHONY: dune
