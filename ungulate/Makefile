CMD:=$(if $(VERBOSE),,@ )
MSG:=$(if $(VERBOSE),@ true || ,@ )

all:: main
.PHONY: all

clean::
	$(CMD) $(RM) .*.aux *.glob *.vo*
	$(CMD) $(RM) extraction.ml extraction.mli
	$(CMD) $(RM) extraction.cmi extraction.cmx extraction.o
	$(CMD) $(RM) adapter.cmi adapter.cmx adapter.o
.PHONY: clean

main:: extraction.mli
	$(MSG) echo OCAMLOPT extraction
	$(CMD) ocamlfind ocamlopt -O2 -c -package num extraction.mli
	$(CMD) ocamlfind ocamlopt -O2 -c -package num extraction.ml
	$(MSG) echo OCAMLOPT adapter
	$(CMD) ocamlfind ocamlopt -O2 -c -package num adapter.mli
	$(CMD) ocamlfind ocamlopt -O2 -c -package num adapter.ml

extraction.mli::
	$(CMD) make -C ../bird
	$(CMD) coqc -Q ../bird Maniunfold Extraction.v
