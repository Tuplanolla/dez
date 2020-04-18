CMD:=$(if $(VERBOSE),,@ )
MSG:=$(if $(VERBOSE),@ true || ,@ )

all:: main
	$(MSG) echo MAIN test
	@ ./main test
.PHONY: all

clean::
	$(CMD) $(RM) *.cmi *.cmx *.o
	$(CMD) $(RM) main
.PHONY: clean

main::
	$(CMD) make -C ../ungulate
	$(MSG) echo OCAMLOPT main
	$(CMD) ocamlfind ocamlopt -I ../ungulate -O2 -c -package num main.ml
	$(CMD) ocamlfind ocamlopt -I ../ungulate -O2 -linkpkg -o main -package num \
	extraction.cmx adapter.cmx main.cmx
