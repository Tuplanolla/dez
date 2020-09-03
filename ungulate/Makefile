CMD:=$(if $(VERBOSE),,@ )
MSG:=$(if $(VERBOSE),@ true || ,@ )

OCAMLPFFTLAGS:=-O2 -package num,logs -thread

build:: def_sys.cmi def_sys.cmx util.cmi util.cmx
.PHONY: build

clean::
	$(CMD) $(RM) *.cmi *.cmx *.o
.PHONY: clean

%.cmi:: %.mli
	$(CMD) ocamlfind ocamlopt $(OCAMLPFFTLAGS) -c $<

%.cmx:: %.ml
	$(CMD) ocamlfind ocamlopt $(OCAMLPFFTLAGS) -c $<
