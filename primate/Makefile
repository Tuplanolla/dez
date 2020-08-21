CMD:=$(if $(VERBOSE),,@ )
MSG:=$(if $(VERBOSE),@ true || ,@ )

all:: main
.PHONY: all

clean::
	$(CMD) $(RM) -r gen-ocaml
	$(CMD) $(RM) *.cmi *.cmx *.o
	$(CMD) $(RM) main
.PHONY: clean

run::
	$(MSG) echo BROKER test
	$(CMD) ./main test
.PHONY: run

OCAMLPFFTLAGS:=-I gen-ocaml -O2 -package num -package logs -package thrift -thread

gen-ocaml:: ../plant/polynomial.thrift
	$(MSG) echo THRIFT primate
	$(CMD) thrift --gen ocaml $<
	$(CMD) ocamlfind ocamlopt $(OCAMLPFFTLAGS) -c gen-ocaml/polynomial_types.mli
	$(CMD) ocamlfind ocamlopt $(OCAMLPFFTLAGS) -c gen-ocaml/polynomial_types.ml
	$(CMD) ocamlfind ocamlopt $(OCAMLPFFTLAGS) -c gen-ocaml/polynomial_consts.ml

main:: gen-ocaml main.ml broker.ml util.ml
	$(MSG) echo OCAMLOPT broker
	$(CMD) ocamlfind ocamlopt $(OCAMLPFFTLAGS) -c util.mli
	$(CMD) ocamlfind ocamlopt $(OCAMLPFFTLAGS) -c util.ml
	$(CMD) ocamlfind ocamlopt $(OCAMLPFFTLAGS) -c broker.mli
	$(CMD) ocamlfind ocamlopt $(OCAMLPFFTLAGS) -c broker.ml
	$(CMD) ocamlfind ocamlopt $(OCAMLPFFTLAGS) -c main.ml
	$(CMD) ocamlfind ocamlopt $(OCAMLPFFTLAGS) -linkpkg -o main \
	gen-ocaml/polynomial_types.cmx gen-ocaml/polynomial_consts.cmx \
	util.cmx broker.cmx main.cmx
