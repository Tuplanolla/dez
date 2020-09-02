CMD:=$(if $(VERBOSE),,@ )
MSG:=$(if $(VERBOSE),@ true || ,@ )

OCAMLPFFTLAGS:=-I gen-ocaml -O2 \
-package num -package logs -package thrift -thread

build:: main
.PHONY: build

clean::
	$(CMD) $(RM) -r gen-ocaml
	$(CMD) $(RM) *.cmi *.cmx *.o
	$(CMD) $(RM) main
.PHONY: clean

run::
	$(MSG) echo BROKER test
	$(CMD) ./main test
.PHONY: run

main:: gen-ocaml main.ml broker.ml util.ml
	$(MSG) echo OCAMLOPT broker
	$(CMD) ocamlfind ocamlopt $(OCAMLPFFTLAGS) -c util.mli
	$(CMD) ocamlfind ocamlopt $(OCAMLPFFTLAGS) -c util.ml
	$(CMD) ocamlfind ocamlopt $(OCAMLPFFTLAGS) -c def_sys.mli
	$(CMD) ocamlfind ocamlopt $(OCAMLPFFTLAGS) -c def_sys.ml
	$(CMD) ocamlfind ocamlopt $(OCAMLPFFTLAGS) -c broker.mli
	$(CMD) ocamlfind ocamlopt $(OCAMLPFFTLAGS) -c broker.ml
	$(CMD) ocamlfind ocamlopt $(OCAMLPFFTLAGS) -c main.ml
	$(CMD) ocamlfind ocamlopt $(OCAMLPFFTLAGS) -linkpkg -o main \
	gen-ocaml/component_types.cmx gen-ocaml/component_consts.cmx \
	gen-ocaml/polynomial_types.cmx gen-ocaml/polynomial_consts.cmx \
	def_sys.cmx util.cmx broker.cmx main.cmx

gen-ocaml:: ../flower/main.thrift
	$(MSG) echo THRIFT $<
	$(CMD) thrift --gen ocaml -r $<
	$(CMD) ocamlfind ocamlopt $(OCAMLPFFTLAGS) -c gen-ocaml/component_types.mli
	$(CMD) ocamlfind ocamlopt $(OCAMLPFFTLAGS) -c gen-ocaml/component_types.ml
	$(CMD) ocamlfind ocamlopt $(OCAMLPFFTLAGS) -c gen-ocaml/component_consts.ml
	$(CMD) ocamlfind ocamlopt $(OCAMLPFFTLAGS) -c gen-ocaml/polynomial_types.mli
	$(CMD) ocamlfind ocamlopt $(OCAMLPFFTLAGS) -c gen-ocaml/polynomial_types.ml
	$(CMD) ocamlfind ocamlopt $(OCAMLPFFTLAGS) -c gen-ocaml/polynomial_consts.ml
