HIDE:=$(if $(VERBOSE),,@)
SHOW:=$(if $(VERBOSE),@ true||,@)

# TODO This.

OCAMLPFFTLAGS:=-I gen-ocaml -I ../ungulate -O2 \
-package num,logs,thrift -thread

all:: main
.PHONY: all

clean::
	$(HIDE) $(RM) -r gen-ocaml
	$(HIDE) $(RM) *.cmi *.cmx *.o
	$(HIDE) $(RM) main
.PHONY: clean

run::
	$(SHOW) echo RUN main
	$(HIDE) ./main
.PHONY: run

main:: gen-ocaml main.ml broker.ml
	$(SHOW) echo OCAMLOPT broker
	$(HIDE) ocamlfind ocamlopt $(OCAMLPFFTLAGS) -c broker.mli
	$(HIDE) ocamlfind ocamlopt $(OCAMLPFFTLAGS) -c broker.ml
	$(HIDE) ocamlfind ocamlopt $(OCAMLPFFTLAGS) -c main.ml
	$(HIDE) ocamlfind ocamlopt $(OCAMLPFFTLAGS) -linkpkg -o main \
	gen-ocaml/component_types.cmx gen-ocaml/component_consts.cmx \
	gen-ocaml/polynomial_types.cmx gen-ocaml/polynomial_consts.cmx \
	def_sys.cmx util.cmx broker.cmx main.cmx

gen-ocaml:: ../flower/main.idl
	$(SHOW) echo THRIFT $<
	$(HIDE) thrift --gen ocaml -r $<
	$(HIDE) ocamlfind ocamlopt $(OCAMLPFFTLAGS) -c gen-ocaml/component_types.mli
	$(HIDE) ocamlfind ocamlopt $(OCAMLPFFTLAGS) -c gen-ocaml/component_types.ml
	$(HIDE) ocamlfind ocamlopt $(OCAMLPFFTLAGS) -c gen-ocaml/component_consts.ml
	$(HIDE) ocamlfind ocamlopt $(OCAMLPFFTLAGS) -c gen-ocaml/polynomial_types.mli
	$(HIDE) ocamlfind ocamlopt $(OCAMLPFFTLAGS) -c gen-ocaml/polynomial_types.ml
	$(HIDE) ocamlfind ocamlopt $(OCAMLPFFTLAGS) -c gen-ocaml/polynomial_consts.ml

# prereq:: ungulate
