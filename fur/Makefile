CMD:=$(if $(VERBOSE),,@ )
MSG:=$(if $(VERBOSE),@ true || ,@ )

OCAMLPFFTLAGS:=-I gen-ocaml -I ../ungulate -I ../primate -O2 \
-package num -package logs -package thrift -thread

main:: gen-ocaml main.ml server_proxy.ml
	$(MSG) echo OCAMLOPT server_proxy
	$(CMD) ocamlfind ocamlopt $(OCAMLPFFTLAGS) -c ../primate/util.mli
	$(CMD) ocamlfind ocamlopt $(OCAMLPFFTLAGS) -c ../primate/util.ml
	# TODO Common package for utilities.
	$(CMD) ocamlfind ocamlopt $(OCAMLPFFTLAGS) -c ../primate/def_sys.mli
	$(CMD) ocamlfind ocamlopt $(OCAMLPFFTLAGS) -c ../primate/def_sys.ml
	$(CMD) ocamlfind ocamlopt $(OCAMLPFFTLAGS) -c server_proxy.mli
	$(CMD) ocamlfind ocamlopt $(OCAMLPFFTLAGS) -c server_proxy.ml
	$(CMD) ocamlfind ocamlopt $(OCAMLPFFTLAGS) -c main.ml
	$(CMD) ocamlfind ocamlopt $(OCAMLPFFTLAGS) -linkpkg -o main \
	gen-ocaml/component_types.cmx gen-ocaml/component_consts.cmx \
	gen-ocaml/polynomial_types.cmx gen-ocaml/polynomial_consts.cmx \
	../ungulate/extraction.cmx ../ungulate/adapter.cmx \
	def_sys.cmx util.cmx server_proxy.cmx main.cmx

gen-ocaml:: ../plant/main.thrift
	$(MSG) echo THRIFT $<
	$(CMD) thrift --gen ocaml -r $<
	$(CMD) ocamlfind ocamlopt $(OCAMLPFFTLAGS) -c gen-ocaml/component_types.mli
	$(CMD) ocamlfind ocamlopt $(OCAMLPFFTLAGS) -c gen-ocaml/component_types.ml
	$(CMD) ocamlfind ocamlopt $(OCAMLPFFTLAGS) -c gen-ocaml/component_consts.ml
	$(CMD) ocamlfind ocamlopt $(OCAMLPFFTLAGS) -c gen-ocaml/polynomial_types.mli
	$(CMD) ocamlfind ocamlopt $(OCAMLPFFTLAGS) -c gen-ocaml/polynomial_types.ml
	$(CMD) ocamlfind ocamlopt $(OCAMLPFFTLAGS) -c gen-ocaml/polynomial_consts.ml

clean::
	$(CMD) $(RM) -r gen-ocaml
	$(CMD) $(RM) *.cmi *.cmx *.o
	$(CMD) $(RM) main
.PHONY: clean

run::
	$(MSG) echo FUR test
	$(CMD) ./main test
.PHONY: run
