CMD:=$(if $(VERBOSE),,@ )
MSG:=$(if $(VERBOSE),@ true || ,@ )

gen-ocaml:: ../plant/polynomial.thrift
	$(MSG) echo THRIFT fur
	$(CMD) thrift --gen ocaml $<

clean::
	$(CMD) $(RM) -r gen-ocaml
	$(CMD) $(RM) *.cmi *.cmx *.o
	$(CMD) $(RM) broker
.PHONY: clean

server_proxy:: gen-ocaml
	$(MSG) echo OCAMLOPT fur
	$(CMD) ocamlfind ocamlopt -I ../ungulate -O2 -c -package num server_proxy.ml
	$(CMD) ocamlfind ocamlopt -I ../ungulate -O2 -linkpkg -o server_proxy -package num \
	extraction.cmx adapter.cmx server_proxy.cmx
