CMD:=$(if $(VERBOSE),,@ )
MSG:=$(if $(VERBOSE),@ true || ,@ )

gen-ocaml:: ../plant/messages.thrift
	$(MSG) echo THRIFT fur
	$(CMD) thrift --gen ocaml $<

clean::
	$(CMD) $(RM) gen-ocaml
	$(CMD) $(RM) *.cmi *.cmx *.o
	$(CMD) $(RM) broker
.PHONY: clean

server-proxy::
	$(MSG) echo OCAMLOPT fur
	$(CMD) ocamlfind ocamlopt -I ../ungulate -O2 -c -package num server-proxy.ml
	$(CMD) ocamlfind ocamlopt -I ../ungulate -O2 -linkpkg -o server-proxy -package num \
	extraction.cmx adapter.cmx server-proxy.cmx
