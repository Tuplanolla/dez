CMD:=$(if $(VERBOSE),,@ )
MSG:=$(if $(VERBOSE),@ true || ,@ )

all:: broker
	$(MSG) echo BROKER test
	@ ./broker test
.PHONY: all

clean::
	$(CMD) $(RM) gen-ocaml
	$(CMD) $(RM) *.cmi *.cmx *.o
	$(CMD) $(RM) broker
.PHONY: clean

gen-ocaml:: ../plant/messages.thrift
	$(MSG) echo THRIFT primate
	$(CMD) thrift --gen ocaml $<

main::
	$(MSG) echo OCAMLOPT broker
	$(CMD) ocamlfind ocamlopt -O2 -c -package num broker.ml
	$(CMD) ocamlfind ocamlopt -O2 -linkpkg -o broker -package num \
	broker.cmx
