CMD:=$(if $(VERBOSE),,@ )
MSG:=$(if $(VERBOSE),@ true || ,@ )

all:: broker
	$(MSG) echo BROKER test
	$(CMD) ./broker test
.PHONY: all

clean::
	$(CMD) $(RM) gen-ocaml
	$(CMD) $(RM) *.cmi *.cmx *.o
	$(CMD) $(RM) broker
.PHONY: clean

gen-ocaml:: ../plant/polynomial.thrift
	$(MSG) echo THRIFT primate
	$(CMD) thrift --gen ocaml $<
	$(CMD) ocamlfind ocamlopt -I gen-ocaml -O2 -c \
	-package num -package thrift -thread gen-ocaml/polynomial_types.mli
	$(CMD) ocamlfind ocamlopt -I gen-ocaml -O2 -c \
	-package num -package thrift -thread gen-ocaml/polynomial_types.ml
	$(CMD) ocamlfind ocamlopt -I gen-ocaml -O2 -c \
	-package num -package thrift -thread gen-ocaml/polynomial_consts.ml

broker:: gen-ocaml broker.ml
	$(MSG) echo OCAMLOPT broker
	$(CMD) ocamlfind ocamlopt -I gen-ocaml -O2 -c \
	-package num -package thrift -thread broker.ml
	$(CMD) ocamlfind ocamlopt -I gen-ocaml -O2 -c \
	-package num -package thrift -thread main.ml
	$(CMD) ocamlfind ocamlopt -I gen-ocaml -O2 -linkpkg -o broker \
	-package num -package thrift -thread \
	gen-ocaml/polynomial_types.cmx gen-ocaml/polynomial_consts.cmx \
	broker.cmx main.cmx
