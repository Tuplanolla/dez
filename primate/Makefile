CMD:=$(if $(VERBOSE),,@ )
MSG:=$(if $(VERBOSE),@ true || ,@ )

all:: main
	$(MSG) echo BROKER test
	$(CMD) ./main test
.PHONY: all

clean::
	$(CMD) $(RM) -r gen-ocaml
	$(CMD) $(RM) *.cmi *.cmx *.o
	$(CMD) $(RM) main
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

main:: gen-ocaml broker.ml
	$(MSG) echo OCAMLOPT broker
	$(CMD) ocamlfind ocamlopt -I gen-ocaml -O2 -c \
	-package num -package thrift -thread util.mli
	$(CMD) ocamlfind ocamlopt -I gen-ocaml -O2 -c \
	-package num -package thrift -thread util.ml
	$(CMD) ocamlfind ocamlopt -I gen-ocaml -O2 -c \
	-package num -package thrift -thread broker.ml
	$(CMD) ocamlfind ocamlopt -I gen-ocaml -O2 -c \
	-package num -package thrift -thread main.ml
	$(CMD) ocamlfind ocamlopt -I gen-ocaml -O2 -linkpkg -o main \
	-package num -package thrift -thread \
	gen-ocaml/polynomial_types.cmx gen-ocaml/polynomial_consts.cmx \
	util.cmx broker.cmx main.cmx
