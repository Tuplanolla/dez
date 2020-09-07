MKDIR:=mkdir -p
COQC:=coqc
COQFLAGS:=-Q ../fowl Maniunfold
CAMLFLAGS:=-I gen-ocaml
CAMLDEP:=ocamlfind ocamldep
CAMLDEPFLAGS:=$(CAMLFLAGS)
CAMLC:=ocamlfind ocamlopt
CAMLCFLAGS:=$(CAMLFLAGS) -O2 -thread -package num,logs

HIDE:=$(if $(VERBOSE),,@)
SHOW:=$(if $(VERBOSE),@ true||,@)

# TODO There is a conflict saying
# `The files ~/.opam/default/lib/ocaml/big_int.cmi and gen-ocaml/Nat.cmi
# make inconsistent assumptions over interface Nat`
# and also this file sucks.

all:: .Makefile.d adapter.cmi adapter.cmx
.PHONY: all

clean::
	$(SHOW) echo CLEAN gen-ocaml
	$(HIDE) $(RM) -r gen-ocaml
	$(HIDE) find . -type f '(' \
	-name '_Coq*' -o -name '*.aux' -o -name '*.cache' -o -name '*.glob' -o \
	-name '*.vio' -o -name '*.vo' -o -name '*.vok' -o -name '*.vos' -o \
	-name '*.cmi' -o -name '*.cmx' -o -name '*.o' \
	')' -exec $(RM) '{}' '+'
.PHONY: clean

%.cmi:: %.mli .Makefile.d
	$(SHOW) echo CAMLC -o $@
	$(HIDE) $(CAMLC) $(CAMLCFLAGS) -c $<

%.cmx:: %.ml .Makefile.d
	$(SHOW) echo CAMLC -o $@
	$(HIDE) $(CAMLC) $(CAMLCFLAGS) -c $<

gen-ocaml/%.cmi:: gen-ocaml/%.mli .Makefile.d
	$(SHOW) echo CAMLC -o $@
	$(HIDE) $(CAMLC) $(CAMLCFLAGS) -c $<

gen-ocaml/%.cmx:: gen-ocaml/%.ml .Makefile.d
	$(SHOW) echo CAMLC -o $@
	$(HIDE) $(CAMLC) $(CAMLCFLAGS) -c $<

gen-ocaml:: Extraction.v
	$(SHOW) echo COQC $<
	$(HIDE) $(MKDIR) gen-ocaml
	$(HIDE) $(COQC) $(COQFLAGS) Extraction.v

# We automatically generate dependencies between components here.
.Makefile.d:: gen-ocaml
	$(SHOW) echo CAMLDEP '>' $@
	$(HIDE) find . -type f '(' \
	-name '*.ml' -o -name '*.mli' \
	')' -exec $(CAMLDEP) $(CAMLDEPFLAGS) '{}' '+' > $@

include .Makefile.d
