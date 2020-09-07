MKDIR:=mkdir -p
COQC:=coqc
COQFLAGS:=-Q ../fowl Maniunfold
CAMLFLAGS:=-I gen-ocaml
CAMLDEP:=ocamlfind ocamldep
CAMLDEPFLAGS:=$(CAMLFLAGS)
CAMLC:=ocamlfind ocamlopt
CAMLCFLAGS:=$(CAMLFLAGS) -O2 -package num,logs -thread

HIDE:=$(if $(VERBOSE),,@)
SHOW:=$(if $(VERBOSE),@ true||,@)

all:: adapter.cmi adapter.cmx
.PHONY: all

clean::
	$(SHOW) echo CLEAN .Makefile.d
	$(HIDE) $(RM) .Makefile.d
	$(SHOW) echo CLEAN gen-ocaml
	$(HIDE) $(RM) -r gen-ocaml
	$(SHOW) echo CLEAN
	$(HIDE) find . -type f '(' \
	-name '_Coq*' -o -name '*.aux' -o -name '*.cache' -o -name '*.glob' -o \
	-name '*.vio' -o -name '*.vo' -o -name '*.vok' -o -name '*.vos' -o \
	-name '*.cmi' -o -name '*.cmx' -o -name '*.o' \
	')' -exec $(RM) '{}' '+'
.PHONY: clean

# We do not need or even have dependency information until extraction is done.
-include .Makefile.d

%.cmi:: %.mli .Makefile.d
	$(SHOW) echo CAMLC $<
	$(HIDE) $(CAMLC) $(CAMLCFLAGS) -c $<

%.cmx:: %.ml .Makefile.d
	$(SHOW) echo CAMLC $<
	$(HIDE) $(CAMLC) $(CAMLCFLAGS) -c $<

# We must duplicate these rules if we do not wish to play around with `VPATH`.
gen-ocaml/%.cmi:: gen-ocaml/%.mli .Makefile.d
	$(SHOW) echo CAMLC $<
	$(HIDE) $(CAMLC) $(CAMLCFLAGS) -c $<

gen-ocaml/%.cmx:: gen-ocaml/%.ml .Makefile.d
	$(SHOW) echo CAMLC $<
	$(HIDE) $(CAMLC) $(CAMLCFLAGS) -c $<

# We use dependency information as the target of this rule,
# because otherwise subsequent rules that write files into the directory
# would trigger this rule again.
.Makefile.d:: Extraction.v ../fowl
	$(SHOW) echo COQC $<
	$(HIDE) $(MKDIR) gen-ocaml
	$(HIDE) $(COQC) $(COQFLAGS) $<
	$(SHOW) echo CAMLDEP '>' $@
	$(HIDE) find . -type f '(' \
	-name '*.ml' -o -name '*.mli' \
	')' -exec $(CAMLDEP) $(CAMLDEPFLAGS) '{}' '+' > $@
