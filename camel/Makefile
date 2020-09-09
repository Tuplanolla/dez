HIDE:=$(if $(VERBOSE),,@)
SHOW:=$(if $(VERBOSE),@ true||,@)

MKDIR:=mkdir -p
COQC:=coqc
COQFLAGS:=-Q ../fowl Maniunfold
CAMLFLAGS:=-I gen-ocaml
CAMLDEP:=ocamlfind ocamldep
CAMLDEPFLAGS:=$(CAMLFLAGS) -native
CAMLC:=ocamlfind ocamlopt
CAMLCFLAGS:=$(CAMLFLAGS) -O2 -package num,logs -thread

TARGETS:=adapter.cm

all :: $(TARGETS:.cm=.cmi) $(TARGETS:.cm=.cmx)
	$(SHOW) echo STAT $^
.PHONY: all

clean ::
	$(SHOW) echo CLEAN .Makefile.d
	$(HIDE) $(RM) .Makefile.d
	$(SHOW) echo CLEAN gen-ocaml
	$(HIDE) $(RM) -r gen-ocaml
	$(SHOW) echo CLEAN COQ
	$(HIDE) find . -type f '(' \
	-name '_Coq*' -o -name '*.aux' -o -name '*.cache' -o -name '*.glob' -o \
	-name '*.vio' -o -name '*.vo' -o -name '*.vok' -o -name '*.vos' -o \
	-false ')' -exec $(RM) '{}' '+'
	$(SHOW) echo CLEAN CAML
	$(HIDE) find . -type f '(' \
	-name '*.cmi' -o -name '*.cmo' -o -name '*.cmx' -o -name '*.o' -o \
	-false ')' -exec $(RM) '{}' '+'
.PHONY: clean

# We use this variable to avoid having to duplicate
# the following rules for `gen-ocaml`.
VPATH:=.:gen-ocaml

%.cmi :: %.mli .Makefile.d
	$(SHOW) echo CAMLC $<
	$(HIDE) $(CAMLC) $(CAMLCFLAGS) -c $<

%.cmo :: %.ml .Makefile.d
	$(SHOW) echo CAMLC $<
	$(HIDE) $(CAMLC) $(CAMLCFLAGS) -c $<

%.cmx %.o :: %.ml .Makefile.d
	$(SHOW) echo CAMLC $<
	$(HIDE) $(CAMLC) $(CAMLCFLAGS) -c $<

Makefile :: .Makefile.d
	$(SHOW) echo MAKE $@

# We use `.Makefile.d` instead of `gen-ocaml` as the target of this rule,
# because otherwise subsequent rules that write files into `gen-ocaml`
# would trigger this rule again.
.Makefile.d :: Extraction.v
	$(SHOW) echo COQC $<
	$(HIDE) $(MKDIR) gen-ocaml
	$(HIDE) $(COQC) $(COQFLAGS) $<
	$(SHOW) echo CAMLDEP -o $@
	$(HIDE) $(CAMLDEP) $(CAMLDEPFLAGS) *.ml *.mli \
	gen-ocaml/*.ml gen-ocaml/*.mli > $@

# We do not have dependency information until code extraction is done.
-include .Makefile.d
