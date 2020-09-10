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

MLFILES:=$(shell cat _MLFiles 2> /dev/null || echo _MLFiles)
MLIFILES:=$(shell cat _MLIFiles 2> /dev/null || echo _MLIFiles)

all :: $(MLFILES:.ml=.cmx) $(MLIFILES:.mli=.cmi)
	$(SHOW) echo STAT $^
.PHONY : all

clean ::
	$(SHOW) echo CLEAN .Makefile.d
	$(HIDE) $(RM) .Makefile.d
	$(SHOW) echo CLEAN _MLFiles _MLIFiles
	$(HIDE) $(RM) _MLFiles _MLIFiles
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
.PHONY : clean

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

.Makefile.d :: _MLFiles _MLIFiles
	$(SHOW) echo CAMLDEP -o $@
	$(HIDE) cat $^ | xargs $(CAMLDEP) $(CAMLDEPFLAGS) > $@

# We use `_MLFiles` and `_MLIFiles` as the target of this rule for two reasons.
# First, if we used `gen-ocaml` as the target,
# subsequent rules that compile any dependencies would trigger this rule again,
# resulting in an infinite loop.
# Second, if we used `.Makefile.d` as the target,
# subsequent rules would only compile transitive dependencies of `$(TARGETS)`,
# resulting in a partial result.
_MLFiles _MLIFiles &:: Extraction.v
	$(SHOW) echo COQC $<
	$(HIDE) $(MKDIR) gen-ocaml
	$(HIDE) $(COQC) $(COQFLAGS) $<
	$(SHOW) echo MAKE _MLFiles _MLIFiles
	$(HIDE) echo *.ml gen-ocaml/*.ml > _MLFiles
	$(HIDE) echo *.mli gen-ocaml/*.mli > _MLIFiles

# We do not have dependency information until code extraction is done.
-include .Makefile.d
