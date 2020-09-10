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

MLFILES:=$(shell cat _MLFiles 2> /dev/null || echo _MLFiles)
MLIFILES:=$(shell cat _MLIFiles 2> /dev/null || echo _MLIFiles)

# We use this special variable to avoid having to duplicate some of the rules.
VPATH:=.:gen-ocaml

all :: $(MLFILES:.ml=.cmx) $(MLIFILES:.mli=.cmi)
	$(SHOW) echo STAT $^
.PHONY : all

clean ::
	$(SHOW) echo CLEAN MAKE
	$(HIDE) $(RM) .Makefile.d _MLFiles _MLIFiles
	$(SHOW) echo CLEAN COQ
	$(HIDE) find . -type f '(' \
	-name '_Coq*' -o -name '*.aux' -o -name '*.cache' -o -name '*.glob' -o \
	-name '*.vio' -o -name '*.vo' -o -name '*.vok' -o -name '*.vos' -o \
	-false ')' -exec $(RM) '{}' '+'
	$(SHOW) echo CLEAN CAML
	$(HIDE) $(RM) -r gen-ocaml
	$(HIDE) find . -type f '(' \
	-name '*.cmi' -o -name '*.cmo' -o -name '*.cmx' -o -name '*.o' -o \
	-false ')' -exec $(RM) '{}' '+'
.PHONY : clean

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
# First, if we used the `gen-ocaml` directory as the target,
# subsequent rules that compile any files within the directory
# would trigger this rule again,
# leading to an infinite loop.
# Second, if we used `.Makefile.d` as the target,
# subsequent rules that compile files
# would only consider the transitive dependencies of our targets,
# leading to an incomplete result.
_MLFiles _MLIFiles &:: Extraction.v
	$(SHOW) echo COQC $<
	$(HIDE) $(MKDIR) gen-ocaml
	$(HIDE) $(COQC) $(COQFLAGS) $<
	$(SHOW) echo MAKE _MLFiles _MLIFiles
	$(HIDE) echo *.ml gen-ocaml/*.ml > _MLFiles
	$(HIDE) echo *.mli gen-ocaml/*.mli > _MLIFiles

# We do not have dependency information until code extraction is done.
-include .Makefile.d
