HIDE:=$(if $(VERBOSE),,@)
SHOW:=$(if $(VERBOSE),@ true||,@)

CAMLFLAGS:=
CAMLDEP:=ocamlfind ocamldep
CAMLDEPFLAGS:=$(CAMLFLAGS) -native
CAMLC:=ocamlfind ocamlopt
CAMLCFLAGS:=$(CAMLFLAGS) -O2 -package logs -thread

MLFILES:=$(shell cat _MLFiles 2> /dev/null || echo _MLFiles)
MLIFILES:=$(shell cat _MLIFiles 2> /dev/null || echo _MLIFiles)

all :: $(MLFILES:.ml=.cmx) $(MLIFILES:.mli=.cmi)
	$(SHOW) echo STAT $^
.PHONY : all

clean ::
	$(SHOW) echo CLEAN MAKE
	$(HIDE) $(RM) .Makefile.d _MLFiles _MLIFiles
	$(SHOW) echo CLEAN CAML
	$(HIDE) find . -type f '(' \
	-name '*.cmi' -o -name '*.cmo' -o -name '*.cmx' -o -name '*.o' -o \
	-false ')' -exec $(RM) '{}' '+'
.PHONY : clean

# This rule is for `ocamlc` and `ocamlopt`.
%.cmi :: %.mli .Makefile.d
	$(SHOW) echo CAMLC $<
	$(HIDE) $(CAMLC) $(CAMLCFLAGS) -c $<

# This rule is for `ocamlc`.
%.cmo :: %.ml .Makefile.d
	$(SHOW) echo CAMLC $<
	$(HIDE) $(CAMLC) $(CAMLCFLAGS) -c $<

# This rule is for `ocamlopt`.
%.cmx %.o :: %.ml .Makefile.d
	$(SHOW) echo CAMLC $<
	$(HIDE) $(CAMLC) $(CAMLCFLAGS) -c $<

# We need this rule to keep track of the included dependencies.
Makefile :: .Makefile.d
	$(SHOW) echo MAKE $@

.Makefile.d :: _MLFiles _MLIFiles
	$(SHOW) echo CAMLDEP -o $@
	$(HIDE) cat $^ | xargs $(CAMLDEP) $(CAMLDEPFLAGS) > $@

_MLFiles :: *.ml
	$(SHOW) echo MAKE _MLFiles
	$(HIDE) echo *.ml > _MLFiles

_MLIFiles :: *.mli
	$(SHOW) echo MAKE _MLIFiles
	$(HIDE) echo *.mli > _MLIFiles

# We always have dependency information.
-include .Makefile.d
