HIDE:=$(if $(VERBOSE),,@)
SHOW:=$(if $(VERBOSE),@ true||,@)

CAMLFLAGS:=
CAMLDEP:=ocamlfind ocamldep
CAMLDEPFLAGS:=$(CAMLFLAGS) -native
CAMLC:=ocamlfind ocamlopt
CAMLCFLAGS:=$(CAMLFLAGS) -O2 -package logs -thread

TARGETS:=$(shell find . -maxdepth 1 -type f '(' \
-name '*.ml' -o -name '*.mli' -o \
-false ')')

all :: $(TARGETS:.ml=.cmx) $(TARGETS:.mli=.cmi)
	$(SHOW) echo STAT $^
.PHONY : all

clean ::
	$(SHOW) echo CLEAN .Makefile.d
	$(HIDE) $(RM) .Makefile.d
	$(SHOW) echo CLEAN CAML
	$(HIDE) find . -type f '(' \
	-name '*.cmi' -o -name '*.cmo' -o -name '*.cmx' -o -name '*.o' -o \
	-false ')' -exec $(RM) '{}' '+'
.PHONY : clean

# We use this rule with `ocamlc` and `ocamlopt`.
%.cmi :: %.mli .Makefile.d
	$(SHOW) echo CAMLC $<
	$(HIDE) $(CAMLC) $(CAMLCFLAGS) -c $<

# We use this rule with `ocamlc`.
%.cmo :: %.ml .Makefile.d
	$(SHOW) echo CAMLC $<
	$(HIDE) $(CAMLC) $(CAMLCFLAGS) -c $<

# We use this rule with `ocamlopt`.
%.cmx %.o :: %.ml .Makefile.d
	$(SHOW) echo CAMLC $<
	$(HIDE) $(CAMLC) $(CAMLCFLAGS) -c $<

# We need this rule to keep track of the included dependencies.
Makefile :: .Makefile.d
	$(SHOW) echo MAKE $@

# We would like to automatically find
# all the transitive dependencies of `*.ml` and `*.mli`,
# but there is currently no simple way to do that,
# so we make do with this rule.
.Makefile.d :: $(TARGETS)
	$(SHOW) echo CAMLDEP -o $@
	$(HIDE) $(CAMLDEP) $(CAMLDEPFLAGS) $(TARGETS) > $@

# We always have dependency information.
-include .Makefile.d
