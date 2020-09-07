CAMLFLAGS:=
CAMLDEP:=ocamlfind ocamldep
CAMLDEPFLAGS:=$(CAMLFLAGS)
CAMLC:=ocamlfind ocamlopt
CAMLCFLAGS:=$(CAMLFLAGS) -O2 -package num,logs -thread

HIDE:=$(if $(VERBOSE),,@)
SHOW:=$(if $(VERBOSE),@ true||,@)

all:: def_sys.cmi def_sys.cmx util.cmi util.cmx
.PHONY: all

clean::
	$(SHOW) echo CLEAN .Makefile.d
	$(HIDE) $(RM) .Makefile.d
	$(SHOW) echo CLEAN
	$(HIDE) find . -type f '(' \
	-name '*.cmi' -o -name '*.cmx' -o -name '*.o' \
	')' -exec $(RM) '{}' '+'
.PHONY: clean

-include .Makefile.d

%.cmi:: %.mli .Makefile.d
	$(SHOW) echo CAMLC $<
	$(HIDE) $(CAMLC) $(CAMLCFLAGS) -c $<

%.cmx:: %.ml .Makefile.d
	$(SHOW) echo CAMLC $<
	$(HIDE) $(CAMLC) $(CAMLCFLAGS) -c $<

.Makefile.d::
	$(SHOW) echo CAMLDEP '>' $@
	$(HIDE) find . -type f '(' \
	-name '*.ml' -o -name '*.mli' \
	')' -exec $(CAMLDEP) $(CAMLDEPFLAGS) '{}' '+' > $@
