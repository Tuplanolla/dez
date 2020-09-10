HIDE:=$(if $(VERBOSE),,@)
SHOW:=$(if $(VERBOSE),@ true||,@)

CAMLFLAGS:=-I gen-ocaml -I ../ungulate -I ../camel -I ../camel/gen-ocaml
CAMLDEP:=ocamlfind ocamldep
CAMLDEPFLAGS:=$(CAMLFLAGS) -native
CAMLC:=ocamlfind ocamlopt
CAMLCFLAGS:=$(CAMLFLAGS) -O2 -package num,logs,thrift -thread
THRIFT:=thrift

all :: main
	$(SHOW) echo STAT $^
.PHONY : all

clean ::
	$(SHOW) echo CLEAN .Makefile.d
	$(HIDE) $(RM) .Makefile.d
	$(SHOW) echo CLEAN gen-ocaml
	$(HIDE) $(RM) -r gen-ocaml
	$(SHOW) echo CLEAN CAML
	$(HIDE) $(RM) main
	$(HIDE) find . -type f '(' \
	-name '*.cmi' -o -name '*.cmo' -o -name '*.cmx' -o -name '*.o' -o \
	-false ')' -exec $(RM) '{}' '+'
.PHONY : clean

run :: main
	$(SHOW) echo RUN $<
	$(HIDE) ./$<
.PHONY : run

# TODO What should we do with this mess? Follow the `camel`!
main :: .main.d main.cmx
	$(SHOW) echo CAMLC -o $@
	$(HIDE) cat .main.d | xargs $(CAMLC) $(CAMLCFLAGS) -linkpkg -o $@

.main.d :: .Makefile.d
	$(SHOW) echo CAMLDEP -o $@
	$(HIDE) { find . -maxdepth 1 -type f -name '*.ml' && \
	find gen-ocaml ../ungulate ../camel -type f -name '*.cmx' | \
	sed 's/\.cmx/.ml/g' ; } | \
	xargs $(CAMLDEP) $(CAMLDEPFLAGS) -sort | \
	sed 's/\.ml/.cmx/g' > $@

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

.Makefile.d :: ../flower/gen.idl
	$(SHOW) echo THRIFT $<
	$(HIDE) $(THRIFT) --gen ocaml -r $<
	$(SHOW) echo CAMLDEP -o $@
	$(HIDE) $(CAMLDEP) $(CAMLDEPFLAGS) *.ml *.mli \
	gen-ocaml/*.ml gen-ocaml/*.mli > $@

# We do not have dependency information until code generation is done.
-include .Makefile.d
