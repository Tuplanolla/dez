HIDE:=$(if $(VERBOSE),,@)
SHOW:=$(if $(VERBOSE),@ true||,@)

CAMLFLAGS:=-I gen-ocaml -I ../ungulate -I ../camel -I ../camel/gen-ocaml
CAMLDEP:=ocamlfind ocamldep
CAMLDEPFLAGS:=$(CAMLFLAGS)
CAMLC:=ocamlfind ocamlopt
CAMLCFLAGS:=$(CAMLFLAGS) -O2 -package num,logs,thrift -thread

all:: main
.PHONY: all

clean::
	$(SHOW) echo CLEAN gen-ocaml
	$(HIDE) $(RM) -r gen-ocaml
	$(SHOW) echo CLEAN CAML
	$(HIDE) find . -type f '(' \
	-name '*.cmi' -o -name '*.cmo' -o -name '*.cmx' -o -name '*.cmxa' -o \
	-name '*.o' \
	')' -exec $(RM) '{}' '+'
	$(HIDE) $(RM) main
.PHONY: clean

run::
	$(SHOW) echo RUN main
	$(HIDE) ./main
.PHONY: run

# TODO What should we do with this mess?
main:: .main.d main.cmx
	$(SHOW) echo CAMLC -o $@
	$(HIDE) cat .main.d | xargs $(CAMLC) $(CAMLCFLAGS) -linkpkg -o $@

.main.d:: .Makefile.d
	$(SHOW) echo CAMLDEP '>' $@
	$(HIDE) { find . -maxdepth 1 -type f -name '*.ml' && \
	find gen-ocaml ../ungulate ../camel -type f -name '*.cmx' | \
	sed 's/\.cmx/.ml/g' ; } | \
	xargs $(CAMLDEP) $(CAMLDEPFLAGS) -sort | \
	sed 's/\.ml/.cmx/g' > $@

%.cmi:: %.mli .Makefile.d
	$(SHOW) echo CAMLC $<
	$(HIDE) $(CAMLC) $(CAMLCFLAGS) -c -o $@ $<

%.cmx:: %.ml .Makefile.d
	$(SHOW) echo CAMLC $<
	$(HIDE) $(CAMLC) $(CAMLCFLAGS) -c -o $@ $<

# We must duplicate these rules if we do not wish to mess around with `VPATH`.
gen-ocaml/%.cmi:: gen-ocaml/%.mli .Makefile.d
	$(SHOW) echo CAMLC $<
	$(HIDE) $(CAMLC) $(CAMLCFLAGS) -c -o $@ $<

gen-ocaml/%.cmx:: gen-ocaml/%.ml .Makefile.d
	$(SHOW) echo CAMLC $<
	$(HIDE) $(CAMLC) $(CAMLCFLAGS) -c -o $@ $<

# We use dependency information as the target of this rule,
# because otherwise subsequent rules that write files into the source directory
# would trigger this rule again.
.Makefile.d::
	$(SHOW) echo THRIFT ../flower/main.idl
	$(HIDE) thrift --gen ocaml -r ../flower/main.idl
	$(SHOW) echo CAMLDEP '>' $@
	$(HIDE) find . -type f '(' \
	-name '*.ml' -o -name '*.mli' \
	')' -exec $(CAMLDEP) $(CAMLDEPFLAGS) '{}' '+' > $@

# .Makefile.d.prereq:: ../flower
# .main.d.prereq:: ../ungulate ../camel

-include .Makefile.d
