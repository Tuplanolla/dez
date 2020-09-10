HIDE:=$(if $(VERBOSE),,@)
SHOW:=$(if $(VERBOSE),@ true||,@)

THRIFT:=thrift
CAMLFLAGS:=-I gen-ocaml -I ../ungulate -I ../camel -I ../camel/gen-ocaml
CAMLDEP:=ocamlfind ocamldep
CAMLDEPFLAGS:=$(CAMLFLAGS) -native
CAMLC:=ocamlfind ocamlopt
CAMLCFLAGS:=$(CAMLFLAGS) -O2 -package num,logs,thrift -thread

MLFILES:=$(shell cat _MLFiles 2> /dev/null || echo _MLFiles)
MLIFILES:=$(shell cat _MLIFiles 2> /dev/null || echo _MLIFiles)

all :: main
	$(SHOW) echo STAT $^
.PHONY : all

clean ::
	$(SHOW) echo CLEAN MAKE
	$(HIDE) $(RM) .Makefile.d _MLFiles _MLIFiles
	$(SHOW) echo CLEAN CAML
	$(HIDE) $(RM) main
	$(HIDE) $(RM) -r gen-ocaml
	$(HIDE) find . -type f '(' \
	-name '*.cmi' -o -name '*.cmo' -o -name '*.cmx' -o -name '*.o' -o \
	-false ')' -exec $(RM) '{}' '+'
.PHONY : clean

run :: main
	$(SHOW) echo RUN $<
	$(HIDE) ./$<
.PHONY : run

MLPATTERN:=\<\([^[:space:]]\+\)\.ml\>

main :: $(MLFILES:.ml=.cmx) $(MLIFILES:.mli=.cmi)
	$(SHOW) echo CAMLC -o $@
	$(HIDE) { cat _MLFiles ; \
	sed 's|$(MLPATTERN)|../ungulate/\1.ml|g' ../ungulate/_MLFiles ; \
	sed 's|$(MLPATTERN)|../camel/\1.ml|g' ../camel/_MLFiles ; } | \
	xargs $(CAMLDEP) $(CAMLDEPFLAGS) -sort | \
	sed 's|$(MLPATTERN)|\1.cmx|g' | \
	xargs $(CAMLC) $(CAMLCFLAGS) -linkpkg -o $@

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

_MLFiles _MLIFiles &:: ../flower/gen.idl
	$(SHOW) echo THRIFT $<
	$(HIDE) $(THRIFT) --gen ocaml -r $<
	$(SHOW) echo MAKE _MLFiles _MLIFiles
	$(HIDE) echo *.ml gen-ocaml/*.ml > _MLFiles
	$(HIDE) echo *.mli gen-ocaml/*.mli > _MLIFiles

# We do not have dependency information until code generation is done.
-include .Makefile.d
