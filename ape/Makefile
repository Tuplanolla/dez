HIDE:=$(if $(VERBOSE),,@)
SHOW:=$(if $(VERBOSE),@ true||,@)

THRIFT:=thrift
CAMLFLAGS:=-I gen-ocaml -I ../ungulate
CAMLDEP:=ocamlfind ocamldep
CAMLDEPFLAGS:=$(CAMLFLAGS) -native
CAMLC:=ocamlfind ocamlopt
CAMLCFLAGS:=$(CAMLFLAGS) -O2 -package logs,thrift -thread

IDLPATTERN:=\<\([^[:space:]]\+\)\.idl\>
MLPATTERN:=\<\([^[:space:]]\+\)\.ml\>

MLFILES:=$(shell cat _MLFiles 2> /dev/null)
MLIFILES:=$(shell cat _MLIFiles 2> /dev/null)

VPATH:=.:gen-ocaml

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

main :: $(MLFILES:.ml=.cmx) $(MLIFILES:.mli=.cmi)
	$(SHOW) echo CAMLC -o $@
	$(HIDE) { cat _MLFiles ; \
	sed 's#$(MLPATTERN)#../ungulate/\1.ml#g' ../ungulate/_MLFiles ; \
	} | xargs $(CAMLDEP) $(CAMLDEPFLAGS) -sort | \
	sed 's#$(MLPATTERN)#\1.cmx#g' | \
	xargs $(CAMLC) $(CAMLCFLAGS) -linkpkg -o $@

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

_MLFiles _MLIFiles &:: ../flower/_IDLFiles
	$(SHOW) echo THRIFT $<
	$(HIDE) for x in $$(sed 's#$(IDLPATTERN)#../flower/\1.idl#g' $^) ; \
	do $(THRIFT) --gen ocaml -r $$x ; \
	done
	$(SHOW) echo MAKE _MLFiles _MLIFiles
	$(HIDE) find . gen-ocaml -maxdepth 1 -type f '(' \
	-name '*.ml' -o \
	-false ')' > _MLFiles
	$(HIDE) find . gen-ocaml -maxdepth 1 -type f '(' \
	-name '*.mli' -o \
	-false ')' > _MLIFiles

-include .Makefile.d
