HIDE:=$(if $(VERBOSE),,@)
SHOW:=$(if $(VERBOSE),@ true||,@)

THRIFT:=thrift
GV:=dot
GVFLAGS:=-Efontname=sans -Gfontname=sans -Nfontname=sans

IDLFILES:=component.idl polynomial.idl

all :: $(addprefix gen-gv/,$(IDLFILES:.idl=.svg))
	$(SHOW) echo STAT $^
.PHONY : all

clean ::
	$(SHOW) echo CLEAN GV
	$(HIDE) $(RM) -r gen-gv
.PHONY : clean

gen-gv/%.svg :: gen-gv/%.gv
	$(SHOW) echo GV $<
	$(HIDE) $(GV) $(GVFLAGS) -Tsvg -o$@ $<

# We generate diagrams just to check that the message specification is valid.
$(addprefix gen-gv/,$(IDLFILES:.idl=.gv)) &:: gen.idl
	$(SHOW) echo THRIFT $<
	$(HIDE) $(THRIFT) --gen gv -r $<

gen.idl :: $(IDLFILES)
	$(SHOW) echo MAKE $@
	$(HIDE) for x in $^ ; do printf 'include "%s"\n' $$x ; done > $@
