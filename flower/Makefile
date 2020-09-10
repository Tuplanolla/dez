HIDE:=$(if $(VERBOSE),,@)
SHOW:=$(if $(VERBOSE),@ true||,@)

GV:=dot
GVFLAGS:=-Efontname=sans -Gfontname=sans -Nfontname=sans
THRIFT:=thrift

TARGETS:=gen-gv/component.g gen-gv/polynomial.g

all :: $(TARGETS:.g=.svg)
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
$(TARGETS:.g=.gv) &:: gen.idl
	$(SHOW) echo THRIFT $<
	$(HIDE) $(THRIFT) --gen gv -r $<

gen.idl :: component.idl polynomial.idl
	$(SHOW) echo MAKE $@
	$(HIDE) for x in $^ ; do printf 'include "%s"\n' $$x ; done > $@
