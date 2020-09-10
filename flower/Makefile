HIDE:=$(if $(VERBOSE),,@)
SHOW:=$(if $(VERBOSE),@ true||,@)

THRIFT:=thrift
GV:=dot
GVFLAGS:=-Efontname=sans -Gfontname=sans -Nfontname=sans

IDLFILES:=component.idl polynomial.idl
GVFILES:=$(shell cat _GVFiles 2> /dev/null || echo _GVFiles)

VPATH:=.:gen-gv

all :: $(GVFILES:.gv=.svg)
	$(SHOW) echo STAT $^
.PHONY : all

clean ::
	$(SHOW) echo CLEAN MAKE
	$(HIDE) $(RM) _GVFiles
	$(SHOW) echo CLEAN GV
	$(HIDE) $(RM) -r gen-gv
.PHONY : clean

%.svg :: %.gv .Makefile.d
	$(SHOW) echo GV $<
	$(HIDE) $(GV) $(GVFLAGS) -Tsvg -o$@ $<

Makefile :: .Makefile.d
	$(SHOW) echo MAKE $@

# This rule is completely unnecessary,
# but we keep it in order to be consistent with the other components.
.Makefile.d :: _GVFiles
	$(HIDE) touch $@

# We generate diagrams just to check that the message specification is valid.
_GVFiles :: gen.idl
	$(SHOW) echo THRIFT $<
	$(HIDE) $(THRIFT) --gen gv -r $<
	$(SHOW) echo MAKE _GVFiles
	$(HIDE) echo gen-gv/*.gv > _GVFiles

gen.idl :: $(IDLFILES)
	$(SHOW) echo MAKE $@
	$(HIDE) for x in $^ ; do printf 'include "%s"\n' $$x ; done > $@

-include .Makefile.d
