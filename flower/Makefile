HIDE:=$(if $(VERBOSE),,@)
SHOW:=$(if $(VERBOSE),@ true||,@)

THRIFT:=thrift
DOT:=dot
DOTFLAGS:=-Efontname=sans -Gfontname=sans -Nfontname=sans

IDLFILES:=$(shell cat _IDLFiles 2> /dev/null)
DOTFILES:=$(shell cat _DOTFiles 2> /dev/null)

# This and several other directives in this file are completely unnecessary,
# but we keep them to be consistent with the other components.
VPATH:=.:gen-gv

# We generate diagrams just to check that the message specification is valid.
all :: $(DOTFILES:.gv=.svg)
	$(SHOW) echo STAT $^
.PHONY : all

clean ::
	$(SHOW) echo CLEAN MAKE
	$(HIDE) $(RM) _IDLFiles _DOTFiles
	$(SHOW) echo CLEAN DOT
	$(HIDE) $(RM) -r gen-gv
.PHONY : clean

%.svg :: %.gv .Makefile.d
	$(SHOW) echo DOT $<
	$(HIDE) $(DOT) $(DOTFLAGS) -Tsvg -o$@ $<

Makefile :: .Makefile.d
	$(SHOW) echo MAKE $@

.Makefile.d :: _IDLFiles _DOTFiles
	$(HIDE) touch $@

_IDLFiles :: $(IDLFILES)
	$(SHOW) echo MAKE $@
	$(HIDE) find . -maxdepth 1 -type f '(' \
	-name '*.idl' -o \
	-false ')' > $@

# We begrudgingly allow GraphViz files to have the extension `.gv`.
_DOTFiles :: _IDLFiles
	$(SHOW) echo THRIFT $<
	$(HIDE) for x in $$(cat $^) ; do $(THRIFT) --gen gv -r $$x ; done
	$(SHOW) echo MAKE $@
	$(HIDE) find . gen-gv -maxdepth 1 -type f '(' \
	-name '*.dot' -o -name '*.gv' -o \
	-false ')' > $@

-include .Makefile.d
