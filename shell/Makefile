HIDE:=$(if $(VERBOSE),,@)
SHOW:=$(if $(VERBOSE),@ true||,@)

THRIFT:=thrift
THRIFTFLAGS:=-r
PY:=python3
PYFLAGS:=

IDLPATTERN:=\<\([^[:space:]]\+\)\.\(idl\)\>
PYPATTERN:=\<\([^[:space:]]\+\)\.\(py\)\>

PYFILES:=$(shell cat _PYFiles 2> /dev/null)

VPATH:=.:gen-py

all :: main
	$(SHOW) echo STAT $^
.PHONY : all

clean ::
	$(SHOW) echo CLEAN MAKE
	$(HIDE) find . -type f '(' \
	-name '.*.d' -o -name '_*Files' -o \
	-false ')' -exec $(RM) '{}' '+'
	$(SHOW) echo CLEAN THRIFT
	$(HIDE) find . -type d '(' \
	-name 'gen-*' -o \
	-false ')' -exec $(RM) -r '{}' '+'
	$(SHOW) echo CLEAN PY
	$(HIDE) $(RM) main
	$(HIDE) find . -type d '(' \
	-name '__pycache__' -o \
	-false ')' -exec $(RM) -r '{}' '+'
	$(HIDE) find . -type f '(' \
	-name '*.pyc' -o \
	-false ')' -exec $(RM) '{}' '+'
.PHONY : clean

run :: main
	$(SHOW) echo RUN $<
	$(HIDE) ./$<
.PHONY : run

main :: $(PYFILES:.py=.pyc)
	$(SHOW) echo TEE $@
	$(HIDE) printf '%s\n\n%s\n\n%s\n' \
	'#! /usr/bin/env python3' \
	'import main' \
	'main.main()' > $@

%.pyc :: %.py .Makefile.d
	$(SHOW) echo PY $<
	$(HIDE) $(PY) $(PYFLAGS) -m py_compile $<

Makefile :: .Makefile.d
	$(SHOW) echo MAKE $@

.Makefile.d :: _PYFiles
	$(HIDE) touch $@

_PYFiles :: ../flower/_IDLFiles
	$(SHOW) echo THRIFT $<
	$(HIDE) for x in $$(sed 's#$(IDLPATTERN)#../flower/\1.idl#g' $^) ; \
	do $(THRIFT) $(THRIFTFLAGS) --gen py $$x ; \
	done
	$(SHOW) echo MAKE $@
	$(HIDE) find . gen-py -type f '(' \
	-name '*.py' -o \
	-false ')' > $@

-include .Makefile.d
