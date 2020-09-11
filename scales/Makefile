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

all :: $(PYFILES:.py=.pyc)
	$(SHOW) echo STAT $^
.PHONY : all

clean ::
	$(SHOW) echo CLEAN MAKE
	$(HIDE) $(RM) .Makefile.d _PYFiles
	$(SHOW) echo CLEAN PY
	$(HIDE) $(RM) -r __pycache__
	$(HIDE) $(RM) -r gen-py
	$(HIDE) find . -type f '(' \
	-name '*.pyc' -o \
	-false ')' -exec $(RM) '{}' '+'
.PHONY : clean

run :: main.py
	$(SHOW) echo RUN $<
	$(HIDE) $(PY) $(PYFLAGS) $<
.PHONY : run

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
