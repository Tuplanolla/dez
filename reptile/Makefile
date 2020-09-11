HIDE:=$(if $(VERBOSE),,@)
SHOW:=$(if $(VERBOSE),@ true||,@)

PY:=python3
PYFLAGS:=

PYPATTERN:=\<\([^[:space:]]\+\)\.\(py\)\>

PYFILES:=$(shell cat _PYFiles 2> /dev/null)

all :: $(PYFILES:.py=.pyc)
	$(SHOW) echo STAT $^
.PHONY : all

clean ::
	$(SHOW) echo CLEAN MAKE
	$(HIDE) $(RM) .Makefile.d _PYFiles
	$(SHOW) echo CLEAN PY
	$(HIDE) $(RM) -r __pycache__
	$(HIDE) find . -type f '(' \
	-name '*.pyc' -o \
	-false ')' -exec $(RM) '{}' '+'
.PHONY : clean

# These targets may never be created,
# but that is totally fine.
%.pyc :: %.py .Makefile.d
	$(SHOW) echo PY $<
	$(HIDE) $(PY) $(PYFLAGS) -m py_compile $<

Makefile :: .Makefile.d
	$(SHOW) echo MAKE $@

.Makefile.d :: _PYFiles
	$(HIDE) touch $@

_PYFiles :: $(PYFILES)
	$(SHOW) echo MAKE $@
	$(HIDE) find . -type f '(' \
	-name '*.py' -o \
	-false ')' > $@

-include .Makefile.d

