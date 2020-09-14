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
	$(HIDE) find . -type f '(' \
	-name '.*.d' -o -name '_*Files' -o \
	-false ')' -exec $(RM) '{}' '+'
	$(SHOW) echo CLEAN PY
	$(HIDE) find . -type d '(' \
	-name '__pycache__' -o \
	-false ')' -exec $(RM) -r '{}' '+'
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

_PYFiles :: $(PYFILES)
	$(SHOW) echo MAKE $@
	$(HIDE) find . -type f '(' \
	-name '*.py' -o \
	-false ')' > $@

-include .Makefile.d
