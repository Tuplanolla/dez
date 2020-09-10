HIDE:=$(if $(VERBOSE),,@)
SHOW:=$(if $(VERBOSE),@ true||,@)

PY:=python3
PYVERSION:=cpython-36

PYPATTERN:=\<\([^[:space:]]\+\)\.py\>

PYFILES:=$(shell echo *.py)
PYCFILES:=$(shell echo *.py | \
sed 's|$(PYPATTERN)|__pycache__/\1.$(PYVERSION).pyc|g')

all :: $(PYCFILES)
	$(SHOW) echo STAT $^
.PHONY : all

clean ::
	$(SHOW) echo CLEAN PY
	$(HIDE) $(RM) -r gen-py
	$(HIDE) $(RM) -r __pycache__
.PHONY : clean

run :: main.py
	$(SHOW) echo RUN $<
	$(HIDE) $(PY) $<
.PHONY : run

# Getting the target of this rule right does not matter much,
# as it merely eliminates needless recompilation.
__pycache__/%.$(PYVERSION).pyc :: %.py
	$(SHOW) echo PY $<
	$(HIDE) $(PY) -m py_compile $<
