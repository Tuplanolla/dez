HIDE:=$(if $(VERBOSE),,@)
SHOW:=$(if $(VERBOSE),@ true||,@)

PYTHON:=python3

all::
	@ true
.PHONY: all

clean::
	$(SHOW) echo CLEAN PY
	$(HIDE) $(RM) -r __pycache__
.PHONY: clean

run::
	$(SHOW) echo RUN main.py
	$(HIDE) $(PYTHON) main.py
.PHONY: run

# prereq:: reptile
