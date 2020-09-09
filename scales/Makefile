HIDE:=$(if $(VERBOSE),,@)
SHOW:=$(if $(VERBOSE),@ true||,@)

PYTHON:=python3

all:: gen-py
	@ true
.PHONY: all

clean::
	$(SHOW) echo CLEAN gen-py
	$(HIDE) $(RM) -r gen-py
	$(SHOW) echo CLEAN PY
	$(HIDE) $(RM) -r __pycache__
.PHONY: clean

run::
	$(SHOW) echo RUN main.py
	$(HIDE) $(PYTHON) main.py
.PHONY: run

gen-py:: ../flower/main.idl
	$(SHOW) echo THRIFT $<
	$(HIDE) thrift --gen py -r $<

# prereq:: reptile snake flower
