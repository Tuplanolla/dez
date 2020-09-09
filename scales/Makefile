HIDE:=$(if $(VERBOSE),,@)
SHOW:=$(if $(VERBOSE),@ true||,@)

PYTHON:=python3

all :: gen-py main.pyc
	$(SHOW) echo STAT $^
.PHONY: all

clean ::
	$(SHOW) echo CLEAN gen-py
	$(HIDE) $(RM) -r gen-py
	$(SHOW) echo CLEAN PY
	$(HIDE) $(RM) -r __pycache__
.PHONY: clean

run ::
	$(SHOW) echo RUN main.py
	$(HIDE) $(PYTHON) main.py
.PHONY: run

gen-py :: ../flower/gen.idl
	$(SHOW) echo THRIFT $<
	$(HIDE) thrift --gen py -r $<

%.pyc :: %.py
	$(PYTHON) -m py_compile $<
