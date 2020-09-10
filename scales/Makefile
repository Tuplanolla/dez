HIDE:=$(if $(VERBOSE),,@)
SHOW:=$(if $(VERBOSE),@ true||,@)

THRIFT:=thrift
PY:=python3

all :: gen-py *.py
	$(SHOW) echo STAT $^
.PHONY : all

clean ::
	$(SHOW) echo CLEAN PY
	$(HIDE) $(RM) -r __pycache__
	$(HIDE) $(RM) -r gen-py
	$(HIDE) find . -type f '(' \
	-name '*.pyc' -o \
	-false ')' -exec $(RM) '{}' '+'
.PHONY : clean

run :: main.py
	$(SHOW) echo RUN $<
	$(HIDE) $(PY) $<
.PHONY : run

gen-py :: ../flower/gen.idl
	$(SHOW) echo THRIFT $<
	$(HIDE) $(THRIFT) --gen py -r $<

# TODO Unify with `_MLFiles` convention.
