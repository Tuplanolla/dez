HIDE:=$(if $(VERBOSE),,@)
SHOW:=$(if $(VERBOSE),@ true||,@)

THRIFT:=thrift
PY:=python3

IDLPATTERN:=\<\([^[:space:]]\+\)\.idl\>

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

gen-py :: ../flower/_IDLFiles
	$(SHOW) echo THRIFT $<
	$(HIDE) for x in $$(sed 's#$(IDLPATTERN)#../flower/\1.idl#g' $^) ; \
	do $(THRIFT) --gen py -r $$x ; \
	done

# TODO Unify with `_MLFiles` convention.
