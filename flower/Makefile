HIDE:=$(if $(VERBOSE),,@)
SHOW:=$(if $(VERBOSE),@ true||,@)

all:: gen-gv
.PHONY: all

clean::
	$(SHOW) echo CLEAN gen-gv
	$(HIDE) $(RM) -r gen-gv
.PHONY: clean

# We generate diagrams just to check that the message specification is valid.
gen-gv:: main.idl
	$(SHOW) echo THRIFT -o $@
	$(HIDE) thrift --gen gv -r $<

main.idl:: component.idl polynomial.idl
	$(SHOW) echo MAKE $@
	$(HIDE) for x in $^ ; do printf 'include "%s"\n' $$x ; done > $@
