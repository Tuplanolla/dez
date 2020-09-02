CMD:=$(if $(VERBOSE),,@ )
MSG:=$(if $(VERBOSE),@ true || ,@ )

build:: gen-gv
.PHONY: build

clean::
	$(MSG) echo RM gen-gv
	$(CMD) $(RM) -r gen-gv
.PHONY: clean

# We generate diagrams just to check that the specification is valid.
gen-gv:: main.thrift component.thrift polynomial.thrift
	$(MSG) echo THRIFT $<
	$(CMD) thrift --gen gv -r $<
