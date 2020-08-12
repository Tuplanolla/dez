CMD:=$(if $(VERBOSE),,@ )
MSG:=$(if $(VERBOSE),@ true || ,@ )

# We generate a diagram just to check that the specification is valid.
gen-gv:: messages.thrift
	$(MSG) echo THRIFT plant
	$(CMD) thrift --gen gv $<

clean::
	$(CMD) $(RM) -r gen-gv
.PHONY: clean
