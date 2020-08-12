CMD:=$(if $(VERBOSE),,@ )
MSG:=$(if $(VERBOSE),@ true || ,@ )

gen-gv:: messages.thrift
	$(MSG) echo THRIFT plant
	# This generates a diagram just to check that the specification is valid.
	$(CMD) thrift --gen gv $<

clean::
	$(CMD) $(RM) gen-gv
.PHONY: clean
