CMD:=$(if $(VERBOSE),,@ )
MSG:=$(if $(VERBOSE),@ true || ,@ )

gen-py:: ../plant/polynomial.thrift
	$(MSG) echo THRIFT scales
	$(CMD) thrift --gen py $<

clean::
	$(CMD) $(RM) -r gen-py
.PHONY: clean

run:: gen-py
	$(CMD) python3 main.py
