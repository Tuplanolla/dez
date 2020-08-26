CMD:=$(if $(VERBOSE),,@ )
MSG:=$(if $(VERBOSE),@ true || ,@ )

build:: gen-py
.PHONY: build

clean::
	$(CMD) $(RM) -r gen-py
.PHONY: clean

run:: gen-py
	$(CMD) python3 main.py

gen-py:: ../plant/main.thrift ../plant/component.thrift ../plant/polynomial.thrift
	$(MSG) echo THRIFT $<
	$(CMD) thrift --gen py -r $<
