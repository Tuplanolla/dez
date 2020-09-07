CMD:=$(if $(VERBOSE),,@ )
MSG:=$(if $(VERBOSE),@ true || ,@ )

# TODO This.

build:: gen-py
.PHONY: build

clean::
	$(CMD) $(RM) -r gen-py
.PHONY: clean

run:: gen-py
	$(CMD) python3 main.py

gen-py:: ../flower/main.idl ../flower/component.idl ../flower/polynomial.idl
	$(MSG) echo THRIFT $<
	$(CMD) thrift --gen py -r $<
