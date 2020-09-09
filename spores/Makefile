HIDE:=$(if $(VERBOSE),,@)
SHOW:=$(if $(VERBOSE),@ true||,@)

all::
	@ true
.PHONY: all

clean::
	@ true
.PHONY: clean

run::
	$(SHOW) echo RUN main
	$(HIDE) ./main
.PHONY: run

# prereq:: flower fungus truffle
