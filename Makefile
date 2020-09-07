HIDE:=$(if $(VERBOSE),,@)
SHOW:=$(if $(VERBOSE),@ true||,@)

# We cannot easily track dependencies between components,
# because they span several languages,
# which is why we do not even try.

COMPONENTS:=fowl \
flower ungulate camel fur reptile snake scales fungus truffle spores ape

all:: habitat.svg habitat-with-example.svg $(COMPONENTS)
.PHONY: all

clean::
	$(SHOW) echo CLEAN $(COMPONENTS)
	$(HIDE) for x in $(COMPONENTS) ; do $(MAKE) -C $$x -s $@ ; done
.PHONY: clean

run::
	echo TODO This.
.PHONY: run

$(COMPONENTS)::
	$(SHOW) echo MAKE -C $@
	$(HIDE) $(MAKE) -C $@ -s
.PHONY: $(COMPONENTS)

%.svg:: %.dot
	$(SHOW) echo DOT -o $@
	$(HIDE) dot -Efontname=sans -Gfontname=sans -Nfontname=sans -Tsvg -o$@ $<

habitat.dot:: habitat.dot.h
	$(SHOW) echo CPP -o $@
	$(HIDE) cpp -P -D CLUSTER -D COMPILE -D SHOWCOMPILE -U RUN -U SHOWRUN -o$@ $<

habitat-with-example.dot:: habitat.dot.h
	$(SHOW) echo CPP -o $@
	$(HIDE) cpp -P -D CLUSTER -D COMPILE -U SHOWCOMPILE -D RUN -D SHOWRUN -o$@ $<
