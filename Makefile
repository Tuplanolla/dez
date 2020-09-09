HIDE:=$(if $(VERBOSE),,@)
SHOW:=$(if $(VERBOSE),@ true||,@)

COMPONENTS:=fowl \
flower ungulate camel fur reptile snake scales fungus truffle spores ape

all:: $(COMPONENTS) habitat.svg habitat-with-example.svg
.PHONY: all

clean::
	$(SHOW) echo CLEAN $(COMPONENTS)
	$(HIDE) for x in $(COMPONENTS) ; do $(MAKE) -C $$x -s $@ ; done
.PHONY: clean

run:: fur scales ape
	$(SHOW) echo RUN $^
	$(HIDE) ( sleep 1 && $(MAKE) -C fur -s $@ ; ) & \
	( sleep 1 && $(MAKE) -C scales -s $@ ; ) & \
	$(MAKE) -C ape -s $@
.PHONY: run

# We do not even try to track dependencies between components,
# because they span several languages.
$(COMPONENTS)::
	$(SHOW) echo MAKE -C $@
	$(HIDE) $(MAKE) -C $@ -s
.PHONY: $(COMPONENTS)

%.svg:: %.dot
	$(SHOW) echo DOT $<
	$(HIDE) dot -Efontname=sans -Gfontname=sans -Nfontname=sans -Tsvg -o$@ $<

habitat.dot:: habitat.dot.h
	$(SHOW) echo CPP -o $@ $<
	$(HIDE) cpp -P -D CLUSTER -D COMPILE -D SHOWCOMPILE -U RUN -U SHOWRUN -o$@ $<

habitat-with-example.dot:: habitat.dot.h
	$(SHOW) echo CPP -o $@ $<
	$(HIDE) cpp -P -D CLUSTER -D COMPILE -U SHOWCOMPILE -D RUN -D SHOWRUN -o$@ $<
