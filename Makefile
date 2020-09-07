HIDE:=$(if $(VERBOSE),,@)
SHOW:=$(if $(VERBOSE),@ true||,@)

TARGETS:=fowl \
flower ungulate camel fur reptile snake scales fungus truffle spores ape

all:: habitat.svg habitat-with-example.svg $(TARGETS)
.PHONY: all

clean::
	$(SHOW) echo CLEAN $(TARGETS)
	$(HIDE) for x in $(TARGETS) ; do \
	$(MAKE) -C $$x -s $@ ; \
	done
.PHONY: clean

$(TARGETS)::
	$(SHOW) echo MAKE -C $@
	$(HIDE) $(MAKE) -C $@ -s

camel:: fowl
fur:: flower ungulate camel
snake:: reptile
scales:: reptile snake flower
spores:: flower fungus truffle
ape:: ungulate

%.svg:: %.dot
	$(SHOW) echo DOT $<
	$(HIDE) dot -Efontname=sans -Gfontname=sans -Nfontname=sans -Tsvg -o$@ $<

habitat.dot:: habitat.dot.h
	$(SHOW) echo CPP -DCOMPILE $<
	$(HIDE) cpp -P -DCLUSTER -DCOMPILE -DSHOWCOMPILE -URUN -USHOWRUN -o$@ $<

habitat-with-example.dot:: habitat.dot.h
	$(SHOW) echo CPP -DRUN $<
	$(HIDE) cpp -P -DCLUSTER -DCOMPILE -USHOWCOMPILE -DRUN -DSHOWRUN -o$@ $<
