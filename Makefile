# These commands inspired by `coq_makefile` are intended to reduce noise.
HIDE:=$(if $(VERBOSE),,@)
SHOW:=$(if $(VERBOSE),@ true||,@)

CPP:=cpp
CPPFLAGS:=-P
GV:=dot
GVFLAGS:=-Efontname=sans -Gfontname=sans -Nfontname=sans

COMPONENTS:=fowl \
flower ungulate camel fur reptile snake scales fungus truffle spores ape
TARGETS:=habitat.svg habitat-with-example.svg

all :: $(COMPONENTS) $(TARGETS)
	$(SHOW) echo STAT $(TARGETS)
.PHONY : all

clean ::
	$(SHOW) echo CLEAN $(COMPONENTS)
	$(HIDE) for x in $(COMPONENTS) ; do $(MAKE) -C $$x -s $@ ; done
.PHONY : clean

run :: fur scales ape
	$(SHOW) echo RUN $^
	$(HIDE) ( sleep 1 && $(MAKE) -C fur -s $@ ; ) & \
	( sleep 1 && $(MAKE) -C scales -s $@ ; ) & \
	( sleep 1 && $(MAKE) -C spores -s $@ ; ) & \
	$(MAKE) -C ape -s $@
.PHONY : run

# We track the dependencies between components here,
# because we do not want to have the components
# care about compiling each other.
camel :: fowl
fur :: flower ungulate camel
snake :: reptile
scales :: flower reptile snake
spores :: flower fungus truffle
ape :: ungulate

# This rule must come after rules that define dependencies between components,
# so that the dependencies are built first.
$(COMPONENTS) ::
	$(SHOW) echo MAKE -C $@
	$(HIDE) $(MAKE) -C $@ -s
.PHONY : $(COMPONENTS)

%.svg :: %.dot
	$(SHOW) echo GV $<
	$(HIDE) $(GV) $(GVFLAGS) -Tsvg -o$@ $<

habitat.dot :: habitat.dot.h
	$(SHOW) echo CPP -o $@ $<
	$(HIDE) $(CPP) $(CPPFLAGS) \
	-D CLUSTER -D COMPILE -D SHOWCOMPILE -U RUN -U SHOWRUN -o$@ $<

habitat-with-example.dot :: habitat.dot.h
	$(SHOW) echo CPP -o $@ $<
	$(HIDE) $(CPP) $(CPPFLAGS) \
	-D CLUSTER -D COMPILE -U SHOWCOMPILE -D RUN -D SHOWRUN -o$@ $<
