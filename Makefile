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
	$(SHOW) echo STAT $^
.PHONY : all

clean ::
	$(SHOW) echo CLEAN $(COMPONENTS)
	$(HIDE) for x in $$(echo $(COMPONENTS) | tac -s ' ') ; \
	do $(MAKE) -C $$x -s $@ ; \
	done
.PHONY : clean

# We have this failsafe mechanism in place,
# because cleaning some of the components may require
# having some of the other components built.
deep-clean ::
	$(SHOW) echo CLEAN MAKE
	$(HIDE) find . -type f '(' \
	-name '.*.d' -o -name '_*Files' -o \
	-false ')' -exec $(RM) '{}' '+'
	$(SHOW) echo CLEAN COQ
	$(HIDE) find . -type f '(' \
	-name '_Coq*' -o -name '*.aux' -o -name '*.cache' -o -name '*.glob' -o \
	-name '*.vio' -o -name '*.vo' -o -name '*.vok' -o -name '*.vos' -o \
	-false ')' -exec $(RM) '{}' '+'
	$(SHOW) echo CLEAN THRIFT
	$(HIDE) find . -type d '(' \
	-name 'gen-*' -o \
	-false ')' -exec $(RM) -r '{}' '+'
	$(SHOW) echo CLEAN CAML
	$(HIDE) find . -type f '(' \
	-name '*.cmi' -o -name '*.cmo' -o -name '*.cmx' -o -name '*.o' -o \
	-false ')' -exec $(RM) '{}' '+'
	$(SHOW) echo CLEAN CXX
	$(HIDE) find . -type f '(' \
	-name '*.o' -o \
	-false ')' -exec $(RM) '{}' '+'
.PHONY : deep-clean

# We do not depend on the components here,
# because having them as phony targets slows down the launch.
run :: # fur scales ape
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
