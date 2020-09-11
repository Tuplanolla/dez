HIDE:=$(if $(VERBOSE),,@)
SHOW:=$(if $(VERBOSE),@ true||,@)

COMPONENTS:=LoadMsh # MeshGeneration MeshSplitter RelativisticSchrodinger \
RotatingCavity ShrinkingCavity UnitCubeTest WavePropagation

all :: $(COMPONENTS)
	$(SHOW) echo STAT $^
.PHONY : all

clean ::
	$(SHOW) echo CLEAN $(COMPONENTS)
	$(HIDE) for x in $(COMPONENTS) ; \
	do $(MAKE) -C gfd/Samples/$$x -s $@ ; \
	done
.PHONY : clean

$(COMPONENTS) ::
	$(SHOW) echo MAKE -C $@
	$(HIDE) $(MAKE) -C gfd/Samples/$@ -s
.PHONY : $(COMPONENTS)
