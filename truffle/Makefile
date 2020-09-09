HIDE:=$(if $(VERBOSE),,@)
SHOW:=$(if $(VERBOSE),@ true||,@)

# TODO This.

SUBCOMPONENTS:=LoadMsh # MeshGeneration MeshSplitter RelativisticSchrodinger \
RotatingCavity ShrinkingCavity UnitCubeTest WavePropagation

DEFAULT::
	$(HIDE) for x in $(SUBCOMPONENTS) ; \
	do echo SUBMAKE $$x && make --no-print-directory -C gfd/Samples/$$x ; \
	done
.PHONY: DEFAULT

Makefile::
	@ true

clean::
	$(HIDE) for x in $(SUBCOMPONENTS) ; \
	do echo SUBCLEAN $$x && make --no-print-directory -C gfd/Samples/$$x -s $@ ; \
	done
.PHONY: clean
