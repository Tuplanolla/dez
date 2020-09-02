CMD:=$(if $(VERBOSE),,@ )
MSG:=$(if $(VERBOSE),@ true || ,@ )

SUBCOMPONENTS:=LoadMsh # MeshGeneration MeshSplitter RelativisticSchrodinger \
RotatingCavity ShrinkingCavity UnitCubeTest WavePropagation

DEFAULT::
	$(CMD) for x in $(SUBCOMPONENTS) ; \
	do echo SUBMAKE $$x && make --no-print-directory -C gfd/Samples/$$x ; \
	done
.PHONY: DEFAULT

Makefile::
	@ true

clean::
	$(CMD) for x in $(SUBCOMPONENTS) ; \
	do echo SUBCLEAN $$x && make --no-print-directory -C gfd/Samples/$$x -s $@ ; \
	done
.PHONY: clean
