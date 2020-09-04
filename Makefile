CMD:=$(if $(VERBOSE),,@ )
MSG:=$(if $(VERBOSE),@ true || ,@ )

SUBCOMPONENTS:=fowl flower ungulate camel fur reptile snake scales \
fungus truffle spores ape

# TODO Do it like this and then make subcomponents independent...
#
# .PHONY: partA partB partC
#
# all: partA partB partC
#
# partA partB partC:
# 	$(MAKE) -C $@
#
# partB: partA

DEFAULT::
	$(CMD) for x in $(SUBCOMPONENTS) ; \
	do echo SUBMAKE $$x && make --no-print-directory -C $$x ; \
	done
.PHONY: DEFAULT

Makefile::
	@ true

clean::
	$(CMD) for x in $(SUBCOMPONENTS) ; \
	do echo SUBCLEAN $$x && make --no-print-directory -C $$x -s $@ ; \
	done
.PHONY: clean

habitat::
	cpp -P -DCLUSTER -DCOMPILE -URUN -o habitat.dot habitat.dot.h
	cpp -P -DCLUSTER -DCOMPILE -DRUN -o habitat-with-example.dot habitat.dot.h
	for x in habitat habitat-with-example ; \
	do dot -Gfontname=sans -Efontname=sans -Nfontname=sans -Tsvg $$x.dot -o$$x.svg ; \
	done
.PHONY: habitat
