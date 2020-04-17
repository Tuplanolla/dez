CMD:=$(if $(VERBOSE),,@ )
MSG:=$(if $(VERBOSE),@ true || ,@ )

SUBCOMPONENTS:=bird ungulate fungus reptile plant fur spores scales primate

DEFAULT::
	$(CMD) for x in $(SUBCOMPONENTS) ; \
	do make -C $$x ; \
	done
.PHONY: DEFAULT

Makefile::
	@ true

clean::
	$(CMD) for x in $(SUBCOMPONENTS) ; \
	do make -C $$x -s $@ ; \
	done
.PHONY: clean

habitat::
	cpp -P -DCLUSTER -DCOMPILE -URUN -o first.dot habitat.dot
	cpp -P -DCLUSTER -UCOMPILE -DRUN -o second.dot habitat.dot
	cpp -P -DCLUSTER -DCOMPILE -DRUN -o both.dot habitat.dot
	for x in first second both ; \
	do dot -Gfontname=sans -Efontname=sans -Nfontname=sans -Tsvg $$x.dot -o$$x.svg ; \
	done
.PHONY: habitat
