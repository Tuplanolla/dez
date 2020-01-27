CMD:=$(if $(VERBOSE),,@ )
MSG:=$(if $(VERBOSE),@ true || ,@ )

all:: main
	$(MSG) echo MAIN test
	@ ./main test
.PHONY: all

clean:: squeaky-clean
	$(CMD) $(RM) _CoqProject _CoqFiles \
	_CoqMakefile _CoqMakefile.args _CoqMakefile.conf _CoqMakefile.local
	$(CMD) $(RM) extraction.ml extraction.mli
	$(CMD) $(RM) extraction.cmi extraction.cmx extraction.o
	$(CMD) $(RM) adapter.cmi adapter.cmx adapter.o
	$(CMD) $(RM) main.cmi main.cmx main.o main
.PHONY: clean

squeaky-clean::
	$(CMD) test -e theories/Makefile && $(MAKE) -C theories -s clean || exit 0
	$(CMD) test -e _CoqMakefile && $(MAKE) -f _CoqMakefile -s clean || exit 0
.PHONY: squeaky-clean

extraction.mli:: _CoqMakefile
	$(CMD) $(MAKE) -C theories -s all
	$(CMD) $(MAKE) -f _CoqMakefile -s all

_CoqMakefile:: _CoqMakefile.args _CoqMakefile.local
	$(CMD) coq_makefile INSTALLDEFAULTROOT = . -f $< -o $@ -opt

_CoqMakefile.args:: _CoqProject _CoqFiles
	$(CMD) cat $^ > $@

_CoqProject::
	$(CMD) printf '%s %s %s\n%s %s %s\n' \
	'-Q' 'theories' 'Maniunfold' '-Q' 'extraction' 'Protofold' > $@

_CoqFiles::
	$(CMD) find . -type f -name 'Extraction.v' | LC_ALL=C sort > $@

_CoqMakefile.local::
	$(CMD) printf '%s::\n\t@ %s %s %s\n' 'clean' 'find . -type f' \
	"'(' -name '*.aux' -o -name '*.glob' -o -name '*.vo' ')'" \
	"-exec rm '{}' '+'" > $@

main:: extraction.mli
	$(MSG) echo OCAMLOPT extraction
	$(CMD) ocamlfind ocamlopt -O2 -c -package num extraction.mli
	$(CMD) ocamlfind ocamlopt -O2 -c -package num extraction.ml
	$(MSG) echo OCAMLOPT adapter
	$(CMD) ocamlfind ocamlopt -O2 -c -package num adapter.mli
	$(CMD) ocamlfind ocamlopt -O2 -c -package num adapter.ml
	$(MSG) echo OCAMLOPT main
	$(CMD) ocamlfind ocamlopt -O2 -c -package num main.ml
	$(CMD) ocamlfind ocamlopt -O2 -linkpkg -o main -package num \
	extraction.cmx adapter.cmx main.cmx

dune::
	dune build @install
.PHONY: dune

habitat::
	cpp -P -DCLUSTER -DCOMPILE -URUN -o first.dot habitat.dot
	cpp -P -DCLUSTER -UCOMPILE -DRUN -o second.dot habitat.dot
	cpp -P -DCLUSTER -DCOMPILE -DRUN -o both.dot habitat.dot
	for x in first second both ; \
	do dot -Gfontname=sans -Efontname=sans -Nfontname=sans -Tsvg $$x.dot -o$$x.svg ; \
	done
.PHONY: habitat
