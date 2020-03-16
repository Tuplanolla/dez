CMD:=$(if $(VERBOSE),,@ )
MSG:=$(if $(VERBOSE),@ true || ,@ )

DEFAULT::
	$(MSG) echo MAKE
	$(CMD) make -s _CoqMakefile
	$(CMD) make -f _CoqMakefile -s
.PHONY: DEFAULT

Makefile::
	@ true

%:: .FORCE
	$(MSG) echo MAKE $@
	$(CMD) make -s _CoqMakefile
	$(CMD) make -f _CoqMakefile -s $@

_CoqMakefile:: _CoqMakefile.args _CoqMakefile.local
	$(MSG) echo MAKE $@
	$(CMD) coq_makefile -f $< -o $@ -opt

_CoqMakefile.args:: _CoqProject _CoqFiles
	$(CMD) cat $^ > $@

_CoqProject::
	$(CMD) printf '%s %s %s\n' '-Q' '.' 'Maniunfold' > $@

_CoqFiles::
	$(CMD) find . -type f -name '*.v' | LC_ALL=C sort > $@

_CoqMakefile.local::
	$(CMD) printf 'clean::\n\t@ %s %s %s\n' \
	"find . -type f '('" \
	"-name '*_Coq*' -o -name '*.aux*' -o -name '*.glob*' -o -name '*.vo*'" \
	"')' -exec rm '{}' '+'" > $@

.FORCE::
	@ true
.PHONY: .FORCE
