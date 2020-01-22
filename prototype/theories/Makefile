CMD:=$(if $(VERBOSE),,@ )
MSG:=$(if $(VERBOSE),@ true || ,@ )

all:: _CoqMakefile
	$(CMD) $(MAKE) -f _CoqMakefile -s all
.PHONY: all

clean::
	$(CMD) $(MAKE) -f _CoqMakefile -s clean
	$(CMD) $(RM) _CoqProject _CoqFiles \
	_CoqMakefile _CoqMakefile.args _CoqMakefile.conf _CoqMakefile.local
.PHONY: clean

_CoqMakefile:: _CoqMakefile.args _CoqMakefile.local
	$(CMD) coq_makefile -f $< -o $@ -opt

_CoqMakefile.args:: _CoqProject _CoqFiles
	$(CMD) cat $^ > $@

_CoqProject::
	$(CMD) printf '%s %s %s\n' '-Q' '.' 'Maniunfold' > $@

_CoqFiles::
	$(CMD) find . -type f -name '*.v' | LC_ALL=C sort > $@

_CoqMakefile.local::
	$(CMD) printf '%s::\n\t@ %s %s %s\n' 'clean' 'find . -type f' \
	"'(' -name '*.aux' -o -name '*.glob' -o -name '*.vo' ')'" \
	"-exec rm '{}' '+'" > $@
