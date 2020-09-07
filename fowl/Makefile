HIDE:=$(if $(VERBOSE),,@)
SHOW:=$(if $(VERBOSE),@ true||,@)

DEFAULT::
	$(HIDE) $(MAKE) -s _CoqMakefile
	$(SHOW) echo MAKE
	$(HIDE) $(MAKE) -f _CoqMakefile -s
.PHONY: DEFAULT

# This target is here just to prevent a loop.
.FORCE::
	@ true
.PHONY: .FORCE

%:: .FORCE
	$(HIDE) $(MAKE) -s _CoqMakefile
	$(SHOW) echo MAKE $@
	$(HIDE) $(MAKE) -f _CoqMakefile -s $@

# This target is here just to prevent a loop.
Makefile::
	@ true

_CoqMakefile:: _CoqMakefile.args _CoqMakefile.local
	$(SHOW) echo MAKE $@
	$(HIDE) coq_makefile -f $< -o $@ -opt

_CoqMakefile.args:: _CoqProject _CoqFiles
	$(SHOW) echo MAKE $@
	$(HIDE) cat $^ > $@

_CoqProject::
	$(SHOW) echo MAKE $@
	$(HIDE) printf '%s\n' "INSTALLDEFAULTROOT = . -Q . Maniunfold" > $@

_CoqFiles::
	$(SHOW) echo MAKE $@
	$(HIDE) find . -type f -name '*.v' | LC_ALL=C sort > $@

_CoqMakefile.local::
	$(SHOW) echo MAKE $@
	$(HIDE) printf 'clean::\n\t@ %s %s %s %s\n' \
	"find . -type f '('" \
	"-name '_Coq*' -o -name '*.aux' -o -name '*.cache' -o -name '*.glob' -o" \
	"-name '*.vio' -o -name '*.vo' -o -name '*.vok' -o -name '*.vos'" \
	"')' -exec rm '{}' '+'" > $@
