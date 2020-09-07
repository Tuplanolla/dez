HIDE:=$(if $(VERBOSE),,@)
SHOW:=$(if $(VERBOSE),@ true||,@)

DEFAULT::
	$(HIDE) $(MAKE) -s _CoqMakefile
	$(SHOW) echo MAKE
	$(HIDE) $(MAKE) -f _CoqMakefile -s
.PHONY: DEFAULT

# We have this target just to prevent getting stuck on nothing to do.
.FORCE::
	@ true
.PHONY: .FORCE

%:: .FORCE
	$(HIDE) $(MAKE) -s _CoqMakefile
	$(SHOW) echo MAKE $@
	$(HIDE) $(MAKE) -f _CoqMakefile -s $@

# We have this target just to prevent getting stuck on an infinite loop.
Makefile::
	@ true

_CoqMakefile:: _CoqMakefile.args _CoqMakefile.local
	$(SHOW) echo COQ_MAKEFILE -o $@
	$(HIDE) coq_makefile -f $< -o $@ -opt

_CoqMakefile.args:: _CoqProject _CoqFiles
	$(SHOW) echo SH '>' $@
	$(HIDE) cat $^ > $@

_CoqProject::
	$(SHOW) echo SH '>' $@
	$(HIDE) printf '%s\n' "INSTALLDEFAULTROOT = . -Q . Maniunfold" > $@

_CoqFiles::
	$(SHOW) echo SH '>' $@
	$(HIDE) find . -type f -name '*.v' | LC_ALL=C sort > $@

_CoqMakefile.local::
	$(SHOW) echo SH '>' $@
	$(HIDE) printf 'clean::\n\t@ %s %s %s %s\n' \
	"find . -type f '('" \
	"-name '_Coq*' -o -name '*.aux' -o -name '*.cache' -o -name '*.glob' -o" \
	"-name '*.vio' -o -name '*.vo' -o -name '*.vok' -o -name '*.vos'" \
	"')' -exec $(RM) '{}' '+'" > $@
