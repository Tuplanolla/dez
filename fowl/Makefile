HIDE:=$(if $(VERBOSE),,@)
SHOW:=$(if $(VERBOSE),@ true||,@)

DEFAULT ::
	$(HIDE) $(MAKE) -s _CoqMakefile
	$(SHOW) echo MAKE -f _CoqMakefile
	$(HIDE) $(MAKE) -f _CoqMakefile -s
.PHONY : DEFAULT

.FORCE ::
	$(HIDE) true
.PHONY : .FORCE

% :: .FORCE
	$(HIDE) $(MAKE) -s _CoqMakefile
	$(SHOW) echo MAKE $@
	$(HIDE) $(MAKE) -f _CoqMakefile -s $@

# We need this rule to override an implicit rule
# that would otherwise lead to an infinite loop.
Makefile ::
	$(HIDE) true

_CoqMakefile :: _CoqMakefile.args _CoqMakefile.local
	$(SHOW) echo COQ_MAKEFILE -o $@
	$(HIDE) coq_makefile -f $< -o $@ -opt

_CoqMakefile.args :: _CoqProject _CoqFiles
	$(SHOW) echo TEE $@
	$(HIDE) cat $^ > $@

_CoqProject ::
	$(SHOW) echo TEE $@
	$(HIDE) echo 'INSTALLDEFAULTROOT = . -Q . Maniunfold' > $@

_CoqFiles ::
	$(SHOW) echo TEE $@
	$(HIDE) find . -type f -name '*.v' | LC_ALL=C sort > $@

_CoqMakefile.local ::
	$(SHOW) echo TEE $@
	$(HIDE) printf 'clean ::\n\t@ %s \\\n\t%s \\\n\t%s \\\n\t%s\n' \
	"find . -type f '('" \
	"-name '_Coq*' -o -name '*.aux' -o -name '*.cache' -o -name '*.glob' -o" \
	"-name '*.vio' -o -name '*.vo' -o -name '*.vok' -o -name '*.vos' -o" \
	"-false ')' -exec $(RM) '{}' '+'" > $@
