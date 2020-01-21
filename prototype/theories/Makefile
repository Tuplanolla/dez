CMD:=$(if $(VERBOSE),,@ )
MSG:=$(if $(VERBOSE),@ true || ,@ )

all:: make
	@ $(MAKE) -f make -s all
.PHONY: all

clean::
	@ $(MAKE) -f make -s clean
	$(CMD) $(RM) make make.args make.conf make.local make.vfiles
.PHONY: clean

make::
	$(CMD) find . -type f -name '*.v' | LC_ALL=C sort > make.vfiles
	$(CMD) cat make.vfiles _CoqProject > make.args
	$(CMD) coq_makefile -f make.args -o make -opt
	$(CMD) printf '%s::\n\t@ %s %s %s\n' 'clean' 'find . -type f' \
	"'(' -name '*.aux' -o -name '*.glob' -o -name '*.vo' ')'" \
	"-exec rm '{}' '+'" > make.local
