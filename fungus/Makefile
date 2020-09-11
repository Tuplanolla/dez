HIDE:=$(if $(VERBOSE),,@)
SHOW:=$(if $(VERBOSE),@ true||,@)

all ::
	$(SHOW) echo STAT $^
	$(HIDE) touch _CXXFiles _HXXFiles
.PHONY : all

clean ::
	$(SHOW) echo CLEAN CXX
.PHONY : clean

# TODO Unify with `_MLFiles` convention.
