HIDE:=$(if $(VERBOSE),,@)
SHOW:=$(if $(VERBOSE),@ true||,@)

all ::
	$(SHOW) echo STAT
.PHONY : all

clean ::
	$(SHOW) echo CLEAN PY
	$(HIDE) $(RM) -r __pycache__
.PHONY : clean
