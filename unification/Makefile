COQC:=coqc

logs : $(shell find . -maxdepth 1 -name '*.dot' | sed 's|\.dot$$|.log|')

%.log : %.v
	@ $(COQC) $< > $@
	@ $(RM) $(<:.v=.glob) $(<:.v=.vo) $(<:.v=.vok) $(<:.v=.vos)
