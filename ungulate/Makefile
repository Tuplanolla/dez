CMD:=$(if $(VERBOSE),,@ )
MSG:=$(if $(VERBOSE),@ true || ,@ )

all:: extraction.cmi adapter.cmi
.PHONY: all

clean::
	$(CMD) $(RM) .*.aux *.glob *.vo*
	$(CMD) bash -c "echo *.{ml,mli,cmx,cmi,o} | tr ' ' '\n' | \
	grep -v 'adapter.ml' | xargs rm -f"
.PHONY: clean

OCAMLPFFTLAGS:=-O2 -package num -package logs -thread

extraction.cmi:: extraction.mli
	$(MSG) echo OCAMLOPT extraction
	$(CMD) ocamlfind ocamlopt $(OCAMLPFFTLAGS) extraction.mli
	$(CMD) ocamlfind ocamlopt $(OCAMLPFFTLAGS) extraction.ml

adapter.cmi:: adapter.mli
	$(MSG) echo OCAMLOPT adapter
	$(CMD) ocamlfind ocamlopt $(OCAMLPFFTLAGS) adapter.mli
	$(CMD) ocamlfind ocamlopt $(OCAMLPFFTLAGS) adapter.ml

extraction.mli:: Extraction.v
	$(CMD) coqc -Q ../bird Maniunfold Extraction.v
