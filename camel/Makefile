CMD:=$(if $(VERBOSE),,@ )
MSG:=$(if $(VERBOSE),@ true || ,@ )

all:: extraction.cmx adapter.cmx
.PHONY: all

clean::
	$(CMD) $(RM) .*.aux *.glob *.vo*
	$(CMD) bash -c "echo *.{ml,mli,cmx,cmi,o} | tr ' ' '\n' | \
	grep -v 'adapter.ml' | xargs rm -f"
.PHONY: clean

OCAMLPFFTLAGS:=-O2 -package num -package logs -thread

extraction.cmi:: extraction.mli
	$(MSG) echo OCAMLOPT extraction
	$(CMD) ocamlfind ocamlopt -c $(OCAMLPFFTLAGS) extraction.mli

extraction.cmx:: extraction.ml
	$(MSG) echo OCAMLOPT extraction
	$(CMD) ocamlfind ocamlopt -c $(OCAMLPFFTLAGS) extraction.ml

adapter.cmi:: adapter.mli
	$(MSG) echo OCAMLOPT adapter
	$(CMD) ocamlfind ocamlopt -c $(OCAMLPFFTLAGS) adapter.mli

adapter.cmx:: adapter.ml
	$(MSG) echo OCAMLOPT adapter
	$(CMD) ocamlfind ocamlopt -c $(OCAMLPFFTLAGS) adapter.ml

extraction.mli:: Extraction.v
	$(CMD) coqc -Q ../fowl Maniunfold Extraction.v
