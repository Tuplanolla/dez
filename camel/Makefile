MKDIR:=mkdir -p

CMD:=$(if $(VERBOSE),,@ )
MSG:=$(if $(VERBOSE),@ true || ,@ )

all:: adapter.cmi adapter.cmx extraction.cmi extraction.cmx
.PHONY: all

# TODO Take clean from `fowl`.
clean::
	$(CMD) $(RM) .*.aux *.glob *.vo*
	$(CMD) $(RM) extraction.{ml,mli,cmx,cmi,o}
	$(CMD) $(RM) -r gen-ocaml
.PHONY: clean

OCAMLPFFTLAGS:=-O2 -package num -package logs -thread

extraction.cmi:: extraction.mli
	$(MSG) echo OCAMLOPT extraction
	$(CMD) ocamlfind ocamlopt -c $(OCAMLPFFTLAGS) extraction.mli

extraction.cmx:: extraction.ml
	$(MSG) echo OCAMLOPT extraction
	$(CMD) ocamlfind ocamlopt -c $(OCAMLPFFTLAGS) extraction.ml

adapter.cmi:: adapter.mli extraction.cmi
	$(MSG) echo OCAMLOPT adapter
	$(CMD) ocamlfind ocamlopt -c $(OCAMLPFFTLAGS) adapter.mli

adapter.cmx:: adapter.ml extraction.cmi
	$(MSG) echo OCAMLOPT adapter
	$(CMD) ocamlfind ocamlopt -c $(OCAMLPFFTLAGS) adapter.ml

extraction.mli:: Extraction.v
	$(MKDIR) gen-ocaml
	$(CMD) coqc -Q ../fowl Maniunfold Extraction.v
