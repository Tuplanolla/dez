CMD:=$(if $(VERBOSE),,@ )
MSG:=$(if $(VERBOSE),@ true || ,@ )

all:: extraction.cmi adapter.cmi
.PHONY: all

clean::
	$(CMD) $(RM) .*.aux *.glob *.vo*
	$(CMD) bash -c "echo *.{ml,mli,cmx,cmi,o} | tr ' ' '\n' | \
	grep -v 'adapter.ml' | xargs rm -f"
.PHONY: clean

extraction.cmi:: extraction.mli
	$(MSG) echo OCAMLOPT extraction
	$(CMD) ocamlfind ocamlopt -O2 -c -package num extraction.mli
	$(CMD) ocamlfind ocamlopt -O2 -c -package num extraction.ml

adapter.cmi:: adapter.mli
	$(MSG) echo OCAMLOPT adapter
	$(CMD) ocamlfind ocamlopt -O2 -c -package num adapter.mli
	$(CMD) ocamlfind ocamlopt -O2 -c -package num adapter.ml

extraction.mli:: Extraction.v
	$(CMD) coqc -Q ../bird Maniunfold Extraction.v
