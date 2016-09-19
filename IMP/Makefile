OCB_FLAGS = -libs nums -libs unix -I extract/ -I ml/
OCB_FLAGS := -use-menhir -yaccflags --explain $(OCB_FLAGS)

Imp.native: proof
	ocamlbuild $(OCB_FLAGS) ml/Imp.native

Imp.p.native: proof
	ocamlbuild $(OCB_FLAGS) ml/Imp.p.native

Imp.d.byte: proof
	ocamlbuild $(OCB_FLAGS) ml/Imp.d.byte

proof: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

test: Imp.native
	./test/regression/test.sh
	./test/parser_pretty/test.sh 50
	./test/bounded/test.sh -2 2

clean-coq: Makefile.coq
	rm -f extract/*
	$(MAKE) -f Makefile.coq clean
	rm Makefile.coq
	find . -name '.*.aux' -delete

clean-ml:
	ocamlbuild -clean

clean: clean-coq clean-ml

clean-test:
	rm -f test/regression/*.imp.input
	rm -f test/regression/*.imp.result
	rm -f test/parser_pretty/*.imp
	rm -f test/bounded/TESTIMP.*

cleaner: clean clean-test
	rm -f _CoqProject

.PHONY: proof test clean-coq clean-ml clean clean-test cleaner
