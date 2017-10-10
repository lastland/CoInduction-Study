all: Makefile.coq
	@$(MAKE) -f Makefile.coq

Makefile.coq: */*.v _CoqProject
	@coq_makefile -f _CoqProject -o Makefile.coq
