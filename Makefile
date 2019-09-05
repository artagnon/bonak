all: Makefile.coq
	@make -f Makefile.coq all

clean: Makefile.coq
	@make -f Makefile.coq clean
	@rm -f Makefile.coq

Makefile.coq: _CoqProject Makefile
	@coq_makefile -f _CoqProject -o Makefile.coq
