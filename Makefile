.PHONY: all pretty-timed test check_CoqProject coqdoc clean depgraphdoc

all:
	@$(MAKE) -C theories
	@dune build

pretty-timed:
	@$(MAKE) pretty-timed -C theories
	@dune build

test:
	@dune runtest

check_CoqProject:
	scripts/check_projects.sh theories

coqdoc:
	@$(MAKE) coqdoc -C theories

depgraphdoc:
	@$(MAKE) depgraphdoc -C theories

clean:
	@$(MAKE) clean -C theories
	@dune clean
	@echo "Cleaning finished."
