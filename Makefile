.PHONY: all pretty-timed test check_CoqProject rocqdoc clean depgraphdoc

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

rocqdoc:
	@$(MAKE) rocq doc -C theories

depgraphdoc:
	@$(MAKE) depgraphdoc -C theories

clean:
	@$(MAKE) clean -C theories
	@dune clean
	@echo "Cleaning finished."
