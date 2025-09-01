.PHONY: all pretty-timed test coqdoc clean depgraphdoc

all:
	@$(MAKE) -C theories
#	@dune build

pretty-timed:
	@$(MAKE) pretty-timed -C theories
#	@dune build

test:
#	@dune runtest

coqdoc:
	@$(MAKE) coqdoc -C theories

depgraphdoc:
	@$(MAKE) depgraphdoc -C theories

clean:
	@$(MAKE) clean -C theories
	@dune clean
	@echo "Cleaning finished."
